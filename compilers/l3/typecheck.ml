open! Core
open! Syntax
open Or_error.Let_syntax

module Or_used = struct
  type 'a t =
    | Ok of 'a
    | Used
end

module Gamma : sig
  type t [@@deriving sexp]

  val empty : t
  val add_var : Typechecked.Type.t -> t -> t
  val add_fun : Typechecked.Type.t -> t -> t
  val consume_var : int -> t -> Typechecked.Type.t Or_used.t option
  val get_fun : int -> t -> Typechecked.Type.t option
  val check_var_used_exn : int -> t -> bool
  val num_unused : t -> int
end = struct
  type t =
    { vars : (Typechecked.Type.t * bool ref) list
    ; funs : Typechecked.Type.t list
    }
  [@@deriving sexp]

  let empty = { vars = []; funs = [] }
  let add_var typ t = { t with vars = (typ, ref false) :: t.vars }
  let add_fun typ t = { t with funs = t.funs @ [ typ ] }

  let consume_var n t =
    Option.map (List.nth t.vars n) ~f:(fun (typ, used) ->
      match typ with
      | Info (_, Bang _) -> Or_used.Ok typ
      | _ ->
        if !used
        then Or_used.Used
        else (
          used := true;
          Ok typ))
  ;;

  let get_fun n t = List.nth t.funs n

  let check_var_used_exn n t =
    let typ, used = List.nth_exn t.vars n in
    match typ with
    | Info (_, Bang _) -> true
    | _ -> !used
  ;;

  let num_unused t = List.count t.vars ~f:(fun (_, used) -> not !used)
end

let rec type_eq (Info (_, t1) : Typechecked.Type.t) (Info (_, t2) : Typechecked.Type.t) =
  let type_eq_list ts1 ts2 =
    match List.zip ts1 ts2 with
    | Ok zipped -> List.for_all zipped ~f:(fun (t1, t2) -> type_eq t1 t2)
    | Unequal_lengths -> false
  in
  match t1, t2 with
  | Int, Int | Unit, Unit -> true
  | Prod ts1, Prod ts2 -> type_eq_list ts1 ts2
  | Fun { foralls = f1; args = a1; ret = r1 }, Fun { foralls = f2; args = a2; ret = r2 }
    -> f1 = f2 && type_eq_list a1 a2 && type_eq r1 r2
  | Bang t1, Bang t2 -> type_eq t1 t2
  | Ptr v1, Ptr v2 -> v1 = v2
  | Cap (v1, t1, n1), Cap (v2, t2, n2) | Ref (v1, t1, n1, _), Ref (v2, t2, n2, _) ->
    v1 = v2 && type_eq t1 t2 && n1 = n2
  | Exists t1, Exists t2 -> type_eq t1 t2
  | _ -> false
;;

let e_type (Typechecked.Expr.Info { tag = _; typ; e = _ }) = typ
let e_tag (Typechecked.Expr.Info { tag; typ = _; e = _ }) = tag

let rec size_of_type (Info (_, t) : Typechecked.Type.t) =
  match t with
  | Int -> 1
  | Unit -> 0
  | Prod ts -> List.sum (module Int) ~f:size_of_type ts
  | Fun _ -> 2
  | Bang t -> size_of_type t
  | Ptr _ | Ref _ -> 2
  | Cap _ -> 0
  | Exists t -> size_of_type t
;;

let bind_pattern var typ gamma =
  match (var : Typechecked.Binding_or_unit.t), (typ : Typechecked.Type.t) with
  | `Unit, Info (_, Unit) | `Unit, Info (_, Bang (Info (_, Unit))) -> return gamma
  | `Unit, actual_type ->
    Or_error.error_s
      [%message "unit binding had non-unit type" (actual_type : Typechecked.Type.t)]
  | `Binding, typ -> return (Gamma.add_var typ gamma)
;;

let incr_free_vars_in_t incr t =
  let rec h_t (Info (tag, t) : Typechecked.Type.t) ~depth =
    let h = h_t ~depth in
    let t =
      match t with
      | Int | Unit -> t
      | Prod ts -> Prod (List.map ~f:h ts)
      | Fun { foralls; args; ret } ->
        let depth = depth + foralls in
        let f = h_t ~depth in
        Fun { foralls; args = List.map ~f args; ret = f ret }
      | Bang t -> Bang (h t)
      | Ptr v -> if v < depth then Ptr v else Ptr (v + incr)
      | Cap (v, t, n) ->
        let t = h t in
        if v < depth then Cap (v, t, n) else Cap (v + incr, t, n)
      | Ref (v, t, n, nativity) ->
        let t = h t in
        if v < depth then Ref (v, t, n, nativity) else Ref (v + incr, t, n, nativity)
      | Exists t -> Exists (h_t ~depth:(depth + 1) t)
    in
    Info (tag, t)
  in
  h_t t ~depth:0
;;

let subst_in_t ?(depth = 0) subst t =
  let subst = subst - depth in
  let rec h_t (Info (tag, t) : Typechecked.Type.t) ~depth =
    let h = h_t ~depth in
    let t =
      match t with
      | Int | Unit -> t
      | Prod ts -> Prod (List.map ~f:h ts)
      | Fun { foralls; args; ret } ->
        let depth = depth + foralls in
        let f = h_t ~depth in
        Fun { foralls; args = List.map ~f args; ret = f ret }
      | Bang t -> Bang (h t)
      | Ptr v -> if v = depth then Ptr (subst + depth) else Ptr v
      | Cap (v, t, n) ->
        let t = h t in
        if v = depth then Cap (subst + depth, t, n) else Cap (v, t, n)
      | Ref (v, t, n, nativity) ->
        let t = h t in
        if v = depth then Ref (subst + depth, t, n, nativity) else Ref (v, t, n, nativity)
      | Exists t -> Exists (h_t ~depth:(depth + 1) t)
    in
    Info (tag, t)
  in
  h_t t ~depth
;;

let vars_well_bound t =
  let rec h_t (Info (_, t) : Typechecked.Type.t) ~depth =
    let h = h_t ~depth in
    match t with
    | Int | Unit -> return ()
    | Prod ts -> ts |> List.map ~f:h |> Or_error.all_unit
    | Fun { foralls; args; ret } ->
      let depth = depth + foralls in
      let f = h_t ~depth in
      let%bind () = args |> List.map ~f |> Or_error.all_unit in
      f ret
    | Bang t -> h t
    | Ptr v ->
      if v = depth
      then Or_error.error_s [%message "var not bound after unpack"]
      else return ()
    | Cap (v, t, _) | Ref (v, t, _, _) ->
      let%bind () = h t in
      if v = depth
      then Or_error.error_s [%message "var not bound after unpack"]
      else return ()
    | Exists t -> h_t ~depth:(depth + 1) t
  in
  h_t t ~depth:0
;;

let rec typecheck_e (e : Debruijned.Expr.t) ~gamma ~delta : Typechecked.Expr.t Or_error.t =
  let h = typecheck_e ~gamma ~delta in
  let open Typechecked.Expr in
  let (Info (tag, e)) = e in
  let tag_t t = Typechecked.Type.Info (tag, t) in
  let%bind e, typ =
    match e with
    | Int i -> return (Int i, tag_t Int)
    | Binop (e1, e2, op) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      let%bind () =
        match e_type e1, e_type e2 with
        | Info (_, Int), Info (_, Int)
        | Info (_, Bang (Info (_, Int))), Info (_, Int)
        | Info (_, Int), Info (_, Bang (Info (_, Int)))
        | Info (_, Bang (Info (_, Int))), Info (_, Bang (Info (_, Int))) -> return ()
        | _ ->
          Or_error.error_s
            [%message
              "binops require two ints"
                ~actual_first_type:(e_type e1 : Typechecked.Type.t)
                ~actual_second_type:(e_type e2 : Typechecked.Type.t)]
      in
      return (Binop (e1, e2, op), tag_t (Bang (tag_t Int)))
    | Unit -> return (Unit, tag_t Unit)
    | LetUnit { bind; body } ->
      let%bind bind = h bind in
      let%bind () =
        match e_type bind with
        | Info (_, Unit) | Info (_, Bang (Info (_, Unit))) -> return ()
        | _ ->
          Or_error.error_s
            [%message
              "let unit requires a unit type bind"
                ~actual_type:(e_type bind : Typechecked.Type.t)]
      in
      let%bind body = h body in
      return (LetUnit { bind; body }, e_type body)
    | Prod es ->
      let%bind es = List.map ~f:h es |> Or_error.all in
      return (Prod es, tag_t (Prod (List.map ~f:e_type es)))
    | LetProd { vars; bind; body } ->
      let%bind bind = h bind in
      let%bind vars_and_typs =
        match e_type bind with
        | Info (_, Prod typs) when List.length typs = List.length vars ->
          return (List.zip_exn vars typs)
        | _ ->
          Or_error.error_s
            [%message
              "let prod requires a prod type with the correct number of elements"
                ~actual_type:(e_type bind : Typechecked.Type.t)]
      in
      let%bind gamma =
        List.fold_left vars_and_typs ~init:(return gamma) ~f:(fun gamma (var, typ) ->
          let%bind gamma = gamma in
          bind_pattern var typ gamma)
      in
      let%bind body = typecheck_e ~gamma ~delta body in
      let%bind () =
        vars_and_typs
        |> List.filter ~f:(fun (var, _) ->
          match var with
          | `Unit -> false
          | `Binding -> true)
        |> List.mapi ~f:(fun n (_, typ) ->
          match typ with
          | Info (_, Bang _) -> return ()
          | _ ->
            if Gamma.check_var_used_exn n gamma
            then return ()
            else
              Or_error.error_s [%message "variable was not consumed by body of let prod"])
        |> Or_error.all_unit
      in
      return (LetProd { vars; bind; body }, e_type body)
    | Var i ->
      (match Gamma.consume_var i gamma with
       | Some (Ok typ) -> return (Var i, typ)
       | Some Used ->
         Or_error.error_s [%message "Variable was already used" ~variable:(i : int)]
       | None ->
         raise_s [%message "BUG: variable was not found in context after debruijning"])
    | Fun i ->
      (match Gamma.get_fun i gamma with
       | Some typ -> return (Fun i, typ)
       | None ->
         raise_s [%message "BUG: fun variable was not found in context after debruijning"])
    | Apply { f; args } ->
      let%bind f = h f in
      (match e_type f with
       | Info (_, Fun { foralls; args = arg_typs; ret })
       | Info (_, Bang (Info (_, Fun { foralls; args = arg_typs; ret })))
         when List.length arg_typs = List.length args && foralls = 0 ->
         let%bind args = List.map ~f:h args |> Or_error.all in
         let check_arg_type (t1, t2) =
           if type_eq t1 t2
           then return ()
           else
             Or_error.error_s
               [%message
                 "application had wrong type"
                   ~expected:(t1 : Typechecked.Type.t)
                   ~got:(t2 : Typechecked.Type.t)]
         in
         let%bind () =
           args
           |> List.map ~f:e_type
           |> List.zip_exn arg_typs
           |> List.map ~f:check_arg_type
           |> Or_error.all_unit
         in
         return (Apply { f; args }, ret)
       | _ ->
         Or_error.error_s
           [%message
             "application did not have a fully instantiated function and corresponding \
              args"
               ~actual_fun_type:(e_type f : Typechecked.Type.t)
               ~num_args:(List.length args : int)])
    | Bang e ->
      let rec is_value (Info (_, e) : Debruijned.Expr.t) =
        match e with
        | Int _ | Unit | Var _ | Fun _ -> return ()
        | Bang e | Pack (_, e) -> is_value e
        | Prod es -> List.map ~f:is_value es |> Or_error.all_unit
        | _ ->
          Or_error.error_s
            [%message "Bang contained a non_value" (e : Debruijned.Expr.t_base)]
      in
      let%bind () = is_value e in
      let before_unused = Gamma.num_unused gamma in
      let%bind e = h e in
      let after_unused = Gamma.num_unused gamma in
      let%bind () =
        if before_unused = after_unused
        then return ()
        else
          Or_error.error_s
            [%message "Bang contained uses of linear variables" (e : Typechecked.Expr.t)]
      in
      return (Bang e, tag_t (Bang (e_type e)))
    | LetBang { var; bind; body } ->
      let%bind bind = h bind in
      let%bind typ =
        match e_type bind with
        | Info (_, Bang typ) -> return typ
        | _ ->
          Or_error.error_s
            [%message
              "let bang requires a bang type"
                ~actual_type:(e_type bind : Typechecked.Type.t)]
      in
      let%bind gamma = bind_pattern var typ gamma in
      let%bind body = typecheck_e ~gamma ~delta body in
      let%bind () =
        match var with
        | `Unit -> return ()
        | `Binding ->
          (match typ with
           | Info (_, Bang _) -> return ()
           | _ ->
             if Gamma.check_var_used_exn 0 gamma
             then return ()
             else
               Or_error.error_s [%message "variable was not consumed by body of let bang"])
      in
      return (LetBang { var; bind; body }, e_type body)
    | Dupl e ->
      let%bind e = h e in
      let typ = e_type e in
      (match typ with
       | Info (_, Bang _) -> return (Dupl e, tag_t (Prod [ typ; typ ]))
       | _ ->
         Or_error.error_s
           [%message "Dupl requires bang type" ~actual_type:(typ : Typechecked.Type.t)])
    | Drop e ->
      let%bind e = h e in
      let typ = e_type e in
      (match typ with
       | Info (_, Bang _) -> return (Drop e, tag_t Unit)
       | _ ->
         Or_error.error_s
           [%message "Drop requires bang type" ~actual_type:(typ : Typechecked.Type.t)])
    | New (e, n) ->
      let%bind e = h e in
      let typ = e_type e in
      let size = size_of_type typ in
      let%bind () =
        if size <= n
        then return ()
        else
          Or_error.error_s
            [%message
              "new was called on too small a size"
                ~size:(n : int)
                ~type_:(typ : Typechecked.Type.t)
                ~actual_size:(size : int)]
      in
      return
        ( New (e, n)
        , tag_t
            (Exists
               (tag_t
                  (Prod
                     [ tag_t (Cap (0, incr_free_vars_in_t 1 typ, n))
                     ; tag_t (Bang (tag_t (Ptr 0)))
                     ]))) )
    | Free e ->
      let%bind e = h e in
      let%bind typ =
        match e_type e with
        | Info
            ( _
            , Exists
                (Info
                  (_, Prod [ Info (_, Cap (0, typ, _)); Info (_, Bang (Info (_, Ptr 0))) ]))
            ) -> return typ
        | _ ->
          Or_error.error_s
            [%message
              "Free called on wrong type" ~actual_type:(e_type e : Typechecked.Type.t)]
      in
      return (Free e, tag_t (Exists typ))
    | Swap (e1, e2) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      (match e_type e1, e_type e2 with
       | ( Info (_, Bang (Info (_, Ptr n1)))
         , Info (tag_prod, Prod [ Info (tag_cap, Cap (n2, typ1, sz)); typ2 ]) )
         when n1 = n2 ->
         let%bind () =
           let size = size_of_type typ2 in
           if size <= sz
           then return ()
           else
             Or_error.error_s
               [%message
                 "swap was called on too large a type"
                   ~size:(sz : int)
                   ~type_:(typ2 : Typechecked.Type.t)
                   ~actual_size:(size : int)]
         in
         return
           ( Swap (e1, e2)
           , Typechecked.Type.Info
               (tag_prod, Prod [ Info (tag_cap, Cap (n2, typ2, sz)); typ1 ]) )
       | _ ->
         Or_error.error_s
           [%message
             "Swap had wrong types"
               ~actual_first:(e_type e1 : Typechecked.Type.t)
               ~actual_second:(e_type e2 : Typechecked.Type.t)])
    | Join e ->
      let%bind e = h e in
      let%bind typ =
        match e_type e with
        | Info
            ( _
            , Exists
                (Info
                  ( _
                  , Prod [ Info (_, Cap (0, typ, sz)); Info (_, Bang (Info (_, Ptr 0))) ]
                  )) ) ->
          return (Typechecked.Type.Exists (tag_t (Ref (0, typ, sz, Native))))
        | _ ->
          Or_error.error_s
            [%message
              "Join called on wrong type" ~actual_type:(e_type e : Typechecked.Type.t)]
      in
      return (Join e, tag_t typ)
    | Split e ->
      let%bind e = h e in
      let%bind typ =
        match e_type e with
        | Info (_, Exists (Info (_, Ref (n, typ, sz, Native)))) ->
          return
            (Typechecked.Type.Exists
               (tag_t (Prod [ tag_t (Cap (n, typ, sz)); tag_t (Bang (tag_t (Ptr n))) ])))
        | _ ->
          Or_error.error_s
            [%message
              "Split called on wrong type" ~actual_type:(e_type e : Typechecked.Type.t)]
      in
      return (Split e, tag_t typ)
    | Inst (e, insts) ->
      let%bind e = h e in
      let%bind foralls, args, ret =
        match e_type e with
        | Info (_, Fun { foralls; args; ret }) when foralls >= List.length insts ->
          return (foralls, args, ret)
        | _ ->
          Or_error.error_s
            [%message
              "Inst not on function with enough foralls"
                ~actual_type:(e_type e : Typechecked.Type.t)]
      in
      let foralls, args, ret =
        List.fold insts ~init:(foralls, args, ret) ~f:(fun (foralls, args, ret) inst ->
          let inst = inst + foralls in
          let args =
            List.map
              ~f:(fun arg -> arg |> subst_in_t inst |> incr_free_vars_in_t (-1))
              args
          in
          let ret = ret |> subst_in_t inst |> incr_free_vars_in_t (-1) in
          let foralls = foralls - 1 in
          foralls, args, ret)
      in
      return (Inst (e, insts), tag_t (Fun { foralls; args; ret }))
    | Pack (n, e) ->
      let%bind e = h e in
      let typ = e |> e_type |> incr_free_vars_in_t 1 |> subst_in_t ~depth:(n + 1) 0 in
      return (Pack (n, e), tag_t (Exists typ))
    | Unpack { var; package; body } ->
      let%bind package = h package in
      let%bind typ =
        match e_type package with
        | Info (_, Exists typ) -> return typ
        | _ ->
          Or_error.error_s
            [%message
              "unpack given non existential"
                ~actual_type:(e_type package : Typechecked.Type.t)]
      in
      let%bind gamma = bind_pattern var typ gamma in
      let delta = delta + 1 in
      let%bind body = typecheck_e ~gamma ~delta body in
      let%bind () =
        match var with
        | `Unit -> return ()
        | `Binding ->
          (match typ with
           | Info (_, Bang _) -> return ()
           | _ ->
             if Gamma.check_var_used_exn 0 gamma
             then return ()
             else
               Or_error.error_s [%message "variable was not consumed by body of unpack"])
      in
      let%bind () = body |> e_type |> vars_well_bound in
      let typ = body |> e_type |> incr_free_vars_in_t (-1) in
      return (Unpack { var; package; body }, typ)
  in
  return (Info { tag; typ; e })
;;

let rec typecheck_m (m : Debruijned.Module.t) ~gamma ~source_printer
  : Typechecked.Module.t Or_error.t
  =
  let open Typechecked.Module in
  match m with
  | LetIm ({ typ; mod_name; fun_name }, m) ->
    let is_bang_fun (Typechecked.Type.Info (_, t)) =
      match t with
      | Bang (Info (_, Fun _)) -> true
      | _ -> false
    in
    let%bind () =
      if is_bang_fun typ
      then return ()
      else
        Or_error.error_s
          [%message
            "Invalid import type"
              ~module_:(mod_name : string)
              ~function_:(fun_name : string)
              ~type_:(typ : Typechecked.Type.t)]
    in
    let%bind m = typecheck_m m ~gamma:(Gamma.add_fun typ gamma) ~source_printer in
    return (LetIm ({ typ; mod_name; fun_name }, m))
  | LetEx (s, { foralls; args; body }, m) ->
    let%bind gamma_e =
      List.fold_left args ~init:(return gamma) ~f:(fun gamma_e (pattern, typ) ->
        let%bind gamma_e = gamma_e in
        bind_pattern pattern typ gamma_e)
    in
    let%bind body = typecheck_e body ~gamma:gamma_e ~delta:foralls in
    let func = { foralls; args; body } in
    let tag x = Typechecked.Type.Info (e_tag body, x) in
    let typ =
      tag (Bang (tag (Fun { foralls; args = List.map ~f:snd args; ret = e_type body })))
    in
    let%bind m = typecheck_m m ~gamma:(Gamma.add_fun typ gamma) ~source_printer in
    return (LetEx (s, func, m))
  | Body e ->
    let%bind e = typecheck_e e ~gamma ~delta:0 in
    return (Body e)
;;

let typecheck m = typecheck_m m ~gamma:Gamma.empty
