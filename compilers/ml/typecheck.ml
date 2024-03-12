open! Core
open! Syntax
open Or_error.Let_syntax

let max_qual ts =
  let exists_lin =
    List.fold ts ~init:false ~f:(fun seen_lin t ->
      match (t : Typechecked.Type.t) with
      | Info (_, Lin _) -> true
      | Info (_, Typ _) -> seen_lin)
  in
  if exists_lin
  then fun pt -> Typechecked.Type.Lin pt
  else fun pt -> Typechecked.Type.Typ pt
;;

let incr_free_variables n t =
  let rec incr_free_variables_t t ~depth =
    let open Typechecked.Type in
    match t with
    | Info (tag, Typ pt) -> Info (tag, Typ (incr_free_variables_pt pt ~depth))
    | Info (tag, Lin pt) -> Info (tag, Lin (incr_free_variables_pt pt ~depth))
  and incr_free_variables_pt pt ~depth =
    let open Typechecked.Pretype in
    let h = incr_free_variables_t ~depth in
    match pt with
    | Int | Unit -> pt
    | Var i -> if i < depth then Var i else Var (i + n)
    | Fun { foralls; args; ret } ->
      let depth = depth + foralls in
      Fun
        { foralls
        ; args = List.map ~f:(incr_free_variables_t ~depth) args
        ; ret = incr_free_variables_t ret ~depth
        }
    | Ref t -> Ref (h t)
    | Variant ts -> Variant (List.map ~f:h ts)
    | Prod ts -> Prod (List.map ~f:h ts)
    | Rec t -> Rec (h t)
  in
  incr_free_variables_t t ~depth:0
;;

module Gamma : sig
  type t

  val empty : t
  val add_var : Typechecked.Type.t -> t -> t
  val add_glob : Typechecked.Type.t -> t -> t
  val add_fun : Typechecked.Type.t -> t -> t
  val find_var : int -> t -> Typechecked.Type.t option
  val find_fun : int -> t -> Typechecked.Type.t option
  val find_glob : int -> t -> Typechecked.Type.t option
  val bind_type_vars : int -> t -> t
end = struct
  type t =
    { vars : Typechecked.Type.t list
    ; globs : Typechecked.Type.t list
    ; funs : Typechecked.Type.t list
    }

  let empty = { vars = []; globs = []; funs = [] }
  let add_var e t = { t with vars = e :: t.vars }
  let add_glob e t = { t with globs = t.globs @ [ e ] }
  let add_fun e t = { t with funs = t.funs @ [ e ] }
  let find_var i t = List.nth t.vars i
  let find_glob i t = List.nth t.globs i
  let find_fun i t = List.nth t.funs i
  let bind_type_vars n t = { t with vars = List.map ~f:(incr_free_variables n) t.vars }
end

let subst_typ_t ~in_:(t : Typechecked.Type.t) ~(subst : Typechecked.Type.t)
  : Typechecked.Type.t
  =
  let rec subst_typ_h (Info (tag, t) : Typechecked.Type.t) ~depth =
    let h = subst_typ_h ~depth in
    let pt, flin =
      match t with
      | Lin pt -> pt, fun pt -> Typechecked.Type.Lin pt
      | Typ pt -> pt, fun pt -> Typ pt
    in
    match pt with
    | Var i ->
      if i = depth
      then incr_free_variables depth subst
      else if i > depth
      then Info (tag, flin (Var (i - 1)))
      else Info (tag, flin (Var i))
    | Int -> Info (tag, flin Int)
    | Unit -> Info (tag, flin Unit)
    | Fun { foralls; args; ret } ->
      let depth = depth + foralls in
      Info
        ( tag
        , flin
            (Fun
               { foralls
               ; args = List.map ~f:(fun x -> subst_typ_h x ~depth) args
               ; ret = subst_typ_h ret ~depth
               }) )
    | Ref t -> Info (tag, flin (Ref (h t)))
    | Variant ts -> Info (tag, flin (Variant (List.map ~f:h ts)))
    | Prod ts -> Info (tag, flin (Prod (List.map ~f:h ts)))
    | Rec t -> Info (tag, flin (Rec (subst_typ_h t ~depth:(depth + 1))))
  in
  subst_typ_h t ~depth:0
;;

let rec type_eq (Info (_, t1) : Typechecked.Type.t) (Info (_, t2) : Typechecked.Type.t) =
  let pt_eq (pt1 : Typechecked.Pretype.t) (pt2 : Typechecked.Pretype.t) =
    match pt1, pt2 with
    | Var i1, Var i2 -> i1 = i2
    | Int, Int -> true
    | Unit, Unit -> true
    | Fun { foralls = f1; args = a1; ret = r1 }, Fun { foralls = f2; args = a2; ret = r2 }
      ->
      (match List.zip a1 a2 with
       | Ok l ->
         f1 = f2 && type_eq r1 r2 && List.for_all ~f:(fun (t1, t2) -> type_eq t1 t2) l
       | Unequal_lengths -> false)
    | Ref t1, Ref t2 -> type_eq t1 t2
    | Variant ts1, Variant ts2 ->
      (match List.zip ts1 ts2 with
       | Ok l -> List.for_all ~f:(fun (t1, t2) -> type_eq t1 t2) l
       | Unequal_lengths -> false)
    | Prod ts1, Prod ts2 ->
      (match List.zip ts1 ts2 with
       | Ok l -> List.for_all ~f:(fun (t1, t2) -> type_eq t1 t2) l
       | Unequal_lengths -> false)
    | Rec t1, Rec t2 -> type_eq t1 t2
    | _, _ -> false
  in
  match t1, t2 with
  | Lin pt1, Lin pt2 | Typ pt1, Typ pt2 -> pt_eq pt1 pt2
  | _ -> false
;;

let bind_pattern var typ gamma =
  match (var : Typechecked.Pattern_binding.t), (typ : Typechecked.Type.t) with
  | Unit, Info (_, Typ Unit) | Unit, Info (_, Lin Unit) -> return gamma
  | Unit, actual_type ->
    Or_error.error_s
      [%message "unit binding had non-unit type" (actual_type : Typechecked.Type.t)]
  | Variable, typ -> return (Gamma.add_var typ gamma)
  | (Tuple n, Info (_, Typ (Prod typs)) | Tuple n, Info (_, Lin (Prod typs)))
    when n = List.length typs ->
    return (List.fold_left typs ~init:gamma ~f:(fun gamma typ -> Gamma.add_var typ gamma))
  | Tuple expected_number, actual_type ->
    Or_error.error_s
      [%message
        "tuple binding was not given a tuple of the correct number of values"
          (expected_number : int)
          (actual_type : Typechecked.Type.t)]
;;

let e_type (Typechecked.Expr.Info { tag = _; typ; e = _ }) = typ
let e_tag (Typechecked.Expr.Info { tag; typ = _; e = _ }) = tag

let rec typecheck_e ?no_fun_calls (e : Debruijned.Expr.t) ~gamma ~source_printer
  : Typechecked.Expr.t Or_error.t
  =
  let typecheck_e_with_fun_calls = typecheck_e in
  let typecheck_e = typecheck_e ?no_fun_calls in
  let ensure_is_int typ expr_description =
    match (typ : Typechecked.Type.t) with
    | Info (_, Lin Int) | Info (_, Typ Int) -> return ()
    | _ ->
      let str = "Non int in " ^ expr_description in
      let actual_type = typ in
      Or_error.error_s [%message str (actual_type : Typechecked.Type.t)]
  in
  let (Info (tag, e)) = e in
  let e_and_typ =
    let open Typechecked.Expr in
    let open Typechecked.Type in
    match e with
    | Int i -> return (Int i, Info (tag, Typ Int))
    | Binop (e1, e2, op) ->
      let%bind e1 = typecheck_e e1 ~gamma ~source_printer in
      let%bind e2 = typecheck_e e2 ~gamma ~source_printer in
      let%bind () = ensure_is_int (e_type e1) "binop" in
      let%bind () = ensure_is_int (e_type e2) "binop" in
      return (Binop (e1, e2, op), Info (tag, Typ Int))
    | If0 (e1, e2, e3) ->
      let%bind e1 = typecheck_e e1 ~gamma ~source_printer in
      let%bind e2 = typecheck_e e2 ~gamma ~source_printer in
      let%bind e3 = typecheck_e e3 ~gamma ~source_printer in
      let%bind () = ensure_is_int (e_type e1) "if0 condition" in
      let then_type = e_type e2 in
      let else_type = e_type e3 in
      if type_eq then_type else_type
      then return (If0 (e1, e2, e3), then_type)
      else
        Or_error.error_s
          [%message
            "Unequal types in if0 body"
              (then_type : Typechecked.Type.t)
              (else_type : Typechecked.Type.t)]
    | Let { var; bind; body } ->
      let%bind bind = typecheck_e bind ~gamma ~source_printer in
      let%bind gamma = bind_pattern var (e_type bind) gamma in
      let%bind body = typecheck_e body ~gamma ~source_printer in
      return (Let { var; bind; body }, e_type body)
    | Var i ->
      let typ = Gamma.find_var i gamma in
      return (Var i, Option.value_exn typ)
    | Coderef i ->
      let typ = Gamma.find_fun i gamma in
      return (Coderef i, Option.value_exn typ)
    | Global i ->
      let typ = Gamma.find_glob i gamma in
      return (Global i, Option.value_exn typ)
    | Unit -> return (Unit, Info (tag, Typ Unit))
    | Lambda { foralls; args; body } ->
      let gamma = Gamma.bind_type_vars foralls gamma in
      let%bind gamma =
        List.fold_left args ~init:(return gamma) ~f:(fun gamma (pattern, typ) ->
          let%bind gamma = gamma in
          bind_pattern pattern typ gamma)
      in
      let%bind body = typecheck_e_with_fun_calls body ~gamma ~source_printer in
      return
        ( Lambda { foralls; args; body }
        , Info (tag, Typ (Fun { foralls; args = List.map ~f:snd args; ret = e_type body }))
        )
    | Apply _ when Option.is_some no_fun_calls ->
      Or_error.error_s [%message "Attempted to apply a function in a global varaible"]
    | Apply { f; inst; args } ->
      let%bind f = typecheck_e f ~gamma ~source_printer in
      let%bind args =
        List.map ~f:(typecheck_e ~gamma ~source_printer) args |> Or_error.all
      in
      let%bind typ =
        match e_type f with
        | Info (_, Lin (Fun { foralls; args = arg_typs; ret }))
        | Info (_, Typ (Fun { foralls; args = arg_typs; ret })) ->
          let%bind subst_foralls =
            if List.length inst = foralls
            then
              return (fun typ ->
                List.fold_right
                  ~init:typ
                  ~f:(fun subst in_ -> subst_typ_t ~subst ~in_)
                  inst)
            else
              Or_error.error_s
                [%message
                  "Application with wrong number of type instantiations"
                    ~actual_type:(e_type f : Typechecked.Type.t)
                    ~number_of_insts:(List.length inst : int)]
          in
          let arg_typs = List.map ~f:subst_foralls arg_typs in
          let check_arg_type (t1, t2) =
            if type_eq t1 t2
            then return ()
            else
              Or_error.error_s
                [%message
                  "Application with wrong arg type"
                    ~expected_type:(t1 : Typechecked.Type.t)
                    ~actual_type:(t2 : Typechecked.Type.t)]
          in
          let%bind () =
            match List.zip arg_typs (List.map ~f:e_type args) with
            | Unequal_lengths ->
              Or_error.error_s
                [%message
                  "Application with incorrect arg number"
                    ~expected_number:(List.length arg_typs : int)
                    ~actual_number:(List.length args : int)]
            | Ok l -> List.map ~f:check_arg_type l |> Or_error.all_unit
          in
          ret |> subst_foralls |> return
        | _ ->
          Or_error.error_s
            [%message
              "Application of non function" ~actual_type:(e_type f : Typechecked.Type.t)]
      in
      return (Apply { f; inst; args }, typ)
    | New e ->
      let%bind e = typecheck_e e ~gamma ~source_printer in
      return (New e, Info (tag, Typ (Ref (e_type e))))
    | New_lin typ -> return (New_lin typ, Info (tag, Typ (Ref typ)))
    | Deref e ->
      let%bind e = typecheck_e e ~gamma ~source_printer in
      (match e_type e with
       | Info (_, Lin (Ref t)) | Info (_, Typ (Ref t)) -> return (Deref e, t)
       | _ ->
         Or_error.error_s
           [%message
             "Dereference of non reference" ~actual_type:(e_type e : Typechecked.Type.t)])
    | Assign { ref; value } ->
      let%bind ref = typecheck_e ref ~gamma ~source_printer in
      let%bind value = typecheck_e value ~gamma ~source_printer in
      (match e_type ref with
       | Info (_, Lin (Ref t)) | Info (_, Typ (Ref t)) ->
         if type_eq t (e_type value)
         then return (Assign { ref; value }, Info (tag, Typ Unit))
         else
           Or_error.error_s
             [%message
               "Assign with wrong type"
                 ~expected_type:(t : Typechecked.Type.t)
                 ~actual_type:(e_type value : Typechecked.Type.t)]
       | _ ->
         Or_error.error_s
           [%message
             "Assign into non reference" ~actual_type:(e_type ref : Typechecked.Type.t)])
    | Inj { n; typ; value } ->
      let%bind value = typecheck_e value ~gamma ~source_printer in
      (match List.nth typ n with
       | Some typ_n ->
         if type_eq typ_n (e_type value)
         then (
           let flin = max_qual typ in
           return
             (Inj { n; typ; value }, Info (tag, flin (Typechecked.Pretype.Variant typ))))
         else
           Or_error.error_s
             [%message
               "Inj with wrong type"
                 ~expected_type:(typ_n : Typechecked.Type.t)
                 ~actual_type:(e_type value : Typechecked.Type.t)]
       | None ->
         Or_error.error_s
           [%message
             "Inj without enough types" (n : int) ~types:(typ : Typechecked.Type.t list)])
    | Case { bind; body } ->
      let%bind bind = typecheck_e bind ~gamma ~source_printer in
      let%bind body =
        match e_type bind with
        | Info (_, Lin (Variant ts)) | Info (_, Typ (Variant ts)) ->
          (match List.zip ts body with
           | Ok l ->
             List.map
               ~f:(fun (bind, body) ->
                 typecheck_e body ~gamma:(Gamma.add_var bind gamma) ~source_printer)
               l
             |> Or_error.all
           | Unequal_lengths ->
             Or_error.error_s
               [%message
                 "Case with incorrect number of cases"
                   ~actual_type:(e_type bind : Typechecked.Type.t)
                   ~number_of_cases:(List.length body : int)])
        | _ ->
          Or_error.error_s
            [%message
              "Case on non variant" ~actual_type:(e_type bind : Typechecked.Type.t)]
      in
      let verify_same t1 t2 =
        let%bind t1 = t1 in
        match t1 with
        | Some t ->
          if type_eq t t2
          then return (Some t)
          else (
            let case_types = List.map ~f:e_type body in
            Or_error.error_s
              [%message
                "Case branch types not equal" (case_types : Typechecked.Type.t list)])
        | None -> return (Some t2)
      in
      let%bind typ =
        List.fold_left ~init:(return None) ~f:verify_same (List.map ~f:e_type body)
        |> Or_error.map ~f:(fun x -> Option.value_exn x)
      in
      return (Case { bind; body }, typ)
    | Prod es ->
      let%bind es = List.map ~f:(typecheck_e ~gamma ~source_printer) es |> Or_error.all in
      let flin = max_qual (List.map ~f:e_type es) in
      return (Prod es, Info (tag, flin (Typechecked.Pretype.Prod (List.map ~f:e_type es))))
    | Proj { e; n } ->
      let%bind e = typecheck_e e ~gamma ~source_printer in
      let%bind typ =
        match e_type e with
        | Info (_, Lin (Prod ts)) | Info (_, Typ (Prod ts)) ->
          (match List.nth ts n with
           | Some t -> return t
           | None ->
             Or_error.error_s
               [%message
                 "Proj out of bounds"
                   ~actual_type:(e_type e : Typechecked.Type.t)
                   ~index:(n : int)])
        | _ ->
          Or_error.error_s
            [%message "Proj on non prod" ~actual_type:(e_type e : Typechecked.Type.t)]
      in
      return (Proj { e; n }, typ)
    | Fold { typ; e } ->
      let%bind e = typecheck_e e ~gamma ~source_printer in
      let%bind () =
        match typ with
        | Info (_, Lin (Rec t)) | Info (_, Typ (Rec t)) ->
          if type_eq (subst_typ_t ~subst:typ ~in_:t) (e_type e)
          then return ()
          else
            Or_error.error_s
              [%message
                "Fold of incompatible types"
                  ~from:(e_type e : Typechecked.Type.t)
                  ~to_:(typ : Typechecked.Type.t)]
        | _ ->
          Or_error.error_s
            [%message
              "Fold with non-rec annotation" ~annotation:(typ : Typechecked.Type.t)]
      in
      return (Fold { typ; e }, typ)
    | Unfold e ->
      let%bind e = typecheck_e e ~gamma ~source_printer in
      (match e_type e with
       | Info (_, Lin (Rec t)) | Info (_, Typ (Rec t)) ->
         return (Unfold e, subst_typ_t ~subst:(e_type e) ~in_:t)
       | _ ->
         Or_error.error_s
           [%message "Unfold on non rec" ~actual_type:(e_type e : Typechecked.Type.t)])
  in
  let in_expr = Source_printer.get_source source_printer tag in
  let%bind e, typ =
    e_and_typ |> Or_error.tag_s ~tag:[%message (in_expr : string option)]
  in
  return (Typechecked.Expr.Info { tag; typ; e })
;;

let rec typecheck_m (m : Debruijned.Module.t) ~gamma ~source_printer
  : Typechecked.Module.t Or_error.t
  =
  let open Typechecked.Module in
  match m with
  | LetIm ({ typ; mod_name; fun_name }, m, tag) ->
    let type_ = Typechecked.Type.Info (tag, Typ (Fun typ)) in
    let%bind m = typecheck_m m ~gamma:(Gamma.add_fun type_ gamma) ~source_printer in
    return (LetIm ({ typ; mod_name; fun_name }, m, tag))
  | LetEx (s, { foralls; args; body }, m, tag) ->
    let gamma_e = Gamma.bind_type_vars foralls gamma in
    let%bind gamma_e =
      List.fold_left args ~init:(return gamma_e) ~f:(fun gamma_e (pattern, typ) ->
        let%bind gamma_e = gamma_e in
        bind_pattern pattern typ gamma_e)
    in
    let%bind body = typecheck_e body ~gamma:gamma_e ~source_printer in
    let func = { Typechecked.Module.foralls; args; body } in
    let typ =
      Typechecked.Type.Info
        (e_tag body, Typ (Fun { foralls; args = List.map ~f:snd args; ret = e_type body }))
    in
    let%bind m = typecheck_m m ~gamma:(Gamma.add_fun typ gamma) ~source_printer in
    return (LetEx (s, func, m, tag))
  | Global (e, m, tag) ->
    let%bind e = typecheck_e e ~no_fun_calls:() ~gamma ~source_printer in
    let%bind m = typecheck_m m ~gamma:(Gamma.add_glob (e_type e) gamma) ~source_printer in
    return (Global (e, m, tag))
  | Body e ->
    let%bind e = typecheck_e e ~gamma ~source_printer in
    return (Body e)
;;

let typecheck m = typecheck_m m ~gamma:Gamma.empty
