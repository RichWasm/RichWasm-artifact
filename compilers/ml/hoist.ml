open Core
open! Syntax

module Incr_map : sig
  type t

  val empty : t
  val add_bindings : int -> t -> t
  val incr : t -> t
  val find_exn : int -> t -> int
end = struct
  type t = int list

  let empty = []
  let add_bindings n t = List.init n ~f:(fun _ -> 0) @ t
  let incr = List.map ~f:(fun i -> i + 1)
  let find_exn n t = List.nth_exn t n
end

let rec convert_type (t : Typechecked.Type.t) ~incr_map =
  let open Hoisted.Type in
  match t with
  | Info (tag, Typ pt) -> Info (tag, Typ (convert_pretype pt ~incr_map))
  | Info (tag, Lin pt) -> Info (tag, Lin (convert_pretype pt ~incr_map))

and convert_pretype (pt : Typechecked.Pretype.t) ~incr_map =
  let open Hoisted.Pretype in
  match pt with
  | Int -> Int
  | Var v -> Var (v + Incr_map.find_exn v incr_map)
  | Unit -> Unit
  | Fun { foralls; args; ret } ->
    let incr_map = incr_map |> Incr_map.incr |> Incr_map.add_bindings foralls in
    let args = List.map ~f:(convert_type ~incr_map) args in
    let ret = convert_type ret ~incr_map in
    Exists_closure { foralls; args; ret }
  | Ref t -> Ref (convert_type t ~incr_map)
  | Variant ts -> Variant (List.map ~f:(convert_type ~incr_map) ts)
  | Prod ts -> Prod (List.map ~f:(convert_type ~incr_map) ts)
  | Rec t -> Rec (convert_type t ~incr_map:(Incr_map.add_bindings 1 incr_map))
;;

let pattern_depth var =
  match (var : Typechecked.Pattern_binding.t) with
  | Unit -> 0
  | Variable -> 1
  | Tuple n -> n
;;

(*
   let incr_free_expr_vars n e =
  let rec h_e e ~depth =
    let h = h_e ~depth in
    let (Typechecked.Expr.Info { typ; e; tag }) = e in
    let e =
      match e with
      | Int i -> Typechecked.Expr.Int i
      | Unit -> Unit
      | Binop (e1, e2, op) ->
        let e1 = h e1 in
        let e2 = h e2 in
        Binop (e1, e2, op)
      | If0 (e1, e2, e3) ->
        let e1 = h e1 in
        let e2 = h e2 in
        let e3 = h e3 in
        If0 (e1, e2, e3)
      | Let { var; bind; body } ->
        let incr = pattern_depth var in
        let bind = h bind in
        let body = h_e body ~depth:(depth + incr) in
        Let { var; bind; body }
      | Var i -> if i < depth then Var i else Var (i + n)
      | Coderef i -> Coderef i
      | Global i -> Global i
      | Lambda { foralls; args; body } ->
        let incr =
          List.sum (module Int) args ~f:(fun (pattern, _) -> pattern_depth pattern)
        in
        let body = h_e body ~depth:(depth + incr) in
        Lambda { foralls; args; body }
      | Apply { f; inst; args } ->
        let f = h f in
        let args = List.map args ~f:h in
        Apply { f; inst; args }
      | New e ->
        let e = h e in
        New e
      | New_lin typ -> New_lin typ
      | Deref e ->
        let e = h e in
        Deref e
      | Assign { ref; value } ->
        let ref = h ref in
        let value = h value in
        Assign { ref; value }
      | Inj { n; typ; value } ->
        let value = h value in
        Inj { n; typ; value }
      | Case { bind; body } ->
        let bind = h bind in
        let body = List.map body ~f:(h_e ~depth:(depth + 1)) in
        Case { bind; body }
      | Prod es ->
        let es = List.map ~f:h es in
        Prod es
      | Proj { e; n } ->
        let e = h e in
        Proj { e; n }
      | Fold { typ; e } ->
        let e = h e in
        Fold { typ; e }
      | Unfold e ->
        let e = h e in
        Unfold e
    in
    Typechecked.Expr.Info { typ; e; tag }
  in
  h_e e ~depth:0
;;
*)

let incr_free_type_vars_t ?(depth = 0) n t =
  let rec h_t t ~depth =
    let open Typechecked.Type in
    match t with
    | Info (tag, Typ pt) -> Info (tag, Typ (h_pt pt ~depth))
    | Info (tag, Lin pt) -> Info (tag, Lin (h_pt pt ~depth))
  and h_pt pt ~depth =
    match pt with
    | Int -> Int
    | Var i -> if i < depth then Var i else Var (i + n)
    | Unit -> Unit
    | Fun { foralls; args; ret } ->
      let depth = depth + foralls in
      let args = List.map ~f:(h_t ~depth) args in
      let ret = h_t ~depth ret in
      Fun { foralls; args; ret }
    | Ref t -> Ref (h_t t ~depth)
    | Variant ts -> Variant (List.map ts ~f:(h_t ~depth))
    | Prod ts -> Prod (List.map ts ~f:(h_t ~depth))
    | Rec t -> Rec (h_t t ~depth:(depth + 1))
  in
  h_t t ~depth
;;

(*
   let incr_free_type_vars n e =
  let rec h_e e ~depth =
    let h = h_e ~depth in
    let (Typechecked.Expr.Info { typ; e; tag }) = e in
    let e =
      match e with
      | Int i -> Typechecked.Expr.Int i
      | Unit -> Unit
      | Binop (e1, e2, op) ->
        let e1 = h e1 in
        let e2 = h e2 in
        Binop (e1, e2, op)
      | If0 (e1, e2, e3) ->
        let e1 = h e1 in
        let e2 = h e2 in
        let e3 = h e3 in
        If0 (e1, e2, e3)
      | Let { var; bind; body } ->
        let bind = h bind in
        let body = h body in
        Let { var; bind; body }
      | Var i -> Var i
      | Coderef i -> Coderef i
      | Global i -> Global i
      | Lambda { foralls; args; body } ->
        let depth = depth + foralls in
        let body = h_e body ~depth in
        let args =
          List.map args ~f:(fun (pattern, typ) ->
            pattern, incr_free_type_vars_t n ~depth typ)
        in
        Lambda { foralls; args; body }
      | Apply { f; inst; args } ->
        let f = h f in
        let args = List.map ~f:h args in
        let inst = List.map inst ~f:(incr_free_type_vars_t n ~depth) in
        Apply { f; inst; args }
      | New e ->
        let e = h e in
        New e
      | New_lin typ ->
        let typ = incr_free_type_vars_t n ~depth typ in
        New_lin typ
      | Deref e ->
        let e = h e in
        Deref e
      | Assign { ref; value } ->
        let ref = h ref in
        let value = h value in
        Assign { ref; value }
      | Inj { n; typ; value } ->
        let value = h value in
        let typ = List.map ~f:(incr_free_type_vars_t n ~depth) typ in
        Inj { n; typ; value }
      | Case { bind; body } ->
        let bind = h bind in
        let body = List.map ~f:h body in
        Case { bind; body }
      | Prod es ->
        let es = List.map ~f:h es in
        Prod es
      | Proj { e; n } ->
        let e = h e in
        Proj { e; n }
      | Fold { typ; e } ->
        let e = h e in
        let typ = incr_free_type_vars_t n ~depth typ in
        Fold { typ; e }
      | Unfold e ->
        let e = h e in
        Unfold e
    in
    let typ = incr_free_type_vars_t n ~depth typ in
    Typechecked.Expr.Info { typ; e; tag }
  in
  h_e e ~depth:0
;;
*)

let ftvs ts ~delta_depth =
  let next_idx = ref 0 in
  let next_idx () =
    let v = !next_idx in
    incr next_idx;
    v
  in
  let rec h_t t ~depth =
    let open Typechecked.Type in
    match t with
    | Info (tag, Typ pt) ->
      let ftvs_pt, pt = h_pt pt ~depth ~flin:(fun pt -> Info (tag, Typ pt)) in
      ftvs_pt, Info (tag, Typ pt)
    | Info (tag, Lin pt) ->
      let ftvs_pt, pt = h_pt pt ~depth ~flin:(fun pt -> Info (tag, Lin pt)) in
      ftvs_pt, Info (tag, Lin pt)
  and h_pt pt ~depth ~flin =
    match pt with
    | Int -> [], Int
    | Var i ->
      if i < depth then [], Var i else [ flin (Var (i - depth)) ], Var (next_idx ())
    | Unit -> [], Unit
    | Fun { foralls; args; ret } ->
      let depth = depth + foralls in
      let ftvs_args, args =
        List.fold_map args ~init:[] ~f:(fun ftvs arg ->
          let ftvs_arg, arg = h_t arg ~depth in
          ftvs_arg @ ftvs, arg)
      in
      let ftvs_ret, ret = h_t ~depth ret in
      ftvs_ret @ ftvs_args, Fun { foralls; args; ret }
    | Ref t ->
      let ftvs_t, t = h_t t ~depth in
      ftvs_t, Ref t
    | Variant ts ->
      let ftvs_ts, ts =
        List.fold_map ts ~init:[] ~f:(fun ftvs t ->
          let ftvs_t, t = h_t t ~depth in
          ftvs_t @ ftvs, t)
      in
      ftvs_ts, Variant ts
    | Prod ts ->
      let ftvs_ts, ts =
        List.fold_map ts ~init:[] ~f:(fun ftvs t ->
          let ftvs_t, t = h_t t ~depth in
          ftvs_t @ ftvs, t)
      in
      ftvs_ts, Prod ts
    | Rec t ->
      let ftvs_t, t = h_t t ~depth:(depth + 1) in
      ftvs_t, Rec t
  in
  List.fold_map ts ~init:[] ~f:(fun ftvs (pattern, t) ->
    let ftvs_t, t = h_t t ~depth:delta_depth in
    ftvs_t @ ftvs, (pattern, t))
;;

let fvs e ~gamma_depth =
  let next_idx = ref 0 in
  let next_idx () =
    let v = !next_idx in
    incr next_idx;
    v
  in
  let rec h_e e ~gamma_depth ~delta_depth =
    let h = h_e ~gamma_depth ~delta_depth in
    let (Typechecked.Expr.Info { typ; e; tag }) = e in
    let fvs, e =
      match e with
      | Int i -> [], Typechecked.Expr.Int i
      | Unit -> [], Unit
      | Binop (e1, e2, op) ->
        let fvs_e1, e1 = h e1 in
        let fvs_e2, e2 = h e2 in
        fvs_e1 @ fvs_e2, Binop (e1, e2, op)
      | If0 (e1, e2, e3) ->
        let fvs_e1, e1 = h e1 in
        let fvs_e2, e2 = h e2 in
        let fvs_e3, e3 = h e3 in
        fvs_e1 @ fvs_e2 @ fvs_e3, If0 (e1, e2, e3)
      | Let { var; bind; body } ->
        let incr = pattern_depth var in
        let fvs_bind, bind = h bind in
        let fvs_body, body = h_e body ~gamma_depth:(gamma_depth + incr) ~delta_depth in
        fvs_bind @ fvs_body, Let { var; bind; body }
      | Var i ->
        if i < gamma_depth
        then [], Var i
        else (
          let typ_to_subst_later = Typechecked.Type.Info (tag, Typ (Var (-1))) in
          ( [ Typechecked.Expr.Info
                { typ = incr_free_type_vars_t (-1 * delta_depth) typ
                ; e = Var (i - gamma_depth)
                ; tag
                }
            ]
          , Proj
              { n = next_idx ()
              ; e =
                  Info
                    { tag
                    ; typ = typ_to_subst_later
                    ; e =
                        Deref
                          (Info
                             { tag
                             ; typ = Info (tag, Typ (Ref typ_to_subst_later))
                             ; e = Var gamma_depth
                             })
                    }
              } ))
      | Coderef i -> [], Coderef i
      | Global i -> [], Global i
      | Lambda { foralls; args; body } ->
        let gamma_incr =
          List.sum (module Int) args ~f:(fun (pattern, _) -> pattern_depth pattern)
        in
        let fvs_body, body =
          h_e
            body
            ~gamma_depth:(gamma_depth + gamma_incr)
            ~delta_depth:(delta_depth + foralls)
        in
        fvs_body, Lambda { foralls; args; body }
      | Apply { f; inst; args } ->
        let fvs_f, f = h f in
        let fvs_args, args =
          List.fold_map args ~init:[] ~f:(fun fvs arg ->
            let fvs_arg, arg = h arg in
            fvs @ fvs_arg, arg)
        in
        fvs_f @ fvs_args, Apply { f; inst; args }
      | New e ->
        let fvs_e, e = h e in
        fvs_e, New e
      | New_lin typ -> [], New_lin typ
      | Deref e ->
        let fvs_e, e = h e in
        fvs_e, Deref e
      | Assign { ref; value } ->
        let fvs_ref, ref = h ref in
        let fvs_value, value = h value in
        fvs_ref @ fvs_value, Assign { ref; value }
      | Inj { n; typ; value } ->
        let fvs_value, value = h value in
        fvs_value, Inj { n; typ; value }
      | Case { bind; body } ->
        let fvs_bind, bind = h bind in
        let fvs_body, body =
          List.fold_map body ~init:[] ~f:(fun fvs e ->
            let fvs_e, e = h_e e ~gamma_depth:(gamma_depth + 1) ~delta_depth in
            fvs @ fvs_e, e)
        in
        fvs_bind @ fvs_body, Case { bind; body }
      | Prod es ->
        let fvs_es, es =
          List.fold_map es ~init:[] ~f:(fun fvs e ->
            let fvs_e, e = h e in
            fvs @ fvs_e, e)
        in
        fvs_es, Prod es
      | Proj { e; n } ->
        let fvs_e, e = h e in
        fvs_e, Proj { e; n }
      | Fold { typ; e } ->
        let fvs_e, e = h e in
        fvs_e, Fold { typ; e }
      | Unfold e ->
        let fvs_e, e = h e in
        fvs_e, Unfold e
    in
    fvs, Typechecked.Expr.Info { typ; e; tag }
  in
  h_e e ~gamma_depth ~delta_depth:0
;;

let rec subst_env_type_in_typ env_type_in_ref typ =
  match (typ : Typechecked.Type.t) with
  | Info (tag, Lin pt) ->
    subst_env_type_in_pretype env_type_in_ref pt ~flin:(fun pt ->
      Typechecked.Type.Info (tag, Lin pt))
  | Info (tag, Typ pt) ->
    subst_env_type_in_pretype env_type_in_ref pt ~flin:(fun pt ->
      Typechecked.Type.Info (tag, Typ pt))

and subst_env_type_in_pretype env_type_in_ref pretype ~flin =
  match pretype with
  | Var n when n = -1 -> env_type_in_ref
  | Int | Unit | Var _ | Fun _ -> flin pretype
  | Ref t -> flin (Ref (subst_env_type_in_typ env_type_in_ref t))
  | Variant ts -> flin (Variant (List.map ts ~f:(subst_env_type_in_typ env_type_in_ref)))
  | Prod ts -> flin (Prod (List.map ts ~f:(subst_env_type_in_typ env_type_in_ref)))
  | Rec t -> flin (Rec (subst_env_type_in_typ env_type_in_ref t))
;;

let rec subst_env_type_in_body env_type_in_ref e =
  let h = subst_env_type_in_body env_type_in_ref in
  let h_typ typ = subst_env_type_in_typ env_type_in_ref typ in
  let (Typechecked.Expr.Info { typ; e; tag }) = e in
  let typ = h_typ typ in
  let e =
    match e with
    | Int _ | Unit | Var _ | Coderef _ | Global _ -> e
    | Binop (e1, e2, op) ->
      let e1 = h e1 in
      let e2 = h e2 in
      Binop (e1, e2, op)
    | If0 (e1, e2, e3) ->
      let e1 = h e1 in
      let e2 = h e2 in
      let e3 = h e3 in
      If0 (e1, e2, e3)
    | Let { var; bind; body } ->
      let bind = h bind in
      let body = h body in
      Let { var; bind; body }
    | Lambda { foralls; args; body } ->
      let args = List.map args ~f:(fun (pattern, typ) -> pattern, h_typ typ) in
      let body = h body in
      Lambda { foralls; args; body }
    | Apply { f; inst; args } ->
      let f = h f in
      let inst = List.map inst ~f:h_typ in
      let args = List.map args ~f:h in
      Apply { f; inst; args }
    | New e -> New (h e)
    | New_lin typ -> New_lin (h_typ typ)
    | Deref e -> Deref (h e)
    | Assign { ref; value } ->
      let ref = h ref in
      let value = h value in
      Assign { ref; value }
    | Inj { n; typ; value } ->
      let typ = List.map ~f:h_typ typ in
      let value = h value in
      Inj { n; typ; value }
    | Case { bind; body } ->
      let bind = h bind in
      let body = List.map ~f:h body in
      Case { bind; body }
    | Prod es -> Prod (List.map ~f:h es)
    | Proj { e; n } ->
      let e = h e in
      Proj { e; n }
    | Fold { typ; e } ->
      let typ = h_typ typ in
      let e = h e in
      Fold { typ; e }
    | Unfold e -> Unfold (h e)
  in
  Typechecked.Expr.Info { typ; e; tag }
;;

let hoist_e e ~next_idx ~var_depth ~incr_map =
  let rec hoist_e e ~next_idx ~var_depth ~incr_map =
    let open Hoisted.Expr in
    let (Typechecked.Expr.Info { tag; typ; e }) = e in
    let e, fs =
      match e with
      | Int i -> Int i, []
      | Binop (e1, e2, op) ->
        let e1, e1_f = hoist_e e1 ~next_idx ~var_depth ~incr_map in
        let e2, e2_f =
          hoist_e e2 ~next_idx:(next_idx + List.length e1_f) ~var_depth ~incr_map
        in
        Binop (e1, e2, op), e1_f @ e2_f
      | If0 (e1, e2, e3) ->
        let e1, e1_f = hoist_e e1 ~next_idx ~var_depth ~incr_map in
        let e2, e2_f =
          hoist_e e2 ~next_idx:(next_idx + List.length e1_f) ~var_depth ~incr_map
        in
        let e3, e3_f =
          hoist_e
            e3
            ~next_idx:(next_idx + List.length e1_f + List.length e2_f)
            ~var_depth
            ~incr_map
        in
        If0 (e1, e2, e3), e1_f @ e2_f @ e3_f
      | Let { var; bind; body } ->
        let incr = pattern_depth var in
        let bind, bind_f = hoist_e bind ~next_idx ~var_depth ~incr_map in
        let body, body_f =
          hoist_e
            body
            ~next_idx:(next_idx + List.length bind_f)
            ~var_depth:(var_depth + incr)
            ~incr_map
        in
        Let { var; bind; body }, bind_f @ body_f
      | Var i -> Var i, []
      | Coderef i ->
        ( Coderef
            { f = i
            ; env = Info { tag; typ = Hoisted.Type.Info (tag, Typ Unit); e = Unit }
            ; type_insts = []
            }
        , [] )
      | Global i -> Global i, []
      | Unit -> Unit, []
      | Lambda { foralls; args; body } ->
        let gamma_depth =
          List.sum (module Int) args ~f:(fun (pattern, _) -> pattern_depth pattern)
        in
        let free_variables, body = fvs body ~gamma_depth in
        let free_variable_types =
          List.map free_variables ~f:(fun (Typechecked.Expr.Info { typ; _ }) -> typ)
        in
        let free_variables =
          List.map free_variables ~f:(fun (Typechecked.Expr.Info { e; tag; typ }) ->
            match e with
            | Var i ->
              Hoisted.Expr.Info { tag; e = Var i; typ = convert_type ~incr_map typ }
            | _ -> raise_s [%message "Hoisted non-variable"])
        in
        let env_type_in_ref =
          Typechecked.Type.Info (tag, Typ (Prod free_variable_types))
        in
        let body = subst_env_type_in_body env_type_in_ref body in
        let args =
          ( Hoisted.Pattern_binding.Variable
          , Typechecked.Type.Info (tag, Typ (Ref env_type_in_ref)) )
          :: args
        in
        let free_type_variables, args = ftvs args ~delta_depth:foralls in
        let count = List.length free_type_variables in
        let foralls = count + foralls in
        let free_type_variables =
          List.map ~f:(convert_type ~incr_map) free_type_variables
        in
        let body, body_f =
          hoist_e
            body
            ~next_idx
            ~var_depth:(gamma_depth + 1)
            ~incr_map:(Incr_map.add_bindings count incr_map)
        in
        let incr_map = Incr_map.empty |> Incr_map.add_bindings foralls in
        let env_type_in_ref =
          match
            List.hd_exn args
            |> snd
            |> incr_free_type_vars_t (-1 * foralls)
            |> convert_type ~incr_map
          with
          | Info (_, Typ (Ref env)) -> env
          | _ -> raise_s [%message "BUG: env type was not a reference"]
        in
        let args =
          List.map
            ~f:(fun (pattern, typ) ->
              pattern, convert_type ~incr_map:(Incr_map.add_bindings count incr_map) typ)
            args
        in
        let func = Hoisted.Module.{ foralls; args; body } in
        ( Coderef
            { f = next_idx + List.length body_f
            ; env =
                Info
                  { tag
                  ; typ = Info (tag, Typ (Ref env_type_in_ref))
                  ; e = New (Info { tag; typ = env_type_in_ref; e = Prod free_variables })
                  }
            ; type_insts = free_type_variables
            }
        , body_f @ [ func, tag ] )
      | Apply { f; inst; args } ->
        let f, f_f = hoist_e f ~next_idx ~var_depth ~incr_map in
        let incr_map = Incr_map.incr incr_map in
        let args_f, args =
          List.fold_map
            ~init:[]
            ~f:(fun fs e ->
              let e, e_f =
                hoist_e
                  e
                  ~next_idx:(next_idx + List.length f_f + List.length fs)
                  ~var_depth:(var_depth + 1)
                  ~incr_map
              in
              fs @ e_f, e)
            args
        in
        let inst = List.map ~f:(convert_type ~incr_map) inst in
        Apply { f; inst; args }, f_f @ args_f
      | New e ->
        let e, e_f = hoist_e e ~next_idx ~var_depth ~incr_map in
        New e, e_f
      | New_lin typ ->
        let typ = convert_type typ ~incr_map in
        New_lin typ, []
      | Deref e ->
        let e, e_f = hoist_e e ~next_idx ~var_depth ~incr_map in
        Deref e, e_f
      | Assign { ref; value } ->
        let ref, ref_f = hoist_e ref ~next_idx ~var_depth ~incr_map in
        let value, value_f =
          hoist_e value ~next_idx:(next_idx + List.length ref_f) ~var_depth ~incr_map
        in
        Assign { ref; value }, ref_f @ value_f
      | Inj { n; typ; value } ->
        let typ = List.map typ ~f:(convert_type ~incr_map) in
        let value, value_f = hoist_e value ~next_idx ~var_depth ~incr_map in
        Inj { n; typ; value }, value_f
      | Case { bind; body } ->
        let bind, bind_f = hoist_e bind ~next_idx ~var_depth ~incr_map in
        let body_f, body =
          List.fold_map
            ~init:[]
            ~f:(fun fs e ->
              let e, e_f =
                hoist_e
                  e
                  ~next_idx:(next_idx + List.length bind_f + List.length fs)
                  ~var_depth
                  ~incr_map
              in
              fs @ e_f, e)
            body
        in
        Case { bind; body }, bind_f @ body_f
      | Prod es ->
        let fs, es =
          List.fold_map
            ~init:[]
            ~f:(fun fs e ->
              let e, e_f =
                hoist_e e ~next_idx:(next_idx + List.length fs) ~var_depth ~incr_map
              in
              fs @ e_f, e)
            es
        in
        Prod es, fs
      | Proj { e; n } ->
        let e, e_f = hoist_e e ~next_idx ~var_depth ~incr_map in
        Proj { e; n }, e_f
      | Fold { typ; e } ->
        let typ = convert_type typ ~incr_map in
        let e, e_f = hoist_e e ~next_idx ~var_depth ~incr_map in
        Fold { typ; e }, e_f
      | Unfold e ->
        let e, e_f = hoist_e e ~next_idx ~var_depth ~incr_map in
        Unfold e, e_f
    in
    let typ = convert_type ~incr_map typ in
    Info { tag; typ; e }, fs
  in
  hoist_e e ~next_idx ~var_depth ~incr_map
;;

let rec hoist_module m ~hoisted ~next_idx : Hoisted.Module.t =
  let open Hoisted.Module in
  match (m : Typechecked.Module.t) with
  | LetIm ({ typ; mod_name; fun_name }, m, tag) ->
    let incr_map = Incr_map.empty |> Incr_map.add_bindings typ.foralls in
    let typ =
      Hoisted.Funtype.
        { foralls = typ.foralls
        ; args = Info (tag, Typ Unit) :: List.map ~f:(convert_type ~incr_map) typ.args
        ; ret = convert_type typ.ret ~incr_map
        }
    in
    let m = hoist_module m ~hoisted ~next_idx in
    LetIm ({ typ; mod_name; fun_name }, m, tag)
  | LetEx (s, { foralls; args; body }, m, tag) ->
    let incr_map = Incr_map.empty |> Incr_map.add_bindings foralls in
    let args =
      (Hoisted.Pattern_binding.Variable, Hoisted.Type.Info (tag, Typ Unit))
      :: List.map ~f:(fun (pattern, typ) -> pattern, convert_type ~incr_map typ) args
    in
    let var_depth =
      List.sum (module Int) ~f:(fun (pattern, _) -> pattern_depth pattern) args
    in
    let body, body_f = hoist_e body ~next_idx ~var_depth ~incr_map in
    let m =
      hoist_module m ~hoisted:(hoisted @ body_f) ~next_idx:(next_idx + List.length body_f)
    in
    LetEx (s, { foralls; args; body }, m, tag)
  | Global (e, m, tag) ->
    let e, e_f = hoist_e e ~next_idx ~var_depth:0 ~incr_map:Incr_map.empty in
    let m =
      hoist_module m ~hoisted:(hoisted @ e_f) ~next_idx:(next_idx + List.length e_f)
    in
    Global (e, m, tag)
  | Body e ->
    let e, e_f = hoist_e e ~next_idx ~var_depth:0 ~incr_map:Incr_map.empty in
    let hoisted = hoisted @ e_f in
    let main_fun = MainFun { foralls = 0; args = []; body = e } in
    List.fold_right hoisted ~init:main_fun ~f:(fun (func, tag) rest ->
      LetFun (func, rest, tag))
;;

let rec function_count m =
  match (m : Typechecked.Module.t) with
  | LetIm (_, m, _) -> 1 + function_count m
  | LetEx (_, _, m, _) -> 1 + function_count m
  | Global (_, m, _) -> function_count m
  | Body _ -> 0
;;

let hoist m ~source_printer:_ =
  Or_error.return (hoist_module m ~hoisted:[] ~next_idx:(function_count m))
;;
