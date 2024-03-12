open! Core
open! Syntax
open! Or_error.Let_syntax
open! Annotated

module Annotation_env : sig
  type t [@@deriving sexp]

  val empty : t
  val add_size : t -> t
  val add_delta : Qual.t * Size.t -> t -> t
  val find_delta_exn : int -> t -> Qual.t * Size.t
end = struct
  type t = (Qual.t * Size.t) list [@@deriving sexp]

  let rec incr_size = function
    | Size.Const n -> Size.Const n
    | Var n -> Var (n + 1)
    | Plus (s1, s2) -> Plus (incr_size s1, incr_size s2)
  ;;

  let empty = []
  let add_size t = List.map ~f:(fun (q, sz) -> q, incr_size sz) t
  let add_delta e t = e :: t
  let find_delta_exn i t = List.nth_exn t i
end

let rec get_quals_for_alpha i ts =
  let get_qual_in_pt i pt q =
    match (pt : Hoisted.Pretype.t) with
    | Var v when v = i -> return (Some q)
    | Int | Unit | Var _ | Exists_closure _ -> return None
    | Ref t -> get_quals_for_alpha i [ t ]
    | Variant ts -> get_quals_for_alpha i ts
    | Prod ts -> get_quals_for_alpha i ts
    | Rec t -> get_quals_for_alpha (i + 1) [ t ]
  in
  let get_qual_in_t i t =
    match (t : Hoisted.Type.t) with
    | Info (_, Typ pt) -> get_qual_in_pt i pt Annotated.Qual.Unr
    | Info (_, Lin pt) -> get_qual_in_pt i pt Annotated.Qual.Lin
  in
  List.fold ts ~init:(return None) ~f:(fun acc t ->
    let%bind acc = acc in
    let%bind q = get_qual_in_t i t in
    match acc, q with
    | None, None -> return None
    | Some q, None | None, Some q -> return (Some q)
    | Some q1, Some q2 ->
      if Annotated.Qual.equal q1 q2
      then return (Some q1)
      else
        error_s
          [%message
            "Inconsistent qualifiers for type variable"
              (q1 : Annotated.Qual.t)
              (q2 : Annotated.Qual.t)])
;;

let get_quals_for_alpha i ts =
  let%bind found_qual = get_quals_for_alpha i ts in
  Option.value found_qual ~default:Qual.Unr |> return
;;

let rec size_of_t t ~env =
  match (t : Hoisted.Type.t) with
  | Info (_, Typ pt) | Info (_, Lin pt) -> size_of_pt pt ~env

and size_of_pt pt ~env =
  let open Size in
  match (pt : Hoisted.Pretype.t) with
  | Int -> Const 32
  | Var v -> Annotation_env.find_delta_exn v env |> snd
  | Unit -> Const 0
  | Exists_closure _ -> Const 64
  | Ref _ -> Const 64
  | Variant _ -> Const 64
  | Prod ts -> List.fold ts ~init:(Const 0) ~f:(fun acc t -> Plus (acc, size_of_t t ~env))
  | Rec t -> size_of_t t ~env:(Annotation_env.add_delta (Qual.Unr, Size.Const (-1)) env)
;;

let abstractions_of_foralls ~foralls args =
  let%bind forall_alpha =
    List.init foralls ~f:(fun i ->
      let i = foralls - (i + 1) in
      let%bind qual_for_var = get_quals_for_alpha i args in
      return Abstraction.[ Size; Type (qual_for_var, Size.Var 0) ])
    |> Or_error.all
  in
  return (List.concat forall_alpha)
;;

let env_of_foralls ~env ~foralls =
  List.fold foralls ~init:env ~f:(fun env ->
      function
      | Abstraction.Size -> Annotation_env.add_size env
      | Type (q, sz) -> Annotation_env.add_delta (q, sz) env)
;;

let rec annotate_t t ~env ~source_printer =
  let open Annotated.Type in
  match (t : Hoisted.Type.t) with
  | Info (tag, Typ pt) ->
    let%bind pt = annotate_pt pt ~env ~source_printer in
    return (Info (tag, (Qual.Unr, pt)))
  | Info (tag, Lin pt) ->
    let%bind pt = annotate_pt pt ~env ~source_printer in
    return (Info (tag, (Qual.Lin, pt)))

and annotate_pt pt ~env ~source_printer =
  let open Annotated.Pretype in
  match (pt : Hoisted.Pretype.t) with
  | Int -> return Int
  | Var v -> return (Var v)
  | Unit -> return Unit
  | Exists_closure { foralls; args; ret } ->
    let%bind foralls = abstractions_of_foralls ~foralls args in
    let env = Annotation_env.add_delta (Qual.Unr, Size.Const 64) env in
    let env = env_of_foralls ~env ~foralls in
    let%bind args = List.map ~f:(annotate_t ~env ~source_printer) args |> Or_error.all in
    let%bind ret = annotate_t ret ~env ~source_printer in
    return (Exists_closure { foralls; args; ret })
  | Ref t ->
    let sz = size_of_t t ~env in
    let%bind t = annotate_t t ~env ~source_printer in
    return (Ref (sz, t))
  | Variant ts ->
    let%bind ts = List.map ~f:(annotate_t ~env ~source_printer) ts |> Or_error.all in
    return (Variant ts)
  | Prod ts ->
    let%bind ts = List.map ~f:(annotate_t ~env ~source_printer) ts |> Or_error.all in
    return (Prod ts)
  | Rec t ->
    let sz = size_of_t t ~env:(Annotation_env.add_delta (Qual.Unr, Size.Const 0) env) in
    let%bind q = get_quals_for_alpha 0 [ t ] in
    let%bind t =
      annotate_t t ~env:(Annotation_env.add_delta (q, sz) env) ~source_printer
    in
    return (Rec (q, t))
;;

let e_type e =
  match (e : Expr.t) with
  | Info { typ; _ } -> typ
;;

let rec annotate_e e ~env ~source_printer =
  let open Expr in
  let h = annotate_e ~env ~source_printer in
  let (Hoisted.Expr.Info { tag; e; typ }) = e in
  let%bind e =
    match e with
    | Int i -> return (Int i)
    | Binop (e1, e2, op) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      return (Binop (e1, e2, op))
    | If0 (e1, e2, e3) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      let%bind e3 = h e3 in
      return (If0 (e1, e2, e3))
    | Let { var; bind; body } ->
      let%bind bind = h bind in
      let%bind body = h body in
      return (Let { var; bind; body })
    | Var v -> return (Var v)
    | Global i -> return (Global i)
    | Unit -> return Unit
    | Coderef { f; env = packed_env; type_insts } ->
      let%bind packed_env = h packed_env in
      let%bind type_insts =
        List.map ~f:(annotate_t ~env ~source_printer) type_insts |> Or_error.all
      in
      return (Coderef { f; env = packed_env; type_insts })
    | Apply { f; inst; args } ->
      let%bind f = h f in
      let env = Annotation_env.add_delta (Unr, Const 64) env in
      let inst = List.map ~f:(fun t -> size_of_t ~env t, t) inst in
      let%bind inst =
        List.map
          ~f:(fun (sz, t) ->
            let%map t = annotate_t t ~env ~source_printer in
            sz, t)
          inst
        |> Or_error.all
      in
      let%bind args =
        List.map ~f:(annotate_e ~env ~source_printer) args |> Or_error.all
      in
      return (Apply { f; inst; args })
    | New e ->
      let%bind e = h e in
      return (New e)
    | New_lin typ ->
      let%bind typ = annotate_t typ ~env ~source_printer in
      return (New_lin typ)
    | Deref e ->
      let%bind e = h e in
      return (Deref e)
    | Assign { ref; value } ->
      let%bind ref = h ref in
      let%bind value = h value in
      return (Assign { ref; value })
    | Inj { n; typ; value } ->
      let%bind value = h value in
      let%bind typ = List.map ~f:(annotate_t ~env ~source_printer) typ |> Or_error.all in
      return (Inj { n; typ; value })
    | Case { bind; body } ->
      let%bind bind = h bind in
      let%bind body = List.map ~f:h body |> Or_error.all in
      return (Case { bind; body })
    | Prod ts ->
      let%bind ts = List.map ~f:h ts |> Or_error.all in
      return (Prod ts)
    | Proj { e; n } ->
      let%bind e = h e in
      return (Proj { e; n })
    | Fold { typ; e } ->
      let%bind typ = annotate_t typ ~env ~source_printer in
      let%bind e = h e in
      return (Fold { typ; e })
    | Unfold e ->
      let%bind e = h e in
      return (Unfold e)
  in
  let%bind typ = annotate_t typ ~env ~source_printer in
  return (Info { tag; typ; e })
;;

let rec annotate_m (m : Hoisted.Module.t) ~source_printer : Annotated.Module.t Or_error.t =
  let h_func Hoisted.Module.{ foralls; args; body } =
    let%bind foralls = abstractions_of_foralls ~foralls (List.map ~f:snd args) in
    let env = env_of_foralls ~env:Annotation_env.empty ~foralls in
    let%bind args =
      List.map
        ~f:(fun (pattern, typ) ->
          let%bind typ = annotate_t ~env ~source_printer typ in
          return (pattern, typ))
        args
      |> Or_error.all
    in
    let%bind body = annotate_e body ~env ~source_printer in
    let ret = e_type body in
    return Module.{ foralls; args; ret; body }
  in
  let open Module in
  match (m : Hoisted.Module.t) with
  | LetIm ({ typ; mod_name; fun_name }, m, tag) ->
    let%bind typ =
      let Hoisted.Funtype.{ foralls; args; ret } = typ in
      let%bind foralls = abstractions_of_foralls ~foralls args in
      let env = env_of_foralls ~env:Annotation_env.empty ~foralls in
      let%bind args =
        List.map ~f:(annotate_t ~env ~source_printer) args |> Or_error.all
      in
      let%bind ret = annotate_t ret ~env ~source_printer in
      return Funtype.{ foralls; args; ret }
    in
    let%bind m = annotate_m m ~source_printer in
    return (LetIm ({ typ; mod_name; fun_name }, m, tag))
  | LetEx (s, func, m, tag) ->
    let%bind func = h_func func in
    let%bind m = annotate_m m ~source_printer in
    return (LetEx (s, func, m, tag))
  | LetFun (func, m, tag) ->
    let%bind func = h_func func in
    let%bind m = annotate_m m ~source_printer in
    return (LetFun (func, m, tag))
  | Global (e, m, tag) ->
    let%bind e = annotate_e e ~env:Annotation_env.empty ~source_printer in
    let%bind m = annotate_m m ~source_printer in
    return (Global (e, m, tag))
  | MainFun func ->
    let%bind func = h_func func in
    return (MainFun func)
;;

let annotate m = annotate_m m
