open! Core
open! Syntax
open Tagging

type t = Tagged.Module.t

let create x = x
let first_some_list = List.fold_left ~init:None ~f:Option.first_some

let rec get_source_typ tagged tag_to_find =
  let open Tagged.Type in
  let h x = get_source_typ x tag_to_find in
  match tagged with
  | Info (tag, _) when Tag.equal tag tag_to_find ->
    tagged |> untag_t |> Source.Type.sexp_of_t |> Sexp.to_string |> Option.return
  | Info (_, Lin t) | Info (_, Typ t) ->
    (match t with
     | Int -> None
     | Var _ -> None
     | Unit -> None
     | Fun { foralls = _; args; ret } -> ret :: args |> List.map ~f:h |> first_some_list
     | Ref t -> h t
     | Variant ts -> ts |> List.map ~f:h |> first_some_list
     | Prod ts -> ts |> List.map ~f:h |> first_some_list
     | Rec (_, t) -> h t)
;;

let rec get_source_expr tagged tag_to_find =
  let open Tagged.Expr in
  let h x = get_source_expr x tag_to_find in
  let ht x = get_source_typ x tag_to_find in
  match tagged with
  | Info (tag, _) when Tag.equal tag tag_to_find ->
    tagged |> untag_e |> Source.Expr.sexp_of_t |> Sexp.to_string |> Option.return
  | Info (_, e) ->
    (match e with
     | Int _ -> None
     | Binop (e1, e2, _) -> Option.first_some (h e1) (h e2)
     | If0 (e1, e2, e3) -> [ h e1; h e2; h e3 ] |> first_some_list
     | Let { var = _; bind; body } -> Option.first_some (h bind) (h body)
     | Var _ -> None
     | Unit -> None
     | Lambda { foralls = _; args; body } ->
       h body :: List.map ~f:(fun (_, t) -> ht t) args |> first_some_list
     | Apply { f; inst; args } ->
       h f :: (List.map ~f:ht inst @ List.map ~f:h args) |> first_some_list
     | New t -> h t
     | New_lin typ -> ht typ
     | Deref t -> h t
     | Assign { ref; value } -> Option.first_some (h ref) (h value)
     | Inj { n = _; typ; value } -> h value :: List.map ~f:ht typ |> first_some_list
     | Case { var = _; bind; body } -> bind :: body |> List.map ~f:h |> first_some_list
     | Prod ts -> ts |> List.map ~f:h |> first_some_list
     | Proj { e; n = _ } -> h e
     | Fold { typ; e } -> Option.first_some (ht typ) (h e)
     | Unfold t -> h t)
;;

let rec get_source tagged tag_to_find =
  let open Tagged.Module in
  let he x = get_source_expr x tag_to_find in
  let ht x = get_source_typ x tag_to_find in
  let h x = get_source x tag_to_find in
  match tagged with
  | LetIm ({ typ; mod_name; fun_name }, m, tag) when Tag.equal tag tag_to_find ->
    let typ =
      Source.Funtype.
        { foralls = typ.foralls
        ; args = List.map ~f:untag_t typ.args
        ; ret = untag_t typ.ret
        }
    in
    LetIm ({ typ; mod_name; fun_name }, untag m)
    |> Source.Module.sexp_of_t
    |> Sexp.to_string
    |> Option.return
  | LetIm ({ typ; mod_name = _; fun_name = _ }, m, _) ->
    List.map ~f:ht typ.args @ [ ht typ.ret; h m ] |> first_some_list
  | LetEx (name, { foralls; args; body }, m, tag) when Tag.equal tag tag_to_find ->
    LetEx
      ( name
      , { foralls
        ; args = List.map ~f:(fun (s, t) -> s, untag_t t) args
        ; body = untag_e body
        }
      , untag m )
    |> Source.Module.sexp_of_t
    |> Sexp.to_string
    |> Option.return
  | LetEx (_, { foralls = _; args; body }, m, _) ->
    (he body :: List.map ~f:(fun (_, t) -> ht t) args) @ [ h m ] |> first_some_list
  | Global (name, e, m, tag) when Tag.equal tag tag_to_find ->
    Global (name, untag_e e, untag m)
    |> Source.Module.sexp_of_t
    |> Sexp.to_string
    |> Option.return
  | Global (_, e, m, _) -> Option.first_some (he e) (h m)
  | Body e -> he e
;;
