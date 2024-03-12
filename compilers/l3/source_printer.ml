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
  | Info (_, t) ->
    (match t with
     | Int -> None
     | Unit -> None
     | Prod ts -> ts |> List.map ~f:h |> first_some_list
     | Fun { foralls = _; args; ret } -> ret :: args |> List.map ~f:h |> first_some_list
     | Bang t -> h t
     | Ptr _ -> None
     | Cap (_, t, _) -> h t
     | Ref (_, t, _, _) -> h t
     | Exists (_, t) -> h t)
;;

let rec get_source_expr tagged tag_to_find =
  let open Tagged.Expr in
  let h x = get_source_expr x tag_to_find in
  match tagged with
  | Info (tag, _) when Tag.equal tag tag_to_find ->
    tagged |> untag_e |> Source.Expr.sexp_of_t |> Sexp.to_string |> Option.return
  | Info (_, e) ->
    (match e with
     | Int _ -> None
     | Binop (e1, e2, _) -> Option.first_some (h e1) (h e2)
     | Unit -> None
     | LetUnit { bind; body } -> Option.first_some (h bind) (h body)
     | Prod es -> es |> List.map ~f:h |> first_some_list
     | LetProd { vars = _; bind; body } -> Option.first_some (h bind) (h body)
     | Var _ -> None
     | Apply { f; args } -> h f :: List.map ~f:h args |> first_some_list
     | Bang e -> h e
     | LetBang { var = _; bind; body } -> Option.first_some (h bind) (h body)
     | Dupl e -> h e
     | Drop e -> h e
     | New (e, _) -> h e
     | Free e -> h e
     | Swap (e1, e2) -> [ e1; e2 ] |> List.map ~f:h |> first_some_list
     | Join e -> h e
     | Split e -> h e
     | Inst (e, _) -> h e
     | Pack (_, e) -> h e
     | Unpack { locvar = _; var = _; package; body } ->
       Option.first_some (h package) (h body))
;;

let rec get_source tagged tag_to_find =
  let open Tagged.Module in
  let he x = get_source_expr x tag_to_find in
  let ht x = get_source_typ x tag_to_find in
  let h x = get_source x tag_to_find in
  match tagged with
  | LetIm ({ typ; mod_name = _; fun_name = _ }, m) -> Option.first_some (ht typ) (h m)
  | LetEx (_, { foralls = _; args; body }, m) ->
    (he body :: List.map ~f:(fun (_, t) -> ht t) args) @ [ h m ] |> first_some_list
  | Body e -> he e
;;
