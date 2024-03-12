open! Core
open! Syntax

let tag (m : Source.Module.t) : Tagged.Module.t =
  let counter = Tag.new_counter () in
  let wrap_t t = Tagged.Type.Info (counter (), t) in
  let wrap_e e = Tagged.Expr.Info (counter (), e) in
  let rec tag_t (t : Source.Type.t) : Tagged.Type.t =
    let tag_pt (pt : Source.Pretype.t) : Tagged.Pretype.t =
      match pt with
      | Int -> Int
      | Var s -> Var s
      | Unit -> Unit
      | Fun { foralls; args; ret } ->
        Fun { foralls; args = List.map ~f:tag_t args; ret = tag_t ret }
      | Ref t -> Ref (tag_t t)
      | Variant ts -> Variant (List.map ~f:tag_t ts)
      | Prod ts -> Prod (List.map ~f:tag_t ts)
      | Rec (s, t) -> Rec (s, tag_t t)
    in
    (match t with
     | Lin pt -> Lin (tag_pt pt)
     | Typ pt -> Typ (tag_pt pt))
    |> wrap_t
  in
  let rec tag_e (e : Source.Expr.t) : Tagged.Expr.t =
    (match e with
     | Int i -> Int i
     | Binop (e1, e2, op) -> Binop (tag_e e1, tag_e e2, op)
     | If0 (e1, e2, e3) -> If0 (tag_e e1, tag_e e2, tag_e e3)
     | Let { var; bind; body } -> Let { var; bind = tag_e bind; body = tag_e body }
     | Var s -> Var s
     | Unit -> Unit
     | Lambda { foralls; args; body } ->
       Lambda
         { foralls
         ; args = List.map ~f:(fun (s, t) -> s, tag_t t) args
         ; body = tag_e body
         }
     | Apply { f; inst; args } ->
       Apply { f = tag_e f; inst = List.map ~f:tag_t inst; args = List.map ~f:tag_e args }
     | New t -> New (tag_e t)
     | New_lin typ -> New_lin (tag_t typ)
     | Deref t -> Deref (tag_e t)
     | Assign { ref; value } -> Assign { ref = tag_e ref; value = tag_e value }
     | Inj { n; typ; value } ->
       Inj { n; typ = List.map ~f:tag_t typ; value = tag_e value }
     | Case { var; bind; body } ->
       Case { var; bind = tag_e bind; body = List.map ~f:tag_e body }
     | Prod ts -> Prod (List.map ~f:tag_e ts)
     | Proj { e; n } -> Proj { e = tag_e e; n }
     | Fold { typ; e } -> Fold { typ = tag_t typ; e = tag_e e }
     | Unfold t -> Unfold (tag_e t))
    |> wrap_e
  in
  let rec tag_m (m : Source.Module.t) : Tagged.Module.t =
    match m with
    | LetIm ({ typ; mod_name; fun_name }, m) ->
      let typ =
        Tagged.Funtype.
          { foralls = typ.foralls
          ; args = List.map ~f:tag_t typ.args
          ; ret = tag_t typ.ret
          }
      in
      LetIm ({ typ; mod_name; fun_name }, tag_m m, counter ())
    | LetEx (s, { foralls; args; body }, m) ->
      let func =
        { Tagged.Module.foralls
        ; args = List.map ~f:(fun (s, t) -> s, tag_t t) args
        ; body = tag_e body
        }
      in
      LetEx (s, func, tag_m m, counter ())
    | Global (name, e, m) -> Global (name, tag_e e, tag_m m, counter ())
    | Body e -> Body (tag_e e)
  in
  tag_m m
;;

let rec untag_t (t : Tagged.Type.t) : Source.Type.t =
  let untag_pt (pt : Tagged.Pretype.t) : Source.Pretype.t =
    match pt with
    | Int -> Int
    | Var s -> Var s
    | Unit -> Unit
    | Fun { foralls; args; ret } ->
      Fun { foralls; args = List.map ~f:untag_t args; ret = untag_t ret }
    | Ref t -> Ref (untag_t t)
    | Variant ts -> Variant (List.map ~f:untag_t ts)
    | Prod ts -> Prod (List.map ~f:untag_t ts)
    | Rec (s, t) -> Rec (s, untag_t t)
  in
  let (Info (_, t)) = t in
  match t with
  | Lin pt -> Lin (untag_pt pt)
  | Typ pt -> Typ (untag_pt pt)
;;

let rec untag_e (e : Tagged.Expr.t) : Source.Expr.t =
  let (Info (_, e)) = e in
  match e with
  | Int i -> Int i
  | Binop (e1, e2, op) -> Binop (untag_e e1, untag_e e2, op)
  | If0 (e1, e2, e3) -> If0 (untag_e e1, untag_e e2, untag_e e3)
  | Let { var; bind; body } -> Let { var; bind = untag_e bind; body = untag_e body }
  | Var s -> Var s
  | Unit -> Unit
  | Lambda { foralls; args; body } ->
    Lambda
      { foralls
      ; args = List.map ~f:(fun (s, t) -> s, untag_t t) args
      ; body = untag_e body
      }
  | Apply { f; inst; args } ->
    Apply
      { f = untag_e f; inst = List.map ~f:untag_t inst; args = List.map ~f:untag_e args }
  | New t -> New (untag_e t)
  | New_lin typ -> New_lin (untag_t typ)
  | Deref t -> Deref (untag_e t)
  | Assign { ref; value } -> Assign { ref = untag_e ref; value = untag_e value }
  | Inj { n; typ; value } ->
    Inj { n; typ = List.map ~f:untag_t typ; value = untag_e value }
  | Case { var; bind; body } ->
    Case { var; bind = untag_e bind; body = List.map ~f:untag_e body }
  | Prod ts -> Prod (List.map ~f:untag_e ts)
  | Proj { e; n } -> Proj { e = untag_e e; n }
  | Fold { typ; e } -> Fold { typ = untag_t typ; e = untag_e e }
  | Unfold t -> Unfold (untag_e t)
;;

let untag (m : Tagged.Module.t) : Source.Module.t =
  let rec untag_m (m : Tagged.Module.t) : Source.Module.t =
    match m with
    | LetIm ({ typ; mod_name; fun_name }, m, _) ->
      let typ =
        Source.Funtype.
          { foralls = typ.foralls
          ; args = List.map ~f:untag_t typ.args
          ; ret = untag_t typ.ret
          }
      in
      LetIm ({ typ; mod_name; fun_name }, untag_m m)
    | LetEx (s, { foralls; args; body }, m, _) ->
      let func =
        { Source.Module.foralls
        ; args = List.map ~f:(fun (s, t) -> s, untag_t t) args
        ; body = untag_e body
        }
      in
      LetEx (s, func, untag_m m)
    | Global (name, e, m, _) -> Global (name, untag_e e, untag_m m)
    | Body e -> Body (untag_e e)
  in
  untag_m m
;;
