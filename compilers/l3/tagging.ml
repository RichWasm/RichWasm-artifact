open! Core
open! Syntax

let tag (m : Source.Module.t) : Tagged.Module.t =
  let counter = Tag.new_counter () in
  let wrap_t t = Tagged.Type.Info (counter (), t) in
  let wrap_e e = Tagged.Expr.Info (counter (), e) in
  let rec tag_t (t : Source.Type.t) : Tagged.Type.t =
    (match t with
     | Unit -> Tagged.Type.Unit
     | Int -> Int
     | Prod ts -> Prod (List.map ~f:tag_t ts)
     | Fun { foralls; args; ret } ->
       let args = List.map ~f:tag_t args in
       let ret = tag_t ret in
       Fun { foralls; args; ret }
     | Bang t -> Bang (tag_t t)
     | Ptr s -> Ptr s
     | Cap (s, t, n) -> Cap (s, tag_t t, n)
     | Ref (s, t, n, nativity) -> Ref (s, tag_t t, n, nativity)
     | Exists (s, t) -> Exists (s, tag_t t))
    |> wrap_t
  in
  let rec tag_e (e : Source.Expr.t) : Tagged.Expr.t =
    (match e with
     | Int i -> Int i
     | Binop (e1, e2, op) ->
       let e1 = tag_e e1 in
       let e2 = tag_e e2 in
       Binop (e1, e2, op)
     | Unit -> Unit
     | LetUnit { bind; body } ->
       let bind = tag_e bind in
       let body = tag_e body in
       LetUnit { bind; body }
     | Prod es -> Prod (List.map ~f:tag_e es)
     | LetProd { vars; bind; body } ->
       let bind = tag_e bind in
       let body = tag_e body in
       LetProd { vars; bind; body }
     | Var s -> Var s
     | Apply { f; args } ->
       let f = tag_e f in
       let args = List.map ~f:tag_e args in
       Apply { f; args }
     | Bang e -> Bang (tag_e e)
     | LetBang { var; bind; body } ->
       let bind = tag_e bind in
       let body = tag_e body in
       LetBang { var; bind; body }
     | Dupl e -> Dupl (tag_e e)
     | Drop e -> Drop (tag_e e)
     | New (e, n) -> New (tag_e e, n)
     | Free e -> Free (tag_e e)
     | Swap (e1, e2) -> Swap (tag_e e1, tag_e e2)
     | Join e -> Join (tag_e e)
     | Split e -> Split (tag_e e)
     | Inst (e, ss) -> Inst (tag_e e, ss)
     | Pack (s, e) -> Pack (s, tag_e e)
     | Unpack { locvar; var; package; body } ->
       let package = tag_e package in
       let body = tag_e body in
       Unpack { locvar; var; package; body })
    |> wrap_e
  in
  let rec tag_m (m : Source.Module.t) : Tagged.Module.t =
    match m with
    | LetIm ({ typ; mod_name; fun_name }, m) ->
      LetIm ({ typ = tag_t typ; mod_name; fun_name }, tag_m m)
    | LetEx (s, { foralls; args; body }, m) ->
      let func =
        { Tagged.Module.args = List.map ~f:(fun (s, t) -> s, tag_t t) args
        ; foralls
        ; body = tag_e body
        }
      in
      LetEx (s, func, tag_m m)
    | Body e -> Body (tag_e e)
  in
  tag_m m
;;

let rec untag_t (t : Tagged.Type.t) : Source.Type.t =
  let (Info (_, t)) = t in
  match t with
  | Int -> Int
  | Unit -> Unit
  | Prod ts -> Prod (List.map ~f:untag_t ts)
  | Fun { foralls; args; ret } ->
    let args = List.map ~f:untag_t args in
    let ret = untag_t ret in
    Fun { foralls; args; ret }
  | Bang t -> Bang (untag_t t)
  | Ptr s -> Ptr s
  | Cap (s, t, n) -> Cap (s, untag_t t, n)
  | Ref (s, t, n, nativity) -> Ref (s, untag_t t, n, nativity)
  | Exists (s, t) -> Exists (s, untag_t t)
;;

let rec untag_e (e : Tagged.Expr.t) : Source.Expr.t =
  let (Info (_, e)) = e in
  match e with
  | Int i -> Int i
  | Binop (e1, e2, op) ->
    let e1 = untag_e e1 in
    let e2 = untag_e e2 in
    Binop (e1, e2, op)
  | Unit -> Unit
  | LetUnit { bind; body } ->
    let bind = untag_e bind in
    let body = untag_e body in
    LetUnit { bind; body }
  | Prod es -> Prod (List.map ~f:untag_e es)
  | LetProd { vars; bind; body } ->
    let bind = untag_e bind in
    let body = untag_e body in
    LetProd { vars; bind; body }
  | Var s -> Var s
  | Apply { f; args } ->
    let f = untag_e f in
    let args = List.map ~f:untag_e args in
    Apply { f; args }
  | Bang e -> Bang (untag_e e)
  | LetBang { var; bind; body } ->
    let bind = untag_e bind in
    let body = untag_e body in
    LetBang { var; bind; body }
  | Dupl e -> Dupl (untag_e e)
  | Drop e -> Drop (untag_e e)
  | New (e, n) -> New (untag_e e, n)
  | Free e -> Free (untag_e e)
  | Swap (e1, e2) -> Swap (untag_e e1, untag_e e2)
  | Join e -> Join (untag_e e)
  | Split e -> Split (untag_e e)
  | Inst (e, ss) -> Inst (untag_e e, ss)
  | Pack (s, e) -> Pack (s, untag_e e)
  | Unpack { locvar; var; package; body } ->
    let package = untag_e package in
    let body = untag_e body in
    Unpack { locvar; var; package; body }
;;

let untag (m : Tagged.Module.t) : Source.Module.t =
  let rec untag_m (m : Tagged.Module.t) : Source.Module.t =
    match m with
    | LetIm ({ typ; mod_name; fun_name }, m) ->
      LetIm ({ typ = untag_t typ; mod_name; fun_name }, untag_m m)
    | LetEx (s, { foralls; args; body }, m) ->
      let func =
        { Source.Module.args = List.map ~f:(fun (s, t) -> s, untag_t t) args
        ; foralls
        ; body = untag_e body
        }
      in
      LetEx (s, func, untag_m m)
    | Body e -> Body (untag_e e)
  in
  untag_m m
;;
