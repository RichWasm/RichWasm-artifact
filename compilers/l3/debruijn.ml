open! Core
open! Syntax
open Or_error.Let_syntax

module Debruijn_env : sig
  type t

  val empty : t
  val add_var : string -> t -> t
  val add_fun : string -> t -> t
  val find : string -> t -> ([ `Var | `Fun ] * int) option
end = struct
  type t = (string * [ `Var | `Fun ]) list

  let empty = []
  let add_var s t = (s, `Var) :: t
  let add_fun s t = (s, `Fun) :: t

  let find s t =
    let found, (`Var _, `Fun fun_count) =
      List.fold_left
        t
        ~init:(None, (`Var 0, `Fun 0))
        ~f:(fun (found, (`Var var_count, `Fun fun_count)) (e, kind) ->
          let kind_result, new_counts =
            let eq = String.equal e s in
            match kind with
            | `Var ->
              Option.some_if eq (`Var var_count), (`Var (var_count + 1), `Fun fun_count)
            | `Fun ->
              Option.some_if eq (`Fun fun_count), (`Var var_count, `Fun (fun_count + 1))
          in
          match found with
          | Some _ -> found, new_counts
          | None -> kind_result, new_counts)
    in
    Option.map found ~f:(function
      | `Var n -> `Var, n
      | `Fun n -> `Fun, fun_count - (n + 1))
  ;;
end

let rec debruijn_t (t : Tagged.Type.t) ~delta : Debruijned.Type.t Or_error.t =
  let h = debruijn_t ~delta in
  let open Debruijned.Type in
  let (Info (tag, t)) = t in
  let%bind t =
    match t with
    | Unit -> return Unit
    | Int -> return Int
    | Prod ts ->
      let%bind ts = List.map ~f:h ts |> Or_error.all in
      return (Prod ts)
    | Fun { foralls; args; ret } ->
      let delta =
        List.fold_left
          ~init:delta
          ~f:(fun delta var -> Debruijn_env.add_var var delta)
          foralls
      in
      let%bind args = List.map ~f:(debruijn_t ~delta) args |> Or_error.all in
      let%bind ret = debruijn_t ~delta ret in
      return (Fun { foralls = List.length foralls; args; ret })
    | Bang t ->
      let%bind t = h t in
      return (Bang t)
    | Ptr variable ->
      (match Debruijn_env.find variable delta with
       | Some (`Var, i) -> return (Ptr i)
       | Some (`Fun, _) | None ->
         Or_error.error_s [%message "Unbound variable" (variable : string)])
    | Cap (variable, t, n) ->
      (match Debruijn_env.find variable delta with
       | Some (`Var, i) ->
         let%bind t = h t in
         return (Cap (i, t, n))
       | Some (`Fun, _) | None ->
         Or_error.error_s [%message "Unbound variable" (variable : string)])
    | Ref (variable, t, n, nativity) ->
      (match Debruijn_env.find variable delta with
       | Some (`Var, i) ->
         let%bind t = h t in
         return (Ref (i, t, n, nativity))
       | Some (`Fun, _) | None ->
         Or_error.error_s [%message "Unbound variable" (variable : string)])
    | Exists (s, t) ->
      let%bind t = debruijn_t t ~delta:(Debruijn_env.add_var s delta) in
      return (Exists t)
  in
  return (Info (tag, t))
;;

let rec debruijn_e (e : Tagged.Expr.t) ~delta ~gamma : Debruijned.Expr.t Or_error.t =
  let h = debruijn_e ~delta ~gamma in
  let open Debruijned.Expr in
  let (Info (tag, e)) = e in
  let%bind e =
    match e with
    | Int i -> return (Int i)
    | Binop (e1, e2, op) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      return (Binop (e1, e2, op))
    | Unit -> return Unit
    | LetUnit { bind; body } ->
      let%bind bind = h bind in
      let%bind body = h body in
      return (LetUnit { bind; body })
    | Prod es ->
      let%bind es = List.map ~f:h es |> Or_error.all in
      return (Prod es)
    (* CR: it would be good to check that there are no duplicate bindings *)
    | LetProd { vars; bind; body } ->
      let gamma, vars =
        List.fold_map
          ~init:gamma
          ~f:(fun gamma var ->
            match var with
            | `Unit -> gamma, `Unit
            | `Binding s -> Debruijn_env.add_var s gamma, `Binding)
          vars
      in
      let%bind bind = h bind in
      let%bind body = debruijn_e body ~delta ~gamma in
      return (LetProd { vars; bind; body })
    | Var variable ->
      (match Debruijn_env.find variable gamma with
       | Some (`Var, i) -> return (Var i)
       | Some (`Fun, i) -> return (Fun i)
       | None -> Or_error.error_s [%message "Unbound var" (variable : string)])
    | Apply { f; args } ->
      let%bind f = h f in
      let%bind args = List.map ~f:h args |> Or_error.all in
      return (Apply { f; args })
    | Bang e ->
      let%bind e = h e in
      return (Bang e)
    | LetBang { var; bind; body } ->
      let gamma, var =
        match var with
        | `Unit -> gamma, `Unit
        | `Binding var -> Debruijn_env.add_var var gamma, `Binding
      in
      let%bind bind = h bind in
      let%bind body = debruijn_e body ~delta ~gamma in
      return (LetBang { var; bind; body })
    | Dupl e ->
      let%bind e = h e in
      return (Dupl e)
    | Drop e ->
      let%bind e = h e in
      return (Drop e)
    | New (e, n) ->
      let%bind e = h e in
      return (New (e, n))
    | Free e ->
      let%bind e = h e in
      return (Free e)
    | Swap (e1, e2) ->
      let%bind e1 = h e1 in
      let%bind e2 = h e2 in
      return (Swap (e1, e2))
    | Join e ->
      let%bind e = h e in
      return (Join e)
    | Split e ->
      let%bind e = h e in
      return (Split e)
    | Inst (e, ss) ->
      let%bind insts =
        List.map
          ~f:(fun variable ->
            match Debruijn_env.find variable delta with
            | Some (`Var, i) -> return i
            | Some (`Fun, _) | None ->
              Or_error.error_s [%message "Unbound var" (variable : string)])
          ss
        |> Or_error.all
      in
      let%bind e = h e in
      return (Inst (e, insts))
    | Pack (variable, e) ->
      (match Debruijn_env.find variable delta with
       | Some (`Var, i) ->
         let%bind e = h e in
         return (Pack (i, e))
       | Some (`Fun, _) | None ->
         Or_error.error_s [%message "Unbound var" (variable : string)])
    | Unpack { locvar; var; package; body } ->
      let delta = Debruijn_env.add_var locvar delta in
      let gamma, var =
        match var with
        | `Unit -> gamma, `Unit
        | `Binding var -> Debruijn_env.add_var var gamma, `Binding
      in
      let%bind package = h package in
      let%bind body = debruijn_e body ~delta ~gamma in
      return (Unpack { var; package; body })
  in
  return (Info (tag, e))
;;

let rec debruijn_m (m : Tagged.Module.t) ~gamma ~source_printer
  : Debruijned.Module.t Or_error.t
  =
  let open Debruijned.Module in
  match m with
  | LetIm ({ typ; mod_name; fun_name }, m) ->
    let delta = Debruijn_env.empty in
    let%bind typ = debruijn_t typ ~delta in
    let gamma = Debruijn_env.add_fun fun_name gamma in
    let%bind m = debruijn_m m ~gamma ~source_printer in
    return (LetIm ({ typ; mod_name; fun_name }, m))
  | LetEx (s, { foralls; args; body }, m) ->
    let delta =
      List.fold_left foralls ~init:Debruijn_env.empty ~f:(fun delta var ->
        Debruijn_env.add_var var delta)
    in
    let gamma_e, args =
      List.fold_map
        ~init:gamma
        ~f:(fun gamma (var, typ) ->
          match var with
          | `Unit ->
            let arg =
              let%bind typ = debruijn_t ~delta typ in
              return (`Unit, typ)
            in
            gamma, arg
          | `Binding var ->
            let gamma = Debruijn_env.add_var var gamma in
            let arg =
              let%bind typ = debruijn_t ~delta typ in
              return (`Binding, typ)
            in
            gamma, arg)
        args
    in
    let%bind args = Or_error.all args in
    let%bind body = debruijn_e body ~delta ~gamma:gamma_e in
    let func = { foralls = List.length foralls; args; body } in
    let%bind m = debruijn_m m ~gamma:(Debruijn_env.add_fun s gamma) ~source_printer in
    return (LetEx (s, func, m))
  | Body e ->
    let%bind e = debruijn_e e ~delta:Debruijn_env.empty ~gamma in
    return (Body e)
;;

let debruijn = debruijn_m ~gamma:Debruijn_env.empty
