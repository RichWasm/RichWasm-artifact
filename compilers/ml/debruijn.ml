open! Core
open! Syntax
open Or_error.Let_syntax

module Debruijn_env : sig
  type t

  val empty : t
  val add_var : string -> t -> t
  val add_global : string -> t -> t
  val add_fun : string -> t -> t
  val find : string -> t -> ([ `Var | `Glob | `Fun ] * int) option
end = struct
  type t = (string * [ `Var | `Glob | `Fun ]) list

  let empty = []
  let add_var s t = (s, `Var) :: t
  let add_global s t = (s, `Glob) :: t
  let add_fun s t = (s, `Fun) :: t

  let find s t =
    let found, (`Var _, `Glob glob_count, `Fun fun_count) =
      List.fold_left
        t
        ~init:(None, (`Var 0, `Glob 0, `Fun 0))
        ~f:(fun (found, (`Var var_count, `Glob glob_count, `Fun fun_count)) (e, kind) ->
          let kind_result, new_counts =
            let eq = String.equal e s in
            match kind with
            | `Var ->
              ( Option.some_if eq (`Var var_count)
              , (`Var (var_count + 1), `Glob glob_count, `Fun fun_count) )
            | `Glob ->
              ( Option.some_if eq (`Glob glob_count)
              , (`Var var_count, `Glob (glob_count + 1), `Fun fun_count) )
            | `Fun ->
              ( Option.some_if eq (`Fun fun_count)
              , (`Var var_count, `Glob glob_count, `Fun (fun_count + 1)) )
          in
          match found with
          | Some _ -> found, new_counts
          | None -> kind_result, new_counts)
    in
    Option.map found ~f:(function
      | `Var n -> `Var, n
      | `Glob n -> `Glob, glob_count - (n + 1)
      | `Fun n -> `Fun, fun_count - (n + 1))
  ;;
end

let rec debruijn_t (t : Tagged.Type.t) ~delta ~source_printer
  : Debruijned.Type.t Or_error.t
  =
  let h = debruijn_t ~delta ~source_printer in
  let (Info (tag, t)) = t in
  let debruijn_pt (pt : Tagged.Pretype.t) : Debruijned.Pretype.t Or_error.t =
    let open Debruijned.Pretype in
    match pt with
    | Int -> return Int
    | Var variable ->
      (match Debruijn_env.find variable delta with
       | Some (`Var, i) -> return (Var i)
       | Some (`Glob, _) | Some (`Fun, _) | None ->
         Or_error.error_s [%message "Unbound variable" (variable : string)])
    | Unit -> return Unit
    | Fun { foralls; args; ret } ->
      let delta =
        List.fold_left
          ~init:delta
          ~f:(fun delta var -> Debruijn_env.add_var var delta)
          foralls
      in
      let%bind args =
        List.map ~f:(debruijn_t ~delta ~source_printer) args |> Or_error.all
      in
      let%bind ret = debruijn_t ret ~delta ~source_printer in
      return (Fun { foralls = List.length foralls; args; ret })
    | Ref t ->
      let%bind t = h t in
      return (Ref t)
    | Variant ts ->
      let%bind ts = List.map ~f:h ts |> Or_error.all in
      return (Variant ts)
    | Prod ts ->
      let%bind ts = List.map ~f:h ts |> Or_error.all in
      return (Prod ts)
    | Rec (s, t) ->
      let%bind t = debruijn_t t ~delta:(Debruijn_env.add_var s delta) ~source_printer in
      return (Rec t)
  in
  let in_type = Source_printer.get_source source_printer tag in
  let error_tag = [%message (in_type : string option)] in
  let%bind t =
    let open Debruijned.Type in
    match t with
    | Lin pt ->
      let%bind pt = debruijn_pt pt |> Or_error.tag_s ~tag:error_tag in
      return (Lin pt)
    | Typ pt ->
      let%bind pt = debruijn_pt pt |> Or_error.tag_s ~tag:error_tag in
      return (Typ pt)
  in
  return (Debruijned.Type.Info (tag, t))
;;

let h_pattern var gamma =
  match (var : Tagged.Pattern_binding.t) with
  | Unit -> gamma, Debruijned.Pattern_binding.Unit
  | Variable var -> Debruijn_env.add_var var gamma, Variable
  | Tuple vars ->
    ( List.fold_left vars ~init:gamma ~f:(fun gamma var -> Debruijn_env.add_var var gamma)
    , Tuple (List.length vars) )
;;

let rec debruijn_e (e : Tagged.Expr.t) ~delta ~gamma ~source_printer
  : Debruijned.Expr.t Or_error.t
  =
  let h = debruijn_e ~delta ~gamma ~source_printer in
  let ht = debruijn_t ~delta ~source_printer in
  let (Info (tag, e)) = e in
  let e =
    let open Debruijned.Expr in
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
      let gamma, var = h_pattern var gamma in
      let%bind bind = h bind in
      let%bind body = debruijn_e body ~delta ~gamma ~source_printer in
      return (Let { var; bind; body })
    | Var variable ->
      (match Debruijn_env.find variable gamma with
       | Some (`Var, i) -> return (Var i)
       | Some (`Glob, i) -> return (Global i)
       | Some (`Fun, i) -> return (Coderef i)
       | None -> Or_error.error_s [%message "Unbound variable" (variable : string)])
    | Unit -> return Unit
    | Lambda { foralls; args; body } ->
      let delta =
        List.fold_left
          ~init:delta
          ~f:(fun delta var -> Debruijn_env.add_var var delta)
          foralls
      in
      let gamma, args =
        List.fold_map args ~init:gamma ~f:(fun gamma (var, typ) ->
          let gamma, var = h_pattern var gamma in
          let typ = debruijn_t typ ~delta ~source_printer in
          gamma, Or_error.map typ ~f:(fun typ -> var, typ))
      in
      let%bind args = Or_error.all args in
      let%bind body = debruijn_e body ~delta ~gamma ~source_printer in
      return (Lambda { foralls = List.length foralls; args; body })
    | Apply { f; inst; args } ->
      let%bind f = h f in
      let%bind inst = List.map ~f:ht inst |> Or_error.all in
      let%bind args = List.map ~f:h args |> Or_error.all in
      return (Apply { f; inst; args })
    | New t ->
      let%bind t = h t in
      return (New t)
    | New_lin typ ->
      let%bind typ = ht typ in
      return (New_lin typ)
    | Deref t ->
      let%bind t = h t in
      return (Deref t)
    | Assign { ref; value } ->
      let%bind ref = h ref in
      let%bind value = h value in
      return (Assign { ref; value })
    | Inj { n; typ; value } ->
      let%bind typ = List.map ~f:ht typ |> Or_error.all in
      let%bind value = h value in
      return (Inj { n; typ; value })
    | Case { var; bind; body } ->
      let gamma = Debruijn_env.add_var var gamma in
      let%bind bind = h bind in
      let%bind body =
        List.map ~f:(fun x -> debruijn_e x ~delta ~gamma ~source_printer) body
        |> Or_error.all
      in
      return (Case { bind; body })
    | Prod ts ->
      let%bind ts = List.map ~f:h ts |> Or_error.all in
      return (Prod ts)
    | Proj { e; n } ->
      let%bind e = h e in
      return (Proj { e; n })
    | Fold { typ; e } ->
      let%bind typ = ht typ in
      let%bind e = h e in
      return (Fold { typ; e })
    | Unfold t ->
      let%bind t = h t in
      return (Unfold t)
  in
  let in_expr = Source_printer.get_source source_printer tag in
  let%bind e = e |> Or_error.tag_s ~tag:[%message (in_expr : string option)] in
  return (Debruijned.Expr.Info (tag, e))
;;

let rec debruijn_m (m : Tagged.Module.t) ~gamma ~source_printer
  : Debruijned.Module.t Or_error.t
  =
  let open Debruijned.Module in
  match m with
  | LetIm ({ typ; mod_name; fun_name }, m, tag) ->
    let gamma = Debruijn_env.add_fun fun_name gamma in
    let delta = Debruijn_env.empty in
    let typ =
      let typ = Tagged.Type.Info (tag, Typ (Fun typ)) in
      Or_error.map (debruijn_t typ ~delta ~source_printer) ~f:(function
        | Debruijned.Type.Info (_, Typ (Fun typ)) -> typ
        | _ ->
          raise_s
            [%message
              "BUG: debruijning transformed a function type into a non-function type"])
    in
    let in_import = Source_printer.get_source source_printer tag in
    let%bind typ = typ |> Or_error.tag_s ~tag:[%message (in_import : string option)] in
    let%bind m = debruijn_m m ~gamma ~source_printer in
    return (LetIm ({ typ; mod_name; fun_name }, m, tag))
  | LetEx (s, { foralls; args; body }, m, tag) ->
    let delta =
      List.fold_left
        ~init:Debruijn_env.empty
        ~f:(fun delta var -> Debruijn_env.add_var var delta)
        foralls
    in
    let gamma_e, args =
      List.fold_map args ~init:gamma ~f:(fun gamma (var, typ) ->
        let gamma, var = h_pattern var gamma in
        let typ = debruijn_t typ ~delta ~source_printer in
        gamma, Or_error.map typ ~f:(fun typ -> var, typ))
    in
    let args = Or_error.all args in
    let body = debruijn_e body ~delta ~gamma:gamma_e ~source_printer in
    let in_exported_fun = Source_printer.get_source source_printer tag in
    let tag_error e =
      Or_error.tag_s e ~tag:[%message (in_exported_fun : string option)]
    in
    let%bind args = args |> tag_error in
    let%bind body = body |> tag_error in
    let func = { Debruijned.Module.foralls = List.length foralls; args; body } in
    let%bind m = debruijn_m m ~gamma:(Debruijn_env.add_fun s gamma) ~source_printer in
    return (LetEx (s, func, m, tag))
  | Global (global_name, e, m, tag) ->
    let%bind e =
      debruijn_e e ~delta:Debruijn_env.empty ~gamma ~source_printer
      |> Or_error.tag_s ~tag:[%message (global_name : string)]
    in
    let%bind m =
      debruijn_m m ~gamma:(Debruijn_env.add_global global_name gamma) ~source_printer
    in
    return (Global (e, m, tag))
  | Body e ->
    let e = debruijn_e e ~delta:Debruijn_env.empty ~gamma ~source_printer in
    let%bind e = e |> Or_error.tag_s ~tag:[%message "in module body"] in
    return (Body e)
;;

let debruijn = debruijn_m ~gamma:Debruijn_env.empty
