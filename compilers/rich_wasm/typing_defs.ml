open! Core
open Rich_wasm
open Or_error.Let_syntax

module type S = Solver.S

let incr_q n = function
  | Qual.QualC _ as q -> q
  | QualV v -> QualV (v + n)
;;

let rec incr_sz n = function
  | Size.SizeC _ as sz -> sz
  | SizeV v -> SizeV (v + n)
  | SizeP (sz1, sz2) -> SizeP (incr_sz n sz1, incr_sz n sz2)
;;

module Local_ctx = struct
  type t = (Type.t * Size.t) list [@@deriving equal, sexp]

  let rec apply_local_effect tl t =
    match tl with
    | [] -> return t
    | (i, typ) :: rest ->
      if List.length t > i
      then (
        let updated =
          List.mapi t ~f:(fun n (cur_typ, sz) -> if i = n then typ, sz else cur_typ, sz)
        in
        apply_local_effect rest updated)
      else
        Or_error.error_s
          [%message
            "local effect was beyond bounds of local context"
              ~ctx:(t : t)
              ~index:(i : int)]
  ;;
end

module Function_ctx = struct
  type t =
    { label : (Type.t list * Local_ctx.t) list
    ; ret : Type.t list option
    ; qual : (Qual.t list * Qual.t list) list
    ; size : (Size.t list * Size.t list) list
    ; typ_ : (Qual.t * Size.t * Heapable_const.t) list
    ; loc : int
    ; linear : Qual.t list list
    }

  let qual_solver t =
    let module Solver = (val Solver.create_constraint_checker ()) in
    let open Solver.Qual in
    List.iteri t.qual ~f:(fun i (q_leq, q_greater) ->
      let q = of_qual (QualV i) in
      let incr_q = incr_q (i + 1) in
      List.iter q_leq ~f:(fun q_leq ->
        let less = q_leq |> incr_q |> of_qual in
        assume_leq ~less ~greater:q);
      List.iter q_greater ~f:(fun q_greater ->
        let greater = q_greater |> incr_q |> of_qual in
        assume_leq ~less:q ~greater));
    (module Solver : S)
  ;;

  let size_solver t =
    let module Solver = (val Solver.create_constraint_checker ()) in
    let open Solver.Size in
    List.iteri t.size ~f:(fun i (sz_leq, sz_greater) ->
      let sz = of_size (SizeV i) in
      let incr_sz = incr_sz (i + 1) in
      List.iter sz_leq ~f:(fun sz_leq ->
        let less = sz_leq |> incr_sz |> of_size in
        assume_leq ~less ~greater:sz);
      List.iter sz_greater ~f:(fun sz_greater ->
        let greater = sz_greater |> incr_sz |> of_size in
        assume_leq ~less:sz ~greater);
      assume_leq ~less:(of_size (SizeC 0)) ~greater:sz);
    (module Solver : S)
  ;;

  let add_constraint constraint_ t =
    match (constraint_ : KindVar.t) with
    | Loc ->
      return
        { label =
            List.map t.label ~f:(fun (typs, ctx) ->
              let typs = List.map typs ~f:(Substitution.Loc.incr_unbound_in_t 1) in
              let ctx =
                List.map ctx ~f:(fun (typ, sz) ->
                  Substitution.Loc.incr_unbound_in_t 1 typ, sz)
              in
              typs, ctx)
        ; ret = Option.map t.ret ~f:(List.map ~f:(Substitution.Loc.incr_unbound_in_t 1))
        ; qual = t.qual
        ; size = t.size
        ; typ_ = t.typ_
        ; loc = t.loc + 1
        ; linear = t.linear
        }
    | Qual (less, greater) ->
      let t =
        { label =
            List.map t.label ~f:(fun (typs, ctx) ->
              let typs = List.map typs ~f:(Substitution.Qual.incr_unbound_in_t 1) in
              let ctx =
                List.map ctx ~f:(fun (typ, sz) ->
                  Substitution.Qual.incr_unbound_in_t 1 typ, sz)
              in
              typs, ctx)
        ; ret = Option.map t.ret ~f:(List.map ~f:(Substitution.Qual.incr_unbound_in_t 1))
        ; qual = (less, greater) :: t.qual
        ; size = t.size
        ; typ_ = t.typ_ |> List.map ~f:(fun (q, sz, h) -> incr_q 1 q, sz, h)
        ; loc = t.loc
        ; linear = t.linear |> List.map ~f:(List.map ~f:(incr_q 1))
        }
      in
      let module Solver = (val qual_solver t) in
      if Solver.check ()
      then return t
      else
        Or_error.error_s
          [%message
            "Adding constraint leads to inconsistent assumptions"
              (constraint_ : KindVar.t)]
    | Size (less, greater) ->
      let t =
        { label =
            List.map t.label ~f:(fun (typs, ctx) ->
              let typs = List.map typs ~f:(Substitution.Size.incr_unbound_in_t 1) in
              let ctx =
                List.map ctx ~f:(fun (typ, sz) ->
                  Substitution.Size.incr_unbound_in_t 1 typ, incr_sz 1 sz)
              in
              typs, ctx)
        ; ret = Option.map t.ret ~f:(List.map ~f:(Substitution.Size.incr_unbound_in_t 1))
        ; qual = t.qual
        ; size = (less, greater) :: t.size
        ; typ_ = t.typ_ |> List.map ~f:(fun (q, sz, h) -> q, incr_sz 1 sz, h)
        ; loc = t.loc
        ; linear = t.linear
        }
      in
      let module Solver = (val size_solver t) in
      if Solver.check ()
      then return t
      else
        Or_error.error_s
          [%message
            "Adding constraint leads to inconsistent assumptions"
              (constraint_ : KindVar.t)]
    | Type (qual, size, heapable) ->
      return
        { label =
            List.map t.label ~f:(fun (typs, ctx) ->
              let typs = List.map typs ~f:(Substitution.Type.incr_unbound_in_t 1) in
              let ctx =
                List.map ctx ~f:(fun (typ, sz) ->
                  Substitution.Type.incr_unbound_in_t 1 typ, sz)
              in
              typs, ctx)
        ; ret = Option.map t.ret ~f:(List.map ~f:(Substitution.Type.incr_unbound_in_t 1))
        ; qual = t.qual
        ; size = t.size
        ; typ_ = (qual, size, heapable) :: t.typ_
        ; loc = t.loc
        ; linear = t.linear
        }
  ;;

  let empty =
    { label = []; ret = None; qual = []; size = []; typ_ = []; loc = 0; linear = [ [] ] }
  ;;

  let type_constraints n t =
    match List.nth t.typ_ n with
    | Some result -> return result
    | None -> Or_error.error_s [%message "Unbound type variable" (n : int)]
  ;;

  let size_bounds_of_types t = List.map t.typ_ ~f:(fun (_, sz, _) -> sz)
  let qual_bound n t = List.length t.qual > n
  let size_bound n t = List.length t.size > n
  let loc_bound n t = t.loc > n

  let add_frame_constraint q t =
    { t with linear = (q :: List.hd_exn t.linear) :: List.tl_exn t.linear }
  ;;

  let new_frame t = { t with linear = [] :: t.linear }
  let set_ret ret t = { t with ret = Some ret }

  let add_label output_types l t =
    let t = { t with label = (output_types, l) :: t.label } in
    { t with linear = [] :: t.linear }
  ;;

  let jump_requirements n t =
    match List.nth t.label n with
    | None -> Or_error.error_s [%message "label context is not deep enough" (n : int)]
    | Some (types, local_ctx) -> return (types, local_ctx)
  ;;

  let linear_requirements n t =
    match List.nth t.linear n with
    | None -> Or_error.error_s [%message "linear context is not deep enough" (n : int)]
    | Some qs -> return qs
  ;;

  let all_linear_requirements t = t.linear
  let ret t = t.ret
end

module Store_typing = struct
  type t = Module_type.t String.Map.t [@@deriving sexp]
end

let%test_module "add_constraints" =
  (module struct
    open Function_ctx

    let add_constraint_exn k = Fn.compose Or_error.ok_exn (add_constraint k)

    let%expect_test "add locs" =
      let f = empty |> add_constraint_exn Loc |> add_constraint_exn Loc in
      assert (loc_bound 0 f);
      assert (loc_bound 1 f);
      assert (not (loc_bound 2 f))
    ;;

    let%expect_test "add quals" =
      let f =
        empty
        |> add_constraint_exn (Qual ([], []))
        |> add_constraint_exn (Qual ([ QualV 0 ], []))
        |> add_constraint_exn (Qual ([ QualV 1 ], [ QualV 0 ]))
      in
      print_s [%sexp (f.qual : (Qual.t list * Qual.t list) list)];
      [%expect {| ((((QualV 1)) ((QualV 0))) (((QualV 0)) ()) (() ())) |}];
      assert (Or_error.is_error (add_constraint (Qual ([ QualC Lin ], [ QualC Unr ])) f))
    ;;

    let%expect_test "add quals" =
      let f =
        empty
        |> add_constraint_exn (Qual ([], []))
        |> add_constraint_exn (Qual ([ QualV 0 ], []))
        |> add_constraint_exn (Qual ([ QualV 1 ], [ QualV 0 ]))
      in
      print_s [%sexp (f.qual : (Qual.t list * Qual.t list) list)];
      [%expect {| ((((QualV 1)) ((QualV 0))) (((QualV 0)) ()) (() ())) |}];
      assert (Or_error.is_error (add_constraint (Qual ([ QualC Lin ], [ QualC Unr ])) f))
    ;;

    let%expect_test "add sizes" =
      let f =
        empty
        |> add_constraint_exn (Size ([], []))
        |> add_constraint_exn (Size ([ SizeV 0 ], [ SizeC 1 ]))
        |> add_constraint_exn (Size ([ SizeV 1; SizeC 2 ], [ SizeP (SizeV 1, SizeV 0) ]))
      in
      print_s [%sexp (f.size : (Size.t list * Size.t list) list)];
      [%expect
        {|
        ((((SizeV 1) (SizeC 2)) ((SizeP (SizeV 1) (SizeV 0))))
         (((SizeV 0)) ((SizeC 1))) (() ())) |}];
      assert (Or_error.is_error (add_constraint (Size ([ SizeV 2 ], [ SizeC 0 ])) f))
    ;;

    let%expect_test "add types" =
      let f =
        empty
        |> add_constraint_exn (Size ([], []))
        |> add_constraint_exn (Qual ([], []))
        |> add_constraint_exn (Type (QualV 0, SizeV 0, Heapable))
      in
      print_s [%sexp (f.typ_ : (Qual.t * Size.t * Heapable_const.t) list)];
      [%expect {| (((QualV 0) (SizeV 0) Heapable)) |}];
      let f =
        f |> add_constraint_exn (Size ([], [])) |> add_constraint_exn (Qual ([], []))
      in
      print_s [%sexp (f.typ_ : (Qual.t * Size.t * Heapable_const.t) list)];
      [%expect {| (((QualV 1) (SizeV 1) Heapable)) |}]
    ;;
  end)
;;

let%test_module "size solver" =
  (module struct
    open Function_ctx

    let add_constraint_exn k = Fn.compose Or_error.ok_exn (add_constraint k)

    let f =
      empty
      |> add_constraint_exn (Size ([], []))
      |> add_constraint_exn (Size ([ SizeV 0 ], [ SizeC 2 ]))
      |> add_constraint_exn (Size ([ SizeV 0 ], [ SizeC 3 ]))
    ;;

    let%expect_test "simple checks" =
      let module Solver = (val size_solver f) in
      let open Solver in
      let open Size in
      check_leq ~less:(of_size (SizeP (SizeV 0, SizeV 1))) ~greater:(of_size (SizeC 5));
      check_leq ~less:(of_size (SizeV 2)) ~greater:(of_size (SizeC 2));
      check_leq ~less:(of_size (SizeC 0)) ~greater:(of_size (SizeV 2));
      assert (check ());
      check_leq ~less:(of_size (SizeV 2)) ~greater:(of_size (SizeC 1));
      assert (not (check ()))
    ;;
  end)
;;
