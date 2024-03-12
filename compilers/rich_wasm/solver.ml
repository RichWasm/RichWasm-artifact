open! Core
open! Z3

let bool_of_status_exn =
  let open Solver in
  function
  | UNSATISFIABLE -> false
  | UNKNOWN -> raise_s [%message "unknown"]
  | SATISFIABLE -> true
;;

module type S = sig
  val check : unit -> bool

  module Qual : sig
    type t

    val of_qual : Rich_wasm.Qual.t -> t
    val assume_leq : less:t -> greater:t -> unit
    val assume_eq : t -> t -> unit
    val check_leq : less:t -> greater:t -> unit
  end

  module Size : sig
    type t

    val of_size : Rich_wasm.Size.t -> t
    val assume_leq : less:t -> greater:t -> unit
    val assume_eq : t -> t -> unit
    val check_leq : less:t -> greater:t -> unit
  end
end

let create_constraint_checker () =
  let context = mk_context [] in
  let assumptions = ref [] in
  let goals = ref [] in
  let int_sort = Arithmetic.Integer.mk_sort context in
  (module struct
    let check_assumptions () =
      let solver = Solver.mk_solver context None in
      !assumptions |> Solver.check solver |> bool_of_status_exn
    ;;

    let check () =
      if not (check_assumptions ())
      then false
      else (
        let solver = Solver.mk_solver context None in
        let assumption = Boolean.mk_and context !assumptions in
        let goal = Boolean.mk_and context !goals in
        Boolean.mk_implies context assumption goal
        |> Boolean.mk_not context
        |> List.return
        |> Solver.check solver
        |> bool_of_status_exn
        |> not)
    ;;

    module Qual = struct
      type t = Expr.expr

      let unr = Boolean.mk_false context
      let lin = Boolean.mk_true context

      let assume_leq ~less ~greater =
        let assumption = Boolean.mk_or context [ greater; Boolean.mk_not context less ] in
        assumptions := assumption :: !assumptions
      ;;

      let assume_eq x y =
        let assumption = Boolean.mk_eq context x y in
        assumptions := assumption :: !assumptions
      ;;

      let check_leq ~less ~greater =
        let goal = Boolean.mk_or context [ greater; Boolean.mk_not context less ] in
        goals := goal :: !goals
      ;;

      let new_qual s = Boolean.mk_const context (Symbol.mk_string context s)

      let of_qual (q : Rich_wasm.Qual.t) =
        match q with
        | QualC Lin -> lin
        | QualC Unr -> unr
        | QualV n -> n |> string_of_int |> new_qual
      ;;
    end

    module Size = struct
      type t = Expr.expr

      let const n = Expr.mk_numeral_int context n int_sort
      (*
         let zero = const 0
         let sub x y = Arithmetic.mk_sub context [ x; y ]
      *)

      let add x y = Arithmetic.mk_add context [ x; y ]

      let assume_leq ~less ~greater =
        assumptions := Arithmetic.mk_le context less greater :: !assumptions
      ;;

      let assume_eq x y =
        let assumption =
          Boolean.mk_and
            context
            [ Arithmetic.mk_le context x y; Arithmetic.mk_ge context x y ]
        in
        assumptions := assumption :: !assumptions
      ;;

      let check_leq ~less ~greater =
        goals := Arithmetic.mk_le context less greater :: !goals
      ;;

      let new_size = Arithmetic.Integer.mk_const_s context

      let rec of_size (sz : Rich_wasm.Size.t) =
        match sz with
        | SizeC n -> const n
        | SizeV n -> n |> string_of_int |> new_size
        | SizeP (sz1, sz2) -> add (of_size sz1) (of_size sz2)
      ;;
    end
  end : S)
;;

let test f =
  let module Solver = (val create_constraint_checker ()) in
  let y () = assert (Solver.check ()) in
  let n () = assert (not (Solver.check ())) in
  f ~y ~n (module Solver : S)
;;

let%test_module "qual" =
  (module struct
    let%expect_test "invalid assumption" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Qual in
        let lin = of_qual (QualC Lin) in
        let unr = of_qual (QualC Unr) in
        y ();
        assume_leq ~less:lin ~greater:unr;
        n ())
    ;;

    let%expect_test "invalid assumption transitive" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Qual in
        let lin = of_qual (QualC Lin) in
        let unr = of_qual (QualC Unr) in
        let q0 = of_qual (QualV 0) in
        y ();
        assume_leq ~less:lin ~greater:q0;
        assume_leq ~less:q0 ~greater:unr;
        n ())
    ;;

    let%expect_test "check uncertain" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Qual in
        let lin = of_qual (QualC Lin) in
        let q0 = of_qual (QualV 0) in
        y ();
        check_leq ~less:lin ~greater:q0;
        n ())
    ;;

    let%expect_test "check true" =
      test (fun ~y ~n:_ (module Solver) ->
        let open Solver.Qual in
        let lin = of_qual (QualC Lin) in
        let q0 = of_qual (QualV 0) in
        let q1 = of_qual (QualV 1) in
        y ();
        assume_leq ~less:lin ~greater:q1;
        assume_leq ~less:q1 ~greater:q0;
        check_leq ~less:lin ~greater:q0;
        y ())
    ;;

    let%expect_test "check false" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Qual in
        let lin = of_qual (QualC Lin) in
        let unr = of_qual (QualC Unr) in
        let q0 = of_qual (QualV 0) in
        let q1 = of_qual (QualV 1) in
        y ();
        assume_leq ~less:lin ~greater:q1;
        assume_leq ~less:q1 ~greater:q0;
        check_leq ~less:q0 ~greater:unr;
        n ())
    ;;
  end)
;;

let%test_module "size" =
  (module struct
    let%expect_test "invalid assumption" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Size in
        let sc0 = of_size (SizeC 0) in
        let sc1 = of_size (SizeC 1) in
        y ();
        assume_leq ~less:sc1 ~greater:sc0;
        n ())
    ;;

    let%expect_test "invalid assumption transitive" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Size in
        let sc0 = of_size (SizeC 0) in
        let sc1 = of_size (SizeC 1) in
        let sv0 = of_size (SizeV 0) in
        y ();
        assume_leq ~less:sc1 ~greater:sv0;
        assume_leq ~less:sv0 ~greater:sc0;
        n ())
    ;;

    let%expect_test "x + x <= x may be true unless 1 < x" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Size in
        let sc1 = of_size (SizeC 1) in
        let sv0 = of_size (SizeV 0) in
        let sp = of_size (SizeP (SizeV 0, SizeV 0)) in
        y ();
        assume_leq ~less:sp ~greater:sv0;
        y ();
        assume_leq ~less:sc1 ~greater:sp;
        n ())
    ;;

    let%expect_test "basic arithmetic implications" =
      test (fun ~y ~n (module Solver) ->
        let open Solver.Size in
        let sc1 = of_size (SizeC 1) in
        let sc2 = of_size (SizeC 2) in
        let sc3 = of_size (SizeC 3) in
        let sv0 = of_size (SizeV 0) in
        let sv1 = of_size (SizeV 1) in
        let sp = of_size (SizeP (SizeV 0, SizeV 1)) in
        y ();
        assume_leq ~less:sv0 ~greater:sc1;
        assume_leq ~less:sv1 ~greater:sc2;
        check_leq ~less:sp ~greater:sc3;
        y ();
        assume_leq ~less:sv1 ~greater:sv0;
        y ();
        check_leq ~less:sp ~greater:sc2;
        y ();
        check_leq ~less:sp ~greater:sc1;
        n ())
    ;;
  end)
;;
