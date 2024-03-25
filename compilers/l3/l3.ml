module Syntax = Syntax
module Parse = Parse
module Tagging = Tagging
module Source_printer = Source_printer
module Debruijn = Debruijn
module Typecheck = Typecheck
module Codegen = Codegen
open Core

let compile m =
  let open Or_error.Let_syntax in
  let map ~f m_and_printer =
    let%bind m, source_printer = m_and_printer in
    let%map m = f m ~source_printer in
    m, source_printer
  in
  m
  |> Parse.parse
  |> Tagging.tag
  |> (fun x -> return (x, Source_printer.create x))
  |> map ~f:Debruijn.debruijn
  |> map ~f:Typecheck.typecheck
  |> map ~f:Codegen.codegen
;;

let compile_to_typechecked m =
  let open Or_error.Let_syntax in
  let map ~f m_and_printer =
    let%bind m, source_printer = m_and_printer in
    let%map m = f m ~source_printer in
    m, source_printer
  in
  m
  |> Parse.parse
  |> Tagging.tag
  |> (fun x -> return (x, Source_printer.create x))
  |> map ~f:Debruijn.debruijn
  |> map ~f:Typecheck.typecheck
;;

let rec body_type m =
  match (m : Syntax.Typechecked.Module.t) with
  | LetIm (_, m) -> body_type m
  | LetEx (_, _, m) -> body_type m
  | Body e ->
    (match e with
     | Info { typ; _ } -> typ)
;;

let test_typechecking s =
  s
  |> compile_to_typechecked
  |> Or_error.ok_exn
  |> fst
  |> body_type
  |> Syntax.Typechecked.Type.sexp_of_t
  |> print_s
;;

let test s =
  s |> compile |> Or_error.ok_exn |> fst |> Rich_wasm.Module.sexp_of_t |> print_s
;;

let test_to_debruijn m =
  let open Or_error.Let_syntax in
  let map ~f m_and_printer =
    let%bind m, source_printer = m_and_printer in
    let%map m = f m ~source_printer in
    m, source_printer
  in
  m
  |> Parse.parse
  |> Tagging.tag
  |> (fun x -> return (x, Source_printer.create x))
  |> map ~f:Debruijn.debruijn
  |> Or_error.ok_exn
  |> fst
  |> Syntax.Debruijned.Module.sexp_of_t
  |> print_s
;;

let prog1 =
  {| 
import ml.stash : !(A. E l. Ref l !Int 1 -o E l. Ref l !Int 1) in
import ml.get_stashed : !(A. !I -o E l. Ref l !Int 1) in
let! stash = stash in
let! get_stashed = get_stashed in
let {_,_} = free split (stash join new !42 1) in
free split (get_stashed !*)
  |}
;;

let%expect_test _ =
  test_typechecking prog1;
  [%expect {| (Info 15 (Exists (Info 22 (Bang (Info 21 Int))))) |}]
;;

let%expect_test _ =
  test prog1;
  [%expect
    {|
    (((FunIm ()
       (()
        ((((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       (Import ml stash))
      (FunIm ()
       (()
        (((Unit (QualC Unr)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       (Import ml get_stashed))
      (Fun (main)
       (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
       ((SizeC 64) (SizeC 64) (SizeC 32) (SizeC 32) (SizeC 32))
       ((ICoderefI 0) (IQualify (QualC Lin)) (ISet_local 0) (ICoderefI 1)
        (IQualify (QualC Lin)) (ISet_local 1)
        (IVal (Num (Int S I32) (Second 42)))
        (IStructMalloc ((SizeC 32)) (QualC Lin))
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack
         (()
          (((ExLoc
             ((Ref W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (QualC Lin))))
         () (IUngroup IRefJoin (IMemPack (LocV 0))))
        (IGet_local 0 (QualC Lin)) ICall_indirect
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin))))
         ()
         (IUngroup IRefJoin (IVal Unit) (IStructSwap 0) (ISet_local 2)
          IStructFree (IGet_local 2 (QualC Unr)) (IVal Unit) (ISet_local 2)
          (IMemPack (LocV 0)) (IQualify (QualC Lin))))
        (IMemUnpack (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin))))
         ((1 (Unit (QualC Unr))))
         ((ISet_local 3) (IVal Unit) (IGet_local 1 (QualC Lin)) ICall_indirect
          (IMemUnpack
           (()
            (((ExLoc
               ((Prod
                 (((Cap W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                   (QualC Lin))
                  ((Ptr (LocV 0)) (QualC Unr))))
                (QualC Lin)))
              (QualC Lin))))
           () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
          (IMemUnpack
           (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))) ()
           (IUngroup IRefJoin (IVal Unit) (IStructSwap 0) (ISet_local 4)
            IStructFree (IGet_local 4 (QualC Unr)) (IVal Unit) (ISet_local 4)
            (IMemPack (LocV 0)) (IQualify (QualC Lin))))
          (IVal Unit) (ISet_local 3)))
        (IVal Unit) (ISet_local 1) (IVal Unit) (ISet_local 0))))
     () (0 1 2)) |}]
;;

let prog2 =
  {| 
import ml.stash : !(A. !I, E l. Ref l !Int 1 -o !I ) in
import ml.get_stashed : !(A. !I, !I -o E l. Ref l !Int 1) in
let! stash = stash in
let! get_stashed = get_stashed in
let! * = (stash !*, join new !42 1) in
free split (get_stashed !*, !*)
  |}
;;

let%expect_test _ =
  test prog2;
  [%expect
    {|
    (((FunIm ()
       (()
        (((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         ((Unit (QualC Unr)))))
       (Import ml stash))
      (FunIm ()
       (()
        (((Unit (QualC Unr)) (Unit (QualC Unr)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       (Import ml get_stashed))
      (Fun (main)
       (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
       ((SizeC 64) (SizeC 64) (SizeC 32))
       ((ICoderefI 0) (IQualify (QualC Lin)) (ISet_local 0) (ICoderefI 1)
        (IQualify (QualC Lin)) (ISet_local 1) (IVal Unit)
        (IVal (Num (Int S I32) (Second 42)))
        (IStructMalloc ((SizeC 32)) (QualC Lin))
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack
         (()
          (((ExLoc
             ((Ref W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (QualC Lin))))
         () (IUngroup IRefJoin (IMemPack (LocV 0))))
        (IGet_local 0 (QualC Lin)) ICall_indirect IDrop (IVal Unit) (IVal Unit)
        (IGet_local 1 (QualC Lin)) ICall_indirect
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin))))
         ()
         (IUngroup IRefJoin (IVal Unit) (IStructSwap 0) (ISet_local 2)
          IStructFree (IGet_local 2 (QualC Unr)) (IVal Unit) (ISet_local 2)
          (IMemPack (LocV 0)) (IQualify (QualC Lin))))
        (IVal Unit) (ISet_local 1) (IVal Unit) (ISet_local 0))))
     () (0 1 2)) |}]
;;

let prog3 =
  {|
let {l, cap_and_ptr} = new !42 2 in
let <cap, ptr> = cap_and_ptr in
let <cap, old_val> = swap ptr <cap, <!69, !420>> in
<{l, <cap, ptr>}, old_val>
|}
;;

let%expect_test _ =
  test prog3;
  [%expect
    {|
    (((Fun (main)
       (()
        (()
         (((Prod
            (((ExLoc
               ((Prod
                 (((Cap W (LocV 0)
                    (Struct
                     ((((Prod
                         (((Num (Int S I32)) (QualC Unr))
                          ((Num (Int S I32)) (QualC Unr))))
                        (QualC Lin))
                       (SizeC 64)))))
                   (QualC Lin))
                  ((Ptr (LocV 0)) (QualC Unr))))
                (QualC Lin)))
              (QualC Lin))
             ((Num (Int S I32)) (QualC Unr))))
           (QualC Lin)))))
       ((SizeC 64) (SizeC 0) (SizeC 64) (SizeC 64) (SizeC 32) (SizeC 0)
        (SizeC 32))
       ((IVal (Num (Int S I32) (Second 42)))
        (IStructMalloc ((SizeC 64)) (QualC Lin))
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 64)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack
         (()
          (((Prod
             (((ExLoc
                ((Prod
                  (((Cap W (LocV 0)
                     (Struct
                      ((((Prod
                          (((Num (Int S I32)) (QualC Unr))
                           ((Num (Int S I32)) (QualC Unr))))
                         (QualC Lin))
                        (SizeC 64)))))
                    (QualC Lin))
                   ((Ptr (LocV 0)) (QualC Unr))))
                 (QualC Lin)))
               (QualC Lin))
              ((Num (Int S I32)) (QualC Unr))))
            (QualC Lin))))
         ((0 (Unit (QualC Unr))) (1 (Unit (QualC Unr))) (5 (Unit (QualC Unr))))
         ((ISet_local 0) (IGet_local 0 (QualC Lin)) IUngroup (ISet_local 2)
          (ISet_local 1) (IGet_local 1 (QualC Lin))
          (IVal (Num (Int S I32) (Second 69)))
          (IVal (Num (Int S I32) (Second 420))) (IGroup 2 (QualC Lin))
          (IGroup 2 (QualC Lin)) IUngroup (ISet_local 3)
          (IGet_local 2 (QualC Unr)) IRefJoin (IGet_local 3 (QualC Lin))
          (IVal Unit) (ISet_local 3) (IStructSwap 0) (ISet_local 4) IRefSplit
          IDrop (IGet_local 4 (QualC Unr)) (IVal Unit) (ISet_local 4)
          (IGroup 2 (QualC Lin)) IUngroup (ISet_local 6) (ISet_local 5)
          (IGet_local 5 (QualC Lin)) (IGet_local 2 (QualC Unr))
          (IGroup 2 (QualC Lin)) (IMemPack (LocV 0)) (IGet_local 6 (QualC Unr))
          (IGroup 2 (QualC Lin)) (IVal Unit) (ISet_local 6) (IVal Unit)
          (ISet_local 5) (IVal Unit) (ISet_local 2) (IVal Unit) (ISet_local 1)
          (IVal Unit) (ISet_local 0))))))
     () (0)) |}]
;;

let util =
  {|
export easy_swap_int = A l. fun r : <Cap l !Int 1, !Ptr l>, v : !Int.
  let <cap, ptr> = r in
  let <cap, old_v> = swap ptr <cap, v> in
  <<cap, ptr>, old_v>
in
export add_to_snd_int_in_pair = A. fun r : E l. Ref l <!Int, !Int> 2, to_add : !Int.
  let {l, c_and_p} = split r in
  let <cap, ptr> = c_and_p in
  let <cap, ints> = swap ptr <cap, !*> in
  let <x, y> = ints in
  let! y = y in
  let! to_add = to_add in
  let <cap, *> = swap ptr <cap, <x, ( + y to_add)>> in
  {l, <cap, ptr>}
in
*
|}
;;

let%expect_test _ =
  test util;
  [%expect {|
    (((Fun (easy_swap_int)
       ((Loc)
        ((((Prod
            (((Cap W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin))
             ((Ptr (LocV 0)) (QualC Unr))))
           (QualC Lin))
          ((Num (Int S I32)) (QualC Unr)))
         (((Prod
            (((Prod
               (((Cap W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin))
             ((Num (Int S I32)) (QualC Unr))))
           (QualC Lin)))))
       ((SizeC 0) (SizeC 64) (SizeC 32) (SizeC 32) (SizeC 0) (SizeC 32))
       ((IGet_local 0 (QualC Lin)) IUngroup (ISet_local 3) (ISet_local 2)
        (IGet_local 2 (QualC Lin)) (IGet_local 1 (QualC Unr))
        (IGroup 2 (QualC Lin)) IUngroup (ISet_local 4) (IGet_local 3 (QualC Unr))
        IRefJoin (IGet_local 4 (QualC Unr)) (IVal Unit) (ISet_local 4)
        (IStructSwap 0) (ISet_local 5) IRefSplit IDrop (IGet_local 5 (QualC Unr))
        (IVal Unit) (ISet_local 5) (IGroup 2 (QualC Lin)) IUngroup (ISet_local 7)
        (ISet_local 6) (IGet_local 6 (QualC Lin)) (IGet_local 3 (QualC Unr))
        (IGroup 2 (QualC Lin)) (IGet_local 7 (QualC Unr)) (IGroup 2 (QualC Lin))
        (IVal Unit) (ISet_local 7) (IVal Unit) (ISet_local 6) (IVal Unit)
        (ISet_local 3) (IVal Unit) (ISet_local 2)))
      (Fun (add_to_snd_int_in_pair)
       (()
        ((((ExLoc
            ((Ref W (LocV 0)
              (Struct
               ((((Prod
                   (((Num (Int S I32)) (QualC Unr))
                    ((Num (Int S I32)) (QualC Unr))))
                  (QualC Lin))
                 (SizeC 64)))))
             (QualC Lin)))
           (QualC Lin))
          ((Num (Int S I32)) (QualC Unr)))
         (((ExLoc
            ((Prod
              (((Cap W (LocV 0)
                 (Struct
                  ((((Prod
                      (((Num (Int S I32)) (QualC Unr))
                       ((Num (Int S I32)) (QualC Unr))))
                     (QualC Lin))
                    (SizeC 64)))))
                (QualC Lin))
               ((Ptr (LocV 0)) (QualC Unr))))
             (QualC Lin)))
           (QualC Lin)))))
       ((SizeC 64) (SizeC 0) (SizeC 64) (SizeC 0) (SizeC 64) (SizeC 0) (SizeC 64)
        (SizeC 32) (SizeC 32) (SizeC 32) (SizeC 32) (SizeC 64) (SizeC 0)
        (SizeC 0))
       ((IGet_local 0 (QualC Lin))
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct
                   ((((Prod
                       (((Num (Int S I32)) (QualC Unr))
                        ((Num (Int S I32)) (QualC Unr))))
                      (QualC Lin))
                     (SizeC 64)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 0))))
        (IMemUnpack
         (()
          (((ExLoc
             ((Prod
               (((Cap W (LocV 0)
                  (Struct
                   ((((Prod
                       (((Num (Int S I32)) (QualC Unr))
                        ((Num (Int S I32)) (QualC Unr))))
                      (QualC Lin))
                     (SizeC 64)))))
                 (QualC Lin))
                ((Ptr (LocV 0)) (QualC Unr))))
              (QualC Lin)))
            (QualC Lin))))
         ((2 (Unit (QualC Unr))) (3 (Unit (QualC Unr))) (8 (Unit (QualC Unr)))
          (7 (Unit (QualC Unr))) (12 (Unit (QualC Unr))) (11 (Unit (QualC Unr)))
          (15 (Unit (QualC Unr))))
         ((ISet_local 2) (IGet_local 2 (QualC Lin)) IUngroup (ISet_local 4)
          (ISet_local 3) (IGet_local 3 (QualC Lin)) (IVal Unit)
          (IGroup 2 (QualC Lin)) IUngroup (ISet_local 5)
          (IGet_local 4 (QualC Unr)) IRefJoin (IGet_local 5 (QualC Unr))
          (IVal Unit) (ISet_local 5) (IStructSwap 0) (ISet_local 6) IRefSplit
          IDrop (IGet_local 6 (QualC Lin)) (IVal Unit) (ISet_local 6)
          (IGroup 2 (QualC Lin)) IUngroup (ISet_local 8) (ISet_local 7)
          (IGet_local 8 (QualC Lin)) IUngroup (ISet_local 10) (ISet_local 9)
          (IGet_local 10 (QualC Unr)) (IQualify (QualC Lin)) (ISet_local 11)
          (IGet_local 1 (QualC Unr)) (IQualify (QualC Lin)) (ISet_local 12)
          (IGet_local 7 (QualC Lin)) (IGet_local 9 (QualC Unr))
          (IGet_local 12 (QualC Lin)) (IGet_local 11 (QualC Lin))
          (INe (Ib I32 Iadd)) (IGroup 2 (QualC Lin)) (IGroup 2 (QualC Lin))
          IUngroup (ISet_local 13) (IGet_local 4 (QualC Unr)) IRefJoin
          (IGet_local 13 (QualC Lin)) (IVal Unit) (ISet_local 13) (IStructSwap 0)
          (ISet_local 14) IRefSplit IDrop (IGet_local 14 (QualC Unr)) (IVal Unit)
          (ISet_local 14) (IGroup 2 (QualC Lin)) IUngroup IDrop (ISet_local 15)
          (IGet_local 15 (QualC Lin)) (IGet_local 4 (QualC Unr))
          (IGroup 2 (QualC Lin)) (IMemPack (LocV 0)) (IVal Unit) (ISet_local 15)
          (IVal Unit) (ISet_local 12) (IVal Unit) (ISet_local 11) (IVal Unit)
          (ISet_local 10) (IVal Unit) (ISet_local 9) (IVal Unit) (ISet_local 8)
          (IVal Unit) (ISet_local 7) (IVal Unit) (ISet_local 4) (IVal Unit)
          (ISet_local 3) (IVal Unit) (ISet_local 2)))))
      (Fun (main) (() (() ((Unit (QualC Lin))))) ()
       ((IVal Unit) (IQualify (QualC Lin)))))
     () (0 1 2)) |}]
;;
