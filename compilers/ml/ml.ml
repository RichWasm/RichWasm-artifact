module Syntax = Syntax
module Parse = Parse
module Tagging = Tagging
module Source_printer = Source_printer
module Debruijn = Debruijn
module Typecheck = Typecheck
module Hoist = Hoist
module Annotate = Annotate
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
  |> map ~f:Hoist.hoist
  |> map ~f:Annotate.annotate
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
  | LetIm (_, m, _) -> body_type m
  | LetEx (_, _, m, _) -> body_type m
  | Global (_, m, _) -> body_type m
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

let test_compilation s =
  s |> compile |> Or_error.ok_exn |> fst |> Rich_wasm.Module.sexp_of_t |> print_s
;;

let prog1 = {| 
export f = fun []. x : Int, y : Int -> ( + x y) in
(f [] (0, 1))
  |}

let%expect_test _ =
  test_typechecking prog1;
  [%expect {| (Info 2 (Typ Int)) |}]
;;

let%expect_test _ =
  test_compilation prog1;
  [%expect
    {|
    (((Fun (f)
       (()
        (((Unit (QualC Unr)) ((Num (Int S I32)) (QualC Unr))
          ((Num (Int S I32)) (QualC Unr)))
         (((Num (Int S I32)) (QualC Unr)))))
       ()
       ((IGet_local 2 (QualC Unr)) (IGet_local 1 (QualC Unr))
        (INe (Ib I32 Iadd))))
      (Fun () (() (() (((Num (Int S I32)) (QualC Unr))))) ((SizeC 64))
       ((IVal Unit) (ICoderefI 0) (IInst ()) (IGroup 2 (QualC Unr))
        (IExistPack Unit
         (Ex (QualC Unr) (SizeC 64)
          ((Prod
            (((Var 0) (QualC Unr))
             ((Coderef
               (()
                ((((Var 0) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))
                  ((Num (Int S I32)) (QualC Unr)))
                 (((Num (Int S I32)) (QualC Unr))))))
              (QualC Unr))))
           (QualC Unr)))
         (QualC Unr))
        (IMemUnpack (() (((Num (Int S I32)) (QualC Unr)))) ()
         ((IExistUnpack (QualC Unr) (() (((Num (Int S I32)) (QualC Unr)))) ()
           (IUngroup (ISet_local 0) (IVal (Num (Int S I32) (Second 0)))
            (IVal (Num (Int S I32) (Second 1))) (IGet_local 0 (QualC Unr))
            (IInst ()) ICall_indirect (IVal Unit) (ISet_local 0))))))))
     () (0 1)) |}]
;;

let prog_1_and_a_half =
  {|
let a = 0 in
let b = new 1 in
let (c, d) = ( * 2, ()) in
let () = () in
( * a, b, c, d)
|}
;;

let%expect_test _ =
  test_typechecking prog_1_and_a_half;
  [%expect
    {|
    (Info 4
     (Typ
      (Prod
       ((Info 14 (Typ Int)) (Info 12 (Typ (Ref (Info 11 (Typ Int)))))
        (Info 7 (Typ Int)) (Info 8 (Typ Unit)))))) |}]
;;

let%expect_test _ =
  test_compilation prog_1_and_a_half;
  [%expect
    {|
    (((Fun ()
       (()
        (()
         (((Prod
            (((Num (Int S I32)) (QualC Unr))
             ((ExLoc
               ((Ref W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Unr)))
              (QualC Unr))
             ((Num (Int S I32)) (QualC Unr)) (Unit (QualC Unr))))
           (QualC Unr)))))
       ((SizeC 32) (SizeC 64) (SizeC 32) (SizeC 0))
       ((IVal (Num (Int S I32) (Second 0))) (ISet_local 0)
        (IVal (Num (Int S I32) (Second 1)))
        (IStructMalloc ((SizeC 32)) (QualC Unr)) (ISet_local 1)
        (IVal (Num (Int S I32) (Second 2))) (IVal Unit) (IGroup 2 (QualC Unr))
        IUngroup (ISet_local 3) (ISet_local 2) (IVal Unit) IDrop
        (IGet_local 0 (QualC Unr)) (IGet_local 1 (QualC Unr))
        (IGet_local 2 (QualC Unr)) (IGet_local 3 (QualC Unr))
        (IGroup 4 (QualC Unr)) (IVal Unit) (ISet_local 3) (IVal Unit)
        (ISet_local 2) (IVal Unit) (ISet_local 1) (IVal Unit) (ISet_local 0))))
     () (0)) |}]
;;

let prog2 =
  {|
let f =
fun [a]. x : a ->
fun [b]. y : b ->
fun [c]. z : c ->
( * x, y, z)
in
((f [Int] (0)) [Unit] (()))
    |}
;;

let%expect_test _ =
  test_typechecking prog2;
  [%expect
    {|
    (Info 12
     (Typ
      (Fun
       ((foralls 1) (args ((Info 11 (Typ (Var 0)))))
        (ret
         (Info 10
          (Typ
           (Prod
            ((Info 3 (Typ Int)) (Info 1 (Typ Unit)) (Info 11 (Typ (Var 0)))))))))))) |}]
;;

let prog3 =
  {|
let f =
fun [a]. x : a ->
fun [b]. y : b ->
( * x, y)
in
fun [c]. z : c -> (f [c] (z))
    |}
;;

let%expect_test _ =
  test_typechecking prog3;
  [%expect
    {|
    (Info 5
     (Typ
      (Fun
       ((foralls 1) (args ((Info 4 (Typ (Var 0)))))
        (ret
         (Info 10
          (Typ
           (Fun
            ((foralls 1) (args ((Info 9 (Typ (Var 0)))))
             (ret
              (Info 8
               (Typ (Prod ((Info 1 (Typ (Var 1))) (Info 9 (Typ (Var 0))))))))))))))))) |}]
;;

let prog4 =
  {|
let p = ( * 3, (), new inj 0 ( + Unit) ()) in
( * proj 1 p, proj 2 p, proj 0 p)
    |}
;;

let%expect_test _ =
  test_typechecking prog4;
  [%expect
    {|
    (Info 6
     (Typ
      (Prod
       ((Info 8 (Typ Unit))
        (Info 12 (Typ (Ref (Info 11 (Typ (Variant ((Info 10 (Typ Unit)))))))))
        (Info 7 (Typ Int)))))) |}]
;;

let%expect_test _ =
  test_compilation prog4;
  [%expect
    {|
    (((Fun ()
       (()
        (()
         (((Prod
            ((Unit (QualC Unr))
             ((ExLoc
               ((Ref W (LocV 0)
                 (Struct
                  ((((ExLoc
                      ((Ref W (LocV 0) (Variant ((Unit (QualC Unr)))))
                       (QualC Unr)))
                     (QualC Unr))
                    (SizeC 64)))))
                (QualC Unr)))
              (QualC Unr))
             ((Num (Int S I32)) (QualC Unr))))
           (QualC Unr)))))
       ((SizeP (SizeP (SizeP (SizeC 0) (SizeC 32)) (SizeC 0)) (SizeC 64))
        (SizeC 0) (SizeC 64) (SizeC 32))
       ((IVal (Num (Int S I32) (Second 3))) (IVal Unit) (IVal Unit)
        (IVariantMalloc 0 ((Unit (QualC Unr))) (QualC Unr))
        (IStructMalloc ((SizeC 64)) (QualC Unr)) (IGroup 3 (QualC Unr))
        (ISet_local 0) (IGet_local 0 (QualC Unr)) IUngroup IDrop (ISet_local 1)
        IDrop (IGet_local 1 (QualC Unr)) (IVal Unit) (ISet_local 1)
        (IGet_local 0 (QualC Unr)) IUngroup (ISet_local 2) IDrop IDrop
        (IGet_local 2 (QualC Unr)) (IVal Unit) (ISet_local 2)
        (IGet_local 0 (QualC Unr)) IUngroup IDrop IDrop (ISet_local 3)
        (IGet_local 3 (QualC Unr)) (IVal Unit) (ISet_local 3)
        (IGroup 3 (QualC Unr)) (IVal Unit) (ISet_local 0))))
     () (0)) |}]
;;

let prog5 =
  let list_type = "Rec a1. ( + Unit, ( * Int, a1))" in
  let variant_type = [%string "( + Unit, ( * Int, %{list_type}))"] in
  [%string
    {| 
let empty = fold inj 0 %{variant_type} () as %{list_type} in
let add = fun []. l : %{list_type}, x : Int ->
  fold inj 1 %{variant_type} ( * x, l) as %{list_type}
in
let remove = fun []. l : %{list_type} ->
  case l = unfold l in
  { empty
  ; proj 1 l
  }
in
let non_empty = (add [] (empty, 1)) in
let non_empty = (add [] (non_empty, 2)) in
(remove [] (non_empty))
    |}]
;;

let%expect_test _ =
  test_typechecking prog5;
  [%expect
    {|
    (Info 72
     (Typ
      (Rec
       (Info 71
        (Typ
         (Variant
          ((Info 67 (Typ Unit))
           (Info 70 (Typ (Prod ((Info 68 (Typ Int)) (Info 69 (Typ (Var 0)))))))))))))) |}]
;;

let prog6 =
  [%string
    {|
global r = new_lin <Ref Int> in
export stash = fun []. l : <Ref Int> ->
  let () = (r := l) in
  l
in
export get_stashed = fun []. () : Unit ->
  !r
in
()
    |}]
;;

let%expect_test _ =
  test_typechecking prog6;
  [%expect {| (Info 13 (Typ Unit)) |}]
;;

let%expect_test _ =
  test_compilation prog6;
  [%expect
    {|
    (((Fun (stash)
       (()
        (((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       ()
       ((IGet_global 0)
        (IMemUnpack (() ((Unit (QualC Unr)))) ((1 (Unit (QualC Unr))))
         ((IGet_local 1 (QualC Lin))
          (IVariantMalloc 1
           ((Unit (QualC Unr))
            ((ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Lin)))
             (QualC Lin)))
           (QualC Lin))
          (IStructSwap 0)
          (IMemUnpack (() ()) ()
           ((IVariantCase (QualC Lin) (() ()) () ((IDrop) (IUnreachable)))))
          IDrop (IVal Unit)))
        IDrop (IGet_local 1 (QualC Lin))))
      (Fun (get_stashed)
       (()
        (((Unit (QualC Unr)) (Unit (QualC Unr)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       ((SizeC 64))
       ((IGet_global 0)
        (IMemUnpack (() ())
         ((2
           ((ExLoc
             ((Ref W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (QualC Lin))))
         ((IVal Unit)
          (IVariantMalloc 0
           ((Unit (QualC Unr))
            ((ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Lin)))
             (QualC Lin)))
           (QualC Lin))
          (IStructSwap 0)
          (IMemUnpack (() ())
           ((2
             ((ExLoc
               ((Ref W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Lin)))
              (QualC Lin))))
           ((IVariantCase (QualC Lin) (() ())
             ((2
               ((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin))))
             ((IUnreachable) ((ISet_local 2))))))
          IDrop))
        (IGet_local 2 (QualC Lin)) (IVal Unit) (ISet_local 2)))
      (Fun () (() (() ((Unit (QualC Unr))))) () ((IVal Unit))))
     ((GlobEx ()
       (ExLoc
        ((Ref W (LocV 0)
          (Struct
           ((((ExLoc
               ((Ref W (LocV 0)
                 (Variant
                  ((Unit (QualC Unr))
                   ((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin)))))
                (QualC Lin)))
              (QualC Lin))
             (SizeC 64)))))
         (QualC Unr)))
       ((IVal Unit)
        (IVariantMalloc 0
         ((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         (QualC Lin))
        (IStructMalloc ((SizeC 64)) (QualC Unr)))))
     (0 1 2)) |}]
;;

let prog7 =
  [%string
    {|
export linear_pair = fun []. l : <Ref Int> -> ( * l, 0) in
linear_pair
    |}]
;;

let%expect_test _ =
  test_compilation prog7;
  [%expect
    {|
    (((Fun (linear_pair)
       (()
        (((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         (((Prod
            (((ExLoc
               ((Ref W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Lin)))
              (QualC Lin))
             ((Num (Int S I32)) (QualC Unr))))
           (QualC Lin)))))
       ()
       ((IGet_local 1 (QualC Lin)) (IVal (Num (Int S I32) (Second 0)))
        (IGroup 2 (QualC Lin))))
      (Fun ()
       (()
        (()
         (((ExLoc
            ((Ref W (LocV 0)
              (Ex (QualC Unr) (SizeC 64)
               ((Prod
                 (((Var 0) (QualC Unr))
                  ((Coderef
                    (()
                     ((((Var 0) (QualC Unr))
                       ((ExLoc
                         ((Ref W (LocV 0)
                           (Struct
                            ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                          (QualC Lin)))
                        (QualC Lin)))
                      (((Prod
                         (((ExLoc
                            ((Ref W (LocV 0)
                              (Struct
                               ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                             (QualC Lin)))
                           (QualC Lin))
                          ((Num (Int S I32)) (QualC Unr))))
                        (QualC Lin))))))
                   (QualC Unr))))
                (QualC Unr))))
             (QualC Unr)))
           (QualC Unr)))))
       ()
       ((IVal Unit) (ICoderefI 0) (IInst ()) (IGroup 2 (QualC Unr))
        (IExistPack Unit
         (Ex (QualC Unr) (SizeC 64)
          ((Prod
            (((Var 0) (QualC Unr))
             ((Coderef
               (()
                ((((Var 0) (QualC Unr))
                  ((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin)))
                 (((Prod
                    (((ExLoc
                       ((Ref W (LocV 0)
                         (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Lin)))
                      (QualC Lin))
                     ((Num (Int S I32)) (QualC Unr))))
                   (QualC Lin))))))
              (QualC Unr))))
           (QualC Unr)))
         (QualC Unr)))))
     () (0 1)) |}]
;;

let prog8 = [%string {|
inj 0 ( + Unit, <Int>) ()
    |}]

let%expect_test _ =
  test_compilation prog8;
  [%expect
    {|
    (((Fun ()
       (()
        (()
         (((ExLoc
            ((Ref W (LocV 0)
              (Variant ((Unit (QualC Unr)) ((Num (Int S I32)) (QualC Lin)))))
             (QualC Unr)))
           (QualC Lin)))))
       ()
       ((IVal Unit)
        (IVariantMalloc 0 ((Unit (QualC Unr)) ((Num (Int S I32)) (QualC Lin)))
         (QualC Unr)))))
     () (0)) |}]
;;

let prog9 =
  [%string
    {|
global r = new_lin <Ref Int> in
export stash = fun []. l : <Ref Int> ->
  let () = (r := l) in ()
in
export get_stashed = fun []. () : Unit ->
  !r
in
()
    |}]
;;

let%expect_test _ =
  test_compilation prog9;
  [%expect
    {|
    (((Fun (stash)
       (()
        (((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         ((Unit (QualC Unr)))))
       ()
       ((IGet_global 0)
        (IMemUnpack (() ((Unit (QualC Unr)))) ((1 (Unit (QualC Unr))))
         ((IGet_local 1 (QualC Lin))
          (IVariantMalloc 1
           ((Unit (QualC Unr))
            ((ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Lin)))
             (QualC Lin)))
           (QualC Lin))
          (IStructSwap 0)
          (IMemUnpack (() ()) ()
           ((IVariantCase (QualC Lin) (() ()) () ((IDrop) (IUnreachable)))))
          IDrop (IVal Unit)))
        IDrop (IVal Unit)))
      (Fun (get_stashed)
       (()
        (((Unit (QualC Unr)) (Unit (QualC Unr)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))))
       ((SizeC 64))
       ((IGet_global 0)
        (IMemUnpack (() ())
         ((2
           ((ExLoc
             ((Ref W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (QualC Lin))))
         ((IVal Unit)
          (IVariantMalloc 0
           ((Unit (QualC Unr))
            ((ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Lin)))
             (QualC Lin)))
           (QualC Lin))
          (IStructSwap 0)
          (IMemUnpack (() ())
           ((2
             ((ExLoc
               ((Ref W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Lin)))
              (QualC Lin))))
           ((IVariantCase (QualC Lin) (() ())
             ((2
               ((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin))))
             ((IUnreachable) ((ISet_local 2))))))
          IDrop))
        (IGet_local 2 (QualC Lin)) (IVal Unit) (ISet_local 2)))
      (Fun () (() (() ((Unit (QualC Unr))))) () ((IVal Unit))))
     ((GlobEx ()
       (ExLoc
        ((Ref W (LocV 0)
          (Struct
           ((((ExLoc
               ((Ref W (LocV 0)
                 (Variant
                  ((Unit (QualC Unr))
                   ((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin)))))
                (QualC Lin)))
              (QualC Lin))
             (SizeC 64)))))
         (QualC Unr)))
       ((IVal Unit)
        (IVariantMalloc 0
         ((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         (QualC Lin))
        (IStructMalloc ((SizeC 64)) (QualC Unr)))))
     (0 1 2)) |}]
;;

let prog10 = [%string {|
let x = 3 in
let f = fun []. -> x in
(f [] ())
    |}]

let%expect_test _ =
  test_compilation prog10;
  [%expect
    {|
    (((Fun ()
       (()
        ((((ExLoc
            ((Ref W (LocV 0)
              (Struct
               ((((Prod (((Num (Int S I32)) (QualC Unr)))) (QualC Unr))
                 (SizeP (SizeC 0) (SizeC 32))))))
             (QualC Unr)))
           (QualC Unr)))
         (((Num (Int S I32)) (QualC Unr)))))
       ((SizeP (SizeC 0) (SizeC 32)) (SizeC 32))
       ((IGet_local 0 (QualC Unr))
        (IMemUnpack (() (((Prod (((Num (Int S I32)) (QualC Unr)))) (QualC Unr))))
         ()
         ((IStructGet 0) (ISet_local 1) IDrop (IGet_local 1 (QualC Unr))
          (IVal Unit) (ISet_local 1)))
        IUngroup (ISet_local 2) (IGet_local 2 (QualC Unr)) (IVal Unit)
        (ISet_local 2)))
      (Fun () (() (() (((Num (Int S I32)) (QualC Unr)))))
       ((SizeC 32) (SizeC 64) (SizeC 64))
       ((IVal (Num (Int S I32) (Second 3))) (ISet_local 0)
        (IGet_local 0 (QualC Unr)) (IGroup 1 (QualC Unr))
        (IStructMalloc ((SizeP (SizeC 0) (SizeC 32))) (QualC Unr)) (ICoderefI 0)
        (IInst ()) (IGroup 2 (QualC Unr))
        (IExistPack
         (ExLoc
          ((Ref W (LocV 0)
            (Struct
             ((((Prod (((Num (Int S I32)) (QualC Unr)))) (QualC Unr))
               (SizeP (SizeC 0) (SizeC 32))))))
           (QualC Unr)))
         (Ex (QualC Unr) (SizeC 64)
          ((Prod
            (((Var 0) (QualC Unr))
             ((Coderef
               (() ((((Var 0) (QualC Unr))) (((Num (Int S I32)) (QualC Unr))))))
              (QualC Unr))))
           (QualC Unr)))
         (QualC Unr))
        (ISet_local 1) (IGet_local 1 (QualC Unr))
        (IMemUnpack (() (((Num (Int S I32)) (QualC Unr)))) ()
         ((IExistUnpack (QualC Unr) (() (((Num (Int S I32)) (QualC Unr)))) ()
           (IUngroup (ISet_local 2) (IGet_local 2 (QualC Unr)) (IInst ())
            ICall_indirect (IVal Unit) (ISet_local 2)))))
        (IVal Unit) (ISet_local 1) (IVal Unit) (ISet_local 0))))
     () (0 1)) |}]
;;
