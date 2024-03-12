open! Core
open! Rich_wasm
module Interface = Rich_wasm_compiler_interface

let test modules =
  modules
  |> String.Map.of_alist_exn
  |> Rich_wasm_typechecker.typecheck
  |> Or_error.ok_exn
  |> String.Map.sexp_of_t Module_type.sexp_of_t
  |> print_s
;;

let test_annotation modules =
  modules
  |> String.Map.of_alist_exn
  |> Rich_wasm_typechecker.annotate
  |> Or_error.ok_exn
  |> String.Map.sexp_of_t Interface.Module.sexp_of_t
  |> print_s
;;

let test_fail modules =
  let modules = modules |> String.Map.of_alist_exn |> Rich_wasm_typechecker.typecheck in
  print_s [%sexp (modules : Module_type.t String.Map.t Or_error.t)]
;;

let%expect_test "polymorphism 1" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [ SizeC 2 ]); Type (QualC Unr, SizeP (SizeV 0, SizeC 1), Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , [ SizeC 3 ]
      , [ IGet_local (0, QualC Unr); ISet_local 1; IGet_local (1, QualC Unr) ] )
  in
  let module_ = [ f ], [], [] in
  test [ "module", module_ ];
  [%expect
    {|
    ((module
      ((funcs
        ((((Size () ((SizeC 2)))
           (Type (QualC Unr) (SizeP (SizeV 0) (SizeC 1)) Heapable))
          ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))))
       (globs ()) (table ()) (func_exports ()) (glob_exports ())))) |}]
;;

let%expect_test "polymorphism 2" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [])
          ; Size ([], [ SizeV 0 ])
          ; Qual ([], [])
          ; Qual ([ QualV 0 ], [])
          ; Type (QualV 1, SizeV 0, Heapable)
          ; Type (QualV 1, SizeV 1, Heapable)
          ]
        , ( [ Var 0, QualV 0; Var 1, QualV 1 ]
          , [ Prod [ Var 0, QualV 0; Var 1, QualV 1 ], QualV 0 ] ) )
      , [ SizeP (SizeV 1, SizeV 1) ]
      , [ IGet_local (0, QualV 0)
        ; IGet_local (1, QualV 1)
        ; IGroup (2, QualV 0)
        ; ISet_local 2
        ; IVal Unit
        ; IGet_local (2, QualV 0)
        ; IRet
        ] )
  in
  let module_ = [ f ], [], [] in
  test [ "module", module_ ];
  [%expect
    {|
    ((module
      ((funcs
        ((((Size () ()) (Size () ((SizeV 0))) (Qual () ()) (Qual ((QualV 0)) ())
           (Type (QualV 1) (SizeV 0) Heapable)
           (Type (QualV 1) (SizeV 1) Heapable))
          ((((Var 0) (QualV 0)) ((Var 1) (QualV 1)))
           (((Prod (((Var 0) (QualV 0)) ((Var 1) (QualV 1)))) (QualV 0)))))))
       (globs ()) (table ()) (func_exports ()) (glob_exports ())))) |}]
;;

let%expect_test "polymorphism fail qual" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [])
          ; Size ([], [ SizeV 0 ])
          ; Qual ([], [])
          ; Qual ([ QualV 0 ], [])
          ; Type (QualV 1, SizeV 0, Heapable)
          ; Type (QualV 1, SizeV 1, Heapable)
          ]
        , ( [ Var 0, QualV 0; Var 1, QualV 1 ]
          , [ Prod [ Var 0, QualV 0; Var 1, QualV 1 ], QualV 1 ] ) )
      , [ SizeP (SizeV 1, SizeV 1) ]
      , [ IGet_local (0, QualV 0)
        ; IGet_local (1, QualV 1)
        ; IGroup (2, QualV 1)
        ; ISet_local 2
        ; IVal Unit
        ; IGet_local (2, QualV 1)
        ; IRet
        ] )
  in
  let module_ = [ f ], [], [] in
  test_fail [ "module", module_ ];
  [%expect
    {|
    (Error
     (("Failed to typecheck module" (name module))
      (("Failed to typecheck function" (function_index 0))
       ("Contents of product were not leq product qualifier" (qual (QualV 1))
        (types (((Var 0) (QualV 0)) ((Var 1) (QualV 1)))))))) |}]
;;

let%expect_test "polymorphism fail size" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [])
          ; Size ([], [ SizeV 0 ])
          ; Qual ([], [])
          ; Qual ([ QualV 0 ], [])
          ; Type (QualV 1, SizeV 0, Heapable)
          ; Type (QualV 1, SizeV 1, Heapable)
          ]
        , ( [ Var 0, QualV 0; Var 1, QualV 1 ]
          , [ Prod [ Var 0, QualV 0; Var 1, QualV 1 ], QualV 0 ] ) )
      , [ SizeP (SizeV 0, SizeV 0) ]
      , [ IGet_local (0, QualV 0)
        ; IGet_local (1, QualV 1)
        ; IGroup (2, QualV 0)
        ; ISet_local 2
        ; IVal Unit
        ; IGet_local (2, QualV 0)
        ; IRet
        ] )
  in
  let module_ = [ f ], [], [] in
  test_fail [ "module", module_ ];
  [%expect
    {|
    (Error
     (("Failed to typecheck module" (name module))
      (("Failed to typecheck function" (function_index 0))
       ("Set local with type too large for slot"
        (type_ ((Prod (((Var 0) (QualV 0)) ((Var 1) (QualV 1)))) (QualV 0)))
        (size (SizeP (SizeP (SizeC 0) (SizeV 1)) (SizeV 0)))
        (slot_size (SizeP (SizeV 0) (SizeV 0))))))) |}]
;;

let%expect_test "instantiation fail" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [ SizeC 2 ]); Type (QualC Unr, SizeP (SizeV 0, SizeC 1), Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , [ SizeC 3 ]
      , [ IGet_local (0, QualC Unr); ISet_local 1; IGet_local (1, QualC Unr) ] )
  in
  let f_inst : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Unit, QualC Unr ]))
      , []
      , [ ICall (0, [ SizeI (SizeC 0); SizeI (SizeC 1) ]) ] )
  in
  let module_ = [ f; f_inst ], [], [] in
  test_fail [ "module", module_ ];
  [%expect
    {|
    (Error
     (("Failed to typecheck module" (name module))
      (("Failed to typecheck function" (function_index 1))
       ("Could not instantiate function type with index"
        (function_type
         (((Type (QualC Unr) (SizeP (SizeC 0) (SizeC 1)) Heapable))
          ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr))))))
        (index (SizeI (SizeC 1))))))) |}]
;;

let%expect_test "polymorphic call" =
  let f : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], [])
          ; Size ([ SizeV 0 ], [])
          ; Qual ([], [])
          ; Type (QualV 0, SizeV 1, Heapable)
          ]
        , ( [ Var 0, QualV 0 ]
          , [ ( ExLoc (Ref (W, LocV 0, Struct [ (Var 0, QualV 0), SizeV 0 ]), QualC Lin)
              , QualC Lin )
            ] ) )
      , []
      , [ IGet_local (0, QualV 0); IStructMalloc ([ SizeV 0 ], QualC Lin) ] )
  in
  let f_inst : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Unit, QualC Unr ]))
      , []
      , [ IVal Unit
        ; IGroup (1, QualC Lin)
        ; ICall
            ( 0
            , [ SizeI (SizeC 0)
              ; SizeI (SizeC 30000000)
              ; QualI (QualC Lin)
              ; PretypeI (Prod [ Unit, QualC Unr ])
              ] )
        ; IMemUnpack
            (([], []), [], [ IVal Unit; IStructSwap 0; IUngroup; IDrop; IStructFree ])
        ; IVal Unit
        ] )
  in
  let module_ = [ f; f_inst ], [], [] in
  test_fail [ "module", module_ ];
  [%expect
    {|
    (Ok
     ((module
       ((funcs
         ((((Size () ()) (Size ((SizeV 0)) ()) (Qual () ())
            (Type (QualV 0) (SizeV 1) Heapable))
           ((((Var 0) (QualV 0)))
            (((ExLoc
               ((Ref W (LocV 0) (Struct ((((Var 0) (QualV 0)) (SizeV 0)))))
                (QualC Lin)))
              (QualC Lin)))))
          (() (() ((Unit (QualC Unr)))))))
        (globs ()) (table ()) (func_exports ()) (glob_exports ()))))) |}]
;;

let%expect_test _ =
  let m =
    let f =
      Instruction.Fun
        ( []
        , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
        , []
        , [ IVal (Num (Int (U, I64), First (Int64.of_int 40))); IVal Unit; IDrop ] )
    in
    [ f ], [], [ 0 ]
  in
  test_annotation [ "module", m ];
  [%expect
    {|
    ((module
      (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
         ((IVal (Num (Int U I64) (First 40))) (IVal Unit) IDrop)))
       () (0)))) |}]
;;

module Example_1_rwasm = struct
  let l3_module =
    let lin_ref : Type.t =
      ( ExLoc
          ( Ref (W, LocV 0, Struct [ (Num (Int (U, I32)), QualC Unr), SizeC 32 ])
          , QualC Lin )
      , QualC Lin )
    in
    let stash : Instruction.f =
      FunIm ([], ([], ([ lin_ref ], [ lin_ref ])), Import ("ml_module", "stash"))
    in
    let get_stashed : Instruction.f =
      FunIm
        ([], ([], ([ Unit, QualC Unr ], [ lin_ref ])), Import ("ml_module", "get_stashed"))
    in
    let main : Instruction.f =
      Fun
        ( []
        , ([], ([], []))
        , []
        , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
          ; IStructMalloc ([ SizeC 32 ], QualC Lin)
          ; ICall (0, [])
          ; IMemUnpack (([], []), [], [ IStructFree ])
          ; IVal Unit
          ; ICall (1, [])
          ; IMemUnpack (([], []), [], [ IStructFree ])
          ] )
    in
    [ stash; get_stashed; main ], [], []
  ;;

  let ml_module =
    let lin_ref : Type.t =
      ( ExLoc
          ( Ref (W, LocV 0, Struct [ (Num (Int (U, I32)), QualC Unr), SizeC 32 ])
          , QualC Lin )
      , QualC Lin )
    in
    let variant_cases : Type.t list = [ Unit, QualC Unr; lin_ref ] in
    let variant_type : Type.t =
      ExLoc (Ref (W, LocV 0, Variant variant_cases), QualC Lin), QualC Lin
    in
    let global_pretype : Type.pt =
      ExLoc (Ref (W, LocV 0, Struct [ variant_type, SizeC 64 ]), QualC Unr)
    in
    let global : Glob.t =
      GlobEx
        ( []
        , global_pretype
        , [ IVal Unit
          ; IVariantMalloc (0, variant_cases, QualC Lin)
          ; IStructMalloc ([ SizeC 64 ], QualC Unr)
          ] )
    in
    let stash : Instruction.f =
      Fun
        ( [ "stash" ]
        , ([], ([ lin_ref ], [ lin_ref ]))
        , []
        , [ IGet_global 0
          ; IMemUnpack
              ( ([], [])
              , [ 0, variant_type ]
              , [ IGet_local (0, QualC Lin)
                ; IVariantMalloc (1, variant_cases, QualC Lin)
                ; IStructSwap 0
                ; ISet_local 0
                ; IDrop
                ] )
          ; IGet_local (0, QualC Lin)
          ; IMemUnpack
              ( ([], [ lin_ref ])
              , []
              , [ IVariantCase
                    ( QualC Lin
                    , ([], [ lin_ref ])
                    , []
                    , [ [ IDrop; IGet_local (0, QualC Lin) ]; [ IUnreachable ] ] )
                ] )
          ] )
    in
    let get_stashed : Instruction.f =
      Fun
        ( [ "get_stashed" ]
        , ([], ([ Unit, QualC Unr ], [ lin_ref ]))
        , [ SizeC 64 ]
        , [ IGet_global 0
          ; IMemUnpack
              ( ([], [ variant_type ])
              , []
              , [ IVal Unit
                ; IVariantMalloc (0, variant_cases, QualC Lin)
                ; IStructSwap 0
                ; ISet_local 1
                ; IDrop
                ; IGet_local (1, QualC Lin)
                ] )
          ; IMemUnpack
              ( ([], [ lin_ref ])
              , []
              , [ IVariantCase (QualC Lin, ([], [ lin_ref ]), [], [ [ IUnreachable ]; [] ])
                ] )
          ] )
    in
    let main : Instruction.f =
      Fun ([], ([], ([], [ Unit, QualC Unr ])), [], [ IVal Unit ])
    in
    [ stash; get_stashed; main ], [ global ], []
  ;;

  let%expect_test _ =
    test_fail [ "ml_module", ml_module; "l3_module", l3_module ];
    [%expect
      {|
      (Error
       (("Failed to typecheck module" (name ml_module))
        (("Failed to typecheck function" (function_index 0))
         ("Qual did not match annotated type on local get" (expected (QualC Lin))
          (got (QualC Unr)) (slot_number 0) (slot_type Unit))))) |}]
  ;;
end

module Example_2 = struct
  let program_configuration_ref : Type.t =
    ( ExLoc
        (Ref (R, LocV 0, Struct [ (Num (Int (U, I32)), QualC Unr), SizeC 32 ]), QualC Unr)
    , QualC Unr )
  ;;

  let contents : Type.t =
    ( ExLoc
        ( Prod
            [ ( Cap (W, LocV 0, Struct [ (Num (Int (U, I32)), QualC Unr), SizeC 32 ])
              , QualC Lin )
            ; Ptr (LocV 0), QualC Unr
            ]
        , QualC Lin )
    , QualC Lin )
  ;;

  let linear_component : Type.t =
    ( ExLoc
        ( Ref
            (W, LocV 0, Struct [ contents, SizeC 64; program_configuration_ref, SizeC 64 ])
        , QualC Lin )
    , QualC Lin )
  ;;

  let pretype : Type.pt =
    ExLoc (Ref (W, LocV 0, Struct [ linear_component, SizeC 64 ]), QualC Unr)
  ;;

  let type_ : Type.t = pretype, QualC Unr

  let new_counter_internals : Instruction.f =
    Fun
      ( []
      , ([], ([ program_configuration_ref ], [ linear_component ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IStructMalloc ([ SizeC 32 ], QualC Lin)
        ; IMemUnpack
            ( ([], [ contents ])
            , []
            , [ IRefSplit; IGroup (2, QualC Lin); IMemPack (LocV 0) ] )
        ; IGet_local (0, QualC Unr)
        ; IStructMalloc ([ SizeC 64; SizeC 64 ], QualC Lin)
        ] )
  ;;

  let increment : Instruction.f =
    Fun
      ( []
      , ([], ([ type_ ], [ Num (Int (U, I32)), QualC Unr ]))
      , [ SizeC 32 ]
      , [ IGet_local (0, QualC Unr)
        ; IMemUnpack
            ( ([], [])
            , [ 1, (Num (Int (U, I32)), QualC Unr) ]
            , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
              ; IStructMalloc ([ SizeC 32 ], QualC Unr)
              ; IMemUnpack
                  ( ([], [ program_configuration_ref ])
                  , []
                  , [ IRefDemote; IMemPack (LocV 0) ] )
              ; ICall (0, [])
              ; IStructSwap 0
              ; IMemUnpack
                  ( ([], [ linear_component ])
                  , [ 1, (Num (Int (U, I32)), QualC Unr) ]
                  , [ IStructGet 1
                    ; IMemUnpack
                        ( ([], [])
                        , [ 1, (Num (Int (U, I32)), QualC Unr) ]
                        , [ IStructGet 0; ISet_local 1; IDrop ] )
                    ; IVal Unit
                    ; IStructSwap 0
                    ; IMemUnpack
                        ( ([], [ contents ])
                        , []
                        , [ IUngroup
                          ; IRefJoin
                          ; IStructGet 0
                          ; IGet_local (1, QualC Unr)
                          ; INe (Ib (I32, Iadd))
                          ; ITee_local 1
                          ; IStructSet 0
                          ; IRefSplit
                          ; IGroup (2, QualC Lin)
                          ; IMemPack (LocV 0)
                          ] )
                    ; IStructSwap 0
                    ; IDrop
                    ; IMemPack (LocV 0)
                    ] )
              ; IStructSwap 0
              ; IMemUnpack
                  ( ([], [])
                  , []
                  , [ IVal Unit
                    ; IStructSwap 0
                    ; IMemUnpack (([], []), [], [ IUngroup; IRefJoin; IStructFree ])
                    ; IStructFree
                    ] )
              ; IDrop
              ] )
        ; IGet_local (1, QualC Unr)
        ] )
  ;;

  let exist_heaptype : Type.ht =
    Ex
      ( QualC Unr
      , SizeC 64
      , ( Prod
            [ Var 0, QualC Unr
            ; ( Coderef ([], ([ Var 0, QualC Unr ], [ Num (Int (U, I32)), QualC Unr ]))
              , QualC Unr )
            ]
        , QualC Unr ) )
  ;;

  let exist_type : Type.t = ExLoc (Ref (W, LocV 0, exist_heaptype), QualC Unr), QualC Unr

  let create : Instruction.f =
    Fun
      ( []
      , ([], ([ program_configuration_ref ], [ exist_type ]))
      , []
      , [ IGet_local (0, QualC Unr)
        ; ICall (0, [])
        ; IStructMalloc ([ SizeC 64 ], QualC Unr)
        ; ICoderefI 0
        ; IGroup (2, QualC Unr)
        ; IExistPack (pretype, exist_heaptype, QualC Unr)
        ] )
  ;;

  let module_ = [ new_counter_internals; increment; create ], [], [ 1 ]

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            ((((ExLoc
                ((Ref R (LocV 0)
                  (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Unr)))
               (QualC Unr)))
             (((ExLoc
                ((Ref W (LocV 0)
                  (Struct
                   ((((ExLoc
                       ((Prod
                         (((Cap W (LocV 0)
                            (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                           (QualC Lin))
                          ((Ptr (LocV 0)) (QualC Unr))))
                        (QualC Lin)))
                      (QualC Lin))
                     (SizeC 64))
                    (((ExLoc
                       ((Ref R (LocV 0)
                         (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Unr)))
                      (QualC Unr))
                     (SizeC 64)))))
                 (QualC Lin)))
               (QualC Lin)))))
           ()
           ((IVal (Num (Int U I32) (Second 0)))
            (IStructMalloc ((SizeC 32)) (QualC Lin)
             (((Num (Int U I32)) (QualC Unr))))
            (IMemUnpack
             (()
              (((ExLoc
                 ((Prod
                   (((Cap W (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin))
                    ((Ptr (LocV 0)) (QualC Unr))))
                  (QualC Lin)))
                (QualC Lin))))
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
            (IGet_local 0 (QualC Unr)
             (ExLoc
              ((Ref R (LocV 0)
                (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Unr))))
            (IStructMalloc ((SizeC 64) (SizeC 64)) (QualC Lin)
             (((ExLoc
                ((Prod
                  (((Cap W (LocV 0)
                     (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin))
                   ((Ptr (LocV 0)) (QualC Unr))))
                 (QualC Lin)))
               (QualC Lin))
              ((ExLoc
                ((Ref R (LocV 0)
                  (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Unr)))
               (QualC Unr))))))
          (Fun ()
           (()
            ((((ExLoc
                ((Ref W (LocV 0)
                  (Struct
                   ((((ExLoc
                       ((Ref W (LocV 0)
                         (Struct
                          ((((ExLoc
                              ((Prod
                                (((Cap W (LocV 0)
                                   (Struct
                                    ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                                  (QualC Lin))
                                 ((Ptr (LocV 0)) (QualC Unr))))
                               (QualC Lin)))
                             (QualC Lin))
                            (SizeC 64))
                           (((ExLoc
                              ((Ref R (LocV 0)
                                (Struct
                                 ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                               (QualC Unr)))
                             (QualC Unr))
                            (SizeC 64)))))
                        (QualC Lin)))
                      (QualC Lin))
                     (SizeC 64)))))
                 (QualC Unr)))
               (QualC Unr)))
             (((Num (Int U I32)) (QualC Unr)))))
           ((SizeC 32))
           ((IGet_local 0 (QualC Unr)
             (ExLoc
              ((Ref W (LocV 0)
                (Struct
                 ((((ExLoc
                     ((Ref W (LocV 0)
                       (Struct
                        ((((ExLoc
                            ((Prod
                              (((Cap W (LocV 0)
                                 (Struct
                                  ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                                (QualC Lin))
                               ((Ptr (LocV 0)) (QualC Unr))))
                             (QualC Lin)))
                           (QualC Lin))
                          (SizeC 64))
                         (((ExLoc
                            ((Ref R (LocV 0)
                              (Struct
                               ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                             (QualC Unr)))
                           (QualC Unr))
                          (SizeC 64)))))
                      (QualC Lin)))
                    (QualC Lin))
                   (SizeC 64)))))
               (QualC Unr))))
            (IMemUnpack (() ()) ((1 ((Num (Int U I32)) (QualC Unr))))
             ((IVal (Num (Int U I32) (Second 0)))
              (IStructMalloc ((SizeC 32)) (QualC Unr)
               (((Num (Int U I32)) (QualC Unr))))
              (IMemUnpack
               (()
                (((ExLoc
                   ((Ref R (LocV 0)
                     (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Unr)))
                  (QualC Unr))))
               () (IRefDemote (IMemPack (LocV 1))))
              (ICall 0 ())
              (IStructSwap 0
               (((ExLoc
                  ((Ref W (LocV 0)
                    (Struct
                     ((((ExLoc
                         ((Prod
                           (((Cap W (LocV 0)
                              (Struct
                               ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                             (QualC Lin))
                            ((Ptr (LocV 0)) (QualC Unr))))
                          (QualC Lin)))
                        (QualC Lin))
                       (SizeC 64))
                      (((ExLoc
                         ((Ref R (LocV 0)
                           (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                          (QualC Unr)))
                        (QualC Unr))
                       (SizeC 64)))))
                   (QualC Lin)))
                 (QualC Lin))))
              (IMemUnpack
               (()
                (((ExLoc
                   ((Ref W (LocV 0)
                     (Struct
                      ((((ExLoc
                          ((Prod
                            (((Cap W (LocV 0)
                               (Struct
                                ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                              (QualC Lin))
                             ((Ptr (LocV 0)) (QualC Unr))))
                           (QualC Lin)))
                         (QualC Lin))
                        (SizeC 64))
                       (((ExLoc
                          ((Ref R (LocV 0)
                            (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                           (QualC Unr)))
                         (QualC Unr))
                        (SizeC 64)))))
                    (QualC Lin)))
                  (QualC Lin))))
               ((1 ((Num (Int U I32)) (QualC Unr))))
               ((IStructGet 1
                 (((ExLoc
                    ((Prod
                      (((Cap W (LocV 0)
                         (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Lin))
                       ((Ptr (LocV 0)) (QualC Unr))))
                     (QualC Lin)))
                   (QualC Lin))
                  ((ExLoc
                    ((Ref R (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Unr)))
                   (QualC Unr))))
                (IMemUnpack (() ()) ((1 ((Num (Int U I32)) (QualC Unr))))
                 ((IStructGet 0 (((Num (Int U I32)) (QualC Unr))))
                  (ISet_local 1 ((Num (Int U I32)) (QualC Unr))) IDrop))
                (IVal Unit)
                (IStructSwap 0
                 (((ExLoc
                    ((Prod
                      (((Cap W (LocV 0)
                         (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Lin))
                       ((Ptr (LocV 0)) (QualC Unr))))
                     (QualC Lin)))
                   (QualC Lin))
                  ((ExLoc
                    ((Ref R (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Unr)))
                   (QualC Unr))))
                (IMemUnpack
                 (()
                  (((ExLoc
                     ((Prod
                       (((Cap W (LocV 0)
                          (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                         (QualC Lin))
                        ((Ptr (LocV 0)) (QualC Unr))))
                      (QualC Lin)))
                    (QualC Lin))))
                 ()
                 (IUngroup IRefJoin
                  (IStructGet 0 (((Num (Int U I32)) (QualC Unr))))
                  (IGet_local 1 (QualC Unr) (Num (Int U I32))) (INe (Ib I32 Iadd))
                  (ITee_local 1 ((Num (Int U I32)) (QualC Unr)))
                  (IStructSet 0 (((Num (Int U I32)) (QualC Unr)))) IRefSplit
                  (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
                (IStructSwap 0
                 ((Unit (QualC Unr))
                  ((ExLoc
                    ((Ref R (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Unr)))
                   (QualC Unr))))
                IDrop (IMemPack (LocV 1))))
              (IStructSwap 0
               (((ExLoc
                  ((Ref W (LocV 0)
                    (Struct
                     ((((ExLoc
                         ((Prod
                           (((Cap W (LocV 0)
                              (Struct
                               ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                             (QualC Lin))
                            ((Ptr (LocV 0)) (QualC Unr))))
                          (QualC Lin)))
                        (QualC Lin))
                       (SizeC 64))
                      (((ExLoc
                         ((Ref R (LocV 0)
                           (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                          (QualC Unr)))
                        (QualC Unr))
                       (SizeC 64)))))
                   (QualC Lin)))
                 (QualC Lin))))
              (IMemUnpack (() ()) ()
               ((IVal Unit)
                (IStructSwap 0
                 (((ExLoc
                    ((Prod
                      (((Cap W (LocV 0)
                         (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Lin))
                       ((Ptr (LocV 0)) (QualC Unr))))
                     (QualC Lin)))
                   (QualC Lin))
                  ((ExLoc
                    ((Ref R (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Unr)))
                   (QualC Unr))))
                (IMemUnpack (() ()) ()
                 (IUngroup IRefJoin
                  (IStructFree (((Num (Int U I32)) (QualC Unr))))))
                (IStructFree
                 ((Unit (QualC Unr))
                  ((ExLoc
                    ((Ref R (LocV 0)
                      (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Unr)))
                   (QualC Unr))))))
              IDrop))
            (IGet_local 1 (QualC Unr) (Num (Int U I32)))))
          (Fun ()
           (()
            ((((ExLoc
                ((Ref R (LocV 0)
                  (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Unr)))
               (QualC Unr)))
             (((ExLoc
                ((Ref W (LocV 0)
                  (Ex (QualC Unr) (SizeC 64)
                   ((Prod
                     (((Var 0) (QualC Unr))
                      ((Coderef
                        (()
                         ((((Var 0) (QualC Unr)))
                          (((Num (Int U I32)) (QualC Unr))))))
                       (QualC Unr))))
                    (QualC Unr))))
                 (QualC Unr)))
               (QualC Unr)))))
           ()
           ((IGet_local 0 (QualC Unr)
             (ExLoc
              ((Ref R (LocV 0)
                (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Unr))))
            (ICall 0 ())
            (IStructMalloc ((SizeC 64)) (QualC Unr)
             (((ExLoc
                ((Ref W (LocV 0)
                  (Struct
                   ((((ExLoc
                       ((Prod
                         (((Cap W (LocV 0)
                            (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                           (QualC Lin))
                          ((Ptr (LocV 0)) (QualC Unr))))
                        (QualC Lin)))
                      (QualC Lin))
                     (SizeC 64))
                    (((ExLoc
                       ((Ref R (LocV 0)
                         (Struct ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                        (QualC Unr)))
                      (QualC Unr))
                     (SizeC 64)))))
                 (QualC Lin)))
               (QualC Lin))))
            (ICoderefI 0) (IGroup 2 (QualC Unr))
            (IExistPack
             (ExLoc
              ((Ref W (LocV 0)
                (Struct
                 ((((ExLoc
                     ((Ref W (LocV 0)
                       (Struct
                        ((((ExLoc
                            ((Prod
                              (((Cap W (LocV 0)
                                 (Struct
                                  ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                                (QualC Lin))
                               ((Ptr (LocV 0)) (QualC Unr))))
                             (QualC Lin)))
                           (QualC Lin))
                          (SizeC 64))
                         (((ExLoc
                            ((Ref R (LocV 0)
                              (Struct
                               ((((Num (Int U I32)) (QualC Unr)) (SizeC 32)))))
                             (QualC Unr)))
                           (QualC Unr))
                          (SizeC 64)))))
                      (QualC Lin)))
                    (QualC Lin))
                   (SizeC 64)))))
               (QualC Unr)))
             (Ex (QualC Unr) (SizeC 64)
              ((Prod
                (((Var 0) (QualC Unr))
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I32)) (QualC Unr))))))
                  (QualC Unr))))
               (QualC Unr)))
             (QualC Unr)))))
         () (1)))) |}]
  ;;
end

module Example_1 = struct
  let%expect_test _ =
    let module_ =
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
      (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
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
     () (0 1 2)) 
    |}
    in
    let ml_module_stubs =
      ( [ Instruction.Fun
            ( [ "stash" ]
            , ( []
              , ( [ ( ExLoc
                        ( Ref
                            ( W
                            , LocV 0
                            , Struct [ (Num (Int (S, I32)), QualC Unr), SizeC 32 ] )
                        , QualC Lin )
                    , QualC Lin )
                  ]
                , [ ( ExLoc
                        ( Ref
                            ( W
                            , LocV 0
                            , Struct [ (Num (Int (S, I32)), QualC Unr), SizeC 32 ] )
                        , QualC Lin )
                    , QualC Lin )
                  ] ) )
            , []
            , [ IUnreachable ] )
        ; Instruction.Fun
            ( [ "get_stashed" ]
            , ( []
              , ( [ Unit, QualC Unr ]
                , [ ( ExLoc
                        ( Ref
                            ( W
                            , LocV 0
                            , Struct [ (Num (Int (S, I32)), QualC Unr), SizeC 32 ] )
                        , QualC Lin )
                    , QualC Lin )
                  ] ) )
            , []
            , [ IUnreachable ] )
        ]
      , []
      , [] )
    in
    test_annotation
      [ "l3", module_ |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp
      ; "ml", ml_module_stubs
      ];
    [%expect
      {|
      ((l3
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
          (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
           ((SizeC 64) (SizeC 64) (SizeC 32) (SizeC 32) (SizeC 32))
           ((ICoderefI 0) (IQualify (QualC Lin))
            (ISet_local 0
             ((Coderef
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
                   (QualC Lin))))))
              (QualC Lin)))
            (ICoderefI 1) (IQualify (QualC Lin))
            (ISet_local 1
             ((Coderef
               (()
                (((Unit (QualC Unr)))
                 (((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin))))))
              (QualC Lin)))
            (IVal (Num (Int S I32) (Second 42)))
            (IStructMalloc ((SizeC 32)) (QualC Lin)
             (((Num (Int S I32)) (QualC Unr))))
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
            (IMemUnpack
             (()
              (((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin))))
             () (IUngroup IRefJoin (IMemPack (LocV 1))))
            (IGet_local 0 (QualC Lin)
             (Coderef
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
                  (QualC Lin)))))))
            (ICall_indirect
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
            (IMemUnpack
             (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))) ()
             (IUngroup IRefJoin (IVal Unit)
              (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
              (ISet_local 2 ((Num (Int S I32)) (QualC Unr)))
              (IStructFree ((Unit (QualC Unr))))
              (IGet_local 2 (QualC Unr) (Num (Int S I32))) (IVal Unit)
              (ISet_local 2 (Unit (QualC Unr))) (IMemPack (LocV 1))
              (IQualify (QualC Lin))))
            (IMemUnpack
             (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin))))
             ((1 (Unit (QualC Unr))))
             ((ISet_local 3 ((Num (Int S I32)) (QualC Unr))) (IVal Unit)
              (IGet_local 1 (QualC Lin)
               (Coderef
                (()
                 (((Unit (QualC Unr)))
                  (((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin)))))))
              (ICall_indirect
               (((Unit (QualC Unr)))
                (((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin)))))
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
               () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
              (IMemUnpack
               (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))) ()
               (IUngroup IRefJoin (IVal Unit)
                (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
                (ISet_local 4 ((Num (Int S I32)) (QualC Unr)))
                (IStructFree ((Unit (QualC Unr))))
                (IGet_local 4 (QualC Unr) (Num (Int S I32))) (IVal Unit)
                (ISet_local 4 (Unit (QualC Unr))) (IMemPack (LocV 1))
                (IQualify (QualC Lin))))
              (IVal Unit) (ISet_local 3 (Unit (QualC Unr)))))
            (IVal Unit) (ISet_local 1 (Unit (QualC Unr))) (IVal Unit)
            (ISet_local 0 (Unit (QualC Unr))))))
         () (0 1 2)))
       (ml
        (((Fun (stash)
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
           () (IUnreachable))
          (Fun (get_stashed)
           (()
            (((Unit (QualC Unr)))
             (((ExLoc
                ((Ref W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin)))
               (QualC Lin)))))
           () (IUnreachable)))
         () ()))) |}]
  ;;

  let%expect_test _ =
    let module_ =
      {| 

    (((FunIm ()
       (()
        ((((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Lin)))
           (QualC Lin)))
         ((Unit (QualC Unr)))))
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
      (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
       ((SizeC 64) (SizeC 64) (SizeC 32))
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
        (IGet_local 0 (QualC Lin)) ICall_indirect IDrop (IVal Unit)
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
     () (0 1 2)) 
    |}
    in
    let ml_module_stubs =
      ( [ Instruction.Fun
            ( [ "stash" ]
            , ( []
              , ( [ ( ExLoc
                        ( Ref
                            ( W
                            , LocV 0
                            , Struct [ (Num (Int (S, I32)), QualC Unr), SizeC 32 ] )
                        , QualC Lin )
                    , QualC Lin )
                  ]
                , [ Unit, QualC Unr ] ) )
            , []
            , [ IUnreachable ] )
        ; Instruction.Fun
            ( [ "get_stashed" ]
            , ( []
              , ( [ Unit, QualC Unr ]
                , [ ( ExLoc
                        ( Ref
                            ( W
                            , LocV 0
                            , Struct [ (Num (Int (S, I32)), QualC Unr), SizeC 32 ] )
                        , QualC Lin )
                    , QualC Lin )
                  ] ) )
            , []
            , [ IUnreachable ] )
        ]
      , []
      , [] )
    in
    test_annotation
      [ "l3", module_ |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp
      ; "ml", ml_module_stubs
      ];
    [%expect
      {|
        ((l3
          (((FunIm ()
             (()
              ((((ExLoc
                  ((Ref W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                   (QualC Lin)))
                 (QualC Lin)))
               ((Unit (QualC Unr)))))
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
            (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
             ((SizeC 64) (SizeC 64) (SizeC 32))
             ((ICoderefI 0) (IQualify (QualC Lin))
              (ISet_local 0
               ((Coderef
                 (()
                  ((((ExLoc
                      ((Ref W (LocV 0)
                        (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                       (QualC Lin)))
                     (QualC Lin)))
                   ((Unit (QualC Unr))))))
                (QualC Lin)))
              (ICoderefI 1) (IQualify (QualC Lin))
              (ISet_local 1
               ((Coderef
                 (()
                  (((Unit (QualC Unr)))
                   (((ExLoc
                      ((Ref W (LocV 0)
                        (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                       (QualC Lin)))
                     (QualC Lin))))))
                (QualC Lin)))
              (IVal (Num (Int S I32) (Second 42)))
              (IStructMalloc ((SizeC 32)) (QualC Lin)
               (((Num (Int S I32)) (QualC Unr))))
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
               () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
              (IMemUnpack
               (()
                (((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin))))
               () (IUngroup IRefJoin (IMemPack (LocV 1))))
              (IGet_local 0 (QualC Lin)
               (Coderef
                (()
                 ((((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin)))
                  ((Unit (QualC Unr)))))))
              (ICall_indirect
               ((((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin)))
                ((Unit (QualC Unr)))))
              IDrop (IVal Unit)
              (IGet_local 1 (QualC Lin)
               (Coderef
                (()
                 (((Unit (QualC Unr)))
                  (((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin)))))))
              (ICall_indirect
               (((Unit (QualC Unr)))
                (((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin)))))
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
               () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
              (IMemUnpack
               (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))) ()
               (IUngroup IRefJoin (IVal Unit)
                (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
                (ISet_local 2 ((Num (Int S I32)) (QualC Unr)))
                (IStructFree ((Unit (QualC Unr))))
                (IGet_local 2 (QualC Unr) (Num (Int S I32))) (IVal Unit)
                (ISet_local 2 (Unit (QualC Unr))) (IMemPack (LocV 1))
                (IQualify (QualC Lin))))
              (IVal Unit) (ISet_local 1 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 0 (Unit (QualC Unr))))))
           () (0 1 2)))
         (ml
          (((Fun (stash)
             (()
              ((((ExLoc
                  ((Ref W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                   (QualC Lin)))
                 (QualC Lin)))
               ((Unit (QualC Unr)))))
             () (IUnreachable))
            (Fun (get_stashed)
             (()
              (((Unit (QualC Unr)))
               (((ExLoc
                  ((Ref W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                   (QualC Lin)))
                 (QualC Lin)))))
             () (IUnreachable)))
           () ()))) |}]
  ;;

  let%expect_test _ =
    let module_ =
      {| 
    (((Fun (stash)
       (()
        (((Unit (QualC Unr))
          ((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Unr)))
           (QualC Lin)))
         (((ExLoc
            ((Ref W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
             (QualC Unr)))
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
               (QualC Unr)))
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
             (QualC Unr)))
           (QualC Lin)))))
       ((SizeC 64))
       ((IGet_global 0)
        (IMemUnpack (() ())
         ((2
           ((ExLoc
             ((Ref W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Unr)))
            (QualC Lin))))
         ((IVal Unit)
          (IVariantMalloc 0
           ((Unit (QualC Unr))
            ((ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Unr)))
             (QualC Lin)))
           (QualC Lin))
          (IStructSwap 0)
          (IMemUnpack (() ())
           ((2
             ((ExLoc
               ((Ref W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Unr)))
              (QualC Lin))))
           ((IVariantCase (QualC Lin) (() ())
             ((2
               ((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Unr)))
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
                      (QualC Unr)))
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
             (QualC Unr)))
           (QualC Lin)))
         (QualC Lin))
        (IStructMalloc ((SizeC 64)) (QualC Unr)))))
     (0 1 2)) 


    |}
    in
    test_fail [ "ml", module_ |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp ];
    (* This should be an error because ML is duplicating a linear reference.
     * Specifically the local gets filled with an unrestricted unit after
     * the original linear value is read, which leads to this error. *)
    [%expect
      {|
      (Error
       (("Failed to typecheck module" (name ml))
        (("Failed to typecheck function" (function_index 0))
         ("Qual did not match annotated type on local get" (expected (QualC Lin))
          (got (QualC Unr)) (slot_number 1) (slot_type Unit))))) |}]
  ;;

  (* Adjusted example 1 which typechecks, as proposed in the paper. *)
  let%expect_test _ =
    let ml_module =
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
     (0 1 2)) 


      |}
    in
    let l3_module =
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
      (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
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
     () (0 1 2))
        |}
    in
    test_annotation
      [ "ml", ml_module |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp
      ; "l3", l3_module |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp
      ];
    [%expect
      {|
      ((l3
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
          (Fun () (() (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))))
           ((SizeC 64) (SizeC 64) (SizeC 32))
           ((ICoderefI 0) (IQualify (QualC Lin))
            (ISet_local 0
             ((Coderef
               (()
                (((Unit (QualC Unr))
                  ((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin)))
                 ((Unit (QualC Unr))))))
              (QualC Lin)))
            (ICoderefI 1) (IQualify (QualC Lin))
            (ISet_local 1
             ((Coderef
               (()
                (((Unit (QualC Unr)) (Unit (QualC Unr)))
                 (((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin))))))
              (QualC Lin)))
            (IVal Unit) (IVal (Num (Int S I32) (Second 42)))
            (IStructMalloc ((SizeC 32)) (QualC Lin)
             (((Num (Int S I32)) (QualC Unr))))
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
            (IMemUnpack
             (()
              (((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin))))
             () (IUngroup IRefJoin (IMemPack (LocV 1))))
            (IGet_local 0 (QualC Lin)
             (Coderef
              (()
               (((Unit (QualC Unr))
                 ((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin)))
                ((Unit (QualC Unr)))))))
            (ICall_indirect
             (((Unit (QualC Unr))
               ((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin)))
              ((Unit (QualC Unr)))))
            IDrop (IVal Unit) (IVal Unit)
            (IGet_local 1 (QualC Lin)
             (Coderef
              (()
               (((Unit (QualC Unr)) (Unit (QualC Unr)))
                (((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin)))))))
            (ICall_indirect
             (((Unit (QualC Unr)) (Unit (QualC Unr)))
              (((ExLoc
                 ((Ref W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                  (QualC Lin)))
                (QualC Lin)))))
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
            (IMemUnpack
             (() (((ExLoc ((Num (Int S I32)) (QualC Unr))) (QualC Lin)))) ()
             (IUngroup IRefJoin (IVal Unit)
              (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
              (ISet_local 2 ((Num (Int S I32)) (QualC Unr)))
              (IStructFree ((Unit (QualC Unr))))
              (IGet_local 2 (QualC Unr) (Num (Int S I32))) (IVal Unit)
              (ISet_local 2 (Unit (QualC Unr))) (IMemPack (LocV 1))
              (IQualify (QualC Lin))))
            (IVal Unit) (ISet_local 1 (Unit (QualC Unr))) (IVal Unit)
            (ISet_local 0 (Unit (QualC Unr))))))
         () (0 1 2)))
       (ml
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
             ((IGet_local 1 (QualC Lin)
               (ExLoc
                ((Ref W (LocV 0)
                  (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                 (QualC Lin))))
              (IVariantMalloc 1
               ((Unit (QualC Unr))
                ((ExLoc
                  ((Ref W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                   (QualC Lin)))
                 (QualC Lin)))
               (QualC Lin))
              (IStructSwap 0
               (((ExLoc
                  ((Ref W (LocV 0)
                    (Variant
                     ((Unit (QualC Unr))
                      ((ExLoc
                        ((Ref W (LocV 0)
                          (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                         (QualC Lin)))
                       (QualC Lin)))))
                   (QualC Lin)))
                 (QualC Lin))))
              (IMemUnpack (() ()) ()
               ((IVariantCase (QualC Lin)
                 ((Unit (QualC Unr))
                  ((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin)))
                 (() ()) () ((IDrop) (IUnreachable)))))
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
              (IStructSwap 0
               (((ExLoc
                  ((Ref W (LocV 0)
                    (Variant
                     ((Unit (QualC Unr))
                      ((ExLoc
                        ((Ref W (LocV 0)
                          (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                         (QualC Lin)))
                       (QualC Lin)))))
                   (QualC Lin)))
                 (QualC Lin))))
              (IMemUnpack (() ())
               ((2
                 ((ExLoc
                   ((Ref W (LocV 0)
                     (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                    (QualC Lin)))
                  (QualC Lin))))
               ((IVariantCase (QualC Lin)
                 ((Unit (QualC Unr))
                  ((ExLoc
                    ((Ref W (LocV 0)
                      (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                     (QualC Lin)))
                   (QualC Lin)))
                 (() ())
                 ((2
                   ((ExLoc
                     ((Ref W (LocV 0)
                       (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                      (QualC Lin)))
                    (QualC Lin))))
                 ((IUnreachable)
                  ((ISet_local 2
                    ((ExLoc
                      ((Ref W (LocV 0)
                        (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                       (QualC Lin)))
                     (QualC Lin))))))))
              IDrop))
            (IGet_local 2 (QualC Lin)
             (ExLoc
              ((Ref W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
               (QualC Lin))))
            (IVal Unit) (ISet_local 2 (Unit (QualC Unr)))))
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
            (IStructMalloc ((SizeC 64)) (QualC Unr)
             (((ExLoc
                ((Ref W (LocV 0)
                  (Variant
                   ((Unit (QualC Unr))
                    ((ExLoc
                      ((Ref W (LocV 0)
                        (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                       (QualC Lin)))
                     (QualC Lin)))))
                 (QualC Lin)))
               (QualC Lin)))))))
         (0 1 2)))) |}]
  ;;
end

module Group_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ] ) )
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 4)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)))))
           ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 1))) (IVal (Num (Int U I32) (Second 2)))
            (IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I32) (Second 4)))
            (IVal (Num (Int U I64) (First 5))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 6))))))
         () ()))) |}]
  ;;

  let test_with_groups : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ] ) )
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 4)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ; IGroup (3, QualC Unr)
        ; IGroup (7, QualC Unr)
        ; IUngroup
        ; IUngroup
        ] )
  ;;

  let module_ = [ test_with_groups ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)))))
           ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 1))) (IVal (Num (Int U I32) (Second 2)))
            (IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I32) (Second 4)))
            (IVal (Num (Int U I64) (First 5))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 6))) (IGroup 3 (QualC Unr))
            (IGroup 7 (QualC Unr)) IUngroup IUngroup)))
         () ()))) |}]
  ;;

  let test_with_locals : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ] ) )
      , [ Size.SizeC 288 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 4)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ; IGroup (3, QualC Unr)
        ; IGroup (7, QualC Unr)
        ; ISet_local 0
        ; IGet_local (0, QualC Unr)
        ; IUngroup
        ; IUngroup
        ] )
  ;;

  let module_ = [ test_with_locals ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)))))
           ((SizeC 288))
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 1))) (IVal (Num (Int U I32) (Second 2)))
            (IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I32) (Second 4)))
            (IVal (Num (Int U I64) (First 5))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 6))) (IGroup 3 (QualC Unr))
            (IGroup 7 (QualC Unr))
            (ISet_local 0
             ((Prod
               (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                ((Prod
                  (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                   ((Num (Int U I32)) (QualC Unr))))
                 (QualC Unr))))
              (QualC Unr)))
            (IGet_local 0 (QualC Unr)
             (Prod
              (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
               ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
               ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
               ((Prod
                 (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                  ((Num (Int U I32)) (QualC Unr))))
                (QualC Unr)))))
            IUngroup IUngroup)))
         () ()))) |}]
  ;;

  let test_with_struct : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ] ) )
      , [ Size.SizeC 288 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 4)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ; IGroup (3, QualC Unr)
        ; IGroup (7, QualC Unr)
        ; IStructMalloc ([ Size.SizeC 288 ], QualC Unr)
        ; IMemUnpack
            ( ( []
              , [ ( Prod
                      [ Num (Int (U, I32)), QualC Unr
                      ; Unit, QualC Unr
                      ; Num (Int (U, I32)), QualC Unr
                      ; Num (Int (U, I32)), QualC Unr
                      ; Num (Int (U, I64)), QualC Unr
                      ; Num (Int (U, I32)), QualC Unr
                      ; ( Prod
                            [ Num (Int (U, I64)), QualC Unr
                            ; Unit, QualC Unr
                            ; Num (Int (U, I32)), QualC Unr
                            ]
                        , QualC Unr )
                      ]
                  , QualC Unr )
                ] )
            , []
            , [ IStructGet 0
              ; ISet_local 0
              ; IDrop
              ; IGet_local (0, QualC Unr)
              ; IVal Unit
              ; ISet_local 0
              ] )
        ; IUngroup
        ; IUngroup
        ] )
  ;;

  let module_ = [ test_with_struct ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)))))
           ((SizeC 288))
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 1))) (IVal (Num (Int U I32) (Second 2)))
            (IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I32) (Second 4)))
            (IVal (Num (Int U I64) (First 5))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 6))) (IGroup 3 (QualC Unr))
            (IGroup 7 (QualC Unr))
            (IStructMalloc ((SizeC 288)) (QualC Unr)
             (((Prod
                (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                 ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Prod
                   (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                    ((Num (Int U I32)) (QualC Unr))))
                  (QualC Unr))))
               (QualC Unr))))
            (IMemUnpack
             (()
              (((Prod
                 (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                  ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                  ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                  ((Prod
                    (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                     ((Num (Int U I32)) (QualC Unr))))
                   (QualC Unr))))
                (QualC Unr))))
             ()
             ((IStructGet 0
               (((Prod
                  (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                   ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                   ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                   ((Prod
                     (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                      ((Num (Int U I32)) (QualC Unr))))
                    (QualC Unr))))
                 (QualC Unr))))
              (ISet_local 0
               ((Prod
                 (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                  ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                  ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                  ((Prod
                    (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                     ((Num (Int U I32)) (QualC Unr))))
                   (QualC Unr))))
                (QualC Unr)))
              IDrop
              (IGet_local 0 (QualC Unr)
               (Prod
                (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                 ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Prod
                   (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                    ((Num (Int U I32)) (QualC Unr))))
                  (QualC Unr)))))
              (IVal Unit) (ISet_local 0 (Unit (QualC Unr)))))
            IUngroup IUngroup)))
         () ()))) |}]
  ;;

  let identity_on_arbitrary_size_with_local : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], []); Type (QualC Unr, SizeV 0, Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , [ Size.SizeV 0 ]
      , [ IGet_local (0, QualC Unr); ISet_local 1; IGet_local (1, QualC Unr) ] )
  ;;

  let test_with_struct : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ; Unit, QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ] ) )
      , [ Size.SizeC 288 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 4)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVal Unit
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ; IGroup (3, QualC Unr)
        ; IGroup (7, QualC Unr)
        ; ICall
            ( 0
            , [ SizeI (SizeC 288)
              ; PretypeI
                  (Prod
                     [ Num (Int (U, I32)), QualC Unr
                     ; Unit, QualC Unr
                     ; Num (Int (U, I32)), QualC Unr
                     ; Num (Int (U, I32)), QualC Unr
                     ; Num (Int (U, I64)), QualC Unr
                     ; Num (Int (U, I32)), QualC Unr
                     ; ( Prod
                           [ Num (Int (U, I64)), QualC Unr
                           ; Unit, QualC Unr
                           ; Num (Int (U, I32)), QualC Unr
                           ]
                       , QualC Unr )
                     ])
              ] )
        ; IUngroup
        ; IUngroup
        ] )
  ;;

  let module_ = [ identity_on_arbitrary_size_with_local; test_with_struct ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (((Size () ()) (Type (QualC Unr) (SizeV 0) Heapable))
            ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
           ((SizeV 0))
           ((IGet_local 0 (QualC Unr) (Var 0)) (ISet_local 1 ((Var 0) (QualC Unr)))
            (IGet_local 1 (QualC Unr) (Var 0))))
          (Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
              ((Num (Int U I32)) (QualC Unr)))))
           ((SizeC 288))
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 1))) (IVal (Num (Int U I32) (Second 2)))
            (IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I32) (Second 4)))
            (IVal (Num (Int U I64) (First 5))) (IVal Unit)
            (IVal (Num (Int U I32) (Second 6))) (IGroup 3 (QualC Unr))
            (IGroup 7 (QualC Unr))
            (ICall 0
             ((SizeI (SizeC 288))
              (PretypeI
               (Prod
                (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))
                 ((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                 ((Prod
                   (((Num (Int U I64)) (QualC Unr)) (Unit (QualC Unr))
                    ((Num (Int U I32)) (QualC Unr))))
                  (QualC Unr)))))))
            IUngroup IUngroup)))
         () ()))) |}]
  ;;
end

module Function_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0))); IVal Unit ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))) ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit))))
         () ()))) |}]
  ;;

  let id : Instruction.f =
    Fun
      ( []
      , ( []
        , ( [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]
          , [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ] ) )
      , []
      , [ IGet_local (0, QualC Unr); IGet_local (1, QualC Unr) ] )
  ;;

  let with_id : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; ICall (0, [])
        ] )
  ;;

  let module_ = [ id; with_id ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            ((((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr)))
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr)))))
           ()
           ((IGet_local 0 (QualC Unr) (Num (Int U I32)))
            (IGet_local 1 (QualC Unr) Unit)))
          (Fun () (() (() (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))) ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit) (ICall 0 ()))))
         () ()))) |}]
  ;;

  let with_id_coderef : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal Unit
        ; ICoderefI 0
        ; ICall_indirect
        ] )
  ;;

  let module_ = [ id; with_id_coderef ], [], [ 0 ]

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            ((((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr)))
             (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr)))))
           ()
           ((IGet_local 0 (QualC Unr) (Num (Int U I32)))
            (IGet_local 1 (QualC Unr) Unit)))
          (Fun () (() (() (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))) ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal Unit) (ICoderefI 0)
            (ICall_indirect
             ((((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr)))
              (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))))))
         () (0)))) |}]
  ;;

  let id_i32 : Instruction.f =
    Fun
      ( []
      , ([], ([ Num (Int (U, I32)), QualC Unr ], [ Num (Int (U, I32)), QualC Unr ]))
      , []
      , [ IGet_local (0, QualC Unr) ] )
  ;;

  let id_abstract : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], []); Type (QualC Unr, SizeV 0, Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , []
      , [ IGet_local (0, QualC Unr) ] )
  ;;

  let id_abstract_bounded : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], []); Type (QualC Unr, SizeV 0, Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , []
      , [ IGet_local (0, QualC Unr) ] )
  ;;

  let i32_calls : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; ICall (1, [])
        ; ICall (2, [ SizeI (SizeC 32); PretypeI (Num (Int (U, I32))) ])
        ; ICall (3, [ SizeI (SizeC 32); PretypeI (Num (Int (U, I32))) ])
        ; IVal Unit
        ] )
  ;;

  let module_ = [ i32_calls; id_i32; id_abstract; id_abstract_bounded ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))) ()
           ((IVal (Num (Int U I32) (Second 0))) (ICall 1 ())
            (ICall 2 ((SizeI (SizeC 32)) (PretypeI (Num (Int U I32)))))
            (ICall 3 ((SizeI (SizeC 32)) (PretypeI (Num (Int U I32)))))
            (IVal Unit)))
          (Fun ()
           (()
            ((((Num (Int U I32)) (QualC Unr))) (((Num (Int U I32)) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Num (Int U I32)))))
          (Fun ()
           (((Size () ()) (Type (QualC Unr) (SizeV 0) Heapable))
            ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Var 0))))
          (Fun ()
           (((Size () ()) (Type (QualC Unr) (SizeV 0) Heapable))
            ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Var 0)))))
         () ()))) |}]
  ;;

  let indices : Instruction.f =
    Fun
      ( []
      , ( [ Qual ([], [])
          ; Qual ([], [])
          ; Size ([], [])
          ; Size ([], [])
          ; Type (QualV 1, SizeV 1, Heapable)
          ; Type (QualV 0, SizeV 0, Heapable)
          ]
        , ( [ Var 0, QualV 0; Var 1, QualV 1; Var 0, QualV 0 ]
          , [ Var 0, QualV 0; Var 1, QualV 1; Var 0, QualV 0 ] ) )
      , [ SizeV 0 ]
      , [ IGet_local (0, QualV 0)
        ; ISet_local 3
        ; IGet_local (2, QualV 0)
        ; IGet_local (1, QualV 1)
        ; IGet_local (3, QualV 0)
        ] )
  ;;

  let with_indices : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I32)), QualC Unr; Unit, QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 3)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 6)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 9)))
        ; ICall
            ( 1
            , [ QualI (QualC Unr)
              ; QualI (QualC Unr)
              ; SizeI (SizeC 64)
              ; SizeI (SizeC 43)
              ; PretypeI (Num (Int (U, I32)))
              ; PretypeI (Num (Int (U, I32)))
              ] )
        ; INe (Ib (I32, Iadd))
        ; INe (Ib (I32, Isub))
        ; IVal Unit
        ] )
  ;;

  let module_ = [ with_indices; indices ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I32)) (QualC Unr)) (Unit (QualC Unr))))) ()
           ((IVal (Num (Int U I32) (Second 3))) (IVal (Num (Int U I32) (Second 6)))
            (IVal (Num (Int U I32) (Second 9)))
            (ICall 1
             ((QualI (QualC Unr)) (QualI (QualC Unr)) (SizeI (SizeC 64))
              (SizeI (SizeC 43)) (PretypeI (Num (Int U I32)))
              (PretypeI (Num (Int U I32)))))
            (INe (Ib I32 Iadd)) (INe (Ib I32 Isub)) (IVal Unit)))
          (Fun ()
           (((Qual () ()) (Qual () ()) (Size () ()) (Size () ())
             (Type (QualV 1) (SizeV 1) Heapable)
             (Type (QualV 0) (SizeV 0) Heapable))
            ((((Var 0) (QualV 0)) ((Var 1) (QualV 1)) ((Var 0) (QualV 0)))
             (((Var 0) (QualV 0)) ((Var 1) (QualV 1)) ((Var 0) (QualV 0)))))
           ((SizeV 0))
           ((IGet_local 0 (QualV 0) (Var 0)) (ISet_local 3 ((Var 0) (QualV 0)))
            (IGet_local 2 (QualV 0) (Var 0)) (IGet_local 1 (QualV 1) (Var 1))
            (IGet_local 3 (QualV 0) (Var 0)))))
         () ()))) |}]
  ;;
end

module Struct_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ] ) )
      , []
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)))))
           ()
           ((IVal (Num (Int U I32) (Second 0))) (IVal (Num (Int U I32) (Second 1)))
            (IVal (Num (Int U I64) (First 3))))))
         () ()))) |}]
  ;;

  let struct_malloc_get : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ] ) )
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IStructMalloc ([ SizeC 64 ], QualC Unr)
        ; IMemUnpack
            ( ([], [ Num (Int (U, I64)), QualC Unr ])
            , []
            , [ IStructGet 0
              ; ISet_local 0
              ; IDrop
              ; IGet_local (0, QualC Unr)
              ; IVal Unit
              ; ISet_local 0
              ] )
        ] )
  ;;

  let module_ = [ struct_malloc_get ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)))))
           ((SizeC 64))
           ((IVal (Num (Int U I32) (Second 0))) (IVal (Num (Int U I32) (Second 1)))
            (IVal (Num (Int U I64) (First 3)))
            (IStructMalloc ((SizeC 64)) (QualC Unr)
             (((Num (Int U I64)) (QualC Unr))))
            (IMemUnpack (() (((Num (Int U I64)) (QualC Unr)))) ()
             ((IStructGet 0 (((Num (Int U I64)) (QualC Unr))))
              (ISet_local 0 ((Num (Int U I64)) (QualC Unr))) IDrop
              (IGet_local 0 (QualC Unr) (Num (Int U I64))) (IVal Unit)
              (ISet_local 0 (Unit (QualC Unr))))))))
         () ()))) |}]
  ;;

  let struct_multi : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ] ) )
      , [ SizeC 32; SizeC 32; SizeC 64 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IStructMalloc ([ SizeC 32; SizeC 32; SizeC 64 ], QualC Unr)
        ; IMemUnpack
            ( ( []
              , [ Num (Int (U, I32)), QualC Unr
                ; Num (Int (U, I32)), QualC Unr
                ; Num (Int (U, I64)), QualC Unr
                ] )
            , []
            , [ IStructGet 0
              ; ISet_local 0
              ; IStructGet 1
              ; ISet_local 1
              ; IStructGet 2
              ; ISet_local 2
              ; IDrop
              ; IGet_local (0, QualC Unr)
              ; IGet_local (1, QualC Unr)
              ; IGet_local (2, QualC Unr)
              ; IVal Unit
              ; ISet_local 0
              ; IVal Unit
              ; ISet_local 1
              ; IVal Unit
              ; ISet_local 2
              ] )
        ] )
  ;;

  let module_ = [ struct_multi ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)))))
           ((SizeC 32) (SizeC 32) (SizeC 64))
           ((IVal (Num (Int U I32) (Second 0))) (IVal (Num (Int U I32) (Second 1)))
            (IVal (Num (Int U I64) (First 3)))
            (IStructMalloc ((SizeC 32) (SizeC 32) (SizeC 64)) (QualC Unr)
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr))))
            (IMemUnpack
             (()
              (((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
               ((Num (Int U I32)) (QualC Unr))))
             ()
             ((IStructGet 0
               (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                ((Num (Int U I64)) (QualC Unr))))
              (ISet_local 0 ((Num (Int U I32)) (QualC Unr)))
              (IStructGet 1
               (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                ((Num (Int U I64)) (QualC Unr))))
              (ISet_local 1 ((Num (Int U I32)) (QualC Unr)))
              (IStructGet 2
               (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
                ((Num (Int U I64)) (QualC Unr))))
              (ISet_local 2 ((Num (Int U I64)) (QualC Unr))) IDrop
              (IGet_local 0 (QualC Unr) (Num (Int U I32)))
              (IGet_local 1 (QualC Unr) (Num (Int U I32)))
              (IGet_local 2 (QualC Unr) (Num (Int U I64))) (IVal Unit)
              (ISet_local 0 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 1 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 2 (Unit (QualC Unr))))))))
         () ()))) |}]
  ;;

  let struct_group : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ] ) )
      , [ SizeC 64; SizeC 64 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IGroup (2, QualC Unr)
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IStructMalloc ([ SizeC 64; SizeC 64 ], QualC Unr)
        ; IMemUnpack
            ( ( []
              , [ Num (Int (U, I32)), QualC Unr
                ; Num (Int (U, I32)), QualC Unr
                ; Num (Int (U, I64)), QualC Unr
                ] )
            , []
            , [ IStructGet 0
              ; ISet_local 0
              ; IStructGet 1
              ; ISet_local 1
              ; IDrop
              ; IGet_local (0, QualC Unr)
              ; IUngroup
              ; IGet_local (1, QualC Unr)
              ; IVal Unit
              ; ISet_local 0
              ; IVal Unit
              ; ISet_local 1
              ] )
        ] )
  ;;

  let module_ = [ struct_group ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)))))
           ((SizeC 64) (SizeC 64))
           ((IVal (Num (Int U I32) (Second 0))) (IVal (Num (Int U I32) (Second 1)))
            (IGroup 2 (QualC Unr)) (IVal (Num (Int U I64) (First 3)))
            (IStructMalloc ((SizeC 64) (SizeC 64)) (QualC Unr)
             (((Prod
                (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))))
               (QualC Unr))
              ((Num (Int U I64)) (QualC Unr))))
            (IMemUnpack
             (()
              (((Num (Int U I64)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
               ((Num (Int U I32)) (QualC Unr))))
             ()
             ((IStructGet 0
               (((Prod
                  (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))))
                 (QualC Unr))
                ((Num (Int U I64)) (QualC Unr))))
              (ISet_local 0
               ((Prod
                 (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))))
                (QualC Unr)))
              (IStructGet 1
               (((Prod
                  (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))))
                 (QualC Unr))
                ((Num (Int U I64)) (QualC Unr))))
              (ISet_local 1 ((Num (Int U I64)) (QualC Unr))) IDrop
              (IGet_local 0 (QualC Unr)
               (Prod
                (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr)))))
              IUngroup (IGet_local 1 (QualC Unr) (Num (Int U I64))) (IVal Unit)
              (ISet_local 0 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 1 (Unit (QualC Unr))))))))
         () ()))) |}]
  ;;

  let struct_set_swap : Instruction.f =
    Fun
      ( []
      , ( []
        , ( []
          , [ Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I32)), QualC Unr
            ; Num (Int (U, I64)), QualC Unr
            ] ) )
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 100)))
        ; IStructMalloc ([ SizeC 64 ], QualC Lin)
        ; IMemUnpack
            ( ([], [])
            , [ 0, (Num (Int (U, I64)), QualC Unr) ]
            , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 1)))
              ; IStructSet 0
              ; IVal Unit
              ; IStructSwap 0
              ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 2)))
              ; INe (Ib (I64, Iadd))
              ; ISet_local 0
              ; IStructFree
              ] )
        ; IGet_local (0, QualC Unr)
        ] )
  ;;

  let module_ = [ struct_set_swap ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun ()
           (()
            (()
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int U I32)) (QualC Unr))
              ((Num (Int U I64)) (QualC Unr)))))
           ((SizeC 64))
           ((IVal (Num (Int U I32) (Second 0))) (IVal (Num (Int U I32) (Second 1)))
            (IVal (Num (Int U I64) (First 100)))
            (IStructMalloc ((SizeC 64)) (QualC Lin)
             (((Num (Int U I64)) (QualC Unr))))
            (IMemUnpack (() ()) ((0 ((Num (Int U I64)) (QualC Unr))))
             ((IVal (Num (Int U I64) (First 1)))
              (IStructSet 0 (((Num (Int U I64)) (QualC Unr)))) (IVal Unit)
              (IStructSwap 0 (((Num (Int U I64)) (QualC Unr))))
              (IVal (Num (Int U I64) (First 2))) (INe (Ib I64 Iadd))
              (ISet_local 0 ((Num (Int U I64)) (QualC Unr)))
              (IStructFree ((Unit (QualC Unr))))))
            (IGet_local 0 (QualC Unr) (Num (Int U I64))))))
         () ()))) |}]
  ;;
end

module Array_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 12))) ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
           ((IVal (Num (Int U I64) (First 12))))))
         () ()))) |}]
  ;;

  let array_simple : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 12)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
        ; IArrayMalloc (QualC Lin)
        ; IMemUnpack
            ( ([], [])
            , [ 0, (Num (Int (U, I64)), QualC Unr) ]
            , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
              ; IArrayGet
              ; ISet_local 0
              ; IArrayFree
              ] )
        ; IGet_local (0, QualC Unr)
        ] )
  ;;

  let module_ = [ array_simple ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ((SizeC 64))
           ((IVal (Num (Int U I64) (First 12))) (IVal (Num (Int U I32) (Second 1)))
            (IArrayMalloc (QualC Lin) ((Num (Int U I64)) (QualC Unr)))
            (IMemUnpack (() ()) ((0 ((Num (Int U I64)) (QualC Unr))))
             ((IVal (Num (Int U I32) (Second 0)))
              (IArrayGet ((Num (Int U I64)) (QualC Unr)))
              (ISet_local 0 ((Num (Int U I64)) (QualC Unr)))
              (IArrayFree ((Num (Int U I64)) (QualC Unr)))))
            (IGet_local 0 (QualC Unr) (Num (Int U I64))))))
         () ()))) |}]
  ;;

  let array_multi : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , [ SizeC 64; SizeC 64 ]
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 0)))
        ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 2)))
        ; IArrayMalloc (QualC Lin)
        ; IMemUnpack
            ( ([], [])
            , [ 0, (Num (Int (U, I64)), QualC Unr); 1, (Num (Int (U, I64)), QualC Unr) ]
            , [ IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
              ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 4)))
              ; IArraySet
              ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
              ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 8)))
              ; IArraySet
              ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 0)))
              ; IArrayGet
              ; ISet_local 0
              ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 1)))
              ; IArrayGet
              ; ISet_local 1
              ; IArrayFree
              ] )
        ; IGet_local (0, QualC Unr)
        ; IGet_local (1, QualC Unr)
        ; INe (Ib (I64, Iadd))
        ] )
  ;;

  let module_ = [ array_multi ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr)))))
           ((SizeC 64) (SizeC 64))
           ((IVal (Num (Int U I64) (First 0))) (IVal (Num (Int U I32) (Second 2)))
            (IArrayMalloc (QualC Lin) ((Num (Int U I64)) (QualC Unr)))
            (IMemUnpack (() ())
             ((0 ((Num (Int U I64)) (QualC Unr)))
              (1 ((Num (Int U I64)) (QualC Unr))))
             ((IVal (Num (Int U I32) (Second 0)))
              (IVal (Num (Int U I64) (First 4)))
              (IArraySet ((Num (Int U I64)) (QualC Unr)))
              (IVal (Num (Int U I32) (Second 1)))
              (IVal (Num (Int U I64) (First 8)))
              (IArraySet ((Num (Int U I64)) (QualC Unr)))
              (IVal (Num (Int U I32) (Second 0)))
              (IArrayGet ((Num (Int U I64)) (QualC Unr)))
              (ISet_local 0 ((Num (Int U I64)) (QualC Unr)))
              (IVal (Num (Int U I32) (Second 1)))
              (IArrayGet ((Num (Int U I64)) (QualC Unr)))
              (ISet_local 1 ((Num (Int U I64)) (QualC Unr)))
              (IArrayFree ((Num (Int U I64)) (QualC Unr)))))
            (IGet_local 0 (QualC Unr) (Num (Int U I64)))
            (IGet_local 1 (QualC Unr) (Num (Int U I64))) (INe (Ib I64 Iadd)))))
         () ()))) |}]
  ;;
end

module Variant_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5))) ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
           ((IVal (Num (Int U I64) (First 5))))))
         () ()))) |}]
  ;;

  let variant_simple : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; IVariantMalloc
            ( 1
            , [ Unit, QualC Unr; Num (Int (U, I64)), QualC Unr; Unit, QualC Unr ]
            , QualC Lin )
        ; IMemUnpack
            ( ([], [ Num (Int (U, I64)), QualC Unr ])
            , []
            , [ IVariantCase
                  ( QualC Lin
                  , ([], [ Num (Int (U, I64)), QualC Unr ])
                  , []
                  , [ [ IUnreachable ]; []; [ IUnreachable ] ] )
              ] )
        ] )
  ;;

  let module_ = [ variant_simple ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
           ((IVal (Num (Int U I64) (First 5)))
            (IVariantMalloc 1
             ((Unit (QualC Unr)) ((Num (Int U I64)) (QualC Unr))
              (Unit (QualC Unr)))
             (QualC Lin))
            (IMemUnpack (() (((Num (Int U I64)) (QualC Unr)))) ()
             ((IVariantCase (QualC Lin)
               ((Unit (QualC Unr)) ((Num (Int U I64)) (QualC Unr))
                (Unit (QualC Unr)))
               (() (((Num (Int U I64)) (QualC Unr)))) ()
               ((IUnreachable) () (IUnreachable))))))))
         () ()))) |}]
  ;;

  let variant_with_groups : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 3)))
        ; IVal (Num (Int (U, I64), First (Int64.of_int_exn 2)))
        ; IGroup (2, QualC Unr)
        ; IVariantMalloc
            ( 2
            , [ Unit, QualC Unr
              ; Num (Int (U, I64)), QualC Unr
              ; ( Prod [ Num (Int (U, I64)), QualC Unr; Num (Int (U, I64)), QualC Unr ]
                , QualC Unr )
              ]
            , QualC Unr )
        ; IMemUnpack
            ( ([], [])
            , [ 0, (Num (Int (U, I64)), QualC Unr) ]
            , [ IVariantCase
                  ( QualC Unr
                  , ([], [ Num (Int (U, I64)), QualC Unr ])
                  , []
                  , [ [ IDrop; IVal (Num (Int (U, I64), First (Int64.of_int_exn 2))) ]
                    ; []
                    ; [ IUngroup; INe (Ib (I64, Iadd)) ]
                    ] )
              ; ISet_local 0
              ] )
        ; IGet_local (0, QualC Unr)
        ] )
  ;;

  let module_ = [ variant_with_groups ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ((SizeC 64))
           ((IVal (Num (Int U I64) (First 3))) (IVal (Num (Int U I64) (First 2)))
            (IGroup 2 (QualC Unr))
            (IVariantMalloc 2
             ((Unit (QualC Unr)) ((Num (Int U I64)) (QualC Unr))
              ((Prod
                (((Num (Int U I64)) (QualC Unr)) ((Num (Int U I64)) (QualC Unr))))
               (QualC Unr)))
             (QualC Unr))
            (IMemUnpack (() ()) ((0 ((Num (Int U I64)) (QualC Unr))))
             ((IVariantCase (QualC Unr)
               ((Unit (QualC Unr)) ((Num (Int U I64)) (QualC Unr))
                ((Prod
                  (((Num (Int U I64)) (QualC Unr)) ((Num (Int U I64)) (QualC Unr))))
                 (QualC Unr)))
               (() (((Num (Int U I64)) (QualC Unr)))) ()
               ((IDrop (IVal (Num (Int U I64) (First 2)))) ()
                (IUngroup (INe (Ib I64 Iadd)))))
              (ISet_local 0 ((Num (Int U I64)) (QualC Unr)))))
            (IGet_local 0 (QualC Unr) (Num (Int U I64))))))
         () ()))) |}]
  ;;
end

module Exist_examples = struct
  let test_endstate : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5))) ] )
  ;;

  let module_ = [ test_endstate ], [], []

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
           ((IVal (Num (Int U I64) (First 5))))))
         () ()))) |}]
  ;;

  let id : Instruction.f =
    Fun
      ( []
      , ([], ([ Num (Int (U, I64)), QualC Unr ], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IGet_local (0, QualC Unr) ] )
  ;;

  let id_abstract : Instruction.f =
    Fun
      ( []
      , ( [ Size ([], []); Type (QualC Unr, SizeC 64, Heapable) ]
        , ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]) )
      , []
      , [ IGet_local (0, QualC Unr) ] )
  ;;

  let exist_simple : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , []
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; ICoderefI 0
        ; IGroup (2, QualC Unr)
        ; IExistPack
            ( Num (Int (U, I64))
            , Ex
                ( QualC Unr
                , SizeC 64
                , ( Prod
                      [ Var 0, QualC Unr
                      ; ( Coderef
                            ([], ([ Var 0, QualC Unr ], [ Num (Int (U, I64)), QualC Unr ]))
                        , QualC Unr )
                      ]
                  , QualC Unr ) )
            , QualC Unr )
        ; IMemUnpack
            ( ([], [ Num (Int (U, I64)), QualC Unr ])
            , []
            , [ IExistUnpack
                  ( QualC Unr
                  , ([], [ Num (Int (U, I64)), QualC Unr ])
                  , []
                  , [ IUngroup; ICall_indirect ] )
              ] )
        ] )
  ;;

  let module_ = [ exist_simple; id ], [], [ 1 ]

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ()
           ((IVal (Num (Int U I64) (First 5))) (ICoderefI 0) (IGroup 2 (QualC Unr))
            (IExistPack (Num (Int U I64))
             (Ex (QualC Unr) (SizeC 64)
              ((Prod
                (((Var 0) (QualC Unr))
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                  (QualC Unr))))
               (QualC Unr)))
             (QualC Unr))
            (IMemUnpack (() (((Num (Int U I64)) (QualC Unr)))) ()
             ((IExistUnpack (QualC Unr) (() (((Num (Int U I64)) (QualC Unr)))) ()
               (IUngroup
                (ICall_indirect
                 ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
               ((Prod
                 (((Var 0) (QualC Unr))
                  ((Coderef
                    (()
                     ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                   (QualC Unr))))
                (QualC Unr)))))))
          (Fun ()
           (()
            ((((Num (Int U I64)) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Num (Int U I64))))))
         () (1)))) |}]
  ;;

  let exist_more_complex_a : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; ICoderefI 0
        ; ICoderefI 1
        ; IInst [ SizeI (SizeC 64); PretypeI (Num (Int (U, I64))) ]
        ; IGroup (3, QualC Unr)
        ; IExistPack
            ( Num (Int (U, I64))
            , Ex
                ( QualC Unr
                , SizeC 64
                , ( Prod
                      [ Var 0, QualC Unr
                      ; ( Coderef ([], ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]))
                        , QualC Unr )
                      ; ( Coderef
                            ([], ([ Var 0, QualC Unr ], [ Num (Int (U, I64)), QualC Unr ]))
                        , QualC Unr )
                      ]
                  , QualC Unr ) )
            , QualC Unr )
        ; IMemUnpack
            ( ([], [ Num (Int (U, I64)), QualC Unr ])
            , []
            , [ IExistUnpack
                  ( QualC Unr
                  , ([], [ Num (Int (U, I64)), QualC Unr ])
                  , []
                  , [ IUngroup
                    ; ISet_local 0
                    ; ICall_indirect
                    ; IGet_local (0, QualC Unr)
                    ; ICall_indirect
                    ; IVal Unit
                    ; ISet_local 0
                    ] )
              ] )
        ] )
  ;;

  let module_ = [ exist_more_complex_a; id; id_abstract ], [], [ 1; 2 ]

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ((SizeC 64))
           ((IVal (Num (Int U I64) (First 5))) (ICoderefI 0) (ICoderefI 1)
            (IInst ((SizeI (SizeC 64)) (PretypeI (Num (Int U I64)))))
            (IGroup 3 (QualC Unr))
            (IExistPack (Num (Int U I64))
             (Ex (QualC Unr) (SizeC 64)
              ((Prod
                (((Var 0) (QualC Unr))
                 ((Coderef (() ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr))))))
                  (QualC Unr))
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                  (QualC Unr))))
               (QualC Unr)))
             (QualC Unr))
            (IMemUnpack (() (((Num (Int U I64)) (QualC Unr)))) ()
             ((IExistUnpack (QualC Unr) (() (((Num (Int U I64)) (QualC Unr)))) ()
               (IUngroup
                (ISet_local 0
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                  (QualC Unr)))
                (ICall_indirect ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
                (IGet_local 0 (QualC Unr)
                 (Coderef
                  (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))))
                (ICall_indirect
                 ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))
                (IVal Unit) (ISet_local 0 (Unit (QualC Unr))))
               ((Prod
                 (((Var 0) (QualC Unr))
                  ((Coderef (() ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr))))))
                   (QualC Unr))
                  ((Coderef
                    (()
                     ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                   (QualC Unr))))
                (QualC Unr)))))))
          (Fun ()
           (()
            ((((Num (Int U I64)) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Num (Int U I64)))))
          (Fun ()
           (((Size () ()) (Type (QualC Unr) (SizeC 64) Heapable))
            ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Var 0)))))
         () (1 2)))) |}]
  ;;

  let exist_more_complex_b : Instruction.f =
    Fun
      ( []
      , ([], ([], [ Num (Int (U, I64)), QualC Unr ]))
      , [ SizeC 64 ]
      , [ IVal (Num (Int (U, I64), First (Int64.of_int_exn 5)))
        ; ICoderefI 1
        ; IInst [ SizeI (SizeC 64); PretypeI (Num (Int (U, I64))) ]
        ; ICoderefI 0
        ; IGroup (3, QualC Unr)
        ; IExistPack
            ( Num (Int (U, I64))
            , Ex
                ( QualC Unr
                , SizeC 64
                , ( Prod
                      [ Var 0, QualC Unr
                      ; ( Coderef ([], ([ Var 0, QualC Unr ], [ Var 0, QualC Unr ]))
                        , QualC Unr )
                      ; ( Coderef
                            ([], ([ Var 0, QualC Unr ], [ Num (Int (U, I64)), QualC Unr ]))
                        , QualC Unr )
                      ]
                  , QualC Unr ) )
            , QualC Unr )
        ; IMemUnpack
            ( ([], [ Num (Int (U, I64)), QualC Unr ])
            , []
            , [ IExistUnpack
                  ( QualC Unr
                  , ([], [ Num (Int (U, I64)), QualC Unr ])
                  , []
                  , [ IUngroup
                    ; ISet_local 0
                    ; ICall_indirect
                    ; IGet_local (0, QualC Unr)
                    ; ICall_indirect
                    ; IVal Unit
                    ; ISet_local 0
                    ] )
              ] )
        ] )
  ;;

  let module_ = [ exist_more_complex_b; id; id_abstract ], [], [ 1; 2 ]

  let%expect_test _ =
    test_annotation [ "module", module_ ];
    [%expect
      {|
      ((module
        (((Fun () (() (() (((Num (Int U I64)) (QualC Unr))))) ((SizeC 64))
           ((IVal (Num (Int U I64) (First 5))) (ICoderefI 1)
            (IInst ((SizeI (SizeC 64)) (PretypeI (Num (Int U I64))))) (ICoderefI 0)
            (IGroup 3 (QualC Unr))
            (IExistPack (Num (Int U I64))
             (Ex (QualC Unr) (SizeC 64)
              ((Prod
                (((Var 0) (QualC Unr))
                 ((Coderef (() ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr))))))
                  (QualC Unr))
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                  (QualC Unr))))
               (QualC Unr)))
             (QualC Unr))
            (IMemUnpack (() (((Num (Int U I64)) (QualC Unr)))) ()
             ((IExistUnpack (QualC Unr) (() (((Num (Int U I64)) (QualC Unr)))) ()
               (IUngroup
                (ISet_local 0
                 ((Coderef
                   (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                  (QualC Unr)))
                (ICall_indirect ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
                (IGet_local 0 (QualC Unr)
                 (Coderef
                  (() ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))))
                (ICall_indirect
                 ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))
                (IVal Unit) (ISet_local 0 (Unit (QualC Unr))))
               ((Prod
                 (((Var 0) (QualC Unr))
                  ((Coderef (() ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr))))))
                   (QualC Unr))
                  ((Coderef
                    (()
                     ((((Var 0) (QualC Unr))) (((Num (Int U I64)) (QualC Unr))))))
                   (QualC Unr))))
                (QualC Unr)))))))
          (Fun ()
           (()
            ((((Num (Int U I64)) (QualC Unr))) (((Num (Int U I64)) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Num (Int U I64)))))
          (Fun ()
           (((Size () ()) (Type (QualC Unr) (SizeC 64) Heapable))
            ((((Var 0) (QualC Unr))) (((Var 0) (QualC Unr)))))
           () ((IGet_local 0 (QualC Unr) (Var 0)))))
         () (1 2)))) |}]
  ;;
end

module L3_misc = struct
  let%expect_test _ =
    let module_ =
      {|
    (((Fun ()
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
     () (0)) |}
    in
    test_annotation [ "l3", module_ |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp ];
    [%expect
      {|
      ((l3
        (((Fun ()
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
            (IStructMalloc ((SizeC 64)) (QualC Lin)
             (((Num (Int S I32)) (QualC Unr))))
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
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
             ((ISet_local 0
               ((Prod
                 (((Cap W (LocV 0)
                    (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 64)))))
                   (QualC Lin))
                  ((Ptr (LocV 0)) (QualC Unr))))
                (QualC Lin)))
              (IGet_local 0 (QualC Lin)
               (Prod
                (((Cap W (LocV 0)
                   (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 64)))))
                  (QualC Lin))
                 ((Ptr (LocV 0)) (QualC Unr)))))
              IUngroup (ISet_local 2 ((Ptr (LocV 0)) (QualC Unr)))
              (ISet_local 1
               ((Cap W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 64)))))
                (QualC Lin)))
              (IGet_local 1 (QualC Lin)
               (Cap W (LocV 0)
                (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 64))))))
              (IVal (Num (Int S I32) (Second 69)))
              (IVal (Num (Int S I32) (Second 420))) (IGroup 2 (QualC Lin))
              (IGroup 2 (QualC Lin)) IUngroup
              (ISet_local 3
               ((Prod
                 (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))))
                (QualC Lin)))
              (IGet_local 2 (QualC Unr) (Ptr (LocV 0))) IRefJoin
              (IGet_local 3 (QualC Lin)
               (Prod
                (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr)))))
              (IVal Unit) (ISet_local 3 (Unit (QualC Unr)))
              (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
              (ISet_local 4 ((Num (Int S I32)) (QualC Unr))) IRefSplit IDrop
              (IGet_local 4 (QualC Unr) (Num (Int S I32))) (IVal Unit)
              (ISet_local 4 (Unit (QualC Unr))) (IGroup 2 (QualC Lin)) IUngroup
              (ISet_local 6 ((Num (Int S I32)) (QualC Unr)))
              (ISet_local 5
               ((Cap W (LocV 0)
                 (Struct
                  ((((Prod
                      (((Num (Int S I32)) (QualC Unr))
                       ((Num (Int S I32)) (QualC Unr))))
                     (QualC Lin))
                    (SizeC 64)))))
                (QualC Lin)))
              (IGet_local 5 (QualC Lin)
               (Cap W (LocV 0)
                (Struct
                 ((((Prod
                     (((Num (Int S I32)) (QualC Unr))
                      ((Num (Int S I32)) (QualC Unr))))
                    (QualC Lin))
                   (SizeC 64))))))
              (IGet_local 2 (QualC Unr) (Ptr (LocV 0))) (IGroup 2 (QualC Lin))
              (IMemPack (LocV 1)) (IGet_local 6 (QualC Unr) (Num (Int S I32)))
              (IGroup 2 (QualC Lin)) (IVal Unit) (ISet_local 6 (Unit (QualC Unr)))
              (IVal Unit) (ISet_local 5 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 2 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 1 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 0 (Unit (QualC Unr))))))))
         () (0)))) |}]
  ;;

  let%expect_test _ =
    let module_ =
      {|
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
      (Fun () (() (() ((Unit (QualC Lin))))) ()
       ((IVal Unit) (IQualify (QualC Lin)))))
     () (0 1 2)) |}
    in
    test_annotation [ "l3", module_ |> Sexp.of_string |> Rich_wasm.Module.t_of_sexp ];
    [%expect {|
      ((l3
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
           ((IGet_local 0 (QualC Lin)
             (Prod
              (((Cap W (LocV 0)
                 (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
                (QualC Lin))
               ((Ptr (LocV 0)) (QualC Unr)))))
            IUngroup (ISet_local 3 ((Ptr (LocV 0)) (QualC Unr)))
            (ISet_local 2
             ((Cap W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (IGet_local 2 (QualC Lin)
             (Cap W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32))))))
            (IGet_local 1 (QualC Unr) (Num (Int S I32))) (IGroup 2 (QualC Lin))
            IUngroup (ISet_local 4 ((Num (Int S I32)) (QualC Unr)))
            (IGet_local 3 (QualC Unr) (Ptr (LocV 0))) IRefJoin
            (IGet_local 4 (QualC Unr) (Num (Int S I32))) (IVal Unit)
            (ISet_local 4 (Unit (QualC Unr)))
            (IStructSwap 0 (((Num (Int S I32)) (QualC Unr))))
            (ISet_local 5 ((Num (Int S I32)) (QualC Unr))) IRefSplit IDrop
            (IGet_local 5 (QualC Unr) (Num (Int S I32))) (IVal Unit)
            (ISet_local 5 (Unit (QualC Unr))) (IGroup 2 (QualC Lin)) IUngroup
            (ISet_local 7 ((Num (Int S I32)) (QualC Unr)))
            (ISet_local 6
             ((Cap W (LocV 0)
               (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32)))))
              (QualC Lin)))
            (IGet_local 6 (QualC Lin)
             (Cap W (LocV 0)
              (Struct ((((Num (Int S I32)) (QualC Unr)) (SizeC 32))))))
            (IGet_local 3 (QualC Unr) (Ptr (LocV 0))) (IGroup 2 (QualC Lin))
            (IGet_local 7 (QualC Unr) (Num (Int S I32))) (IGroup 2 (QualC Lin))
            (IVal Unit) (ISet_local 7 (Unit (QualC Unr))) (IVal Unit)
            (ISet_local 6 (Unit (QualC Unr))) (IVal Unit)
            (ISet_local 3 (Unit (QualC Unr))) (IVal Unit)
            (ISet_local 2 (Unit (QualC Unr)))))
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
           ((SizeC 64) (SizeC 0) (SizeC 64) (SizeC 0) (SizeC 64) (SizeC 0)
            (SizeC 64) (SizeC 32) (SizeC 32) (SizeC 32) (SizeC 32) (SizeC 64)
            (SizeC 0) (SizeC 0))
           ((IGet_local 0 (QualC Lin)
             (ExLoc
              ((Ref W (LocV 0)
                (Struct
                 ((((Prod
                     (((Num (Int S I32)) (QualC Unr))
                      ((Num (Int S I32)) (QualC Unr))))
                    (QualC Lin))
                   (SizeC 64)))))
               (QualC Lin))))
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
             () (IRefSplit (IGroup 2 (QualC Lin)) (IMemPack (LocV 1))))
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
              (7 (Unit (QualC Unr))) (12 (Unit (QualC Unr)))
              (11 (Unit (QualC Unr))) (15 (Unit (QualC Unr))))
             ((ISet_local 2
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
              (IGet_local 2 (QualC Lin)
               (Prod
                (((Cap W (LocV 0)
                   (Struct
                    ((((Prod
                        (((Num (Int S I32)) (QualC Unr))
                         ((Num (Int S I32)) (QualC Unr))))
                       (QualC Lin))
                      (SizeC 64)))))
                  (QualC Lin))
                 ((Ptr (LocV 0)) (QualC Unr)))))
              IUngroup (ISet_local 4 ((Ptr (LocV 0)) (QualC Unr)))
              (ISet_local 3
               ((Cap W (LocV 0)
                 (Struct
                  ((((Prod
                      (((Num (Int S I32)) (QualC Unr))
                       ((Num (Int S I32)) (QualC Unr))))
                     (QualC Lin))
                    (SizeC 64)))))
                (QualC Lin)))
              (IGet_local 3 (QualC Lin)
               (Cap W (LocV 0)
                (Struct
                 ((((Prod
                     (((Num (Int S I32)) (QualC Unr))
                      ((Num (Int S I32)) (QualC Unr))))
                    (QualC Lin))
                   (SizeC 64))))))
              (IVal Unit) (IGroup 2 (QualC Lin)) IUngroup
              (ISet_local 5 (Unit (QualC Unr)))
              (IGet_local 4 (QualC Unr) (Ptr (LocV 0))) IRefJoin
              (IGet_local 5 (QualC Unr) Unit) (IVal Unit)
              (ISet_local 5 (Unit (QualC Unr)))
              (IStructSwap 0
               (((Prod
                  (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))))
                 (QualC Lin))))
              (ISet_local 6
               ((Prod
                 (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))))
                (QualC Lin)))
              IRefSplit IDrop
              (IGet_local 6 (QualC Lin)
               (Prod
                (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr)))))
              (IVal Unit) (ISet_local 6 (Unit (QualC Unr))) (IGroup 2 (QualC Lin))
              IUngroup
              (ISet_local 8
               ((Prod
                 (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))))
                (QualC Lin)))
              (ISet_local 7
               ((Cap W (LocV 0) (Struct (((Unit (QualC Unr)) (SizeC 64)))))
                (QualC Lin)))
              (IGet_local 8 (QualC Lin)
               (Prod
                (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr)))))
              IUngroup (ISet_local 10 ((Num (Int S I32)) (QualC Unr)))
              (ISet_local 9 ((Num (Int S I32)) (QualC Unr)))
              (IGet_local 10 (QualC Unr) (Num (Int S I32))) (IQualify (QualC Lin))
              (ISet_local 11 ((Num (Int S I32)) (QualC Lin)))
              (IGet_local 1 (QualC Unr) (Num (Int S I32))) (IQualify (QualC Lin))
              (ISet_local 12 ((Num (Int S I32)) (QualC Lin)))
              (IGet_local 7 (QualC Lin)
               (Cap W (LocV 0) (Struct (((Unit (QualC Unr)) (SizeC 64))))))
              (IGet_local 9 (QualC Unr) (Num (Int S I32)))
              (IGet_local 12 (QualC Lin) (Num (Int S I32)))
              (IGet_local 11 (QualC Lin) (Num (Int S I32))) (INe (Ib I32 Iadd))
              (IGroup 2 (QualC Lin)) (IGroup 2 (QualC Lin)) IUngroup
              (ISet_local 13
               ((Prod
                 (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr))))
                (QualC Lin)))
              (IGet_local 4 (QualC Unr) (Ptr (LocV 0))) IRefJoin
              (IGet_local 13 (QualC Lin)
               (Prod
                (((Num (Int S I32)) (QualC Unr)) ((Num (Int S I32)) (QualC Unr)))))
              (IVal Unit) (ISet_local 13 (Unit (QualC Unr)))
              (IStructSwap 0 ((Unit (QualC Unr))))
              (ISet_local 14 (Unit (QualC Unr))) IRefSplit IDrop
              (IGet_local 14 (QualC Unr) Unit) (IVal Unit)
              (ISet_local 14 (Unit (QualC Unr))) (IGroup 2 (QualC Lin)) IUngroup
              IDrop
              (ISet_local 15
               ((Cap W (LocV 0)
                 (Struct
                  ((((Prod
                      (((Num (Int S I32)) (QualC Unr))
                       ((Num (Int S I32)) (QualC Unr))))
                     (QualC Lin))
                    (SizeC 64)))))
                (QualC Lin)))
              (IGet_local 15 (QualC Lin)
               (Cap W (LocV 0)
                (Struct
                 ((((Prod
                     (((Num (Int S I32)) (QualC Unr))
                      ((Num (Int S I32)) (QualC Unr))))
                    (QualC Lin))
                   (SizeC 64))))))
              (IGet_local 4 (QualC Unr) (Ptr (LocV 0))) (IGroup 2 (QualC Lin))
              (IMemPack (LocV 1)) (IVal Unit) (ISet_local 15 (Unit (QualC Unr)))
              (IVal Unit) (ISet_local 12 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 11 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 10 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 9 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 8 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 7 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 4 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 3 (Unit (QualC Unr))) (IVal Unit)
              (ISet_local 2 (Unit (QualC Unr)))))))
          (Fun () (() (() ((Unit (QualC Lin))))) ()
           ((IVal Unit) (IQualify (QualC Lin)))))
         () (0 1 2)))) |}]
  ;;
end
