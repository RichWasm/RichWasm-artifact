open Core
module Cap = Rich_wasm.Cap
module Sign = Rich_wasm.Sign
module Heapable_const = Rich_wasm.Heapable_const
module Qual_const = Rich_wasm.Qual_const
module Loc = Rich_wasm.Loc
module Qual = Rich_wasm.Qual
module Size = Rich_wasm.Size
module IntType = Rich_wasm.IntType
module FloatType = Rich_wasm.FloatType
module NumType = Rich_wasm.NumType
module KindVar = Rich_wasm.KindVar
module Type = Rich_wasm.Type
module Mut = Rich_wasm.Mut
module Table = Rich_wasm.Table
module LocalEffect = Rich_wasm.LocalEffect
module Index = Rich_wasm.Index
module Value = Rich_wasm.Value
module IUnOp = Rich_wasm.IUnOp
module IBinOp = Rich_wasm.IBinOp
module FUnOp = Rich_wasm.FUnOp
module FBinOp = Rich_wasm.FBinOp
module ITestOp = Rich_wasm.ITestOp
module IRelOp = Rich_wasm.IRelOp
module FRelOp = Rich_wasm.FRelOp
module CvtOp = Rich_wasm.CvtOp
module NumInstr = Rich_wasm.NumInstr
module Ex = Rich_wasm.Ex
module Im = Rich_wasm.Im

module Instruction = struct
  type t =
    | IVal of Value.t
    | INe of NumInstr.t
    | IUnreachable
    | INop
    | IDrop of Type.pt (* DIFFERENT *)
    | ISelect
    | IBlock of Type.at * LocalEffect.t * t list
    | ILoop of Type.at * t list
    | IITE of Type.at * LocalEffect.t * t list * t list
    | IBr of int
    | IBr_if of int
    | IBr_table of int list * int
    | IRet
    | IGet_local of int * Qual.t * Type.pt (* DIFFERENT *)
    | ISet_local of int * Type.t (* DIFFERENT *)
    | ITee_local of int * Type.t (* DIFFERENT *)
    | IGet_global of int
    | ISet_global of int
    | ICoderefI of int
    | IInst of Index.t list
    | ICall_indirect of Type.at (* DIFFERENT *)
    | ICall of int * Index.t list
    | IRecFold of Type.pt
    | IRecUnfold
    | IGroup of int * Qual.t
    | IUngroup
    | ICapSplit
    | ICapJoin
    | IRefDemote
    | IMemPack of Loc.t
    | IMemUnpack of Type.at * LocalEffect.t * t list * Type.t (* DIFFERENT *)
    | IStructMalloc of Size.t list * Qual.t * Type.t list (* DIFFERENT *)
    | IStructFree of Type.t list (* DIFFERENT *)
    | IStructGet of int * Type.t list (* DIFFERENT *)
    | IStructSet of int * Type.t list * Type.pt (* DIFFERENT *)
    | IStructSwap of int * Type.t list * Type.pt (* DIFFERENT *)
    | IVariantMalloc of int * Type.t list * Qual.t
    | IVariantCase of
        Qual.t * Type.t list * Type.at * LocalEffect.t * t list list (* DIFFERENT *)
    | IArrayMalloc of Qual.t * Type.t (* DIFFERENT *)
    | IArrayGet of Type.t (* DIFFERENT *)
    | IArraySet of Type.t (* DIFFERENT *)
    | IArrayFree of Type.t (* DIFFERENT *)
    | IExistPack of Type.pt * Type.ht * Qual.t
    | IExistUnpack of Qual.t * Type.at * LocalEffect.t * t list * Type.t (* DIFFERENT *)
    | IRefSplit
    | IRefJoin
    | IQualify of Qual.t

  and f =
    | Fun of Ex.t list * Type.ft * Size.t list * t list
    | FunIm of Ex.t list * Type.ft * Im.t
  [@@deriving sexp, quickcheck]
end

module Glob = struct
  type t =
    | GlobMut of Type.pt * Instruction.t list
    | GlobEx of Ex.t list * Type.pt * Instruction.t list
    | GlobIm of Ex.t list * Type.pt * Im.t
  [@@deriving sexp, quickcheck]
end

module Module = struct
  type t = Instruction.f list * Glob.t list * Table.t [@@deriving sexp, quickcheck]
end

(*
   let%expect_test _ =
   let x =
   ( [ Instruction.Fun
          ( []
          , ([], ([], []))
          , [ SizeC 96 ]
          , [ IGet_global 0
            ; IUngroup (* stack = unit, coderef, E ref array (i32, i64) *)
            ; IMemUnpack
                ( ( []
                  , [ ( ExLoc
                          ( Ref
                              ( Cap.W
                              , LocV 0
                              , Array
                                  ( Prod
                                      [ Num (Int (U, I32)), QualC Unr
                                      ; Num (Int (S, I64)), QualC Unr
                                      ]
                                  , QualC Unr ) )
                          , QualC Unr )
                      , QualC Unr )
                    ] )
                , []
                , [ (* stack = ref array (i32, i64) *)
                    IVal (Num (Int (U, I32), Second (Int32.of_int_exn 3)))
                  ; IArrayGet (SizeC 96) (* stack = ref array (i32, i64), (i32, i64) *)
                  ; IUngroup
                  ; IVal (Num (Int (S, I64), First (Int64.of_int 1)))
                  ; INe (Ib (I64, Iadd))
                  ; IGroup (2, QualC Unr) (* stack = ref array (i32, i64), (i32, i64) *)
                  ; ISet_local
                      ( 0
                      , ( Prod
                            [ Num (Int (U, I32)), QualC Unr
                            ; Num (Int (S, I64)), QualC Unr
                            ]
                        , QualC Unr ) )
                  ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 3)))
                  ; IGet_local
                      ( 0
                      , QualC Unr
                      , Prod
                          [ Num (Int (U, I32)), QualC Unr; Num (Int (S, I64)), QualC Unr ]
                      )
                    (* stack = ref array (i32, i64), i32, (i32, i64) *)
                  ; IArraySet (SizeC 96)
                  ; IMemPack (LocV 0)
                  ] )
            ; IGroup (3, QualC Unr)
            ; ISet_global 0
            ] )
      ]
   , [ Glob.GlobMut
          ( Prod
              [ Unit, QualC Unr
              ; Coderef ([], ([], [])), QualC Unr
              ; ( ExLoc
                    ( Ref
                        ( Cap.W
                        , LocV 0
                        , Array
                            ( Prod
                                [ Num (Int (U, I32)), QualC Unr
                                ; Num (Int (S, I64)), QualC Unr
                                ]
                            , QualC Unr ) )
                    , QualC Unr )
                , QualC Unr )
              ]
          , [ IVal Unit
            ; ICoderefI 0
            ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 10)))
            ; IVal (Num (Int (S, I64), First (Int64.of_int 50)))
            ; IGroup (2, QualC Unr)
            ; IVal (Num (Int (U, I32), Second (Int32.of_int_exn 100)))
            ; IArrayMalloc (QualC Unr, SizeC 96)
            ; IGroup (3, QualC Unr)
            ] )
      ]
   , [] )
   in
   print_s [%sexp (x : Module.t)];
   [%expect
    {|
    (((Fun () (() (() ())) ((SizeC 96))
       ((IGet_global 0) IUngroup
        (IMemUnpack
         (()
          (((ExLoc
             ((Ref W (LocV 0)
               (Array
                ((Prod
                  (((Num (Int U I32)) (QualC Unr))
                   ((Num (Int S I64)) (QualC Unr))))
                 (QualC Unr))))
              (QualC Unr)))
            (QualC Unr))))
         ()
         ((IVal (Num (Int U I32) (Second 3))) (IArrayGet (SizeC 96)) IUngroup
          (IVal (Num (Int S I64) (First 1))) (INe (Ib I64 Iadd))
          (IGroup 2 (QualC Unr))
          (ISet_local 0
           ((Prod
             (((Num (Int U I32)) (QualC Unr)) ((Num (Int S I64)) (QualC Unr))))
            (QualC Unr)))
          (IVal (Num (Int U I32) (Second 3)))
          (IGet_local 0 (QualC Unr)
           (Prod
            (((Num (Int U I32)) (QualC Unr)) ((Num (Int S I64)) (QualC Unr)))))
          (IArraySet (SizeC 96)) (IMemPack (LocV 0))))
        (IGroup 3 (QualC Unr)) (ISet_global 0))))
     ((GlobMut
       (Prod
        ((Unit (QualC Unr)) ((Coderef (() (() ()))) (QualC Unr))
         ((ExLoc
           ((Ref W (LocV 0)
             (Array
              ((Prod
                (((Num (Int U I32)) (QualC Unr)) ((Num (Int S I64)) (QualC Unr))))
               (QualC Unr))))
            (QualC Unr)))
          (QualC Unr))))
       ((IVal Unit) (ICoderefI 0) (IVal (Num (Int U I32) (Second 10)))
        (IVal (Num (Int S I64) (First 50))) (IGroup 2 (QualC Unr))
        (IVal (Num (Int U I32) (Second 100)))
        (IArrayMalloc (QualC Unr) (SizeC 96)) (IGroup 3 (QualC Unr)))))
     ()) |}]
   ;;
*)
