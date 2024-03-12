open! Core

module Cap = struct
  type t =
    | R
    | W
  [@@deriving sexp, equal, quickcheck, compare]
end

module Sign = struct
  type t =
    | S
    | U
  [@@deriving sexp, equal, quickcheck, compare]
end

module Heapable_const = struct
  type t =
    | Heapable
    | NotHeapable
  [@@deriving sexp, equal, quickcheck, compare]
end

module Qual_const = struct
  type t =
    | Lin
    | Unr
  [@@deriving sexp, equal, quickcheck, compare]
end

module Loc = struct
  type t = LocV of int [@@deriving sexp, equal, quickcheck, compare]
end

module Qual = struct
  type t =
    | QualV of int
    | QualC of Qual_const.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module Size = struct
  type t =
    | SizeV of int
    | SizeC of int
    | SizeP of t * t
  [@@deriving sexp, equal, quickcheck, compare]

  let rec constant_value = function
    | SizeV _ -> None
    | SizeC n -> Some n
    | SizeP (s1, s2) ->
      let%bind.Option s1 = constant_value s1 in
      let%bind.Option s2 = constant_value s2 in
      Some (s1 + s2)
  ;;


  let equal s1 s2 =
    match constant_value s1, constant_value s2 with
    | Some n1, Some n2 -> n1 = n2
    | _ -> equal s1 s2
  ;;
end

module IntType = struct
  type t =
    | I32
    | I64
  [@@deriving sexp, equal, quickcheck, compare]
end

module FloatType = struct
  type t =
    | F32
    | F64
  [@@deriving sexp, equal, quickcheck, compare]
end

module NumType = struct
  type t =
    | Int of Sign.t * IntType.t
    | Float of FloatType.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module KindVar = struct
  type t =
    | Loc
    | Qual of Qual.t list * Qual.t list
    | Size of Size.t list * Size.t list
    | Type of Qual.t * Size.t * Heapable_const.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module Type = struct
  type t = pt * Qual.t

  and pt =
    | Num of NumType.t
    | Var of int
    | Unit
    | Prod of t list
    | Coderef of ft
    | Rec of Qual.t * t
    | Ptr of Loc.t
    | ExLoc of t
    | Own of Loc.t
    | Cap of Cap.t * Loc.t * ht
    | Ref of Cap.t * Loc.t * ht

  and ht =
    | Variant of t list
    | Struct of (t * Size.t) list
    | Array of t
    | Ex of Qual.t * Size.t * t

  and at = t list * t list
  and ft = KindVar.t list * at [@@deriving sexp, equal, quickcheck, compare]
end

module Mut = struct
  type t = bool [@@deriving sexp, quickcheck, compare]
end

module GlobalType = struct
  type t = Mut.t * Type.pt [@@deriving sexp, quickcheck, compare]
end

module Table = struct
  type t = int list [@@deriving sexp, quickcheck, compare]
end

module LocalEffect = struct
  type t = (int * Type.t) list [@@deriving sexp, quickcheck, compare]
end

module Index = struct
  type t =
    | LocI of Loc.t
    | SizeI of Size.t
    | QualI of Qual.t
    | PretypeI of Type.pt
  [@@deriving sexp, quickcheck, compare]
end

module Value = struct
  type t =
    | Num of NumType.t * (int64, int32) Either.t
    | Unit
  [@@deriving sexp, quickcheck, compare]
end

module IUnOp = struct
  type t =
    | Iclz
    | Ictz
    | Ipopcnt
  [@@deriving sexp, quickcheck, compare]
end

module IBinOp = struct
  type t =
    | Iadd
    | Isub
    | Imul
    | Idiv of Sign.t
    | Irem of Sign.t
    | Iand
    | Ior
    | Ixor
    | Ishl
    | Ishr of Sign.t
    | Irotl
    | Irotr
  [@@deriving sexp, quickcheck, compare]
end

module FUnOp = struct
  type t =
    | Iabs
    | Ineq
    | Isqrt
    | Iceil
    | Ifloor
    | Itrunc
    | Inearest
  [@@deriving sexp, quickcheck, compare]
end

module FBinOp = struct
  type t =
    | Iaddf
    | Isubf
    | Imulf
    | Idivf
    | Imin
    | Imax
    | Icopysign
  [@@deriving sexp, quickcheck, compare]
end

module ITestOp = struct
  type t = Ieqz [@@deriving sexp, quickcheck, compare]
end

module IRelOp = struct
  type t =
    | Ieq
    | Ine
    | Ilt of Sign.t
    | Igt of Sign.t
    | Ile of Sign.t
    | Ige of Sign.t
  [@@deriving sexp, quickcheck, compare]
end

module FRelOp = struct
  type t =
    | Ieqf
    | Inef
    | Iltf
    | Igtf
    | Ilef
    | Igef
  [@@deriving sexp, quickcheck, compare]
end

module CvtOp = struct
  type t =
    | IWrap of IntType.t
    | IExtend of IntType.t
    | ITrunc of FloatType.t * Sign.t
    | ITruncSat of FloatType.t * Sign.t
    | IConvert of IntType.t * Sign.t
    | IDemote of FloatType.t
    | IPromote of FloatType.t
    | IReinterpret of IntType.t
  [@@deriving sexp, quickcheck, compare]
end

module NumInstr = struct
  type t =
    | Iu of IntType.t * IUnOp.t
    | Ib of IntType.t * IBinOp.t
    | Fu of FloatType.t * FUnOp.t
    | Fb of FloatType.t * FBinOp.t
    | It of IntType.t * ITestOp.t
    | Ir of IntType.t * IRelOp.t
    | Fr of FloatType.t * FRelOp.t
    | CvtI of IntType.t * CvtOp.t
    | CvtF of FloatType.t * CvtOp.t
  [@@deriving sexp, quickcheck, compare]
end

module Ex = struct
  type t = string [@@deriving sexp, quickcheck, compare]

  let quickcheck_generator =
    Quickcheck.Generator.map
      (Quickcheck.Generator.list_non_empty Quickcheck.Generator.char_alphanum)
      ~f:String.of_char_list
  ;;
end

module Im = struct
  type t = Import of string * string [@@deriving sexp, quickcheck, compare]

  let quickcheck_generator =
    Quickcheck.Generator.map
      (Quickcheck.Generator.tuple2 Ex.quickcheck_generator Ex.quickcheck_generator)
      ~f:(fun (s1, s2) -> Import (s1, s2))
  ;;
end

module Instruction = struct
  type t =
    | IVal of Value.t
    | INe of NumInstr.t
    | IUnreachable
    | INop
    | IDrop
    | ISelect
    | IBlock of Type.at * LocalEffect.t * t list
    | ILoop of Type.at * t list
    | IITE of Type.at * LocalEffect.t * t list * t list
    | IBr of int
    | IBr_if of int
    | IBr_table of int list * int
    | IRet
    | IGet_local of int * Qual.t
    | ISet_local of int
    | ITee_local of int
    | IGet_global of int
    | ISet_global of int
    | ICoderefI of int
    | IInst of Index.t list
    | ICall_indirect
    | ICall of int * Index.t list
    | IRecFold of Type.pt
    | IRecUnfold
    | IGroup of int * Qual.t
    | IUngroup
    | ICapSplit
    | ICapJoin
    | IRefDemote
    | IMemPack of Loc.t
    | IMemUnpack of Type.at * LocalEffect.t * t list
    | IStructMalloc of Size.t list * Qual.t
    | IStructFree
    | IStructGet of int
    | IStructSet of int
    | IStructSwap of int
    | IVariantMalloc of int * Type.t list * Qual.t
    | IVariantCase of Qual.t * Type.at * LocalEffect.t * t list list
    | IArrayMalloc of Qual.t
    | IArrayGet
    | IArraySet
    | IArrayFree
    | IExistPack of Type.pt * Type.ht * Qual.t
    | IExistUnpack of Qual.t * Type.at * LocalEffect.t * t list
    | IRefSplit
    | IRefJoin
    | IQualify of Qual.t

  and f =
    | Fun of Ex.t list * Type.ft * Size.t list * t list
    | FunIm of Ex.t list * Type.ft * Im.t
  [@@deriving sexp, quickcheck, compare]
end

module Glob = struct
  type t =
    | GlobMut of Type.pt * Instruction.t list
    | GlobEx of Ex.t list * Type.pt * Instruction.t list
    | GlobIm of Ex.t list * Type.pt * Im.t
  [@@deriving sexp, quickcheck, compare]
end

module Module = struct
  type t = Instruction.f list * Glob.t list * Table.t [@@deriving sexp, quickcheck, compare]
end

module Module_type = struct
  type t =
    { funcs : Type.ft list
    ; globs : GlobalType.t list
    ; table : Type.ft list
    ; func_exports : int String.Map.t 
    ; glob_exports : int String.Map.t
    }
  [@@deriving sexp, compare]
end

(*
let%expect_test _ =
  let int_ref : Type.t =
    ( ExLoc
        (Ref (W, LocV 0, Struct [ (Num (Int (U, I32)), QualC Unr), SizeC 32 ]), QualC Unr)
    , QualC Unr )
  in
  let closure : Type.t = (ExLoc (Ref (W, LocV 0,  ), QualC Unr), QualC Unr)
  let closure_heap : Type.ht =
    Ex (QualC Unr, SizeC 32, (Prod [Var 0, QualC Unr; Coderef ([], ([], [])), QualC Unr], QualC Unr))
  print_s [%sexp (int_ref : Type.t)];
  [%expect {| |}]
;;
   *)
