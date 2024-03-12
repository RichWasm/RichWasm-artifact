open! Core

module Cap : sig
  type t =
    | R
    | W
  [@@deriving sexp, equal, quickcheck, compare]
end

module Sign : sig
  type t =
    | S
    | U
  [@@deriving sexp, equal, quickcheck, compare]
end

module Heapable_const : sig
  type t =
    | Heapable
    | NotHeapable
  [@@deriving sexp, equal, quickcheck, compare]
end

module Qual_const : sig
  type t =
    | Lin
    | Unr
  [@@deriving sexp, equal, quickcheck, compare]
end

module Loc : sig
  type t = LocV of int [@@deriving sexp, equal, quickcheck, compare]
end

module Qual : sig
  type t =
    | QualV of int
    | QualC of Qual_const.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module Size : sig
  type t =
    | SizeV of int
    | SizeC of int
    | SizeP of t * t
  [@@deriving sexp, equal, quickcheck, compare]
end

module IntType : sig
  type t =
    | I32
    | I64
  [@@deriving sexp, equal, quickcheck, compare]
end

module FloatType : sig
  type t =
    | F32
    | F64
  [@@deriving sexp, equal, quickcheck, compare]
end

module NumType : sig
  type t =
    | Int of Sign.t * IntType.t
    | Float of FloatType.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module KindVar : sig
  type t =
    | Loc
    | Qual of Qual.t list * Qual.t list
    | Size of Size.t list * Size.t list
    | Type of Qual.t * Size.t * Heapable_const.t
  [@@deriving sexp, equal, quickcheck, compare]
end

module Type : sig
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

module Mut : sig
  type t = bool [@@deriving sexp, quickcheck, compare]
end

module GlobalType : sig
  type t = Mut.t * Type.pt [@@deriving sexp, quickcheck, compare]
end

module Table : sig
  type t = int list [@@deriving sexp, quickcheck, compare]
end

module LocalEffect : sig
  type t = (int * Type.t) list [@@deriving sexp, quickcheck, compare]
end

module Index : sig
  type t =
    | LocI of Loc.t
    | SizeI of Size.t
    | QualI of Qual.t
    | PretypeI of Type.pt
  [@@deriving sexp, quickcheck, compare]
end

module Value : sig
  type t =
    | Num of NumType.t * (int64, int32) Either.t
    | Unit
  [@@deriving sexp, quickcheck, compare]
end

module IUnOp : sig
  type t =
    | Iclz
    | Ictz
    | Ipopcnt
  [@@deriving sexp, quickcheck, compare]
end

module IBinOp : sig
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

module FUnOp : sig
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

module FBinOp : sig
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

module ITestOp : sig
  type t = Ieqz [@@deriving sexp, quickcheck, compare]
end

module IRelOp : sig
  type t =
    | Ieq
    | Ine
    | Ilt of Sign.t
    | Igt of Sign.t
    | Ile of Sign.t
    | Ige of Sign.t
  [@@deriving sexp, quickcheck, compare]
end

module FRelOp : sig
  type t =
    | Ieqf
    | Inef
    | Iltf
    | Igtf
    | Ilef
    | Igef
  [@@deriving sexp, quickcheck, compare]
end

module CvtOp : sig
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

module NumInstr : sig
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

module Ex : sig
  type t = string [@@deriving sexp, quickcheck, compare]
end

module Im : sig
  type t = Import of string * string [@@deriving sexp, quickcheck, compare]
end

module Instruction : sig
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

module Glob : sig
  type t =
    | GlobMut of Type.pt * Instruction.t list
    | GlobEx of Ex.t list * Type.pt * Instruction.t list
    | GlobIm of Ex.t list * Type.pt * Im.t
  [@@deriving sexp, quickcheck, compare]
end

module Module : sig
  type t = Instruction.f list * Glob.t list * Table.t [@@deriving sexp, quickcheck, compare]
end

module Module_type : sig
  type t =
    { funcs : Type.ft list
    ; globs : GlobalType.t list
    ; table : Type.ft list
    ; func_exports : int String.Map.t
    ; glob_exports : int String.Map.t
    }
  [@@deriving sexp, compare]
end
