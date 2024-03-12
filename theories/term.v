From Coq Require Import Numbers.BinNums List NArith.

Import ListNotations.

Definition var := nat.

(* Types and term for the RichWasm language *)

(** ** Types *)

Inductive cap := R | W. 

Inductive Sign := U | S.

(* Definition Range := (N * N)%type. *)
(* Definition MemRange := Range. *)
(* Inductive MemRef := *)
(* | MemVar   : var -> MemRef *)
(* | MemConst : nat -> MemRef. *)

Definition Ptr := N.

Inductive HeapableConstant :=
| Heapable
| NotHeapable.

Inductive QualConstant :=
| Unrestricted
| Linear.

Definition qualconstr_eq_dec (r1 r2 : QualConstant) : {r1 = r2} + {r1 <> r2}.
Proof.    
  destruct r1, r2; try (right; congruence); eauto.
Defined.


Inductive Loc :=
| LocV   : var -> Loc
| LocP   : Ptr -> QualConstant -> Loc.
  

Inductive Qual :=
| QualVar : var -> Qual
| QualConst : QualConstant -> Qual.

Coercion QualConst : QualConstant >-> Qual.

Inductive Size :=
| SizeVar : var -> Size
| SizePlus : Size -> Size -> Size
| SizeConst : nat -> Size.

(* Numeric Types *)

Inductive IntType := i32 | i64.

Inductive FloatType := f32 | f64.

Inductive NumType :=
| Int : Sign -> IntType -> NumType
| Float : FloatType -> NumType.


Inductive KindVar := (* Binding sites for kind variables *)
| LOC  : KindVar
| QUAL : list Qual -> list Qual -> KindVar
| SIZE : list Size -> list Size -> KindVar
| TYPE : Size -> Qual -> HeapableConstant -> KindVar.


Inductive Pretype :=
| Num      : NumType -> Pretype
| TVar     : var -> Pretype
| Unit     : Pretype
| ProdT    : list Typ -> Pretype
| CoderefT : FunType -> Pretype
| Rec      : Qual -> Typ -> Pretype (* binding site *)
| PtrT     : Loc -> Pretype
| ExLoc    : Typ -> Pretype (* binding site *)
| OwnR     : Loc -> Pretype
| CapT     : cap -> Loc -> HeapType -> Pretype
| RefT     : cap -> Loc -> HeapType -> Pretype

with Typ :=
| QualT : Pretype -> Qual -> Typ

with HeapType :=
| VariantType : list Typ -> HeapType
| StructType  : list (Typ * Size) -> HeapType
| ArrayType   : Typ -> HeapType
| Ex          : Size -> Qual -> Typ -> HeapType (* binding site *)

with ArrowType :=
| Arrow : list Typ -> list Typ -> ArrowType

with FunType :=
| FunT : list KindVar -> ArrowType -> FunType.

Definition Mut := bool.

Inductive GlobalType :=
| GT : Mut -> Pretype -> GlobalType.

Definition Table := list nat.

Definition LocalEffect := list (nat * Typ).

Inductive Index :=
| LocI        : Loc -> Index
| SizeI       : Size -> Index
| QualI       : Qual -> Index
| PretypeI    : Pretype -> Index.

Coercion LocI        : Loc >-> Index.
Coercion SizeI       : Size >-> Index.
Coercion QualI       : Qual >-> Index.
Coercion PretypeI    : Pretype >-> Index.

(** ** Terms *)

Inductive Value :=
| NumConst  : NumType -> nat -> Value
| Tt        : Value (* Unit value *)
| Coderef   : nat(* module index *) -> nat (* table index *) -> list Index -> Value
| Fold      : Value -> Value
| Prod      : list Value -> Value
| Ref       : Loc -> Value
| PtrV      : Loc -> Value                                                     
| Cap       : Value
| Own       : Value
| Mempack   : Loc -> Value -> Value.

Inductive HeapValue :=
| Variant : nat -> Value -> HeapValue
| Struct  : list Value -> HeapValue
| Array   : nat -> list Value -> HeapValue
| Pack    : Pretype -> Value ->  HeapType -> HeapValue.

Fixpoint size_val (v : Value) : nat :=
  match v with
  | NumConst (Int _ i32) _ => 32
  | NumConst (Int _ i64) _ => 64
  | NumConst (Float f32) _ => 32
  | NumConst (Float f64) _ => 64
  | Tt => 0
  | Coderef _ _ _ => 64
  | Fold v => size_val v
  | Prod vs => fold_left (fun n v => (size_val v + n)) vs 0
  | Ref _ => 64
  | PtrV _ => 64
  | Cap => 0
  | Own => 0
  | Mempack _ v => size_val v
  end.

Definition size (hv : HeapValue) : nat :=
  match hv with
  | Variant n v => (size_val v) + 32
  | Struct vs => fold_left (fun n v => (size_val v + n)) vs 0
  | Array i vs => fold_left (fun n v => (size_val v + n)) vs 0
  | Pack p v ht => (size_val v) + 32
  end.

Inductive IUnOp :=
| clz | ctz | popcnt.

Inductive IBinOp :=
| add | sub | div : Sign -> IBinOp | rem : Sign -> IBinOp
| and | or | xor | shl | shr : Sign -> IBinOp | rotl | rotr.

Inductive FUnOp :=
| abs | neg | sqrt | ceil | floor | trunc | nearest.

Inductive FBinOp :=
| addf | subf | mulf | divf | min | max | copysign.

Inductive ITestOp := eqz.

Inductive IRelOp :=
| eq | ne
| lt : Sign -> IRelOp | gt : Sign -> IRelOp
| le : Sign -> IRelOp | ge : Sign -> IRelOp.

Inductive FRelOp :=
| eqf | nef
| ltf | gtf
| lef | gef.

Inductive CvtOp :=
| Wrap        : IntType -> CvtOp
| Extend      : IntType -> Sign -> CvtOp
| Trunc       : FloatType -> Sign -> CvtOp
| TruncSat    : FloatType -> Sign -> CvtOp
| Convert     : IntType -> Sign -> CvtOp
| Demote      : FloatType -> CvtOp
| Promote     : FloatType -> CvtOp
| Reinterpret : IntType -> CvtOp.

Inductive NumInstr :=
| Iu   : IntType -> NumInstr
| Ib   : IntType -> NumInstr
| Fu   : FloatType -> NumInstr
| Fb   : FloatType -> NumInstr
| It   : IntType -> NumInstr
| Ir   : IntType -> NumInstr
| Fr   : FloatType -> NumInstr
| CvtI : IntType -> NumInstr
| CvtF : FloatType -> NumInstr.

(* exports *)
Definition ex := positive.
(* imports *)
Definition im := positive.


Inductive Instruction :=
(* Values are instructions *)
| Val : Value -> Instruction

| Ne : NumInstr -> Instruction
| Unreachable
| Nop
| Drop
| Select
| Block : ArrowType -> LocalEffect -> list Instruction -> Instruction
| Loop  : ArrowType -> list Instruction -> Instruction
| ITE   : ArrowType -> LocalEffect -> list Instruction -> list Instruction -> Instruction
| Br    : nat -> Instruction
| Br_if : nat -> Instruction
| Br_table : list nat -> nat -> Instruction
| Ret
| Get_local  : nat -> Qual -> Instruction
| Set_local  : nat -> Instruction
| Tee_local  : nat -> Instruction
| Get_global : nat -> Instruction
| Set_global : nat -> Instruction
| CoderefI   : nat -> Instruction
| Inst       : list Index -> Instruction
| Call_indirect
| Call : nat -> list Index -> Instruction
                                     
(* Rec *)                                     
| RecFold : Pretype -> Instruction
| RecUnfold

(* Seq *)
| Group : nat -> Qual -> Instruction
| Ungroup : Instruction

(* Cap Instructions *)
| CapSplit
| CapJoin

| RefDemote 

| MemPack   : Loc -> Instruction (* XXX Loc or not? *) 
| MemUnpack : ArrowType -> LocalEffect -> list Instruction -> Instruction (* binding site *) 

(* Struct Instructions *)
| StructMalloc : list Size -> Qual -> Instruction
| StructFree
| StructGet : nat -> Instruction
| StructSet : nat -> Instruction
| StructSwap : nat -> Instruction

(* Variant Instructions *)
| VariantMalloc : nat -> list Typ -> Qual -> Instruction
| VariantCase   : Qual -> HeapType -> ArrowType -> LocalEffect -> list (list Instruction) -> Instruction

(* Array Instructions *)
| ArrayMalloc : Qual -> Instruction
| ArrayGet
| ArraySet
| ArrayFree


(* Existsential Instructions *)
| ExistPack   : Pretype -> HeapType -> Qual -> Instruction
| ExistUnpack : Qual -> HeapType -> ArrowType -> LocalEffect -> list Instruction -> Instruction (* binding site *)

(* Ref operations *) 
| RefSplit 
| RefJoin
    
| Qualify : Qual -> Instruction


                      
(* Administrative Instructions *)
| Trap
| CallAdm :  Closure -> list Index -> Instruction
| Label : nat -> ArrowType -> list Instruction -> list Instruction -> Instruction
| Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> Instruction
| Malloc : Size -> HeapValue -> Qual -> Instruction
| Free

with Func :=
| Fun : list ex -> FunType -> list Size -> list Instruction -> Func

with Closure :=
| Clo : nat -> Func -> Closure.


Coercion Val : Value >-> Instruction.

Inductive Glob :=
| GlobMut : Pretype -> list Instruction -> Glob
| GlobEx : list ex -> Pretype -> list Instruction -> Glob
| GlobIm : list ex -> Pretype -> im -> Glob.

Definition module :=
  (list Func * 
   list Glob *
   Table)%type.


Record MInst :=
  { func : list Closure;
    glob : list (Mut * Value);
    tab  : list Closure;
  }.



(** Useful properties *)

Lemma Value_ind' :
  forall P : Value -> Prop,
    (forall (n : NumType) (n0 : nat), P (NumConst n n0)) ->
    P Tt ->
    (forall (n n0 : nat) (l : list Index), P (Coderef n n0 l)) ->
    (forall v : Value, P v -> P (Fold v)) ->
    (forall l : list Value, Forall P l -> P (Prod l)) ->
    (forall l : Loc, P (Ref l)) ->
    (forall l : Loc, P (PtrV l)) ->
    P Cap ->
    P Own ->
    (forall (l : Loc) (v : Value), P v -> P (Mempack l v)) ->
    forall v : Value, P v.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  fix IHv 1. induction v; try (now clear IHv; eauto).
  eapply H5. 
  induction l. 
  - now constructor.
  - constructor. eapply IHv. eassumption.
Qed.

Inductive Forall_type {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_type_nil : Forall_type P []
| Forall_type_cons : forall (x : A) (l : list A),
    P x -> Forall_type P l -> Forall_type P (x :: l).

Lemma Value_rect' :
  forall P : Value -> Type,
    (forall (n : NumType) (n0 : nat), P (NumConst n n0)) ->
    P Tt ->
    (forall (n n0 : nat) (l : list Index), P (Coderef n n0 l)) ->
    (forall v : Value, P v -> P (Fold v)) ->
    (forall l : list Value, Forall_type P l -> P (Prod l)) ->
    (forall l : Loc, P (Ref l)) ->
    (forall l : Loc, P (PtrV l)) ->
    P Cap ->
    P Own ->
    (forall (l : Loc) (v : Value), P v -> P (Mempack l v)) ->
    forall v : Value, P v.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  fix IHv 1. induction v; try (now clear IHv; eauto).
  eapply H5. 
  induction l. 
  - now constructor.
  - constructor. eapply IHv. eassumption.
Qed.

Section PretypeInd.

  Context
    (P : Pretype -> Prop)
    (Q : Typ -> Prop)
    (F : FunType -> Prop)
    (H : HeapType -> Prop)
    (A : ArrowType -> Prop)
    (HQual : forall q p, P p -> Q (QualT p q))
    (HNum : forall n : NumType, P (Num n))
    (HVar : forall v : var, P (TVar v))
    (HUnit : P Unit)
    (HProd : forall l : list Typ, Forall Q l -> P (ProdT l))
    (HCoderef : forall f : FunType, F f -> P (CoderefT f))
    (HRec : forall q (t : Typ), Q t -> P (Rec q t))
    (HPtr : forall l : Loc, P (PtrT l))
    (HExLoc : forall (t : Typ), Q t -> P (ExLoc t))
    (HOwn : forall l : Loc, P (OwnR l))
    (HCap : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (CapT c l h))
    (HRef : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (RefT c l h))
    (HFun : forall (l : list KindVar) (a : ArrowType), A a -> F (FunT l a))
    (HArrow : forall (l1 l2 : list Typ), Forall Q l1 -> Forall Q l2 -> A (Arrow l1 l2))
    (HVariant : forall l : list Typ, Forall Q l -> H (VariantType l))
    (HStruct : forall l : list (Typ * Size), Forall (fun '(t, s) => Q t) l -> H (StructType l))
    (HArray : forall t : Typ, Q t -> H (ArrayType t))
    (HEx : forall (s : Size) q (t : Typ), Q t -> H (Ex s q t)).

  Fixpoint Pretype_ind' (p : Pretype) {struct p} : P p
  with Typ_ind' (q : Typ) {struct q} : Q q
  with FunType_ind' (f : FunType) {struct f} : F f
  with ArrowType_ind' (a : ArrowType) {struct a} : A a
  with HeapType_ind' (h : HeapType) {struct h} : H h.
  Proof.
    - destruct p.
      + apply HNum.
      + apply HVar.
      + apply HUnit.
      + apply HProd.
        induction l; [constructor|constructor].
        * apply Typ_ind'.
        * apply IHl.
      + apply HCoderef, FunType_ind'.
      + apply HRec, Typ_ind'.
      + apply HPtr.
      + apply HExLoc, Typ_ind'.
      + apply HOwn.
      + apply HCap, HeapType_ind'.
      + apply HRef, HeapType_ind'.
    - destruct q. apply HQual, Pretype_ind'.
    - destruct f. apply HFun, ArrowType_ind'.
    - destruct a as [l1 l2].
      apply HArrow; ((induction l1 + induction l2); constructor;
                     [apply Typ_ind'|apply IHl1+apply IHl2]).
    - destruct h.
      + apply HVariant. induction l; constructor; [apply Typ_ind'|apply IHl].
      + apply HStruct. induction l; constructor; [destruct a; apply Typ_ind'|apply IHl].
      + apply HArray, Typ_ind'.
      + apply HEx, Typ_ind'.
  Defined.

  Corollary Pre_Typ_Fun_Arrow_Heap_ind :
    (forall p, P p) /\ (forall q, Q q) /\ (forall f, F f) /\ (forall a, A a) /\ (forall h, H h).
  Proof.
    repeat split;
      (apply Pretype_ind'||apply Typ_ind'||apply FunType_ind'
       ||apply ArrowType_ind'||apply HeapType_ind').
  Qed.
  
End PretypeInd.

Section PretypeRect.

  Context
    (P : Pretype -> Type)
    (Q : Typ -> Type)
    (F : FunType -> Type)
    (H : HeapType -> Type)
    (A : ArrowType -> Type)
    (HQual : forall q p, P p -> Q (QualT p q))
    (HNum : forall n : NumType, P (Num n))
    (HVar : forall v : var, P (TVar v))
    (HUnit : P Unit)
    (HProd : forall l : list Typ, Forall_type Q l -> P (ProdT l))
    (HCoderef : forall f : FunType, F f -> P (CoderefT f))
    (HRec : forall q (t : Typ), Q t -> P (Rec q t))
    (HPtr : forall l : Loc, P (PtrT l))
    (HExLoc : forall (t : Typ), Q t -> P (ExLoc t))
    (HOwn : forall l : Loc, P (OwnR l))
    (HCap : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (CapT c l h))
    (HRef : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (RefT c l h))
    (HFun : forall (l : list KindVar) (a : ArrowType), A a -> F (FunT l a))
    (HArrow : forall (l1 l2 : list Typ), Forall_type Q l1 -> Forall_type Q l2 -> A (Arrow l1 l2))
    (HVariant : forall l : list Typ, Forall_type Q l -> H (VariantType l))
    (HStruct : forall l : list (Typ * Size), Forall_type (fun '(t, s) => Q t) l -> H (StructType l))
    (HArray : forall t : Typ, Q t -> H (ArrayType t))
    (HEx : forall (s : Size) q (t : Typ), Q t -> H (Ex s q t)).

  Fixpoint Pretype_rect' (p : Pretype) {struct p} : P p
  with Typ_rect' (q : Typ) {struct q} : Q q
  with FunType_rect' (f : FunType) {struct f} : F f
  with ArrowType_rect' (a : ArrowType) {struct a} : A a
  with HeapType_rect' (h : HeapType) {struct h} : H h.
  Proof.
    - destruct p.
      + apply HNum.
      + apply HVar.
      + apply HUnit.
      + apply HProd.
        induction l; [constructor|constructor].
        * apply Typ_rect'.
        * apply IHl.
      + apply HCoderef, FunType_rect'.
      + apply HRec, Typ_rect'.
      + apply HPtr.
      + apply HExLoc, Typ_rect'.
      + apply HOwn.
      + apply HCap, HeapType_rect'.
      + apply HRef, HeapType_rect'.
    - destruct q. apply HQual, Pretype_rect'.
    - destruct f. apply HFun, ArrowType_rect'.
    - destruct a as [l1 l2].
      apply HArrow; ((induction l1 + induction l2); constructor;
                     [apply Typ_rect'|apply IHl1+apply IHl2]).
    - destruct h.
      + apply HVariant. induction l; constructor; [apply Typ_rect'|apply IHl].
      + apply HStruct. induction l; constructor; [destruct a; apply Typ_rect'|apply IHl].
      + apply HArray, Typ_rect'.
      + apply HEx, Typ_rect'.
  Defined.

  Corollary Pre_Typ_Fun_Arrow_Heap_rect :
    (forall p, P p) * (forall q, Q q) * (forall f, F f) * (forall a, A a) * (forall h, H h).
  Proof.
    repeat split;
      (apply Pretype_rect'||apply Typ_rect'||apply FunType_rect'
       ||apply ArrowType_rect'||apply HeapType_rect').
  Qed.
  
End PretypeRect.

Section InstructionInd.

  Context
    (I : Instruction -> Prop)
    (F : Func -> Prop)
    (C : Closure -> Prop).

  Context
    (HVal : forall v, I (Val v))
    (HNe : forall ninstr, I (Ne ninstr))
    (HUnreachable : I Unreachable)
    (HNop : I Nop)
    (HDrop : I Drop)
    (HSelect : I Select)
    (HBlock : forall arty leff insns, Forall I insns -> I (Block arty leff insns))
    (HLoop  : forall arty insns, Forall I insns -> I (Loop arty insns))
    (HITE   : forall arty leff insns1 insns2,
        Forall I insns1 ->
        Forall I insns2 ->
        I (ITE arty leff insns1 insns2))
    (HBr    : forall n, I (Br n))
    (HBr_if : forall n, I (Br_if n))
    (HBr_table : forall ns n, I (Br_table ns n))
    (HRet : I Ret)
    (HGet_local  : forall n qual, I (Get_local n qual))
    (HSet_local  : forall n, I (Set_local n))
    (HTee_local  : forall n, I (Tee_local n))
    (HGet_global : forall n, I (Get_global n))
    (HSet_global : forall n, I (Set_global n))
    (HCoderefI   : forall n, I (CoderefI n))
    (HInst       : forall ixs, I (Inst ixs))
    (HCall_indirect : I Call_indirect)
    (HCall : forall n ixs, I (Call n ixs))
    (HRecFold : forall pt, I (RecFold pt))
    (HRecUnfold : I RecUnfold)
    (HGroup : forall n qual, I (Group n qual))
    (HUngroup : I Ungroup)
    (HCapSplit : I CapSplit)
    (HCapJoin : I CapJoin)
    (HRefDemote  : I RefDemote)
    (HMemPack   : forall l, I (MemPack l))
    (HMemUnpack : forall arty leff insns, Forall I insns -> I (MemUnpack arty leff insns))
    (HStructMalloc : forall szs qual, I (StructMalloc szs qual))
    (HStructFree : I StructFree)
    (HStructGet : forall n, I (StructGet n))
    (HStructSet : forall n, I (StructSet n))
    (HStructSwap : forall n, I (StructSwap n))
    (HVariantMalloc : forall n typs qual, I (VariantMalloc n typs qual))
    (HVariantCase   : forall qual arty leff insnss tausv,
        Forall (Forall I) insnss ->
        I (VariantCase qual tausv arty leff insnss))
    (HArrayMalloc : forall qual, I (ArrayMalloc qual))
    (HArrayGet : I ArrayGet)
    (HArraySet : I ArraySet)
    (HArrayFree : I ArrayFree)
    (HExistPack   : forall pt ht qual, I (ExistPack pt ht qual))
    (HExistUnpack : forall qual arty leff insns ex , Forall I insns -> I (ExistUnpack qual ex arty leff insns))
    (HRefSplit  : I RefSplit)
    (HRefJoin : I RefJoin)
    (HQualify : forall qual, I (Qualify qual))
    (HTrap : I Trap)
    (HCallAdm : forall clo ixs, C clo -> I (CallAdm clo ixs))
    (HLabel : forall n arty insns1 insns2,
        Forall I insns1 ->
        Forall I insns2 ->
        I (Label n arty insns1 insns2))
    (HLocal : forall n1 n2 vs ns insns, Forall I insns -> I (Local n1 n2 vs ns insns))
    (HMalloc : forall sz hv qual, I (Malloc sz hv qual))
    (HFree : I Free).

  Context (HFun : forall exs fty szs insns, Forall I insns -> F (Fun exs fty szs insns)).

  Context (HClo : forall n func, F func -> C (Clo n func)).

  Local Ltac clear_ihs :=
    try match goal with
    | HI : forall x, I x, HF : forall x, F x, HC : forall x, C x |- _ => clear HI HF HC
    end.
  
  Local Ltac list_ind :=
    match goal with
    | IH : forall _, ?P _ |- Forall (Forall ?P) ?l =>
      clear - IH; induction l; constructor; try assumption; list_ind
    | IH : forall _, ?P _ |- Forall ?P ?l =>
      clear - IH; induction l; constructor; auto
    end.
  
  Fixpoint Instruction_ind' (insn : Instruction) {struct insn} : I insn
  with Func_ind' (func : Func) {struct func} : F func
  with Closure_ind' (clo : Closure) {struct clo} : C clo.
  Proof.
    - destruct insn;
      multimatch goal with
      | HI : forall x, I x, HF : forall x, F x, HC : forall x, C x, H : _ |- _ => apply H
      end; solve [list_ind|clear_ihs; eauto|eauto].
    - destruct func; apply HFun; list_ind.
    - destruct clo; apply HClo; apply Func_ind'.
  Qed.

  Corollary Instruction_Func_Closure_ind :
    (forall i, I i) /\ (forall f, F f) /\ (forall c, C c).
  Proof. repeat split; (apply Instruction_ind'||apply Func_ind'||apply Closure_ind'). Qed.
  
End InstructionInd.
