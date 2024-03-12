From Coq Require Import Numbers.BinNums ZArith List Ensembles.

Require Import RWasm.term RWasm.memory RWasm.EnsembleUtil
        RWasm.functions RWasm.tactics.

Import ListNotations.

Instance Loc_EqDec : EquivDec.EqDec Ptr Logic.eq.
Proof.
  intros x y.
  destruct (N.eqb_spec x y); eauto.
Qed.

Module Location (M : Memory).

  Module MUtils := MemUtils M.

  Import M MUtils.


  Section Renaming.

    Context (B : Loc -> option Loc).
    
    Definition rename_Loc (l : term.Loc) :=
      match l with
      | LocV _ 
      | LocP _ Linear => l
      | LocP l' Unresticted =>
        match B l' with
        | Some l'' => LocP l'' Unresticted
        | None => l
        end
      end.

    Fixpoint rename_PreType (pt : Pretype) :=
      match pt with
      | Num _
      | TVar _
      | Unit => pt
      | ProdT ts => ProdT (map rename_Typ ts)
      | CoderefT ft => CoderefT (rename_FunType ft)
      | Rec q t => Rec q (rename_Typ t)
      | PtrT l => PtrT (rename_Loc l)
      | ExLoc t => ExLoc (rename_Typ t)
      | OwnR l => OwnR (rename_Loc l)
      | CapT c l ht => CapT c (rename_Loc l) (rename_HeapType ht)
      | RefT c l ht => RefT c (rename_Loc l) (rename_HeapType ht)
      end
    with rename_Typ (t : Typ) :=
           match t with
           | QualT pt q => QualT (rename_PreType pt) q
           end
    with rename_HeapType (ht : HeapType) :=
           match ht with
           | VariantType ts => VariantType (map rename_Typ ts)
           | StructType tss => StructType (map (fun '(t, s) => (rename_Typ t, s)) tss)
           | ArrayType t => ArrayType (rename_Typ t)
           | Ex s q t => Ex s q (rename_Typ t)
           end
    with rename_ArrowType (a : ArrowType) :=
           match a with
           | Arrow ts1 ts2 => Arrow (map rename_Typ ts1) (map rename_Typ ts2)
           end
    with rename_FunType (ft : FunType) :=
           match ft with
           | FunT foralls a =>
             FunT foralls (rename_ArrowType a)
           end.
             

           
    Definition rename_GlobalType (gt : GlobalType) :=
      match gt with
      | GT m pt => GT m (rename_PreType pt)
      end.


    Definition rename_LocalEffect (lf : LocalEffect) :=
      map (fun '(n, t) => (n, rename_Typ t)) lf.
        

    
    Fixpoint rename_Value (v : Value) :=
      match v with
      | NumConst _ _ 
      | Tt 
      | Cap 
      | Own
      | Coderef _ _ _ => v
      | Fold v => Fold (rename_Value v)
      | term.Prod vs => term.Prod (map rename_Value vs)
      | Ref l => Ref (rename_Loc l)
      | PtrV l => PtrV (rename_Loc l)
      | Mempack l v => Mempack (rename_Loc l) (rename_Value v) (* TODO not sure about that *)
      end.        

    Definition rename_HeapValue (hv : HeapValue) :=
      match hv with
      | Variant n v => Variant n (rename_Value v)
      | Struct vs => Struct (map rename_Value vs)
      | Array i vs => Array i (map rename_Value vs)
      | Pack pt v ht => Pack (rename_PreType pt) (rename_Value v) (rename_HeapType ht)
      end.

    Definition rename_Index (i : Index) :=
      match i with
      | LocI l => LocI (rename_Loc l)
      | SizeI _ => i
      | QualI _ => i
      | PretypeI pt => PretypeI (rename_PreType pt)
      end.


    Fixpoint rename_Instruction (i : Instruction) :=
      match i with
      | term.Val v => term.Val (rename_Value v)
      | Ne _
      | Unreachable
      | Nop
      | Drop
      | Select
      | Br_if _
      | Br_table _ _
      | Ret
      | Get_local _ _
      | Set_local _
      | Tee_local _
      | Get_global _
      | Set_global _
      | CoderefI _
      | Call_indirect
      | RecUnfold
      | Group _ _
      | Ungroup
      | CapSplit
      | CapJoin
      | RefDemote
      | StructMalloc _ _
      | StructFree
      | StructGet _
      | StructSet _ 
      | StructSwap _ 
      | ArrayMalloc _
      | ArrayGet
      | ArraySet
      | ArrayFree
      | RefSplit
      | RefJoin
      | Qualify _
      | Trap
      | Br _ 
      | Free => i
      | Block tf tl i => Block (rename_ArrowType tf) (rename_LocalEffect tl) (map rename_Instruction i)
      | Loop tf i => Loop (rename_ArrowType tf) (map rename_Instruction i)
      | ITE tf tl i1 i2 => ITE (rename_ArrowType tf) (rename_LocalEffect tl) (map rename_Instruction i1) (map rename_Instruction i2)
      | Inst i => Inst (map rename_Index i)
      | Call n i => Call n (map rename_Index i)
      | RecFold pt => RecFold (rename_PreType pt)
      | MemPack l => MemPack (rename_Loc l) (* XXX not sure *)
      | MemUnpack tf tl i => MemUnpack (rename_ArrowType tf) (rename_LocalEffect tl) (map rename_Instruction i)

      | VariantMalloc n ts q => VariantMalloc n (map rename_Typ ts) q
      | VariantCase q tausv tf tl iss => VariantCase q (rename_HeapType tausv) (rename_ArrowType tf) (rename_LocalEffect tl)
                                               (map (map (rename_Instruction)) iss)
          
      | ExistPack pt ht a => ExistPack (rename_PreType pt) (rename_HeapType ht) a
      | ExistUnpack q ex tf tl i => ExistUnpack q (rename_HeapType ex) (rename_ArrowType tf) (rename_LocalEffect tl) (map rename_Instruction i)

      | CallAdm cl i => CallAdm (rename_Closure cl) (map rename_Index i)
      | Label i tf i1 i2 => Label i (rename_ArrowType tf) (map rename_Instruction i1) (map rename_Instruction i2)
      | Local n m vs ss i => Local n m (map rename_Value vs) ss (map rename_Instruction i)
      | Malloc sz hv q => Malloc sz (rename_HeapValue hv) q
      end
    with rename_Func (f : Func) :=
           match f with
           | Fun exs ft s i => Fun exs (rename_FunType ft) s (map rename_Instruction i)
           end
    with rename_Closure (cl : Closure) :=
           match cl with
           | Clo n fn => Clo n (rename_Func fn)
           end.


    Definition rename_MInst (i : MInst) :=
      match i with
      | Build_MInst func glob tab =>
        Build_MInst (map rename_Closure func)
                    (map (fun '(mut, glob) => (mut, rename_Value glob)) glob)
                    (map rename_Closure tab)
      end.

    Definition rename_out_set (l : list M.Loc) :=
      map (fun l => match B l with Some l' => l' | None => l end) l.

  End Renaming.

  Section Locs.

    Context (mode : QualConstant).

    (* The set of locs appearing in various language constructs *)

    Definition locs_Loc (l : term.Loc) : Ensemble Loc :=
      match l with
      | LocV _ => Empty_set _
      | LocP l mode' => if qualconstr_eq_dec mode mode' then [set l] else Empty_set _
      end.    

    Global Instance Decidable_locs_Loc l : Decidable (locs_Loc l).
    Proof.
      destruct l; simpl; tci.
      destruct (qualconstr_eq_dec mode q); tci.
    Qed.      
           

    Fixpoint locs_Value (v : Value) : Ensemble Loc :=
      match v with
      | NumConst _ _
      | Tt
      | Cap
      | Own
      | Coderef _ _ _
      | PtrV _ => Empty_set _
      | Fold v | Mempack _ v =>  locs_Value v
      | term.Prod vs => Union_list (map locs_Value vs)
      | Ref l => locs_Loc l
      end.

    
    Global Instance Decidable_locs_Value v : Decidable (locs_Value v).
    Proof.
      eapply Value_rect' with (P := fun v => Decidable (locs_Value v)).
      all: intros; simpl in *.
      all: try auto.
      all:
        try match goal with
            | [ |- Decidable (Empty_set _) ] =>
              apply Decidable_Empty_set
            end.
      - revert H.
        induction l; intros; simpl in *; auto.
        -- apply Decidable_Empty_set.
        -- inversion H; subst; simpl in *.
           apply Decidable_Union; auto.
      - apply Decidable_locs_Loc.
    Qed.

    Definition locs_HeapValue (hv : HeapValue) : Ensemble Loc :=
      match hv with
      | Variant _ v => locs_Value v
      | Struct vs => Union_list (map locs_Value vs)
      | Array _ vs => Union_list (map locs_Value vs)
      | Pack _ v _ => locs_Value v
      end.

    Global Instance Decidable_locs_HeapValue v : Decidable (locs_HeapValue v).
    Proof.
      destruct v; simpl; tci.
    Qed.

    Definition locs_Index (i : Index) : Ensemble Loc :=
      match i with
      | LocI l => locs_Loc l (* because potentially can instantiate a Ref loc. But it's an overapprox *)
      | _ => Empty_set _
      end.
    
    Fixpoint locs_Instruction (i : Instruction) : Ensemble Loc :=
      match i with
      | term.Val v => locs_Value v
      | Ne _
      | Unreachable
      | Nop
      | Drop
      | Select
      | Br_if _
      | Br_table _ _
      | Ret
      | Get_local _ _
      | Set_local _
      | Tee_local _
      | Get_global _
      | Set_global _
      | CoderefI _
      | Call_indirect
      | RecUnfold
      | Group _ _
      | Ungroup
      | CapSplit
      | CapJoin
      | RefDemote
      | StructMalloc _ _
      | StructFree
      | StructGet _
      | StructSet _ 
      | StructSwap _ 
      | ArrayMalloc _
      | ArrayGet
      | ArraySet
      | ArrayFree
      | RefSplit
      | RefJoin
      | Qualify _
      | Trap
      | Br _ 
      | Free => Empty_set _
      | Block tf tl i => Union_list (map locs_Instruction i)
      | Loop tf i => Union_list (map locs_Instruction i)
      | ITE tf tl i1 i2 => (Union_list (map locs_Instruction i1)) :|: (Union_list (map locs_Instruction i2))
      | Inst i => Union_list (map locs_Index i)
      | Call n i => Union_list (map locs_Index i)
      | RecFold pt => Empty_set _
      | MemPack l => Empty_set _ (* locs_Loc l (* XXX not sure *) *)
      | MemUnpack tf tl i => Union_list (map locs_Instruction i)
      | VariantMalloc n ts q => Empty_set _
      | VariantCase q tausv tf tl iss =>
        Union_list (map (fun i => Union_list (map locs_Instruction i)) iss)
      | ExistPack pt ht a => Empty_set _
      | ExistUnpack q ex tf tl i => Union_list (map locs_Instruction i)
      | CallAdm cl i => locs_Closure cl :|: Union_list (map locs_Index i)
      | Label i tf i1 i2 => (Union_list (map locs_Instruction i1)) :|: (Union_list (map locs_Instruction i2))
      | Local n m vs ss i => (Union_list (map locs_Value vs)) :|: (Union_list (map locs_Instruction i))
      | Malloc sz hv q => locs_HeapValue hv
      end
    with locs_Func (f : Func) :=
           match f with
           | Fun exs ft s i => (Union_list (map locs_Instruction i))
           end
    with locs_Closure (cl : Closure) :=
           match cl with
           | Clo n fn => locs_Func fn
           end.


    Definition locs_MInst (i : MInst) :=
      match i with
      | Build_MInst func glob tab =>
        (Union_list (map locs_Closure func)) :|: (Union_list (map (fun '(_, glob) => locs_Value glob) glob)) :|: (Union_list (map locs_Closure tab))
      end.
        

  End Locs.
  
  (* Unresticted reachable locs *)

  Section Reachable.

    Context (mode : QualConstant).    

    
    (** The locations that are pointed by the locations in S *)  
    Definition post (H : M.t) (S : Ensemble Loc) :=
      [ set l : Loc | exists l' v n, l' \in S /\ get l' mode H = Some (v, n) /\
                                            l \in locs_HeapValue mode v].  

    (* The reachable set of locations starting from a root set S *)
    Definition reach (H : M.t) (S : Ensemble Loc) : Ensemble Loc :=
      \bigcup_(n : nat) (((post H) ^ n) S).
    
  End Reachable.

  (* Reachable *unrestricted* locations in *unrestricted* memory *)
  Definition reach_unr H S := reach Unrestricted H S.

  (* Reachable *linear* locations in *linear* memory *)  
  Definition reach_lin H S := reach Linear H S. 

  (* Linear locations that appear in unrestricted memory *) 
  Definition lin_locs_in_unr H :=
    [ set l : Loc | exists l' v n, get l' Unrestricted H = Some (v, n) /\
                                   l \in locs_HeapValue Linear v].

  

  Definition outset (h : M.t) : Ensemble Loc :=
    [ set l | exists l' v len, get l' Linear h = Some (v, len) /\ l \in locs_HeapValue Unrestricted v ]. 
          

  (* Collect Unrestructicted heap *)
  
  Definition collect_unr
             (S : Ensemble Loc) (* roots *)
             (H : M.t) (* initial heap *)
             (H' : M.t) (* resulting heap *) :=

    sub_heap Unrestricted H' H /\
    sub_heap Linear H' H /\
      
    (* Collect the GC'ed memory *) 
    (forall l v n, l \in reach_unr H (S :|: outset H) <->
                   (M.get l Unrestricted H = Some (v, n) /\ M.get l Unrestricted H' = Some (v, n))) /\

    (* Recursively free dangling chains of references in linear memory *)
    (forall l, l \in reach_lin H (lin_locs_in_unr H \\ lin_locs_in_unr H') <->
    ((exists v, get l Linear H = Some v) /\ get l Linear H' = None)).

  Definition has_urn_ptr_Loc (l : term.Loc) : bool :=
    match l with
    | LocP l Unrestricted => true
    | _ => false
    end.    

           
  Definition has_urn_ptr_Value (v : Value) : bool :=
    match v with
    | Ref l => has_urn_ptr_Loc l        
    | _ => false
    end.
  
  Definition has_urn_ptr_HeapValue (hv : HeapValue) : bool :=
    match hv with
    | Variant _ v => has_urn_ptr_Value v
    | Struct vs => existsb has_urn_ptr_Value vs
    | Array _ vs => existsb has_urn_ptr_Value vs
    | Pack _ v _ => has_urn_ptr_Value v
    end.

End Location.
