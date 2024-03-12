From Coq Require Import Numbers.BinNums ZArith List Sets.Ensembles.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import MonadNotation.
Import ListNotations.

Require Import RWasm.EnsembleUtil RWasm.functions RWasm.tactics RWasm.typing
        RWasm.term RWasm.debruijn RWasm.subst RWasm.memory RWasm.locations.

Open Scope monad_scope.

Fixpoint set_nth {A} (l : list A) (n : nat) (y : A) :=
  match l with
  | [] => []
  | x :: l =>
    if n =? 0 then y :: l else x :: (set_nth l (n-1) y)
  end.  

Definition subst_in_size is (szs : list Size) := fold_right (fun i szs => subst_index i szs) szs is.
  
Definition value (v : Instruction) : Prop :=
  match v with
  | term.Val _ => True
  | _ => False
  end.

Definition values (vs : list Instruction) : Prop :=
  List.Forall value vs.


Definition qual_const_lub (q p : QualConstant) : QualConstant :=
  match q with
  | Unrestricted => p
  | Linear => Linear
  end.

Definition qual_lub (q p : Qual) : option Qual :=
  match q, p with
  | QualConst q, QualConst p => Some (QualConst (qual_const_lub q p))
  | _, _ => None
  end. 

Definition qual_opt_lub (q p : option Qual) : option Qual :=
  match q, p with
  | Some q, Some p => qual_lub q p
  | _, _ => None
  end.

(* Returns the least upper bound of a list of (option) use qualifiers, if that exists. *)
Definition lub (qs : list (option Qual)) : option Qual :=
  fold_left qual_opt_lub qs (Some (QualConst Unrestricted)).


Definition to_value (v : Instruction) (H : value v) : Value.
  destruct v; try now (exfalso; inversion H; subst; inversion H2).
  exact v.
Defined.

Definition to_values (vs : list Instruction) (H : values vs) : list Value.
  induction vs.
  + exact [].
  + destruct a; try now (exfalso; inversion H; subst; inversion H2).
    assert (Hvs : values vs).
    { inversion H. eassumption. } 
    exact (v :: (IHvs Hvs)).
Defined.


(* Lemmas about [values] and [to_values] *)


Lemma to_values_eq v (H1 H2 : values v) :
  to_values v H1 = to_values v H2.
Proof.    
  rewrite ProofIrrelevance.proof_irrelevance with (p1 := H1) (p2 := H2).
  reflexivity.
Qed.

Lemma to_values_eq2 v1 v2 (H1 : values v1) (H2 : values v2) :
  v1 = v2 ->
  to_values v1 H1 = to_values v2 H2.
Proof.    
  revert v2 H1 H2. induction v1; intros v2 H1 H2 Heq; subst.
  - eapply to_values_eq.
  - simpl.
    assert (Ha := H1). inv Ha.
    destruct a; try now inv H3. f_equal.
    eapply IHv1. reflexivity.
Qed.

Lemma to_values_app v1 v2 (H : values (v1 ++ v2)) (H1 : values v1) (H2 : values v2) :
  to_values (v1 ++ v2) H = to_values v1 H1 ++ to_values v2 H2.
Proof.
  induction v1.
  - erewrite to_values_eq with (H2 := H2). reflexivity.
  - erewrite to_values_eq2 with (v2 := a :: (v1 ++ v2)).
    + simpl.
      assert (Ha := H1). inv Ha.
      destruct a; try now inv H4.
      rewrite <- app_comm_cons.
      f_equal.
      eapply IHv1.
    + eapply app_comm_cons.

      Grab Existential Variables.

      eapply Forall_app in H. destructAll.
      rewrite app_comm_cons.
      eapply Forall_app.  split; eauto.
Qed.

Lemma to_values_len vs (H : values vs) :
  length (to_values vs H) = length vs.
Proof.
  induction vs; simpl; try reflexivity.
  assert (H' := H).
  inv H'.
  destruct a; try now destruct H2. simpl.
  rewrite IHvs. reflexivity.
Qed.   

Lemma values_Val vs :
  values (map Val vs).
Proof. 
  induction vs; simpl.
  - constructor.
  - constructor; eauto. exact I.
Qed.

Lemma to_values_Val vs (H : values (map Val vs)) :
  to_values (map Val vs) H = vs.
Proof.
  induction vs; eauto.
  simpl. f_equal. rewrite IHvs. reflexivity.
Qed.

Inductive context : nat -> Type :=
| LZero : list Value -> list Instruction -> context 0
| LSucc_label :
    forall k,
      list Value ->
      nat -> ArrowType -> list Instruction ->
      context k ->
      list Instruction ->
      context (1 + k).


Fixpoint ctx_app (k : nat) (c : context k) (is : list Instruction) : list Instruction :=
  match c with
  | LZero vs es =>
    map Val vs ++ is ++ es
  | LSucc_label k' vs i tf es1 c' es2 =>
    map Val vs ++ [ Label i tf es1 (ctx_app k' c' is) ] ++ es2
  end.


Notation "L '|[' e ']|' " := (ctx_app _ L e)  (at level 28, no associativity) : ctx_scope.

Lemma ctx_zero_unfold : forall v e1 e2, (map Val v) ++ e2 ++ e1 = ctx_app 0 (LZero v e1) e2. Proof. eauto. Qed.

Lemma ctx_k_unfold :
  forall k vs i tf es1 es2 eshole c,
    (map Val vs) ++ [Label i tf es1 (ctx_app k c eshole)] ++ es2 =
    ctx_app (1 + k) (LSucc_label k vs i tf es1 c es2) eshole.
Proof. eauto. Qed.

Open Scope ctx_scope.

Module Reduction (M : Memory) (T : MemTyping M).

  Import M T T.L. 

  
  Definition Meminst := M.t.

  Definition Val := term.Val.
  Definition Loc := term.Loc. (* TODO fix names? *)



  Definition locs_Store (s : Store) :=
    match s with
    | Build_Store inst meminst out_set =>
      Union_list (map (locs_MInst Unrestricted) inst) 
    end.


  Definition roots_in_lin_mem (s : Store) :=
    let os := out_set s in 
    let h := meminst s in
    [ set l | exists l' hv n, List.In l' os /\ get l' Linear h = Some (hv, n) /\
                              l \in locs_HeapValue Unrestricted hv ]. 
  
  Definition rename_lin_mem (B : M.Loc -> option M.Loc) (s : Store) : Store :=  
    let os := out_set s in 
    let h := meminst s in
    let h' :=
        fold_left (fun h l =>
                     match M.get l Linear h with
                     | Some (hv, n) =>
                       match M.set l Linear h (rename_HeapValue B hv) with
                       | Some h' => h'
                       | None => h (* unreachable *)
                       end
                     | None => h
                     end) os h
    in
    Build_Store (inst s) h' os.

  Inductive Reduce_simple (addr : nat) : list Instruction -> list Instruction -> Type :=
  | red_trap :
      forall (L : context 0),
        Reduce_simple addr (L |[ [Trap] ]|) [Trap]
  | red_unreachable :
      Reduce_simple addr [Unreachable] [Trap]
  | red_nop :
      Reduce_simple addr [Nop] []
  | red_drop :
      forall (v : Value), 
        Reduce_simple addr [Val v ; Drop] []
  | red_select_O :
    forall (v1 v2 : Value) s,
        (* TODO is this typo? *)
        Reduce_simple addr [Val v1; Val v2; Val (NumConst (Int s i32) 0); Select]
                      [Val v2]
  | red_select_not_O :
      forall v1 v2 s z,
        0 <> z ->
        Reduce_simple addr [Val v1; Val v2; Val (NumConst (Int s i32) z); Select]
                      [Val v1]
  | red_block :
      forall vs (Hv : values vs) ts1 ts2 tl es j,
        length ts1 = length vs ->
        length ts2 = j ->
        
        Reduce_simple addr (vs ++ [ Block (Arrow ts1 ts2) tl es ])
                      [Label j (Arrow [] ts2) [] (vs ++ es)]
  | red_loop :
      forall vs (Hv : values vs) ts1 ts2 es j,
        length ts1 = length vs ->
        length ts1 = j ->

        Reduce_simple addr (vs ++ [ Loop (Arrow ts1 ts2) es ])
                      [Label j (Arrow [] ts2) [Loop (Arrow ts1 ts2) es] (vs ++ es)]

  | red_ite_O :
      forall s tf tl es1 es2,
        Reduce_simple addr [Val (NumConst (Int s i32) 0); ITE tf tl es1 es2] [Block tf tl es2]
  | red_ite_not_O :
      forall s tf tl es1 es2 z,
        0 <> z ->            
        Reduce_simple addr [Val (NumConst (Int s i32) z); ITE tf tl es1 es2] [Block tf tl es1]
  | red_label :
      forall n es vs tf,
        values vs ->
        Reduce_simple addr [Label n tf es vs] vs
  | red_label_trap :
      forall n es tf,
        Reduce_simple addr [Label n tf es [Trap]] [Trap]
  | red_label_ctx :
      forall n es vs i (L : context i) tf (Hv : values vs),
        length vs = n ->
        Reduce_simple addr [Label n tf es (L |[ vs ++ [ Br i ] ]|)] (vs ++ es)
  | red_br_if_O  :
      forall s i,
        Reduce_simple addr [Val (NumConst (Int s i32) 0); Br_if i] []
  | red_br_if_not_O  :
      forall s i z,
        0 <> z ->
        Reduce_simple addr [Val (NumConst (Int s i32) z); Br_if i] [Br i]
  | red_br_table_lt  :
      forall s is j i k,
        length is > j ->
        List.nth_error is j = Some k ->
        Reduce_simple addr [Val (NumConst (Int s i32) j); Br_table is i] [ Br k ]
  | red_br_table_geq  :
      forall s is j i,
        length is <= j ->
        Reduce_simple addr [Val (NumConst (Int s i32) j); Br_table is i] [ Br i ]
  | red_tee_local :
      forall j v, 
        Reduce_simple addr [Val v; Tee_local j] [Val v; Val v; Set_local j]
  | red_coderef :
      forall j,
        Reduce_simple addr [CoderefI j] [Val (Coderef addr j [])]
  | red_coderef_inst:
      forall i j zs zs',
        Reduce_simple addr [Val (Coderef i j zs); term.Inst zs'] [Val (Coderef i j (zs ++ zs'))]
  | red_rec_fold:
      forall v pt,
        Reduce_simple addr [Val v; RecFold pt] [Val (Fold v)]
  | red_rec_unfold:
      forall v,
        Reduce_simple addr [Val (Fold v); RecUnfold] [Val v]
  | red_group:
      forall vs i (Hvs : values vs) q, 
        length vs = i ->
        Reduce_simple addr (vs ++ [Group i q]) [Val (Prod (to_values vs Hvs))]
  | red_ungroup:
      forall vs,
        Reduce_simple addr [Val (Prod vs); Ungroup] (map Val vs)
  | red_split:
      Reduce_simple addr [Val Cap; CapSplit] [Val Cap; Val Own]
  | red_join:
      Reduce_simple addr [Val Cap; Val Own; CapJoin] [Val Cap]
  | red_demote:
      forall l,
        Reduce_simple addr [Val (Ref l); RefDemote] [Val (Ref l)]
  | red_refsplit:
      forall l, 
        Reduce_simple addr [Val (Ref l); RefSplit] [Val Cap; Val (PtrV l)]
  | red_refjoin:
      forall l, 
        Reduce_simple addr [Val Cap; Val (PtrV l); RefJoin] [Val (Ref l)] 
  | red_mempack:
      forall v l,
        Reduce_simple addr [Val v; MemPack l] [ Val (Mempack l v) ]
  | red_memunpack: 
      forall loc v tl tf es,
        Reduce_simple addr [Val (Mempack loc v); MemUnpack tf tl es]
                      [ Block tf tl (Val v :: map (subst_ext (Kind:=Kind) (ext SLoc loc id)) es) ]
  | red_struct_malloc: (* TODO from size to nat *)
      forall k vs (Hvs : values vs) ss (Hss : sizes_closed ss) d sz,
        (* Q: Struct malloc list size or list nat?? *)
        length vs = k ->
        length ss = k ->
        fold_left (fun sz1 sz2 => (SizePlus sz1 sz2)) ss (SizeConst 0) = sz ->
        Reduce_simple addr (vs ++ [StructMalloc ss d])
                      [Malloc sz (Struct (to_values vs Hvs)) d]
  | red_variant_malloc:
      forall v j ts d,
        (* Q: types in variant? *)
        Reduce_simple addr [Val v; VariantMalloc j ts d]
                      [Malloc (SizePlus (SizeConst 32) (size_of_value v)) (Variant j v) d]
  | red_array_malloc:
      forall v j d2,
        (* Q: init with the same or different values? *)
        (* TODO: change to single value *) 
        let sz := fold_left (fun sz1 sz2 => (SizePlus sz1 sz2))(repeat (size_of_value v) j) (SizeConst 0) in
        Reduce_simple addr ([Val v ; Val (NumConst (Int U i32) j) ; ArrayMalloc d2])
                      [Malloc (SizePlus (SizeConst 32) sz) (Array j (repeat v j)) d2]
  | red_exist_pack:
      forall v pt ht d,
        Reduce_simple addr [Val v; ExistPack pt ht d]
                      [Malloc (SizePlus (SizeConst 64) (size_of_value v)) (Pack pt v ht) d]
  | red_qualify:
      forall pv d,
        Reduce_simple addr [Val pv; Qualify d] [Val pv]
  | red_local:
      forall j im vl vs szs (Hvs : values vs),
        (* Zoe: I'm not sure if the hypothesis Hvs is necessary (might be for the soundness proof).
         Also, if it is might need to add it to more places *) 
        Reduce_simple addr [ Local j im vl szs vs ] vs
  | red_local_trap :
      forall j im vl szs,
        Reduce_simple addr [ Local j im vl szs [ Trap ] ] [ Trap ]
  | red_local_ctx :
      forall j im vl k (L : context k) vs szs (Hvs : values vs),
        length vs = j ->
        Reduce_simple addr [ Local j im vl szs (L |[ vs ++ [ Ret ] ]|) ] vs
  | red_call_adm :
      (* XXX Michael: come back to this rule *)
    forall vs i exps ft ins i1 i2 foralls ts1 ts2 sz1 zs1 locals szs (H : sizes_closed (subst_in_size zs1 szs))
           (H' : sizes_closed (subst_in_size zs1 sz1)),
        length vs = i1 ->
        length ts1 = i1 ->
        length ts2 = i2 ->
        locals = map (fun s => Tt) szs ->
        (* TODO 1. what is nat in local's list (Value * nat) *)
        (* Q: CHANGE the size of each value after subst *) 
        ft = (FunT foralls (Arrow ts1 ts2)) ->
        let F_cnstr := add_constraints empty_Function_Ctx foralls in
        Forall2 (fun tau sz => sizeOfType (type F_cnstr) tau = Some sz) ts1 sz1 ->

        Reduce_simple addr (map Val vs ++ [ CallAdm (Clo i (Fun exps ft szs ins)) zs1 ])
                      [ Local i2 i (vs ++ locals) (to_sizes (subst_in_size zs1 sz1) H' ++ to_sizes (subst_in_size zs1 szs) H)
                              (map (subst_indices zs1) ins) ].

  Definition update_globals (i : MInst) (g : list (Mut * Value)) :=
    match i with
    | Build_MInst func _ tab =>
      Build_MInst func g tab
    end.

  Definition update_inst (st : Store) (i : list MInst) :=
    match st with
    | Build_Store _ meminst os => Build_Store i meminst os 
    end.


  Definition range_eq_dec (r1 r2 : Loc) : {r1 = r2} + {r1 <> r2}.
  Proof.    
    destruct r1, r2; try (right; congruence).
    - destruct (Nat.eq_dec v v0); subst; eauto.
      right. congruence.
    - destruct (N.eq_dec p p0); subst; eauto.
      destruct q; destruct q0; subst; eauto.
      right. congruence.
      right. congruence.
      right. congruence.      
  Defined.
  

  
  Definition get_mem (s : Store) (loc : Ptr) (q : QualConstant) : option (HeapValue * Len) :=
    M.get loc q (meminst s).
  
  Definition update_mem (s : Store) (l : Ptr) (q : QualConstant) (hv : HeapValue) : option Store :=
    let mem := meminst s in  
    match M.set l q mem hv with
    | Some mem' =>          
      Some (Build_Store (inst s) mem' (out_set s))
    | None => None
    end.  

  Definition free_mem_range (s : Store) (l : Ptr) (q : QualConstant) : option Store :=
    let mem := meminst s in  
    match M.free l q mem with
    | Some mem' =>          
      Some (Build_Store (inst s) mem' (out_set s))
    | None => None
    end.

  Definition alloc_mem_range (s : Store) (q : QualConstant) (sz : Size) (H : size_closed sz) (hv : HeapValue) : option (Ptr * Store) :=
    let mem := meminst s in  
    match M.alloc mem q (N.of_nat (to_size sz H)) hv with
    | Some (mem', l1, l2) =>          
      Some (l1, Build_Store (inst s) mem' (out_set s))
    | None => None
    end.


  Definition remove_out_set (l : M.Loc) (s : Store) :=
    Build_Store (inst s) (meminst s) (remove Loc_EqDec l (out_set s)).
  
  Definition add_out_set (l : M.Loc) (s : Store) (hv : HeapValue) :=
    if has_urn_ptr_HeapValue hv
    then Build_Store (inst s) (meminst s) (l :: out_set s)
    else s.

  Definition update_out_set (l : M.Loc) (s : Store) (hvo hvn : HeapValue) :=
    if has_urn_ptr_HeapValue hvn
    then
      if has_urn_ptr_HeapValue hvo then s
      else Build_Store (inst s) (meminst s) (l :: out_set s)
    else
      if has_urn_ptr_HeapValue hvo then remove_out_set l s
      else s.

  Inductive Reduce_full (addr : nat) : 
    Store ->
    list Value ->
    list nat -> (* the size of each local slot *) 
    list Instruction ->
    Store ->
    list Value ->
    list Instruction -> Type :=
  | red_get_local_unr :
      forall st locals locsize v j,
        nth_error locals j = Some v ->
        Reduce_full addr st locals locsize [Get_local j Unrestricted] st locals [Val v]
  | red_get_local_lin :
      forall st locals locsize locals' v j,
        nth_error locals j = Some v ->
        set_nth locals j Tt = locals' ->
        Reduce_full addr st locals locsize [Get_local j Linear] st locals' [Val v]
  | red_set_local :
      forall st locals locsize locals' v v' s j,
        nth_error locals j = Some v ->
        nth_error locsize j = Some s ->
        (size_val v' <= s)%nat ->        
        set_nth locals j v' = locals' ->
        Reduce_full addr st locals locsize [Val v'; Set_local j] st locals' []
  | red_get_global :
      forall st locals locsize j i v mut,
        nth_error (inst st) addr = Some i ->
        nth_error (glob i) j = Some (mut, v) ->
        Reduce_full addr st locals locsize [Get_global j] st locals [Val v]
  | red_set_global :
      forall st locals locsize j v i pv_old globals inst' mut,
        nth_error (inst st) addr = Some i ->
        nth_error (glob i) j = Some (mut, pv_old) ->
        set_nth (glob i) j (mut, v) = globals ->
        set_nth (inst st) addr (update_globals i globals) = inst' ->
        Reduce_full addr st locals locsize [Val v; Set_global j] (update_inst st inst') locals []
  | red_call_indirect :
      forall st locals locsize ins cl i j is,
        nth_error (inst st) i = Some ins ->
        nth_error (tab ins) j = Some cl ->      
        Reduce_full addr st locals locsize [Val (Coderef i j is); Call_indirect]
                    st locals [CallAdm cl is]
  | red_call :
      forall st locals locsize ins cl j is,
        nth_error (inst st) addr = Some ins ->
        nth_error (func ins) j = Some cl ->      
        Reduce_full addr st locals locsize [Call j is] st locals [CallAdm cl is]
  | red_struct_free :
      forall st locals locsize ,
        (* Q : no val in stack? *) 
        Reduce_full addr st locals locsize [StructFree] st locals [Free]
  | red_struct_get :
      forall st locals locsize l s j vis vi m,
        (* TODO perhaps change mem model to two different mems *) 
        get_mem st l m = Some (Struct vis, s) ->
        nth_error vis j = Some vi ->
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); StructGet j]
                    st locals [ Val (Ref (LocP l m)); Val vi]
  | red_struct_set :
      forall st st' st'' locals locsize l j vis vis' _v v m s,
        get_mem st l m = Some (Struct vis, s) ->
        nth_error vis j = Some _v ->
        set_nth vis j v = vis' ->
        update_mem st l m (Struct vis') = Some st' ->
        (if qualconstr_eq_dec m Linear then st'' = update_out_set l st' (Struct vis) (Struct vis') else st' = st'') -> 

        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val v; StructSet j]
                    st'' locals [ Val (Ref (LocP l m)) ]
  | red_struct_swap :
      forall st st' st'' locals locsize l j vis vis' vo v m s,
        get_mem st l m = Some (Struct vis, s) ->
        nth_error vis j = Some vo ->
        set_nth vis j v = vis' ->
        update_mem st l m (Struct vis')  = Some st' ->
        (if qualconstr_eq_dec m Linear then st'' = update_out_set l st' (Struct vis) (Struct vis') else st' = st'') -> 
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val v; StructSwap j]
                    st'' locals [ Val (Ref (LocP l m)); Val vo ]
  | red_variant_case_am :
      forall st m locals locsize l tf tl ess es i v s tausv vs (Hv : values vs) taus1 taus2,
        get_mem st l m = Some (Variant i v, s) ->
        nth_error ess i = Some es ->
        tf = Arrow taus1 taus2 ->
        length vs = length taus1 ->
        Reduce_full addr st locals locsize (vs ++ [ Val (Ref (LocP l m)); VariantCase Unrestricted tausv tf tl ess ])
                    st locals ((Val (Ref (LocP l m))) :: (vs ++  [Block tf tl (Val v :: es) ]))
  | red_variant_case_mm :
      forall st st' locals locsize l tf tl ess es i v s tausv tauv taus1 taus2 tf',
        get_mem st l Linear = Some (Variant i v, s) ->
        (* replace value with unit so we can free safely *)
        update_mem st l Linear (Array 0 []) = Some st' ->
        nth_error ess i = Some es ->
        nth_error tausv i = Some tauv ->
        tf = Arrow taus1 taus2 ->
        tf' = Arrow (taus1 ++ [tauv]) taus2 ->
        Reduce_full addr st locals locsize [ Val (Ref (LocP l Linear)); VariantCase Linear (VariantType tausv) tf tl ess ]
                    st' locals [ Val v; Val (Ref (LocP l Linear)); Free; Block tf' tl es ]

(*

Array : multiple steps between now and free, replace it with array so that linear invariant is preserved

Unrestricted: we need to rearrange vs and Ref 

TODO change the reduction and typing rule so that v is inside the block

*) 
  | red_array_get :
      forall st locals locsize l su i j vs v m s,
        get_mem st l m = Some (Array i vs, s) ->
        nth_error vs j = Some v ->
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val (NumConst (Int su i32) j); ArrayGet ]
                    st locals [ Val (Ref (LocP l m)); Val v]
  | red_array_get_trap :
      forall st locals locsize l su i j vs m s,
        get_mem st l m = Some (Array i vs, s) ->
        nth_error vs j = None ->
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val (NumConst (Int su i32) j); ArrayGet ]
                    st locals [Trap]
  | red_array_set :
      forall st st' st'' locals locsize l su i j vs v vs' m s,
        get_mem st l m = Some (Array i vs, s) ->
        j < length vs ->
        set_nth vs j v = vs' ->
        update_mem st l m (Array i vs') = Some st' ->
        (if qualconstr_eq_dec m Linear then st'' = update_out_set l st' (Array i vs) (Array i vs') else st' = st'') -> 
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val (NumConst (Int su i32) j); Val v; ArraySet ]
                    st'' locals [ Val (Ref (LocP l m)) ]
  | red_array_set_trap :
      forall st locals locsize l su i j vs v m s,
        get_mem st l m = Some (Array i vs, s) ->
        j >= length vs ->
        Reduce_full addr st locals locsize [ Val (Ref (LocP l m)); Val (NumConst (Int su i32) j); Val v; ArraySet ]
                    st locals [Trap]
  | red_array_free :
      forall st locals locsize,
        (* Q : no val in stack *) 
        Reduce_full addr st locals locsize  [ ArrayFree ] st locals [ Free ]
  | red_unpack_am :
      forall st locals locsize  tf tl es l pt v ht m s ex vs (Hv : values vs) taus1 taus2,
        get_mem st l m = Some (Pack pt v ht, s) ->
        tf = Arrow taus1 taus2 ->
        length vs = length taus1 ->
        (* NOTE: discuss mempack in block *) 
        Reduce_full addr st locals locsize  (vs ++ [ Val (Ref (LocP l m)); ExistUnpack Unrestricted ex tf tl es ])
                    st locals (Val (Ref (LocP l m)) :: (vs ++ [Block tf tl (Val v :: map (subst_ext (Kind:=Kind) (ext SPretype pt id)) es)]))
  | red_unpack_mm :
      forall st st' locals locsize  tf tl es l pt v s ht taus1 taus2 tf' sz qα tau,
        get_mem st l Linear = Some (Pack pt v ht, s) ->
        (* replace value with unit so we can free safely *)
        update_mem st l Linear (Array 0 []) = Some st' ->
        tf = Arrow taus1 taus2 ->
        tf' = Arrow (taus1 ++ [(subst_ext (Kind:= Kind) (ext SPretype pt id)) tau]) taus2 ->
        Reduce_full addr st locals locsize  [ Val (Ref (LocP l Linear)); ExistUnpack Linear (Ex sz qα tau) tf tl es ]
                    st' locals [ Val v; Val (Ref (LocP l Linear)); Free;
                              Block tf' tl
                                    (map (subst_ext (Kind:=Kind) (ext SPretype pt id)) es) ]
  | red_free :
      forall st st' st'' locals locsize l,
        free_mem_range st l Linear = Some st' ->
        st'' = remove_out_set l st' -> (* Zoe: We can only free linear locs *) 
        (* (if qualconstr_eq_dec m Linear then st'' = remove_out_set l st' else st' = st'') ->  *)
        Reduce_full addr st locals locsize  [ Val (Ref (LocP l Linear)); Free ] st'' locals [ ]
  | red_malloc :
      forall st st' st'' locals locsize hv q l sz (H : size_closed sz),
        (* Q : list of values or product? *)
        alloc_mem_range st q sz H hv = Some (l, st') ->
        (if qualconstr_eq_dec q Linear then st'' = add_out_set l st' hv else st' = st'') ->
        Reduce_full addr st locals locsize  [ Malloc sz hv (QualConst q) ]  st'' locals
                    [ Val (Mempack (LocP l q) (Ref (LocP l q))) ]
  | red_malloc_trap :
      forall st locals locsize  hv q sz (H : size_closed sz),
        alloc_mem_range st q sz H hv = None ->
        Reduce_full addr st locals locsize [ Malloc sz hv (QualConst q) ]  st locals [ Trap ].

  (* Q: Variant and Unpack updates? *)

  Inductive Reduce :
    Store ->
    list Value ->
    list nat ->
    list Instruction ->
    nat -> (* address *)
    Store ->
    list Value ->
    list Instruction -> Prop :=
  | CtxCongr :
      forall (s1 s2 : Store) (vs1 vs2 : list Value) szs1 (addr : nat)
             (es1 es2 : list Instruction) (k : nat) (L : context k),
        (* Q : do the i's need to be the same in vs1 vs2? *)
        Reduce s1 vs1 szs1 es1 addr s2 vs2 es2 ->
        Reduce s1 vs1 szs1 (L |[ es1 ]|) addr s2 vs2 (L |[ es2 ]|)
  | LocalCongr :
      forall (s1 s2 : Store) (vs0 vs1 vs2 : list Value) (szs0 szs1 : list nat)
             (i_r i_m i_f : nat)
             (es es1 es2 : list Instruction),
        Reduce s1 vs1 szs1 es1 i_f s2 vs2 es2 ->
        Reduce s1 vs0 szs0 [Local i_r i_f vs1 szs1 es1] i_m s2 vs0 [Local i_r i_f vs2 szs1 es2]
  | StepSimple :
      forall (s1 : Store) (vs1 : list Value) szs1 (addr : nat)
             (es1 es2 : list Instruction),
        Reduce_simple addr es1 es2 ->
        Reduce s1 vs1 szs1 es1 addr s1 vs1 es2
  | StepFull :
      forall (s1 s2 : Store) (vs1 vs2 : list Value) szs1 (addr : nat)
             (es1 es2 : list Instruction),
        Reduce_full addr s1 vs1 szs1 es1 s2 vs2 es2 ->
        Reduce s1 vs1 szs1 es1 addr s2 vs2 es2.

  Inductive GC_step :
    Store ->
    list Value ->
    list Instruction ->
    nat -> (* address *)
    Store ->
    list Value ->
    list Instruction -> Prop :=
  | step_GC :
      forall (s : Store)(vs : list Value) (addr : nat)
             (es : list Instruction) (h2 : Meminst) (outset2 : list M.Loc),
        let h1 := meminst s in
        let outset1 := out_set s in
        let roots := Union_list (map (locs_Instruction Unrestricted) es) :|:
                                Union_list (map (fun v => locs_Value Unrestricted v) vs) :|:
                                locs_Store s
        in
        (* collect the heap *) 
        collect_unr roots h1 h2 ->
        (* Build new store *)
        let s' := Build_Store (inst s) h2 outset1 in
        GC_step s vs es addr s' vs es.

  Inductive Reduce_GC :
    Store ->
    list Value ->
    list nat -> 
    list Instruction ->
    nat -> (* address *)
    Store ->
    list Value ->
    list Instruction -> Prop :=

  | Red :
      forall (s1 s2 : Store) (vs1 vs2 : list Value) sz1 (addr : nat)
             (es1 es2 : list Instruction),
        Reduce s1 vs1 sz1 es1 addr s2 vs2 es2 ->
        Reduce_GC s1 vs1 sz1 es1 addr s2 vs2 es2
  | GC :
      forall s vs sz es addr s',
        GC_step s vs es addr s' vs es ->
        Reduce_GC s vs sz es addr s' vs es.

End Reduction. 
