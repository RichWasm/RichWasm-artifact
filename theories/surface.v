From Coq Require Import Numbers.BinNums ZArith List Sets.Ensembles.

Require Import RWasm.EnsembleUtil RWasm.functions RWasm.tactics RWasm.term
        RWasm.debruijn RWasm.memory RWasm.locations RWasm.reduction RWasm.typing
        RWasm.splitting.

Import ListNotations.


Definition surface_Value (v : Value) : bool := 
  match v with
  | NumConst _ _ 
  | Tt => true
  | Coderef _ _ _
  | Fold _
  | Prod _
  | Ref _
  | PtrV _
  | Cap
  | Own
  | Mempack _ _ => false
  end.

  
Fixpoint surface_Inst (i : Instruction) : bool :=
  match i with
  | Val x => surface_Value x
  | Ne _
  | Unreachable
  | Nop
  | Drop
  | Select
  | Br _
  | Br_if _
  | Br_table _ _
  | Ret
  | Get_local _ _
  | Set_local _
  | Tee_local _
  | Get_global _
  | Set_global _
  | Inst _
  | Call_indirect
  | term.Call _ _
  | RecFold _ 
  | RecUnfold
  | Group _ _
  | Ungroup
  | CapSplit
  | CapJoin
  | RefDemote
  | MemPack _
  | StructMalloc _ _
  | StructFree 
  | StructGet _ 
  | StructSet _
  | StructSwap _
  | VariantMalloc _ _ _ 
  | ArrayMalloc _
  | ArrayGet
  | ArraySet
  | ArrayFree
  | CoderefI _ 
  | ExistPack _ _ _
  | RefSplit
  | RefJoin
  | Qualify _ => true
  (* admin instructions *)
  | Trap 
  | CallAdm _ _
  | Malloc _ _ _
  | Label _ _ _ _
  | Local _ _ _ _ _
  | Free => false
  (* Recursive cases *)
  | Block _ _ ins => forallb surface_Inst ins
  | Loop _ ins => forallb surface_Inst ins
  | ITE _ _ ins1 ins2 =>
    forallb surface_Inst ins1 && forallb surface_Inst ins2
  | MemUnpack _ _ ins => forallb surface_Inst ins
  | VariantCase _ _ _ _ ins => forallb (forallb surface_Inst) ins
  | ExistUnpack _ _ _ _ ins => forallb surface_Inst ins
  end.


Definition nonval_Inst (i : Instruction) : bool :=
  match i with
  | Val _ => false | _ => true
  end.

Definition well_formed_context {k} (C : context k) : bool :=
  match C with
  | LZero vs is => forallb surface_Inst is
  | LSucc_label vs _ _ _ is1 ctx is2 => forallb surface_Inst is2   
  end.

Definition well_formed_in_context p :=
  forall k (C : context k) p',
    p' <> [] ->
    existsb nonval_Inst p' = true ->  
    C |[ p' ]| = p -> well_formed_context C = true.


Fixpoint well_formed_Inst_list (is : list Instruction) : bool :=
  match is with
  | Val _ :: is => well_formed_Inst_list is 
  | _ :: is => forallb surface_Inst is
  | [] => true
  end. 


(** Usefull tactics *)

Ltac do_Forall_app :=
  match goal with
  | [H : Forall _ (_ ++ _) |- _ ] =>
      eapply Forall_app in H; destructAll
  end.

Ltac do_bools :=
  match goal with
  | [ H : (_ && _)%bool = true |- _ ] =>
      eapply andb_prop in H; destructAll
  | [ |- (_ && _)%bool = true ] =>
      eapply andb_true_intro
  | [ H : (_ || _)%bool = true |- _ ] =>
      eapply Bool.orb_prop in H
  | [ |- (_ || _)%bool = true ] => 
      eapply Bool.orb_true_intro
  end.

Ltac do_forall_app :=
  match goal with
  | [H : forallb _ (_ ++ _) = _ |- _ ] =>
      rewrite forallb_app in H
  | [|- forallb _ (_ ++ _) = _ ] =>
      rewrite forallb_app 
  end.



Lemma surface_Inst_is_well_formed_Inst_list ins : 
  forallb surface_Inst ins = true ->
  well_formed_Inst_list ins = true. 
Proof.
  induction ins; simpl; eauto.

  intros H. do_bools.
  destruct a; simpl in *; try congruence; eauto;
  eapply forallb_surface_Inst_is_emptylin_Inst; eauto.
Qed.


Lemma well_formed_Inst_list_app_vals_l vs ins :
  values vs ->
  well_formed_Inst_list (vs ++ ins) = true ->
  well_formed_Inst_list ins = true.  
Proof.
  intros Hvs Hwf; induction vs; simpl in *; eauto.
  destruct a; inv Hvs; try contradiction; eauto.
Qed.


Lemma well_formed_Inst_list_app_vals_r vs ins :
  values vs ->
  well_formed_Inst_list ins = true ->
  well_formed_Inst_list (vs ++ ins) = true.  
Proof.
  intros Hvs Hwf; induction vs; simpl in *; eauto.
  destruct a; inv Hvs; try contradiction; eauto.
Qed.

Lemma well_formed_Inst_list_app_l ins ins' :
  well_formed_Inst_list (ins ++ ins') = true ->
  well_formed_Inst_list ins = true /\ well_formed_Inst_list ins' = true.
Proof.
  induction ins; simpl in *; eauto.
  - destruct a; intros H; eauto;
    assert (H2 := surface_Inst_is_well_formed_Inst_list _ H);
    repeat do_forall_app; repeat do_bools;
    split; eauto;    
    eapply IHins; eauto.
Qed.

Lemma well_formed_Inst_list_app_r ins ins' : 
  well_formed_Inst_list ins = true ->  
  forallb surface_Inst ins' = true ->
  well_formed_Inst_list (ins ++ ins') = true.
Proof.
  intros Hwf Hsur; induction ins; simpl in *.
  eapply surface_Inst_is_well_formed_Inst_list; eauto.
  destruct a; eauto; repeat do_forall_app; do_bools; split; eauto.
Qed.
                                        
Lemma well_formed_Inst_list_app_non_val ins ins' :
  well_formed_Inst_list (ins ++ ins') = true ->  
  existsb nonval_Inst ins = true ->
  forallb surface_Inst ins' = true.
Proof.
  intros Hwf Hex; induction ins; simpl in *; eauto.
  - congruence.
  - repeat do_bools. inv Hex.

    + destruct a; simpl in *; try congruence;
        do_forall_app; do_bools; eassumption.
    + destruct a; try now (do_forall_app; do_bools; eassumption).
      eapply IHins; eauto.
Qed.
  
Lemma well_formews_Inst_list_is_well_formed_in_context (is : list Instruction) :
  well_formed_Inst_list is = true ->
  well_formed_in_context is.
Proof.
  intros Hwf k C p' Hneq Hex Happ. revert is Hwf p' Hneq Hex Happ. 
  induction C; intros is Hwf p' Hneq Hex Happ; simpl in *.
  - rewrite <- Happ in Hwf.
    eapply well_formed_Inst_list_app_vals_l in Hwf.
    2:{ eapply values_Val. }

    eapply well_formed_Inst_list_app_non_val in Hwf; eauto.

  - rewrite <- Happ in Hwf. 
    eapply well_formed_Inst_list_app_vals_l in Hwf.
    2:{ eapply values_Val. } simpl in *.  eassumption.
Qed.


Fixpoint well_formed_Inst (i : Instruction) : bool :=
  match i with
  | Val _ 
  | Ne _
  | Unreachable
  | Nop
  | Drop
  | Select
  | Br _
  | Br_if _
  | Br_table _ _
  | Ret
  | Get_local _ _
  | Set_local _
  | Tee_local _
  | Get_global _
  | Set_global _
  | CoderefI _
  | Inst _
  | Call_indirect 
  | RecFold _
  | RecUnfold
  | Group _ _
  | Ungroup 
  | CapSplit
  | CapJoin
  | RefDemote
  | MemPack _
  | term.Call _ _
  | StructMalloc _ _
  | StructFree 
  | StructGet _
  | StructSet _ 
  | StructSwap _
  | VariantMalloc _ _ _
  | ArrayMalloc _
  | ArrayGet 
  | ArraySet
  | ArrayFree 
  | ExistPack _ _ _
  | RefSplit 
  | RefJoin 
  | Qualify _
  | Trap 
  | Malloc _ _ _
  | Free => true
              
  | Block _ _ ins => andb (forallb well_formed_Inst ins) (well_formed_Inst_list ins)
  | Loop _ ins => forallb surface_Inst ins
  | ITE _ _ ins1 ins2 =>
    andb (forallb surface_Inst ins1) (forallb surface_Inst ins2)
  | MemUnpack _ _ ins => forallb surface_Inst ins
  | VariantCase _ _ _ _ ins => forallb (forallb surface_Inst) ins
  | ExistUnpack _ _ _ _ ins => forallb surface_Inst ins
  | Label _ _ ins0 ins =>
      andb (forallb surface_Inst ins0) (andb (forallb well_formed_Inst ins) (well_formed_Inst_list ins))
  | Local _ _ _ vs ins =>
      andb (forallb well_formed_Inst ins) (well_formed_Inst_list ins)
  | CallAdm cl _ => well_formed_Closure cl
  end
with well_formed_Func (f : Func) :=
       match f with
       | Fun _ _ _ ins => forallb surface_Inst ins
       end
with well_formed_Closure (c : Closure) :=
       match c with
       | Clo _ f => well_formed_Func f
       end.

      
Lemma surface_Inst_is_well_formed_Inst i : 
  surface_Inst i = true ->
  well_formed_Inst i = true. 
Proof.
  eapply Instruction_ind' with (I := fun i => surface_Inst i = true ->
                                              well_formed_Inst i = true)
                               (C := fun _ => True) (F := fun _ => True);
    intros; simpl in *; eauto.
  - do_bools. split; eauto.
    + induction insns; simpl in *; eauto.
      inv H. repeat do_bools; split; eauto.
    + induction insns; simpl in *; eauto.
      inv H. repeat do_bools.
      destruct a; eauto.

  - congruence.
  - congruence.
  - congruence.
Qed.

Lemma forallb_surface_Inst_is_well_formed_Inst i : 
  forallb surface_Inst i = true ->
  forallb well_formed_Inst i = true. 
Proof.
  induction i; simpl; eauto. intros Hin. repeat do_bools.
  split; eauto.
  eapply surface_Inst_is_well_formed_Inst. eassumption. 
Qed. 



Ltac eauto_wf := eauto using surface_Inst_is_well_formed_Inst_list,
    forallb_surface_Inst_is_well_formed_Inst,
    surface_Inst_is_well_formed_Inst_list. 


Lemma well_formed_Inst_context k (L : context k) es :
  forallb well_formed_Inst (L |[ es ]|) = true ->
  forallb well_formed_Inst es = true.
Proof.
  induction L.
  - simpl. intros H.
    repeat (do_forall_app; do_bools).
    eassumption. 
  - simpl.
    intros H.
    repeat (do_forall_app; do_bools).
    simpl in *.
    repeat do_bools.
    eauto.
Qed.

Lemma well_formed_Inst_list_context k (L : context k) es :
  well_formed_Inst_list (L |[ es ]|) = true ->
  forallb well_formed_Inst (L |[ es ]|) = true ->
  well_formed_Inst_list es = true.
Proof.
  induction L; simpl; intros H1 H2.
  - eapply well_formed_Inst_list_app_vals_l in H1.
    eapply well_formed_Inst_list_app_l in H1. destructAll. eassumption.
    eapply values_Val.
  - repeat do_forall_app. repeat do_bools. simpl in *.
    repeat do_forall_app. repeat do_bools. simpl in *.
    eapply IHL; eassumption. 
Qed.

Lemma well_formed_Inst_list_context_hole k (L : context k) es es' :
  well_formed_Inst_list (L |[ es ]|) = true ->
  existsb nonval_Inst es = true ->
  well_formed_Inst_list es' = true ->    
  well_formed_Inst_list (L |[ es' ]|) = true.
Proof.
  induction L; simpl; intros Hwf1 Hval Hwf2.
  - eapply well_formed_Inst_list_app_vals_r. eapply values_Val.
    eapply well_formed_Inst_list_app_vals_l in Hwf1.
    eapply well_formed_Inst_list_app_non_val in Hwf1; eauto.
    now eapply well_formed_Inst_list_app_r; eauto.
    now eapply values_Val.
  - eapply well_formed_Inst_list_app_vals_r. eapply values_Val.
    eapply well_formed_Inst_list_app_vals_l in Hwf1.
    2:{ eapply values_Val. }
    simpl in *. eassumption.
Qed.
  
Lemma well_formed_Inst_context_hole k (L : context k) es es' :
  forallb well_formed_Inst (L |[ es ]|) = true ->
  existsb nonval_Inst es = true ->
  forallb well_formed_Inst es' = true ->
  well_formed_Inst_list es' = true ->    
  forallb well_formed_Inst (L |[ es' ]|) = true.
Proof.
  induction L; intros Hwf1 Hval Hwf2 Hwfl; simpl in *.
  - repeat do_forall_app. repeat do_bools. split; eauto.
    repeat do_forall_app. repeat do_bools. split; eauto.
  - repeat do_forall_app. repeat do_bools. simpl in *; split; eauto.
    repeat do_forall_app. repeat do_bools.
    split; eauto.
    repeat do_forall_app. repeat do_bools. split; eauto.
    repeat do_forall_app. repeat do_bools. split; eauto.
    eapply well_formed_Inst_list_context_hole; eauto.
Qed.

Section SurfaceTyping.

  Lemma HasTypeValue_surface : 
    forall S F v t,
      HasTypeValue S F v t ->
      surface_Value v = true ->
      M.is_empty (LinTyp S) = true.
  Proof.
    intros S F v t Htyp Ht.
    induction Htyp; try now eauto; try congruence.
  Qed.
        

  Lemma HasTypeInstruction_surface : 
    forall S C F L es taus L',
      HasTypeInstruction S C F L es taus L' ->
      forallb surface_Inst es = true ->
      M.is_empty (LinTyp S) = true.
  Proof.
    intros S C F L es taus L' H.
    induction H; intros; simpl in *; try repeat do_bools;
      destructAll; try now eauto; try congruence.

    - eapply HasTypeValue_surface; eauto.
    - eapply SplitStoreTypings_Empty'.  eassumption.
      rewrite  forallb_app in H2. 
      eapply Bool.andb_true_iff in H2. destructAll; eauto.
  Qed.

End SurfaceTyping.

Lemma well_formed_Value v :
  value v -> 
  well_formed_Inst v = true.
Proof.
  intros Hv; destruct v; simpl in *; eauto; contradiction.
Qed.

Lemma well_formed_Values vs :
  values vs ->
  forallb well_formed_Inst vs = true.
Proof.
  intros Hvs. induction vs; eauto.
  simpl. inv Hvs. do_bools. split. 
  eapply well_formed_Value. eassumption.
  now eauto.
Qed.


Lemma Forall_surface_is_well_formed_Inst es :
  forallb surface_Inst es = true ->
  forallb well_formed_Inst es = true.
Proof.
  induction es; eauto. 
  intros Hb. simpl in *.
  eapply Bool.andb_true_iff in Hb; destructAll.
  do_bools; split; eauto.
  eapply surface_Inst_is_well_formed_Inst. eassumption.
Qed. 

Definition well_formed_propgram (ins : list Instruction) : bool :=
  andb (forallb well_formed_Inst ins) (well_formed_Inst_list ins).

Definition well_formed_MInst (i : MInst) : bool :=
  match i with
  | Build_MInst func glob tab =>
      andb (forallb well_formed_Closure func)
           (forallb well_formed_Closure tab)
  end.

  

Module WFPres (M : Memory) (T : MemTyping M).

  Module Red := Reduction M T.
  
  Import M T Red T.L.

  Definition well_formed_Store (s : Store) :=
    let '(Build_Store inst minst o) := s in
    forallb well_formed_MInst inst.

  Lemma forallb_impl {A} P1 P2 (l : list A) :
    forallb P1 l = true ->
    (forall x, P1 x = true -> P2 x = true) -> 
    forallb P2 l = true.
  Proof. 
    intros Hall Himpl. induction l; simpl in *; eauto.
    repeat do_bools. split; eauto.
  Qed.

  Lemma forallb_map_impl {A} P f (l : list A) :
    forallb P l = true ->
    (forall x, P x = true -> P (f x) = true) -> 
    forallb P (map f l) = true.
  Proof. 
    intros Hall Himpl. induction l; simpl in *; eauto.
    repeat do_bools. split; eauto.
  Qed.

  Lemma Reduce_implies_nonval s vs ks es j s' vs' es' :
    Reduce s vs ks es j s' vs' es' ->
    existsb nonval_Inst es = true.
  Proof.
    intros Hred; induction Hred.
    - induction L; simpl.
      rewrite existsb_app. do_bools. right.
      rewrite existsb_app. do_bools. left. eassumption.

      rewrite existsb_app. simpl.
      do_bools. eauto.
    - reflexivity.
    - destruct H; simpl; eauto.
      + induction L; simpl.
        rewrite existsb_app. do_bools. right. reflexivity. 
        rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
    - destruct X; eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
      + rewrite existsb_app. simpl.
        do_bools. eauto.
  Qed.

  Lemma subst_inst_preserves_surface e sub :
    surface_Inst e = true ->    
    surface_Inst (subst.subst'_instruction sub e) = true.
  Proof.
    revert sub.
    eapply Instruction_ind' with (I := fun e => forall sub, 
                                           surface_Inst e = true ->    
                                           surface_Inst (subst.subst'_instruction sub e) = true)
                                 (F := fun f => True)
                                 (C := fun c => True); intros; simpl in *; eauto.    
    - destruct v; eauto.
    - induction H; eauto.
      simpl in *. repeat do_bools. split; eauto.
    - induction H; eauto.
      simpl in *. repeat do_bools. split; eauto.
    - repeat do_bools.
      split.
      + induction H; simpl in *; eauto.
        repeat do_bools; eauto. 
      + induction H0; simpl in *; eauto.
        repeat do_bools; eauto.
    - induction H; eauto.
      simpl in *. repeat do_bools. split; eauto.
    - induction H; eauto.
      simpl in *. repeat do_bools. split; eauto.
      induction H; simpl in *; eauto.
      repeat do_bools. split; eauto.
    - induction H; eauto.
      simpl in *. repeat do_bools. split; eauto.
  Qed.

  
  Lemma subst_inst_preserves_wf_list es sub :
    well_formed_Inst_list es = true ->    
    well_formed_Inst_list (map (subst.subst'_instruction sub) es) = true.
  Proof.
    revert sub. induction es; simpl; intros sub Hwf; eauto.

    destruct a; simpl in *; eauto using forallb_map_impl,
      subst_inst_preserves_surface.
  Qed.

  Lemma subst_inst_preserves_wf e :
    forall sub, 
      well_formed_Inst e = true ->    
      well_formed_Inst (subst.subst'_instruction sub e) = true.
  Proof.
    eapply Instruction_ind' with (I := fun e => forall sub, 
                                           well_formed_Inst e = true ->    
                                           well_formed_Inst (subst.subst'_instruction sub e) = true)
                                 (F := fun f =>
                                           well_formed_Func f = true ->    
                                           well_formed_Func f = true)
                                 (C := fun c =>
                                           well_formed_Closure c = true ->    
                                           well_formed_Closure c = true); intros; simpl in *; eauto using forallb_map_impl, subst_inst_preserves_surface.
    
    - repeat do_forall_app; repeat do_bools.
      split; eauto.
      + clear H1. 
        induction H; simpl in *; eauto.
        repeat do_bools. 
        split; eauto.
      + eapply subst_inst_preserves_wf_list. eassumption.

    - repeat do_forall_app; repeat do_bools.
      split; eauto.
      + induction H; simpl in *; eauto.
        repeat do_bools. 
        split; eauto.
        eapply subst_inst_preserves_surface. eassumption.        
      + induction H0; simpl in *; eauto.
        repeat do_bools. 
        split; eauto.
        eapply subst_inst_preserves_surface. eassumption. 
    - repeat do_forall_app; repeat do_bools.
      split; eauto.
      + eauto using forallb_map_impl, subst_inst_preserves_surface.
      + repeat do_bools; split; eauto.
        * clear H3. induction H0; eauto.
          simpl in *. repeat do_bools; simpl. split; eauto.
        * eapply subst_inst_preserves_wf_list. eassumption.
  Qed.       


  Lemma subst_ind_preserves_wf e sub :
    well_formed_Inst e = true ->    
    well_formed_Inst (subst.subst_indices sub e) = true.
  Proof.
    revert e.
    induction sub; intros e H; simpl; eauto.
    destruct a; simpl;
      eapply subst_inst_preserves_wf; eauto.
  Qed.

  Lemma subst_ind_preserves_wf_list' es sub :
    well_formed_Inst_list es = true ->    
    well_formed_Inst_list (map (subst.subst_index sub) es) = true.
  Proof.
    induction es; simpl; intros H; eauto.
    destruct a;
    now destruct sub; simpl; eauto using forallb_map_impl,
      subst_inst_preserves_surface.
  Qed.
  
  Lemma subst_ind_preserves_wf_list es sub :
    well_formed_Inst_list es = true ->    
    well_formed_Inst_list (map (subst.subst_indices sub) es) = true.
  Proof.
    revert es.
    induction sub; simpl; eauto; intros es.
    - rewrite map_id; eauto.
    - intros H.
      rewrite <- map_map.
      eapply subst_ind_preserves_wf_list'.
      eauto.
  Qed.
  
  Lemma Reduce_simple_preserves_wf i ins ins' :
    Reduce_simple i ins ins' ->
    forallb well_formed_Inst ins = true ->
    forallb well_formed_Inst ins' = true.
  Proof.
    pose (es := ins).  
    intros Hred Htrue; destruct Hred; simpl in *; 
      try now (repeat (do_bools; try split; eauto_wf)). 
    - do_forall_app. repeat (do_bools; simpl in *).
      split; eauto. 
      do_bools. split; eauto.
      do_forall_app. do_bools. split; eauto.
      eapply well_formed_Inst_list_app_vals_r; eauto_wf.
      
    - repeat do_forall_app. repeat (do_bools; simpl in *).
      split; eauto. do_bools.
      split; eauto. repeat (do_bools; split; eauto).
      do_bools; split; eauto.
      do_forall_app. do_bools. split; eauto.
      eapply forallb_surface_Inst_is_well_formed_Inst. eassumption.
      eapply well_formed_Inst_list_app_vals_r; eauto_wf.
                                    
   - repeat do_forall_app. repeat do_bools. split; eauto_wf. 
     eapply well_formed_Inst_context in H1.
     repeat do_forall_app; repeat do_bools; eauto.

   - eapply well_formed_Values. eapply values_Val.
     
   - repeat do_bools. split; eauto. repeat do_bools.
     split.
     + eapply forallb_map_impl.
       eapply Forall_surface_is_well_formed_Inst. eassumption.
       intros. eapply subst_inst_preserves_wf. eassumption.
     + eapply subst_inst_preserves_wf_list.
       eapply surface_Inst_is_well_formed_Inst_list. eassumption.
   - simpl in *.
     eapply well_formed_Values. eassumption.

   - simpl in *. repeat do_forall_app.
     repeat do_bools. simpl in *. split; eauto. repeat do_bools.
     split.
     + eapply forallb_map_impl.
       eapply Forall_surface_is_well_formed_Inst. eassumption.
       intros. eapply subst_ind_preserves_wf. eassumption.
     + eapply subst_ind_preserves_wf_list.
       eapply surface_Inst_is_well_formed_Inst_list. eassumption.
   Qed.   

  (* TODO move *)
  Lemma nth_error_forallb (A : Type) (l : list A) i e P :
    nth_error l i = Some e ->
    forallb P l = true ->
    P e = true.
  Proof.
    revert i; induction l; intros i Hnth Hall; simpl in *; eauto.
    - destruct i; simpl in *; try congruence; eauto.
    - do_bools. destruct i; simpl in *. now inv Hnth; eauto.
      eauto.
  Qed. 

    
  Lemma Reduce_full_preserves_wf i  s vs szs ins s' vs' ins' :
    Reduce_full i s vs szs ins s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    forallb well_formed_Inst ins' = true.
  Proof.
    intros Hred Hs Hwd; destruct Hred; simpl; eauto; repeat do_bools;
     try (split; eauto).
    - destruct cl. simpl.
      destruct f; destruct st; simpl in *.
      eapply nth_error_forallb in e; eauto.
      destruct ins. simpl in *. do_bools.
      eapply nth_error_forallb in e0; eauto. simpl in *.
      eassumption.

    - destruct cl. simpl in *.
      destruct st; destruct f; simpl in *.
      eapply nth_error_forallb in e; eauto.
      destruct ins. simpl in *. do_bools.
      eapply nth_error_forallb in e0; eauto. simpl in *.
      eassumption.

    - rewrite forallb_app in Hwd.
      rewrite forallb_app.
      do_bools.
      eapply andb_true_intro; split; eauto.
      simpl in H0.
      simpl.
      do_bools.
      eapply andb_true_intro; split; eauto.
      assert (Hes := nth_error_forallb _ _ _ _ _ e0 H0).
      eapply andb_true_intro; split; eauto.
      eapply Forall_surface_is_well_formed_Inst; eauto.
      eapply surface_Inst_is_well_formed_Inst_list; eauto.

    - simpl in *. repeat do_bools.
      eapply nth_error_forallb in H; eauto. split; eauto_wf.

    - simpl in *. repeat do_forall_app.
      repeat do_bools. simpl in *. split; eauto. repeat do_bools.
      split; eauto. repeat do_bools. split. 
      + eapply forallb_map_impl.
        eapply Forall_surface_is_well_formed_Inst. eassumption.
        intros. eapply subst_inst_preserves_wf. eassumption.
      + eapply subst_inst_preserves_wf_list.
        eapply surface_Inst_is_well_formed_Inst_list. eassumption.
    - simpl in *. repeat do_forall_app.
      repeat do_bools. simpl in *.
      split.
      + eapply forallb_map_impl.
        eapply Forall_surface_is_well_formed_Inst. eassumption.
        intros. eapply subst_inst_preserves_wf. eassumption.
      + eapply subst_inst_preserves_wf_list.
        eapply surface_Inst_is_well_formed_Inst_list. eassumption.
  Qed.

  Lemma Reduce_simple_preserves_wf_list i ins ins' :
    Reduce_simple i ins ins' ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    well_formed_Inst_list ins' = true. 
  Proof.
    intros Hred Hwf Hwf'. destruct Hred; simpl in *; eauto.
    - replace vs with (vs ++ []).
      eapply well_formed_Inst_list_app_vals_r; eauto.
      eapply app_nil_r.
    - repeat do_bools. eapply well_formed_Inst_context in H1.
      repeat do_forall_app. repeat do_bools.
      eapply well_formed_Inst_list_app_vals_r; eauto.
      eauto_wf.
    - replace (map Val vs)  with ((map Val vs)  ++ []).
      eapply well_formed_Inst_list_app_vals_r; eauto. eapply values_Val. 
      eapply app_nil_r.
    - replace vs with (vs ++ []).
      eapply well_formed_Inst_list_app_vals_r; eauto.
      eapply app_nil_r.
    - replace vs with (vs ++ []).
      eapply well_formed_Inst_list_app_vals_r; eauto.
      eapply app_nil_r.
  Qed. 
  

  Lemma Reduce_full_preserves_wf_list i s vs ks ins vs' ks' ins' :
    Reduce_full i s vs ks ins vs' ks' ins' ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    well_formed_Inst_list ins' = true. 
  Proof.
    intros Hred Hall Hwf.
    induction Hred; simpl in *; eauto.
    - eapply well_formed_Inst_list_app_vals_l in Hwf; eauto.
      eapply well_formed_Inst_list_app_vals_r; eauto.
    - repeat do_bools. split; eauto.
      eapply nth_error_forallb; eauto.
    - eapply well_formed_Inst_list_app_vals_l in Hwf; eauto.
      eapply well_formed_Inst_list_app_vals_r; eauto.
    - subst. repeat do_bools. split; eauto.
      eapply forallb_map_impl. eassumption. 
      intros. eapply subst_inst_preserves_surface. eassumption.
  Qed.
  
  Lemma well_formed_Store_update_MInst st inst:
    well_formed_Store st = true ->
    forallb well_formed_MInst inst = true ->
    well_formed_Store (update_inst st inst) = true. 
  Proof.
    intros Hwf Hwf'.
    destruct st; simpl in *; eauto.
  Qed.
  
  (* TODO move *) 
  Lemma In_set_nth A l i (x z: A) :
    List.In z (set_nth l i x) ->
    z = x \/ List.In z l.
  Proof.
    revert i; induction l; simpl; intros i Hin; eauto.

    destruct i; simpl in *; eauto.

    - inv Hin; eauto.

    - inv Hin; eauto.
      
      eapply IHl in H. inv H; eauto.
  Qed.
  

  Lemma forallb_set_nth A p l (x : A) i :
    forallb p l = true ->
    p x = true ->
    forallb p (set_nth l i x) = true.
  Proof.
    intros Hall Hp.
    eapply forallb_forall.
    intros y Hin.
    eapply In_set_nth in Hin. inv Hin; eauto.
    
    eapply forallb_forall in Hall; eauto.
  Qed. 

  Lemma forallb_In A p l (x : A) :    
    forallb p l = true ->
    List.In x l ->
    p x = true.
  Proof.
    intros Hall Hin.
    induction l; eauto.

    simpl in *.
    eapply Bool.andb_true_iff in Hall; destructAll;
      inv Hin; eauto.
  Qed.
  
    
  Lemma well_formed_MInst_update_globals inst gs :
    well_formed_MInst inst = true ->
    well_formed_MInst (update_globals inst gs)= true.
  Proof.                     
    destruct inst; eauto.
  Qed.

  Lemma well_formed_Store_update_outset l st hv1 hv2 :
    well_formed_Store st = true ->
    well_formed_Store (update_out_set l st hv1 hv2) = true.
  Proof.
    destruct st; simpl.
    unfold update_out_set.
    destruct (L.has_urn_ptr_HeapValue hv2); eauto.
    destruct (L.has_urn_ptr_HeapValue hv1); eauto.
    destruct (L.has_urn_ptr_HeapValue hv1); eauto.
  Qed.
  
  Lemma well_formed_Store_remove_outset l st :
    well_formed_Store st = true ->
    well_formed_Store (remove_out_set l st) = true.
  Proof.
    destruct st; simpl; eauto.
  Qed.

  Lemma well_formed_Store_add_outset l st hv :
    well_formed_Store st = true ->
    well_formed_Store (add_out_set l st hv) = true.
  Proof.
    destruct st; simpl.
    unfold add_out_set.
    destruct (L.has_urn_ptr_HeapValue hv); eauto.
  Qed.


  Lemma well_formed_Store_update_mem st st' l q hv :
    well_formed_Store st = true ->
    update_mem st l q hv = Some st' ->
    well_formed_Store st' = true.
  Proof.
    intros Hwf Hupd.
    destruct st; unfold update_mem in *; simpl in *.

    destruct (set l q meminst0 hv); try congruence.
    inv Hupd. eassumption.
  Qed.
        

  Lemma well_formed_Store_free_mem_range st st' l :
    well_formed_Store st = true ->
    free_mem_range st l Linear = Some st' ->
    well_formed_Store st' = true.
  Proof.
    intros Hwf Hupd.
    destruct st; unfold free_mem_range in *; simpl in *.

    destruct (free l Linear meminst0); try congruence.
    inv Hupd. eassumption.
  Qed.

  Lemma well_formed_Store_alloc_mem_range st q sz H hv st' l :
    well_formed_Store st = true ->
    alloc_mem_range st q sz H hv = Some (l, st') ->
    well_formed_Store st' = true.
  Proof.
    intros Hwf Hall.
    destruct st; unfold alloc_mem_range in *; simpl in *.
    
    destruct (alloc meminst0 q (N.of_nat (to_size sz H)) hv); try congruence.
    destruct p. destruct p. inv Hall.
    simpl. eassumption.
  Qed.

  
  Lemma Reduce_full_preserves_wf_store i  s vs szs ins s' vs' ins' :
    Reduce_full i s vs szs ins s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    well_formed_Store s' = true.
  Proof.
    intros Hred Hs Htrue; destruct Hred; simpl; eauto.
    - eapply well_formed_Store_update_MInst; eauto.
      subst.
      destruct st; simpl in *.

      eapply forallb_set_nth; eauto.

      eapply well_formed_MInst_update_globals.
      eapply forallb_In; eauto.
      eapply nth_error_In; eauto.

    - destruct (qualconstr_eq_dec m Linear) eqn:Heq; subst; eauto.
      + eapply well_formed_Store_update_outset.
        eapply well_formed_Store_update_mem; eauto.
      + eapply well_formed_Store_update_mem; eauto.

    - destruct (qualconstr_eq_dec m Linear) eqn:Heq; subst; eauto.
      + eapply well_formed_Store_update_outset.
        eapply well_formed_Store_update_mem; eauto.
      + eapply well_formed_Store_update_mem; eauto.

    - eapply well_formed_Store_update_mem; eauto.
        
    - destruct (qualconstr_eq_dec m Linear) eqn:Heq; subst; eauto.
      + eapply well_formed_Store_update_outset.
        eapply well_formed_Store_update_mem; eauto.
      + eapply well_formed_Store_update_mem; eauto.

    - eapply well_formed_Store_update_mem; eauto.

    - subst. eapply well_formed_Store_remove_outset.
      eapply well_formed_Store_free_mem_range; eauto.

    - destruct (qualconstr_eq_dec q Linear) eqn:Heq; subst; eauto.
      + eapply well_formed_Store_add_outset.
        eapply well_formed_Store_alloc_mem_range; eauto.
      + eapply well_formed_Store_alloc_mem_range; eauto.
  Qed.


  Lemma Reduce_preserves_wf_Inst_list i s vs szs ins s' vs' ins' :
    Reduce s vs szs ins i s' vs' ins' ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    well_formed_Inst_list ins' = true. 
  Proof.
    intros Hred Hwf1 Hwf2. induction Hred; simpl in *; eauto.
    - eapply well_formed_Inst_list_context_hole. eassumption.
      eapply Reduce_implies_nonval. eassumption.
      eapply IHHred.
      eapply well_formed_Inst_context.
      eassumption.      
      eapply well_formed_Inst_list_context.
      eassumption. eassumption.
    - eapply Reduce_simple_preserves_wf_list; eauto.
    - eapply Reduce_full_preserves_wf_list. eassumption.
      eassumption. eassumption.
  Qed.

  Lemma Reduce_preserves_wf_Inst i s vs szs ins s' vs' ins' :
    Reduce s vs szs ins i s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    forallb well_formed_Inst ins'= true.
  Proof.
    intros Hred Hwf1 Hwf2 Hwfl. induction Hred.
    - eapply well_formed_Inst_context_hole. eassumption.
      eapply Reduce_implies_nonval; eauto.
      eapply IHHred. eassumption.
      eapply well_formed_Inst_context. eassumption.
      now eapply well_formed_Inst_list_context; eauto.
      eapply Reduce_preserves_wf_Inst_list. eassumption.
      eapply well_formed_Inst_context. eassumption.
      now eapply well_formed_Inst_list_context; eauto.    
    - simpl in *. repeat do_bools. split; eauto. do_bools. split; eauto.
      eapply Reduce_preserves_wf_Inst_list; eauto.
    - eapply Reduce_simple_preserves_wf; eauto.
    - eapply Reduce_full_preserves_wf; eauto.
  Qed.

  Lemma Reduce_preserves_wf_Store i s vs szs ins s' vs' ins' :
    Reduce s vs szs ins i s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    well_formed_Store s' = true.
  Proof.
    intros Hred Hwf1 Hwfl. induction Hred; eauto.
    - eapply IHHred; eauto.
      eapply well_formed_Inst_context. eassumption.
    - simpl in *. repeat do_bools. eapply IHHred. eassumption.
      eassumption.
    - eapply Reduce_full_preserves_wf_store; eauto.
  Qed.
  
  Lemma Reduce_GC_preserves_wf_Inst i s vs szs ins s' vs' ins' :
    Reduce_GC s vs szs ins i s' vs' ins' ->
    well_formed_Store s = true  ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    forallb well_formed_Inst ins' = true.
  Proof.
    intros Hred Hwf1 Hwf2 Hwf3. induction Hred.
    - eapply Reduce_preserves_wf_Inst; eauto.
    - eassumption.
  Qed.

  Lemma Reduce_GC_preserves_wf_Store i s vs szs ins s' vs' ins' :
    Reduce_GC s vs szs ins i s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    well_formed_Store s' = true.
  Proof.
    intros Hred Hwf1 Hwf2. induction Hred.
    - eapply Reduce_preserves_wf_Store; eauto.
    - inv H.
      unfold s'0, well_formed_Store  in *. simpl in *.
      destruct s. eassumption.
  Qed.


  Lemma Reduce_GC_preserves_wf_Inst_list i s vs szs ins s' vs' ins' :
    Reduce_GC s vs szs ins i s' vs' ins' ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    well_formed_Inst_list ins' = true. 
  Proof.
    intros Hred Hwf1 Hwf2. induction Hred.
    - eapply Reduce_preserves_wf_Inst_list; eauto.
    - eassumption.
  Qed.

  Corollary Reduce_GC_preserves_wf_top i  s vs szs ins s' vs' ins' :
    Reduce_GC s vs szs ins i s' vs' ins' ->
    well_formed_Store s = true ->
    forallb well_formed_Inst ins = true ->
    well_formed_Inst_list ins = true ->
    well_formed_Store s' = true /\
    forallb well_formed_Inst ins' = true /\
    well_formed_Inst_list ins' = true. 
  Proof.
    intros Hred Hwf1 Hwf2 Hwf3. 
    split; [ | split ].
    + eapply Reduce_GC_preserves_wf_Store; eauto.
    + eapply Reduce_GC_preserves_wf_Inst; eauto.
    + eapply Reduce_GC_preserves_wf_Inst_list; eauto.
  Qed.
   
End WFPres. 
