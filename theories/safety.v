From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive Sets.Ensembles micromega.Lia Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Instance OptionMonad : Monad option :=
  { ret := @Some;
    bind :=
      fun t u m f =>
        match m with
        | Some x => f x
        | None => None
        end
  }.


Module M := PositiveMap.

Require Import RWasm.tactics RWasm.term RWasm.EnsembleUtil RWasm.locations RWasm.memory RWasm.reduction RWasm.typing RWasm.list_util RWasm.typing_util RWasm.misc_util RWasm.splitting RWasm.progress RWasm.surface RWasm.preservation_GC RWasm.preservation RWasm.debruijn RWasm.subst RWasm.preservation_full.

Module Safety (M : Memory) (T : MemTyping M).
  Module Progress := Progress M T.
  Definition size_t := size.
  Module WFPres := WFPres M T.
  Module PreservationGC := PreservationGC M T.
  Module Preservation := Preservation M T.
  Module PreservationFull := PreservationFull M T.
  Module Location := Location M.
  Import M Progress T Location WFPres Preservation Preservation.Red PreservationGC PreservationFull.
  Import Utils.

  Inductive Red_Star : nat -> Store -> list Value -> list nat -> list Instruction -> nat -> Store -> list Value -> list Instruction -> Prop :=
  | RRefl : forall s vs szs es i, Red_Star 0 s vs szs es i s vs es
  | RStep : forall s vs szs es i s' vs' es' s'' vs'' es'' n,
      Reduce_GC s vs szs es i s' vs' es' -> Red_Star n s' vs' szs es' i s'' vs'' es'' -> Red_Star (n + 1) s vs szs es i s'' vs'' es''.

  Definition update_unr (U : HeapTyping ) (S : StoreTyping) : StoreTyping :=
    {| InstTyp := InstTyp S; LinTyp := LinTyp S; UnrTyp := U |}.

  Lemma update_unr_empty_lintyp_swap U S :
    update_unr U (empty_LinTyp S) = empty_LinTyp (update_unr U S).
  Proof.
    destruct S; unfold update_unr; simpl; congruence.
  Qed.

 
  Lemma reduce_full_preserves_inst n s vs szs es s' vs' es' :
    Reduce_full n s vs szs es s' vs' es' ->
    Forall2 (fun m1 m2 => term.func m1 = term.func m2 /\ tab m1 = tab m2) (inst s) (inst s').
  Proof.
    intros.
    invert X; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s. simpl.
      destruct i. simpl in H. simpl.
      clear - H.
      revert n j v func glob tab H.
      induction inst0; simpl; eauto; intros.
      assert (n = 0 \/ n <> 0) by (destruct n; eauto).
      destruct H0.
      + subst.
        simpl.
        simpl in H.
        invert H.
        eapply Forall2_cons; eauto.
        clear. induction inst0; eauto.
      + destruct n.
        exfalso; eapply H0; lia.
        simpl.
        eapply Forall2_cons; eauto.
        simpl in H.
        assert (Hn : n - 0 = n) by lia.
        rewrite Hn.
        exact (IHinst0 n j v func glob tab H).
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct (qualconstr_eq_dec m Linear); subst.
      + unfold update_mem in H2.
        destruct (set l Linear (meminst s) (Struct (set_nth vis j v))); try discriminate.
        invert H2.
        unfold update_out_set.
        destruct (has_urn_ptr_HeapValue (Struct (set_nth vis j v))); simpl;
        destruct (existsb L.has_urn_ptr_Value (set_nth vis j v)); simpl;
        destruct (existsb L.has_urn_ptr_Value vis); simpl;
        destruct s; simpl; clear; induction inst0; eauto.
      + unfold update_mem in H2.
        destruct (set l m (meminst s) (Struct (set_nth vis j v))); try discriminate.
        invert H2.
        simpl.
        destruct s. simpl. clear. induction inst0; eauto.
    - destruct (qualconstr_eq_dec m Linear); subst.
      + unfold update_mem in H2.
        destruct (set l Linear (meminst s) (Struct (set_nth vis j v))); try discriminate.
        invert H2.
        unfold update_out_set.
        destruct (has_urn_ptr_HeapValue (Struct (set_nth vis j v))); simpl;
        destruct (existsb L.has_urn_ptr_Value (set_nth vis j v)); simpl;
        destruct (existsb L.has_urn_ptr_Value vis); simpl;
        destruct s; simpl; clear; induction inst0; eauto.
      + unfold update_mem in H2.
        destruct (set l m (meminst s) (Struct (set_nth vis j v))); try discriminate.
        invert H2.
        simpl.
        destruct s. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - unfold update_mem in H0.
      destruct (set l Linear (meminst s) (Array 0 [])); try discriminate.
      invert H0.
      simpl.
      destruct s. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct (qualconstr_eq_dec m Linear); subst.
      + unfold update_mem in H2.
        destruct (set l Linear (meminst s) (Array i (set_nth vs0 j v))); try discriminate.
        invert H2.
        unfold update_out_set.
        destruct (has_urn_ptr_HeapValue (Array i (set_nth vs0 j v))); simpl;
        destruct (existsb L.has_urn_ptr_Value (set_nth vs0 j v)); simpl;
        destruct (existsb L.has_urn_ptr_Value vs0); simpl;
        destruct s; simpl; clear; induction inst0; eauto.
      + unfold update_mem in H2.
        destruct (set l m (meminst s) (Array i (set_nth vs0 j v))); try discriminate.
        invert H2.
        simpl.
        destruct s. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
    - unfold update_mem in H0.
      destruct (set l Linear (meminst s) (Array 0 [])); try discriminate.
      invert H0.
      simpl.
      destruct s. simpl. clear. induction inst0; eauto.
    - unfold free_mem_range in H.
      destruct (free l Linear (meminst s)); try discriminate.
      invert H.
      simpl.
      destruct s. simpl. clear. induction inst0; eauto.
    - destruct (qualconstr_eq_dec q Linear); subst.
      + unfold alloc_mem_range in H0.
        destruct (alloc (meminst s) Linear (N.of_nat (to_size sz H)) hv); try discriminate.
        destruct p.
        destruct p.
        invert H0.
        unfold add_out_set.
        destruct (L.has_urn_ptr_HeapValue hv); simpl;
        destruct s; simpl; clear; induction inst0; eauto.
      + unfold alloc_mem_range in H0.
        destruct (alloc (meminst s) q (N.of_nat (to_size sz H)) hv); try discriminate.
        destruct p.
        destruct p.
        invert H0.
        simpl.
        destruct s; simpl; clear; induction inst0; eauto.
    - destruct s'. simpl. clear. induction inst0; eauto.
  Qed.

  Lemma reduce_preserves_inst n s vs szs es s' vs' es' :
    Reduce s vs szs es n s' vs' es' ->
    Forall2 (fun m1 m2 => term.func m1 = term.func m2 /\ tab m1 = tab m2) (inst s) (inst s').
  Proof.
    intros.
    induction H.
    - exact IHReduce.
    - exact IHReduce.
    - destruct s1; simpl; clear; induction inst0; eauto.
    - eapply reduce_full_preserves_inst.
      exact X.
  Qed.



  Lemma well_formed_Inst_list_ctx i (L : context i) es1 :
    well_formed_Inst_list (L |[ es1 ]|) = true ->
    forallb well_formed_Inst (L |[ es1 ]|) = true ->
    well_formed_Inst_list es1 = true.
  Proof.
    revert L es1.
    induction i; intros.
    - clear H0.
      assert (Hn : 0 = 0) by congruence. revert L Hn H. generalize 0 at 2.
      intros.
      assert (Hn' : n = 0) by eauto.
      revert L Hn H. generalize 0.
      intros.
      destruct L; try lia.
      simpl in H.
      induction l.
      + simpl in H.
        eapply well_formed_Inst_list_app_l in H.
        destruct H.
        eassumption.
      + simpl in H.
        eapply IHl in H.
        eassumption.
    - assert (Hn : (Datatypes.S i) = (Datatypes.S i)) by congruence. revert L Hn H H0. generalize (Datatypes.S i) at 2.
      intros.
      assert (Hn' : n = Datatypes.S i) by eauto.
      revert L Hn H H0. generalize (Datatypes.S i).
      intros.
      destruct L; try lia.
      assert (k = i) by lia.
      subst.
      assert (IH := IHi L es1).
      clear - H IH H0.
      simpl in H.
      induction l.
      + simpl in H0.
        do 3 do_bools.
        eapply IH; eauto.
      + simpl in H0.
        simpl in H.
        eapply IHl; eauto.
  Qed.

  Lemma well_formed_Inst_ctx i (L : context i) es1 :
    forallb well_formed_Inst (L |[ es1 ]|) = true ->
    forallb well_formed_Inst es1 = true.
  Proof.
    revert L es1.
    induction i; intros.
    - assert (Hn : 0 = 0) by congruence. revert L Hn H. generalize 0 at 2.
      intros.
      assert (Hn' : n = 0) by eauto.
      revert L Hn H. generalize 0.
      intros.
      destruct L; try lia.
      simpl in H.
      induction l; simpl in H.
      rewrite forallb_app in H.
      do_bools. eauto.
      eapply IHl in H.
      eassumption.
    - assert (Hn : (Datatypes.S i) = (Datatypes.S i)) by congruence. revert L Hn H. generalize (Datatypes.S i) at 2.
      intros.
      assert (Hn' : n = Datatypes.S i) by eauto.
      revert L Hn H. generalize (Datatypes.S i).
      intros.
      destruct L; try lia.
      assert (k = i) by lia.
      subst.
      simpl in H.
      induction l.
      + simpl in H.
        do 3 do_bools.
        eapply IHi in H1.
        eassumption.
      + simpl in H.
        eapply IHl in H.
        eassumption.
  Qed.

  Lemma Red_Star_nil n s vs szs i s' vs' es' : Red_Star n s vs szs [] i s' vs' es' -> es' = [].
  Proof.
    revert s vs szs i s' vs' es'.
    induction n; intros; try (inv H; eauto; lia).
    inv H.
    inv H1; try (eapply IHn; assert (Hn : n0 = n) by lia; rewrite Hn in H2; exact H2).
    exfalso.
    clear - H.
    revert H.
    assert (Hrem : ([] : list Instruction) = []) by eauto.
    revert Hrem.
    generalize ([] : list Instruction) at 2 4.
    intros.
    revert Hrem.
    induction H; intros.
    - destruct L.
      + simpl in Hrem.
        eapply IHReduce.
        destruct l; destruct es1; destruct l0; simpl in Hrem; eauto; discriminate.
      + simpl in Hrem. eapply app_eq_nil in Hrem.
        destruct Hrem.
        discriminate.
    - discriminate.
    - subst.
      inv H; eauto; try (eapply app_eq_nil in H0; destruct H0; discriminate).
      + destruct L; simpl in H1; eapply app_eq_nil in H1; destruct H1; discriminate.
      + eapply app_eq_nil in H1; destruct H1; discriminate.
    - subst.
      inv X; eapply app_eq_nil in H; destructAll; discriminate.
  Qed.

  (* Lemmas for label case *)
  Lemma values_same_local_context S C F L vs taus L':
    HasTypeInstruction S C F L (map term.Val vs) (Arrow [] taus) L' ->
    LCEffEqual (size F) L L'.
  Proof.
    intros.
    eapply HasTypeInstruction_values_locals; eauto.
    unfold values.
    rewrite Forall_forall.
    intros.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    unfold value; auto.
  Qed.

  Lemma HasTypeInstruction_val_app S C F L vs es taus L':
    HasTypeInstruction S C F L (map term.Val vs ++ es) (Arrow [] taus) L' ->
    exists tausvs S_vs S_es,
      HasTypeInstruction S_vs C F L (map term.Val vs) (Arrow [] tausvs) L /\
      HasTypeInstruction S_es C F L es (Arrow tausvs taus) L' /\
      SplitStoreTypings [S_vs; S_es] S.
  Proof.
    revert S C F L vs taus L'.
    eapply rev_ind with (l := es); intros.
    - rewrite app_nil_r in H.
      exists taus. exists S. exists (empty_LinTyp S).
      split; [| split]; eauto.
      + simpl.
        eapply ChangeEndLocalTyp; [ | | eauto ].
        ++ eapply HasTypeInstruction_FirstLocalValid; eauto.
        ++ apply LCEffEqual_sym.
           eapply values_same_local_context; eauto.
      + specialize (HasTypeInstruction_QualValid H).
        intros.
        show_tlvs H; eapply values_same_local_context in H.
        eapply ChangeEndLocalTyp; [ eauto | eauto | ].
        eapply HasTypeInstruction_empty_list; auto.
        destruct S; simpl; eauto.
      + eapply SplitStoreTypings_EmptyHeapTyping_r.
    - rewrite app_assoc in H0.
      edestruct composition_typing_single. eassumption. destructAll.
      assert (x1 = []).
      { clear - H1. destruct x0; destruct x1; eauto. simpl in H1. discriminate. }
      subst.
      eapply H in H4.
      destruct H4 as [tausvs [S_vs [S_es [H20 [H21 H22]]]]].
      destruct (SplitStoreTypings_assoc _ _ _ _ _ H22 H6) as [S' [H23 H24]].
      exists tausvs. exists S_vs. exists S'.
      split; [| split]; eauto. 
      eapply ConsTyp; eauto.
      assert (x0 = []).
      { clear - H1. rewrite app_nil_r in H1. eauto. }
      subst.
      rewrite app_nil_l.
      eassumption.
  Qed.

  Lemma HasTypeInstruction_values_empty_in S C F L vs t1 t2 L':
    HasTypeInstruction S C F L (map term.Val vs) (Arrow t1 t2) L' ->
    exists tvs,
      t2 = t1 ++ tvs /\ HasTypeInstruction S C F L (map term.Val vs) (Arrow [] tvs) L'.
  Proof.
    revert S C F L t1 t2 L'.
    eapply rev_ind with (l := vs); simpl; intros.
    - specialize (HasTypeInstruction_QualValid H).
      intros.
      show_tlvs H; eapply Empty_HasTypeInstruction in H.
      destructAll.
      exists [].
      split; eauto.
      rewrite app_nil_r. congruence.
    - rewrite map_app. rewrite map_app in H0. simpl. simpl in H0.
      edestruct composition_typing_single in H0. eassumption. destructAll.
      eapply H in H4.
      destructAll.
      specialize (HasTypeInstruction_QualValid H5).
      intros.
      show_tlvs H5; eapply Val_HasTypeInstruction in H5.
      destructAll.
      exists (x7 ++ [x3]).
      split.
      + do 3 rewrite app_assoc.
        congruence.
      + eapply ConsTyp.
        exact H6.
        exact H2.
        assert (x7 = x7 ++ []) by (rewrite app_nil_r; eauto).
        rewrite H5 at 1.
        eapply (FrameTyp _ _ _ _ _ Linear); eauto.
        * eapply Forall_trivial. intros. destruct x2. eapply QualLeq_Top.
        * eapply QualLeq_Top.
        * eapply ChangeEndLocalTyp.
          { destruct F; eapply LocalCtxValid_Function_Ctx; eauto. }
          { destruct F; subst; simpl in *; eauto. }
          eapply ValTyp.
          2:{ destruct F; subst; simpl in *; solve_lcvs. }
          2:{ destruct F; simpl; rewrite get_set_hd; econstructor; eauto. }
          eapply HasTypeValue_Function_Ctx; [| | | | exact H10]; destruct F; eauto.
        * econstructor; eauto.
        * solve_tvs.
  Qed.

  Lemma HasTypeInstruction_val_Function_Ctx F F' S C L L' vs tauvs :
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    HasTypeInstruction S C F L (map term.Val vs) (Arrow [] tauvs) L' ->
    QualValid (qual F') (get_hd (linear F')) ->
    HasTypeInstruction S C F' L (map term.Val vs) (Arrow [] tauvs) L'.
  Proof.
    revert F F' S C L L' tauvs.
    eapply rev_ind with (l := vs); simpl; intros.
    - show_tlvs H3; eapply Empty_HasTypeInstruction in H3.
      destructAll.
      eapply ChangeEndLocalTyp.
      { eapply LocalCtxValid_Function_Ctx; eauto. }
      { destruct F; destruct F'; subst; simpl in *; eauto.
        match goal with
        | [ H : _ = ?A |- _ ?A _ _ ] => rewrite <-H; eauto
        end. }
      eapply EmptyTyp; eauto.
      solve_lcvs.
    - rewrite map_app. rewrite map_app in H4. simpl. simpl in H4.
      edestruct composition_typing_single in H4. eassumption. destructAll.
      assert (Hd : [] = x1) by (destruct x0; destruct x1; eauto; discriminate).
      destruct Hd.
      eapply ConsTyp.
      exact H11.
      eapply H; eauto.
      assert (Hd : [] = x0) by (destruct x0; eauto; discriminate).
      destruct Hd.
      rewrite app_nil_l.
      show_tlvs H10; eapply Val_HasTypeInstruction in H10.
      destructAll.
      assert (Hrw : x3 = x3 ++ []) by (rewrite app_nil_r; eauto).
      rewrite Hrw.
      rewrite<- app_assoc.
      eapply (FrameTyp _ _ _ _ _ Linear); eauto.
      + eapply Forall_trivial. intros. destruct x1. eapply QualLeq_Top.
      + eapply QualLeq_Top.
      + rewrite app_nil_l.
        eapply HasTypeValue_Function_Ctx in H15.
        { eapply ChangeEndLocalTyp.
          { destruct F; destruct F'; simpl in *; subst; eapply LocalCtxValid_Function_Ctx; eauto. }
          { destruct F; destruct F'; subst; simpl in *; eauto.
            match goal with
            | [ H : _ = ?A |- _ ?A _ _ ] => rewrite <-H; eauto
            end. }
          eapply ValTyp; eauto.
          - destruct F; destruct F'; subst; simpl in *; solve_lcvs.
          - destruct F'; simpl; rewrite get_set_hd; econstructor; eauto. }
        all: destruct F; destruct F'; eauto.
      + econstructor; eauto.
      + destruct F; destruct F'; subst; simpl in *; solve_tvs.
  Qed.

  Lemma HasTypeInstruction_val_app2 S C F L vs es taus L' tausin:
    HasTypeInstruction S C F L (map term.Val vs ++ es) (Arrow tausin taus) L' ->
    exists tausvs S_vs S_es,
      HasTypeInstruction S_vs C F L (map term.Val vs) (Arrow [] tausvs) L /\
      HasTypeInstruction S_es C F L es (Arrow (tausin ++ tausvs) taus) L' /\
      SplitStoreTypings [S_vs; S_es] S.
  Proof.
    revert S C F L vs taus L' tausin.
    eapply rev_ind with (l := es); simpl; intros.
    - rewrite app_nil_r in H.
      show_tlvs H; eapply HasTypeInstruction_values_empty_in in H.
      destructAll.
      assert ((map term.Val vs) = (map term.Val vs) ++ []) by (rewrite app_nil_r; eauto).
      rewrite H in H4.
      eapply HasTypeInstruction_val_app in H4.
      destructAll.
      do 3 eexists.
      split; eauto.
      split; eauto.
      eapply Empty_HasTypeInstruction in H5.
      destructAll.
      assert (tausin ++ x = tausin ++ x ++ []) by (rewrite app_nil_r; eauto).
      rewrite H5.
      rewrite app_assoc.
      eapply (FrameTyp _ _ _ _ _ Linear); eauto.
      + eapply Forall_trivial. intros. destruct x0. eapply QualLeq_Top.
      + eapply QualLeq_Top.
      + eapply ChangeEndLocalTyp.
        { destruct F; eapply LocalCtxValid_Function_Ctx; eauto. }
        { destruct F; subst; simpl in *; eauto. }
        eapply HasTypeInstruction_empty_list; auto.
        ++ destruct F; subst; simpl in *; solve_lcvs.
        ++ destruct F; simpl; rewrite get_set_hd; econstructor; eauto.
      + eapply HasTypeInstruction_QualValid; eauto.
      + econstructor; eauto.
    - rewrite app_assoc in H0.
      edestruct composition_typing_single_strong in H0. eassumption.
      destructAll.
      simpl in *.
      destructAll.
      eapply H in H1.
      destructAll.
      assert (H20 := SplitStoreTypings_assoc _ _ _ _ _ H10 H7).
      destruct H20 as [x11 [H100 H101]].
      exists x8. exists x9. exists x11.
      split; [eapply HasTypeInstruction_val_Function_Ctx; [| | | | eassumption|]; destruct F; eauto |].
      split; eauto.
      rewrite<- app_assoc.
      eapply FrameTyp; eauto.
  Qed.

  Lemma well_formed_Inst_list_drop_middle es1 es2 l:
    well_formed_Inst_list (es1 ++ l ++ es2) = true ->
    well_formed_Inst_list (es1 ++ es2) = true.
  Proof.
    revert es2 l.
    induction es1; simpl; intros; eauto.
    - eapply well_formed_Inst_list_app_l in H.
      destruct H.
      eassumption.
    - destruct a; try (rewrite forallb_app; rewrite forallb_app in H; do_bools; rewrite forallb_app in H0; do_bools; rewrite H; rewrite H1; simpl; congruence).
      eapply IHes1; eassumption.
  Qed.

  Lemma after_reduction_is_surface es1 es1' es2 s1 s2 vs1 vs2 szs addr:
    Reduce s1 vs1 szs es1 addr s2 vs2 es1' ->
    well_formed_Inst_list (es1 ++ es2) = true ->
    forallb surface_Inst es2 = true.
  Proof.
    intros.
    revert H0.
    induction H; intros; eauto.
    - destruct k.
      + assert (Hn : 0 = 0) by congruence. revert L Hn H0. generalize 0 at 2.
        intros.
        assert (Hn' : n = 0) by eauto.
        revert L Hn H0. generalize 0.
        intros.
        destruct L; try lia.
        clear Hn Hn'.
        simpl in *.
        eapply IHReduce.
        rewrite<- app_assoc in H0.
        eapply well_formed_Inst_list_app_vals_l in H0; [| eapply values_val_map].
        rewrite<- app_assoc in H0.
        eapply well_formed_Inst_list_drop_middle; eassumption.

      + assert (Hn : (Datatypes.S k) = (Datatypes.S k)) by congruence. revert L Hn H0. generalize (Datatypes.S k) at 2.
        intros.
        assert (Hn' : n = (Datatypes.S k)) by eauto.
        revert L Hn H0. generalize (Datatypes.S k).
        intros.
        destruct L; try lia.
        assert (k = k0) by lia.
        subst.
        simpl in H0.
        rewrite<- app_assoc in H0.
        eapply well_formed_Inst_list_app_vals_l in H0; [| eapply values_val_map].
        simpl in H0.
        rewrite forallb_app in H0.
        do_bools.
        eassumption.
    - destruct H; eauto; try (rewrite<- app_assoc in H0; eapply well_formed_Inst_list_app_vals_l in H0; eauto); [| eapply values_val_map].
      assert (Hn : 0 = 0) by congruence. revert L Hn H0. generalize 0 at 2.
      intros.
      assert (Hn' : n = 0) by eauto.
      revert L Hn H0. generalize 0.
      intros.
      destruct L; try lia.
      clear Hn Hn'.
      rewrite<- ctx_zero_unfold in H0.
      simpl in H0.
      rewrite<- app_assoc in H0.
      eapply well_formed_Inst_list_app_vals_l in H0; [| eapply values_val_map].
      simpl in H0.
      rewrite forallb_app in H0.
      do_bools.
      eassumption.
    -  destruct X; eauto.
      + clear - H0.
        revert H0.
        induction vs; eauto; intros.
        destruct a; try (simpl in H0; rewrite forallb_app in H0; do_bools; eassumption).
        simpl in H0.
        eapply IHvs in H0.
        eassumption.
      + clear - H0.
        revert H0.
        induction vs; eauto; intros.
        destruct a; try (simpl in H0; rewrite forallb_app in H0; do_bools; eassumption).
        simpl in H0.
        eapply IHvs in H0.
        eassumption.
  Qed.

  Lemma split_surface_typing S C F es1 es2 taus1 taus3 L L'':
    HasTypeInstruction S C F L (es1 ++ es2) (Arrow taus1 taus3) L'' ->
    forallb surface_Inst es2 = true ->
    exists taus2 L',
           HasTypeInstruction S C F L es1 (Arrow taus1 taus2) L' /\
           HasTypeInstruction (empty_LinTyp S) C F L' es2 (Arrow taus2 taus3) L''.
  Proof.
    intros.
    edestruct composition_typing in H. eassumption. destructAll.
    simpl in *; destructAll.
    exists (x ++ x2). exists x3.
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ ?ES _ _,
        H' : forallb surface_Inst ?ES = true |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 := HasTypeInstruction_surface _ _ _ _ _ _ _ H H')
    end.
    match goal with
    | [ H : SplitStoreTypings _ _,
        H' : M.is_empty (LinTyp _) = true |- _ ] =>
      eapply SplitStoreTypings_comm in H;
      let H0 := fresh "H" in
      assert (H0 := SplitStoreTypings_Empty_eq _ _ _ H H')
    end.
    split.
    - eapply Proper_HasTypeInstruction; eauto.
      eapply StoreTyping_Equiv.
      eassumption.
    - eapply Proper_HasTypeInstruction; eauto.
      destruct S.
      unfold StoreTyping_eq.
      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] => invert H
      end.
      match goal with
      | [ H : Forall _ [_; _] |- _ ] => invert H
      end.
      match goal with
      | [ H : _ /\ _ |- _ ] => destruct H
      end.
      simpl in *.
      split; eauto.
      split; eauto.
      eapply map_util.eq_map_equiv.
      eapply eq_map_is_empty.
      eassumption.
  Qed.

  Lemma ignore_label_vs S_stack0 S_stack1 S_stack Ss Sp S_ignore :
    SplitStoreTypings [S_stack0;  S_stack1] S_stack ->
    SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp ->
    SplitStoreTypings (S_stack1 :: (S_ignore ++ [S_stack0]) ++ Ss) Sp.
  Proof.
    intros.
    eapply SplitStoreTypings_comm in H.
    assert (H1 := SplitStoreTypings_merge' _ _ _ _ H H0).
    eapply SplitStoreTypings_permut; [| exact H1].
    clear.
    eapply Permutation.perm_skip.
    rewrite app_comm_cons.
    eapply Permutation.Permutation_app_tail.
    eapply Permutation.Permutation_cons_append.
  Qed.

  Lemma remember_label_vs S_stack' S_ignore S_vs Ss Sp:
    SplitStoreTypings (S_stack' :: (S_ignore ++ [S_vs]) ++ Ss) Sp ->
    exists S_stack,
      SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp /\
      SplitStoreTypings (S_vs :: [S_stack']) S_stack.
  Proof.
    intros Hs.
    rewrite app_comm_cons in Hs.
    eapply SplitStoreTypings_commutative in Hs.
    replace ((S_ignore ++ [S_vs]) ++ S_stack' :: Ss) with (S_ignore ++ ([S_vs] ++ S_stack' :: Ss)) in Hs by (rewrite app_assoc; reflexivity).
    eapply SplitStoreTypings_comm' in Hs.
    simpl in Hs.
    replace (S_vs :: S_stack' :: Ss ++ S_ignore) with ([S_vs; S_stack'] ++ (Ss ++ S_ignore)) in Hs by (simpl; reflexivity).
    eapply SplitStoreTyping_app in Hs. destructAll.
    exists x.
    split; eauto.
    eapply SplitStoreTypings_permut; [| exact H0].
    eapply Permutation.perm_skip.
    eapply Permutation.Permutation_app_comm.
  Qed.

  Lemma HasTypeInstruction_val_local_agnostic S C F L L' vs tausvs:
    HasTypeInstruction S C F L  (map term.Val vs) (Arrow [] tausvs) L ->
    LocalCtxValid F L' ->
    HasTypeInstruction S C F L' (map term.Val vs) (Arrow [] tausvs) L'.
  Proof.
    revert S C F L L' tausvs.
    eapply rev_ind with (l := vs); simpl; intros.
    - match goal with
      | [ H : HasTypeInstruction _ _ _ _ [] _ _ |- _ ] =>
        specialize (HasTypeInstruction_QualValid H);
        show_tlvs H; eapply Empty_HasTypeInstruction in H
      end.
      destructAll.
      eapply EmptyTyp; eauto.
    - rewrite map_app in *. simpl in *.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ _) _ _ |- _ ] =>
        edestruct composition_typing_single in H0
      end.
      eassumption. destructAll.
      assert (Hd : [] = x1) by (destruct x0; destruct x1; eauto; discriminate).
      destruct Hd.
      assert (Hd : [] = x0) by (destruct x0; eauto; discriminate).
      destruct Hd.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [_] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H
      end.
      destructAll.
      rewrite app_nil_l.
      eapply ConsTyp.
      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] => exact H
      end.
      match goal with
      | [ H : forall _ _ _ _ _ _ _, _ |- _ ] => eapply H
      end.
      eapply ChangeEndLocalTyp; [ eauto | eauto | ].
      eauto.
      solve_lcvs.
      assert (Hrw : x3 = x3 ++ []) by (rewrite app_nil_r; eauto).
      rewrite Hrw.
      rewrite<- app_assoc.
      eapply (FrameTyp _ _ _ _ _ Linear); eauto.
      + eapply Forall_trivial. intros. destruct x1. eapply QualLeq_Top.
      + eapply QualLeq_Top.
      + rewrite app_nil_l.
        eapply ValTyp.
        eapply HasTypeValue_Function_Ctx; [ | | | | eauto]; destruct F; eauto.
        -- destruct F; subst; simpl in *; solve_lcvs.
        -- destruct F; simpl; rewrite get_set_hd; econstructor; eauto.
      + eapply HasTypeInstruction_QualValid; eauto.
      + econstructor; eauto.
  Qed.

  Lemma HasTypeInstruction_val_frame_agnostic S C F L L' vs taus tauvs:
    HasTypeInstruction S C F L (map term.Val vs) (Arrow [] tauvs) L' ->
    Forall (TypeValid F) taus ->
    HasTypeInstruction S C F L (map term.Val vs) (Arrow taus (taus ++ tauvs)) L'.
  Proof.
    intros.
    assert (Htaus : taus = taus ++ []) by (rewrite app_nil_r; eauto).
    rewrite Htaus.
    rewrite<- app_assoc.
    eapply (FrameTyp _ _ _ _ _ Linear); eauto.
    - eapply Forall_trivial. intros. destruct x. eapply QualLeq_Top.
    - eapply QualLeq_Top.
    - rewrite app_nil_l.
      eapply HasTypeInstruction_val_Function_Ctx; [| | | | eauto|]; destruct F;  eauto.
      simpl.
      rewrite get_set_hd; econstructor; eauto.
    - eapply HasTypeInstruction_QualValid; eauto.
    - econstructor; eauto.
  Qed.

  Lemma HasTypeLocals_Function_Ctx Ss F F' vs L:
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    HasTypeLocals F Ss vs L ->
    HasTypeLocals F' Ss vs L.
  Proof.
    intros.
    invert H3.
    eapply LocalCtxTyp.
    eapply Forall3_monotonic; eauto.
    intros.
    destruct x3.
    eapply HasTypeValue_Function_Ctx; eauto.
  Qed.

  Lemma HasTypeInstruction_app_val S_vs S_es S_stack C F L L' vs es tausvs t1 t2:
    SplitStoreTypings [S_vs; S_es] S_stack ->
    HasTypeInstruction S_vs C F L (map term.Val vs) (Arrow [] tausvs) L ->
    HasTypeInstruction S_es C F L es (Arrow (t1 ++ tausvs) t2) L' ->
    HasTypeInstruction S_stack C F L (map term.Val vs ++ es) (Arrow t1 t2) L'.
  Proof.
    revert S_vs S_es S_stack C F L L' vs tausvs t1 t2.
    eapply rev_ind with (l := es); simpl; intros.
    - match goal with
      | [ H : HasTypeInstruction _ _ _ _ [] _ _ |- _ ] =>
        show_tlvs H; eapply Empty_HasTypeInstruction in H
      end.
      destructAll.
      rewrite app_nil_r.
      eapply HasTypeInstruction_val_frame_agnostic.
      2:{ solve_tvs. }
      eapply Proper_HasTypeInstruction; eauto.
      eapply StoreTyping_Equiv.
      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] =>
        eapply SplitStoreTypings_comm in H
      end.
      eapply SplitStoreTypings_Empty_eq; eauto.
    - edestruct composition_typing_single_strong. eassumption. destructAll.
      simpl in *; destructAll.
      match goal with
      | [ H : SplitStoreTypings [?A; ?B] _,
          H' : SplitStoreTypings _ ?B |- _ ] =>
        eapply SplitStoreTypings_comm in H;
        eapply SplitStoreTypings_comm in H';
        assert (IH1 := SplitStoreTypings_assoc _ _ _ _ _ H' H)
      end.
      destructAll.
      match goal with
      | [ H : SplitStoreTypings [?B; _] ?A,
          H' : SplitStoreTypings _ ?A,
          H'' : SplitStoreTypings _ ?B |- _ ] =>
        eapply SplitStoreTypings_comm in H'
      end.
      match goal with
      | [ H : HasTypeInstruction ?S ?C _ ?L ?ES (Arrow ?TAU1 ?TAU2) ?LP
          |- HasTypeInstruction _ _ _ _ (_ ++ ?ES ++ _) (Arrow _ (?TAU0 ++ _)) _ ] =>
        assert (IH1 : HasTypeInstruction S C F L ES (Arrow (TAU0 ++ TAU1) (TAU0 ++ TAU2)) LP)
      end.
      { eapply FrameTyp; eauto. }
      match goal with
      | [ H : ?A = ?B, H' : context[?B] |- _ ] => rewrite <-H in H'
      end.
      match goal with
      | [ H : SplitStoreTypings [_; ?B] S_stack,
          H' : SplitStoreTypings [_; ?B] _ |- _ ] =>
        eapply SplitStoreTypings_comm in H'
      end.
      match goal with
      | [ H : SplitStoreTypings [?E; _] S_stack,
          H' : SplitStoreTypings [?F; _] S_stack,
          H'' : HasTypeInstruction ?F _ _ _ _ _ _
          |- HasTypeInstruction _ _ _ _ (?G ++ _ ++ _) _ _ ] =>
        match type of IH1 with
        | HasTypeInstruction
            ?S ?C ?F ?L ?ES
            (Arrow (?A ++ ?B) ?D) ?LP =>
          assert (IH : HasTypeInstruction E C F L (G ++ ES) (Arrow A D) LP) by eauto
        end
      end.
      rewrite app_assoc.
      eapply ConsTyp; eauto.
  Qed.

  Lemma HasTypeInstruction_cons S_stack C F e es t1 t2 t3 L L' L'':
    HasTypeInstruction S_stack C F L [e] (Arrow t1 t2) L' ->
    HasTypeInstruction (empty_LinTyp S_stack) C F L' es (Arrow t2 t3) L'' ->
    HasTypeInstruction S_stack C F L (e :: es) (Arrow t1 t3) L''.
  Proof.
    revert S_stack C F e t1 t2 t3 L L' L''.
    eapply rev_ind with (l := es); simpl; intros.
    - match goal with
      | [ H : HasTypeInstruction _ _ _ _ [] _ _ |- _ ] =>
        eapply Empty_HasTypeInstruction in H
      end.
      destructAll.
      eapply ChangeEndLocalTyp; [ eauto | eauto | ].
      eassumption.
    - edestruct composition_typing_single_strong. eassumption. destructAll.
      simpl in *; destructAll.
      replace (e :: l ++ [x]) with ((e :: l) ++ [x]) by eauto.
      eapply ConsTyp.
      exact (SplitStoreTypings_EmptyHeapTyping_r S_stack).
      { match goal with
        | [ H : forall _ _ _ _ _ _ _, _ |- _ ] => eapply H
        end.
        eauto.
        eapply FrameTyp; eauto.
        eapply Proper_HasTypeInstruction; eauto.
        match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] =>
          eapply SplitStoreTypings_comm in H;
          eapply StoreTyping_Equiv;
          eapply SplitStoreTypings_Empty_eq; eauto;
          eapply SplitStoreTypings_Empty in H
        end.
        - match goal with
          | [ H : Forall _ [_; _] |- _ ] => inv H; auto
          end.
        - destruct S_stack; simpl; congruence.
      }
      eapply FrameTyp; eauto.
      eapply Proper_HasTypeInstruction; eauto.
      eapply StoreTyping_Equiv.
      eapply SplitStoreTypings_Empty_eq; eauto.
      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] =>
        eapply SplitStoreTypings_Empty in H
      end.
      match goal with
      | [ H : Forall _ [_; _] |- _ ] => invert H
      end.
      eassumption.
      destruct S_stack; simpl; congruence.
  Qed.

  Lemma add_local_effects_length L tl:
    length L = length (add_local_effects L tl).
  Proof.
    revert L.
    induction tl; simpl; intros; eauto.
    destruct a.
    destruct (get_localtype n L); eauto.
    destruct p.
    rewrite<- IHtl.
    clear.
    unfold set_localtype.
    eapply nth_upd_length.
  Qed.

  Lemma nth_error_nth_upd (A : Type) (L : list A) n x :
    n < length L ->
    nth_error (nth_upd L n x) n = Some x.
  Proof.
    revert n.
    induction L; simpl; intros; try lia.
    destruct n; simpl in *; try congruence.
    eapply IHL.
    lia.
  Qed.

  Lemma nth_upd_beyond_length (A : Type) (L : list A) n x:
    length L <= n ->
    nth_upd L n x = L.
  Proof.
    revert n.
    induction L; simpl; intros; eauto.
    destruct n; try lia.
    f_equal.
    eapply IHL.
    lia.
  Qed.

  Lemma get_localtype_set_localtype n t s L:
    n < length L ->
    get_localtype n (set_localtype n t s L) = Some (t, s).
  Proof.
    unfold get_localtype.
    unfold set_localtype.
    eapply nth_error_nth_upd.
  Qed.

  Lemma nth_upd_overwrite (A : Type) (L : list A) n x1 x2:
    (nth_upd (nth_upd L n x1) n x2) = nth_upd L n x2.
  Proof.
    assert (n < length L \/ length L <= n) by lia.
    destruct H.
    - revert n H.
      induction L; simpl; intros; eauto.
      destruct n; simpl; try congruence.
      f_equal. eapply IHL. lia.
    - revert L H.
      induction n; simpl; intros; destruct L; eauto.
      simpl. f_equal. eapply IHn. simpl in H. lia.
  Qed.

  Lemma nth_upd_swap (A : Type) (L : list A) n1 n2 x1 x2 :
    n1 <> n2 ->
    nth_upd (nth_upd L n2 x2) n1 x1 = nth_upd (nth_upd L n1 x1) n2 x2.
  Proof.
    intros.
    assert (n1 < length L \/ length L <= n1) by lia.
    destruct H0.
    - assert (n2 < length L \/ length L <= n2) by lia.
      destruct H1.
      + revert L n2 H H0 H1.
        induction n1; simpl; intros.
        * destruct L; simpl in *; try lia.
          destruct n2; simpl; try lia.
          congruence.
        * revert n1 IHn1 L H H0 H1.
          induction n2; simpl; intros; try (destruct L; simpl in *; try lia; congruence).
          destruct L; simpl in *; try lia.
          f_equal.
          eapply IHn1; eauto; lia.
      + assert (H2 := H1).
        eapply nth_upd_beyond_length in H1.
        rewrite H1.
        erewrite nth_upd_length in H2.
        eapply nth_upd_beyond_length in H2.
        rewrite H2.
        congruence.
    - assert (H1 := H0).
      eapply nth_upd_beyond_length in H0.
      rewrite H0.
      erewrite nth_upd_length in H1.
      eapply nth_upd_beyond_length in H1.
      rewrite H1.
      congruence.
  Qed.

  Lemma add_local_effects_preserves_sizes_n L n t t' s s0 tl :
    n < length L ->
    nth_error (add_local_effects (nth_upd L n (t, s)) tl) n = Some (t', s0) ->
    s = s0.
  Proof.
    revert L t t'.
    induction tl; simpl; intros.
    - revert n H H0.
      eapply rev_ind with (l := L); simpl; intros; try lia.
      eapply nth_error_nth_upd in H0.
      rewrite H0 in H1.
      invert H1; congruence.
    - destruct a.
      unfold set_localtype in H0.
      unfold get_localtype in H0.
      assert (n = n0 \/ n <> n0) by lia.
      destruct H1.
      + subst.
        eapply IHtl; eauto.
        eapply nth_error_nth_upd in H.
        rewrite H in H0.
        rewrite nth_upd_overwrite in H0.
        exact H0.
      + assert (n0 < length L \/ length L <= n0) by lia.
        destruct H2 as [H2 | H2]; simpl; intros.
        * erewrite nth_upd_length in H2.
          eapply nth_error_some_exists in H2.
          destruct H2.
          rewrite H2 in H0.
          destruct x.
          erewrite nth_upd_length in H.
          eapply IHtl; eauto.
          rewrite nth_upd_swap in H0; eauto.
        * erewrite nth_upd_length in H2.
          eapply nth_error_None in H2.
          rewrite H2 in H0.
          eapply IHtl; eauto.
  Qed.

  Lemma nth_error_nth_upd_different (A : Type) (l : list A) n0 x0 n x:
    n0 <> n ->
    nth_error (nth_upd l n x) n0 = Some x0 <->
    nth_error l n0 = Some x0.
  Proof.
    intros.
    unfold "<->".
    split; intros.
    - revert H0.
      eapply rev_ind with (l := l); simpl; intros; eauto.
      assert (n < length l0 \/ n = length l0 \/ n > length l0) by lia.
      destruct H2 as [H2 | [H2 | H2]].
      + assert (n0 < length l0 \/ n0 = length l0 \/ n0 > length l0) by lia.
        destruct H3 as [ H3 | [ H3 | H3 ] ].
        * assert (H4 := H3).
          eapply nth_error_app1 in H3.
          rewrite H3.
          eapply H0.
          eapply nth_upd_length_less in H2.
          rewrite H2 in H1.
          erewrite nth_upd_length in H4.
          eapply nth_error_app1 in H4.
          rewrite H4 in H1.
          eassumption.
        * subst. rewrite nth_error_app.
          eapply nth_upd_length_less in H2.
          rewrite H2 in H1.
          erewrite nth_upd_length in H1.
          rewrite nth_error_app in H1.
          eassumption.
        * assert (n0 >= length (l0 ++ [x1])).
          rewrite app_length. simpl. lia.
          erewrite nth_upd_length in H4.
          eapply nth_error_None in H4.
          rewrite H4 in H1.
          discriminate.
      + subst. rewrite nth_upd_length_eq in H1.
        assert (n0 < length l0 \/ n0 = length l0 \/ n0 > length l0) by lia.
        destruct H2 as [ H2 | [ H2 | H2 ] ]; try lia.
        * assert (H3 := H2).
          eapply nth_error_app1 in H2.
          rewrite H2.
          eapply H0.
          eapply nth_error_app1 in H3.
          rewrite H3 in H1.
          rewrite<- H1.
          rewrite nth_upd_beyond_length; eauto.
        * assert (n0 >= length (l0 ++ [x])).
          rewrite app_length. simpl. lia.
          eapply nth_error_None in H3.
          rewrite H3 in H1.
          discriminate.
      + eapply nth_upd_length_greater in H2.
        rewrite H2 in H1.
        eassumption.
    - revert H0.
      eapply rev_ind with (l := l); simpl; intros; eauto.
      assert (n < length l0 \/ n = length l0 \/ n > length l0) by lia.
      destruct H2 as [H2 | [H2 | H2]].
      + assert (n0 < length l0 \/ n0 = length l0 \/ n0 > length l0) by lia.
        destruct H3 as [ H3 | [ H3 | H3 ] ].
        * assert (H4 := H3).
          eapply nth_error_app1 in H3.
          rewrite H3 in H1.
          eapply H0 in H1.
          eapply nth_upd_length_less in H2.
          rewrite H2.
          erewrite nth_upd_length in H4.
          eapply nth_error_app1 in H4.
          rewrite H4.
          eassumption.
        * subst. rewrite nth_error_app in H1.
          invert H1.
          eapply nth_upd_length_less in H2.
          rewrite H2.
          erewrite nth_upd_length.
          rewrite nth_error_app.
          eassumption.
        * assert (n0 >= length (l0 ++ [x1])).
          rewrite app_length. simpl. lia.
          eapply nth_error_None in H4.
          rewrite H4 in H1.
          discriminate.
      + subst. rewrite nth_upd_length_eq.
        assert (n0 < length l0 \/ n0 = length l0 \/ n0 > length l0) by lia.
        destruct H2 as [ H2 | [ H2 | H2 ] ]; try lia.
        * assert (H3 := H2).
          eapply nth_error_app1 in H2.
          rewrite H2 in H1.
          eapply H0 in H1.
          eapply nth_error_app1 in H3.
          rewrite H3.
          rewrite<- H1.
          rewrite nth_upd_beyond_length; eauto.
        * assert (n0 >= length (l0 ++ [x1])).
          rewrite app_length. simpl. lia.
          eapply nth_error_None in H3.
          rewrite H3 in H1.
          discriminate.
      + eapply nth_upd_length_greater in H2.
        rewrite H2.
        eassumption.
  Qed.

  Lemma add_local_effects_nth_upd_swap l1 l2 n s t t1 t2 tl:
    nth_error l1 n = Some (t1, s) ->
    nth_error l2 n = Some (t2, s) ->
    (List.In n (fst (split tl)) /\ add_local_effects l1 tl = add_local_effects l2 tl)
    \/ (~ List.In n (fst (split tl)) /\ (nth_upd (add_local_effects l1 tl) n (t, s) = nth_upd (add_local_effects l2 tl) n (t, s))) ->
    add_local_effects (nth_upd l1 n (t, s)) tl = add_local_effects (nth_upd l2 n (t, s)) tl.
  Proof.
    intros.
    destruct H1; destruct H1.
    - revert l1 l2 H H0 H1 H2.
      induction tl; simpl; intros; try (subst; eauto).
      destruct a.
      unfold get_localtype in *.
      unfold set_localtype in *.
      assert (n0 < length l1 \/ length l1 <= n0) by lia.
      destruct H3.
      + assert (H4 := H3).
        assert (H100 := H3).
        eapply nth_error_some_exists in H3.
        destruct H3.
        rewrite H3 in H2.
        erewrite nth_upd_length in H4.
        eapply nth_error_some_exists in H4.
        destruct H4.
        rewrite H4.
        destruct x.
        destruct x0.
        assert (n0 < length l2 \/ length l2 <= n0) by lia.
        destruct H5.
        * assert (H6 := H5).
          assert (H101 := H5).
          eapply nth_error_some_exists in H5.
          destruct H5.
          rewrite H5 in H2.
          erewrite nth_upd_length in H6.
          eapply nth_error_some_exists in H6.
          destruct H6.
          rewrite H6.
          destruct x.
          destruct x0.
          assert (n = n0 \/ n <> n0) by lia.
          destruct H7.
          --subst.
            rewrite H0 in H5.
            rewrite H in H3.
            invert H3.
            invert H5.
            eapply (nth_error_nth_upd _ _ _ (t, s2)) in H100.
            rewrite H100 in H4.
            invert H4.
            eapply (nth_error_nth_upd _ _ _ (t4, s1)) in H101.
            rewrite H101 in H6.
            invert H6.
            rewrite nth_upd_overwrite.
            rewrite nth_upd_overwrite.
            eassumption.
          --assert (List.In n (fst (split tl))).
            { clear - H1 H7.
              destruct (split tl).
              simpl in *.
              destruct H1; eauto; lia.
            }
            rewrite<- (nth_error_nth_upd_different _ _ n0 _ n) in H3; eauto.
            rewrite H3 in H4.
            invert H4.
            rewrite<- (nth_error_nth_upd_different _ _ n0 _ n) in H5; eauto.
            rewrite H5 in H6.
            invert H6.
            rewrite (nth_upd_swap _ _ n0); eauto.
            rewrite (nth_upd_swap _ _ n0); eauto.
            rewrite<- nth_error_nth_upd_different in H.
            rewrite<- nth_error_nth_upd_different in H0.
            eapply IHtl; eauto.
            lia. lia.
        * assert (H6 := H5).
          assert (H101 := H5).
          eapply nth_error_None in H5.
          rewrite H5 in H2.
          erewrite nth_upd_length in H6.
          eapply nth_error_None in H6.
          rewrite H6.
          assert (n = n0 \/ n <> n0) by lia.
          destruct H7.
          --subst.
            rewrite H0 in H5.
            rewrite H in H3.
            invert H3.
            invert H5.
          --assert (List.In n (fst (split tl))).
            { clear - H1 H7.
              destruct (split tl).
              simpl in *.
              destruct H1; eauto; lia.
            }
            rewrite<- (nth_error_nth_upd_different _ _ n0 _ n) in H3; eauto.
            rewrite H3 in H4.
            invert H4.
            rewrite (nth_upd_swap _ _ n0); eauto.
            rewrite<- nth_error_nth_upd_different in H.
            eapply IHtl; eauto.
            lia.
      + assert (H4 := H3).
        assert (H100 := H3).
        eapply nth_error_None in H3.
        rewrite H3 in H2.
        erewrite nth_upd_length in H4.
        eapply nth_error_None in H4.
        rewrite H4.
        assert (n0 < length l2 \/ length l2 <= n0) by lia.
        destruct H5.
        * assert (H6 := H5).
          assert (H101 := H5).
          eapply nth_error_some_exists in H5.
          destruct H5.
          rewrite H5 in H2.
          erewrite nth_upd_length in H6.
          eapply nth_error_some_exists in H6.
          destruct H6.
          rewrite H6.
          destruct x.
          destruct x0.
          assert (n = n0 \/ n <> n0) by lia.
          destruct H7.
          --subst.
            rewrite H0 in H5.
            rewrite H in H3.
            invert H3.
          --assert (List.In n (fst (split tl))).
            { clear - H1 H7.
              destruct (split tl).
              simpl in *.
              destruct H1; eauto; lia.
            }
            rewrite<- (nth_error_nth_upd_different _ _ n0 _ n) in H5; eauto.
            rewrite H5 in H6.
            invert H6.
            rewrite (nth_upd_swap _ _ n0); eauto.
            rewrite<- nth_error_nth_upd_different in H0.
            eapply IHtl; eauto.
            lia.
        * assert (H6 := H5).
          assert (H101 := H5).
          eapply nth_error_None in H5.
          rewrite H5 in H2.
          erewrite nth_upd_length in H6.
          eapply nth_error_None in H6.
          rewrite H6.
          assert (n = n0 \/ n <> n0) by lia.
          destruct H7.
          --subst.
            rewrite H0 in H5.
            rewrite H in H3.
            invert H3.
          --assert (List.In n (fst (split tl))).
            { clear - H1 H7.
              destruct (split tl).
              simpl in *.
              destruct H1; eauto; lia.
            }
            eapply IHtl; eauto.
    - revert l1 l2 H H0 H1 H2.
      induction tl; simpl; intros; eauto.
      destruct a.
      assert (~ List.In n (fst (split tl))).
      { clear - H1.
        destruct (split tl).
        simpl in H1.
        unfold "~" in *.
        intros.
        eapply H1.
        right.
        simpl in H.
        eassumption.
      }
      unfold get_localtype in *.
      assert (n0 < length l1 \/ length l1 <= n0) by lia.
      destruct H4.
      + assert (H5 := H4).
        eapply nth_error_some_exists in H4.
        destruct H4.
        rewrite H4 in H2.
        erewrite nth_upd_length in H5.
        eapply nth_error_some_exists in H5.
        destruct H5.
        rewrite H5.
        destruct x.
        destruct x0.
        assert (n0 < length l2 \/ length l2 <= n0) by lia.
        destruct H6.
        * assert (H7 := H6).
          eapply nth_error_some_exists in H6.
          destruct H6.
          rewrite H6 in H2.
          erewrite nth_upd_length in H7.
          eapply nth_error_some_exists in H7.
          destruct H7.
          rewrite H7.
          destruct x.
          destruct x0.
          unfold set_localtype in *.
          assert (Hneq : n0 <> n).
          { clear - H1. unfold "<>". unfold "~" in H1. intros; eapply H1.
            subst. destruct (split tl). simpl. left. congruence.
          }
          rewrite nth_error_nth_upd_different in H5; eauto.
          rewrite nth_error_nth_upd_different in H7; eauto.
          rewrite H4 in H5. invert H5.
          rewrite H6 in H7. invert H7.
          rewrite<- nth_error_nth_upd_different in H.
          rewrite<- nth_error_nth_upd_different in H0.
          assert (IH := IHtl _ _ H H0 H3 H2).
          2 : { lia. }
          2 : { lia. }
          rewrite (nth_upd_swap _ _ n0 n); eauto.
          rewrite (nth_upd_swap _ _ n0 n); eauto.
        * assert (H7 := H6).
          eapply nth_error_None in H6.
          rewrite H6 in H2.
          erewrite nth_upd_length in H7.
          eapply nth_error_None in H7.
          rewrite H7.
          unfold set_localtype in *.
          assert (Hneq : n0 <> n).
          { clear - H1. unfold "<>". unfold "~" in H1. intros; eapply H1.
            subst. destruct (split tl). simpl. left. congruence.
          }
          rewrite nth_error_nth_upd_different in H5; eauto.
          rewrite H4 in H5. invert H5.
          rewrite<- nth_error_nth_upd_different in H.
          assert (IH := IHtl _ _ H H0 H3 H2).
          2 : { lia. }
          rewrite nth_upd_swap; eauto.
      + assert (H5 := H4).
        eapply nth_error_None in H4.
        rewrite H4 in H2.
        erewrite nth_upd_length in H5.
        eapply nth_error_None in H5.
        rewrite H5.
        assert (n0 < length l2 \/ length l2 <= n0) by lia.
        destruct H6.
        * assert (H7 := H6).
          eapply nth_error_some_exists in H6.
          destruct H6.
          rewrite H6 in H2.
          erewrite nth_upd_length in H7.
          eapply nth_error_some_exists in H7.
          destruct H7.
          rewrite H7.
          destruct x.
          destruct x0.
          unfold set_localtype in *.
          assert (Hneq : n0 <> n).
          { clear - H1. unfold "<>". unfold "~" in H1. intros; eapply H1.
            subst. destruct (split tl). simpl. left. congruence.
          }
          rewrite nth_error_nth_upd_different in H7; eauto.
          rewrite H6 in H7. invert H7.
          rewrite<- nth_error_nth_upd_different in H0.
          assert (IH := IHtl _ _ H H0 H3 H2).
          2 : { lia. }
          rewrite nth_upd_swap; eauto.
        * assert (H7 := H6).
          eapply nth_error_None in H6.
          rewrite H6 in H2.
          erewrite nth_upd_length in H7.
          eapply nth_error_None in H7.
          rewrite H7.
          eapply IHtl; eauto.
  Qed.

  Lemma add_local_effects_set_localtype n t s L tl:
    add_local_effects (set_localtype n t s (add_local_effects (set_localtype n t s L) tl)) tl =
    add_local_effects (add_local_effects (set_localtype n t s L) tl) tl.
  Proof.
    assert (n < length L \/ length L <= n) by lia.
    destruct H.
    - revert n t s L H.
      induction tl; simpl; intros.
      + unfold set_localtype.
        revert n H.
        induction L; simpl; intros; eauto.
        destruct n; simpl; try congruence.
        f_equal.
        eapply IHL.
        lia.
      + destruct a.
        assert (n0 = n \/ n0 <> n) by lia.
        destruct H0.
        * subst.
          rewrite (get_localtype_set_localtype _ _ _ L); eauto.
          rewrite get_localtype_set_localtype.
          2 : {
            rewrite<- add_local_effects_length.
            unfold set_localtype.
            rewrite<- nth_upd_length.
            rewrite<- nth_upd_length.
            eassumption.
          }
          unfold get_localtype.
          assert (n < length (add_local_effects (set_localtype n t1 s (set_localtype n t0 s L)) tl)).
          rewrite<- add_local_effects_length.
          unfold set_localtype.
          rewrite<- nth_upd_length.
          rewrite<- nth_upd_length.
          eassumption.
          destruct (nth_error_some_exists _ _ _ H0).
          destruct x.
          rewrite H1.
          unfold set_localtype.
          unfold set_localtype in H1.
          rewrite nth_upd_overwrite.
          rewrite nth_upd_overwrite.
          rewrite nth_upd_overwrite in H1.
          assert (s = s0) by (clear H0; eapply add_local_effects_preserves_sizes_n; eauto).
          subst.
          eauto.
        * unfold get_localtype.
          unfold set_localtype in *.
          assert (n0 < length L \/ length L <= n0) by lia.
          destruct H1; simpl.
          --assert (H2 := H1).
            erewrite nth_upd_length in H2.
            eapply nth_error_some_exists in H2.
            destruct H2.
            rewrite H2.
            destruct x.
            assert (H3 := H1).
            erewrite nth_upd_length in H3.
            erewrite nth_upd_length in H3.
            erewrite add_local_effects_length in H3.
            erewrite nth_upd_length in H3.
            eapply nth_error_some_exists in H3.
            destruct H3.
            rewrite H3.
            destruct x.
            assert (H4 := H1).
            erewrite nth_upd_length in H4.
            erewrite nth_upd_length in H4.
            erewrite add_local_effects_length in H4.
            eapply nth_error_some_exists in H4.
            destruct H4.
            rewrite H4.
            destruct x.
            assert (s1 = s2).
            { clear - H3 H4 H0.
              revert H3 H4.
              generalize (add_local_effects (nth_upd (nth_upd L n (t0, s)) n0 (t1, s0)) tl).
              intros.
              rewrite nth_error_nth_upd_different in H3; eauto.
              rewrite H3 in H4.
              invert H4.
              congruence.
            }
            subst.
            assert (s0 = s2).
            { clear - H1 H4.
              rewrite (nth_upd_length _ _ n (t0, s)) in H1.
              revert H1 H4.
              generalize (nth_upd L n (t0, s)).
              intros.
              eapply add_local_effects_preserves_sizes_n; eauto.
            }
            subst.
            eapply add_local_effects_nth_upd_swap; eauto.
            destruct (LEM (List.In n0 (fst (split tl)))).
            ++left; split; eauto.
              eapply nth_upd_swap in H0.
              rewrite H0.
              eapply IHtl.
              rewrite<- nth_upd_length.
              eassumption.
            ++right; split; eauto.
              f_equal.
              eapply nth_upd_swap in H0.
              rewrite H0.
              eapply IHtl.
              rewrite<- nth_upd_length.
              eassumption.
          --assert (H2 := H1).
            erewrite nth_upd_length in H2.
            eapply nth_error_None in H2.
            rewrite H2; simpl in *.
            clear H2.
            assert (H2 := H1).
            erewrite nth_upd_length in H2.
            erewrite add_local_effects_length in H2.
            eapply nth_error_None in H2.
            rewrite H2.
            clear H2.
            assert (H2 := H1).
            erewrite nth_upd_length in H2.
            erewrite add_local_effects_length in H2.
            erewrite nth_upd_length in H2.
            eapply nth_error_None in H2.
            rewrite H2.
            clear H2.
            eapply IHtl; eassumption.
    - unfold set_localtype.
      assert (H1 := H).
      eapply nth_upd_beyond_length in H.
      rewrite H.
      erewrite add_local_effects_length in H1.
      eapply nth_upd_beyond_length in H1.
      rewrite H1.
      congruence.
  Qed.


  Lemma Local_effects_idempotent L tl :
    add_local_effects L tl = add_local_effects (add_local_effects L tl) tl.
  Proof.
    revert L.
    induction tl; intros; eauto.
    destruct a.
    simpl.
    unfold get_localtype.
    assert (n < length L \/ length L <= n) by lia.
    destruct H.
    - destruct (nth_error_some_exists _ _ _ H).
      rewrite H0.
      destruct x.
      assert (n < length (add_local_effects (set_localtype n t0 s L) tl)).
      { clear - H.
        erewrite<- add_local_effects_length.
        unfold set_localtype.
        rewrite<- nth_upd_length.
        eassumption.
      }
      destruct (nth_error_some_exists _ _ _ H1).
      rewrite H2.
      destruct x.
      unfold set_localtype in H2.
      assert (s = s0) by (clear H1; eapply add_local_effects_preserves_sizes_n; eauto).
      subst.
      rewrite add_local_effects_set_localtype.
      eapply IHtl.
    - assert (H1 := H).
      eapply nth_error_None in H.
      rewrite H.
      erewrite add_local_effects_length in H1.
      eapply nth_error_None in H1.
      rewrite H1.
      eapply IHtl.
  Qed.


  Lemma split_app_single (A B : Type) (l1 l2 : list (A * B)) x1 x2:
    snd (split (l1 ++ [x1])) = snd (split (l2 ++ [x2])) ->
    snd (split l1) = snd (split l2) /\
    snd x1 = snd x2.
  Proof.
    intros.
    assert (Forall2 (fun _ _ => True) l1 l2).
    { eapply Forall2_trivial; eauto.
      eapply (f_equal) in H.
      do 2 rewrite split_length_r in H.
      do 2 rewrite app_length in H.
      simpl in H.
      lia.
    }
    revert l2 H H0.
    induction l1; simpl; intros.
    - invert H0.
      destruct x1. destruct x2.
      simpl in *. invert H.
      eauto.
    - invert H0.
      assert (IH := IHl1 l').
      destruct a. destruct y.
      simpl in *.
      destruct (split (l1 ++ [x1])).
      destruct (split (l' ++ [x2])).
      simpl in *.
      invert H.
      destruct (split l1).
      destruct (split l').
      simpl in *.
      assert (IH' := IH (eq_refl _) H5).
      destructAll.
      split; [f_equal |]; eassumption.
  Qed.

  Lemma ignore_rest_of_stack Sp S_stack S_ignore Ss S_vs S_es:
    SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp ->
    SplitStoreTypings [S_vs; S_es] S_stack ->
    exists S_rest : StoreTyping, SplitStoreTypings ([S_es; S_rest] ++ Ss) Sp.
  Proof.
    intros.
    eapply SplitStoreTypings_merge' in H; eauto.
    assert (SplitStoreTypings ((S_vs :: S_ignore) ++ (S_es :: Ss)) Sp).
    eapply SplitStoreTypings_permut; [| exact H].
    simpl.
    eapply Permutation.perm_skip.
    replace (S_ignore ++ S_es :: Ss) with ((S_ignore ++ [S_es]) ++ Ss) by (rewrite<- app_assoc; simpl; congruence).
    rewrite app_comm_cons.
    eapply Permutation.Permutation_app_tail.
    eapply Permutation.Permutation_cons_append.
    eapply SplitStoreTyping_app in H1.
    destruct H1 as [x [H10 H11]].
    exists x.
    eapply SplitStoreTypings_permut; [| exact H11].
    simpl.
    eapply Permutation.perm_swap.
  Qed.

  Lemma InstTyps_equal_h s S1 S2:
    Forall2 (fun i C => HasTypeInstance (InstTyp S1) i C) (inst s) (InstTyp S1) ->
    Forall2 (fun i C => HasTypeInstance (InstTyp S2) i C) (inst s) (InstTyp S2) ->
    (map func (InstTyp S1)) = (map func (InstTyp S2)) /\ (map table (InstTyp S1)) = (map table (InstTyp S2)).
  Proof.
    intros.
    destruct s. destruct S1. destruct S2.
    simpl in *.
    clear - H H0.
    assert (InstTyp = InstTyp ++ []) by (rewrite app_nil_r; eauto).
    assert (InstTyp0 = InstTyp0 ++ []) by (rewrite app_nil_r; eauto).
    revert H H0 H1 H2.
    generalize InstTyp at 1 3.
    generalize InstTyp0 at 1 3.
    generalize ([] : list Module_Ctx) at 1.
    generalize ([] : list Module_Ctx) at 1.
    revert InstTyp InstTyp0.
    eapply rev_ind with (l := inst0); simpl; intros.
    invert H. invert H0. simpl. split; congruence.
    eapply Forall2_app_inv_l in H0.
    eapply Forall2_app_inv_l in H1.
    destructAll.
    rewrite<- app_assoc in H0.
    rewrite<- app_assoc in H1.
    assert (IH := H _ _ _ _ _ _  H0 H1 (eq_refl _) (eq_refl _)).
    destruct IH.
    do 4 rewrite map_app.
    rewrite H2.
    rewrite H3.
    split; f_equal; clear - H6 H4; invert H6; invert H3; invert H4; invert H7; clear - H1 H2; simpl; f_equal; destruct x; invert H1; invert H2; unfold C in *; unfold C0 in *; simpl.
    - clear - H4 H5.
      revert H4 H5.
      generalize fts1 at 1.
      generalize fts0 at 1.
      revert fts1 fts0.
      induction func; simpl; intros; invert H4; invert H5. congruence.
      assert (IH := IHfunc _ _ _ _ H3 H7).
      subst.
      f_equal.
      clear - H1 H2.
      destruct a.
      invert H1.
      invert H2.
      clear - H6 H8.
      invert H6. invert H8.
      unfold chi. unfold chi1.
      congruence.
    - clear - H6 H9.
      revert H6 H9.
      generalize fts2 at 1.
      generalize fts3 at 1.
      revert fts2 fts3.
      induction tab; simpl; intros; invert H6; invert H9. congruence.
      assert (IH := IHtab _ _ _ _ H3 H5).
      subst.
      f_equal.
      clear - H1 H2.
      destruct a.
      invert H1.
      invert H2.
      clear - H6 H8.
      invert H6. invert H8.
      unfold chi. unfold chi1.
      congruence.
  Qed.


  Lemma SplitStoreTypings_EmptyStoreTyping_cons x l S:
    SplitStoreTypings (x :: l) (typing.EmptyStoreTyping S) ->
    SplitStoreTypings l (typing.EmptyStoreTyping S).
  Proof.
    intros.
    unfold SplitStoreTypings.
    invert H.
    invert H0.
    split; eauto.
    clear - H1.
    simpl in H1.
    invert H1.
    unfold SplitHeapTypings.
    split; simpl; intros.
    - simpl in *.
      rewrite map_util.Dom_ht_empty.
      rewrite map_util.Dom_ht_empty in H.
      assert (H2 := Union_Same_set_Empty_set_l _ _ H).
      rewrite H2 in H.
      rewrite Union_Empty_set_neut_l in H.
      eassumption.
    - unfold map_util.get_heaptype in H2.
      rewrite map_util.M.gempty in H2. discriminate.
  Qed.


  Definition grow_unr_HasTypeInstruction_mind S_stack C F L es tf L' :=
    HasTypeInstruction S_stack C F L es tf L' ->
    forall S_stack',
      map_util.sub_map (UnrTyp S_stack) (UnrTyp S_stack') ->
      HasTypeInstruction (update_unr (UnrTyp S_stack') S_stack) C F L es tf L'.
  Definition grow_unr_HasTypeClosure_mind S C F :=
    HasTypeClosure S C F ->
    forall S',
      map_util.sub_map (UnrTyp S) (UnrTyp S') ->
      HasTypeClosure (update_unr (UnrTyp S') S) C F.
  Definition grow_unr_HasTypeFunc_mind S M f ex chi :=
    HasTypeFunc S M f ex chi ->
    forall S',
      map_util.sub_map (UnrTyp S) (UnrTyp S') ->
      HasTypeFunc (update_unr (UnrTyp S') S) M f ex chi.
  Definition grow_unr_HasTypeConf_mind S_rest ret i vlocs szs es taus :=
    HasTypeConf S_rest ret i vlocs szs es taus ->
    forall S_rest',
      map_util.sub_map (UnrTyp S_rest) (UnrTyp S_rest') ->
      HasTypeConf (update_unr (UnrTyp S_rest') S_rest) ret i vlocs szs es taus.

  Lemma SplitStoreTypings_cons_strong : forall x Ss S,
      SplitStoreTypings (x :: Ss) S ->
      exists S',
        SplitStoreTypings Ss S' /\
        UnrTyp S' = UnrTyp S.
  Proof.
    intros x Ss S H; inv H. inv H0.
    exists {|InstTyp := InstTyp S; UnrTyp := UnrTyp S; LinTyp := minus (LinTyp S) (LinTyp x)|}.
    constructor; auto. constructor; auto. intros Hs; cbn. apply SplitHeapTypings_cons; auto.
  Qed.

  Lemma HasTypeValue_grow_unr S S' F v t:
    HasTypeValue S F v t ->
    map_util.sub_map (UnrTyp S) (UnrTyp S') ->
    HasTypeValue (update_unr (UnrTyp S') S) F v t.
  Proof.
    intros.
    eapply HasTypeValue_add_to_unr; eauto.
    destruct S; simpl in *.
    constructor.
  Qed.

  Lemma HasHeapType_grow_unr S S' F v t:
    map_util.sub_map (UnrTyp S) (UnrTyp S') ->
    HasHeapType S F v t ->
    HasHeapType (update_unr (UnrTyp S') S) F v t.
  Proof.
    intros.
    eapply HasHeapType_add_to_unr; eauto.
    destruct S; simpl in *.
    constructor.
  Qed.

  Lemma HasTypeInstruction_grow_unr S S' C F L es tf L':
    map_util.sub_map (UnrTyp S) (UnrTyp S') ->
    HasTypeInstruction S C F L es tf L' ->
    HasTypeInstruction (update_unr (UnrTyp S') S) C F L es tf L'.
  Proof.
    specialize HasType_Instruction_Closure_Func_Conf_add_to_unr.
    intro H'.
    destruct H' as [H' _].
    intros.
    eapply H'; eauto.
    destruct S; simpl in *.
    constructor.
  Qed.

  (* Lemmas for local case *)
  Lemma get_none_subset (A : Type) (a b : map_util.M.t A) c l :
    map_util.Dom_ht b :|: c <--> map_util.Dom_ht a ->
    map_util.get_heaptype l a = None ->
    map_util.get_heaptype l b = None.
  Proof.
    intros.
    destruct H.
    specialize (H l).
    assert (~In N (map_util.Dom_ht a) l -> ~ In N (map_util.Dom_ht b :|: c) l ) by tauto.
    assert (~ In N (map_util.Dom_ht a) l). {
      intros Hwat.
      unfold In, map_util.Dom_ht, map_util.Dom_map, In, map_util.get_heaptype in *.
      firstorder congruence. }
    apply H2 in H3.
    destruct (map_util.get_heaptype l b) eqn:Hget; [|easy].
    unfold not, In, map_util.Dom_ht, map_util.Dom_map in H3.
    cbn in H3.
    exfalso; apply H3.
    left.
    exists a0. easy.
  Qed.

  Lemma ignore_local_vs S_stack0 Ss0 S_stack Ss Sp S_ignore :
    SplitStoreTypings (S_stack0 :: Ss0) S_stack ->
    SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp ->
    SplitStoreTypings (S_stack0 :: (S_ignore ++ Ss) ++ Ss0) Sp.
  Proof.
    intros.
    unfold SplitStoreTypings.
    split.
    - invert H. invert H0. clear - H1 H3.
      invert H1.
      invert H3.
      destruct H2.
      destruct H5.
      rewrite<- H2 in H4.
      rewrite<- H5 in H4.
      rewrite H in H2.
      rewrite H0 in H5.
      eapply Forall_cons; eauto.
      eapply Forall_app in H6.
      destruct H6.
      rewrite<- app_assoc.
      eapply Forall_app; split; eauto.
      eapply Forall_app; split; eauto.
    - invert H. invert H0. clear - H2 H4. simpl in *.
      unfold SplitHeapTypings.
      split.
      + invert H2. invert H4. clear - H H1.
        simpl in *.
        rewrite<- H in H1.
        clear H.
        assert (map_util.Dom_ht (LinTyp S_stack0) :|: Union_list (map map_util.Dom_ht (map LinTyp ((S_ignore ++ Ss) ++ Ss0))) <--> map_util.Dom_ht (LinTyp S_stack0) :|: Union_list (map map_util.Dom_ht (map LinTyp Ss0)) :|: Union_list (map map_util.Dom_ht (map LinTyp (S_ignore ++ Ss)))).
        2: { rewrite H. eassumption. }
        clear.
        destruct S_stack0. simpl.
        rewrite<- Union_assoc.
        eapply (Same_set_Union_compat (map_util.Dom_ht LinTyp) (map_util.Dom_ht LinTyp)).
        easy.
        rewrite Union_commut.
        do 5 rewrite map_app.
        do 2 rewrite Union_list_app.
        easy.
      + rewrite map_app.
        rewrite map_app.
        rewrite map_app in H4.
        invert H2. invert H4. assert (H100 := H). clear - H0 H3 H100.
        intros.
        assert (H1 := H3 l ht H).
        invert H1.
        * assert (H2 := H0 l ht H6).
          invert H2.
          --eapply (typing.InHead); eauto.
            clear - H9 H12.
            eapply ExactlyInOne_true_app; split; eauto.
          --eapply (typing.NotInHead); eauto.
            eapply splitting.ExactlyInOne_app_r; eauto.
        * eapply (typing.NotInHead); eauto.
          --clear - H9 H100.
            simpl in *.
            destruct S_stack. destruct S_stack0. simpl in *. clear - H9 H100.
            eapply get_none_subset; eauto.
          --eapply splitting.ExactlyInOne_app_l; eauto.
            eapply ExactlyInOne_true.
            unfold "~".
            intros.
            clear - H100 H9 H2.
            eapply get_heaptype_None_not_In in H9.
            eapply H9.
            clear H9.
            rewrite<- H100.
            simpl.
            eapply Union_intror; eauto.
  Qed.

  Lemma remember_local_vs S_stack' S_ignore Ss Ss' Sp :
    SplitStoreTypings (S_stack' :: (S_ignore ++ Ss) ++ Ss') Sp ->
    exists S_stack,
      SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp /\
      SplitStoreTypings (S_stack' :: Ss') S_stack.
  Proof.
    intros Hs.
    rewrite app_comm_cons in Hs.
    eapply SplitStoreTypings_comm' in Hs.
    replace (Ss' ++ S_stack' :: S_ignore ++ Ss) with
      ((Ss' ++ [ S_stack' ]) ++ S_ignore ++ Ss) in Hs by (rewrite <- !app_assoc; reflexivity).

    eapply SplitStoreTyping_app in Hs. destructAll.
    eapply SplitStoreTypings_comm' in H.
    eexists. split; eauto.
  Qed.

  Lemma HasTypeLocals_ret_ctx Ss vs L x:
    HasTypeLocals empty_Function_Ctx Ss vs L <->
    HasTypeLocals (update_ret_ctx (Some x) empty_Function_Ctx) Ss vs L.
  Proof.
    unfold "<->"; split; intros; eapply HasTypeLocals_Function_Ctx; [| | | | eassumption | | | | | eassumption]; eauto.
  Qed.

  Lemma HasTypeLocals_grow_unr F Ss vs L UnrTyp UnrTyp':
    HasTypeLocals F Ss vs L ->
    map_util.sub_map UnrTyp UnrTyp' ->
    Forall (fun S : StoreTyping => typing.UnrTyp S = UnrTyp) Ss ->
    HasTypeLocals F (map (update_unr UnrTyp') Ss) vs L.
  Proof.
    intros.
    invert H.
    clear H.
    eapply LocalCtxTyp.
    revert vs L H1 H2.
    induction Ss; intros.
    invert H2. simpl. eapply Forall3_nil.
    invert H1.
    clear H1.
    invert H2.
    eapply IHSs in H7; eauto.
    destruct z.
    simpl.
    eapply Forall3_cons; eauto.
    destruct a.
    assert (UnrTyp' = typing.UnrTyp {| InstTyp := InstTyp; LinTyp := M.empty HeapType; UnrTyp := UnrTyp' |}). simpl. congruence.
    rewrite H.
    eapply HasTypeValue_grow_unr; eauto.
  Qed.

  Lemma Preservation_Reduce_full_eqv : forall {addr s1 vs1 szs1 es1 s2 vs2 es2},
      Reduce_full addr s1 vs1 szs1 es1 s2 vs2 es2 ->
      Red.Reduce_full addr s1 vs1 szs1 es1 s2 vs2 es2.
  Proof.
    intros.
    induction X; econstructor; eauto.
  Qed.

  Lemma WFPres_Reduce_eqv : forall {s vs szs es i s' vs' es'},
      Reduce s vs szs es i s' vs' es' ->
      WFPres.Red.Reduce s vs szs es i s' vs' es'.
  Proof.
    intros.
    induction H; econstructor; eauto.
    - induction H.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply WFPres.Red.red_label_trap.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply WFPres.Red.red_br_table_geq; auto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply WFPres.Red.red_local_trap.
      -- econstructor; eauto.
      -- econstructor; eauto.
    - induction X; econstructor; eauto.
  Qed.

  Lemma Progress_Reduce_eqv : forall {s vs szs es i x x0 x1},
      Progress.Red.Reduce s vs szs es i x x0 x1 ->
      Reduce s vs szs es i x x0 x1.
  Proof.
    intros.
    intros.
    induction H; econstructor; eauto.
    - induction H.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply red_label_trap.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply red_br_table_geq; auto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- econstructor; eauto.
      -- apply red_local_trap.
      -- econstructor; eauto.
      -- econstructor; eauto.
    - induction X; econstructor; eauto.
  Qed.

  Lemma Preservation_GC_step_eqv : forall {s vs es i s' vs' es'},
      GC_step s vs es i s' vs' es' ->
      PreservationGC.Red.GC_step s vs es i s' vs' es'.
  Proof.
    intros.
    inversion H; subst.
    econstructor; eauto.
  Qed.

  Definition LCHasSizes (L : Local_Ctx) (szs : list nat) :=
    Forall2
        (fun '(tau, sz1) sz2 =>
           SizeLeq [] sz1 (SizeConst sz2) = Some true /\
           SizeLeq [] (SizeConst sz2) sz1 = Some true)
        L szs.

  Lemma LCSizeEqual_LCHasSizes : forall {L L' szs},
      LCSizeEqual [] L L' ->
      LCHasSizes L szs ->
      LCHasSizes L' szs.
  Proof.
    unfold LCSizeEqual, LCHasSizes.
    intros.
    apply forall2_nth_error_inv.
    2:{
      eapply eq_trans; [ apply eq_sym | ].
      all: eapply Forall2_length; eauto.
    }
    intros.
    match goal with
    | [ H : Forall2 _ _ ?L,
        H' : Forall2 _ _ ?L2,
        H'' : nth_error ?L _ = Some _,
        H''' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_args_2 _ _ _ _ _ H H'');
      specialize (forall2_args_2 _ _ _ _ _ H' H''')
    end.
    intros; destructAll.
    destruct_prs.
    destructAll.
    match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inversion H'; subst
    end.
    split; eapply SizeLeq_Trans; eauto.
  Qed.

  Lemma LCHasSizes_trivial_provable : forall {L szs taus'},
      split L = (taus', map SizeConst szs) ->
      LCHasSizes L szs.
  Proof.
    induction L; intros; simpl in *.
    - inversion H; subst.
      destruct szs; simpl in *.
      -- constructor.
      -- inversion H2.
    - destruct_prs.
      remember (split L) as obj.
      revert H IHL Heqobj.
      case obj; intros.
      destruct taus'; destruct szs; simpl in *; inversion H; subst.
      specialize (IHL _ _ eq_refl).
      constructor; [ | eauto ].
      split; apply SizeLeq_Refl.
  Qed.

  Lemma LCHasSizes_trivial : forall {L szs},
      (let (_, szs') := split L in
       szs' = map SizeConst szs) ->
      LCHasSizes L szs.
  Proof.
    intros.
    remember (split L) as obj.
    revert Heqobj H.
    case obj; intros; subst.
    eapply LCHasSizes_trivial_provable; eauto.
  Qed.

  Lemma LCHasSizes_exists : forall {L szs},
      LCHasSizes L szs ->
      exists L',
        LCEffEqual [] L L' /\
        let (_, szs') := split L' in szs' = map SizeConst szs.
  Proof.
    induction L.
    - intros.
      inversion H; subst.
      exists [].
      split; constructor.
    - intros.
      inversion H; subst.
      destruct_prs.
      specialize (IHL _ H4).
      destructAll.
      exists ((t0, SizeConst y) :: x).
      split; simpl.
      -- constructor.
         --- split; auto.
         --- eauto.
      -- remember (split x) as obj.
         revert Heqobj H3.
         case obj; intros; subst; auto.
  Qed.

  Lemma LCEffEqual_closed_sizes_LocalCtxValid : forall {L L' F szs},
      LocalCtxValid F L ->
      LCEffEqual (size F) L L' ->
      (let (_, szs') := split L' in szs' = map SizeConst szs) ->
      LocalCtxValid F L'.
  Proof.
    induction L.
    all: intros; simpl in *.
    all:
      match goal with
      | [ H : LCEffEqual _ _ _ |- _ ] => inv H
      end.
    all: constructor.
    all: destruct_prs.
    all:
      match goal with
      | [ H : LocalCtxValid _ (_ :: _) |- _ ] =>
          rewrite LocalCtxValid_cons in H
      end.
    all: destructAll.
    all: simpl in *.
    all:
      match goal with
      | [ H : context[split ?L] |- _ ] =>
          remember (split L) as obj; destruct obj
      end.
    all:
      match goal with
      | [ H : _ :: _ = map _ ?L |- _ ] =>
          destruct L; simpl in *; inv H
      end.
    - split; auto.
      econstructor; eauto.
    - eapply IHL; eauto.
      match goal with
      | [ H : _ = ?A |- context[?A] ] => rewrite <-H
      end.
      eauto.
  Qed.

  Theorem Preservation_general :
    forall S i s vs szs es taus s' vs' es' L L' C S_ignore S_stack Sp Sh Ss,
    let F := update_ret_ctx None empty_Function_Ctx in
    well_formed_Store s = true ->
    forallb well_formed_Inst es = true ->
    well_formed_Inst_list es = true ->
    SplitStoreTypings [Sp; Sh] S ->
    HasTypeStore s Sh Sp ->
    nth_error (InstTyp Sp) i = Some C ->
    SplitStoreTypings (S_stack :: S_ignore ++ Ss) Sp ->
    HasTypeLocals empty_Function_Ctx Ss vs L ->
    HasTypeInstruction S_stack C F L es (Arrow [] taus) L' ->
    LCHasSizes L szs ->
    Reduce s vs szs es i s' vs' es' ->
    exists S' Sp' Sh' S_stack' Ss' L'',
      SplitStoreTypings [Sp'; Sh'] S' /\
      HasTypeStore s' Sh' Sp' /\
      nth_error (InstTyp Sp') i = Some C /\
      SplitStoreTypings (S_stack' :: (map (update_unr (UnrTyp S')) S_ignore) ++ Ss') Sp' /\
      HasTypeLocals empty_Function_Ctx Ss' vs' L'' /\
      HasTypeInstruction S_stack' C F L'' es' (Arrow [] taus) L' /\
      map_util.sub_map (UnrTyp S) (UnrTyp S') /\
      InstTyp S = InstTyp S' /\
      LCHasSizes L'' szs.
  Proof.
    intros.
    unfold F in *.
    clear F.
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] => revert H
    end.
    generalize (None : option (list Typ)) at 1 2.
    intros.
    assert (Hf_empty : Function_Ctx_empty empty_Function_Ctx) by (unfold Function_Ctx_empty; eauto).
    match goal with
    | [ H : HasTypeLocals _ _ _ _,
        H' : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] =>
      revert H H' Hf_empty
    end.
    generalize empty_Function_Ctx.
    intros.
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] => revert H
    end.
    generalize ([] : list Typ).
    intros.
    match goal with
    | [ H : well_formed_Store _ = true,
        H' : forallb well_formed_Inst _ = true,
        H'' : well_formed_Inst_list _ = true,
        H''' : SplitStoreTypings [_; _] _,
        H'''' : HasTypeStore _ _ _,
        H''''' : nth_error _ _ = Some _,
        H'''''' : SplitStoreTypings (_ :: _ ++ _) _,
        H''''''' : HasTypeLocals _ _ _ _,
        H'''''''' : HasTypeInstruction _ _ _ _ _ _ _,
        H''''''''' : LCHasSizes _ _ |- _ ] =>
      revert H''''''''' H'''''''' H''''''' H'''''' H''''' H'''' H''' H'' H' H
    end.
    revert f l taus o S_stack S_ignore Ss L C L' Hf_empty.
    match goal with
    | [ H : Reduce _ _ _ _ _ _ _ _ |- _ ] => induction H; intros
    end.
    - match goal with
      | [ H : well_formed_Inst_list _ = true |- _ ] =>
        assert (Hremember1 := H);
        eapply well_formed_Inst_list_ctx in H; eauto
      end. 
      match goal with
      | [ H : forallb well_formed_Inst _ = true |- _ ] =>
        assert (Hremember2 := H);
        eapply well_formed_Inst_ctx in H
      end.
      revert Hremember1 Hremember2.
      match goal with
      | [ H : SplitStoreTypings (_ :: _ ++ _) _,
          H' : HasTypeLocals _ _ _ _ |- _ ] => revert H H'
      end.
      revert Hf_empty.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] => revert H
      end.
      revert L L' f S_ignore S_stack l taus.
      induction k; intros.
      + assert (Hn : 0 = 0) by congruence.
        revert Hremember1 Hremember2.
        match goal with
        | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] => revert H
        end.
        revert L Hn.
        generalize 0 at 2.
        intros.
        assert (Hn' : n = 0) by eauto.
        revert Hremember1 Hremember2.
        match goal with
        | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] => revert H
        end.
        revert L Hn.
        generalize 0.
        intros.
        destruct L; try lia.
        rewrite<- ctx_zero_unfold.
        match goal with
        | [ H : HasTypeInstruction _ _ _ _ (LZero _ _ |[ _ ]|) _ _ |- _ ] =>
          rewrite<- ctx_zero_unfold in H
        end.
        rewrite<- ctx_zero_unfold in Hremember1.
        match goal with
        | [ H : context[_ ++ _ ++ _] |- _ ] =>
          eapply HasTypeInstruction_val_app2 in H;
          destruct H as [tausvs [S_vs [S_es [H20 [H21 H22]]]]]
        end.
        assert (Hwf : well_formed_Inst_list (es1 ++ l1) = true).
        { clear - Hremember1. revert es1 l1 Hremember1. induction l0; eauto. }
        match goal with
        | [ H : Reduce _ _ _ _ _ _ _ _ |- _ ] =>
          assert (H200 := after_reduction_is_surface _ _ _ _ _ _ _ _ _ H Hwf)
        end.
        match goal with
        | [ H : HasTypeInstruction _ _ _ _ (_ ++ _) _ _ |- _ ] =>
          eapply split_surface_typing in H; eauto;
          destruct H as [taus2 [L1 [H23 H24]]]
        end.
        match goal with
        | [ H : SplitStoreTypings [_; _] _,
            H' : SplitStoreTypings (_ :: _ ++ _) _ |- _ ] =>
          assert (IH1 := ignore_label_vs _ _ _ _ _ _ H H')
        end.
        assert (IH := IHReduce f (l ++ tausvs) taus2 o S_es (S_ignore ++ [S_vs]) Ss L0 C L1).
        repeat match goal with
               | [ H : ?A -> _, H' : ?A |- _ ] => specialize (H H')
               end.
        destruct IH as [S' [Sp' [Sh' [S_stack' [Ss' [L'' [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 H38]]]]]]]]]]]]]].
        match goal with
        | [ H : context[map _ (_ ++ _)] |- _ ] =>
          rewrite map_app in H; simpl in H;
          eapply remember_label_vs in H;
          destruct H as [S_stack'' [H40 H41]]
        end.
        exists S'. exists Sp'. exists Sh'. eexists S_stack''. exists Ss'. exists L''.
        split; [eassumption |].
        split; [eassumption |].
        split; [eassumption |].
        split; [| split; [eassumption | split]]; eauto.
        eapply HasTypeInstruction_app; eauto.
        eapply HasTypeInstruction_grow_unr.
        { clear - H22 H5 H2 H36.
          invert H2. invert H5. invert H22.
          invert H. invert H1. invert H4.
          destruct H9. destruct H11. destruct H13.
          rewrite<- H15. rewrite<- H11. rewrite<- H8.
          eassumption.
        }
        assert (H50 := HasTypeInstruction_val_local_agnostic _ _ _ _ L'' _ _ H20).
        eapply HasTypeInstruction_val_frame_agnostic in H50.
        eassumption.
        eapply HasTypeInstruction_FirstLocalValid; eauto.

        eapply proj1.
        eapply Forall_app.
        eapply HasTypeInstruction_InputTypesValid; eauto.
        eapply (HasTypeInstruction_grow_unr _ S_stack') in H24.
        2: {
          clear - H36 IH1 H2 H30 H40 H41.
          invert H2. invert IH1.
          invert H. invert H1.
          destruct H6. destruct H8.
          destruct S_es; simpl; simpl in *.
          rewrite<- H8. rewrite<- H5.
          clear - H30 H40 H41 H36.
          invert H30. invert H40. invert H41.
          invert H. invert H1. invert H3. invert H12.
          destruct H13. destruct H7. destruct H9.
          rewrite<- H6. rewrite<- H15. rewrite<- H13.
          exact H36.
        }
        
        eapply HasTypeInstruction_app; eauto.
        assert (H60 : (update_unr (UnrTyp S_stack') (empty_LinTyp S_es) = empty_LinTyp S_stack')).
        { clear - H36 H37 H30 H40 H41 H2 IH1.
          invert H2. invert H. clear H2 H H0 H5. destruct H4.
          invert IH1. invert H1. clear IH1 H1 H2 H6. destruct H5.
          invert H30. invert H3. clear H30 H3 H4 H8. destruct H7.
          invert H40. invert H5. clear H40 H5 H6 H10. destruct H9.
          invert H41. invert H7. invert H12. clear H41 H7 H8 H11 H12 H14. destruct H13.
          unfold update_unr.
          destruct S_es; destruct S_stack'; simpl; simpl in *; f_equal.
          {rewrite<- H7. rewrite<- H5. rewrite<- H3. rewrite<- H37. rewrite H. rewrite H1. congruence. }
        }
        rewrite H60.
        eapply SplitStoreTypings_EmptyHeapTyping_r.
      + assert (Hn : (Datatypes.S k) = (Datatypes.S k)) by congruence. revert L Hn H7 Hremember1 Hremember2. generalize (Datatypes.S k) at 2.
        intros.
        assert (Hn' : n = Datatypes.S k) by eauto.
        revert L Hn H7 Hremember1 Hremember2. generalize (Datatypes.S k).
        intros.
        destruct L; try lia.
        assert (k = k0) by lia.
        subst.
        rewrite<-  ctx_k_unfold in H7.
        rewrite<-  ctx_k_unfold in Hremember1.
        eapply HasTypeInstruction_val_app2 in H7.
        destruct H7 as [tausvs [S_vs [S_es [H20 [H21 H22]]]]].
        assert (Hwf : well_formed_Inst_list ([Label n0 a l1 (L |[ es1 ]|)] ++ l2) = true).
        { clear - Hremember1. revert es1 l1 Hremember1. induction l0; eauto. }
        simpl in Hwf.
        eapply split_surface_typing in H21; eauto.
        destruct H21 as [taus2 [L1 [H23 H24]]].
        assert (IH1 := ignore_label_vs _ _ _ _ _ _ H22 H5).
        eapply Label_HasTypeInstruction in H23.
        destruct H23 as [t [t1' [t2' [qf [L2 [H30 [H31 [H32 [H33 [H34 [H35 [H37 [H38 H39]]]]]]]]]]]]].
        simpl in *.
        destructAll.
        assert (Hrw : (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) (update_label_ctx ((t1', L2) :: label (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f))) (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) = (update_ret_ctx o (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) (update_label_ctx ((t1', L2) :: label (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f))) (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))))) by (destruct f; simpl; congruence).
        simpl in *.
        match type of Hrw with
        | ?A = _ =>
            match goal with
            | [ H : context[A] |- _ ] =>
                rewrite Hrw in H; clear Hrw;
                assert (IH := IHk _ _ _ (S_ignore ++ [S_vs]) _ _ _ H)
            end
        end.
        edestruct IH; eauto.
        { clear - Hf_empty. invert Hf_empty. destruct f; unfold Function_Ctx_empty; simpl; simpl in *. eauto. }
        { eapply HasTypeLocals_Function_Ctx; [ | | | | exact H6]; destruct f; simpl; eauto. }
        { clear - Hremember2. simpl in Hremember2. rewrite forallb_app in Hremember2. simpl in Hremember2. do 4 do_bools. eassumption. }
        { clear - Hremember2. simpl in Hremember2. rewrite forallb_app in Hremember2. simpl in Hremember2. do 4 do_bools. eassumption. }
        match goal with
        | [ H : exists _, _ |- _ ] =>
            destruct H as [Sp' [Sh' [S_stack' [Ss' [L'' [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 H48]]]]]]]]]]]]]
        end.
        rewrite map_app in H43.
        simpl in H43.
        eapply remember_label_vs in H43.
        destruct H43 as [S_stack'' [H50 H51]].
        exists x. exists Sp'. exists Sh'. exists S_stack''. exists Ss'. exists L''.
        split; [eassumption |].
        split; [eassumption |].
        split; [eassumption |].
        split; [eassumption |].
        split; [| split; [|split; [eassumption | split; eassumption]]]; eauto.
        eapply HasTypeLocals_Function_Ctx; [ | | | | exact H44]; destruct f; simpl; eauto.
        simpl.
        subst.
        eapply HasTypeInstruction_app_val; [exact H51 | | ].
        { eapply (HasTypeInstruction_grow_unr _ x) in H20.
          2 : { clear - H22 H5 H2 H46.
                invert H2. invert H5. invert H22.
                invert H. invert H1. invert H4.
                destruct H9. destruct H11. destruct H13.
                rewrite<- H15. rewrite<- H11. rewrite<- H8.
                eassumption.
          }
          eapply HasTypeInstruction_val_local_agnostic.
          exact H20.
          repeat match goal with
                 | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] =>
                   show_tlvs H; clear H
                 end.
          destruct f; subst; simpl in *; solve_lcvs.
        }
        assert (Hes_subset : map_util.sub_map (UnrTyp (empty_LinTyp S_es)) (UnrTyp S_stack')).
        { clear - H46 IH1 H2 H50 H51 H40.
          invert H2. invert H. clear H H0 H5 H2. destruct H4.
          invert IH1. invert H1. clear IH1 H1 H2 H6. destruct H5.
          invert H40. invert H3. clear H40 H3 H4 H8. destruct H7.
          invert H50. invert H5. clear H50 H5 H6 H10. destruct H9.
          invert H51. invert H7. invert H12. clear H51 H7 H8 H11 H12 H14. destruct H13.
          destruct S_es. destruct S_stack'. simpl; simpl in *. 
          rewrite<- H8. rewrite<- H6. rewrite<- H4. rewrite<- H2. rewrite<- H0. exact H46.
        }
        eapply (HasTypeInstruction_grow_unr _ S_stack') in H24; eauto.
        eapply (HasTypeInstruction_grow_unr _ S_stack') in H7; eauto.
        assert (Hrw : (update_unr (UnrTyp S_stack') (empty_LinTyp S_es) = empty_LinTyp S_stack')).
        { clear - IH1 H2 H46 H47 H50 H51 H40.
          invert H2. invert H. clear H H0 H5 H2. destruct H4.
          invert IH1. invert H1. clear IH1 H1 H2 H6. destruct H5.
          invert H40. invert H3. clear H40 H3 H4 H8. destruct H7.
          invert H50. invert H5. clear H50 H5 H6 H10. destruct H9.
          invert H51. invert H7. invert H12. clear H51 H7 H8 H11 H12 H14. destruct H13.
          destruct S_es. destruct S_stack'. unfold update_unr. simpl; simpl in *. f_equal.
          rewrite<- H7. rewrite<- H5. rewrite<- H3. rewrite<- H47. rewrite H. rewrite H1. congruence.
        }
        rewrite Hrw in H24.
        match type of Hrw with
        | ?A = _ =>
            match goal with
            | [ H : context[A] |- _ ] =>
                rewrite Hrw in H; clear Hrw
            end
        end.
        eapply HasTypeInstruction_cons; [| exact H24].
        assert (Hrw : (l ++ tausvs) = ((l ++ tausvs) ++ [])) by (rewrite app_nil_r; eauto).
        rewrite Hrw at 1.
        clear Hrw.
        eapply FrameTyp; [ | exact H34 | exact H35 | | | | ].
        congruence.
        eapply (CtxCongr _ _ _ _ _ _ _ _ k0) in H9.
        let H' := fresh "H" in
        assert (H' : exists S_rest, SplitStoreTypings (S_es :: [S_rest] ++ Ss) Sp) by (clear - H22 H5; eapply ignore_rest_of_stack; eauto);
        destruct H' as [H202 H203].
        let H' := fresh "H" in
        assert (H' : exists S_rest, SplitStoreTypings (S_stack' :: [S_rest] ++ Ss') Sp') by (eapply ignore_rest_of_stack; eauto);
        destruct H' as [H200 H201].
        assert (H204 : well_formed_Inst_list (L |[ es1 ]|) = true).
        { clear - Hremember2.
          simpl in *.
          rewrite forallb_app in Hremember2.
          do_bools.
          simpl in H0.
          do_bools.
          do_bools.
          do_bools.
          eassumption.
        }
        assert (H205 : forallb well_formed_Inst (L |[ es1 ]|) = true).
        { clear - Hremember2.
          simpl in *.
          rewrite forallb_app in Hremember2.
          do_bools.
          simpl in H0.
          do_bools.
          do_bools.
          do_bools.
          eassumption.
        }

        (*)
        assert (Htl := reduce_preserves_local_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H41 H203 H201 H6 H44 H38 H45 H9 H204 H205).
        rewrite<- Htl.
*)

        eapply ChangeEndLocalTyp; [ | apply LCEffEqual_sym; eauto | ].
        {
          eapply HasTypeInstruction_FirstLocalValid; eauto.
        }
        eapply LabelTyp.
        3:{
          eapply ChangeBegLocalTyp; [ eauto | eauto | ].
          eapply ChangeEndLocalTyp; [ eauto | eauto | ].
          match goal with
          | [ H : HasTypeInstruction ?S _ ?F _ _ _ _
              |- HasTypeInstruction ?S2 _ ?F _ _ _ _ ] =>
              replace S2 with S; [ exact H | ]
          end.
          unfold update_unr.
          do 2 match goal with
          | [ |- context[empty_LinTyp ?S] ] => destruct S; simpl
          end.
          simpl in *.
          repeat  match goal with
          | [ H : SplitStoreTypings [_; _] _ |- _ ] => inv H
            end.
          simpl in *.
          repeat match goal with
                 | [ H : Forall _ [_; _] |- _ ] => inv H
                 | [ H : Forall _ [_] |- _ ] => inv H
                 end.
          destructAll.
          simpl in *.
          subst.
          match goal with
          | [ H : ?A = ?B, H' : ?C = ?B |- _ ] =>
              rewrite H'; rewrite <-H
          end.
          auto.
        }
        1:{ eauto. }
        assert (Hrw : (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) (update_label_ctx ((t1', L2) :: label (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f))) (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) = (update_ret_ctx o (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))) (update_label_ctx ((t1', L2) :: label (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f))) (update_linear_ctx (set_hd qf (linear (update_ret_ctx o f))) (update_ret_ctx o f)))))).
        { destruct f; simpl. congruence. }
        rewrite Hrw.
        eapply ChangeEndLocalTyp; [ | destruct f; subst; simpl in *; eauto | ].
        { destruct f; eapply LocalCtxValid_Function_Ctx; eauto. }
        exact H45.

        repeat match goal with
               | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] =>
                 show_tlvs H; clear H
               end.
        destruct f; simpl in *; rewrite get_set_hd; auto.
        destruct f; simpl in *; auto.
        destruct f; simpl in *; auto.
        eapply proj1.
        eapply Forall_app.
        eapply HasTypeInstruction_InputTypesValid; eauto.
    - simpl in H0.
      do_bools.
      do_bools.
      specialize (HasTypeInstruction_QualValid H7).
      intro Hqvalid.
      specialize (HasTypeInstruction_TypeAndLocalValid H7).
      intro Hvalid.
      destruct Hvalid as [Hv1 [Hv2 [Hv3 Hv4]]].
      eapply Local_HasTypeInstruction in H7. destructAll.
      invert H13.
      assert (H100 := ignore_local_vs _ _ _ _ _ _ H15 H5).
      assert (H101 : InstTyp S_stack = InstTyp Sp).
      { clear - H5. eapply SplitStoreTypings_cons_InstTyp in H5. eassumption. }
      rewrite H101 in H12.
      assert (IH_1 : get_hd (linear (update_ret_ctx (Some x) F)) = Unrestricted) by eauto.
      assert (IH_2 : Forall (fun '(QualT _ q) => QualLeq (qual (update_ret_ctx (Some x) F)) q Unrestricted = Some true) []) by eauto.
      assert (IH_3 : QualLeq (qual (update_ret_ctx (Some x) F)) Unrestricted Unrestricted= Some true) by eapply QualLeq_Refl.
      eapply HasTypeLocals_ret_ctx in H16.
      assert (IH_4 : Function_Ctx_empty F) by (unfold Function_Ctx_empty; eauto).
      assert (Hloc' : LCHasSizes L0 szs1).
      { apply LCHasSizes_trivial; auto. }
      assert (IH := IHReduce _ _ _ (Some x) S_stack0 (S_ignore ++ Ss) Ss0 _ _ _ IH_4 Hloc' H18 H16 H100 H12 H3 H2 H11 H0 H).
      destruct IH as [S' [Sp' [Sh' [S_stack' [Ss' [L'' [IH1 [IH2 [IH3 [IH4 [IH5 [IH6 [IH7 [IH8 IH9]]]]]]]]]]]]]].
      rewrite map_app in IH4.
      simpl in IH4.
      assert (H102 := remember_local_vs _ _ _ _ _ IH4).
      destruct H102 as [S_stack'' [H102 H103]].
      exists S'. exists Sp'. exists Sh'. exists S_stack''. exists (map (update_unr (UnrTyp S')) Ss). exists L'.
      split; [eassumption |].
      split; [eassumption |].
      split.
      { clear - IH1 H2 H4 IH8.
        eapply SplitStoreTypings_cons_InstTyp in H2.
        eapply SplitStoreTypings_cons_InstTyp in IH1.
        rewrite IH1.
        rewrite<- IH8.
        rewrite<- H2.
        eassumption.
      }
      split; [eassumption |].
      split.
      { clear - H6 H5 H2 IH7 H14.
        destruct S. destruct S'. simpl. simpl in *.
        assert (H : Forall (fun S => typing.UnrTyp S = UnrTyp) Ss).
        { clear - H5 H2.
          invert H2. invert H. destruct H4. simpl in *.
          rewrite H3. clear - H5.
          invert H5.
          invert H.
          eapply Forall_app in H4.
          destruct H4.
          clear - H2.
          revert Sp H2.
          induction Ss; intros; eauto.
          invert H2.
          invert H1.
          eapply IHSs in H3.
          eapply Forall_cons; eauto.
        }
        clear - H6 IH7 H H14.
        eapply HasTypeLocals_grow_unr; eauto.
        eapply LCEffEqual_HasTypeLocals; eauto.
      }
      split.
      2: {
        split; [eassumption |].
        split; try eassumption.
        eapply LCSizeEqual_LCHasSizes; eauto.
        apply LCEffEqual_LCSizeEqual.
        destruct f; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
      }
      rewrite<- (app_nil_r l) at 1.
      eapply (FrameTyp _ _ _ _ _ Linear); eauto.
      { eapply Forall_trivial; intros. destruct x0. eapply QualLeq_Top. }
      { eapply QualLeq_Top. }
      eapply LocalTyp; eauto.
      specialize (LCHasSizes_exists IH9).
      intros; destructAll.
      eapply ConfTypFull.
      6:{
        eapply ChangeBegLocalTyp.
        - eapply LCEffEqual_closed_sizes_LocalCtxValid; eauto.
          eapply HasTypeInstruction_FirstLocalValid; eauto.
        - unfold empty_Function_Ctx; simpl; eauto.
        - eauto.
      }
      all: eauto.
      -- eapply SplitStoreTypings_cons_InstTyp in H102.
         rewrite H102.
         eassumption.
      -- eapply HasTypeLocals_ret_ctx; eauto.
         eapply LCEffEqual_HasTypeLocals; eauto.
      -- destruct f; subst; simpl in *; solve_lcvs.
      -- destruct f; subst; simpl in *; solve_tvs.
      -- destruct f; simpl; rewrite get_set_hd; econstructor; eauto.
      -- econstructor; eauto.
    - exists S. exists Sp. exists Sh. exists S_stack. exists Ss. exists L.
      split; eauto.
      split; eauto.
      split; eauto.
      assert (Hrw : (map (update_unr (UnrTyp S)) S_ignore) = S_ignore).
      { clear - H5 H2.
        invert H2. invert H. destruct H4. rewrite H3.
        clear - H5.
        invert H5.
        invert H.
        clear - H4.
        revert Sp Ss H4.
        induction S_ignore; intros; eauto.
        invert H4.
        eapply IHS_ignore in H2.
        destruct H1.
        simpl.
        f_equal; eauto.
        destruct a; unfold update_unr; simpl; simpl in *.
        rewrite H0; congruence.
      }
      rewrite Hrw.
      clear Hrw.
      split; eauto.
      split; eauto.
      split; [| split; [eapply Included_refl |]; eauto].
      eapply Preservation_reduce_simpl; eauto.
      eapply SplitStoreTypings_cons_InstTyp in H5.
      rewrite H5; eauto.
      unfold Function_Ctx_empty in Hf_empty; destruct f; eauto.
      unfold In.
      eapply map_util.sub_map_refl.
    - assert (Hf'_empty : Function_Ctx_empty (update_ret_ctx o f)) by (invert Hf_empty; destruct f; simpl; eauto).
      assert (H_locs : HasTypeLocals (update_ret_ctx o f) Ss vs1 L).
      { eapply HasTypeLocals_Function_Ctx; [| | | | exact H6]; destruct f; eauto. }
      apply Preservation_Reduce_full_eqv in X.
      destruct (Preservation_reduce_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hf'_empty H3 H4 H5 H7 H_locs X) as [Sp' [Sh' [Sstack' [Ss' [L'' [H20 [H21 [H22 [H23 [H24 [[H25 H50] H26]]]]]]]]]]].
      invert H20.
      exists S0. exists Sp'. exists Sh'. exists Sstack'. exists Ss'. exists L''.
      split; eauto.
      split; eauto.
      split; eauto.
      split; [invert H9; invert H12; destruct H16; rewrite H15; eassumption|].
      split.
      { eapply HasTypeLocals_Function_Ctx; [| | | | exact H23]; destruct f; eauto. }
      split; eauto.
      split; [invert H2; invert H9; invert H12; invert H14; destruct H18; destruct H27; rewrite H17; rewrite H27; eassumption |].
      split; [invert H2; invert H9; invert H12; invert H14; destruct H18; destruct H27; rewrite H16; rewrite H18; eassumption |].
      clear - H26 H8.
      eapply LCSizeEqual_LCHasSizes; eauto.
      Unshelve.
      eassumption.
  Qed.

  Lemma SplitStoreTypings_add_ignore  Sprog S_stack Ss:
    SplitStoreTypings (S_stack :: Ss) Sprog ->
    SplitStoreTypings (S_stack :: [empty_LinTyp Sprog] ++ Ss) Sprog.
  Proof.
    intros.
    invert H.
    clear H.
    unfold SplitStoreTypings.
    split; [clear H1 | clear H0].
    - invert H0.
      do 2 (eapply Forall_cons; eauto).
      unfold InstTyp; destruct Sprog; simpl; eauto.
    - simpl in H1.
      invert H1.
      clear H1.
      unfold SplitHeapTypings.
      split; [clear H0 | clear H].
      + destruct Sprog; simpl.
        simpl in H.
        rewrite map_util.Dom_ht_empty.
        rewrite Union_Empty_set_neut_l.
        exact H.
      + intros.
        assert (H1 := H0 l ht H).
        clear - H1.
        destruct Sprog.
        simpl.
        invert H1; [eapply (typing.InHead); eauto; eapply (typing.NotInHead); eauto | eapply (typing.NotInHead); eauto; eapply (typing.NotInHead); eauto]; unfold map_util.get_heaptype; eapply M.gempty.
  Qed.

  Lemma SplitStoreTypings_drop_ignore Sprog Sprog' S_stack Ss:
    SplitStoreTypings (S_stack :: [empty_LinTyp Sprog'] ++ Ss) Sprog ->
    SplitStoreTypings (S_stack :: Ss) Sprog.
  Proof.
    intros.
    invert H. clear H.
    unfold SplitStoreTypings.
    split; [clear H1 | clear H0].
    - invert H0.
      eapply Forall_cons; eauto.
      invert H3; eauto.
    - simpl in H1.
      invert H1. clear H1.
      unfold SplitHeapTypings.
      split; [clear H0 | clear H].
      + destruct Sprog; destruct Sprog'; simpl.
        simpl in H.
        rewrite map_util.Dom_ht_empty in H.
        rewrite Union_Empty_set_neut_l in H.
        exact H.
      + intros.
        assert (H1 := H0 l ht H).
        clear - H1.
        destruct Sprog'.
        simpl. simpl in H1.
        invert H1. invert H6.
        eapply (typing.InHead); eauto.
        eapply (typing.NotInHead); eauto.
        invert H7; eauto.
        unfold map_util.get_heaptype in H3. rewrite M.gempty in H3. discriminate.
  Qed.

  Lemma empty_LinTyp_swap S S':
    UnrTyp S = UnrTyp S' ->
    InstTyp S = InstTyp S' ->
    empty_LinTyp S = empty_LinTyp S'.
  Proof.
    intros.
    destruct S. destruct S'. simpl. simpl in *.
    rewrite H. rewrite H0.
    congruence.
  Qed.

  Theorem Preservation :
    forall S i s vs szs es taus s' vs' es',
      HasTypeConfig S i s vs szs es taus ->
      well_formed_Store s = true ->
      forallb well_formed_Inst es = true ->
      well_formed_Inst_list es = true ->
      Reduce s vs szs es i s' vs' es' ->
      well_formed_Store s' = true /\
      forallb well_formed_Inst es' = true /\
      well_formed_Inst_list es' = true /\
      exists S',
        HasTypeConfig S' i s' vs' szs es' taus.
    Proof.
      intros.
      split; [|split]; [| |split].
      - clear - H3 H0.
        revert H0.
        induction H3; eauto.
        intros.
        eapply reduce_full_preserves_inst in X.
        destruct s1.
        destruct s2.
        simpl.
        simpl in X.
        simpl in H0.
        clear - H0 X.
        revert inst1 H0 X.
        induction inst0; intros.
        + invert X.
          eauto.
        + invert X.
          invert H0.
          eapply andb_prop in H1.
          destruct H1.
          assert (IH := IHinst0 l' H1 H4).
          rewrite H.
          rewrite H1.
          simpl.
          rewrite IH.
          rewrite Bool.andb_true_r.
          destruct a.
          destruct y.
          simpl.
          simpl in H2.
          simpl in H0.
          destruct H2.
          subst.
          eauto.
      - eapply Reduce_preserves_wf_Inst; try eapply WFPres_Reduce_eqv; eauto.
      - eapply Reduce_preserves_wf_Inst_list; try eapply WFPres_Reduce_eqv; eauto.
      - invert H.
        clear H.
        invert H6.
        clear H6.
        eapply SplitStoreTypings_add_ignore in H8.
        assert (Hlchszs : LCHasSizes L szs).
        { apply LCHasSizes_trivial; auto. }
        assert (H100 := Preservation_general _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H4 H5 H7 H8 H9 H11 Hlchszs H3).
        destruct H100 as [S' [Sp' [Sh' [S_stack' [Ss' [L'' [H100 [H101 [H102 [H103 [H104 [H105 [H106 [H107 H108]]]]]]]]]]]]]].
        exists S'.
        eapply ConfTyp; eauto.
        simpl in H103.
        rewrite update_unr_empty_lintyp_swap in H103.
        eapply SplitStoreTypings_drop_ignore in H103.
        specialize (LCHasSizes_exists H108).
        intros; destructAll.
        eapply ConfTypFull.
        6:{
          eapply ChangeBegLocalTyp.
          - eapply LCEffEqual_closed_sizes_LocalCtxValid; eauto.
            eapply HasTypeInstruction_FirstLocalValid; eauto.
          - unfold empty_Function_Ctx; simpl; eauto.
          - eauto.
        }
        all: eauto.
        eapply LCEffEqual_HasTypeLocals; eauto.
  Qed.

  Theorem Soundness_full :
    forall S i s vs szs es taus s' vs' es' n,
      HasTypeConfig S i s vs szs es taus ->
      well_formed_Store s = true ->
      well_formed_Inst_list es = true ->
      forallb well_formed_Inst es = true ->
      Red_Star n s vs szs es i s' vs' es' ->
      Forall (fun e => exists v, e = Val v) es' \/
      es' = [Trap] \/
      exists s'' vs'' es'', Reduce s' vs' szs es' i s'' vs'' es''.
  Proof.
    intros.
    revert S H.
    induction H3.
    - intros.
      match goal with
      | [ |- context G[Reduce] ] =>
        let goal := context G[Progress.Red.Reduce] in
        assert (Hgoal : goal)
      end.
      { eapply Progress; eassumption. }
      case Hgoal; eauto.
      intro Hgoal'; case Hgoal'; eauto.
      intros; destructAll.
      right; right.
      do 3 eexists; eapply Progress_Reduce_eqv; eauto.
    - intros.
      invert H.
      + destruct (Preservation _ _ _ _ _ _ _ _ _ _ H4 H0 H2 H1 H5) as [H10 [H11 [H12 H13]]].
        destruct H13.
        eapply IHRed_Star; eassumption.
      + invert H4.
        invert H8.
        apply Preservation_GC_step_eqv in H5.
        destruct (Preservation_reduce_GC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H7 H11 H12 H14 H10 H5) as [Sh' [Sp' [S_stack' [Ss' [H20 [H21 [H22 [H23 H24]]]]]]]].
        invert H24.
        eapply IHRed_Star; eauto.
        * clear - H0 H5.
          invert H5.
          unfold well_formed_Store.
          unfold s'0.
          clear - H0.
          destruct s.
          simpl.
          simpl in H0.
          assumption.
        * eapply ConfTyp; eauto.
          eapply ConfTypFull; eauto.
  Qed.

  Theorem Soundness :
    forall S i s vs szs es taus s' vs' es' n,
      HasTypeConfig S i s vs szs es taus ->
      well_formed_Store s = true ->
      forallb surface_Inst es = true ->
      Red_Star n s vs szs es i s' vs' es' ->
      Forall (fun e => exists v, e = Val v) es' \/
      es' = [Trap] \/
      exists s'' vs'' es'', Reduce s' vs' szs es' i s'' vs'' es''.
  Proof.
    intros.
    assert (es = [] \/ es <> []) by (destruct es; eauto; right; unfold "<>"; intro; discriminate).
    destruct H3; try (subst; clear - H2; eapply Red_Star_nil in H2; subst; eauto).
    assert (Hwfa := surface_Inst_is_well_formed_Inst_list es H1).
    assert (Hwfb := forallb_surface_Inst_is_well_formed_Inst es H1).
    eapply Soundness_full; eauto.
  Qed.

  (* Print Assumptions Soundness. *)

End Safety.
