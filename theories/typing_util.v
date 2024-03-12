From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Sets.Ensembles Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.tactics RWasm.list_util
        RWasm.map_util RWasm.EnsembleUtil RWasm.splitting RWasm.surface RWasm.debruijn RWasm.subst.

(* Used in preservation_full *)
Definition Function_Ctx_empty (F : Function_Ctx) :=
  qual F = [] /\ size F = [] /\ type F = [] /\ location F = 0.

Section StoreEq.
  Lemma HasTypeValue_StoreTyping_eq S1 S2 F v tau :
      HasTypeValue S1 F v tau ->
      StoreTyping_eq S1 S2 ->
      HasTypeValue S2 F v tau.
  Proof.
    intros Htyp Hseq. assert (Hseq' := Hseq). destruct Hseq as [Heq1 [Heq2 Heq3]].
    induction Htyp; simpl in *;
      try now (econstructor; eauto; now erewrite <- is_empty_eq_map; eauto).
    - econstructor; eauto.
      eapply SplitStoreTyping_eq; eauto.
    - econstructor; eauto.
      now erewrite <- is_empty_eq_map; eauto.
      congruence.
    - econstructor; eauto.
      eapply eq_map_trans. eapply eq_map_sym. eassumption.
      eassumption.
    - econstructor; eauto.
      eapply eq_map_trans. eapply eq_map_sym. eassumption.
      eassumption.
    - econstructor; eauto.
      now erewrite <- is_empty_eq_map; eauto.
      congruence.
  Qed.

  Lemma HasHeapType_StoreTyping_eq S1 S2 F hv ht :
    HasHeapType S1 F hv ht ->
    StoreTyping_eq S1 S2 ->
    HasHeapType S2 F hv ht.
  Proof.
    intros Hhtyp Hseq. assert (Hseq' := Hseq). destruct Hseq as [Heq1 [Heq2 Heq3]].
    induction Hhtyp; simpl in *;
      econstructor; eauto using SplitStoreTyping_eq, HasTypeValue_StoreTyping_eq.
  Qed.


  Definition PHasTypeInstruction S1 M F L1 es tau L2 :=
    (forall S2 (Hseq : StoreTyping_eq S1 S2),
        HasTypeInstruction S2 M F L1 es tau L2).

  Definition PHasTypeClosure S1 c ft :=
    (forall S2 (Hseq: StoreTyping_eq S1 S2),
        HasTypeClosure S2 c ft).

  Definition PHasTypeFunc S1 M F exs ft :=
    (forall S2 (Hseq : StoreTyping_eq S1 S2),
        HasTypeFunc S2 M F exs ft).

  Definition PHasTypeConf S1 taus i vs szs is taus' :=
    (forall S2 (Hseq: StoreTyping_eq S1 S2),
        HasTypeConf S2 taus i vs szs is taus').

  Global Instance empty_LinTyp_Proper :
    Proper (StoreTyping_eq ==> StoreTyping_eq) empty_LinTyp.
  Proof.
    intros S1 S2 Heq.
    destruct S1; destruct S2. destruct Heq. destructAll. simpl in *.
    split; eauto. split; eauto.
    simpl. eapply eq_map_refl.
  Qed.

  Lemma HasTypeInstruction_StoreTyping_eq_and :
    (forall S1 M F L1 es tau L2,
        HasTypeInstruction S1 M F L1 es tau L2 ->
        PHasTypeInstruction S1 M F L1 es tau L2) /\
      (forall S1 c ft,
          HasTypeClosure S1 c ft ->
          PHasTypeClosure S1 c ft) /\
      (forall S1 M F exs ft,
          HasTypeFunc S1 M F exs ft ->
          PHasTypeFunc S1 M F exs ft) /\
      (forall S1 taus i vs szs is taus',
          HasTypeConf S1 taus i vs szs is taus' ->
          PHasTypeConf S1 taus i vs szs is taus').
  Proof.
    eapply HasType_Instruction_Closure_Func_Conf_mind
      with (PHasTypeInstruction := PHasTypeInstruction)
           (PHasTypeClosure := PHasTypeClosure)
           (PHasTypeFunc := PHasTypeFunc)
           (PHasTypeConf := PHasTypeConf);
      unfold PHasTypeInstruction, PHasTypeClosure, PHasTypeFunc, PHasTypeConf; intros;
      try (assert (Hseq' := Hseq); destruct Hseq as [Heq1 [Heq2 Heq3]]);
      try now (econstructor; eauto; now erewrite <- is_empty_eq_map; eauto).
    - econstructor; auto. eapply HasTypeValue_StoreTyping_eq; eauto.
    - econstructor; eauto.
      now erewrite <- is_empty_eq_map; eauto.
      revert H3 H2 Hseq'. clear.
      intros Hall1 Hall2 Heq.
      induction Hall1; simpl in *; eauto.
      inv Hall2. constructor; eauto.
    - econstructor; eauto.
      now erewrite <- is_empty_eq_map; eauto.
      revert H0 H1 Hseq'. clear.
      intros Hall1 Hall2 Heq.
      induction Hall1; simpl in *; eauto.
      inv Hall2. constructor; eauto.
    - econstructor; eauto.
      assert (H' : empty_LinTyp S = empty_LinTyp S2).
      { unfold empty_LinTyp.
        destruct S; subst; simpl in *.
        destruct S2; subst; simpl in *; auto. }
      rewrite <-H'; auto.
    - econstructor; eauto.
      eapply HasHeapType_StoreTyping_eq; eauto.
    - econstructor; eauto.
      eauto using SplitStoreTyping_eq.
    - econstructor; eauto. congruence.
    - econstructor; eauto. congruence.
      eauto using SplitStoreTyping_eq.
  Qed.

  Lemma HasTypeInstruction_StoreTyping_eq S1 S2 M F L1 es tau L2:
    HasTypeInstruction S1 M F L1 es tau L2 ->
    StoreTyping_eq S1 S2 ->
    HasTypeInstruction S2 M F L1 es tau L2.
  Proof. intros. eapply HasTypeInstruction_StoreTyping_eq_and; eauto. Qed.

  Lemma HasTypeClosure_StoreTyping_eq S1 S2 c ft :
    HasTypeClosure S1 c ft ->
    StoreTyping_eq S1 S2 ->
    HasTypeClosure S2 c ft.
  Proof. intros. eapply HasTypeInstruction_StoreTyping_eq_and; eauto. Qed.

  Lemma HasTypeConf_StoreTyping_eq S1 S2 taus i szs vs is taus' :
    HasTypeConf S1 taus i szs vs is taus' ->
    StoreTyping_eq S1 S2 ->
    HasTypeConf S2 taus i szs vs is taus'.
  Proof. intros. eapply HasTypeInstruction_StoreTyping_eq_and; eauto. Qed.



  Global Instance Proper_HasTypeInstruction :
    Proper (StoreTyping_eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) HasTypeInstruction.
  Proof.
    repeat (intro; intros); subst.
    split; intros H1; eapply HasTypeInstruction_StoreTyping_eq; eauto.
    unfold StoreTyping_eq in *.
    destructAll. split; eauto. split; eauto. eapply eq_map_sym; eassumption.
  Qed.

  Global Instance Proper_HasTypeValue :
    Proper (StoreTyping_eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) HasTypeValue.
  Proof.
    repeat (intro; intros); subst.
    split; intros H1; eapply HasTypeValue_StoreTyping_eq; eauto.
    unfold StoreTyping_eq in *.
    destructAll. split; eauto. split; eauto. eapply eq_map_sym; eassumption.
  Qed.


  Global Instance Proper_HasHeapType :
    Proper (StoreTyping_eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) HasHeapType.
  Proof.
    repeat (intro; intros); subst.
    split; intros H1; eapply HasHeapType_StoreTyping_eq; eauto.
    unfold StoreTyping_eq in *.
    destructAll. split; eauto. split; eauto. eapply eq_map_sym; eassumption.
  Qed.



  Global Instance Proper_HasTypeClosure :
    Proper (StoreTyping_eq ==> Logic.eq ==> Logic.eq ==> iff) HasTypeClosure.
  Proof.
    repeat (intro; intros); subst.
    split; intros H1; eapply HasTypeClosure_StoreTyping_eq; eauto.
    unfold StoreTyping_eq in *.
    destructAll. split; eauto. split; eauto. eapply eq_map_sym; eassumption.
  Qed.


  Global Instance Proper_HasTypeConf :
    Proper (StoreTyping_eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           HasTypeConf.
  Proof.
    repeat (intro; intros); subst.
    split; intros H1; eapply HasTypeConf_StoreTyping_eq; eauto.
    unfold StoreTyping_eq in *.
    destructAll. split; eauto. split; eauto. eapply eq_map_sym; eassumption.
  Qed.


End StoreEq.

Ltac replace_heaptypevalid_parts label ret size type location :=
  match goal with
  | [ H : HeapTypeValid ?F _ |- _ ] =>
    replace label with (typing.label F) by ltac:(simpl; eauto); replace ret with (typing.ret F) by ltac:(simpl; eauto); replace size with (typing.size F) by ltac:(simpl; eauto); replace type with (typing.type F) by ltac:(simpl; eauto); replace location with (typing.location F) by ltac:(simpl; eauto)
  end.

Ltac replace_typevalid_parts label ret size type location :=
  match goal with
  | [ H : TypeValid ?F ?QUAL |- TypeValid _ ?QUAL ] =>
    replace label with (typing.label F) by ltac:(simpl; eauto); replace ret with (typing.ret F) by ltac:(simpl; eauto); replace size with (typing.size F) by ltac:(simpl; eauto); replace type with (typing.type F) by ltac:(simpl; eauto); replace location with (typing.location F) by ltac:(simpl; eauto)
  end.

Lemma LCEffEqual_nth_error_left : forall {C L L' idx tau sz},
    LCEffEqual C L L' ->
    nth_error L idx = Some (tau, sz) ->
    exists sz',
      nth_error L' idx = Some (tau, sz') /\
      SizeLeq C sz sz' = Some true /\
      SizeLeq C sz' sz = Some true.
  Proof.
    intros.
    generalize dependent idx.
    induction H; simpl; intros.
    - destruct idx; inversion H0.
    - destruct idx; inversion H1; subst; eauto.
      destruct y. destructAll.  simpl in *.
      eauto.
  Qed.

Lemma LCEffEqual_nth_error_right : forall {C L L' idx tau sz},
    LCEffEqual C  L L' ->
    nth_error L' idx = Some (tau, sz) ->
    exists sz',
      nth_error L idx = Some (tau, sz') /\
      SizeLeq C sz sz' = Some true /\
      SizeLeq C sz' sz = Some true.
  Proof.
    intros.
    generalize dependent idx.
    induction H; simpl; intros.
    - destruct idx; inversion H0.
    - destruct idx; inversion H1; subst; eauto.
      destruct x. destructAll. simpl in *.
      eauto.
  Qed.

Ltac use_LCEffEqual_nth_error_left :=
  match goal with
  | [ H : LCEffEqual _ ?L ?LP,
      H' : nth_error ?L _ = Some _ |- _ ] =>
    specialize (LCEffEqual_nth_error_left H H');
    intros; destructAll
  end.
Ltac use_LCEffEqual_nth_error_right :=
  match goal with
  | [ H : LCEffEqual _ ?L ?LP,
      H' : nth_error ?LP _ = Some _ |- _ ] =>
    specialize (LCEffEqual_nth_error_right H H');
    intros; destructAll
  end.

Ltac invert_arrow_eq :=
  match goal with
  | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
    inversion H; subst
  end.
Ltac destyp :=
  match goal with
  | [ X : Typ |- _ ] => destruct X
  end.

Ltac prepare_Forall :=
  rewrite Forall_forall;
  intros;
  repeat destyp;
  repeat match goal with
         | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
         end;
  simpl in *.

Section Utils.

  Hint Constructors HasTypeInstruction.
  Hint Constructors HasTypeValue.

  Lemma KindVarValid_Function_Ctx F kv (H : KindVarValid F kv) :
    forall F',
      qual F = qual F' ->
      size F = size F' ->
      KindVarValid F' kv.
  Proof. destruct kv; cbn; constructor; inv H; congruence. Qed.

  Lemma KindVarsValid_Function_Ctx F kvs (H : KindVarsValid F kvs) :
    forall F',
      qual F = qual F' ->
      size F = size F' ->
      KindVarsValid F' kvs.
  Proof.
    induction H.
    - constructor.
    - constructor.
      + eapply KindVarValid_Function_Ctx; eauto.
      + eapply IHKindVarsValid; destruct C, F', kv; cbn in *; congruence.
  Qed.

  Lemma add_constraints_eq F F' ls:
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    qual (add_constraints F ls) = qual (add_constraints F' ls) /\
    size (add_constraints F ls) = size (add_constraints F' ls) /\
    type (add_constraints F ls) = type (add_constraints F' ls) /\
    location (add_constraints F ls) = location (add_constraints F' ls).
  Proof.
    revert F F'; induction ls; intros F F' Heq1 Heq2 Heq3 Heq4;
      destruct F; destruct F'; simpl in *; subst; eauto.
    edestruct IHls with
      (F := (add_constraint
          {| label := label;
            ret := ret;
            qual := qual0;
            size := size0;
            type := type0;
            location := location0;
            linear := linear
          |} a))
    (F' := add_constraint
          {|
            label := label0;
            ret := ret0;
            qual := qual0;
            size := size0;
            type := type0;
            location := location0;
            linear := linear0
          |} a); eauto.
    - unfold add_constraint; destruct a; simpl; eauto.
    - unfold add_constraint; destruct a; simpl; eauto.
    - unfold add_constraint; destruct a; simpl; eauto.
    - unfold add_constraint; destruct a; simpl; eauto.
  Qed.

  Lemma TypesValid_rel_fields :
    (forall F t,
        TypeValid F t ->
        forall F',
          qual F = qual F' ->
          size F = size F' ->
          type F = type F' ->
          location F = location F' ->
          TypeValid F' t) /\
    (forall F t,
        HeapTypeValid F t ->
        forall F',
          qual F = qual F' ->
          size F = size F' ->
          type F = type F' ->
          location F = location F' ->
          HeapTypeValid F' t) /\
    (forall F t,
        ArrowTypeValid F t ->
        forall F',
          qual F = qual F' ->
          size F = size F' ->
          type F = type F' ->
          location F = location F' ->
          ArrowTypeValid F' t) /\
    (forall F t,
        FunTypeValid F t ->
        forall F',
          qual F = qual F' ->
          size F = size F' ->
          type F = type F' ->
          location F = location F' ->
          FunTypeValid F' t).
  Proof.
    eapply
      (TypesValid_ind'
         (fun F t =>
            forall F',
              qual F = qual F' ->
              size F = size F' ->
              type F = type F' ->
              location F = location F' ->
              TypeValid F' t)
         (fun F ht =>
            forall F',
              qual F = qual F' ->
              size F = size F' ->
              type F = type F' ->
              location F = location F' ->
              HeapTypeValid F' ht)
         (fun F atyp =>
            forall F',
              qual F = qual F' ->
              size F = size F' ->
              type F = type F' ->
              location F = location F' ->
              ArrowTypeValid F' atyp)
         (fun F ft =>
            forall F',
              qual F = qual F' ->
              size F = size F' ->
              type F = type F' ->
              location F = location F' ->
              FunTypeValid F' ft)).
    
    all: intros.
    all:
      match goal with
      | [ H : qual ?C = qual ?F,
          H' : size ?C = size ?F,
          H'' : type ?C = type ?F,
          H''' : location ?C = location ?F |- _ ] =>
        destruct C; subst; simpl in *;
        destruct F; subst; simpl in *
      end.
    all: try ltac:(econstructor; eauto).
    - rewrite Forall_forall in *. intros.
      eapply H1; eauto.
    - rewrite Forall_forall in *. intros.
      eapply H; eauto.
    - rewrite Forall_forall in *. intros.
      specialize (H _ H0).
      destructAll.
      exists x0. split; auto.
    - rewrite Forall_forall in *. intros.
      eapply H; eauto.
    - rewrite Forall_forall in *. intros.
      eapply H0; eauto.
    - clear H0.
      generalize dependent label.
      revert label0 ret ret0 qual0 size0 type0 location0 linear linear0.
      induction quants; simpl; intros; econstructor; inversion H; subst.
      + clear H H4 IHquants.
        generalize dependent label.
        revert label0 ret ret0 qual0 size0 type0 location0 linear linear0.
        induction a; simpl; intros; eauto.
      + destruct a; simpl in *; unfold subst'_function_ctx; simpl; eauto.
   - clear H.
     generalize dependent label.
      revert label0 ret ret0 qual0 size0 type0 location0 linear linear0.
     induction quants; simpl; auto. destruct a; simpl in *;
       unfold subst'_function_ctx in *; simpl in *; eauto.
 Qed.
    
  Lemma TypeValid_Function_Ctx : forall {F F' t},
      TypeValid F t ->
      qual F = qual F' ->
      size F = size F' ->
      type F = type F' ->
      location F = location F' ->
      TypeValid F' t.
  Proof.
    intros.
    specialize TypesValid_rel_fields; intros; destructAll.
    eauto.
  Qed.


  (** HasTypeValue lemmas *)


  Lemma HasTypeValue_Function_Ctx S F F' v tau :
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    HasTypeValue S F v tau ->
    HasTypeValue S F' v tau.
  Proof.
    revert S F F' tau.
    eapply Value_ind' with
        (P := fun v =>
                forall (S : StoreTyping) (F F' : Function_Ctx) (tau : Typ)
                       (Heq1 : qual F = qual F')
                       (Heq2 : size F = size F')
                       (Heq3 : type F = type F')
                       (Heq4 : location F = location F')
                       (Htyp : HasTypeValue S F v tau), HasTypeValue S F' v tau); intros; inv Htyp; eauto.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
      eapply H; eassumption.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
      eapply Forall3_monotonic_strong; [ | eassumption ].
      simpl. intros.
      eapply Forall_forall in H. eapply H; eassumption.
      destruct F; destruct F'; simpl in *. eassumption.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
      destruct F; destruct F'; simpl in *.
      subst. eassumption.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
      destruct F; destruct F'; simpl in *.
      subst. eassumption.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
      destruct F; destruct F'; simpl in *.
      subst. eassumption.
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto).
    - econstructor; try eassumption; try (eapply TypeValid_Function_Ctx; eauto); eauto.
      rewrite Heq4 in H2. auto.
  Qed.

  Lemma TypeValid_linear : forall F h li,
      TypeValid F h ->
      TypeValid {| label := label F; ret := ret F; qual := qual F; size := size F; type := type F; location := location F; linear := li |} h.
  Proof.
    intros.
    eapply TypeValid_Function_Ctx; simpl in *; auto; auto.
  Qed.

  Lemma HeapTypeValid_linear : forall F h li,
      HeapTypeValid F h ->
      HeapTypeValid {| label := label F; ret := ret F; qual := qual F; size := size F; type := type F; location := location F; linear := li |} h.
  Proof.
    intros.
    specialize TypesValid_rel_fields; intros; destructAll.
    eauto.
  Qed.

  Lemma TypeValid_QualLt F pt d d' :
    TypeValid F (QualT pt d) ->
    (forall (cap : cap) (l : Loc) (ht : HeapType),
        pt <> CapT cap l ht) ->
    (forall (cap : cap) (l : Loc) (ht : HeapType),
        pt <> RefT cap l ht) ->
    (forall n, pt <> TVar n) ->
    QualValid (qual F) d' ->
    QualLeq (qual F) d d' = Some true ->
    TypeValid F (QualT pt d').
    revert F d d'.
    induction pt; intros.
    - eapply TNumValid; eauto.
    - exfalso; eapply H2; eauto.
    - eapply TUnitValid; eauto.
    - eapply TProdValid; inv H; eauto.
      clear H0 H1 H2 H3 H7 H10.
      revert H9.
      induction l; eauto; intros.
      inv H9.
      eapply Forall_cons; eauto.
      destruct a.
      eapply QualLeq_Trans; eauto.
    - inv H; eapply TCoderefValid; eauto.
    - inv H. eapply TRecValid; eauto.
      eapply QualLeq_Trans. exact H10. exact H4.
    - inv H; eapply TPtrValid; eauto.
    - inv H; eapply TExLocValid; eauto.
      eapply QualLeq_Trans; eauto.
    - inv H; eapply TOwnValid; eauto.
      eapply QualLeq_Trans; eauto.
    - exfalso; eapply H0; eauto.
    - exfalso; eapply H1; eauto.
  Qed.


  Lemma HasTypeValue_QualLt S F v pt d d' :
    HasTypeValue S F v (QualT pt d) ->
    (forall (cap : cap) (l : Loc) (ht : HeapType),
        pt <> CapT cap l ht) ->
    (forall (cap : cap) (l : Loc) (ht : HeapType),
        pt <> RefT cap l ht) ->
    QualLeq (qual F) d d' = Some true ->
    QualValid (qual F) d' ->
    HasTypeValue S F v (QualT pt d').
  Proof.
    revert S F pt d d'.
    induction v using Value_ind'; intros; eauto;
    try now match goal with
            | [ H : HasTypeValue _ _ _ _ |- _ ] => inv H; econstructor; eauto; eapply TypeValid_QualLt; eauto
            end.
    - inv H; exfalso; eapply H1; reflexivity.
    - inv H; exfalso; eapply H0; reflexivity.
  Qed.


  Ltac HasTypeEauto :=
    match goal with
    | [ |- HasTypeInstruction _ _ _ _ [Block _ _ _] _ _ ] =>
      eapply BlockTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Loop _ _] _ _ ] =>
      eapply LoopTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ITE _ _ _ _] _ _ ] =>
      eapply ITETyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [term.Val _] _ _ ] =>
      eapply ValTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Get_local _ _] _ _ ] =>
      eapply GetlocalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Set_local _] _ _ ] =>
      eapply SetlocalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Tee_local _] _ _ ] =>
      eapply TeelocalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Get_global _] _ _ ] =>
      eapply GetglobalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Set_global _] _ _ ] =>
      eapply SetglobalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [CoderefI _] _ _ ] =>
      eapply CoderefTTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Call_indirect] _ _ ] =>
      eapply Call_indirectTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [term.Call _ _] _ _ ] =>
      eapply Call; eauto
    | [ |- HasTypeInstruction _ _ _ _ [RecFold _] _ _ ] =>
      eapply RecFoldType; eauto
    | [ |- HasTypeInstruction _ _ _ _ [RecUnfold] _ _ ] =>
      eapply RecUnfoldType; eauto
    | [ |- HasTypeInstruction _ _ _ _ [MemPack _] _ _ ] =>
      eapply MemPackTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [MemUnpack _ _ _] _ _ ] =>
      eapply MemUnpackTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [StructMalloc _ _] _ _ ] =>
      eapply StructMallocTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [StructGet _] _ _ ] =>
      eapply StructGetTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [StructSet _] _ _ ] =>
      eapply StructSetTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [StructSwap _] _ _ ] =>
      eapply StructSwapTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [VariantMalloc _ _ _] _ _ ] =>
      eapply VariantMallocTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [VariantCase _ _ _ _ _] _ _ ] =>
      try (eapply VariantCaseTypLin; eauto);
      try (eapply VariantCaseTypUnr; eauto)
    | [ |- HasTypeInstruction _ _ _ _ [ArrayMalloc _] _ _ ] =>
      eapply ArrayMallocTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ArrayGet] _ _ ] =>
      eapply ArrayGetTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ArraySet] _ _ ] =>
      eapply ArraySetTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ArrayFree] _ _ ] =>
      eapply ArrayFreeTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ExistPack _ _ _] _ _ ] =>
      eapply ExistPackTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [ExistUnpack _ _ _ _ _] _ _ ] =>
      try (eapply ExistUnpackTypUnr; eauto);
      try (eapply ExistUnpackTypLin; eauto)
    | [ |- HasTypeInstruction _ _ _ _ [CallAdm _ _] _ _ ] =>
      eapply CallAdmTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Label _ _ _ _] _ _ ] =>
      eapply LabelTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Malloc _ _ _] _ _ ] =>
      eapply MallocTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Free] _ _ ] =>
      eapply FreeTyp; eauto
    end.


  (** HasTypeInstruction lemmas *)

  Theorem HasType_Valid S F v t:
    HasTypeValue S F v t ->
    TypeValid F t.
  Proof.
    generalize dependent S.
    generalize dependent F.
    generalize dependent v.
    destruct t.
    induction p; intros; inversion H; subst; auto.
  Qed.

  Ltac solve_trivial_tlv_subgoal F :=
    rewrite Forall_forall;
    intros;
    destruct_prs;
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H;
      specialize (H _ H')
    end;
    destyp;
    eapply TypeValid_Function_Ctx; eauto;
    destruct F; subst; simpl in *; auto.

  Ltac start_tlv_goal :=
    unfold LocalCtxValid in *;
    match goal with
    | [ H : forall _ _, ?X = _ -> _, H' : ?X = _ |- _ ] =>
      specialize (H _ _ H')
    end;
    destructAll.
  
  Ltac solve_trivial_tlv_goal F :=
    start_tlv_goal;
    repeat split; solve_trivial_tlv_subgoal F.

  Lemma LocalCtxValid_set_localtype_provable : forall idx sz F L tau,
      LocalCtxValid F L ->
      TypeValid F tau ->
      LocalCtxValid F (set_localtype idx tau sz L).
  Proof.
    induction idx.
    - intros.
      destruct L; subst; unfold set_localtype; simpl in *; constructor; auto.
      inversion H; subst; auto.
    - intros.
      destruct L; subst; simpl in *; auto.
      unfold set_localtype.
      simpl.
      inversion H; subst.
      destruct_prs.
      constructor; auto.
      apply IHidx; auto.
  Qed.

  Lemma LocalCtxValid_set_localtype : forall {F L tau} idx sz,
      LocalCtxValid F L ->
      TypeValid F tau ->
      LocalCtxValid F (set_localtype idx tau sz L).
  Proof.
    intros.
    eapply LocalCtxValid_set_localtype_provable; eauto.
  Qed.

  Lemma LCEffEqual_Forall : forall {C L1 L2 P},
      LCEffEqual C L1 L2 ->
      Forall P L1 ->
      (forall t sz1 sz2,
          P (t, sz1) ->
          SizeLeq C sz1 sz2 = Some true ->
          SizeLeq C sz2 sz1 = Some true ->
          P (t, sz2)) ->
      Forall P L2.
  Proof.
    intros.
    induction H; auto.
    destruct x. destruct y. destructAll.
    inversion H0; subst.
    constructor; auto.
    eapply H1; eauto.
  Qed.
  
  Lemma HasTypeInstruction_TypeAndLocalValid_provable : forall S C F L es tf L',
      HasTypeInstruction S C F L es tf L' ->
      forall taus1 taus2,
        tf = Arrow taus1 taus2 ->
        LocalCtxValid F L /\
        Forall (TypeValid F) taus1 /\
        Forall (TypeValid F) taus2 /\
        LocalCtxValid F L'.
  Proof.
    apply
      (HasTypeInstruction_mind'
         (fun S C F L es tf L' =>
            forall taus1 taus2,
              tf = Arrow taus1 taus2 ->
              LocalCtxValid F L /\
              Forall (TypeValid F) taus1 /\
              Forall (TypeValid F) taus2 /\
              LocalCtxValid F L')
         (fun S cl ft => True)
         (fun S C f ex ft => True)
         (fun S maybe_ret i locvis locsz es taus => True)).
    all: auto.
    all: try unfold EmptyRes.
    all: try unfold EmptyArrow.
    all: intros; repeat invert_arrow_eq.
    all: auto.
    

    - unfold EmptyArrow in *.
      invert_arrow_eq.
      split; auto.
      split; auto.
      split; auto.
      constructor; [ | constructor ].
      eapply HasType_Valid; eauto.
    - split; auto.
    - solve_trivial_tlv_goal F.
    - solve_trivial_tlv_goal F.
    - repeat match goal with
             | [ H : forall _ _, _ = _ -> _ |- _ ] =>
               specialize (H _ _ eq_refl)
             end.
      destructAll.
      unfold LocalCtxValid in *.
      split; [ solve_trivial_tlv_subgoal F | ].
      split.
      { apply Forall_app.
        split; [ solve_trivial_tlv_subgoal F | ].
        auto. }
      split; solve_trivial_tlv_subgoal F.
    - split; auto.
      split.
      { apply Forall_app.
        split; auto. }
      split; auto.
    - unfold EmptyArrow in *.
      invert_arrow_eq.
      split; auto.
      split; auto.
      split; auto.
      apply LocalCtxValid_set_localtype; auto.
    - split; auto.
      unfold EmptyRes in *.
      invert_arrow_eq.
      split; auto.
      split; auto.
      apply LocalCtxValid_set_localtype; auto.
    - split; auto.
      split; auto.
      split; auto.
      apply LocalCtxValid_set_localtype; auto.
    - split; auto.
      split.
      { apply Forall_app; split; auto. }
      split; auto.
    - split; auto.
      split.
      { match goal with
        | [ H : TypeValid _ _ |- _ ] => inversion H; subst
        end.
        auto. }
      split; auto.
    - split; auto.
      split; auto.
      split; auto.
      match goal with
      | [ H : TypeValid _ _ |- _ ] => inversion H; subst
      end.
      auto.
    - split; auto.
      split; auto.
      split; auto.
      constructor; auto.
      match goal with
      | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] =>
        inversion H; subst
      end.
      constructor; auto.
    - split; auto.
      split.
      { constructor; auto.
        match goal with
        | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] =>
          inversion H; subst
        end.
        constructor; auto. }
      split; auto.
    - repeat split; auto.
      match goal with
      | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] =>
        inversion H; subst
      end.
      constructor; auto.
      constructor; auto.
    - split; auto.
      split; auto.
      apply Forall_app; split; auto.
    - split; auto.
    - split; auto.
    - split; auto.
      split; auto.
      constructor; auto.
      match goal with
      | [ H : Forall _ ?L, H' : nth_error ?L _ = Some ?T |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : List.In T L);
        [ | rewrite Forall_forall in H; specialize (H _ H0) ]
      end.
      { eapply nth_error_In; eauto. }
      auto.
    - split; auto.
      split.
      { apply Forall_app; split; auto. }
      split; auto.
    - split; auto.
      split.
      { apply Forall_app; split; auto. }
      split; auto.
    - split; auto.
    - split; auto.
    - split; auto.
      split.
      { apply Forall_app; split; auto. }
      split; auto.
    - split; auto.
      split.
      { apply Forall_app; split; auto. }
      split; auto.
    - split; auto.
    - solve_trivial_tlv_goal F.
    - match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] =>
        rewrite H in H'; inversion H'; subst
      end.
      split; auto.
    - repeat match goal with
             | [ H : forall _ _, _ -> _ |- _ ] =>
               specialize (H _ _ eq_refl)
             end.
      destructAll.
      auto.
    - repeat match goal with
             | [ H : forall _ _, _ -> _ |- _ ] =>
               specialize (H _ _ eq_refl)
             end.
      destructAll.
      unfold LocalCtxValid in *.
      repeat split; try solve_trivial_tlv_subgoal F.
      all: apply Forall_app; split; auto.
      all: solve_trivial_tlv_subgoal F.
    - repeat match goal with
             | [ H : forall _ _, _ -> _ |- _ ] =>
               specialize (H _ _ eq_refl)
             end.
      destructAll.
      split; auto.
      unfold LocalCtxValid in *.
      eapply LCEffEqual_Forall; eauto.
    - repeat match goal with
             | [ H : forall _ _, _ -> _ |- _ ] =>
               specialize (H _ _ eq_refl)
             end.
      destructAll.
      repeat split; auto.
      unfold LocalCtxValid in *.
      eapply LCEffEqual_Forall; eauto.
  Qed.

  Lemma HasTypeInstruction_TypeAndLocalValid : forall {S C F L es tau1 tau2 L'},
      HasTypeInstruction S C F L es (Arrow tau1 tau2) L' ->
      LocalCtxValid F L /\
      Forall (TypeValid F) tau1 /\
      Forall (TypeValid F) tau2 /\
      LocalCtxValid F L'.
  Proof.
    intros.
    eapply HasTypeInstruction_TypeAndLocalValid_provable; eauto.
  Qed.

  Ltac start_lceff_subgoals :=
    match goal with
    | [ H : ?A, H' : ?A -> _ |- _ ] =>
      specialize (H' H _ _ eq_refl)
    end;
    destructAll;
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
      inversion H; subst
    end;
    simpl in *; destructAll.

  Lemma LocalCtxValid_LCEffEqual : forall {F C L L'},
      LocalCtxValid F L ->
      LCEffEqual C L L' ->
      LocalCtxValid F L'.
  Proof.
    unfold LocalCtxValid.
    intros.
    eapply LCEffEqual_Forall; eauto.
  Qed.

  Lemma LocalCtxValid_Function_Ctx : forall {F F' L},
      LocalCtxValid F L ->
      qual F = qual F' ->
      size F = size F' ->
      type F = type F' ->
      location F = location F' ->
      LocalCtxValid F' L.
  Proof.
    unfold LocalCtxValid.
    intros.
    rewrite Forall_forall.
    intros.
    destruct_prs.
    eapply TypeValid_Function_Ctx; eauto.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *; auto.
  Qed.

  Lemma Forall_TypeValid_Function_Ctx : forall {F F' taus},
      Forall (TypeValid F) taus ->
      qual F = qual F' ->
      size F = size F' ->
      type F = type F' ->
      location F = location F' ->
      Forall (TypeValid F') taus.
  Proof.
    unfold LocalCtxValid.
    intros.
    rewrite Forall_forall.
    intros.
    eapply TypeValid_Function_Ctx; eauto.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H'); auto
    end.
  Qed.

  Ltac solve_lceff_subgoals n :=
    start_lceff_subgoals;
    do n eexists;
    repeat ltac:(split; eauto);
    eapply LCEffEqual_trans; eauto;
    apply LCEffEqual_sym; eauto.

  Lemma Empty_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [] (Arrow t1 t2) L' ->
    t1 = t2 /\
    LCEffEqual (size F) L L' /\
    M.is_empty (LinTyp S) = true.
  Proof.
    assert (Heq : @nil Instruction = []) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize (@nil Instruction) at 2 3. generalize (Arrow t1 t2) at 2 3.
    intros arr i Heq Heq' Htyp. revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try congruence.
    - inv Heq1.
      repeat split; eauto.
      apply LCEffEqual_refl.
    - symmetry in Heq.
      eapply app_eq_nil in Heq. destructAll. congruence.
    - subst. inv Heq1. edestruct IHHtyp; eauto. subst.
      destructAll. repeat split; eauto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(0).
    - solve_lceff_subgoals ltac:(0).
  Qed.

  Lemma HasTypeInstruction_empty_list S M F ts L :
    M.is_empty (LinTyp S) = true ->
    LocalCtxValid F L ->
    Forall (TypeValid F) ts ->
    HasTypeInstruction S M F L [] (Arrow ts ts) L.
  Proof.
    intros Hs Hlcv Hts.
    rewrite (app_nil_end ts).
    eapply FrameTyp.
    reflexivity.
    eapply Forall_trivial.
    intros [? q]. now eapply QualLeq_Top.
    now eapply QualLeq_Top.

    eapply EmptyTyp; auto.
    
    unfold LocalCtxValid in *.
    solve_trivial_tlv_subgoal F.
    
    auto.
  Qed.

  Lemma HasTypeInstruction_FirstLocalValid : forall {S C F L es tau1 tau2 L'},
      HasTypeInstruction S C F L es (Arrow tau1 tau2) L' ->
      LocalCtxValid F L.
  Proof.
    intros.
    specialize (HasTypeInstruction_TypeAndLocalValid H).
    intros; destructAll; auto.
  Qed.

  Lemma HasTypeInstruction_InputTypesValid : forall {S C F L es tau1 tau2 L'},
      HasTypeInstruction S C F L es (Arrow tau1 tau2) L' ->
      Forall (TypeValid F) tau1.
  Proof.
    intros.
    specialize (HasTypeInstruction_TypeAndLocalValid H).
    intros; destructAll; auto.
  Qed.

  Lemma HasTypeInstruction_OutputTypesValid : forall {S C F L es tau1 tau2 L'},
      HasTypeInstruction S C F L es (Arrow tau1 tau2) L' ->
      Forall (TypeValid F) tau2.
  Proof.
    intros.
    specialize (HasTypeInstruction_TypeAndLocalValid H).
    intros; destructAll; auto.
  Qed.

  Lemma HasTypeInstruction_SecondLocalValid : forall {S C F L es tau1 tau2 L'},
      HasTypeInstruction S C F L es (Arrow tau1 tau2) L' ->
      LocalCtxValid F L'.
  Proof.
    intros.
    specialize (HasTypeInstruction_TypeAndLocalValid H).
    intros; destructAll; auto.
  Qed.

  (** Composition typing lemmas *)

  Lemma composition_typing_single S M F L1 es e ts1 ts2 L2 :
    HasTypeInstruction S M F L1 (es ++ [e]) (Arrow ts1 ts2) L2 ->
    exists ts ts1' ts2' ts3 L3 S1 S2,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (TypeValid F) ts /\
      HasTypeInstruction S1 M F L1 es (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F L3 [e] (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1;S2] S.
  Proof.
    assert (Heq : exists e', es ++ [ e ] = e') by eauto. destruct Heq as [e' Heq].
    assert (Heq' : exists arrt, Arrow ts1 ts2 =  arrt) by eauto. destruct Heq' as [arr Heq'].

    intros Htyp. rewrite Heq, Heq' in Htyp. revert es e ts1 ts2 Heq Heq'.

    induction Htyp; intros es_ e_ ts1 ts2 Heq Heq'; subst; eauto.
    all: try ltac:(eapply elt_eq_unit in Heq;
                   destructAll; try inv Heq';
                   remember I as obj).
    all:
      try match goal with
          | [ H : context[_ = I] |- _ ] =>
            exists []; do 4 eexists; exists (empty_LinTyp S), S
          end.
    all: repeat ltac:(split; [ reflexivity | ]).
    all: try ltac:(split; auto).
    all: try ltac:(split; [ eapply HasTypeInstruction_empty_list; destruct S; eauto | ]).
    all: try ltac:(split; [ | eapply SplitStoreTypings_EmptyHeapTyping_l ]).
    all: try HasTypeEauto.
    all:
      try match goal with
          | [ |- HasTypeInstruction _ _ _ _ _ _ _ ] => now eauto
          end.

    all:
      try match goal with
          | [ |- LocalCtxValid _ _ ] =>
            eapply LocalCtxValid_Function_Ctx;
            [ eapply HasTypeInstruction_FirstLocalValid; eauto | | | | ];
            destruct F; subst; simpl in *; auto
          end.

    Ltac solve_itv_subgoal F :=
      eapply Forall_TypeValid_Function_Ctx;
      [ eapply HasTypeInstruction_InputTypesValid; eauto | | | | ];
      destruct F; subst; simpl in *; auto.
    
    - solve_itv_subgoal F.
    - solve_itv_subgoal F.
    - apply Forall_app.
      split; [ solve_itv_subgoal F | ].
      constructor; auto.
    - apply Forall_app.
      split; auto.
    - apply Forall_app.
      split; auto.
    - match goal with
      | [ H : TypeValid _ _ |- _ ] => inversion H; subst; auto
      end.
    - constructor; auto.
      match goal with
      | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] =>
        inversion H; subst
      end.
      econstructor; eauto.
    - apply Forall_app.
      split; auto.
    - constructor; auto.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_In in H
      end.
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H'); auto
      end.
    - apply Forall_app.
      split; auto.
    - apply Forall_app.
      split; auto.
    - apply Forall_app.
      split; auto.
    - apply Forall_app.
      split; auto.

    - eapply app_eq_nil in Heq. destructAll. congruence.

    - inv Heq'. eapply app_inj_tail in Heq. destructAll.
      exists []; do 6 eexists. do 2 split; [ reflexivity | ]; split; [| split ]; auto; try eassumption; split; eassumption.

    - inv Heq'.

      edestruct IHHtyp. reflexivity. reflexivity. destructAll.

      do 7 eexists; do 2 (split; [ rewrite app_assoc; reflexivity | ]); split; [| split ].

      apply Forall_app; split; auto.
      eapply Forall_TypeValid_Function_Ctx; eauto.
      1-4: destruct F; subst; simpl in *; auto.

      replace x0 with ([] ++ x0) by reflexivity. eapply FrameTyp; eauto.
      replace x1 with ([] ++ x1) by reflexivity. split; [ | eassumption ]. eapply FrameTyp; eauto.
    - specialize (IHHtyp _ _ _ _ eq_refl eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      do 7 eexists.
      do 2 ltac:(split; eauto).
    - specialize (IHHtyp _ _ _ _ eq_refl eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      do 7 eexists.
      do 2 ltac:(split; eauto).
  Qed.
  
  Lemma composition_typing_single_strong S M F L1 es e ts1 ts2 L2 :
    HasTypeInstruction S M F L1 (es ++ [e]) (Arrow ts1 ts2) L2 ->

    exists ts ts1' ts2' ts3 L3 qf S1 S2,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F' := update_linear_ctx (set_hd qf (linear F)) F in

      HasTypeInstruction S1 M F' L1 es (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F' L3 [e] (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1;S2] S /\
      Forall (TypeValid F) ts.
  Proof.
    assert (Heq : exists e', es ++ [ e ] = e') by eauto. destruct Heq as [e' Heq].
    assert (Heq' : exists arrt, Arrow ts1 ts2 =  arrt) by eauto. destruct Heq' as [arr Heq'].

    intros Htyp. rewrite Heq, Heq' in Htyp. revert es e ts1 ts2 Heq Heq'.

    induction Htyp; intros es_ e_ ts1 ts2 Heq Heq'; subst; eauto.

    all: try (apply elt_eq_unit in Heq;
              destructAll; try inv Heq';
              remember I as obj).
    all:
      try match goal with
          | [ H : context[_ = I] |- _ ] =>
            exists []; do 5 eexists; exists (empty_LinTyp S), S
          end.
    all: repeat ltac:(split; [ reflexivity | ]).
    all: try ltac:(split; [ constructor | ]).
    all: try ltac:(split; [ eapply QualLeq_Refl | ]).
    all: simpl in *.
    all:
      try match goal with
          | [ |- _ /\ _ /\ _ ] =>
            destruct F; subst; simpl in *
          end.
    all: try ltac:(split; [ eapply HasTypeInstruction_empty_list; destruct S; eauto | ]).
    all: try rewrite set_get_hd.
    all: try ltac:(split; [ | split; auto ]).
    all: try eapply SplitStoreTypings_EmptyHeapTyping_l.
    all: try HasTypeEauto.
    all:
      try match goal with
          | [ |- HasTypeInstruction _ _ _ _ _ _ _ ] =>
            now eauto
          end.
    all: eauto.

    all:
      try match goal with
          | [ |- LocalCtxValid _ _ ] =>
            eapply LocalCtxValid_Function_Ctx;
            [ eapply HasTypeInstruction_FirstLocalValid; eauto | | | | ];
            auto
          end.

    Ltac solve_itv_subgoal_strong :=
      eapply Forall_TypeValid_Function_Ctx;
      [ eapply HasTypeInstruction_InputTypesValid; eauto | | | | ];
      simpl in *; auto.

    all: try ltac:(apply Forall_app; split; auto).

    - solve_itv_subgoal_strong.
    - solve_itv_subgoal_strong.
    - solve_itv_subgoal_strong.
    - match goal with
      | [ H : TypeValid _ (QualT (ProdT _) _) |- _ ] =>
        inversion H; subst; auto
      end.
    - constructor; auto.
      match goal with
      | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] =>
        inversion H; subst; auto
      end.
      econstructor; eauto.
    - constructor; auto.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_In in H
      end.
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H'); auto
      end.

    - eapply app_eq_nil in Heq. destructAll. congruence.

    - inv Heq'. eapply app_inj_tail in Heq. destructAll.
      exists []; do 7 eexists; do 2 split; [ reflexivity | ]; split.
      now constructor. split; [ now eapply QualLeq_Refl | ].
      rewrite set_get_hd. destruct F; simpl in *. eauto.

    - inv Heq'.

      edestruct IHHtyp. reflexivity. reflexivity. destructAll.

      do 8 eexists; do 2 (split; [ rewrite app_assoc; reflexivity | ]).

      destruct F; unfold F'; simpl in *. destructAll.
      split.

      eapply Forall_app. split. 2:{ eassumption. }

      prepare_Forall.
      eapply QualLeq_Trans; [ eassumption | ].
      rewrite get_set_hd in *; eassumption.

      split. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      rewrite set_set_hd in *. split; eauto. split; eauto.
      split; try eassumption.
      apply Forall_app; split; auto.
      eapply Forall_TypeValid_Function_Ctx; eauto.
    - specialize (IHHtyp _ _ _ _ eq_refl eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      simpl in *; destructAll.
      do 8 eexists.
      do 4 ltac:(split; eauto).
      split; [ | split; eauto ].
      eapply ChangeBegLocalTyp; eauto.
      destruct F; subst; simpl in *; auto.
    - specialize (IHHtyp _ _ _ _ eq_refl eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      simpl in *; destructAll.
      do 8 eexists.
      do 4 ltac:(split; eauto).
      split; [ eauto | split; eauto ].
      eapply ChangeEndLocalTyp; eauto.
      destruct F; subst; simpl in *; auto.
  Qed.

  Corollary composition_typing_double S M F L1 e1 e2 ts1 ts2 L2 :
    HasTypeInstruction S M F L1 [e1 ; e2] (Arrow ts1 ts2) L2 ->
    exists ts ts1' ts2' ts3 L3 S1 S2,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (TypeValid F) ts /\
      HasTypeInstruction S1 M F L1 [e1] (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F L3 [e2] (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1;S2] S.
  Proof.
    intros. replace [e1 ; e2] with ([e1] ++ [e2]) in H by reflexivity.
    eapply composition_typing_single; eauto.
  Qed.

  Corollary composition_typing_double_strong S M F L1 e1 e2 ts1 ts2 L2 :
    HasTypeInstruction S M F L1 [e1 ; e2] (Arrow ts1 ts2) L2 ->
    exists ts ts1' ts2' ts3 L3 qf S1 S2,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F' := update_linear_ctx (set_hd qf (linear F)) F in
      HasTypeInstruction S1 M F' L1 [e1] (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F' L3 [e2] (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1;S2] S /\
      Forall (TypeValid F) ts.
  Proof.
    intros. replace [e1 ; e2] with ([e1] ++ [e2]) in H by reflexivity.
    eapply composition_typing_single_strong; eauto.
  Qed.

  Lemma composition_typing S M F L1 es es' ts1 ts2 L2 :
    HasTypeInstruction S M F L1 (es ++ es') (Arrow ts1 ts2) L2 ->
    exists ts ts1' ts2' ts3 L3 qf S1 S2,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F' := update_linear_ctx (set_hd qf (linear F)) F in
      HasTypeInstruction S1 M F' L1 es (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F' L3 es' (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1;S2] S /\
      Forall (TypeValid F) ts.
  Proof.
    revert S M F L1 es ts1 ts2 L2.
    eapply rev_ind with (l := es').

    - intros S M F L1 es ts1 ts2 L2 Htyp.
      simpl in *. exists []; do 7 eexists; do 2 split; [ reflexivity | ]; split.
      rewrite app_nil_r in Htyp.
      now constructor. split. eapply QualLeq_Refl.
      split. rewrite app_nil_r in *. destruct F; simpl in *.
      rewrite set_get_hd.  eassumption.

      split.
      eapply HasTypeInstruction_empty_list.
      4:{ split; auto; eapply SplitStoreTypings_EmptyHeapTyping_r. }
      -- destruct S; reflexivity.
      -- eapply LocalCtxValid_Function_Ctx.
         1:{ eapply HasTypeInstruction_SecondLocalValid; eauto. }
         all: destruct F; subst; simpl in *; auto.
      -- eapply Forall_TypeValid_Function_Ctx.
         1:{ eapply HasTypeInstruction_OutputTypesValid; eauto. }
         all: destruct F; subst; simpl in *; auto.
    - intros e es IH S M F L1 es_ ts1 ts2 L2 Htyp.
      simpl in *. rewrite app_assoc in Htyp.
      edestruct composition_typing_single_strong. eassumption. destructAll.
      destruct F; simpl in *. destructAll. edestruct IH.
      eassumption. destructAll.
      simpl in *. rewrite set_set_hd in *.

      edestruct SplitStoreTypings_assoc. eapply H11. eassumption. destructAll.

      do 8 eexists. split; [ | split; [ | split; [ | split; [ | split; [ | split ]]]]].

      6:{ eapply ConsTyp; [ | | eassumption  ].
          2:{ eapply FrameTyp. reflexivity.
              simpl. eassumption. simpl. eassumption.
              simpl. rewrite set_set_hd. eassumption.
              
              eapply proj1.
              eapply Forall_app.
              eapply HasTypeInstruction_InputTypesValid; eauto. }
          eassumption. }

      5:{ eapply FrameTyp. reflexivity.
          simpl. eassumption. simpl. eassumption.
          simpl. rewrite set_set_hd. eassumption.
              
          eapply proj1.
          eapply Forall_app.
          eapply HasTypeInstruction_InputTypesValid; eauto. }

      reflexivity. reflexivity.
      eassumption. eassumption.
      split; eassumption.
  Qed.

  Lemma HasTypeInstruction_app S S1 S2 M F es1 es2 L1 L2 L3 t1 t2 t3 :
    HasTypeInstruction S1 M F L1 es1 (Arrow t1 t2) L2 ->
    HasTypeInstruction S2 M F L2 es2 (Arrow t2 t3) L3 ->
    SplitStoreTypings [S1; S2] S ->
    HasTypeInstruction S M F L1 (es1 ++ es2) (Arrow t1 t3) L3.
  Proof.
    revert S S1 S2 M F es1 L1 L2 L3 t1 t2 t3.
    eapply rev_ind with (l := es2).
    - intros S S1 S2 M F es1 L1 L2 L3 t1 t2 t3 Ht1 Ht2 Hs.
      eapply Empty_HasTypeInstruction in Ht2. inv Ht2. inv H0. rewrite app_nil_r.
      destructAll.
      eapply ChangeEndLocalTyp; eauto.
      match goal with
      | [ H : SplitStoreTypings [?S1; ?S2] ?S,
          H' : M.is_empty (LinTyp ?S2) = true |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : SplitStoreTypings [S2; S1] S);
        [ eapply SplitStoreTypings_permut; [ | eauto ]; constructor | ];
        specialize (SplitStoreTypings_Empty_eq _ _ _ H0 H');
        intros
      end.
      eapply HasTypeInstruction_StoreTyping_eq; eauto.
    - intros e es IH S S1 S2 M F es1 L1 L2 L3 t1 t2 t3 Ht1 Ht2 Hs.
      rewrite app_assoc.
      eapply composition_typing_single_strong in Ht2. destructAll.

      destruct F. simpl in *. destructAll.

      edestruct SplitStoreTypings_assoc. eapply SplitStoreTypings_comm. eapply H3.
      eapply SplitStoreTypings_comm. eassumption.
      destructAll.

      simpl. eapply ConsTyp.

      3:{ eapply FrameTyp. reflexivity. eassumption. eassumption.
          simpl in *. eassumption.
          eapply proj1.
          eapply Forall_app.
          eapply HasTypeInstruction_OutputTypesValid; eauto. }

      2:{ eapply IH. eassumption.
          eapply FrameTyp. reflexivity. eassumption. eassumption.
          simpl in *. eassumption.

          eapply proj1.
          eapply Forall_app.
          eapply HasTypeInstruction_OutputTypesValid; eauto.
          
          eapply SplitStoreTypings_comm. eassumption. }

      eapply SplitStoreTypings_comm. eassumption.
  Qed.

  Lemma nth_error_some_exists : forall (A : Type) i (l : list A),
      i < length l -> exists v, nth_error l i = Some v.
  Proof.
    intro.
    intro.
    revert A.
    elim i.
    - intros.
      unfold nth_error.
      revert H.
      case l; eauto.
      intro.
      simpl in H.
      lia.
    - intros.
      revert H0.
      case l.
      * simpl.
        lia.
      * intros.
        simpl in H0.
        assert (H1 := lt_S_n _ _ H0).
        assert (H2 := H _ _ H1).
        simpl.
        eauto.
  Qed.

  Ltac invert_Forall3 :=
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.

  Lemma Forall3_forall : forall {A B C} {P} {l1 : list A} {l2 : list B} {l3 : list C},
      Forall3 P l1 l2 l3 <->
      ((forall i el1 el2 el3,
           nth_error l1 i = Some el1 ->
           nth_error l2 i = Some el2 ->
           nth_error l3 i = Some el3 ->
           P el1 el2 el3) /\
       length l1 = length l2 /\
       length l2 = length l3).
  Proof.
    induction l1.
    - intros; split.
      -- intros.
         invert_Forall3.
         split; auto.
         intros.
         match goal with
         | [ X : nat |- _ ] =>
           destruct X; simpl in *;
           match goal with
           | [ H : None = Some _ |- _ ] => inversion H
           end
         end.
      -- intros.
         destructAll.
         simpl in *.
         match goal with
         | [ H : 0 = length ?L |- _ ] => destruct L; simpl in *
         end.
         2:{
           match goal with
           | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
           end.
         }
         match goal with
         | [ H : 0 = length ?L |- _ ] => destruct L; simpl in *
         end.
         2:{
           match goal with
           | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
           end.
         }
         constructor.
    - intros; split.
      -- intros.
         invert_Forall3.
         match goal with
         | [ H : forall _ _, _, H' : Forall3 _ _ _ _ |- _ ] =>
           rewrite H in H'
         end.
         destructAll.
         split.
         2:{
           split;
           match goal with
           | [ H : ?A = ?B |- Datatypes.S ?A = Datatypes.S ?B ] =>
             rewrite H; auto
           end.
         }
         intros.
         match goal with
         | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
           destruct IDX; simpl in *
         end.
         --- repeat match goal with
                    | [ H : Some _ = Some _ |- _ ] =>
                      inversion H; subst; clear H
                    end.
             auto.
         --- eauto.
      -- intros.
         destructAll.
         simpl in *.
         match goal with
         | [ H : Datatypes.S _ = length ?L |- _ ] =>
           destruct L; simpl in *
         end.
         1:{
           match goal with
           | [ H : Datatypes.S _ = 0|- _ ] => inversion H
           end.
         }
         match goal with
         | [ H : Datatypes.S _ = length ?L |- _ ] =>
           destruct L; simpl in *
         end.
         1:{
           match goal with
           | [ H : Datatypes.S _ = 0|- _ ] => inversion H
           end.
         }
         repeat match goal with
                | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
                  inversion H; subst; clear H
                end.
         constructor.
         --- match goal with
             | [ H : context[_ -> ?P _ _ _] |- ?P _ _ _ ] =>
               eapply (H 0); eauto
             end.
         --- match goal with
             | [ H : forall _ _, _ <-> _ |- _ ] => rewrite H
             end.
             split; [ | split; auto ].
             intros.
             match goal with
             | [ H' : nth_error _ ?IDX = Some _,
                 H : context[_ -> ?P _ _ _] |- ?P _ _ _ ] =>
               eapply (H (Datatypes.S IDX)); eauto
             end.
  Qed.

  Lemma HasTypeInstruction_Values Ss S M F L vs taus (H : values vs) :
    SplitStoreTypings Ss S ->
    Forall3 (fun S v t => HasTypeValue S F v t) Ss (to_values vs H) taus ->
    LocalCtxValid F L ->
    HasTypeInstruction S M F L vs (Arrow [] taus) L.
  Proof.
    revert Ss S M F L taus H. eapply rev_ind with (l := vs).
    - intros Ss S M F L taus Hs H Hall. simpl in Hall. inv Hall; eauto.
      inv H. inv H1. simpl in *.
      eapply EmptyTyp.

      eapply PositiveMap.is_empty_1. intros x v Hc.

      destruct H.

      assert (Hn : forall p, exists n, p = N.succ_pos n).
      { clear. intros p.
        destruct p.
        + exists (2 * (N.pos p))%N. reflexivity.
        + exists (2 * N.pos p - 1)%N. simpl. lia.
        + exists 0%N. reflexivity. }

      edestruct (Hn x). subst.
      edestruct H1. eexists. eapply PositiveMap.find_1.
      eassumption.

    - intros v vs' IH Ss' S M F L taus Hv Hs Hall Hlcv.
      assert (H1 := Hv).
      eapply Forall_app in H1. destructAll.
      rewrite to_values_app with (H1 := H) (H2 := H0) in Hall.

      edestruct Forall3_app_inv_2. eassumption. destructAll.

      assert (H1' := H0). inv H1'.

      simpl in *; destruct v; try now inv H5.
      inv H6. inv H2. inv H9.

      edestruct SplitStoreTyping_app. eassumption. inv H2.

      eapply ConsTyp. eassumption.

      eapply IH; [ | eassumption | eassumption ]. eassumption.


      replace x1 with (x1 ++ []) at 1 by (rewrite app_nil_r; reflexivity).

      eapply FrameTyp.

      reflexivity.

      eapply Forall_trivial. intros [? ?]. now eapply QualLeq_Top.
      now eapply QualLeq_Top.

      eapply ValTyp.

      eapply HasTypeValue_Function_Ctx; [ | | | | eassumption ];

      destruct F; reflexivity.

      -- eapply LocalCtxValid_Function_Ctx; eauto.
         all: destruct F; subst; simpl in *; auto.
      -- rewrite Forall_forall.
         intros.
         match goal with
         | [ X : List.In _ _ |- _ ] => apply In_nth_error in X
         end.
         destructAll.
         match goal with
         | [ H : Forall3 _ ?L1 ?L2 ?L3,
             H' : nth_error ?L3 ?IDX = Some _ |- _ ] =>
           rewrite Forall3_forall in H;
           destruct H as [H]; destructAll;
           let H0 := fresh "H" in
           assert (H0 : exists x, nth_error L1 IDX = Some x);
           [ | let H1 := fresh "H" in
               assert (H1 : exists x, nth_error L2 IDX = Some x);
               [ | let x := fresh "x" in
                   let x2 := fresh "x" in
                   destruct H0 as [x H0]; destruct H1 as [x2 H1];
                   specialize (H _ _ _ _ H0 H1 H') ] ]
         end.
         1-2: apply nth_error_some_exists.
         1-2:
           match goal with
           | [ H : nth_error ?L _ = Some _ |- _ < length ?L2 ] =>
             replace (length L2) with (length L) by congruence
           end.
         1-2: eapply nth_error_Some_length; eauto.

         eapply HasType_Valid; eauto.
  Qed.

  (* Inversion Lemmas *)

  Lemma Nop_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Nop] (Arrow t1 t2) L' ->
    M.is_empty (LinTyp S) = true /\
    t1 = t2 /\ LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Nop] = [Nop]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Nop] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try congruence.
    - inv Heq1; eauto.
      split; eauto.
      split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll.

      edestruct IHHtyp2 as [He1 [Heq1' Heq2']]; subst.

      + reflexivity.

      + eassumption.

      + subst.
        split; [ | split; try reflexivity ].

        * erewrite is_empty_eq_map.
          eassumption.
          eapply eq_map_sym. eapply SplitStoreTypings_Empty_eq. eassumption.
          eassumption.
        * eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp as [? [? ?]]; eauto. subst.
      split; eauto. split; eauto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(0).
    - solve_lceff_subgoals ltac:(0).
  Qed.

  Lemma Val_HasTypeInstruction S M F L t1 t2 L' v :
    HasTypeInstruction S M F L [Val v] (Arrow t1 t2) L' ->
    exists t,
      t1 ++ [t] = t2 /\
      HasTypeValue S F v t /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Val v] = [Val v]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Val v] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. eexists. split. reflexivity.
      split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      eexists; split; eauto; split; eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      eexists. split.
      rewrite app_assoc. reflexivity. split.
      -- eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
         destruct F; unfold F'; reflexivity.
      -- destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(1).
    - solve_lceff_subgoals ltac:(1).
  Qed.

  Lemma Val_HasTypeInstruction_moreinfo S M F L t1 t2 L' v :
    HasTypeInstruction S M F L [Val v] (Arrow t1 t2) L' ->
    exists t qf,
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t1 /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      t1 ++ [t] = t2 /\
      HasTypeValue S (update_linear_ctx (set_hd qf (linear F)) F) v t /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Val v] = [Val v]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Val v] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 2 eexists. split. now constructor.
      split. eapply QualLeq_Refl. split. reflexivity.
      split. rewrite set_get_hd. destruct F; eassumption.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      destructAll.
      do 2 eexists. repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
    - unfold F' in *. destruct F; simpl in *.

      subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 2 eexists. split.

      eapply Forall_app; split; [| eassumption ].
      prepare_Forall.
      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      rewrite get_set_hd in *.
      split. rewrite set_set_hd in *.

      eapply QualLeq_Trans; eassumption.

      split.
      rewrite app_assoc. reflexivity. split; auto.
      eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity.
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

  Lemma Values_HasTypeInstruction S M F L t1 t2 L' vs (H : values vs) :
    HasTypeInstruction S M F L vs (Arrow t1 t2) L' ->
    exists t Ss qf,
      t1 ++ t = t2 /\

      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t1 /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\

      SplitStoreTypings Ss S /\
      Forall3 (fun S v t => HasTypeValue S F v t) Ss (to_values vs H) t /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq. generalize (Arrow t1 t2) at 1 3.
    intros arr Heq Htyp.
    revert t1 t2 Heq.
    induction Htyp; intros t1 t2 Heq1;
      try now (exfalso; inv H; match goal with [ H : value _ |- _ ] => inv H end).
    - inv Heq1. destruct t. do 3 eexists. split. reflexivity.
      split. constructor; eauto. split.
      eapply QualLeq_Top. split.
      eapply SplitStoreTypings_Singl.
      split; eauto. constructor; eauto. constructor.
      apply LCEffEqual_refl.
    - inv Heq1. do 3 eexists. split. reflexivity.
      split. now constructor.
      split. eapply QualLeq_Top. split.
      eapply SplitStoreTypings_Emp. eassumption.
      split. now constructor.
      apply LCEffEqual_refl.
    - assert (H1 := H). eapply Forall_app in H1. destructAll. inv Heq1.
      edestruct (IHHtyp1 H1). reflexivity. destructAll.
      edestruct (IHHtyp2 H2). reflexivity. destructAll.

      rewrite <- app_assoc. do 3 eexists. split. reflexivity.
      split; [| split ].

      eassumption.
      eassumption.

      split.
      2:{ rewrite to_values_app with (H1 := H1) (H2 := H2).

          split; [ | eapply LCEffEqual_trans; eauto ].

          eapply Forall3_app; eassumption. }

      eapply SplitStoreTypings_merge; eassumption.

    - inv Heq1. edestruct IHHtyp. reflexivity. destructAll.
      do 3 eexists. split.
      rewrite <- app_assoc. reflexivity.
      split; eauto.

      destruct F; simpl in *.
      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall.
      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split.

      destruct F; simpl in *. rewrite get_set_hd in *.
      now eapply QualLeq_Trans; eauto.

      split; eauto. split.
      eapply Forall3_monotonic; [| eassumption ].
      simpl. intros S' v1 tau Hyp.
      eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
        try (destruct F; simpl; reflexivity).
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma Ne_HasTypeInstruction S M F L t1 t2 L' n :
    HasTypeInstruction S M F L [Ne n] (Arrow t1 t2) L' ->
    LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Ne n] = [Ne n]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Ne n] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - assert (Heq': e = Ne n /\ es = []).
      {
        induction es; simpl in Heq; injection Heq; auto.
        intros. destruct es; inversion H0.
      }
      destructAll.
      specialize (IHHtyp2 eq_refl).
      eapply Empty_HasTypeInstruction in Htyp1. destructAll.
      specialize (IHHtyp2 _ _ eq_refl).
      eapply LCEffEqual_trans; eauto.
    - destruct F; subst; simpl in *; eauto.
    - solve_lceff_subgoals ltac:(0).
    - solve_lceff_subgoals ltac:(0).
  Qed.

  Lemma set_localtype_LCEffEqual : forall {C L L' sz sz'} n tau,
      LCEffEqual C L L' ->
      SizeLeq C sz sz' = Some true ->
      SizeLeq C sz' sz = Some true ->
      LCEffEqual C
                 (set_localtype n tau sz L)
                 (set_localtype n tau sz' L').
    Proof.
      intros.
      generalize dependent n.
      generalize dependent sz.
      induction H; simpl; intros.
      - constructor.
      - destruct x. destruct y.
        unfold set_localtype in *. simpl.
        destruct n.
        + constructor; auto.
        + constructor. auto.
          eapply IHForall2; eauto.
    Qed.

  Lemma Get_local_HasTypeInstruction S M F L t1 t2 L' n q :
    HasTypeInstruction S M F L [Get_local n q] (Arrow t1 t2) L' ->
    exists pt sz b taunew,
      M.is_empty (LinTyp S) = true /\
      t1 ++ [QualT pt q] = t2 /\
      nth_error L n = Some (QualT pt q, sz) /\
      (b = true -> QualLeq (qual F) q Unrestricted = Some true) /\
      (b = false -> QualLeq (qual F) Linear q = Some true) /\
      (b = true -> taunew = QualT pt q) /\
      (b = false -> taunew = QualT Unit Unrestricted) /\
      LCEffEqual (size F) (set_localtype n taunew sz L) L'.
  Proof.
    assert (Heq : [Get_local n q] = [Get_local n q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Get_local n q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 4 eexists. split. eassumption.
      split. reflexivity.
      repeat ltac:(split; eauto).
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll.
      eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll.
      inv Heq1.
      use_LCEffEqual_nth_error_right.
      do 4 eexists. split; [| repeat ltac:(split; eauto)].
      -- eapply SplitStoreTypings_Empty'. eassumption.
         constructor; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply set_localtype_LCEffEqual; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 4 eexists. split.
      eassumption.
      split.
      rewrite app_assoc. reflexivity.
      split; destruct F; eauto.
    - start_lceff_subgoals.
      use_LCEffEqual_nth_error_left; intros; destructAll.
      do 4 eexists; repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
      apply LCEffEqual_sym.
      apply set_localtype_LCEffEqual; auto.
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma Set_local_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Set_local i] (Arrow t1 t2) L' ->
    exists pt q sz tau tausz,
      M.is_empty (LinTyp S) = true /\
      t1 = t2 ++ [tau] /\
      nth_error L i = Some (QualT pt q, sz) /\
      QualLeq (qual F) q Unrestricted = Some true /\
      sizeOfType (type F) tau = Some tausz /\
      SizeLeq (size F) tausz sz = Some true /\
      LCEffEqual (size F) (set_localtype i tau sz L) L'.
  Proof.
    assert (Heq : [Set_local i] = [Set_local i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Set_local i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr n Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 5 eexists. split. eassumption.
      split. reflexivity.
      repeat ltac:(split; eauto).
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll.
      eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll.
      inv Heq1.
      use_LCEffEqual_nth_error_right.
      do 5 eexists. split; [| repeat ltac:(split; eauto)].
      -- eapply SplitStoreTypings_Empty'. eassumption.
         constructor; eauto.
      -- eapply SizeLeq_Trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply set_localtype_LCEffEqual; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 5 eexists. split.
      eassumption.
      split.
      rewrite app_assoc. reflexivity.
      split; destruct F; eauto.
    - start_lceff_subgoals.
      use_LCEffEqual_nth_error_left; intros; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      -- eapply SizeLeq_Trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym.
         apply set_localtype_LCEffEqual; auto.
    - solve_lceff_subgoals ltac:(5).
  Qed.

  Lemma Free_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Free] (Arrow t1 t2) L' ->
    exists l ht q,
      M.is_empty (LinTyp S) = true /\
      t1 = t2 ++ [ QualT (RefT W l ht) q ] /\
      QualLeq (qual F) Linear q = Some true /\
      QualValid (qual F) q /\
      HeapTypeUnrestricted F ht /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Free] = [Free]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Free] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 3 eexists; split. eassumption.
      split. reflexivity.
      repeat ltac:(split; eauto).
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll.
      eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll.
      inv Heq1.
      do 3 eexists. split; [| repeat ltac:(split; eauto) ].
      -- eapply SplitStoreTypings_Empty'. eassumption.
         constructor; eauto.
      -- eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 3 eexists. split.
      eassumption.
      split.
      rewrite app_assoc. reflexivity.
      split. destruct F. eassumption.
      split. destruct F. simpl in *. assumption.
      split.
      match goal with
      | [ H : HeapTypeUnrestricted _ _ |- _ ] =>
        inversion H; subst; simpl in *; constructor; destruct F; simpl in *; assumption
      end.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma Malloc_HasTypeInstruction S M F L hv q t1 t2 L' sz:
    HasTypeInstruction S M F L [Malloc sz hv q] (Arrow t1 t2) L' ->
    exists ht qf (H : size_closed sz),
      t2 = t1 ++ [QualT (ExLoc (QualT (RefT W (LocV 0) (debruijn.subst_ext (Kind:=subst.Kind) (debruijn.weak subst.SLoc) ht)) q)) q] /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t1 /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      NoCapsHeapType (heapable F) ht = true /\
      QualValid (qual F) q /\
      RoomForStrongUpdates (N.of_nat (to_size sz H)) ht /\
      let F' := update_linear_ctx (set_hd qf (linear F)) F in
      HasHeapType S F' hv ht /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Malloc sz hv q] = [Malloc sz hv q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Malloc sz hv q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 3 eexists; repeat split. now constructor.
      eapply QualLeq_Refl. eassumption. simpl. destruct F. simpl in *.
      auto. eauto. rewrite set_get_hd. simpl.
      destruct F; subst; simpl in *. assumption.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. inv Heq1. simpl.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      simpl in *; destructAll.
      setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      do 3 eexists; repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *.
      specialize (IHHtyp eq_refl _ _ eq_refl).
      destructAll.
      do 3 eexists. split; [| split; [| split; [| split; [ | split ]]]].
      rewrite app_assoc. reflexivity.

      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall.
      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eassumption.
      eassumption.

      split; eauto.
      split; eauto.
      rewrite set_set_hd in *. eauto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma Drop_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Drop] (Arrow t1 t2) L' ->
    exists pt q,
      M.is_empty (LinTyp S) = true /\
      t1 = t2 ++ [QualT pt q] /\
      QualLeq (qual F) q Unrestricted = Some true /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Drop] = [Drop]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Drop] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 2 eexists; split. eassumption.
      split. reflexivity. split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.
      destructAll. inv Heq1. do 2 eexists. split; [ | split; eauto ].

      eapply SplitStoreTypings_Empty'. eassumption.
      constructor. eassumption. constructor; eauto.
      split; eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 2 eexists. split. eassumption.
      split. rewrite app_assoc. reflexivity.
      split. destruct F. eassumption.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

Theorem get_localtype_nil idx:
  get_localtype idx [] = None.
  Proof.
    destruct idx; auto.
  Qed.

Theorem Forall2_nth_upd {T U} l1 l2 n (x: T) (y: U) f:
  Forall2 f l1 l2 ->
  f x y ->
  Forall2 f (nth_upd l1 n x) (nth_upd l2 n y).
  Proof.
    intros.
    revert n.
    induction H; simpl; auto.
    destruct n; constructor; auto.
  Qed.

Theorem get_localtype_same_len_Some l1 l2 n p:
  length l1 = length l2 ->
  get_localtype  n l1 = Some p ->
  exists p', get_localtype n l2 = Some p'.
  Proof.
    revert l2 n p.
    induction l1; intros; destruct l2; destruct n; simpl in *; inversion H0; subst; inversion H; eauto.
 Qed.

Theorem get_localtype_same_len_None l1 l2 n:
  length l1 = length l2 ->
  get_localtype n l1 = None ->
  get_localtype n l2 = None.
  Proof.
    revert l2 n.
    induction l1; intros; destruct l2; destruct n; simpl in *; inversion H0; inversion H; auto.
    rewrite H0. eauto.
  Qed.

  Lemma LCEffEqual_add_local_effects : forall {C L1 L2} tl,
      LCEffEqual C L1 L2 ->
      LCEffEqual C
                 (add_local_effects L1 tl)
                 (add_local_effects L2 tl).
    Proof.
      intros C L1 L2 tl.
      revert C L1 L2.
      induction tl; simpl; intros; auto.
      destruct a.
      inversion H; subst.
      - destruct n; simpl; eauto.
      - destruct x. destruct y. destructAll.
        destruct n; simpl.
        + eapply IHtl.
          unfold set_localtype. simpl.
          econstructor; eauto.
        + destruct (get_localtype n l) eqn:Eq.
          ++ destruct p.
             enough (exists p', get_localtype n l' = Some p').
             destruct H0. destruct x.
             rewrite H0. unfold set_localtype.
             simpl. eapply IHtl. constructor; auto.
             eapply Forall2_nth_upd; eauto.
             apply forall2_nth_error  with
                 (v1 := (t0, s1)) (v2 := (t2, s2)) (i := n) in H1;
               auto.
             destructAll. split; auto.
             eapply get_localtype_same_len_Some with (l1 := l); eauto.
             eapply Forall2_length. eauto.
          ++ enough (get_localtype n l' = None).
             rewrite H0. eapply IHtl.
             constructor; auto.
             eapply get_localtype_same_len_None with (l1 := l); auto.
             eapply Forall2_length. eauto.
   Qed.

  Lemma Br_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Br i] (Arrow t1 t2) L' ->
    exists t1' taus1 taus1' L1 qf tl,
      M.is_empty (LinTyp S) = true /\
      nth_error (label F) i = Some (t1', L1) /\
      (forall j : nat,
          j <= i ->
          exists q : Qual,
            nth_error_plist (linear F) j = Some q /\
            QualLeq (qual F) q Unrestricted = Some true) /\
      t1 = taus1 ++ taus1' ++ t1' /\

      Forall (fun taus => TypQualLeq F taus Unrestricted = Some true) taus1' /\
      QualLeq (qual F) qf Unrestricted = Some true /\

      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) taus1  /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      LCEffEqual (size F) L L1 /\
      LCEffEqual (size F) (add_local_effects L tl) L'.
  Proof.
    assert (Heq : [Br i] = [Br i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Br i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; inv Heq. do 6 eexists; split. eassumption.
      split. eassumption. split. eassumption. split. rewrite app_assoc, app_nil_l. reflexivity.
      split. eassumption. split. eapply QualLeq_Refl.
      split; eauto.
      split; eauto.
      specialize (H2 0 ltac:(lia)). destructAll.
      rewrite nth_error_plist_hd_Zero in H2. inv H2. eassumption.
      split; apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll.
      inv Heq1.
      do 6 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      repeat ltac:(split; eauto).
      -- eapply LCEffEqual_trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *.

      do 6 eexists. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      + eassumption.
      + eassumption.
      + intros k Hleq.
        match goal with
        | [ H : forall _, _ <= _ -> _ |- _ ] => edestruct H
        end.
        eassumption. destructAll.

        destruct k.

        * rewrite nth_error_plist_hd_Zero in *.
          eexists. split. reflexivity.
          rewrite get_set_hd in *.
          match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst
          end.
          eapply QualLeq_Trans; eassumption.

        * match goal with
          | [ H : nth_error_plist _ (Datatypes.S _) = _ |- _ ] =>
            rewrite nth_error_plist_hd_Succ in H
          end.
          eauto.

      + rewrite app_assoc. reflexivity.

      + simpl. eassumption.
      + eassumption.
      + eapply Forall_app. split; [ | eassumption ].

        prepare_Forall. eapply QualLeq_Trans. eassumption.
        rewrite get_set_hd in *. eassumption.
      + eapply QualLeq_Trans. eassumption.
        rewrite get_set_hd in *. eassumption.
      + eauto.
    - start_lceff_subgoals.
      do 6 eexists; repeat ltac:(split; eauto).
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         apply LCEffEqual_sym; auto.
    - start_lceff_subgoals.
      do 6 eexists; repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
  Qed.

  Lemma Unreachable_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Unreachable] (Arrow t1 t2) L' ->
    exists tl,
      M.is_empty (LinTyp S) = true /\
      LCEffEqual (size F) (add_local_effects L tl) L'.
  Proof.
    assert (Heq : [Unreachable] = [Unreachable]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Unreachable] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - eexists. inv Heq1. split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll.
      eapply IHHtyp2 in Heq1; eauto.
      destructAll.
      eexists.
      split.
      -- eapply SplitStoreTypings_Empty'; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto.
      destruct F; subst; simpl in *.
      destructAll; eexists; split; eauto.
    - solve_lceff_subgoals ltac:(1).
      apply LCEffEqual_add_local_effects; auto.
    - solve_lceff_subgoals ltac:(1).
  Qed.

  Lemma Trap_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Trap] (Arrow t1 t2) L' ->
    exists tl,
      LCEffEqual (size F) (add_local_effects L tl) L'.
  Proof.
    assert (Heq : [Trap] = [Trap]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Trap] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - eexists. inv Heq1. apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll.
      eapply IHHtyp2 in Heq1; destructAll; auto.
      eexists; eapply LCEffEqual_trans; eauto.
      apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto.
      destruct F; subst; simpl in *.
      eauto.
    - solve_lceff_subgoals ltac:(1).
      apply LCEffEqual_add_local_effects; auto.
    - solve_lceff_subgoals ltac:(1).
  Qed.

  Lemma Select_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Select] (Arrow t1 t2) L' ->
    exists pt q1 q2 t,
      M.is_empty (LinTyp S) = true /\
      t1 = t ++ [QualT pt q1; QualT pt q1; QualT uint32T q2] /\
      t2 = t ++ [QualT pt q1] /\
      QualLeq (qual F) q1 Unrestricted = Some true /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Select] = [Select]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Select] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr i Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; eauto. inv Heq. do 3 eexists. exists []. split. eassumption.
      split. reflexivity.
      split. reflexivity. split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll. inv Heq1.
      do 4 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 4 eexists. split. eassumption. split.
      rewrite app_assoc. reflexivity. split. rewrite app_assoc. reflexivity.
      split. destruct F. eassumption.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma Block_HasTypeInstruction S M F L arr lf es t1 t2 L' :
    HasTypeInstruction S M F L [Block arr lf es] (Arrow t1 t2) L' ->

    exists t t1' t2' qf L'',
      t1 = t ++ t1' /\
      t2 = t ++ t2' /\
      arr = Arrow t1' t2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear F)) F in
      let F1 := update_label_ctx ((t2', L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      HasTypeInstruction S M F2 L es arr L' /\
      LCEffEqual (size F) (add_local_effects L lf) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    assert (Heq : [Block arr lf es] = [Block arr lf es]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Block arr lf es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros a i Heq Heq' Htyp.
    revert arr lf es t1 t2 Heq Heq'. induction Htyp; intros arr lf es_ t1 t2 Heq Heq1; try now inv Heq.
    - inv Heq. inv Heq1; eauto. exists []. do 4 eexists. split. reflexivity.
      split. reflexivity. split. reflexivity.
      split. now constructor.
      split. eapply QualLeq_Refl. split; eauto.
      rewrite !set_get_hd.
      destruct F. simpl in *. eassumption.
      split; [ apply LCEffEqual_refl | ].
      destruct F; subst; simpl in *; auto.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. eauto.
      simpl. setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 _ _ _ _ _ eq_refl eq_refl).
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inversion H; subst
      end.
      simpl in *; destructAll.
      do 5 eexists.
      repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
      -- destruct F; subst; simpl in *.
         eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F. simpl. subst. unfold F' in *. simpl in *.
      do 3 eexists. exists x2. eexists. split.
      rewrite app_assoc. reflexivity. split. rewrite app_assoc. reflexivity.
      split. reflexivity.

      split.
      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      simpl in *; destructAll.
      split; [ | split; auto ].
      -- rewrite set_set_hd in *. eauto.
      -- auto.
    - specialize (IHHtyp _ _ _ _ _ Heq Heq1).
      destruct F; subst; simpl in *.
      destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
      apply LCEffEqual_add_local_effects.
      apply LCEffEqual_sym; auto.
    - specialize (IHHtyp _ _ _ _ _ Heq Heq1).
      destruct F; subst; simpl in *.
      destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      -- eapply LCEffEqual_trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym; auto.
  Qed.

  Lemma Loop_HasTypeInstruction S M F L arr es t1 t2 L' :
    HasTypeInstruction S M F L [Loop arr es] (Arrow t1 t2) L' ->

    exists t t1' t2' qf L'',
      t1 = t ++ t1' /\
      t2 = t ++ t2' /\
      arr = Arrow t1' t2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear F)) F in
      let F1 := update_label_ctx ((t1', L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      HasTypeInstruction S M F2 L es arr L /\
      LCEffEqual (size F) L L' /\
      LCEffEqual (size F) L L''.
  Proof.
    assert (Heq : [Loop arr es] = [Loop arr es]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Loop arr es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros a i Heq Heq' Htyp.
    revert arr es t1 t2 Heq Heq'. induction Htyp; intros arr es_ t1 t2 Heq Heq1; try now inv Heq.
    - inv Heq. inv Heq1; eauto. exists []. do 4 eexists. split. reflexivity.
      split. reflexivity. split. reflexivity.
      split. now constructor.
      split. eapply QualLeq_Refl. simpl.
      rewrite !set_get_hd.
      destruct F. simpl in *. split; try eassumption.
      split; apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. eauto.
      simpl. setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 _ _ _ _ eq_refl Heq1).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; [ | eapply ChangeEndLocalTyp; eauto ].
         all: destruct F; subst; simpl in *.
         all: apply LCEffEqual_sym; auto.
      -- destruct F; subst; simpl in *; auto.
         eapply LCEffEqual_trans; eauto.
      -- destruct F; subst; simpl in *; auto.
         eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 3 eexists. exists x2. eexists.
      split. rewrite app_assoc. reflexivity. split. rewrite app_assoc. reflexivity.
      split. reflexivity.
      destruct F. simpl. subst. unfold F' in *. simpl in *.

      split.
      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      destruct linear. eassumption. eassumption.
    - specialize (IHHtyp _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; [ | eapply ChangeEndLocalTyp; eauto ].
         all: destruct F; subst; simpl in *; auto.
      -- destruct F; subst; simpl in *.
         eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym; auto.
      -- destruct F; subst; simpl in *.
         eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym; auto.
    - specialize (IHHtyp _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      destruct F; subst; simpl in *.
      eapply LCEffEqual_trans; [ | eauto ]; auto.
  Qed.

  Lemma ITE_HasTypeInstruction S M F L arr lf es1 es2 t1 t2 L' :
    HasTypeInstruction S M F L [ITE arr lf es1 es2] (Arrow t1 t2) L' ->

    exists t t1' t2' q qf L'',
      t1 = t ++ (t1' ++ [QualT uint32T q]) /\
      t2 = t ++ t2' /\
      arr = Arrow t1' t2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear F)) F in
      let F1 := update_label_ctx ((t2', L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      HasTypeInstruction S M F2 L es1 arr L' /\
      HasTypeInstruction S M F2 L es2 arr L' /\
      LCEffEqual (size F) (add_local_effects L lf) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    assert (Heq : [ITE arr lf es1 es2] = [ITE arr lf es1 es2]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [ITE arr lf es1 es2] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros a i Heq Heq' Htyp.
    revert arr lf es1 es2 t1 t2 Heq Heq'. induction Htyp; intros arr lf es1_ es2_ t1 t2 Heq Heq1; try now inv Heq.
    - inv Heq. inv Heq1; eauto. exists []. do 5 eexists.
      split. reflexivity. split. reflexivity. split. reflexivity.
      split. now constructor.
      split. eapply QualLeq_Refl. split; eauto.
      rewrite !set_get_hd.
      destruct F. simpl in *. eauto.
      split; eauto.
      rewrite !set_get_hd.
      destruct F. simpl in *. eauto.
      split; destruct F; simpl in *; auto; apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. eauto. simpl.

      setoid_rewrite <- (SplitStoreTypings_Empty_eq _ _ _ H) at 1; eauto.
      setoid_rewrite <- (SplitStoreTypings_Empty_eq _ _ _ H) at 1; eauto.

      specialize (IHHtyp2 _ _ _ _ _ _ eq_refl eq_refl).
      simpl in *; destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      do 6 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         destruct F; subst; simpl in *; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F. simpl. subst. unfold F' in *. simpl in *.
      destructAll.
      do 4 eexists. exists x3. eexists. split.
      rewrite app_assoc. reflexivity. split. rewrite app_assoc. reflexivity.
      split. reflexivity.

      split.
      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split; [ rewrite set_set_hd in *; eauto | ].
      split; [ rewrite set_set_hd in *; eauto | ].
      eauto.
    - specialize (IHHtyp _ _ _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 6 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
    - specialize (IHHtyp _ _ _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 6 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeEndLocalTyp; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply ChangeEndLocalTyp; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply LCEffEqual_trans; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply LCEffEqual_trans; eauto.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
  Qed.

  Lemma Label_HasTypeInstruction S M F L i arr es1 es2 t1 t2 L' :
    HasTypeInstruction S M F L [Label i arr es1 es2] (Arrow t1 t2) L' ->

    exists t t1' t2' qf L'',
      t1 = t /\
      t2 = t ++ t2' /\
      arr = Arrow [] t2' /\
      length t1' = i /\

      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\

      let F := update_linear_ctx (set_hd qf (linear F)) F in
      let F1 := update_label_ctx ((t1', L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in

      HasTypeInstruction (empty_LinTyp S) M F L' es1 (Arrow t1' t2') L' /\
      HasTypeInstruction S M F2 L es2 (Arrow [] t2') L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    assert (Heq : [Label i arr es1 es2] = [Label i arr es1 es2]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Label i arr es1 es2] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros a j Heq Heq' Htyp.
    revert i arr es1 es2 t1 t2 Heq Heq'. induction Htyp; intros j arr es1_ es2_ t1 t2 Heq Heq1; try now inv Heq.
    - inv Heq. inv Heq1; eauto. exists []. do 4 eexists. split. reflexivity.
      split. reflexivity. split. reflexivity.
      split. now constructor.
      split. now constructor. split. eapply QualLeq_Refl. split; eauto.
      rewrite !set_get_hd.
      destruct F. simpl in *; eauto.
      rewrite !set_get_hd.
      destruct F. simpl in *; split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll.
      eapply Empty_HasTypeInstruction in Htyp1. inv Heq1.
      destructAll. eauto.
      simpl. setoid_rewrite <- (SplitStoreTypings_Empty_eq _ _ _ H H3) at 1;
               eauto.
      simpl. setoid_rewrite <- (SplitStoreTypings_Empty_eq _ _ _ H H3) at 1;
               eauto.

      specialize (IHHtyp2 _ _ _ _ _ _ eq_refl eq_refl).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      eapply ChangeBegLocalTyp; eauto.
      destruct F; subst; simpl in *.
      apply LCEffEqual_sym; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F. simpl. subst. unfold F' in *. simpl in *.
      do 3 eexists. exists x2. eexists. split. reflexivity. split.
      rewrite app_assoc. reflexivity. split. reflexivity.
      split. reflexivity.

      split.
      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      split.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      destructAll.
      destruct linear; repeat split; eassumption.
    - specialize (IHHtyp _ _ _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      eapply ChangeBegLocalTyp; eauto.
      destruct F; subst; simpl in *; auto.
    - specialize (IHHtyp _ _ _ _ _ _ Heq Heq1).
      simpl in *; destructAll.
      do 5 eexists; repeat ltac:(split; eauto).
      -- eapply ChangeBegLocalTyp; [ | eapply ChangeEndLocalTyp; eauto ].
         all: destruct F; subst; simpl in *; auto.
      -- eapply ChangeEndLocalTyp; eauto.
         destruct F; subst; simpl in *; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym.
         destruct F; subst; simpl in *; auto.
  Qed.

  Lemma Br_if_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Br_if i] (Arrow t1 t2) L' ->
    exists t t1' q qf L'',
      M.is_empty (LinTyp S) = true /\
      nth_error (label F) i = Some (t1', L'') /\

      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\

      let F := update_linear_ctx (set_hd qf (linear F)) F in

      (forall j : nat,
          j <= i ->
          exists q : Qual,
            nth_error_plist (linear F) j = Some q /\
            QualLeq (qual F) q Unrestricted = Some true) /\
      t1 = t ++ t1' ++ [QualT uint32T q] /\
      t2 = t ++ t1' /\
      LCEffEqual (size F) L L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    assert (Heq : [Br_if i] = [Br_if i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Br_if i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; inv Heq. destruct F. simpl in *.
      exists []. do 4 eexists; split. eassumption.
      split. eassumption.
      split. now eapply QualLeq_Refl.
      split. now constructor.
      simpl. rewrite set_get_hd. split. eassumption.
      split; eauto.
      split; eauto.
      split; apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity. destructAll. inv Heq1.
      do 5 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      simpl in *; destructAll.
      repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
      destruct F; subst; simpl in *; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. simpl in *. destructAll.
      unfold F' in *. destruct F; simpl in *.
      do 5 eexists. split. eassumption.

      rewrite get_set_hd in *.

      split; [| split; [| split; [| split; [| split; [| split ] ]]] ].
      eassumption.
      5:{ rewrite app_assoc; reflexivity. }
      4:{ rewrite app_assoc; reflexivity. }
      2:{ eapply Forall_app. split; [|  eassumption ].
          prepare_Forall. eapply QualLeq_Trans; eassumption. }

      + eapply QualLeq_Trans; eassumption.
      + rewrite set_set_hd in *. eauto.
      + split; auto.
    - solve_lceff_subgoals ltac:(5).
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(5).
      all: destruct F; subst; simpl in *; auto.
      apply LCEffEqual_sym; auto.
  Qed.

  Lemma Br_table_HasTypeInstruction S M F L t1 t2 L' l i :
    HasTypeInstruction S M F L [Br_table l i] (Arrow t1 t2) L' ->
    exists t t1'' t1' t2' q qf tl L'',
      M.is_empty (LinTyp S) = true /\
      Forall (fun i : nat => nth_error (label F) i = Some (t1', L'')) (l ++ [i]) /\
      Forall (fun tau : Typ => TypQualLeq F tau Unrestricted = Some true) t1'' /\

      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\

      let F := update_linear_ctx (set_hd qf (linear F)) F in

      (forall j : nat,
          j <= list_max (l ++ [i]) ->
          exists q : Qual,
            nth_error_plist (linear F) j = Some q /\
            QualLeq (qual F) q Unrestricted = Some true) /\
      t1 = t ++ t1'' ++ t1' ++ [QualT uint32T q] /\
      t2 = t ++ t2' /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L L''.
  Proof.
    assert (Heq : [Br_table l i] = [Br_table l i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Br_table l i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; inv Heq. do 8 eexists. split. eassumption.
      split. eassumption.
      split. eassumption. split. eapply QualLeq_Refl.
      split. now constructor.
      simpl. split. rewrite set_get_hd.
      destruct F. eassumption.
      split. reflexivity. split; [ reflexivity | ].
      split; apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.
      destructAll. inv Heq1. do 8 eexists.
      split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      simpl in *; destructAll.
      repeat ltac:(split; eauto).
      all: destruct F; subst; simpl in *.
      all: eapply LCEffEqual_trans; eauto.
      apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto.
      destruct F; simpl in *. destructAll.

      do 8 eexists. split. eassumption. split. eassumption.
      rewrite get_set_hd in *.
      split; [| split; [| split; [| split; [| split; [| split]]]]].

      5:{ rewrite app_assoc; reflexivity. }
      5:{ rewrite app_assoc; reflexivity. }
      3:{ eapply Forall_app. split; [|  eassumption ].
          prepare_Forall. eapply QualLeq_Trans; eassumption. }

      + eassumption.
      + eapply QualLeq_Trans; eassumption.
      + rewrite set_set_hd in *. eauto.
      + split; eauto.
    - solve_lceff_subgoals ltac:(8).
      -- apply LCEffEqual_add_local_effects.
         destruct F; subst; simpl in *; auto.
      -- destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(8).
      destruct F; subst; simpl in *.
      apply LCEffEqual_sym; auto.
  Qed.

  Lemma Ret_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Ret] (Arrow t1 t2) L' ->
    exists ts taus1' taus1 taus2 qf tl,
      M.is_empty (LinTyp S) = true /\
      ret F = Some taus1'  /\
      Forall
        (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) L /\

      Forall (fun taus => TypQualLeq F taus Unrestricted = Some true) taus1 /\

      Forall_plist (fun q : Qual => QualLeq (qual F) q Unrestricted = Some true)
                   (linear F) /\

      QualLeq (qual F) qf Unrestricted = Some true /\

      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\

      t1 = ts ++ taus1 ++ taus1' /\
      t2 = ts ++ taus2 /\
      LCEffEqual (size F) (add_local_effects L tl) L'.
  Proof.
    assert (Heq : [Ret] = [Ret]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Ret] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 5 eexists; repeat split; eauto.
      eapply QualLeq_Refl.

      destruct linear.
      + inv H3. simpl; eassumption.
      + inv H3. simpl. eassumption.
      + apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.
      destructAll. inv Heq1. do 6 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now eauto.

      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      simpl in *; destructAll.
      repeat (split; eauto).
      -- eapply LCEffEqual_Forall; eauto.
         apply LCEffEqual_sym; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 6 eexists. esplit; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
      eassumption. reflexivity. eassumption.


      6:{ rewrite app_assoc. reflexivity. }

      6:{ rewrite app_assoc. reflexivity. }


      eapply Forall_impl; [| eassumption ]. intros [? ?].
      now unfold TypQualLeq; eauto.

      simpl.

      { destruct linear; simpl in *.
        all:
          match goal with
          | [ H : Forall_plist _ _ |- _ ] =>
            inversion H; subst; simpl in *
          end.
        all: constructor.
        all: try ltac:(eapply QualLeq_Trans; eassumption).
        all: auto. }

      2:{ eapply Forall_app. split; [| eassumption ].

          prepare_Forall.
          eapply QualLeq_Trans. eassumption.
          rewrite get_set_hd in *. eassumption. }

      2:{ eapply QualLeq_Trans. eassumption.
          rewrite get_set_hd in *. eassumption. }

      eassumption.
      eauto.
    - start_lceff_subgoals.
      do 6 eexists; repeat ltac:(split; eauto).
      -- eapply LCEffEqual_Forall; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         apply LCEffEqual_sym; auto.
    - solve_lceff_subgoals ltac:(6).
  Qed.

  Lemma Get_local_unr_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Get_local i Unrestricted] (Arrow t1 t2) L' ->
    qual F = [] ->
    exists pt sz,
      M.is_empty (LinTyp S) = true /\
      t1 ++ [QualT pt Unrestricted] = t2 /\
      nth_error L i = Some (QualT pt Unrestricted, sz) /\
      LCEffEqual (size F) (set_localtype i (QualT pt Unrestricted) sz L) L'.
  Proof.
    intros.
    apply Get_local_HasTypeInstruction in H.
    destructAll.
    match goal with
    | [ X : bool |- _ ] => destruct X
    end.
    all:
      repeat match goal with
             | [ H : ?A = ?A -> _ |- _ ] =>
               specialize (H eq_refl)
             end.
    - do 2 eexists; repeat ltac:(split; eauto).
      subst; auto.
    - exfalso.
      eapply QualLeq_Const_False.
      match goal with
      | [ H : _ = [] |- _ ] => rewrite <-H; auto
      end.
  Qed.

  Lemma Get_local_lin_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Get_local i Linear] (Arrow t1 t2) L' ->
    qual F = [] ->
    exists pt sz,
      M.is_empty (LinTyp S) = true /\
      t1 ++ [QualT pt Linear] = t2 /\
      nth_error L i = Some (QualT pt Linear, sz) /\
      LCEffEqual (size F) (set_localtype i (QualT Unit Unrestricted) sz L) L'.
  Proof.
    intros.
    apply Get_local_HasTypeInstruction in H.
    destructAll.
    match goal with
    | [ X : bool |- _ ] =>
      assert (X = false);
      [ remember X as obj; generalize (eq_sym Heqobj);
        case obj; auto | ]
    end.
    { intros; subst.
      exfalso; eapply QualLeq_Const_False; eauto.
      match goal with
      | [ H : _ = [] |- _ ] => rewrite <-H; auto
      end. }
    subst.
    repeat match goal with
           | [ H : ?A = ?A -> _ |- _ ] =>
             specialize (H eq_refl)
           end.
    do 2 eexists; repeat ltac:(split; eauto).
    subst; auto.
  Qed.

  Lemma Get_global_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Get_global i] (Arrow t1 t2) L' ->
    exists mut pt,
      M.is_empty (LinTyp S) = true /\
      t2 = t1 ++ [QualT pt Unrestricted] /\
      nth_error (global M) i = Some (GT mut pt) /\
      LCEffEqual (size F) L L'.
    Proof.
    assert (Heq : [Get_global i] = [Get_global i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Get_global i] at 1 3.
    generalize (Arrow t1 t2) at 1 3.
    intros arrtyp linst Heq Heq' Htyp.
    revert t1 t2 Heq'.
    induction Htyp; intros t1 t2 Heq1; try now inversion Heq1.
    - inversion Heq1; inversion Heq; subst. simpl in *.
      do 2 eexists; repeat ltac:(split; eauto).
      apply LCEffEqual_refl.
    - assert (Heq': es = [] /\ e = Get_global i).
      {
        induction es; inversion Heq; auto.
        destruct es; inversion H2.
      }
      destructAll.
      apply Empty_HasTypeInstruction in Htyp1.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      destructAll.
      exists x. exists x0.
      split; auto.
      eapply SplitStoreTypings_Empty'; eauto.
      split; auto.
      injection Heq1. intros. subst. auto.
      split; auto.
      eapply LCEffEqual_trans; eauto.
    - inversion Heq1; subst.
      specialize (IHHtyp eq_refl _ _ eq_refl).
      destructAll.
      exists x. exists x0.
      split; auto.
      split; auto.
      simpl.
      rewrite app_assoc. auto.
      split; auto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

  Lemma Set_global_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Set_global i] (Arrow t1 t2) L' ->
    exists pt q,
      M.is_empty (LinTyp S) = true /\
      t1 = t2 ++ [QualT pt q] /\
      QualLeq (qual F) q Unrestricted = Some true /\
      nth_error (global M) i = Some (GT true pt) /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Set_global i] = [Set_global i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Set_global i] at 1 3.
    generalize (Arrow t1 t2) at 1 3.
    intros arrtyp linst Heq Heq' Htyp.
    revert t1 t2 Heq'.
    induction Htyp; intros t1 t2 Heq1; try now inversion Heq1.
    - inversion Heq; inversion Heq1; subst. simpl in *.
      eexists. eexists.
      repeat split; eauto.
      apply LCEffEqual_refl.
    - inversion Heq1; subst. assert (Heq': es = [] /\ e = Set_global i).
      {
        induction es; inversion Heq; auto.
        destruct es; inversion H2.
      }
      destructAll.
      destructAll.
      apply Empty_HasTypeInstruction in Htyp1.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      destructAll.
      exists x. exists x0.
      split; auto.
      eapply SplitStoreTypings_Empty'; eauto.
      repeat ltac:(split; eauto).
      eapply LCEffEqual_trans; eauto.
    - inversion Heq1; subst.
      specialize (IHHtyp eq_refl _ _ eq_refl).
      destructAll.
      exists x. exists x0.
      split; auto.
      split; auto.
      rewrite app_assoc. auto.
      split; auto.
      unfold  F' in *.
      destruct F. simpl in *. eauto.
      split; auto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

  Lemma Call_indirect_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [Call_indirect] (Arrow t1 t2) L' ->
    exists alpha taus1 taus2 q,
      M.is_empty (LinTyp S) = true /\
      t1 = alpha ++ taus1 ++ [QualT (CoderefT (FunT [] (Arrow taus1 taus2))) q] /\
      t2 = alpha ++ taus2 /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Call_indirect] = [Call_indirect]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Call_indirect] at 1 3.
    generalize (Arrow t1 t2) at 1 3.
    intros arrtyp linst Heq Heq' Htyp.
    revert t1 t2 Heq'.
    induction Htyp; intros t1 t2 Heq1; try now inversion Heq1.
    - inversion Heq; inversion Heq1; subst. simpl in *.
      exists []. do 3 eexists; repeat ltac:(split; eauto).
      apply LCEffEqual_refl.
    - inversion Heq1; subst.
      assert (Heq': es = [] /\ e = Call_indirect).
      {
        induction es; inversion Heq; auto.
        destruct es; inversion H2.
      }
      destructAll.
      apply Empty_HasTypeInstruction in Htyp1.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      destructAll.
      do 4 eexists; repeat ltac:(split; eauto).
      -- eapply SplitStoreTypings_Empty'; eauto.
      -- eapply LCEffEqual_trans; eauto.
    - inversion Heq1; inversion Heq; subst.
      specialize (IHHtyp eq_refl  _ _ eq_refl).
      destructAll.
      unfold F' in *.
      do 4 eexists.
      split; auto.
      split; rewrite app_assoc; eauto.
      split; auto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma InstIndValid_Function_Ctx_stronger : forall {F F' kvs atyp atyp' idx},
      location F = location F' ->
      qual F = qual F' ->
      size F = size F' ->
      type F = type F' ->
      InstIndValid F (FunT kvs atyp) idx ->
      InstIndValid F' (FunT kvs atyp') idx.
  Proof.
    intros.
    destruct idx.
    all:
      match goal with
      | [ H : InstIndValid _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    - apply LocIndValid; auto.
      all:
        match goal with
        | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
        end.
    - apply SizeInstValid; auto.
      all:
        match goal with
        | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
        end.
    - apply QualInstValid; auto.
      all:
        match goal with
        | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
        end.
    - eapply TypeInstValid; eauto.
      3: eapply TypeValid_Function_Ctx; eauto.
      all: unfold heapable.
      all:
        match goal with
        | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; eauto
        end.
  Qed.

  Lemma InstIndsValid_cons_inv : forall {idxs idx F foralls tau1 tau2},
    InstIndsValid F (FunT foralls (Arrow tau1 tau2)) (idx :: idxs) ->
    exists foralls' tau1' tau2',
      InstIndValid F (FunT foralls (Arrow tau1 tau2)) idx /\
      InstInd (FunT foralls (Arrow tau1 tau2)) idx =
      Some (FunT foralls' (Arrow tau1' tau2')) /\
      InstIndsValid F (FunT foralls' (Arrow tau1' tau2')) idxs.
  Proof.
    intros.
    inversion H; subst.
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    match goal with
    | [ X : ArrowType |- _ ] => destruct X
    end.
    do 3 eexists; eauto.
  Qed.

  Lemma InstInd_arrowtype_no_effect_on_kindvars : forall {kv atyp idx kv' atyp' atyp2},
      InstInd (FunT kv atyp) idx = Some (FunT kv' atyp') ->
      exists atyp2',
        InstInd (FunT kv atyp2) idx = Some (FunT kv' atyp2').
  Proof.
    intros.
    destruct idx.
    all: simpl in *.
    all: destruct kv; simpl in *.
    all:
      try match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          end.
    all: match goal with
         | [ X : KindVar |- _ ] => destruct X
         end.
    all: match goal with
         | [ H : None = Some _ |- _ ] => inversion H
         | [ H : Some _ = Some _ |- _ ] => inversion H; subst
         end.
    all: eauto.
  Qed.

  Lemma InstIndsValid_Function_Ctx_stronger : forall {idxs F F' kvs atyp atyp'},
      location F = location F' ->
      qual F = qual F' ->
      size F = size F' ->
      type F = type F' ->
      InstIndsValid F (FunT kvs atyp) idxs ->
      InstIndsValid F' (FunT kvs atyp') idxs.
  Proof.
    induction idxs.
    - constructor.
    - intros; simpl in *.
      repeat match goal with
             | [ X : ArrowType |- _ ] => destruct X
             end.
      match goal with
      | [ H : InstIndsValid _ _ _ |- _ ] =>
        apply InstIndsValid_cons_inv in H
      end.
      destructAll.
      match goal with
      | [ H : InstInd _ _ = Some _
          |- _ _ (_ _ ?L) _ ] =>
        specialize (InstInd_arrowtype_no_effect_on_kindvars (atyp2:=L) H)
      end.
      intros; destructAll.
      econstructor; eauto.
      eapply InstIndValid_Function_Ctx_stronger; eauto.
  Qed.

  Lemma Call_HasTypeInstruction S M F L t1 t2 L' i is :
    HasTypeInstruction S M F L [term.Call i is] (Arrow t1 t2) L' ->
    exists tauf taus1 taus2 chi,
      t1 = tauf ++ taus1 /\
      t2 = tauf ++ taus2 /\
      M.is_empty (LinTyp S) = true /\
      nth_error (func M) i = Some chi /\
      InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) /\
      InstIndsValid F chi is /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [term.Call i is] = [term.Call i is]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [term.Call i is] at 1 3.
    generalize (Arrow t1 t2) at 1 3.
    intros arrtyp linst Heq Heq' Htyp.
    revert t1 t2 Heq'.
    induction Htyp; intros t1 t2 Heq1; try now inversion Heq1.
    - inversion Heq; inversion Heq1; subst. simpl in *.
      exists nil.
      repeat eexists; eauto.
      apply LCEffEqual_refl.
    - inversion Heq1; subst.
      assert (Heq': es = [] /\ e = term.Call i is).
      {
        induction es; inversion Heq; auto.
        destruct es; inversion H2.
      }
      destructAll.
      apply Empty_HasTypeInstruction in Htyp1.
      specialize (IHHtyp2 eq_refl _ _ eq_refl).
      destructAll.
      repeat eexists; eauto.
      -- eapply SplitStoreTypings_Empty'; eauto.
      -- eapply LCEffEqual_trans; eauto.
    - inversion Heq1; subst.
      specialize (IHHtyp eq_refl _ _ eq_refl).
      destructAll.
      exists (taus ++ x).
      exists x0. exists x1. exists x2.
      split; eauto.
      rewrite app_assoc. auto.
      split; eauto.
      rewrite app_assoc. auto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      repeat match goal with
             | [ X : FunType |- _ ] => destruct X
             | [ X : ArrowType |- _ ] => destruct X
             end.
      unfold F' in *. destruct F. simpl in *.
      eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ]; eauto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma Local_HasTypeInstruction S M F L ri mi vl szs es t1 t2 L' :
    HasTypeInstruction S M F L [Local ri mi vl szs es] (Arrow t1 t2) L' ->
    exists taus,
      t2 = t1 ++ taus /\
      length taus = ri /\
      HasTypeConf S (Some taus) mi vl (map SizeConst szs) es taus /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Local ri mi vl szs es] = [Local ri mi vl szs es])
      by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Local ri mi vl szs es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll.
      eapply Empty_HasTypeInstruction in Htyp1.
      destructAll.
      setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 eq_refl _ _ Heq1).
      destructAll.
      eexists; repeat split; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      eexists. split; [| split; [| split ]].
      rewrite app_assoc. reflexivity. reflexivity.
      eassumption.
      auto.
    - solve_lceff_subgoals ltac:(1).
    - solve_lceff_subgoals ltac:(1).
  Qed.

  Lemma HasTypeValue_Unrestricted_LinEmpty v :
    forall S F pt q
           (Ht : HasTypeValue S F v (QualT pt q))
           (Hleq : QualLeq (qual F) q Unrestricted = Some true)
           (Hempty : qual F = []),
      M.is_empty (LinTyp S) = true.
  Proof.
    eapply Value_ind' with (v := v); intros; inv Ht; eauto.
    - eapply H. eassumption.
      inv H5.
      eapply QualLeq_Trans. exact H8. exact Hleq.
      auto.
    - inv H7.
      eapply SplitStoreTypings_Empty'. eassumption.
      revert H H6 H4 Hleq Hempty. clear. intros Hall Hall3 Hall' Hleq Hempty.
      induction Hall3.
      + now constructor.
      + inv Hall. inv Hall'.
        constructor; eauto.

        destruct z. eapply H2. eassumption.

        simpl in *.
        eapply QualLeq_Trans; eassumption.
        auto.
    - exfalso. eapply QualLeq_Const_False.
      rewrite <-Hempty.
      eapply QualLeq_Trans; eassumption.
    - exfalso. eapply QualLeq_Const_False.
      rewrite <-Hempty.
      eapply QualLeq_Trans; eassumption.
    - destruct t. simpl in *. eapply H.
      eassumption.
      simpl.
      assert (subst_eq: subst.subst'_qual
                          (debruijn.subst'_of (debruijn.ext subst.SLoc l debruijn.id)) q0 = q0).
      {
        destruct q0; simpl; auto.
      }
      rewrite subst_eq.
      inversion H7; subst.
      eapply QualLeq_Trans; eauto.
      auto.
  Qed.

  Lemma Forall3_HasTypeValue_Unrestricted_LinEmpty F Ss vs ts :
        Forall3 (fun S v t => HasTypeValue S F v t) Ss vs ts ->
        Forall (fun '(QualT _ q) => QualLeq (qual F) q Unrestricted = Some true) ts ->
        qual F = [] ->
        Forall (fun S => M.is_empty (LinTyp S) = true) Ss.
  Proof.
    intros H3 Hall; induction H3; simpl in *; eauto.
    inv Hall.
    constructor; eauto.
    destruct z. eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
  Qed.

  Lemma Context_HasTypeInstruction_Ret S M F r r' vs L L' L''
        i (C : context i) (Hvs : values vs) :
    well_formed_in_context (C |[ vs ++ [ Ret ] ]|)  ->
    forallb well_formed_Inst (C |[ vs ++ [ Ret ] ]|) = true ->
    HasTypeInstruction S M F L (C |[ vs ++ [ Ret ] ]|) (Arrow [] r') L' ->

    ret F = Some r ->
    get_hd (linear F) = Unrestricted ->
    length r = length vs ->
    forall (Hempty : qual F = []),
    forall (Hvalid : LocalCtxValid F L''),

    Forall_plist
      (fun q : Qual => QualLeq (qual F) q Unrestricted = Some true)
      (linear F) /\
    Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) L /\
    HasTypeInstruction S M F L'' vs (Arrow [] r) L''.
  Proof.
    revert S M F r r' vs L L' L'' Hvs;
      induction C; simpl; intros S M F r r' vs L L' L'' Hvs Hwf Hwf' Htyp Hret Hhd Hlen Hempty.
    - rewrite app_assoc in Htyp.
      eapply composition_typing in Htyp. simpl in *. destructAll.
      symmetry in H. eapply app_eq_nil in H.
      destructAll. simpl in *. clear H1.

      eapply composition_typing in H3. destructAll.
      symmetry in H. eapply app_eq_nil in H. destructAll. clear H1.

      destruct F; simpl in *; destructAll.
      rewrite !get_set_hd in *. rewrite !set_set_hd in *.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ [Ret]) _ _ |- _ ] =>
        eapply composition_typing in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Ret] _ _ |- _ ] =>
        eapply Ret_HasTypeInstruction in H; simpl in *; destructAll
      end.

      rewrite !get_set_hd in *. rewrite !set_set_hd in *.
      match goal with
      | [ H'' : values ?VS,
          H' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        eapply Values_HasTypeInstruction with (H := H'') in H'
      end.
      
      intros; destructAll.

      eapply Values_HasTypeInstruction with (H := values_Val l) in H. destructAll.
      simpl in *; subst.

      split; [ | split ].

      + destruct linear.
        * constructor.
          simpl in *. subst.  eapply QualLeq_Refl.
        * simpl in *.
          match goal with
          | [ H : Forall_plist _ _ |- _ ] => inversion H; subst
          end.
          constructor; eauto.
          simpl in *. eapply QualLeq_Refl.

      + eapply LCEffEqual_Forall; [ | eauto | eauto ].
        apply LCEffEqual_sym.
        eapply LCEffEqual_trans; eauto.
      + eapply SplitStoreTypings_Empty_eq in H0.
        2:{ eapply SplitStoreTypings_comm. eassumption. }

        assert (Hneq : vs ++ [Ret] <> [] ).
        { intro Heq. destruct vs; inv Heq. }
        
        match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] =>
          assert (Hlen' := Forall3_length _ _ _ _ H); destructAll
        end.
        rewrite !to_values_len in *.

        match goal with
        | [ H : _ ++ _ = _ ++ _ ++ _ |- _ ] =>
          rewrite !app_assoc in H; eapply app_eq_len in H; [| congruence ]
        end.

        destructAll.

        assert (Hleq : QualLeq [] x15 Unrestricted = Some true).
        { destruct linear.
          all:
            match goal with
            | [ H : Forall_plist _ _ |- _ ] => inversion H; eauto
            end. }

        match goal with
        | [ H : Forall _ (_ ++ _) |- _ ] =>
          eapply Forall_app in H; destructAll
        end.
        rewrite get_set_hd in *.

        match goal with
        | [ H : Forall3 _ ?SS _ (_ ++ _),
            H' : SplitStoreTypings ?SS _ |- _ ] =>
          eapply SplitStoreTypings_Empty' in H'
        end.
        2:{ eapply Forall3_HasTypeValue_Unrestricted_LinEmpty.
            eassumption. simpl.
            eapply Forall_app.
            split.

            prepare_Forall.
            eapply QualLeq_Trans. eassumption. eassumption.

            eapply Forall_app. split.

            prepare_Forall.
            eapply QualLeq_Trans. eassumption. eassumption.

            eapply Forall_impl; [| eassumption ].
            simpl. intros [? ?] ?. eassumption. simpl; auto. }


        eapply SplitStoreTypings_Empty_eq in H1; [| eassumption ].

        eapply HasTypeInstruction_surface in H4.
        2:{ assert (Hex : existsb nonval_Inst (vs ++ [Ret]) = true).
            { rewrite existsb_app. do_bools. right; reflexivity. }
            specialize (Hwf 0 (LZero l l0) (vs ++ [Ret]) Hneq Hex ltac:(reflexivity)).
            eassumption. }

        match goal with
        | [ H : Some _ = Some _ |- _ ] => inversion H; subst
        end.

        eapply HasTypeInstruction_Values.

        2:{ eapply Forall3_monotonic; [| eassumption ].
            simpl; intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
            reflexivity. }

        eapply SplitStoreTypings_comm in H5.
        eapply SplitStoreTypings_Empty_eq in H5; [| eassumption ].

        eapply SplitStoreTyping_eq. eassumption.
        rewrite H0, H1.  eassumption.

        eapply LocalCtxValid_Function_Ctx; eauto.

    - replace (map Val l ++ Label n a l0 (C |[ vs ++ [Ret] ]|) :: l1)
        with ((map Val l ++ [Label n a l0 (C |[ vs ++ [Ret] ]|)]) ++ l1)
        in Htyp.
      2:{ rewrite <- app_assoc. simpl. reflexivity. }

      eapply composition_typing in Htyp. destructAll.
      destruct F; simpl in *. destructAll.

      symmetry in H. eapply app_eq_nil in H. destructAll.

      eapply composition_typing_single_strong in H0. destructAll.
      simpl in *. destructAll.
      symmetry in H. eapply app_eq_nil in H. destructAll.

      rewrite !get_set_hd in *. rewrite !set_set_hd in *.
      intros; destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Label _ _ _ _] _ _ |- _ ] =>
        eapply Label_HasTypeInstruction in H; destructAll
      end.
      simpl in *; destructAll.
      rewrite !get_set_hd in *. rewrite !set_set_hd in *.
      intros.

      do_forall_app. simpl in *. repeat do_bools. destructAll.

      edestruct IHC.
      2:{ eapply well_formews_Inst_list_is_well_formed_in_context. eassumption. }
      eassumption. eassumption. eassumption.

      simpl. reflexivity.
      simpl. reflexivity.
      eassumption.
      
      simpl in *.
      simpl; auto.
      
      eapply LocalCtxValid_Function_Ctx; eauto.

      eapply Values_HasTypeInstruction with (H := values_Val l) in H0. destructAll.
      simpl in *; subst.

      split; [| split ].

      + match goal with
        | [ H : Forall_plist _ _ |- _ ] =>
          inversion H; subst; clear H
        end.
        destruct linear;
          match goal with
          | [ H : Forall_plist _ _ |- _ ] => inversion H; subst
          end.
        * constructor. simpl in *; subst.
          apply QualLeq_Refl.
        * constructor; eauto.
          simpl in *; subst. apply QualLeq_Refl.

      + eapply LCEffEqual_Forall; [ | eauto | eauto ].
        apply LCEffEqual_sym.
        eapply LCEffEqual_trans; eauto.
        apply LCEffEqual_refl.
      + match goal with
        | [ H' : values ?VS,
            H'' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
          eapply Values_HasTypeInstruction with (H:=H') in H''
        end.
        destructAll.
        simpl in *.
        eapply HasTypeInstruction_Values.

        2:{ eapply Forall3_monotonic; [| eassumption ].
            simpl; intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
            reflexivity. }

        eapply SplitStoreTyping_eq. eassumption.

        match goal with
        | [ H : Forall3 _ ?SS _ ?TS,
            H' : SplitStoreTypings ?SS _,
            H'' : Forall _ ?TS |- _ ] =>
          eapply SplitStoreTypings_Empty' in H'
        end.
        2:{ eapply Forall3_HasTypeValue_Unrestricted_LinEmpty. eassumption.
            simpl.
            eapply Forall_impl; [| eassumption ].
            simpl. intros [? ?] ?.
            eapply QualLeq_Trans. eassumption.
            match goal with
            | [ H : Forall_plist _ _ |- _ ] =>
              inversion H
            end.
            destruct linear;
              match goal with
              | [ H : Forall_plist _ _ |- _ ] =>
                inversion H; subst; eauto
              end.
            simpl; auto. }
        match goal with
        | [ H : M.is_empty (LinTyp ?S) = true,
            H' : SplitStoreTypings [?S; _] _ |- _ ] =>
          eapply SplitStoreTypings_Empty_eq in H; [| eassumption ];
          rewrite H
        end.

        assert (Hneq : vs ++ [Ret] <> [] ).
        { intro Heq. destruct vs; inv Heq. }

        eapply HasTypeInstruction_surface in H3.
        2:{ assert (Hex : existsb nonval_Inst (vs ++ [Ret]) = true).
            { rewrite existsb_app. do_bools. right; reflexivity. }

            specialize (Hwf (1 + k) (LSucc_label k l (length x0) (Arrow [] x2) l0 C l1) (vs ++ [Ret]) Hneq Hex ltac:(reflexivity)).
            simpl in Hwf. eassumption. }

        eapply SplitStoreTypings_comm in H4.
        eapply SplitStoreTypings_Empty_eq in H4; [| eassumption ].
        eassumption.
        auto.
  Qed.

  Lemma Context_HasTypeInstruction_Br S M F r r' vs L L' L'' L0
        j i (C : context i) (Hvs : values vs) :
    well_formed_in_context (C |[ vs ++ [ Br j ] ]|)  ->
    forallb well_formed_Inst (C |[ vs ++ [ Br j ] ]|) = true ->
    HasTypeInstruction S M F L (C |[ vs ++ [ Br j ] ]|) (Arrow [] r') L' ->

    j >= i ->

    nth_error (label F) (j - i) = Some (r, L0) ->

    get_hd (linear F) = Unrestricted ->
    length r = length vs ->
    forall (Hempty : qual F = []),
    forall (Hvalid : LocalCtxValid F L''),

    (forall m, m <= (j - i) ->
               exists q,
                 nth_error_plist (linear F) m = Some q /\
                 QualLeq (qual F) q Unrestricted = Some true) /\
    HasTypeInstruction S M F L'' vs (Arrow [] r) L'' /\
    LCEffEqual (size F) L0 L.
  Proof.
    revert S M F r r' vs L L' L'' j Hvs;
      induction C; simpl;
        intros S M F r r' vs L L' L'' j Hvs Hwf Hwf' Htyp Hleq Hret Hhd Hlen Hempty Hvalid.
    - rewrite app_assoc in Htyp.
      eapply composition_typing in Htyp. simpl in *. destructAll.
      symmetry in H. eapply app_eq_nil in H.
      destructAll. simpl in *. clear H1.

      eapply composition_typing in H3. destructAll.
      symmetry in H. eapply app_eq_nil in H. destructAll. clear H1.

      destruct F; simpl in *; destructAll.
      rewrite !get_set_hd in *. rewrite !set_set_hd in *.

      eapply composition_typing in H0. simpl in *; destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Br _] _ _ |- _ ] =>
        eapply Br_HasTypeInstruction in H; simpl in *; destructAll
      end.

      rewrite !get_set_hd in *. rewrite !set_set_hd in *.

      rewrite Nat.sub_0_r in *.
      match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] => rewrite H in H'; inv H'
      end.
      
      match goal with
      | [ H' : values ?VS,
          H'' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        eapply Values_HasTypeInstruction with (H:=H') in H''
      end.
      destructAll.

      eapply Values_HasTypeInstruction with (H := values_Val l) in H. destructAll.
      simpl in *; subst.

      split; [| split ].

      + intros m Hleq'.
        match goal with
        | [ H : forall _, _ <= _ -> _, H' : _ <= _ |- _ ] =>
          specialize (H _ H')
        end.
        destructAll.
        destruct m.
        * eexists (get_hd linear).
          rewrite nth_error_plist_hd_Zero. split; eauto.
          rewrite Hhd. eapply QualLeq_Refl.
        * rewrite nth_error_plist_hd_Succ in H.
          eexists. split; eauto.

      + eapply SplitStoreTypings_Empty_eq in H0.
        2:{ eapply SplitStoreTypings_comm. eassumption. }

        assert (Hneq : vs ++ [Br j] <> [] ).
        { intro Heq. destruct vs; inv Heq. }


        match goal with
        | [ H : Forall3 _ _ _ _, H' : Forall3 _ _ _ _ |- _ ] =>
          specialize (Forall3_length _ _ _ _ H);
          specialize (Forall3_length _ _ _ _ H')
        end.
        intros; destructAll.
        rewrite !to_values_len in *.

        match goal with
        | [ H : _ ++ _ = _ ++ _ ++ _ |- _ ] =>
          rewrite !app_assoc in H;
          eapply app_eq_len in H; [| congruence ]
        end.

        destructAll.

        assert (HleqU : QualLeq [] x15 Unrestricted = Some true).
        { match goal with
          | [ H : forall _, _ <= _ -> _ |- _ ] =>
            specialize (H 0 ltac:(lia))
          end.
          destructAll.
          match goal with
          | [ H : nth_error_plist _ 0 = Some _ |- _ ] =>
            rewrite nth_error_plist_hd_Zero in H;
            rewrite get_set_hd in *; inv H
          end.
          eassumption. }

        match goal with
        | [ H : Forall _ (_ ++ _) |- _ ] =>
          eapply Forall_app in H; destructAll
        end.
        rewrite get_set_hd in *.

        match goal with
        | [ H : Forall3 _ ?SS _ _,
            H' : SplitStoreTypings ?SS _ |- _ ] =>
          eapply SplitStoreTypings_Empty' in H'
        end.
        2:{ eapply Forall3_HasTypeValue_Unrestricted_LinEmpty.
            eassumption. simpl.
            eapply Forall_app.
            split.

            prepare_Forall.
            eapply QualLeq_Trans. eassumption. eassumption.


            eapply Forall_app. split.

            prepare_Forall.
            eapply QualLeq_Trans. eassumption. eassumption.

            eapply Forall_impl; [| eassumption ].
            simpl. intros [? ?] ?. eassumption. simpl; auto. }

        eapply SplitStoreTypings_Empty_eq in H1; [| eassumption ].

        eapply HasTypeInstruction_surface in H4.
        2:{ assert (Hex : existsb nonval_Inst (vs ++ [Br j]) = true).
            { rewrite existsb_app. do_bools. right; reflexivity. }
            specialize (Hwf 0 (LZero l l0) (vs ++ [Br j]) Hneq Hex ltac:(reflexivity)).
            eassumption. }

        eapply HasTypeInstruction_Values.

        2:{ eapply Forall3_monotonic; [| eassumption ].
            simpl; intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
            reflexivity. }

        eapply SplitStoreTypings_comm in H5.
        eapply SplitStoreTypings_Empty_eq in H5; [| eassumption ].

        eapply SplitStoreTyping_eq. eassumption.
        rewrite H0, H1.  eassumption.

        auto.
        
      + apply LCEffEqual_sym.
        eapply LCEffEqual_trans; [ eapply LCEffEqual_trans | ]; eauto.

    - replace (map Val l ++ Label n a l0 (C |[ vs ++ [Br j] ]|) :: l1)
        with ((map Val l ++ [Label n a l0 (C |[ vs ++ [Br j] ]|)]) ++ l1)
        in Htyp.
      2:{ rewrite <- app_assoc. simpl. reflexivity. }

      eapply composition_typing in Htyp. destructAll.
      destruct F; simpl in *. destructAll.

      symmetry in H. eapply app_eq_nil in H. destructAll.

      eapply composition_typing_single_strong in H0. destructAll.
      simpl in *. destructAll.
      symmetry in H. eapply app_eq_nil in H. destructAll.

      rewrite !get_set_hd in *. rewrite !set_set_hd in *.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Label _ _ _ _] _ _ |- _ ] =>
        eapply Label_HasTypeInstruction in H; destructAll
      end.
      simpl in *; destructAll.
      rewrite !get_set_hd in *. rewrite !set_set_hd in *.

      intros.
      repeat do_forall_app. simpl in *. repeat do_bools.
      destructAll.

      eapply Values_HasTypeInstruction with (H := values_Val l) in H0. destructAll.

      edestruct IHC with (j := j).
      2:{ eapply well_formews_Inst_list_is_well_formed_in_context. eassumption. }
      eassumption. eassumption. eassumption.
      simpl. lia.

      simpl.
      replace (j - k) with (Datatypes.S (j - Datatypes.S k)) by lia.
      simpl. eassumption.

      simpl. reflexivity.

      eassumption.
      simpl; auto.
      
      eapply LocalCtxValid_Function_Ctx; eauto.

      simpl in *.
      destructAll.
      match goal with
      | [ H' : values ?VS,
          H'' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        eapply Values_HasTypeInstruction with (H:=H') in H''
      end.
      destructAll.
      simpl in *; subst.

      split; [| split ].

      + intros m Hleq'.
        assert (Hleq'' : Datatypes.S m <= j - k) by lia.
        specialize (H0 (Datatypes.S m) Hleq''). simpl in *. destructAll.
        destruct m; destructAll.
        * eexists (get_hd linear).
          rewrite nth_error_plist_hd_Zero. split; eauto.
          rewrite Hhd. eapply QualLeq_Refl.
        * rewrite nth_error_plist_hd_Succ in H0.
          eexists. split; eauto.

      + eapply HasTypeInstruction_Values.

        2:{ eapply Forall3_monotonic; [| eassumption ].
            simpl; intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ];
            reflexivity. }

        eapply SplitStoreTyping_eq. eassumption.

        match goal with
        | [ H : Forall3 _ ?SS _ ?TS,
            H' : SplitStoreTypings ?SS _,
            H'' : Forall _ ?TS |- _ ] =>
          eapply SplitStoreTypings_Empty' in H'
        end.
        2:{ eapply Forall3_HasTypeValue_Unrestricted_LinEmpty. eassumption.
            simpl.
            prepare_Forall.
            eapply QualLeq_Trans. eassumption.

            specialize (H0 1 ltac:(lia)). simpl in H0. destructAll.
            rewrite nth_error_plist_hd_Zero in H0. inv H0.
            rewrite get_set_hd in *. eassumption. simpl; auto. }
        match goal with
        | [ H : M.is_empty (LinTyp ?S) = true,
            H' : SplitStoreTypings [?S; _] _ |- _ ] =>
          eapply SplitStoreTypings_Empty_eq in H; [| eassumption ];
          rewrite H
        end.

        assert (Hneq : vs ++ [Br j] <> [] ).
        { intro Heq. destruct vs; inv Heq. }

        eapply HasTypeInstruction_surface in H3.
        2:{ assert (Hex : existsb nonval_Inst (vs ++ [Br j]) = true).
            { rewrite existsb_app. do_bools. right; reflexivity. }
            specialize (Hwf (1 + k) (LSucc_label k l (length x0) (Arrow [] x2) l0 C l1) (vs ++ [Br j]) Hneq Hex ltac:(reflexivity)).
            simpl in Hwf. eassumption. }

        eapply SplitStoreTypings_comm in H4.
        eapply SplitStoreTypings_Empty_eq in H4; [| eassumption ].
        eassumption.
        
        auto.
      + eapply LCEffEqual_trans; eauto.
        apply LCEffEqual_sym; auto.
  Qed.

  Lemma Tee_local_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [Tee_local i] (Arrow t1 t2) L' ->
    exists t' pto qo ptn qn sz szn ,
      let t := QualT ptn qn in
      M.is_empty (LinTyp S) = true /\

      t1 = t' ++ [t] /\
      t2 = t' ++ [t] /\

      nth_error L i = Some (QualT pto qo, sz) /\
      QualLeq (qual F) qo Unrestricted = Some true /\
      QualLeq (qual F) qn Unrestricted = Some true /\
      Some szn = sizeOfType (type F) t /\
      SizeLeq (typing.size F) szn sz = Some true /\
      LCEffEqual (size F) (set_localtype i t sz L) L'.
  Proof.
    assert (Heq : [Tee_local i] = [Tee_local i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'. generalize [Tee_local i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp; simpl.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; inv Heq. exists []. do 6 eexists; repeat split; eauto.
      apply set_localtype_LCEffEqual.
      -- apply LCEffEqual_refl.
      -- apply SizeLeq_Refl.
      -- apply SizeLeq_Refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.

      destructAll. eauto.

      use_LCEffEqual_nth_error_right.
      inv Heq1. do 7 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat split; eauto.
      -- eapply SizeLeq_Trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply set_localtype_LCEffEqual; auto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *.
      do 7 eexists. repeat split; try eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
    - start_lceff_subgoals.
      use_LCEffEqual_nth_error_left.
      do 7 eexists; repeat split; eauto.
      -- eapply SizeLeq_Trans; eauto.
      -- eapply LCEffEqual_trans; eauto.
         apply set_localtype_LCEffEqual; auto.
         apply LCEffEqual_sym; auto.
    - start_lceff_subgoals.
      do 7 eexists; repeat split; eauto.
      eapply LCEffEqual_trans; eauto.
  Qed.

  Lemma CoderefI_HasTypeInstruction S M F L t1 t2 L' i :
    HasTypeInstruction S M F L [CoderefI i] (Arrow t1 t2) L' ->
    exists chi,
      M.is_empty (LinTyp S) = true /\
      nth_error (table M) i = Some chi /\
      TypeValid F (QualT (CoderefT chi) Unrestricted) /\
      t2 = t1 ++ [QualT (CoderefT chi) Unrestricted] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [CoderefI i] = [CoderefI i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [CoderefI i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - inv Heq1; inv Heq. eexists. repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.
      destructAll. inv Heq1.
      eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat split; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *.
      eexists. repeat split; try eassumption.
      eapply TypeValid_Function_Ctx; try eassumption; simpl; congruence.
      rewrite app_assoc. reflexivity.

    - solve_lceff_subgoals ltac:(1).
    - solve_lceff_subgoals ltac:(1).
  Qed.

  Lemma CoderefI_HasTypeValue S F t i j zs :
    HasTypeValue S F (Coderef i j zs) t ->
    exists ftinst q C' ft,
      M.is_empty (LinTyp S) = true /\
      t = QualT (CoderefT ftinst) q /\
      nth_error (InstTyp S) i = Some C' /\
      nth_error (table C') j = Some ft /\
      InstInds ft zs = Some ftinst.
  Proof.
    intros Hv. inv Hv; eauto.
    do 4 eexists. repeat split; eassumption.
  Qed.

  Lemma RecFold_HasTypeInstruction S M F L t1 t2 L' rec :
    HasTypeInstruction S M F L [RecFold rec] (Arrow t1 t2) L' ->
    exists t pt qa q,
      M.is_empty (LinTyp S) = true /\

      let tau := QualT pt q in
      rec = Rec qa tau /\
      TypeValid F (QualT rec q) /\
      (* RecQualValidTyp q 0 tau /\ *)
      (* alpha_consistent q a tau = Some true /\ *)
      t1 = t ++ [subst_ext (Kind:=Kind) (ext SPretype rec id) tau] /\
      t2 = t ++ [QualT rec q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [RecFold rec] = [RecFold rec]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [RecFold rec] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists. repeat (split; eauto).
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.
      simpl in *. destructAll. inv Heq1.
      do 4 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat (split; eauto).
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. repeat (split; eauto); try eassumption.
      eapply TypeValid_Function_Ctx; eauto.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma RecUnfold_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [RecUnfold] (Arrow t1 t2) L' ->
    exists t pt qa q,
      M.is_empty (LinTyp S) = true /\
      let tau := QualT pt q in
      let rec := Rec qa tau in
      TypeValid F (QualT rec q) /\
      t2 = t ++ [subst_ext (Kind:=Kind) (ext SPretype rec id) tau] /\
      t1 = t ++ [QualT rec q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [RecUnfold] = [RecUnfold]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [RecUnfold] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 4 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq.

      destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.
      simpl in *. destructAll. inv Heq1.
      do 4 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat split; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. repeat split; try eassumption.
      eapply TypeValid_Function_Ctx; eauto.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma Group_HasTypeInstruction S M F L t1 t2 L' n q:
    HasTypeInstruction S M F L [Group n q] (Arrow t1 t2) L' ->
    exists ts taus,
      M.is_empty (LinTyp S) = true /\

      t1 = ts ++ taus /\
      t2 = ts ++ [QualT (ProdT taus) q] /\
      length taus = n /\
      TypeValid F (QualT (ProdT taus) q) /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Group n q] = [Group n q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Group n q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1.

      edestruct IHHtyp2. reflexivity. reflexivity.
      simpl in *. destructAll.
      do 2 eexists. split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat split; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 2 eexists. split; [| split ; [| split ; [| split; [| split ]]]].
      eassumption. rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      reflexivity. 
      eapply TypeValid_Function_Ctx; eauto.
      auto.
      
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

  Lemma Ungroup_HasTypeInstruction S M F L t1 t2 L':
    HasTypeInstruction S M F L [Ungroup] (Arrow t1 t2) L' ->
    exists ts taus q,
      M.is_empty (LinTyp S) = true /\

      t2 = ts ++ taus /\
      t1 = ts ++ [QualT (ProdT taus) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Ungroup] = [Ungroup]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Ungroup] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 2 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1. edestruct IHHtyp2. reflexivity. reflexivity.
      destructAll. do 3 eexists.
      destructAll. eauto.
      split.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.

      repeat split; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split ]].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma InstIndValid_Function_Ctx F qs ft i:
    InstIndValid F ft i ->
    InstIndValid (update_linear_ctx qs F) ft i.
  Proof.
    intros.
    destruct ft.
    destruct F; subst; simpl in *.
    eapply InstIndValid_Function_Ctx_stronger; [ | | | | eauto ]; eauto.
  Qed.

  Lemma InstIndsValid_Function_Ctx F qs ft i:
    InstIndsValid F ft i ->
    InstIndsValid (update_linear_ctx qs F) ft i.
  Proof.
    intros.
    destruct ft.
    destruct F; subst; simpl in *.
    eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ]; eauto.
  Qed.

  Lemma InstIndsValid_Function_Ctx_rev F qs ft i:
    InstIndsValid (update_linear_ctx qs F) ft i ->
    InstIndsValid F ft i.
  Proof.
    assert (F = (update_linear_ctx (linear F) (update_linear_ctx qs F))).
    { destruct F; simpl; congruence. }
    rewrite H at 2.
    intros.
    eapply InstIndsValid_Function_Ctx.
    eassumption.
  Qed.

  Lemma Inst_HasTypeInstruction S M F L t1 t2 L' ins:
    HasTypeInstruction S M F L [Inst ins] (Arrow t1 t2) L' ->
    exists ts chi chi' q,
      M.is_empty (LinTyp S) = true /\

      t1 = ts ++ [QualT (CoderefT chi) q] /\
      t2 = ts ++ [QualT (CoderefT chi') q] /\
      (* Zoe: this needs to be added but definition must be fixed first *)
      (* InstIndsValid F chi is *)
      InstInds chi ins = Some chi' /\ InstIndsValid F chi ins /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Inst ins] = [Inst ins]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Inst ins] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. inv Heq1. destructAll.

      eapply Empty_HasTypeInstruction in Htyp1. destructAll.

      edestruct IHHtyp2. reflexivity. reflexivity.

      destructAll. do 4 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. split; [| split; [| split; [| split; [| split ] ] ] ].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity. eassumption.
      unfold F' in *.
      repeat match goal with
             | [ X : FunType |- _ ] => destruct X
             end.
      eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ]; auto.
      auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma CapSplit_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [CapSplit] (Arrow t1 t2) L' ->
    exists ts l ht,
      M.is_empty (LinTyp S) = true /\

      t1 = ts ++ [QualT (CapT W l ht) Linear] /\
      t2 = ts ++ [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [CapSplit] = [CapSplit]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [CapSplit] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split ] ].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma CapJoin_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [CapJoin] (Arrow t1 t2) L' ->
    exists ts l ht,
      M.is_empty (LinTyp S) = true /\

      t2 = ts ++ [QualT (CapT W l ht) Linear] /\
      t1 = ts ++ [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [CapJoin] = [CapJoin]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [CapJoin] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.


    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split ] ].

      eassumption.

      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma RefDemote_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [RefDemote] (Arrow t1 t2) L' ->
    exists ts l ht,
      M.is_empty (LinTyp S) = true /\

      t1 = ts ++ [QualT (RefT W l ht) Unrestricted] /\
      t2 = ts ++ [QualT (RefT R l ht) Unrestricted] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [RefDemote] = [RefDemote]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [RefDemote] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split ] ].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma RefSplit_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [RefSplit] (Arrow t1 t2) L' ->
    exists ts cap l ht q,
      M.is_empty (LinTyp S) = true /\
      QualLeq (typing.qual F) Linear q = Some true /\
      t1 = ts ++ [QualT (RefT cap l ht) q] /\
      t2 = ts ++ [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [RefSplit] = [RefSplit]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [RefSplit] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 4 eexists; repeat split; eauto.
      apply LCEffEqual_refl.

    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. destructAll. do 5 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 5 eexists. split; [| split; [| split; [| split ] ] ].
      eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(5).
    - solve_lceff_subgoals ltac:(5).
  Qed.

  Lemma RefJoin_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [RefJoin] (Arrow t1 t2) L' ->
    exists ts cap l ht q,
      M.is_empty (LinTyp S) = true /\

      t2 = ts ++ [QualT (RefT cap l ht) q] /\
      t1 = ts ++ [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [RefJoin] = [RefJoin]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [RefJoin] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 4 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.


      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. destructAll. do 5 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 5 eexists. split; [| split; [| split ] ].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.

    - solve_lceff_subgoals ltac:(5).
    - solve_lceff_subgoals ltac:(5).
  Qed.

  Definition shift_down_after v kspec kspec' :=
    if v <? kspec
    then (kspec' + v)
    else (kspec' + v - 1).

  Definition shift_up_after v kspec kspec' :=
    if v <? kspec
    then (kspec' + v)
    else (kspec' + v + 1).

  Definition debruijn_subst_ext_conds f ks kndspec obj :=
    (forall ks',
        f kndspec (ks kndspec) ks' =
        subst.subst'_rwasm
          kndspec
          (debruijn.weaks' (debruijn.plus ks ks'))
          obj) /\
    (forall v' ks',
        v' <> ks kndspec ->
        f kndspec v' ks' =
        subst.VarKind
          kndspec
          (shift_down_after v' (ks kndspec) (ks' kndspec))) /\
    (forall knd v' ks',
        knd <> kndspec ->
        f knd v' ks' =
        subst.VarKind knd (ks' knd + v')).

  Definition debruijn_weaks_conds f ks ks'' :=
    (forall knd v' ks',
        v' < ks knd ->
        f knd v' ks' =
        subst.VarKind knd (ks' knd + v')) /\
    (forall knd v' ks',
        v' >= ks knd ->
        f knd v' ks' =
        subst.VarKind knd (ks'' knd + ks' knd + v')).

  Lemma single_weak_debruijn_weak_conds : forall {knd},
      debruijn_weaks_conds (subst'_of (weak knd))
                           debruijn.zero
                           (debruijn.sing knd 1).
  Proof.
    intros.
    constructor; intros.
    - unfold debruijn.zero in *.
      match goal with
      | [ H : _ < 0 |- _ ] => inversion H
      end.
    - simpl.
      unfold subst'_rwasm.
      destruct knd0.
      all: simpl.
      all: unfold get_var'.
      all: unfold weaks'.
      all: unfold var.
      all: simpl.
      all: unfold zero.
      all: rewrite Nat.add_0_r.
      all: rewrite Nat.add_comm.
      all: repeat rewrite <-Nat.add_assoc.
      all:
        match goal with
        | [ |- _ (_ + ?A) = _ (_ + ?B) ] =>
          replace A with B; auto
        end.
      all: apply Nat.add_comm.
  Qed.
  
  Lemma minus_less : forall a b c,
      a < b + c ->
      b <= a ->
      a - b < c.
  Proof.
    intros; lia.
  Qed.

  Lemma minus_geq : forall a b c,
      a >= b + c ->
      b <= a ->
      a - b >= c.
  Proof.
    intros; lia.
  Qed.

  Ltac solve_ineqs :=
    try match goal with
        | [ |- _ <> _ ] =>
          let H' := fresh "H" in
          intro H'; inversion H'
        end.

  Ltac solve_impossibles :=
    try match goal with
        | [ H : ?A <> ?A |- _ ] =>
          exfalso; apply H; auto
        end.

  Lemma weak_no_effect_on_other_vars : forall {f ks knd knd' ks' v},
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      knd <> knd' ->
      f knd' v ks' =
      subst.VarKind knd' (ks' knd' + v).
  Proof.
    unfold debruijn_weaks_conds.
    intros f ks knd knd' ks' v H.
    destruct H as [H0 H1].
    intros.
    assert (H' : v < ks knd' \/ ks knd' <= v) by apply Nat.lt_ge_cases.
    case H'; intro H''.
    - rewrite H0; auto.
    - rewrite H1; auto.
      destruct knd; destruct knd'; solve_impossibles;
        simpl; auto.
  Qed.

  Lemma weak_non_qual_no_effect_on_qual : forall {f ks knd q},
      knd <> subst.SQual ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      subst.subst'_qual f q = q.
  Proof.
    destruct q; simpl; auto.
    unfold debruijn.get_var'.
    intros.
    erewrite weak_no_effect_on_other_vars; eauto.
  Qed.

  Lemma weak_non_qual_no_effect_on_quals : forall {f ks knd qs},
      knd <> subst.SQual ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      subst.subst'_quals f qs = qs.
  Proof.
    induction qs; simpl in *; auto.
    intros.
    erewrite weak_non_qual_no_effect_on_qual; eauto.
    erewrite IHqs; eauto.
  Qed.

  Lemma weak_non_size_no_effect_on_size : forall {f ks knd sz},
      knd <> subst.SSize ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      subst.subst'_size f sz = sz.
  Proof.
    induction sz; simpl; eauto.
    - unfold debruijn.get_var'.
      intros.
      erewrite weak_no_effect_on_other_vars; eauto.
    - intros.
      erewrite IHsz1; eauto.
      erewrite IHsz2; eauto.
  Qed.

  Lemma weak_non_size_no_effect_on_sizes : forall {f ks knd szs},
      knd <> subst.SSize ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      subst.subst'_sizes f szs = szs.
  Proof.
    induction szs; simpl in *; auto.
    intros.
    erewrite weak_non_size_no_effect_on_size; eauto.
    erewrite IHszs; eauto.
  Qed.

  Lemma sizepairs_debruijn_weak : forall {f ks knd} C,
      knd <> subst.SSize ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      map
        (fun '(ss1, ss2) =>
           (subst'_sizes f ss1, subst'_sizes f ss2))
        C
      =
      C.
  Proof.
    intros.
    rewrite <-map_id.
    apply map_ext.
    intros.
    destruct_prs.
    erewrite weak_non_size_no_effect_on_sizes; eauto.
    erewrite weak_non_size_no_effect_on_sizes; eauto.
  Qed. 

  Lemma sizepairs_debruijn_weak_loc : forall C,
      map
        (fun '(ss1, ss2) =>
           (subst'_sizes (subst'_of (weak SLoc)) ss1,
            subst'_sizes (subst'_of (weak SLoc)) ss2))
        C
      =
      C.
  Proof.
    intros.
    erewrite sizepairs_debruijn_weak; eauto.
    2:{
      eapply single_weak_debruijn_weak_conds.
    }
    solve_ineqs.
  Qed.

  Lemma nth_error_map_inv : forall {A B} {f : A -> B} {l : list A} {idx el},
      nth_error (map f l) idx = Some el ->
      exists el',
        nth_error l idx = Some el' /\ el = f el'.
  Proof.
    intros. generalize dependent idx.
    induction l; intros; destruct idx; inversion H; subst; simpl; eauto.
  Qed.

  Lemma LCEffEqual_subst_non_size_knd : forall {C L1 L2 f ks knd},
      knd <> subst.SSize ->
      debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
      LCEffEqual C L1 L2 ->
      LCEffEqual
        C
        (subst'_local_ctx f L1)
        (subst'_local_ctx f L2).
  Proof.
    unfold LCEffEqual.
    intros.
    apply forall2_nth_error_inv.
    2:{
      unfold subst'_local_ctx.
      repeat rewrite map_length.
      eapply Forall2_length; eauto.
    }
    unfold subst'_local_ctx.
    intros.
    repeat match goal with
           | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
             apply nth_error_map_inv in H; destructAll
           end.
    destruct_prs.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.
    intros; simpl in *; destructAll.
    split; auto.
    erewrite weak_non_size_no_effect_on_size; eauto.
    erewrite weak_non_size_no_effect_on_size; eauto.
  Qed.

  Lemma LCEffEqual_subst_weak_loc : forall {C L1 L2},
      LCEffEqual C L1 L2 ->
      LCEffEqual
        C
        (subst'_local_ctx (subst'_of (weak SLoc)) L1)
        (subst'_local_ctx (subst'_of (weak SLoc)) L2).
  Proof.
    intros.
    eapply LCEffEqual_subst_non_size_knd; eauto.
    2:{
      eapply single_weak_debruijn_weak_conds.
    }
    solve_ineqs.
  Qed.

  Lemma MemUnpack_HasTypeInstruction S M F L tf tl  es t1 t2 L' :
    HasTypeInstruction S M F L [MemUnpack tf tl es] (Arrow t1 t2) L' ->
    exists ts tau1 tau2 taurho qrho qf L'',
      t1 = ts ++ tau1 ++ [QualT (ExLoc taurho) qrho] /\
      t2 = ts ++ tau2 /\
      tf = Arrow tau1 tau2 /\

      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\

      let F := update_linear_ctx (set_hd qf (linear F)) F in
      let F1 := update_label_ctx ((tau2, L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      let F3 := subst_ext (weak SLoc) (update_location_ctx (location F + 1) F2) in

      HasTypeInstruction
        S M F3
        (subst_ext (weak SLoc) L)
        es
        (Arrow
           (subst_ext (weak SLoc) tau1 ++ [taurho])
           (subst_ext (weak SLoc) tau2))
        (subst_ext (weak SLoc) L') /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    assert (Heq : [MemUnpack tf tl es] = [MemUnpack tf tl es]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [MemUnpack tf tl es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 6 eexists; repeat split.
      now constructor.
      eapply QualLeq_Refl. simpl in *.
      rewrite !set_get_hd. destruct F; simpl in *; try eassumption.
      all: try apply LCEffEqual_refl.
      destruct F; subst; simpl in *; auto.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. eauto.
      simpl. setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 eq_refl _ _ Heq1).
      simpl in *; destructAll.
      do 7 eexists; repeat split; eauto.
      -- eapply ChangeBegLocalTyp; eauto.
         apply LCEffEqual_sym.
         destruct F; subst; simpl in *.
         rewrite sizepairs_debruijn_weak_loc; auto.
         apply LCEffEqual_subst_weak_loc; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         destruct F; subst; simpl in *; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 7 eexists.
      split; [| split; [| split; [| split ; [| split; [| split ] ] ] ]].
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      reflexivity.

      eapply Forall_app. split; [ | eassumption ].

      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      rewrite set_set_hd in *.

      eassumption.

      split; auto.
      
    - start_lceff_subgoals.
      do 7 eexists; repeat split; eauto.
      -- eapply ChangeBegLocalTyp; eauto.
         destruct F; subst; simpl in *.
         rewrite sizepairs_debruijn_weak_loc; auto.
         apply LCEffEqual_subst_weak_loc; auto.
      -- eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_add_local_effects.
         destruct F; subst; simpl in *.
         apply LCEffEqual_sym; auto.
    - start_lceff_subgoals.
      do 7 eexists; repeat split; eauto.
      -- eapply ChangeEndLocalTyp; eauto.
         destruct F; subst; simpl in *.
         rewrite sizepairs_debruijn_weak_loc; auto.
         apply LCEffEqual_subst_weak_loc; auto.
      -- eapply LCEffEqual_trans; eauto.
         destruct F; subst; simpl in *; auto.
      -- destruct F; subst; simpl in *.
         eapply LCEffEqual_trans; eauto.
         apply LCEffEqual_sym; auto.
  Qed.

  Lemma StructMalloc_HasTypeInstruction S M F L szs q t1 t2 L' :
    HasTypeInstruction S M F L [StructMalloc szs q] (Arrow t1 t2) L' ->
    exists ts taus,
      M.is_empty (LinTyp S) = true /\
      QualValid (qual F) q /\
      Forall2
        (fun (tau : Typ) (sz : Size) =>
           exists tausz : Size,
             sizeOfType (type F) tau = Some tausz /\
             SizeLeq (typing.size F) tausz sz = Some true) taus szs /\
        Forall (fun sz => SizeValid (size F) sz) szs /\
        forallb (NoCapsTyp (heapable F)) taus = true /\
      let psi := StructType (combine (subst_ext (Kind:=Kind) (weak SLoc) taus) szs) in
      t1 = ts ++ taus /\
      t2 = ts ++ [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [StructMalloc szs q] = [StructMalloc szs q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [StructMalloc szs q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 2 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.


      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 2 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 2 eexists. split; [| split; [| split; [| split; [| split; [| split ]]]]].
      eassumption.
      eassumption.
      eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. split; auto.
    - solve_lceff_subgoals ltac:(2).
    - solve_lceff_subgoals ltac:(2).
  Qed.

  Lemma VariantMalloc_HasTypeInstruction S M F L n taus q t1 t2 L' :
    HasTypeInstruction S M F L [VariantMalloc n taus q] (Arrow t1 t2) L' ->
    exists ts p qp,
      M.is_empty (LinTyp S) = true /\
      Forall (TypeValid F) taus /\
      QualValid (qual F) q /\
      let tau := QualT p qp in
      nth_error taus n = Some tau /\
      QualLeq (qual F) qp q = Some true /\
      forallb (NoCapsTyp (heapable F)) taus = true /\
      let psi := VariantType (subst_ext (Kind:=Kind) (weak SLoc) taus) in
      t1 = ts ++ [tau] /\
      t2 = ts ++ [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [VariantMalloc n taus q] = [VariantMalloc n taus q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [VariantMalloc n taus q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.


      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split ]]]]]]].
      eassumption.

      { prepare_Forall; try eapply TypeValid_Function_Ctx; eauto. }

      eassumption. eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma ArrayMalloc_HasTypeInstruction S M F L q t1 t2 L' :
    HasTypeInstruction S M F L [ArrayMalloc q] (Arrow t1 t2) L' ->
    exists ts p qp qi,
      M.is_empty (LinTyp S) = true /\
      QualValid (qual F) q /\
      let tau := QualT p qp in
      let psi := ArrayType (subst_ext (Kind:=Kind) (weak SLoc) tau) in
      QualLeq (qual F) qp Unrestricted = Some true /\
      t1 = ts ++ [tau; QualT uint32T qi] /\
      t2 = ts ++ [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q] /\
      NoCapsTyp (heapable F) tau = true /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [ArrayMalloc q] = [ArrayMalloc q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ArrayMalloc q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 4 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. split; [| split; [| split; [| split; [| split; [| split ]]]]].
      eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity. eassumption.
      auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma ArraySet_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [ArraySet] (Arrow t1 t2) L' ->
    exists ts p l qi q,
      M.is_empty (LinTyp S) = true /\
      let tau := QualT p Unrestricted in
      NoCapsTyp (heapable F) tau = true /\
      t1 = ts ++ [QualT (RefT W l (ArrayType tau)) q; QualT uint32T qi; tau] /\
      t2 = ts ++ [QualT (RefT W l (ArrayType tau)) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [ArraySet] = [ArraySet]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ArraySet] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 4 eexists. repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 5 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 5 eexists. split; [| split; [| split; [| split ]]].
      eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(5).
    - solve_lceff_subgoals ltac:(5).
  Qed.

  Lemma ArrayGet_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [ArrayGet] (Arrow t1 t2) L' ->
    exists alpha cap l p q qi,
      M.is_empty (LinTyp S) = true /\
      t1 = alpha ++ [QualT (RefT cap l (ArrayType (QualT p Unrestricted))) q; QualT uint32T qi] /\
      t2 = alpha ++ [QualT (RefT cap l (ArrayType (QualT p Unrestricted))) q; QualT p Unrestricted] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [ArrayGet] = [ArrayGet]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ArrayGet] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 5 eexists. repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 6 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 6 eexists. split; [| split; [| split ]].
      eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(6).
    - solve_lceff_subgoals ltac:(6).
  Qed.

  Lemma ArrayFree_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [ArrayFree] (Arrow t1 t2) L' ->
    exists l p q,
      M.is_empty (LinTyp S) = true /\
      QualValid (qual F) q /\
      QualLeq (qual F) Linear q = Some true /\
      t1 = t2 ++ [QualT (RefT W l (ArrayType (QualT p Unrestricted))) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [ArrayFree] = [ArrayFree]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ArrayFree] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      do 3 eexists. repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split; [| split ]]].
      eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma ExistsPack_HasTypeInstruction S M F L p psi q t1 t2 L' :
    HasTypeInstruction S M F L [ExistPack p psi q] (Arrow t1 t2) L' ->
    exists ts szp sz qα hp hq,
      M.is_empty (LinTyp S) = true /\
      QualLeq (qual F) hq q = Some true /\
      QualValid (qual F) q /\
      sizeOfPretype (type F) p = Some szp /\
      SizeLeq (typing.size F) szp sz = Some true /\
      SizeValid (typing.size F) szp /\
      SizeValid (typing.size F) sz /\
      TypeValid F (QualT p q) /\
      TypeValid (subst_ext (weak SPretype) (update_type_ctx ((sz, q, Heapable) :: type F) F)) (QualT hp hq) /\
      NoCapsPretype (heapable F) p = true /\
      NoCapsTyp (heapable (update_type_ctx ((sz, q, Heapable) :: type F) F)) (QualT hp hq) = true /\
      let tau := subst_ext (Kind:=Kind) (ext SPretype p id) (QualT hp hq) in
      psi = Ex sz qα (subst_ext (Kind:= Kind) (weak SLoc) (QualT hp hq)) /\
      q = qα /\
      t1 = ts ++ [tau] /\
      t2 = ts ++ [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q]  /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [ExistPack p psi q] = [ExistPack p psi q]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ExistPack p psi q] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 5 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 6 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 6 eexists.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split ] ] ] ] ] ] ] ] ] ] ] ].
      eassumption. eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
      unfold F' in *.
      now eapply TypeValid_Function_Ctx; try eassumption; try reflexivity.
      now eapply TypeValid_Function_Ctx; try eassumption; try reflexivity.
      eassumption.
      eassumption.
      reflexivity. reflexivity.
      split.
      rewrite app_assoc. reflexivity.
      split.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(6).
    - solve_lceff_subgoals ltac:(6).
  Qed.

  Lemma sizepairs_debruijn_weak_pretype : forall C,
      map
        (fun '(ss1, ss2) =>
           (subst'_sizes (subst'_of (weak SPretype)) ss1,
            subst'_sizes (subst'_of (weak SPretype)) ss2))
        C
      =
      C.
  Proof.
    intros.
    erewrite sizepairs_debruijn_weak; eauto.
    2:{
      eapply single_weak_debruijn_weak_conds.
    }
    solve_ineqs.
  Qed.

  Theorem subst_size_weak_id s:
    subst'_size (subst'_of (weak SPretype)) s = s.
  Proof.
    induction s; simpl; auto.
    f_equal; eauto.
  Qed.

  Lemma LCEffEqual_subst_weak_pretype : forall {C L1 L2},
      LCEffEqual C L1 L2 ->
      LCEffEqual
        C
        (subst'_local_ctx (subst'_of (weak SPretype)) L1)
        (subst'_local_ctx (subst'_of (weak SPretype)) L2).
  Proof.
    intros.
    eapply LCEffEqual_subst_non_size_knd; eauto.
    2:{
      eapply single_weak_debruijn_weak_conds.
    }
    solve_ineqs.
  Qed.

  Lemma MemPack_HasTypeInstruction S M F L l t1 t2 L' :
    HasTypeInstruction S M F L [MemPack l] (Arrow t1 t2) L' ->
    exists ts pt q taurho,
      M.is_empty (LinTyp S) = true /\
      let tau := QualT pt q in
      subst_ext (ext SLoc l id) taurho = tau /\
      t1 = ts ++ [tau] /\
      t2 = ts ++ [QualT (ExLoc taurho) q] /\
      TypeValid F tau /\
      LocValid (location F) l /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [MemPack l] = [MemPack l]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [MemPack l] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 4 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 4 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. split; [| split; [| split; [| split; [| split ]]]].
      eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      eapply TypeValid_Function_Ctx; eauto.
      split; auto.
      
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma Qualify_HasTypeInstruction S M F L qnew t1 t2 L' :
    HasTypeInstruction S M F L [Qualify qnew] (Arrow t1 t2) L' ->
    exists ts p qold,
      M.is_empty (LinTyp S) = true /\
      (forall cap l ht, p <> CapT cap l ht) /\
      (forall cap l ht, p <> RefT cap l ht) /\
      QualLeq (qual F) qold qnew = Some true /\
      t1 = ts ++ [QualT p qold] /\
      t2 = ts ++ [QualT p qnew] /\
      QualValid (qual F) qnew /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [Qualify qnew] = [Qualify qnew]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [Qualify qnew] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - simpl in *. inv Heq. inv Heq1.
      exists []. do 2 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.

      edestruct IHHtyp2. reflexivity. reflexivity.

      inv Heq1. simpl in *. destructAll. do 3 eexists.

      repeat split; eauto.

      eapply SplitStoreTypings_Empty'. eassumption. now constructor; eauto.
      eapply LCEffEqual_trans; eauto.

    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 3 eexists. split; [| split; [| split; [| split; [| split; [| split; [| split ] ] ] ] ] ].
      eassumption. eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto. eassumption.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma CallAdm_HasTypeInstruction S M F L cl i t1 t2 L' :
    HasTypeInstruction S M F L [CallAdm cl i] (Arrow t1 t2) L' ->
    exists ts t1' t2' chi,
      HasTypeClosure S cl chi /\
      InstInds chi i = Some (FunT [] (Arrow t1' t2')) /\
      InstIndsValid F chi i /\
      t1 = ts ++ t1' /\
      t2 = ts ++ t2' /\ LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [CallAdm cl i] = [CallAdm cl i]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [CallAdm cl i] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - subst. inv Heq.
      exists []. do 3 eexists; repeat split; eauto.
      -- invert_arrow_eq; auto.
      -- apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      destructAll. eauto.
      setoid_rewrite <- SplitStoreTypings_Empty_eq; eauto.
      specialize (IHHtyp2 eq_refl _ _ Heq1).
      destructAll.
      do 4 eexists; repeat split; eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      destruct F; simpl in *. destructAll.
      do 4 eexists. split; [| split; [| split; [| split; [| split]]]].
      eassumption. eassumption.
      eapply InstIndsValid_Function_Ctx_rev. eassumption.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
      auto.
    - solve_lceff_subgoals ltac:(4).
    - solve_lceff_subgoals ltac:(4).
  Qed.

  Lemma StructFree_HasTypeInstruction S M F L t1 t2 L' :
    HasTypeInstruction S M F L [StructFree] (Arrow t1 t2) L' ->
    exists l tauszs q,
      M.is_empty (LinTyp S) = true /\
      QualValid (qual F) q /\
      QualLeq (qual F) Linear q = Some true /\
      Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) tauszs /\
      t1 = t2 ++ [QualT (RefT W l (StructType tauszs)) q] /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [StructFree] = [StructFree]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [StructFree] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - subst. inv Heq. inv Heq1.
      do 3 eexists; repeat split; eauto.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1. destructAll. assert (IH := IHHtyp2 (eq_refl _) _ _ (eq_refl _)). destructAll.
      do 3 eexists; repeat split; eauto.
      eapply SplitStoreTypings_Empty_eq in H; eauto.
      inv H.
      destruct H9.
      eapply is_empty_eq_map in H.
      eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      do 3 eexists. split; [| split; [| split; [| split; [| split]]]]; destruct F; simpl in *.
      eassumption. eassumption. eassumption. eassumption.
      rewrite app_assoc. reflexivity. auto.
    - solve_lceff_subgoals ltac:(3).
    - solve_lceff_subgoals ltac:(3).
  Qed.

  Lemma StructGet_HasTypeInstruction S M F L t1 t2 L' n :
    HasTypeInstruction S M F L [StructGet n] (Arrow t1 t2) L' ->
    exists alpha cap l q taus szs pv qv,
      t1 = alpha ++ [QualT (RefT cap l (StructType (combine taus szs))) q] /\
      t2 = alpha ++ [QualT (RefT cap l (StructType (combine taus szs))) q; QualT pv qv] /\
      M.is_empty (LinTyp S) = true /\
      length taus = length szs /\
      nth_error taus n = Some (QualT pv qv) /\
      QualLeq (qual F) qv Unrestricted = Some true /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [StructGet n] = [StructGet n]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [StructGet n] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - subst. inv Heq. inv Heq1.
      do 8 eexists; repeat split; eauto; unfold psi. rewrite app_nil_l. reflexivity. reflexivity.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1. destructAll. assert (IH := IHHtyp2 (eq_refl _) _ _ (eq_refl _)). destructAll.
      do 8 eexists; repeat split; eauto.
      eapply SplitStoreTypings_Empty_eq in H; eauto.
      inv H.
      destruct H4.
      eapply is_empty_eq_map in H.
      eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      exists (taus ++ x); do 7 eexists. split; [| split; [| split; [| split; [| split]]]]; eauto.
      rewrite app_assoc; reflexivity.
      rewrite app_assoc; reflexivity.
      split; eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; auto.
    - solve_lceff_subgoals ltac:(8).
    - solve_lceff_subgoals ltac:(8).
  Qed.

  Lemma StructSet_HasTypeInstruction S M F L t1 t2 L' n :
    HasTypeInstruction S M F L [StructSet n] (Arrow t1 t2) L' ->
    exists alpha cap l q taus taus' tau p_old q_old szs sz tau_sz,
      t1 = alpha ++ [QualT (RefT cap l (StructType (combine taus szs))) q; tau] /\
      t2 = alpha ++ [QualT (RefT cap l (StructType (combine taus' szs))) q] /\
      M.is_empty (LinTyp S) = true /\
      length taus = length szs /\
      ReplaceAtIdx n taus tau = Some (taus', QualT p_old q_old) /\
      QualLeq (qual F) q_old Unrestricted = Some true /\
      nth_error szs n = Some sz /\
      sizeOfType (type F) tau = Some tau_sz /\
      SizeLeq (size F) tau_sz sz = Some true /\
      TypeValid F tau /\
      NoCapsTyp (heapable F) tau = true /\
      (QualLeq (qual F) Linear q = Some true \/ tau = QualT p_old q_old) /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [StructSet n] = [StructSet n]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [StructSet n] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - subst. inv Heq. inv Heq1.
      do 12 eexists; repeat split; eauto. rewrite app_nil_l. reflexivity. reflexivity.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1. destructAll. assert (IH := IHHtyp2 (eq_refl _) _ _ (eq_refl _)). destructAll.
      do 12 eexists. repeat split; eauto.
      eapply SplitStoreTypings_Empty_eq in H; eauto.
      inv H.
      destruct H4.
      eapply is_empty_eq_map in H.
      eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      exists (taus ++ x); do 11 eexists. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]; eauto.
      rewrite app_assoc; reflexivity.
      rewrite app_assoc; reflexivity.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *.
      replace_typevalid_parts label ret size type location.
      apply TypeValid_linear.
      eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; eauto.
    - solve_lceff_subgoals ltac:(12).
    - solve_lceff_subgoals ltac:(12).
  Qed.

  Lemma StructSwap_HasTypeInstruction S M F L t1 t2 L' n :
    HasTypeInstruction S M F L [StructSwap n] (Arrow t1 t2) L' ->
    exists alpha l q taus taus' tau tau_old szs sz tau_sz,
      t1 = alpha ++ [QualT (RefT W l (StructType (combine taus szs))) q; tau] /\
      t2 = alpha ++ [QualT (RefT W l (StructType (combine taus' szs))) q; tau_old] /\
      M.is_empty (LinTyp S) = true /\
      length taus = length szs /\
      ReplaceAtIdx n taus tau = Some (taus', tau_old) /\
      nth_error szs n = Some sz /\
      sizeOfType (type F) tau = Some tau_sz /\
      SizeLeq (size F) tau_sz sz = Some true /\
      TypeValid F tau /\
      NoCapsTyp (heapable F) tau = true /\
      (QualLeq (qual F) Linear q = Some true \/ tau = tau_old) /\
      LCEffEqual (size F) L L'.
  Proof.
    assert (Heq : [StructSwap n] = [StructSwap n]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [StructSwap n] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - subst. inv Heq. inv Heq1.
      do 11 eexists; repeat split; eauto. rewrite app_nil_l. reflexivity. reflexivity.
      apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      inv Heq1. destructAll. assert (IH := IHHtyp2 (eq_refl _) _ _ (eq_refl _)). destructAll.
      do 10 eexists. repeat split; eauto.
      eapply SplitStoreTypings_Empty_eq in H; eauto.
      inv H.
      destruct H4.
      eapply is_empty_eq_map in H.
      eauto.
      eapply LCEffEqual_trans; eauto.
    - subst. inv Heq1. edestruct IHHtyp; eauto. destructAll.
      exists (taus ++ x); do 9 eexists. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]; eauto.
      rewrite app_assoc; reflexivity.
      rewrite app_assoc; reflexivity.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *.
      replace_typevalid_parts label ret size type location.
      apply TypeValid_linear.
      eauto.
      destruct F; simpl in *; eauto.
      destruct F; simpl in *; eauto.
      destruct F; subst; simpl in *; auto.
    - solve_lceff_subgoals ltac:(10).
    - solve_lceff_subgoals ltac:(10).
  Qed.

  Lemma VariantCase_HasTypeInstruction S M F L q ht tf tl es t1 t2 L' :
    HasTypeInstruction S M F L [VariantCase q ht tf tl es] (Arrow t1 t2) L' ->
    (exists t taus1 taus2 qv l tausv qf L'',
        Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
        QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
        let F  := update_linear_ctx (set_hd qf (linear F)) F in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        ht = (VariantType tausv) /\
        M.is_empty (LinTyp S) = true /\
        tf = Arrow taus1 taus2 /\
        Forall2 (fun es0 tau => HasTypeInstruction S M F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv /\
        QualLeq (qual F) Linear q = Some true /\
        QualLeq (qual F) Linear qv = Some true /\
        QualValid (qual F) q /\
        QualValid (qual F) qv /\
        t1 = t ++ taus1 ++ [QualT (RefT W l (VariantType tausv)) qv] /\
        t2 = t ++ taus2 /\
        LCEffEqual (size F) (add_local_effects L tl) L' /\
        LCEffEqual (size F) L' L'')
      \/
      (exists t taus1 taus2 q' qv cap l tausv qf L'',
        Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
        QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
        let F  := update_linear_ctx (set_hd qf (linear F)) F in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        ht = (VariantType tausv) /\
        M.is_empty (LinTyp S) = true /\
        QualLeq (qual F) qv q' = Some true /\
        QualLeq (qual F) (get_hd (linear F)) q' = Some true /\
        tf = Arrow taus1 taus2 /\
        Forall2 (fun es0 tau => HasTypeInstruction S M F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv /\
        Forall (fun '(QualT _ q0) => QualLeq (qual F) q0 Unrestricted = Some true) tausv /\
        QualLeq (qual F) q Unrestricted = Some true /\
        QualValid (qual F) q /\
        QualValid (qual F) qv /\
        t1 = t ++ taus1 ++ [QualT (RefT cap l (VariantType tausv)) qv] /\
        t2 = t ++ [QualT (RefT cap l (VariantType tausv)) qv] ++ taus2 /\
        LCEffEqual (size F) (add_local_effects L tl) L' /\
        LCEffEqual (size F) L' L'')
    .
    Proof.
    assert (Heq : [VariantCase q ht tf tl es] = [VariantCase q ht tf tl es]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [VariantCase q ht tf tl es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'. induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - right. simpl in *. inv Heq. inv Heq1.
      match goal with
      | [ H : QualLeq (qual _) ?Q2 ?Q1 = Some true,
          H' : QualLeq (qual _) (get_hd (linear ?F)) ?Q1 = Some true |- _ ] =>
        destruct F; simpl in *; eauto;
        exists []; do 2 eexists;
        exists Q1; exists Q2; do 3 eexists
      end.
      do 2 eexists.
      repeat split; try rewrite set_get_hd; try rewrite get_set_hd; try rewrite set_set_hd; eauto.
      -- apply QualLeq_Refl.
      -- apply LCEffEqual_refl.
    - left. simpl in *. inv Heq. inv Heq1.
      exists []. do 5 eexists. exists (get_hd (linear F)). eexists. repeat split; try rewrite set_get_hd; destruct F; simpl in *; eauto.
      -- apply QualLeq_Refl.
      -- apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.
      edestruct IHHtyp2; try reflexivity.
      + left. inv Heq1. simpl in *. destructAll. do 8 eexists.
        repeat split; eauto.
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        inv H.
        destruct H6.
        eapply is_empty_eq_map in H.
        eauto.
        eapply Forall2_monotonic; eauto; intros.
        simpl in *.
        eapply Proper_HasTypeInstruction; eauto.
        2:{
          eapply ChangeBegLocalTyp; eauto.
          destruct F; subst; simpl in *.
          apply LCEffEqual_sym; auto.
        }
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        eapply StoreTyping_Equiv; auto.
        eapply LCEffEqual_trans; eauto.
        apply LCEffEqual_add_local_effects.
        destruct F; subst; simpl in *; auto.
      + right. inv Heq1. simpl in *. destructAll. do 10 eexists.
        repeat split; eauto.
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        inv H.
        destruct H6.
        eapply is_empty_eq_map in H.
        eauto.
        eapply Forall2_monotonic; eauto; intros.
        simpl in *.
        eapply Proper_HasTypeInstruction; eauto.
        2:{
          eapply ChangeBegLocalTyp; eauto.
          destruct F; subst; simpl in *.
          apply LCEffEqual_sym; auto.
        }
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        eapply StoreTyping_Equiv; eauto.
        eapply LCEffEqual_trans; eauto.
        apply LCEffEqual_add_local_effects.
        destruct F; subst; simpl in *; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto; destructAll; simpl in *; destructAll.
      + left. unfold F' in *. destruct F; subst; simpl in *. exists (taus ++ x); do 7 eexists. repeat split.
        4:{
          rewrite set_set_hd in *; eauto.
        }
        all: eauto.
        -- rewrite Forall_app; split; auto.
           prepare_Forall.
           eapply QualLeq_Trans; eauto.
           rewrite get_set_hd in *; auto.
        -- eapply QualLeq_Trans; eauto.
           rewrite get_set_hd in *; auto.
        -- rewrite app_assoc; auto.
        -- rewrite app_assoc; auto.
      + right. unfold F' in *. destruct F; subst; simpl in *. exists (taus ++ x). do 3 eexists.
        match goal with
        | [ |- context[QualT (RefT _ _ (VariantType _)) ?Q] ] =>
          exists Q
        end.
        do 4 eexists. eexists. repeat split.
        6:{ repeat rewrite set_set_hd in *; eauto. }
        1:{
          rewrite Forall_app; split; [ | eauto ].
          prepare_Forall.
          eapply QualLeq_Trans; eauto.
          rewrite get_set_hd in *; auto.
        }
        all: eauto.
        -- eapply QualLeq_Trans; eauto.
           rewrite get_set_hd in *; auto.
        -- rewrite get_set_hd in *; auto.
        -- rewrite app_assoc; auto.
        -- rewrite app_assoc; auto. 
    - start_lceff_subgoals.
      destruct IHHtyp; destructAll.
      -- left; do 8 eexists; repeat split; eauto.
         --- apply forall2_nth_error_inv; [ | eapply Forall2_length; eauto ].
             intros.
             match goal with
             | [ H : Forall2 _ ?L1 ?L2,
                 H' : nth_error ?L1 _ = Some _,
                 H'' : nth_error ?L2 _ = Some _ |- _ ] =>
               specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
             end.
             intros; simpl in *.
             eapply ChangeBegLocalTyp; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_add_local_effects.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
      -- right; do 10 eexists; repeat split; eauto.
         --- apply forall2_nth_error_inv; [ | eapply Forall2_length; eauto ].
             intros.
             match goal with
             | [ H : Forall2 _ ?L1 ?L2,
                 H' : nth_error ?L1 _ = Some _,
                 H'' : nth_error ?L2 _ = Some _ |- _ ] =>
               specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
             end.
             intros; simpl in *.
             eapply ChangeBegLocalTyp; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_add_local_effects.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
    - start_lceff_subgoals.
      destruct IHHtyp; destructAll.
      -- left; do 9 eexists; repeat split; eauto.
         --- apply forall2_nth_error_inv; [ | eapply Forall2_length; eauto ].
             intros.
             match goal with
             | [ H : Forall2 _ ?L1 ?L2,
                 H' : nth_error ?L1 _ = Some _,
                 H'' : nth_error ?L2 _ = Some _ |- _ ] =>
               specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
             end.
             intros; simpl in *.
             eapply ChangeEndLocalTyp; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
      -- right; do 10 eexists; repeat split; eauto.
         --- apply forall2_nth_error_inv; [ | eapply Forall2_length; eauto ].
             intros.
             match goal with
             | [ H : Forall2 _ ?L1 ?L2,
                 H' : nth_error ?L1 _ = Some _,
                 H'' : nth_error ?L2 _ = Some _ |- _ ] =>
               specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
             end.
             intros; simpl in *.
             eapply ChangeEndLocalTyp; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             destruct F; subst; simpl in *; auto.
         --- eapply LCEffEqual_trans; eauto.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
  Qed.

  Lemma VariantCaseTypUnr_HasTypeInstruction S M Forig L t1 t2 L' tf tl es tausv' :
    HasTypeInstruction S M Forig L [VariantCase Unrestricted tausv' tf tl es] (Arrow t1 t2) L' ->
    qual Forig = [] ->
    exists tausv alpha cap l q' qv taus1 taus2 qf L'',
      tausv' = VariantType tausv /\
      Forall (fun '(QualT _ q) => QualLeq (qual Forig) q qf = Some true) alpha /\
      QualLeq (qual Forig) (get_hd (linear Forig)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear Forig)) Forig in
      M.is_empty (LinTyp S) = true /\
      QualLeq (qual F) qv q' = Some true /\
      QualLeq (qual F) (get_hd (linear F)) q' = Some true /\
      tf = Arrow taus1 taus2 /\
      let F1 := update_label_ctx ((taus2, L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
      Forall2 (fun es' tau => HasTypeInstruction S M F2 L es' (Arrow (taus1 ++ [tau]) taus2) L') es tausv /\
      Forall (fun '(QualT _ q0) => QualLeq (qual F) q0 Unrestricted = Some true) tausv /\
      QualValid (qual F) qv /\
      t1 = alpha ++ taus1 ++ [QualT (RefT cap l (VariantType tausv)) qv] /\
      t2 = alpha ++ [QualT (RefT cap l (VariantType tausv)) qv] ++ taus2 /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    intros.
    apply VariantCase_HasTypeInstruction in H.
    case H; intros; simpl in *; destructAll.
    - destruct Forig; subst; simpl in *; subst.
      exfalso; eapply QualLeq_Const_False; eauto.
    - do 10 eexists.
      repeat split; eauto.
  Qed.

  Lemma VariantCaseTypLin_HasTypeInstruction S M Forig L t1 t2 L' tausv' tf tl es :
    HasTypeInstruction S M Forig L [VariantCase Linear tausv' tf tl es] (Arrow t1 t2) L' ->
    qual Forig = [] ->
    exists alpha l qv taus1 taus2 tausv qf L'',
      tausv' = VariantType tausv /\
      Forall (fun '(QualT _ q) => QualLeq (qual Forig) q qf = Some true) alpha /\
      QualLeq (qual Forig) (get_hd (linear Forig)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear Forig)) Forig in
      M.is_empty (LinTyp S) = true /\
      tf = Arrow taus1 taus2 /\
      let F1 := update_label_ctx ((taus2, L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      Forall2 (fun es' tau => HasTypeInstruction S M F2 L es' (Arrow (taus1 ++ [tau]) taus2) L') es tausv /\
      QualLeq (qual F) Linear qv = Some true /\
      QualValid (qual F) qv /\
      t1 = alpha ++ taus1 ++ [QualT (RefT W l (VariantType tausv)) qv] /\
      t2 = alpha ++ taus2 /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    intros.
    apply VariantCase_HasTypeInstruction in H.
    case H; intros; simpl in *; destructAll.
    - do 8 eexists.
      repeat split; eauto.
    - destruct Forig; subst; simpl in *; subst.
      exfalso; eapply QualLeq_Const_False; eauto.
  Qed.

  Lemma ExistUnpack_HasTypeInstruction S M F L q ht tf tl es t1 t2 L' :
    HasTypeInstruction S M F L [ExistUnpack q ht tf tl es] (Arrow t1 t2) L' ->
    (exists t qf taus1 taus2 tau qv l sz qα L'',
        Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
        QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
        let F := update_linear_ctx (set_hd qf (linear F)) F in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: type F2) F2) in
        ht = (Ex sz qα tau) /\
        M.is_empty (LinTyp S) = true /\
        tf = Arrow taus1 taus2 /\
        HasTypeInstruction S M F3 (subst_ext (weak SPretype) L) es (Arrow (subst_ext (weak SPretype) taus1 ++ [tau]) (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') /\
        QualLeq (qual F) Linear q = Some true /\
        QualLeq (qual F) Linear qv = Some true /\
        QualValid (qual F) q /\
        QualValid (qual F) qv /\
        t1 = t ++ taus1 ++ [QualT (RefT W l (Ex sz qα tau)) qv] /\
        t2 = t ++ taus2 /\
        LCEffEqual (size F) (add_local_effects L tl) L' /\
        LCEffEqual (size F) L' L'')
      \/
    (exists t taus1 taus2 tau q' qv l sz qα q_ex p_ex L'' qf cap,
        Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) t /\
        QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
        ht = (Ex sz qα tau) /\
        tf = Arrow taus1 taus2 /\
        let F := update_linear_ctx (set_hd qf (linear F)) F in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        let F3 := subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: type F2) F2) in
        HasTypeInstruction S M F3 (subst_ext (weak SPretype) L) es (Arrow (subst_ext (weak SPretype) taus1 ++ [tau]) (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') /\
        tau = QualT p_ex q_ex /\
        QualLeq (qual F) q_ex Unrestricted = Some true /\
        QualLeq (qual F) q Unrestricted = Some true /\
        QualValid (qual F) q /\
        QualValid (qual F) qv /\
        QualLeq (qual F) qv q' = Some true /\
        QualLeq (qual F) (get_hd (linear F)) q' = Some true /\
        M.is_empty (LinTyp S) = true /\
        t1 = t ++ taus1 ++ [QualT (RefT cap l (Ex sz qα tau)) qv] /\
        t2 = t ++ [QualT (RefT cap l (Ex sz qα tau)) qv] ++ taus2 /\
        LCEffEqual (size F) (add_local_effects L tl) L' /\
        LCEffEqual (size F) L' L'').
  Proof.
    assert (Heq : [ExistUnpack q ht tf tl es] = [ExistUnpack q ht tf tl es]) by reflexivity.
    assert (Heq' : Arrow t1 t2 = Arrow t1 t2) by reflexivity.
    revert Heq Heq'.
    generalize [ExistUnpack q ht tf tl es] at 1 3. generalize (Arrow t1 t2) at 1 3.
    intros arr l1 Heq Heq' Htyp.
    revert t1 t2 Heq'.
    induction Htyp; intros t1 t2 Heq1; try now inv Heq.
    - right. simpl in *. inv Heq. inv Heq1.
      destruct F; simpl in *.
      exists []. do 13 eexists. repeat split.
      all: try eauto.
      -- rewrite set_set_hd; auto.
      -- rewrite get_set_hd; apply QualLeq_Refl.
      -- apply LCEffEqual_refl.
    - left. simpl in *. inv Heq. inv Heq1.
      destruct F; simpl in *.
      exists []. exists (get_hd linear). do 8 eexists; repeat split; try rewrite set_get_hd; eauto.
      -- apply QualLeq_Refl.
      -- apply LCEffEqual_refl.
    - eapply elt_eq_unit in Heq. destructAll. eapply Empty_HasTypeInstruction in Htyp1.


      edestruct IHHtyp2; try reflexivity.
      + left. inv Heq1. simpl in *. destructAll. do 10 eexists.
        repeat split; eauto.
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        inv H.
        destruct H6.
        eapply is_empty_eq_map in H.
        eauto.
        eapply Proper_HasTypeInstruction; eauto.
        eapply SplitStoreTypings_Empty_eq in H; eauto.
        2:{
          eapply ChangeBegLocalTyp; eauto.
          destruct F; subst; simpl in *.
          rewrite sizepairs_debruijn_weak_pretype.
          apply LCEffEqual_sym.
          apply LCEffEqual_subst_weak_pretype; auto.
        }
        eapply StoreTyping_Equiv; eauto.
        eapply LCEffEqual_trans; eauto.
        apply LCEffEqual_add_local_effects.
        destruct F; subst; simpl in *; auto.
      + right. inv Heq1. simpl in *. destructAll. do 14 eexists.
        repeat split.
        3:{
          eapply Proper_HasTypeInstruction.
          2-4,6-7: eauto.
          3:{
            destruct F; subst; simpl in *.
            eapply ChangeBegLocalTyp; eauto.
            simpl.
            rewrite sizepairs_debruijn_weak_pretype.
            apply LCEffEqual_sym.
            apply LCEffEqual_subst_weak_pretype; auto.
          }
          eapply SplitStoreTypings_Empty_eq in H; eauto.
          eapply StoreTyping_Equiv; eauto.
          eauto.
        }
        all: eauto.
        -- eapply SplitStoreTypings_Empty_eq in H; eauto.
           inv H.
           destruct H6.
           eapply is_empty_eq_map in H.
           eauto.
        -- destruct F; subst; simpl in *.
           eapply LCEffEqual_trans; eauto.
           apply LCEffEqual_add_local_effects; auto.
    - subst. inv Heq1. edestruct IHHtyp; eauto; destructAll; simpl in *; destructAll.
      + left.
        destruct F; subst; simpl in *.
        exists (taus ++ x). do 9 eexists. repeat split.
        4:{ rewrite set_set_hd in *; eauto. }
        all: try eauto.
        all: try rewrite app_assoc; try reflexivity.
        * apply Forall_app; split; [ | eauto ].
          prepare_Forall.
          eapply QualLeq_Trans; eauto.
          rewrite get_set_hd in *; auto.
        * eapply QualLeq_Trans; eauto.
          rewrite get_set_hd in *; auto.
      + right. destruct F; subst; simpl in *; exists (taus ++ x). do 13 eexists. repeat split; rewrite set_set_hd in *; rewrite get_set_hd in *.
        1:{
          apply Forall_app; split; [ | eauto ].
          prepare_Forall.
          eapply QualLeq_Trans; eauto.
        }
        all: eauto.
        * eapply QualLeq_Trans; eauto.
        * rewrite set_set_hd in *; auto.
        * rewrite app_assoc; reflexivity.
        * rewrite app_assoc; reflexivity.
    - start_lceff_subgoals.
      case IHHtyp; [ left | right ]; destructAll.
      -- do 10 eexists; repeat split; eauto.
         --- eapply ChangeBegLocalTyp; eauto.
             destruct F; subst; simpl in *.
             rewrite sizepairs_debruijn_weak_pretype.
             apply LCEffEqual_subst_weak_pretype; auto.
         --- eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_add_local_effects.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
      -- do 14 eexists; repeat split; eauto.
         --- eapply ChangeBegLocalTyp; eauto.
             destruct F; subst; simpl in *.
             rewrite sizepairs_debruijn_weak_pretype.
             apply LCEffEqual_subst_weak_pretype; auto.
         --- eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_add_local_effects.
             destruct F; subst; simpl in *.
             apply LCEffEqual_sym; auto.
    - start_lceff_subgoals.
      case IHHtyp; [ left | right ]; destructAll.
      -- do 10 eexists; repeat split; eauto.
         --- eapply ChangeEndLocalTyp; eauto.
             destruct F; subst; simpl in *.
             rewrite sizepairs_debruijn_weak_pretype.
             apply LCEffEqual_subst_weak_pretype; auto.
         --- eapply LCEffEqual_trans; eauto.
             destruct F; subst; simpl in *; auto.
         --- destruct F; subst; simpl in *; auto.
             eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_sym; auto.
      -- do 14 eexists; repeat split; eauto.
         --- eapply ChangeEndLocalTyp; eauto.
             destruct F; subst; simpl in *.
             rewrite sizepairs_debruijn_weak_pretype.
             apply LCEffEqual_subst_weak_pretype; auto.
         --- destruct F; subst; simpl in *.
             eapply LCEffEqual_trans; eauto.
         --- destruct F; subst; simpl in *.
             eapply LCEffEqual_trans; eauto.
             apply LCEffEqual_sym; auto.
  Qed.

  Lemma ExistUnpackUnr_HasTypeInstruction S M Forig L t1 t2 L' ht tf tl es :
    HasTypeInstruction S M Forig L [ExistUnpack Unrestricted ht tf tl es] (Arrow t1 t2) L' ->
    qual Forig = [] ->
    exists qf alpha cap l q' qv sz qa p_ex q_ex taus1 taus2 L'',
      Forall (fun '(QualT _ q) => QualLeq (qual Forig) q qf = Some true) alpha /\
      QualLeq (qual Forig) (get_hd (linear Forig)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear Forig)) Forig in
      ht = Ex sz qa (QualT p_ex q_ex) /\
      t1 = alpha ++ taus1 ++ [QualT (RefT cap l (Ex sz qa (QualT p_ex q_ex))) qv] /\
      t2 = alpha ++ [QualT (RefT cap l (Ex sz qa (QualT p_ex q_ex))) qv] ++ taus2 /\
      tf = Arrow taus1 taus2 /\
      let F1 := update_label_ctx ((taus2, L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
      HasTypeInstruction
        S M
        (debruijn.subst_ext (debruijn.weak subst.SPretype)
                            (update_type_ctx ((sz, qa, Heapable) :: type F2) F2))
        (debruijn.subst_ext (debruijn.weak subst.SPretype) L) es
        (Arrow
           (debruijn.subst_ext (debruijn.weak subst.SPretype)
              taus1 ++ [QualT p_ex q_ex])
           (debruijn.subst_ext (debruijn.weak subst.SPretype)
              taus2))
        (debruijn.subst_ext (debruijn.weak subst.SPretype) L') /\
      QualValid (qual F) qv /\
      QualLeq (qual F) qv q' = Some true /\
      QualLeq (qual F) (get_hd (linear F)) q' = Some true /\
      QualLeq (qual F) q_ex Unrestricted = Some true /\
      M.is_empty (LinTyp S) = true /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    intros.
    apply ExistUnpack_HasTypeInstruction in H.
    case H; intros; simpl in *; destructAll.
    - destruct Forig; subst; simpl in *; subst.
      exfalso; eapply QualLeq_Const_False; eauto.
    - do 13 eexists.
      repeat split; eauto.
  Qed.

  Lemma ExistUnpackLin_HasTypeInstruction S M Forig L t1 t2 L' sz qa tau tf tl es :
    HasTypeInstruction S M Forig L [ExistUnpack Linear (Ex sz qa tau) tf tl es] (Arrow t1 t2) L' ->
    qual Forig = [] ->
    exists qf alpha l qv taus1 taus2 L'',
      Forall (fun '(QualT _ q) => QualLeq (qual Forig) q qf = Some true) alpha /\
      QualLeq (qual Forig) (get_hd (linear Forig)) qf = Some true /\
      let F := update_linear_ctx (set_hd qf (linear Forig)) Forig in
      t1 = alpha ++ taus1 ++ [QualT (RefT W l (Ex sz qa tau)) qv] /\
      t2 = alpha ++ taus2 /\
      tf = Arrow taus1 taus2 /\
      let F1 := update_label_ctx ((taus2, L'') :: label F) F in
      let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
      HasTypeInstruction
        S M
        (debruijn.subst_ext (debruijn.weak subst.SPretype)
                            (update_type_ctx ((sz, qa, Heapable) :: type F2) F2))
        (debruijn.subst_ext (debruijn.weak subst.SPretype) L) es
        (Arrow
           (debruijn.subst_ext (debruijn.weak subst.SPretype)
              taus1 ++ [tau])
           (debruijn.subst_ext (debruijn.weak subst.SPretype)
              taus2))
        (debruijn.subst_ext (debruijn.weak subst.SPretype) L') /\
      QualValid (qual F) qv /\
      QualLeq (qual F) Linear qv = Some true /\
      M.is_empty (LinTyp S) = true /\
      LCEffEqual (size F) (add_local_effects L tl) L' /\
      LCEffEqual (size F) L' L''.
  Proof.
    intros.
    apply ExistUnpack_HasTypeInstruction in H.
    case H; intros; simpl in *; destructAll.
    - match goal with
      | [ H : Ex _ _ _ = Ex _ _ _ |- _ ] =>
        inversion H; subst
      end.
      do 7 eexists.
      repeat split; eauto.
    - destruct Forig; subst; simpl in *; subst.
      exfalso; eapply QualLeq_Const_False; eauto.
  Qed.

End Utils.
