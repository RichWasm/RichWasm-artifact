From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.map_util
        RWasm.typing_util RWasm.tactics RWasm.list_util RWasm.EnsembleUtil
        RWasm.splitting RWasm.surface RWasm.memory RWasm.subst RWasm.debruijn RWasm.misc_util.

Lemma HasTypeInstruction_subst_index : forall {S C F L es tau1 tau2 L' ks idx},
    InstIndValid_at F ks idx ->
    HasTypeInstruction
      S C F
      L es (Arrow tau1 tau2) L' ->
    HasTypeInstruction
      S C (InstFunctionCtxInd_under_ks F ks idx)
      (subst_ext' (under_ks' ks (subst'_of (subst_of_index idx))) L)
      (map
         (subst_ext' (under_ks' ks (subst'_of (subst_of_index idx))))
         es)
      (Arrow
         (subst_ext'
            (under_ks' ks (subst'_of (subst_of_index idx))) tau1)
         (subst_ext'
            (under_ks' ks (subst'_of (subst_of_index idx))) tau2))
      (subst_ext' (under_ks' ks (subst'_of (subst_of_index idx))) L').
Admitted.

Lemma HasTypeInstruction_subst_indices : forall {idxs S C F F' L es tau1 tau2 L' kvs},
    InstIndsValid F' (FunT kvs (Arrow tau1 tau2)) idxs ->
    Function_Ctx_empty F' ->
    InstFunctionCtxInds F idxs = Some F' ->
    simple_fields_eq F (add_constraints F' kvs) ->
    KindVarsValid F' kvs ->
    HasTypeInstruction
      S C F
      L es (Arrow tau1 tau2) L' ->
    HasTypeInstruction
      S C F'
      (subst.subst_indices idxs L)
      (map (subst.subst_indices idxs) es)
      (Arrow
         (subst.subst_indices idxs tau1)
         (subst.subst_indices idxs tau2))
      (subst.subst_indices idxs L').
Proof.
  induction idxs.
  all: intros; simpl in *; auto.
  1:{
    rewrite map_id.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H; auto
    end.
  }
  match goal with
  | [ H : context[InstFunctionCtxInds ?F ?IDX] |- _ ] =>
    remember (InstFunctionCtxInds F IDX) as obj;
    generalize (eq_sym Heqobj); case obj; intros; subst
  end.
  2:{
    match goal with
    | [ H : ?A = None, H' : context[?A] |- _ ] =>
      rewrite H in H'; inv H'
    end.
  }
  match goal with
  | [ H : ?A = Some _, H' : context[?A] |- _ ] =>
    rewrite H in H'
  end.
  match goal with
  | [ H : InstIndsValid _ _ _ |- _ ] =>
    generalize H; intros; inv H
  end.
  match goal with
  | [ X : FunType |- _ ] => destruct X
  end.
  match goal with
  | [ H : InstIndsValid _ _ (_ :: _),
      H' : InstIndsValid _ _ _ |- _ ] =>
    generalize H'; intros;
    apply InstIndsValid_length_eq_to_InstInds in H'
  end.
  2:{
    match goal with
    | [ H : InstIndsValid _ _ (_ :: _) |- _ ] =>
      eapply InstFunctionCtxInds_add_constraints in H
    end.
    2:{
      simpl.
      match goal with
      | [ H : InstFunctionCtxInds _ _ = Some _ |- _ ] =>
        rewrite H
      end.
      auto.
    }
    2: auto.
    match goal with
    | [ |- ?A = ?B ] =>
      let H' := fresh "H" in
      assert (H' : Datatypes.S A = Datatypes.S B);
      [ | inv H'; auto ]
    end.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      apply InstInd_length in H
    end.
    simpl in *.
    lia.
  }
  destructAll.
  match goal with
  | [ H : Function_Ctx_empty ?F,
      H' : InstIndsValid ?F (FunT ?KVS ?ATYP) ?IDXS,
      H'' : InstInds (FunT ?KVS ?ATYP) ?IDXS = Some (FunT ?KVSP ?ATYPP),
      H''' : InstIndValid ?F (FunT ?KVSPP ?ATYPPP) ?IDX |- _ ] =>
    specialize (subst_of_indices_commute_gen H H' H'' H''')
  end.
  simpl.
  intros.

  Ltac solve_subst_index_comp_goal :=
    rewrite subst_ext_subst_of_index;
    do 2 rewrite subst_ext_subst_of_indices;
    do 2 rewrite subst_ext'_assoc;
    rewrite subst'_of_comp;
    match goal with
    | [ |- subst_ext' ?A _ = subst_ext' ?B _ ] =>
      replace B with A; auto
    end.

  match goal with
  | [ H : _ ∘' under_kindvars' ?KVS _ = _
      |- context[subst_index ?IDX (subst_indices ?IDXS ?L)] ] =>
    match goal with
    | [ |- context[map ?F _] ] =>
      replace F with
          (fun inst : Instruction =>
             (subst_indices
                IDXS
                (subst_ext'
                   (under_kindvars'
                      KVS
                      (subst'_of (subst_of_index IDX)))
                   inst)))
    end
  end.
  2:{
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    solve_subst_index_comp_goal.
  }
  
  repeat match goal with
  | [ H : _ ∘' under_kindvars' ?KVS _ = _
      |- context[subst_index ?IDX (subst_indices ?IDXS ?L)] ] =>
    replace (subst_index IDX (subst_indices IDXS L)) with
        (subst_indices
           IDXS
           (subst_ext'
              (under_kindvars'
                 KVS
                 (subst'_of (subst_of_index IDX)))
              L))
        by solve_subst_index_comp_goal
  end.
  
  rewrite <-map_map.
  match goal with
  | [ H : InstFunctionCtxInds ?F ?IDXS = Some ?FP,
      H' : InstFunctionCtxInd ?FP ?IDX = Some ?FPP |- _ ] =>
    let H'' := fresh "H" in
    assert (H'' : Forall index_closed IDXS);
    [ eapply InstIndValids_index_closed; eauto | ];
    let H''' := fresh "H" in
    assert (H''' : index_closed IDX);
    [ eapply InstIndValid_index_closed; eauto | ];
    specialize (InstFunctionCtxInds_comm (ks:=zero) (idx:=IDX) H H'' H''')
  end.
  erewrite InstFunctionCtxInd_under_empty_ks; eauto.
  rewrite plus_zero.
  intros.

  match goal with
  | [ H : InstInd _ _ = Some (FunT ?KVS _),
      H' : context[ks_of_idxs ?IDXS] |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : ks_of_kvs KVS = ks_of_idxs IDXS)
  end.
  { eapply ks_of_kvs_to_ks_of_idxs; eauto.
    match goal with
    | [ H : simple_fields_eq ?F (add_constraints ?FP ?KVS),
        H' : InstIndsValid ?FP (FunT ?KVS ?ATYP) ?IDXS |- _ ] =>
      specialize (InstFunctionCtxInds_add_constraints
                    (F:=F) (F':=FP) (kvs:=KVS)
                    (atyp:=ATYP) (idxs:=IDXS))
    end.
    simpl.
    match goal with
    | [ H : ?A = _ |- context[?A] ] => rewrite H
    end.
    intros.
    match goal with
    | [ H : ?A -> ?B -> ?C -> _,
        H' : ?A, H'' : ?B, H''' : ?C |- _ ] =>
      specialize (H H' H'' H''')
    end.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      apply InstInd_length in H
    end.
    lia. }
  
  eapply IHidxs; auto.
  - eapply InstIndsValid_Function_Ctx_stronger; eauto.
  - eauto.
  - match goal with
    | [ H : _ = ks_of_idxs ?A |- context[ks_of_idxs ?A] ] =>
      rewrite <-H
    end.
    eapply simple_fields_eq_subst; eauto.
  - eapply KindVarsValid_InstInd; eauto.
  - rewrite under_kindvars'_to_under_ks'.
    match goal with
    | [ H : ks_of_kvs ?A = _ |- context[ks_of_kvs ?A] ] =>
      rewrite H
    end.
    eapply HasTypeInstruction_subst_index; auto.
    match goal with
    | [ H : _ = ks_of_idxs ?A |- context[ks_of_idxs ?A] ] =>
      rewrite <-H
    end.
    eapply InstIndValid_to_InstIndValid_at; eauto.
Qed.
