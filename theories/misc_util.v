From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Sets.Ensembles Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.tactics RWasm.list_util
        RWasm.map_util RWasm.EnsembleUtil RWasm.splitting RWasm.surface RWasm.typing_util RWasm.debruijn RWasm.subst.

Lemma cons_split : forall (A B : Type) cs (a : A) (b : B) a_s bs,
    (a :: a_s, b :: bs) = split cs ->
    exists cs',
      (a_s, bs) = split cs'.
Proof.
  intros.
  destruct cs as [ | [] cs' ].
  - simpl in *.
    congruence.
  - simpl in *.
    exists cs'.
    destruct (split cs').
    congruence.
Qed.

(* TODO move *)
Lemma fold_size_vals_pull_base_out vs base :
  (fold_left (fun (n : nat) (v : Value) => size_val v + n) vs base
  =
  base + fold_left (fun (n : nat) (v : Value) => size_val v + n) vs 0).
Proof.
  rewrite !fold_left_map with (f := Nat.add) (g := size_val) by lia.
  rewrite !fold_symmetric by lia.
  induction vs; cbn; lia.
Qed.

(* TODO move *)
Lemma fold_sizes_pull_base_out szs base :
  (fold_left (fun (acc : nat) (sz : Size) =>
                match size_to_nat sz with
                | Some n => acc + n
                | None => acc
                end) szs base
  =
  base + fold_left (fun (acc : nat) (sz : Size) =>
                match size_to_nat sz with
                | Some n => acc + n
                | None => acc
                end) szs 0).
Proof.
  rewrite !fold_left_map with (f := Nat.add)
                              (g := fun sz => match size_to_nat sz with
                                           | Some n => n
                                           | None => 0%nat end)
    by (intros acc sz; destruct (size_to_nat sz); lia).
  rewrite !fold_symmetric by lia.
  induction szs; cbn; lia.
Qed.

(* TODO move *)
Lemma fold_leq_holds_under_base_accumulator : forall vs szs base1 base2,
    (fold_left (fun (n : nat) (v : Value) => size_val v + n) vs 0 <=
     fold_left
       (fun (acc : nat) (sz : Size) =>
        match size_to_nat sz with
        | Some n => acc + n
        | None => acc
        end) szs 0)%nat ->
    (base1 <= base2)%nat ->
    (fold_left (fun (n : nat) (v : Value) => size_val v + n) vs base1 <=
     fold_left
       (fun (acc : nat) (sz : Size) =>
        match size_to_nat sz with
        | Some n => acc + n
        | None => acc
        end) szs base2)%nat.
Proof.
  intros*.
  rewrite fold_size_vals_pull_base_out with (base := base1).
  rewrite fold_sizes_pull_base_out with (base := base2).
  lia.
Qed.

Lemma size_valid_empty_implies_to_nat : forall sz,
    SizeValid [] sz ->
    exists n, size_to_nat sz = Some n.
Proof.
  induction sz; intros.
  + inv H; try discriminate.
    destruct var; inv H1.
  + inv H; try discriminate.
    inv H0.
    eapply IHsz1 in H1.
    eapply IHsz2 in H2.
    destruct H1 as [n1 H1].
    destruct H2 as [n2 H2].
    exists (n1 + n2).
    simpl.
    rewrite H1.
    rewrite H2.
    congruence.
  + exists n.
    simpl.
    congruence.
Qed.


Lemma is_size_to_nat sz :
  size_closed sz ->
  exists n, size_to_nat sz = Some n.
Proof.
  induction sz; intros; simpl in *; eauto.
  contradiction.
  destructAll. edestruct IHsz1; eauto.
  edestruct IHsz2; eauto.
  rewrite H1, H2. now eauto.
Qed.

Lemma sizeOfPretyType_env_concrete S pt sz :
  Forall (fun '(s, _, _) => size_closed s) S ->
  sizeOfPretype S pt = Some sz  ->
  exists n,
    size_to_nat sz = Some n.
Proof.
  revert S sz.
  eapply Pretype_ind'
    with (P := fun pretype =>
                 forall S sz,
                   Forall (fun '(s, _, _) => size_closed s) S ->
                   sizeOfPretype S pretype = Some sz  ->
                   exists n,
                     size_to_nat sz = Some n)
         (Q := fun typ =>
                 forall S sz,
                   Forall (fun '(s, _, _) => size_closed s) S ->
                   sizeOfType S typ = Some sz  ->
                   exists n,
                     size_to_nat sz = Some n)
         (F := fun _ => True) (H := fun _ => True) (A := fun _ => True);
    intros; simpl in *; eauto;
    try now (match goal with
             | [ H : Some _ = Some _ |- _ ] => inv H; simpl; eauto
             end).
  - simpl in *. destruct n; eauto. destruct i; eauto.
    inv H0. simpl. now eauto.
    inv H0. simpl. now eauto.
    destruct f.
    inv H0. simpl. now eauto.
    inv H0. simpl. now eauto.
  - destruct (nth_error S v) eqn:Hnth; simpl in *; try congruence.
    eapply nth_error_In in Hnth.
    eapply Forall_forall in Hnth; eauto.
    destruct p as [[? ? ] ?].
    eapply is_size_to_nat. inv H0. assumption.
  - revert sz H1. induction l; intros sz H1; simpl in *.
    + inv H1; simpl; eauto.
    + destruct (sizeOfType S a) eqn:Hs; try congruence.
      destruct (fold_size (map (sizeOfType S) l)) eqn:Hss; try congruence.
      inv H1. simpl in *.
      inv H. edestruct H3; eauto. rewrite H.
      edestruct IHl; simpl; eauto. rewrite H1. eauto.
  - eapply H; [| eassumption ].
    constructor; eauto.
    simpl. eauto.
Qed.

Corollary sizeOfPretyType_concrete pt sz :
  sizeOfPretype [] pt = Some sz  ->
  exists n,
    size_to_nat sz = Some n.
Proof.
  intros. eapply sizeOfPretyType_env_concrete; eauto.
Qed.

Lemma sizeOfPretype_length T T' tau sz :
  sizeOfPretype T tau = Some sz ->
  length T = length T' ->
  exists sz',
    sizeOfPretype T' tau = Some sz'.
Proof.
  revert T T' sz.
  eapply Pretype_ind'
    with (P := fun pt =>
                 forall T T' sz,
                   sizeOfPretype T pt = Some sz ->
                   length T = length T' ->
                   exists sz',
                     sizeOfPretype T' pt = Some sz')
         (Q := fun typ =>
                 forall T T' sz,
                   sizeOfType T typ = Some sz ->
                   length T = length T' ->
                   exists sz',
                     sizeOfType T' typ = Some sz')
         (F := fun _ => True) (H := fun _ => True) (A := fun _ => True);

    intros; simpl in *; eauto.
  - destruct (nth_error T v) eqn:Hnth; simpl in *; try congruence.
    inv H. eapply nth_error_Some_length in Hnth.
    erewrite nth_error_nth' with (d := (SizeConst 0, QualConst Unrestricted, Heapable)); [| congruence ].
    simpl; eauto.
  - revert sz H0. induction l; intros sz Hf; simpl in *; eauto.
    destruct (sizeOfType T a) eqn:Hsz; try congruence.
    destruct (fold_size (map (sizeOfType T) l)) eqn:Hszs; try congruence. inv Hf.

    inv H. simpl. edestruct H3; eauto. rewrite H.
    edestruct IHl; eauto. rewrite H0. now eauto.
  - eapply H; eauto. simpl; congruence.
Qed.

Lemma TypeValid_sizeOfType F tau :
  TypeValid F tau ->
  exists sz,
    sizeOfType (type F) tau = Some sz.
Proof.
  intros Htyp.
  set (P := fun (F : Function_Ctx) tau  =>
              exists sz,
                sizeOfType (type F) tau = Some sz).
  eapply (TypeValid_ind' P (fun _ _ => True) (fun _ _ => True) (fun _ _ => True));
    unfold P; intros; simpl; eauto.
  - destruct n as [? [] | [|]]; simpl; eauto.
  - rewrite H1. simpl. eauto.
  - simpl in *.
    revert H1. clear. intros Hall. induction Hall; simpl; eauto.
    destructAll. rewrite H. rewrite H0. eauto.
  - simpl. destructAll. eapply sizeOfPretype_length.
    eassumption. destruct C. simpl. eapply map_length.
Qed.


Lemma HasTypeValue_sizeOfType S F v tau :
  HasTypeValue S F v tau ->
  exists sz,
    sizeOfType (type F) tau = Some sz.
Proof.
  intros Htyp.
  set (P := fun (S : StoreTyping) (F : Function_Ctx) (v : Value) tau  =>
              exists (sz : Size), sizeOfType (type F) tau = Some sz).
  eapply HasTypeValue_ind' with (P := P); try eassumption; unfold P;
    intros; try now (do 2 eexists; intuition eauto).
  - destruct nt as [? [] | [|]]; simpl; eauto.
  - eapply TypeValid_sizeOfType. eassumption.
  - eapply TypeValid_sizeOfType. eassumption.
  - eapply TypeValid_sizeOfType. eassumption.
Qed.


Lemma HasTypeValue_sizeOfType_concrete S F v tau :
  HasTypeValue S F v tau ->
  type F = [] ->
  exists sz n,
    sizeOfType [] tau = Some sz /\
      size_to_nat sz = Some n.
Proof.
  intros Htyp Heq.
  eapply HasTypeValue_sizeOfType in Htyp. destructAll.
  rewrite Heq in H. destruct tau. simpl in *.
  edestruct sizeOfPretyType_concrete. eassumption.
  do 2 eexists. split; eauto.
Qed.


Lemma size_val_Prod vs : size_val (term.Prod vs) = fold_right Nat.add 0%nat (map size_val vs).
Proof.
  cbn.
  rewrite fold_left_map with (f := Nat.add) (g := size_val) by lia.
  now rewrite fold_symmetric by lia.
Qed.

Theorem TypeValid_Prod_cons F z l q:
TypeValid F (QualT (ProdT (z :: l)) q) -> TypeValid F (QualT (ProdT l) q).
Proof.
  intros.
  inversion H; subst. inversion H4; inversion H5; subst.
  econstructor; eauto.
Qed.

Fixpoint under'_n_loc (n: nat) S:=
match n with
  | 0 => S
  | Datatypes.S n' => under' SLoc (under'_n_loc n' S)
end.
Theorem under'_n_loc_S n S:
under' SLoc (under'_n_loc n S) =  under'_n_loc (Datatypes.S n) S.
Proof. auto. Qed.

Fixpoint under'_n_pretype (n: nat) S :=
match n with
  | 0 => S
  | Datatypes.S n' => under' SPretype (under'_n_pretype n' S)
end.


Theorem under_n_loc_not_loc n l v s f:
s <> SLoc ->
under'_n_loc n (subst'_of (ext SLoc l id)) s v f = VarKind s (v + f s).
Proof.
  revert l v f.
  induction n; simpl; intros.
  - destruct s. exfalso. apply H. auto.
    all: simpl; unfold get_var'; unfold weaks'; unfold var; simpl;
      f_equal; unfold zero; lia.
  - destruct s; unfold under'; unfold under_ks';
     match goal with
      | [h: ?s <> ?s |- _ ] => exfalso; apply h; auto
      | [ |- (if (_ <? sing ?s1 1 ?s2) then _ else _) = _ ] =>
          assert (h: sing s1 1 s2 = 0); auto; rewrite h; simpl; erewrite IHn; [
          simpl;  f_equal; unfold plus; lia | intro h'; inversion h']
    end.
 Qed.
Theorem under_n_loc_loc_plus_not_loc n l v  f1 f2:
f1 SLoc = 0 ->
under'_n_loc n (subst'_of (ext SLoc l id)) SLoc v (plus f1 f2) =
  under'_n_loc n (subst'_of (ext SLoc l id)) SLoc v f2.
Proof.
  revert l v f1 f2.
  induction n; simpl; intros.
  - unfold subst'_loc. unfold ext. simpl.
    destruct v; simpl.
    + destruct l; auto.
      unfold get_var'. unfold weaks'. unfold var. simpl.
      f_equal. unfold plus. lia.
    + unfold get_var'. unfold weaks'. unfold var. simpl.
      f_equal. unfold plus. lia.
  - unfold under'. unfold under_ks'.
    enough (sing SLoc 1 SLoc = 1); auto. rewrite H0.
    destruct v; simpl.
    unfold var'. unfold var. simpl.
    f_equal. unfold plus. lia.
    enough (plus (sing SLoc 1) (plus f1 f2) = plus f1 (plus (sing SLoc 1) f2)).
    rewrite H1.
    rewrite IHn; auto.
    rewrite plus_comm. rewrite <- plus_assoc.
    f_equal. rewrite plus_comm. auto.
 Qed.

From Coq.Logic Require Import FunctionalExtensionality.

Lemma sizeOfType_subst_n_loc C l t n:
  sizeOfType C (subst'_type (under'_n_loc n (subst'_of (ext SLoc l id))) t) =
  sizeOfType C t.
Proof.
  revert C l n.
  induction t using Typ_ind' with
    (P := fun p => forall C l n,
              sizeOfPretype C (subst'_pretype (under'_n_loc n (subst'_of (ext SLoc l id))) p) = sizeOfPretype C p)
    (F := fun _ => True) (A := fun _ => True) (H := fun _ => True);
    intros; simpl in *; eauto.
  - unfold get_var'. erewrite under_n_loc_not_loc.
    simpl. unfold zero. f_equal. f_equal. lia.
    intro. inversion H.
  - induction l; simpl; simpl; auto.
    rewrite Forall_forall in *.
    rewrite H; [ | left; auto ].
    destruct (sizeOfType C a) eqn:Eq; auto.
    rewrite IHl; eauto.
    intros. rewrite H; auto. right. auto.
  - erewrite <- IHt. repeat f_equal.
    + destruct q; auto; simpl.
      unfold get_var'.
      erewrite under_n_loc_not_loc. simpl. f_equal. unfold zero. lia.
      intro. inversion H.
    + unfold under'. unfold under_ks'.
       extensionality x. extensionality n'. extensionality f.
       destruct x; simpl.
      -- enough (sing SPretype 1 SLoc = 0); auto. rewrite H.
         rewrite Nat.sub_0_r.
         rewrite under_n_loc_loc_plus_not_loc; eauto.
      -- enough (sing SPretype 1 SQual = 0); auto. rewrite H.
         repeat erewrite under_n_loc_not_loc.
         simpl. f_equal. unfold plus. lia.
         all: intro; inversion H0.
      -- enough (sing SPretype 1 SSize = 0); auto. rewrite H.
         repeat erewrite under_n_loc_not_loc.
         simpl. f_equal. unfold plus. lia.
         all: intro; inversion H0.
      -- enough (sing SPretype 1 SPretype = 1); auto.
         rewrite H. destruct n'; simpl.
         unfold var'. unfold var. simpl.
         rewrite under_n_loc_not_loc. simpl. auto.
         intro. inversion H0.
         repeat erewrite under_n_loc_not_loc.
         simpl. unfold plus. rewrite H.
         f_equal. lia.
         all: intro; inversion H0.
  - rewrite  under'_n_loc_S . eauto.
Qed.

Theorem sizeOfType_subst_loc C l t:
  sizeOfType C (subst_ext (ext SLoc l id) t) = sizeOfType C t.
Proof.
  intros.
  specialize sizeOfType_subst_n_loc  with (n := 0).
  simpl. auto.
Qed.

Lemma nth_error_shift_down : forall {v} {A} {l : list A} {v'},
    v <> v' ->
    nth_error (remove_nth l v') (shift_down_after v v' 0) =
    nth_error l v.
Proof.
  induction v.
  - intros.
    destruct l; simpl.
    -- match goal with
       | [ |- nth_error _ ?IDX = _ ] =>
         destruct IDX; auto
       end.
    -- destruct v'; solve_impossibles.
       unfold shift_down_after.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with true; auto
       end.
  - intros.
    destruct l; simpl.
    -- match goal with
       | [ |- nth_error _ ?IDX = _ ] =>
         destruct IDX; auto
       end.
    -- destruct v'.
       --- unfold shift_down_after.
           match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with false; auto
           end.
           rewrite Nat.sub_1_r.
           simpl; auto.
       --- erewrite <-IHv.
           2:{
             match goal with
             | [ H : Datatypes.S ?V <> Datatypes.S ?V2 |- _ ] =>
               assert (V <> V2); eauto
             end.
           }
           unfold shift_down_after; simpl.
           match goal with
           | [ |- _ = _ _ (if ?B then _ else _) ] =>
             remember B as b; generalize (eq_sym Heqb);
             case b; intros
           end.
           all:
             match goal with
             | [ H : (?A <? ?B) = _ |- context[?C <? ?D] ] =>
               replace (C <? D) with (A <? B); rewrite H
             end.
           2,4: unfold Nat.ltb in *; simpl in *; auto.
           ---- simpl; auto.
           ---- match goal with
                | [ |- context[?A - 1] ] => destruct A
                end.
                ----- match goal with
                      | [ |- context[remove_nth _ ?A] ] => destruct A
                      end.
                      ------ lia.
                      ------ unfold Nat.ltb in *; simpl in *; lia.
                ----- simpl.
                      rewrite Nat.sub_0_r; auto.
Qed.

Lemma ltb_S: forall n1 n2,
  (n1 <? n2) = (Datatypes.S n1 <? Datatypes.S n2).
Proof.
  intro n1. induction n1; intros; destruct n2; auto.
Qed.

Lemma minus_less_bool : forall {c a b},
    c <= a ->
    c <= b ->
    (a - c <? b - c) = (a <? b).
Proof.
  induction c.
  - intros.
    repeat rewrite Nat.sub_0_r; auto.
  - intros.
    destruct a; simpl in *.
    1:{
      exfalso; eapply Nat.nle_succ_0; eauto.
    }
    destruct b; simpl in *.
    1:{
      exfalso; eapply Nat.nle_succ_0; eauto.
    }
    rewrite <-ltb_S.
    match goal with
    | [ H : forall _ _, _ |- _ ] => apply H
    end.
    all: apply Peano.le_S_n; auto.
Qed.

Lemma shift_up_after_new_kspec : forall v kspec,
    shift_up_after v kspec 0 <> kspec.
Proof.
  intros v.
  induction v; intros; destruct kspec; simpl;
    unfold shift_up_after in *; simpl in *; auto.
  destruct (v <? kspec) eqn:Eq.
  - specialize (IHv kspec).
    rewrite <- ltb_S.
    rewrite Eq in *. lia.
  - specialize (IHv kspec).
    rewrite <- ltb_S.
    rewrite Eq in *.
    lia.
Qed.

Lemma shift_down_shift_up_after_eq_id : forall v kspec,
    shift_down_after (shift_up_after v kspec 0) kspec 0
    =
    v.
Proof.
  intros v. induction v; intros; destruct kspec;
    unfold shift_down_after in *; unfold shift_up_after in *; simpl; auto.
  lia.
  destruct (v <? kspec) eqn:Eq.
  - rewrite <- ltb_S. rewrite Eq in *.
    rewrite <- ltb_S. rewrite Eq. lia.
  - specialize (IHv kspec).
    rewrite <- ltb_S. rewrite Eq in *.
    rewrite <- ltb_S. simpl in *.
    destruct (v + 1 <? kspec) eqn:Eq'; lia.
Qed.

Lemma simpl_debruijn_subst_ext_conds : forall {knd obj},
    debruijn_subst_ext_conds
      (debruijn.subst'_of
         (debruijn.ext knd obj debruijn.id))
      debruijn.zero
      knd
      obj.
Proof.
  split; [ | split ].
  all: intros; simpl in *.
  - unfold debruijn.zero.
    unfold debruijn.ext.
    simpl.
    destruct knd; simpl in *.
    all: unfold debruijn.zero.
    all: unfold debruijn.ext.
    all: simpl.
    all: rewrite debruijn.plus_id; auto.
  - destruct knd; simpl in *.
    all: unfold debruijn.zero in *.
    all: unfold debruijn.ext.
    all: simpl.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        let H := fresh "H" in
        case B; intros; subst; solve_impossibles
      end.
    all: unfold debruijn.id.
    all: unfold debruijn.var.
    all: simpl.
    all: unfold debruijn.get_var'.
    all: unfold debruijn.weaks'.
    all: unfold debruijn.var.
    all: simpl.
    all: unfold shift_down_after.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        let H := fresh "H" in
        remember B as b; generalize (eq_sym Heqb);
        case b; intros
      end.
    all: try rewrite Nat.ltb_lt in *.
    all:
      try match goal with
          | [ H : _ < 0 |- _ ] => inversion H
          end.      
    all: unfold debruijn.zero.
    all: rewrite Nat.add_0_r.
    all: rewrite Nat.add_sub_assoc; auto.
    all:
      match goal with
      | [ H : ?V <> 0 |- _ <= ?V ] =>
        revert H; case V; intros; solve_impossibles
      end.
    all: apply Peano.le_n_S.
    all: apply Nat.le_0_l.
  - unfold debruijn.ext.
    all: destruct knd; destruct knd0; solve_impossibles.
    all: simpl.
    all: unfold debruijn.get_var'.
    all: unfold debruijn.weaks'.
    all: unfold debruijn.var.
    all: simpl.
    all: unfold debruijn.zero.
    all: rewrite Nat.add_0_r; auto.
Qed.

Lemma simpl_debruijn_weak_conds : forall {ks},
    debruijn_weaks_conds (debruijn.weaks' ks) debruijn.zero ks.
Proof.
  intros.
  constructor; intros.
  - unfold debruijn.zero in *.
    match goal with
    | [ H : _ < 0 |- _ ] => inversion H
    end.
  - constructor.
Qed.

Lemma qual_debruijn_subst_ext : forall {q ks kndspec f obj},
    kndspec <> subst.SQual ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_qual f q = q.
Proof.
  destruct q; simpl; auto.
  intros.
  unfold debruijn.get_var'.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  destruct kndspec.
  all: solve_impossibles.
  all: rewrite H2; auto.
Qed.

Lemma quals_debruijn_subst_ext : forall {qs ks kndspec f obj},
    kndspec <> subst.SQual ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_quals f qs = qs.
Proof.
  induction qs; simpl; auto.
  intros.
  erewrite IHqs; eauto.
  erewrite qual_debruijn_subst_ext; eauto.
Qed.

Lemma loc_debruijn_subst_ext : forall {l ks kndspec f obj},
    kndspec <> subst.SLoc ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_loc f l = l.
Proof.
  destruct l; simpl; auto.
  intros.
  unfold debruijn.get_var'.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  destruct kndspec.
  all: solve_impossibles.
  all: rewrite H2; auto.
Qed.

Lemma size_debruijn_subst_ext : forall {sz ks kndspec f obj},
    kndspec <> subst.SSize ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_size f sz = sz.
Proof.
  induction sz; simpl; auto.
  2:{
    intros.
    erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
  }

  intros.
  unfold debruijn.get_var'.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  destruct kndspec.
  all: solve_impossibles.
  all: rewrite H2; auto.
Qed.

Lemma sizes_debruijn_subst_ext : forall {szs ks kndspec f obj},
    kndspec <> subst.SSize ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_sizes f szs = szs.
Proof.
  induction szs; simpl; auto.
  intros.
  erewrite IHszs; eauto.
  erewrite size_debruijn_subst_ext; eauto.
Qed.

Definition related_subst_conds f1 f2 kndspec obj1 obj2 :=
  exists ks,
    debruijn_subst_ext_conds f1 ks kndspec obj1 /\
    debruijn_subst_ext_conds f2 ks kndspec obj2.

Ltac solve_related_lemma lem :=
  unfold related_subst_conds;
  intros; destructAll;
  eapply lem; eauto.

Lemma qual_related_subst_conds1 : forall {q kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_qual f1 q = q.
Proof.
  solve_related_lemma @qual_debruijn_subst_ext.
Qed.

Lemma qual_related_subst_conds2 : forall {q kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_qual f2 q = q.
Proof.
  solve_related_lemma @qual_debruijn_subst_ext.
Qed.

Lemma quals_related_subst_conds1 : forall {qs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_quals f1 qs = qs.
Proof.
  solve_related_lemma @quals_debruijn_subst_ext.
Qed.

Lemma quals_related_subst_conds2 : forall {qs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_quals f2 qs = qs.
Proof.
  solve_related_lemma @quals_debruijn_subst_ext.
Qed.

Lemma loc_related_subst_conds1 : forall {l kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SLoc ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_loc f1 l = l.
Proof.
  solve_related_lemma @loc_debruijn_subst_ext.
Qed.

Lemma loc_related_subst_conds2 : forall {l kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SLoc ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_loc f2 l = l.
Proof.
  solve_related_lemma @loc_debruijn_subst_ext.
Qed.

Lemma size_related_subst_conds1 : forall {sz kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_size f1 sz = sz.
Proof.
  solve_related_lemma @size_debruijn_subst_ext.
Qed.

Lemma size_related_subst_conds2 : forall {sz kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_size f2 sz = sz.
Proof.
  solve_related_lemma @size_debruijn_subst_ext.
Qed.

Lemma sizes_related_subst_conds1 : forall {szs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_sizes f1 szs = szs.
Proof.
  solve_related_lemma @sizes_debruijn_subst_ext.
Qed.

Lemma sizes_related_subst_conds2 : forall {szs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_sizes f2 szs = szs.
Proof.
  solve_related_lemma @sizes_debruijn_subst_ext.
Qed.

Lemma kindvar_debruijn_subst_ext : forall {kv ks kndspec f obj},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_kindvar f kv = kv.
Proof.
  destruct kv; simpl; auto; intros.
  - repeat erewrite quals_debruijn_subst_ext; eauto.
  - repeat erewrite sizes_debruijn_subst_ext; eauto.
  - erewrite size_debruijn_subst_ext; eauto.
    erewrite qual_debruijn_subst_ext; eauto.
Qed.

Lemma kindvar_related_subst_conds1 : forall {kv kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_kindvar f1 kv = kv.
Proof.
  solve_related_lemma @kindvar_debruijn_subst_ext.
Qed.

Lemma kindvar_related_subst_conds2 : forall {kv kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_kindvar f2 kv = kv.
Proof.
  solve_related_lemma @kindvar_debruijn_subst_ext.
Qed.

Lemma debruijn_weaks_conds_under_knd : forall {f knd ks ks''},
    debruijn_weaks_conds f ks ks'' ->
    debruijn_weaks_conds
      (debruijn.under' knd f)
      (debruijn.plus (debruijn.sing knd 1) ks)
      ks''.
Proof.
  unfold debruijn_weaks_conds.
  intros; destructAll.
  split; intros.
  - unfold debruijn.under'.
    unfold debruijn.under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
      generalize (eq_sym Heqb); case b; intros
    end.
    -- unfold debruijn.var'.
       unfold debruijn.var; auto.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
       end.
       2:{
         apply minus_less; auto.
         rewrite Nat.ltb_ge in *; auto.
       }
       unfold debruijn.plus.
       rewrite Nat.add_comm.
       rewrite Nat.add_assoc.
       rewrite Nat.sub_add.
       --- rewrite Nat.add_comm; auto.
       --- rewrite Nat.ltb_ge in *; auto.
  - unfold debruijn.under'.
    unfold debruijn.under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      let H := fresh "H" in
      assert (H : B = false); [ | rewrite H ]
    end.
    { rewrite Nat.ltb_ge.
      unfold Peano.ge in *.
      unfold debruijn.plus in *.
      eapply Nat.le_trans.
      - eapply OrdersEx.Nat_as_OT.le_add_le_sub_r; eauto.
      - apply Nat.le_sub_l. }
    match goal with
    | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; auto
    end.
    2:{
      apply minus_geq; auto.
      rewrite Nat.ltb_ge in *; auto.
    }
    unfold debruijn.plus.
    repeat rewrite <-Nat.add_assoc.
    match goal with
    | [ |- _ _ (_ + ?A) = _ _ (_ + ?B) ] =>
      let H := fresh "H" in
      assert (H : A = B); [ | rewrite H; auto ]
    end.
    rewrite Nat.add_comm.
    rewrite <-Nat.add_assoc.
    rewrite Nat.sub_add; auto.
    rewrite Nat.ltb_ge in *; auto.
Qed.

Lemma debruijn_weaks_conds_under_kindvars : forall {kvs f ks ks''},
    debruijn_weaks_conds f ks ks'' ->
    debruijn_weaks_conds
      (subst.under_kindvars' kvs f)
      (fold_right
         (fun kv ks' =>
            (debruijn.plus
               (debruijn.sing
                  (subst.kind_of_kindvar kv)
                  1)
               ks'))
         ks
         kvs)
      ks''.
Proof.
  induction kvs; simpl; auto.
  intros.
  all: destruct a; simpl.
  all: unfold subst.under_kindvar'; simpl.
  all: apply debruijn_weaks_conds_under_knd.
  all: eauto.
Qed.

Lemma plus_never_less : forall {A ks ks' knd},
    @debruijn.plus A ks ks' knd <? ks knd = false.
Proof.
  intros.
  unfold debruijn.plus.
  rewrite Nat.ltb_ge.
  apply le_plus_l.
Qed.

Lemma minus_noneq : forall {b a c},
    a <> b + c ->
    b <= a ->
    a - b <> c.
Proof.
  intros; lia.
Qed.

Lemma shift_down_after_shifts : forall {v kspec kspec' shft},
    shft <= v ->
    shft <= kspec ->
    shift_down_after (v - shft) (kspec - shft) (kspec' + shft) =
    shift_down_after v kspec kspec'.
Proof.
  intros.
  unfold shift_down_after.
  rewrite minus_less_bool; auto.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    remember B as b;
      generalize (eq_sym Heqb); case b; intros
  end.
  - rewrite <-Nat.add_assoc.
    match goal with
    | [ |- ?A + ?B = ?A + ?C ] =>
      let H := fresh "H" in
      assert (H : B = C); [ | rewrite H; auto ]
    end.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add; auto.
  - rewrite <-Nat.add_assoc.
    match goal with
    | [ |- ?A + ?B - ?D = ?A + ?C - ?D ] =>
      let H := fresh "H" in
      assert (H : B = C); [ | rewrite H; auto ]
    end.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add; auto.
Qed.

Lemma debruijn_subst_ext_under_knd : forall {f ks kndspec knd obj},
    debruijn_subst_ext_conds f ks kndspec obj ->
    debruijn_subst_ext_conds
      (debruijn.under' knd f)
      (debruijn.plus (debruijn.sing knd 1) ks)
      kndspec
      obj.
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  split; [ | split ]; intros; simpl.
  - unfold debruijn.under'.
    unfold debruijn.under_ks'.
    rewrite plus_never_less.
    unfold debruijn.plus.
    rewrite minus_plus.
    rewrite H; auto.
    match goal with
    | [ |-
        subst.subst'_rwasm _ (debruijn.weaks' ?F1) _ =
        subst.subst'_rwasm _ (debruijn.weaks' ?F2) _ ] =>
      let H := fresh "H" in
      assert (H : F1 = F2);
        [ | rewrite H; auto ]
    end.
    unfold debruijn.plus.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    rewrite Nat.add_comm.
    rewrite <-Nat.add_assoc.
    rewrite <-Nat.add_assoc.
    match goal with
    | [ |- ?A + ?B = ?A + ?C ] =>
      let H := fresh "H" in
      assert (H : B = C);
        [ | rewrite H; auto ]
    end.
    apply Nat.add_comm.
  - unfold debruijn.under'.
    unfold debruijn.under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
        generalize (eq_sym Heqb); case b; intros
    end.
    -- unfold debruijn.var'.
       unfold debruijn.var.
       unfold shift_down_after.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         let H := fresh "H" in
         assert (H : B = true); [ | rewrite H; auto ]
       end.
       rewrite Nat.ltb_lt in *.
       unfold debruijn.plus.
       eapply Nat.lt_le_trans; eauto.
       apply le_plus_l.
    -- rewrite H0.
       2:{
         apply minus_noneq; auto.
         rewrite Nat.ltb_ge in *; auto.
       }
       unfold debruijn.plus.
       match goal with
       | [ |- _ = _ _ (shift_down_after ?V (?SHFT + _) _) ] =>
         rewrite <-(shift_down_after_shifts (v:=V) (shft:=SHFT))
       end.
       --- rewrite minus_plus.
           rewrite Nat.add_comm; auto.
       --- rewrite Nat.ltb_ge in *; auto.
       --- apply le_plus_l.
  - unfold debruijn.under'.
    unfold debruijn.under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
        generalize (eq_sym Heqb); case b; intros
    end.
    -- unfold debruijn.var'.
       unfold debruijn.var; auto.
    -- rewrite H1; auto.
       unfold debruijn.plus.
       rewrite Nat.add_comm.
       rewrite Nat.add_assoc.
       rewrite Nat.sub_add.
       --- rewrite Nat.add_comm; auto.
       --- rewrite Nat.ltb_ge in *; auto.
Qed.

Lemma debruijn_subst_ext_under_kindvars : forall {kvs ks f kndspec obj},
    debruijn_subst_ext_conds f ks kndspec obj ->
    debruijn_subst_ext_conds
      (subst.under_kindvars' kvs f)
      (fold_right
         (fun kv ks' =>
            (debruijn.plus
               (debruijn.sing
                  (subst.kind_of_kindvar kv)
                  1)
               ks'))
         ks
         kvs)
      kndspec
      obj.
Proof.
  induction kvs; simpl; auto.
  intros.
  specialize (IHkvs _ _ _ _ H).
  destruct a; simpl.
  all: unfold subst.under_kindvar'; simpl.
  all: apply debruijn_subst_ext_under_knd; auto.
Qed.

Lemma kindvars_debruijn_subst_ext : forall {kvs ks kndspec f obj},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    debruijn_subst_ext_conds f ks kndspec obj ->
    subst.subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; simpl; auto; intros.
  all: erewrite kindvar_debruijn_subst_ext; eauto.
  all: destruct a; simpl in *.
  all: erewrite IHkvs; eauto.
  all: unfold subst.under_kindvar'; simpl.
  all: eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma kindvars_related_subst_conds1 : forall {kvs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_kindvars f1 kvs = kvs.
Proof.
  solve_related_lemma @kindvars_debruijn_subst_ext.
Qed.

Lemma kindvars_related_subst_conds2 : forall {kvs kndspec f1 f2 obj1 obj2},
    kndspec <> subst.SSize ->
    kndspec <> subst.SQual ->
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    subst.subst'_kindvars f2 kvs = kvs.
Proof.
  solve_related_lemma @kindvars_debruijn_subst_ext.
Qed.

Lemma sizeOfPretype_subst_rec_provable : forall {pt f ks pt' tctx},
    debruijn_subst_ext_conds f ks SPretype pt' ->
    RecVarUnderRefPretype pt (ks SPretype) true ->
    sizeOfPretype
      (remove_nth tctx (ks SPretype))
      (subst'_pretype f pt) =
    sizeOfPretype tctx pt.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f ks pt' tctx,
            debruijn_subst_ext_conds f ks SPretype pt' ->
            RecVarUnderRefPretype pt (ks SPretype) true ->
            sizeOfPretype
              (remove_nth tctx (ks SPretype))
              (subst'_pretype f pt) =
            sizeOfPretype tctx pt)
       (fun t =>
          forall f ks pt' tctx,
            debruijn_subst_ext_conds f ks SPretype pt' ->
            RecVarUnderRefTyp t (ks SPretype) true ->
            sizeOfType
              (remove_nth tctx (ks SPretype))
              (subst'_type f t) =
            sizeOfType tctx t)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    eauto.
  - unfold debruijn_subst_ext_conds in *.
    destructAll.
    unfold get_var' in *.
    match goal with
    | [ H : context[_ <> _ _] |- _ ] => rewrite H
    end.
    1: simpl.
    1: unfold zero.
    1: rewrite nth_error_shift_down; auto.

    all:
      match goal with
      | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
        inversion H; subst
      end.
    all: intro; subst.
    all: rewrite Nat.eqb_refl in *.
    all: lia.
  - match goal with
    | [ |- fold_size ?A = fold_size ?B ] =>
      replace B with A; auto
    end.
    rewrite map_map.
    apply map_ext_in.
    intros.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; eapply (H _ H'); eauto
    end.
    match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
      inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; eapply (H _ H'); eauto
    end.
  - match goal with
    | [ |- context[?A :: remove_nth ?L (?F ?KND)] ] =>
      replace (A :: remove_nth L (F KND)) with
          (remove_nth (A :: L)
                      ((plus (sing KND 1) F) KND))
    end.
    2:{ unfold plus; unfold sing; auto. }
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    2:{
      unfold plus; unfold sing; simpl.
      match goal with
      | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
        inversion H; subst
      end.
      rewrite Nat.add_1_r in *; auto.
    }
    eapply debruijn_subst_ext_under_knd; eauto.
  - match goal with
    | [ |- context[remove_nth ?L (?F ?KND)] ] =>
      replace (remove_nth L (F KND)) with
          (remove_nth L
                      ((plus (sing SLoc 1) F) KND))
    end.
    2:{ unfold plus; unfold sing; auto. }
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    2:{
      unfold plus; unfold sing; simpl.
      match goal with
      | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
        inversion H; subst; auto
      end.
    }
    eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma sizeOfPretype_subst_rec : forall {pt' pt tctx sz q hc},
    RecVarUnderRefPretype pt 0 true ->
    sizeOfPretype
      tctx
      (subst'_pretype (subst'_of (ext SPretype pt' id)) pt) =
    sizeOfPretype ((sz, q, hc) :: tctx) pt.
Proof.
  intros.
  replace tctx with (remove_nth ((sz, q, hc) :: tctx) (zero SPretype)) by auto.
  eapply sizeOfPretype_subst_rec_provable; eauto.
  eapply simpl_debruijn_subst_ext_conds; eauto.
Qed.

Lemma SizeOfValue_Typecheck_Actual : forall v S F tau sztau n,
  HasTypeValue S F v tau ->
  sizeOfType (type F) tau = Some sztau ->
  (size F) = [] ->
  size_to_nat sztau = Some n ->
  (size_val v = n).
Proof with
  (match goal with H : Some _ = Some _ |- _ => inv H end;
   match goal with H : size_to_nat (SizeConst _) = _ |- _ => cbn in H; inv H end;
   easy).
  intros v S F tau sztau n H; revert sztau n.
  pose (P := fun (S : StoreTyping) (F : Function_Ctx) (v : Value) tau =>
               forall (sztau : Size) (n : nat),
                 sizeOfType (type F) tau = Some sztau ->
                 size F = [] -> size_to_nat sztau = Some n -> size_val v = n).
  change (P S F v tau).
  revert H. apply HasTypeValue_ind'; try apply H; unfold P; clear P.
  - cbn; destruct nt as [? [] | [|]]; intros...
  - cbn. intros...
  - intros.
    revert S0 q H H1 sztau n H2 H3 H4.
    induction H0.
    + intros; cbn in *...
    + intros S0 q Hsplit Hforall sztau n Hsize HsizeC Hsztau.
      rewrite size_val_Prod.
      cbn. rewrite <- size_val_Prod.
      pose proof Hsplit as HS'; apply SplitStoreTypings_cons in HS'; destruct HS' as [S' HS'].
      inv Hforall.
      simpl in Hsize.
      assert (hsz1: exists sz1, sizeOfType (type C) z = Some sz1).
      {
        destruct (sizeOfType (type C) z) eqn:Eq; eauto.
      } destruct hsz1 as [sz1 hsz1].
      rewrite hsz1 in Hsize.
      assert (hsz2: exists sz2, fold_size (map (sizeOfType (type C)) l'') = Some sz2).
      {
        destruct (fold_size (map (sizeOfType (type C)) l'')) eqn:Eq; eauto.
      } destruct hsz2 as [sz2 hsz2]. rewrite hsz2 in Hsize.
      injection Hsize as hsztau. subst.
      simpl in Hsztau.
      assert (hn1: exists n1, size_to_nat sz1 = Some n1).
      { destruct (size_to_nat sz1) eqn:Eq; eauto. } destruct hn1 as [n1 hn1].
      rewrite hn1 in Hsztau. 
      assert (hn2: exists n2, size_to_nat sz2 = Some n2).
      { destruct (size_to_nat sz2) eqn:Eq; eauto. } destruct hn2 as [n2 hn2].
      rewrite hn2 in Hsztau. injection Hsztau as hn1n2.
      subst.
      f_equal; eauto.
      -- apply SplitStoreTypings_cons in Hsplit. destruct Hsplit.
         erewrite IHForall3; eauto.
         inversion H5; inversion H6; subst.
         econstructor; eauto.
  - cbn. intros...
  - cbn. intros...
  - cbn. intros...
  - cbn. intros...
  - cbn. intros...
  - intros. cbn. erewrite H0; eauto.
    simpl. simpl in H1.
    match goal with
    | [ H : TypeValid _ _ |- _ ] => inversion H; subst
    end.
    erewrite sizeOfPretype_subst_rec; eauto.
  - intros. cbn. erewrite H1; eauto.
    simpl in H2.
    rewrite sizeOfType_subst_loc. eauto.
  - cbn. intros...
Qed.

Lemma nth_error_app : forall (A : Type) (a : A) L1 L2, nth_error (L1 ++ a :: L2) (length L1) = Some a.
Proof.
  intros.
  induction L1; eauto.
Qed.

Lemma nth_upd_length_eq (A : Type) (l : list A) x1 x2 :
  nth_upd (l ++ [x1]) (length l) x2 = l ++ [x2].
Proof.
  revert x1 x2.
  induction l; simpl; eauto; intros.
  f_equal.
  eapply IHl.
Qed.

Lemma nth_upd_length_less (A : Type) (l : list A) x1 x2 n :
  n < length l ->
  nth_upd (l ++ [x1]) n x2 = (nth_upd l n x2) ++ [x1].
Proof.
  revert n x1 x2.
  induction l; simpl; intros; try lia.
  destruct n; eauto.
  simpl.
  f_equal.
  eapply IHl.
  lia.
Qed.

Lemma nth_upd_length_greater (A : Type) (l : list A) x1 x2 n :
  n > length l ->
  nth_upd (l ++ [x1]) n x2 = l ++ [x1].
Proof.
  revert n x1 x2.
  induction l; simpl; intros.
  - destruct n; try lia; eauto.
  - destruct n; try lia.
    f_equal.
    eapply IHl.
    lia.
Qed.

Lemma nth_upd_length (A : Type) (l : list A) n x:
  length l = length (nth_upd l n x).
Proof.
  revert x n.
  induction l; eauto; simpl; intros.
  destruct n; simpl; eauto.
Qed.

Lemma add_local_effects_addition l tl tau1 tau2 sz:
  add_local_effects l tl ++ [(tau2, sz)] = add_local_effects (l ++ [(tau1, sz)]) (tl ++ [(length l, tau2)]).
Proof.
  revert l tau2 sz tau1.
  induction tl; simpl; intros.
  - unfold get_localtype.
    rewrite nth_error_app.
    unfold set_localtype.
    rewrite nth_upd_length_eq.
    congruence.
  - destruct a.
    unfold get_localtype.
    assert (n < (length l) \/ n = (length l) \/ n > (length l)) by lia.
    destruct H as [H | [H | H]].
    + rewrite (nth_error_app1 _ _ H).
      destruct (nth_error_some_exists _ _ _ H).
      rewrite H0.
      destruct x.
      unfold set_localtype.
      eapply nth_upd_length_less in H.
      rewrite H.
      erewrite nth_upd_length.
      eapply IHtl.
    + assert (length l <= n) by lia.
      eapply nth_error_None in H0.
      rewrite H0.
      rewrite H.
      rewrite nth_error_app.
      unfold set_localtype.
      rewrite nth_upd_length_eq.
      eapply IHtl.
    + assert (length l <= n) by lia.
      eapply nth_error_None in H0.
      rewrite H0.
      assert (length (l ++ [(tau1, sz)]) <= n) by (rewrite app_length; simpl; lia).
      eapply nth_error_None in H1.
      rewrite H1.
      eapply IHtl.
Qed.

Lemma add_local_effects_addition_lceff C l l' tl tau1 tau2 sz sz':
  SizeLeq C sz sz' = Some true ->
  SizeLeq C sz' sz = Some true ->
  LCEffEqual C l' (add_local_effects l tl) ->
  LCEffEqual C (l' ++ [(tau2, sz)]) (add_local_effects (l ++ [(tau1, sz')]) (tl ++ [(length l, tau2)])).
Proof.
  intros.
  rewrite <-add_local_effects_addition.
  apply Forall2_app; auto.
Qed.

Theorem nth_upd_same_second {U T} (x x': U) (y: T) l n:
      nth_error l n = Some (x, y) ->
      snd (split (nth_upd l n (x', y))) = snd (split l).
  Proof.
    revert x x' y n.
    induction l; simpl; intros; auto.
    destruct a. destruct n.
    - simpl. destruct (split l) eqn:Eq; simpl.
      f_equal. simpl in H. injection H. auto.
    - simpl. destruct (split l) eqn:Eq. simpl in *.
      specialize (IHl x x' y n H). 
      destruct (split (nth_upd l n (x', y))) eqn:Eq'.
      simpl in *.
      f_equal; auto.
   Qed.

Lemma add_local_effects_preserves_sizes L tl:
  snd (split L) = snd (split (add_local_effects L tl)).
Proof.
  revert L.
  induction tl; intros; destruct L; simpl; auto.
  - destruct a.
    enough (get_localtype n [] = None). rewrite H.
    rewrite <- IHtl. auto.
    destruct n; auto.
  - destruct a. destruct p. destruct (split L) eqn:Eq.
    destruct (get_localtype n ((t0, s) :: L)) eqn:Eq'.
    + destruct p. rewrite <- IHtl. unfold set_localtype.
      unfold get_localtype in Eq'.
      erewrite nth_upd_same_second; eauto.
      simpl. destruct (split L) eqn:Eq''.
      simpl. f_equal. injection Eq. auto.
    + rewrite <- IHtl. simpl. destruct (split L) eqn:Eq''.
      simpl. f_equal. injection Eq. auto.
Qed.

Theorem snd_split_same_length : forall {T U} {l1 l1' l2: list (T * U)},
    snd (split (l1 ++ l2)) = snd (split (l1' ++ l2)) ->
    length l1 = length l1'.
Proof.
  intros.
  assert (Hlen : length (snd (split (l1 ++ l2))) = length (snd (split (l1' ++ l2)))).
  { rewrite H; auto. }
  do 2 rewrite split_length_r in Hlen.
  do 2 rewrite app_length in Hlen.
  lia.
Qed.

Theorem snd_split_same_mid_provable : forall {T U} (l1 l1' l2: list (T * U)) a b L1 L1' L2 L2',
    snd (split (l1 ++ l2)) = snd (split (l1' ++ l2)) ->
    length l1 = length l1' ->
    split (l1  ++ (a,b) :: l2) = (L1, L1') ->
    split (l1' ++ (a,b) :: l2) = (L2, L2') ->
    L1' = L2'.
Proof.
  induction l1; intros; simpl in *.
  - destruct l1'; simpl in *.
    2:{
      match goal with
      | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
      end.
    }
    repeat match goal with
           | [ H : context[split l2] |- _ ] => revert H
           end.
    remember (split l2) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros; simpl in *; subst.
    repeat match goal with
           | [ H : (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H; auto
           end.
  - destruct l1'; simpl in *.
    1:{
      match goal with
      | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
      end.
    }
    destruct_prs.
    repeat match goal with
           | [ H : _ = _ |- _ ] => revert H
           end.
    remember (split (l1 ++ l2)) as obj.
    generalize (eq_sym Heqobj).
    case obj.
    remember (split (l1' ++ l2)) as obj'.
    generalize (eq_sym Heqobj').
    case obj'.
    remember (split (l1 ++ (a0, b) :: l2)) as obj''.
    generalize (eq_sym Heqobj'').
    case obj''.
    remember (split (l1' ++ (a0, b) :: l2)) as obj'''.
    generalize (eq_sym Heqobj''').
    case obj'''.
    intros; simpl in *.
    match goal with
    | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
      inversion H
    end. 
    repeat match goal with
           | [ H : (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H
           end.
    match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ |- _ :: ?A = _ :: ?B ] =>
      replace B with A; auto
    end.
    eapply IHl1.
    2-4: eauto.
    repeat match goal with
           | [ H : ?A = _ |- context[?A] ] => rewrite H
           end.
    simpl; auto.
Qed.

Theorem snd_split_same_mid : forall {T U} (l1 l1' l2: list (T * U)) a b L1 L1' L2 L2',
  snd (split (l1 ++ l2)) = snd (split (l1' ++ l2)) ->
  split (l1  ++ (a,b) :: l2) = (L1, L1') ->
  split (l1' ++ (a,b) :: l2) = (L2, L2') ->
  L1' = L2'.
Proof.
  intros.
  eapply snd_split_same_mid_provable; eauto.
  eapply snd_split_same_length; eauto.
Qed.

Lemma snd_split_app_1 (A B : Type) (l1 : list (A * B)) l1' l2:
  snd (split l1) = snd (split l1') ->
  snd (split (l1 ++ l2)) = snd (split (l1' ++ l2)).
  Proof.
    revert l1 l1'.
    induction l2; simpl; intros.
    - repeat rewrite app_nil_r. auto.
    - destruct l1; destruct l1'; simpl; auto; destruct a; destruct p; simpl in *.
      + destruct (split l1') eqn:Eqsl1'. simpl in H. inversion H.
      + destruct (split l1) eqn:Eqsl1. simpl in H. inversion H.
      + specialize (IHl2 l1 l1').
        destruct (split l1') eqn:Eqsl1'. destruct (split l1) eqn:Eqsl1.
        destruct (split (l1 ++ (a, b) :: l2)) eqn:Eqsl1abl2.
        destruct (split (l1' ++ (a, b) :: l2)) eqn:Eqsl1'abl2.
        destruct p0. simpl in *. injection H as h. subst.
        f_equal.
        specialize (IHl2 eq_refl).
        eapply snd_split_same_mid; eauto.
  Qed.

Lemma snd_split_app_2 (A B : Type) (l1 : list (A * B)) l2' l2:
  snd (split l2) = snd (split l2') ->
  snd (split (l1 ++ l2)) = snd (split (l1 ++ l2')).
  Proof.
    revert l2 l2'.
    induction l1; simpl; intros; auto.
    destruct a.
    specialize (IHl1 _ _ H).
    destruct (split (l1 ++ l2)) eqn:Eqsl12.
    destruct (split (l1 ++ l2')) eqn:Eqsl12'.
    simpl in *.
    f_equal. auto.  
  Qed.

Definition LCSizeEqual C (L : Local_Ctx) (L' : Local_Ctx) :=
  Forall2
    (fun '(t0, sz0) '(t1, sz1) =>
       SizeLeq C sz0 sz1 = Some true /\
       SizeLeq C sz1 sz0 = Some true)
    L L'.

Lemma LCSizeEqual_refl : forall C L,
    LCSizeEqual C L L.
  Proof.
    intros.
    induction L; constructor.
    destruct a.
    split; auto; apply SizeLeq_Refl.
    inversion IHL; subst; eauto.
  Qed.

Lemma LCSizeEqual_sym : forall {C L1 L2},
    LCSizeEqual C L1 L2 ->
    LCSizeEqual C L1 L1.
  Proof.
    intros.
    induction H; simpl; constructor.
    destruct x. destruct y. destructAll.
    split; apply SizeLeq_Refl.
    apply LCSizeEqual_refl.
  Qed.

Lemma LCSizeEqual_trans : forall {C L1 L2 L3},
    LCSizeEqual C L1 L2 ->
    LCSizeEqual C L2 L3 ->
    LCSizeEqual C L1 L3.
  Proof.
    intros C L1.
    induction L1; intros; destruct L2; destruct L3; simpl.
    constructor.
    inversion H0.
    inversion H0.
    inversion H.
    inversion H.
    inversion H.
    inversion H0.
    inversion H. inversion H0. subst.
    destruct a. destruct p. destruct p0. destructAll.
    constructor.
    split; eapply SizeLeq_Trans; eauto.
    eapply IHL1; eauto.
 Qed.

Lemma LCEffEqual_LCSizeEqual : forall {C L1 L2},
    LCEffEqual C L1 L2 ->
    LCSizeEqual C L1 L2.
  Proof.
    intros.
    induction H; simpl; constructor.
    destruct x. destruct y. destructAll.
    split; auto.
    inversion H0; subst; auto.
 Qed.

Lemma set_localtype_both_LCSizeEqual : forall {C L L' sz sz'} n tau,
    LCSizeEqual C L L' ->
    SizeLeq C sz sz' = Some true ->
    SizeLeq C sz' sz = Some true ->
    LCSizeEqual C
                (set_localtype n tau sz L)
                (set_localtype n tau sz' L').
  Proof.
    unfold set_localtype.
    intros.
    generalize dependent sz.
    revert n sz' tau.
    induction H; simpl; intros.
    constructor.
    destruct n.
    - constructor; auto.
    - constructor; auto.
      eapply IHForall2; auto.
  Qed.

Lemma set_localtype_LCSizeEqual : forall {C L n tau tau' sz sz'},
    nth_error L n = Some (tau, sz) ->
    SizeLeq C sz sz' = Some true ->
    SizeLeq C sz' sz = Some true ->
    LCSizeEqual C
                L
                (set_localtype n tau' sz' L).
  Proof.
    unfold set_localtype. unfold LCSizeEqual.
    intros C L.
    induction L; simpl; intros.
    constructor.
    destruct n; simpl in *; inversion H; subst.
    - constructor; auto.
      clear IHL.
      induction L; eauto.
      apply Forall2_cons.
      destruct a. split; apply SizeLeq_Refl.
      apply IHL.
    - constructor; eauto.
      destruct a.
      split; apply SizeLeq_Refl.
  Qed.

Lemma add_local_effects_LCSizeEqual : forall {C L L'} tl,
    LCSizeEqual C L L' ->
    LCSizeEqual C
                (add_local_effects L tl)
                (add_local_effects L tl).
  Proof.
    intros.
    generalize dependent L.
    revert C L'.
    induction tl; simpl; intros.
    - apply LCSizeEqual_refl.
    - destruct a.
      destruct (get_localtype n L) eqn:Eq.
      + destruct p. eapply IHtl; eauto.
        eapply LCSizeEqual_refl.
      + eapply IHtl; eauto.
 Qed.

Theorem Forall2_nth_upd_r {T U} l1 l2 n (x: T) (x': U) f:
Forall2 f l1 l2 ->
nth_error l1 n = Some x ->
f x x' ->
Forall2 f l1 (nth_upd l2 n x').
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  - destruct n; inversion H0.
  - destruct n; inversion H2; subst; simpl; eauto.
Qed.

Theorem LCSizeEqual_set_localtype_r C L n tau tau' s sz L':
LCSizeEqual C L L' ->
nth_error L n = Some (tau', sz) ->
SizeLeq C sz s = Some true ->
SizeLeq C s sz = Some true ->
LCSizeEqual C L (set_localtype n tau s L').
Proof.
  intros.
  generalize dependent n.
  generalize dependent sz.
  revert s tau tau'.
  induction H; simpl; intros.
  - destruct n; inversion H0.
  - destruct x. destruct y. destructAll.
    unfold set_localtype in *. simpl.
    destruct n; inversion H3; subst; econstructor; eauto.
    eapply Forall2_nth_upd_r; eauto.
    simpl. split; auto.
Qed.

Theorem Forall2_nth_error_imp_ex_nth_error
{U T} l1 l2 n x (P: U -> T -> Prop):
Forall2 P l1 l2 ->
nth_error l2 n = Some x ->
exists y, nth_error l1 n = Some y.
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  - destruct n; inversion H0.
  - destruct n; inversion H1; subst; simpl; eauto.
Qed.

Theorem LCSizeEqual_in_SizeLeq C L L' sz sz' tau tau' n:
        LCSizeEqual C L L' ->
        nth_error L n = Some (tau, sz) ->
        nth_error L' n = Some (tau', sz') ->
        SizeLeq C sz sz' = Some true /\ SizeLeq C sz' sz = Some true.
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  - destruct n; inversion H0.
  - destruct x. destruct y. destructAll.
    destruct n; inversion H1; inversion H2; subst; eauto.
 Qed.

Theorem LCSizeEqual_add_local_effects_r C L L' tl:
LCSizeEqual C L L' ->
LCSizeEqual C L (add_local_effects L' tl).
Proof.
  revert L L'.
  induction tl; simpl; intros; eauto.
  destruct a.
  destruct (get_localtype n L) eqn:Eq.
  - eapply get_localtype_same_len_Some in Eq. destruct Eq.
    + rewrite H0. destruct x.
      unfold get_localtype in H0.
      enough (exists y, nth_error L n = Some y). destructAll.
      destruct x.
      specialize (LCSizeEqual_in_SizeLeq _ _ _ _ _ _ _ _ H H1 H0).
      intros  [h1 h2].
      eapply IHtl.
      eapply LCSizeEqual_set_localtype_r; eauto.
      eapply  Forall2_nth_error_imp_ex_nth_error; eauto.
    + eapply Forall2_length. eauto.
  - eapply get_localtype_same_len_None in Eq. rewrite Eq.
    eauto.
    eapply Forall2_length. eauto.
 Qed.

Theorem LCSizeEqual_comm C L1 L2:
  LCSizeEqual C L1 L2 <-> LCSizeEqual C L2 L1.
Proof.
  split; intros; induction H; constructor.
  - destruct x. destruct y. destructAll.
    split; auto.
  - inversion H0; subst; auto.
  - destruct x. destruct y. destructAll. split; auto.
  - inversion H0; subst; auto.
Qed.

Lemma HasTypeInstruction_locals_eq_sizes S M F L es tf L':
  HasTypeInstruction S M F L es tf L' ->
  LCSizeEqual (size F) L L'.
Proof.
  intros.
  induction H; subst;
  try apply LCSizeEqual_add_local_effects_r;
    try apply LCSizeEqual_refl.
  - eapply LCSizeEqual_set_localtype_r; eauto.
    apply LCSizeEqual_refl.
    all: apply SizeLeq_Refl.
  - eapply LCSizeEqual_set_localtype_r; eauto.
    apply LCSizeEqual_refl.
    all: apply SizeLeq_Refl.
  - eapply LCSizeEqual_set_localtype_r; eauto.
    apply LCSizeEqual_refl.
    all: apply SizeLeq_Refl.
  - destruct F. auto.
  - eapply LCSizeEqual_trans; eauto.
  - unfold F' in *.
    destruct F. destruct F'. auto.
  - apply LCEffEqual_LCSizeEqual in H0.
    rewrite  LCSizeEqual_comm in H0.
    eapply LCSizeEqual_trans; eauto.
  - apply LCEffEqual_LCSizeEqual in H0.
    eapply LCSizeEqual_trans; eauto.
Qed.

Lemma HasTypeInstruction_local_is_tl : forall S M F L es tf L',
  HasTypeInstruction S M F L es tf L' ->
  exists tl,
    LocalCtxValid F (add_local_effects L tl) /\
    LCEffEqual (size F) (add_local_effects L tl) L'.
Proof.
  apply
    (HasTypeInstruction_mind'
       (fun S M F L es tf L' =>
          exists tl,
            LocalCtxValid F (add_local_effects L tl) /\
            LCEffEqual (size F) (add_local_effects L tl) L')
       (fun _ _ _ => True)
       (fun _ _ _ _ _ => True)
       (fun _ _ _ _ _ _ _ => True)).
  all: intros; simpl in *; auto.
    
  all:
    try match goal with
        | [ |- exists _, LocalCtxValid _ _ /\ LCEffEqual _ (add_local_effects _ _) (add_local_effects _ _) ] =>
          eexists; split; eauto; apply LCEffEqual_refl
        end.
  all:
    try match goal with
        | [ |- exists _, LocalCtxValid _ _ /\ LCEffEqual _ (add_local_effects ?L _) _ ] =>
          exists []; simpl; split; eauto; apply LCEffEqual_refl
        end.
  all: destructAll.
  all: destruct F; subst; simpl in *.
  all:
    try match goal with
        | [ H : LCEffEqual _ (add_local_effects ?L ?ANS) ?LP
            |- context[LCEffEqual _ (add_local_effects ?L _) ?LP] ] =>
          exists ANS; auto
        end.
  all:
    try match goal with
        | [ |- context[LCEffEqual _ (add_local_effects ?L _)
                                  (set_localtype ?IDX ?TAU _ ?L)] ] =>
          exists [(IDX, TAU)]; simpl; unfold get_localtype
        end.
  all:
    try match goal with
        | [ H : ?A = _ |- context[?A] ] =>
          rewrite H; split; eauto; [ | apply LCEffEqual_refl ]
        end.
  all: try split; eauto.
  all: try eapply LocalCtxValid_Function_Ctx; eauto.
  all: try eapply LocalCtxValid_set_localtype; eauto; try eapply LocalCtxValid_SizeValid_provable; eauto.
  all: try now ltac:(eexists; split; eauto; apply LCEffEqual_refl).

  - eexists.
    split.
    2: eapply add_local_effects_app_lceff; eauto.
    rewrite <-add_local_effects_app.
    eapply LocalCtxValid_LCEffEqual_add_local_effects; eauto.
  - eexists.
    split.
    2:{
      eapply LCEffEqual_trans; [ | eauto ].
      apply LCEffEqual_add_local_effects.
      apply LCEffEqual_sym; auto.
    }
    eapply LocalCtxValid_LCEffEqual_add_local_effects; eauto.
    simpl.
    apply LCEffEqual_sym; auto.
  - eexists.
    split.
    2:{
      eapply LCEffEqual_trans; eauto.
    }
    eapply LocalCtxValid_LCEffEqual_add_local_effects; eauto.
    -- eapply HasTypeInstruction_FirstLocalValid; eauto.
    -- apply LCEffEqual_refl.
Qed.

Lemma Forall2_app_inv : forall {A B} {P : A -> B -> _} {l1 l1' l2 l2'},
    Forall2 P (l1 ++ l1') (l2 ++ l2') ->
    length l1' = length l2' ->
    Forall2 P l1 l2 /\
    Forall2 P l1' l2'.
  Proof.
    intros A B P l1.
    induction l1; intros; destruct l1'; destruct l2; destruct l2';
      auto; inversion H; inversion H0; subst.
    - exfalso.
      apply Forall2_length in H6.
      rewrite app_length in H6.
      simpl in *. lia.
    - split; auto. repeat rewrite app_nil_r in *.
      apply Forall2_cons; auto.
    - exfalso.
      apply Forall2_length in H6.
      rewrite app_length in H6.
      simpl in *. lia.
    - specialize (IHl1 (a0 :: l1') l2 (b0 :: l2')).
      repeat rewrite <- app_comm_cons in H.
      inversion H; subst.
      specialize (IHl1 H9 H0).
      destructAll.
      split; auto.
  Qed.

Lemma HasTypeInstruction_local_is_tl_rev S M F L es tf L':
  HasTypeInstruction S M F L es tf L' ->
  exists tl,
    LCEffEqual (size F) L (add_local_effects L' tl).
Proof.
  intros.
  eapply HasTypeInstruction_locals_eq_sizes in H; try exact [].
  revert L' H.
  eapply rev_ind with (l := L); intros; eauto.
  - destruct L'; exists []; simpl in *. constructor. destruct p. destruct (split L'). inv H.
  - destruct (destruct_last L').
    + rewrite H1 in H0; destruct l; [rewrite app_nil_l in H0; destruct x | destruct p; simpl in H0;  destruct (split (l ++ [x]))]; simpl in H0; inv H0.
    + do 2 destruct H1.
      subst.
      eapply Forall2_app_inv in H0.
      2:{ simpl; auto. }
      destruct H0.
      eapply H in H0.
      destruct H0.
      destruct x1. destruct x. inv H1. destructAll.
      eexists.
      eapply add_local_effects_addition_lceff; eauto.
Qed.

Lemma add_local_effects_collapse L tl1 tl2:
  add_local_effects (add_local_effects L tl1) tl2 = add_local_effects L (tl1 ++ tl2).
Proof.
  revert L.
  induction tl1; simpl; intros; eauto.
  destruct a. destruct (get_localtype n L); [destruct p|]; eapply IHtl1.
Qed.

Lemma composition_typing_tl S M F L es es' ts1 ts2 tl:
  HasTypeInstruction S M F L (es ++ es') (Arrow ts1 ts2) (add_local_effects L tl) ->
  exists ts ts1' ts2' ts3 qf S1 S2 tl',
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
    QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
    QualValid (qual F) (get_hd (linear F)) /\
    QualValid (qual F) qf /\
    let F' := update_linear_ctx (set_hd qf (linear F)) F in
    HasTypeInstruction S1 M F' L es (Arrow ts1' ts3) (add_local_effects L tl') /\
    HasTypeInstruction S2 M F' (add_local_effects L tl') es' (Arrow ts3 ts2') (add_local_effects L tl) /\
    SplitStoreTypings [S1;S2] S.
Proof. 
  revert S M F L es ts1 ts2 tl.
  eapply rev_ind with (l := es').

  - intros S M F L1 es ts1 ts2 L2 Htyp.
    simpl in *. exists []; do 7 eexists; do 2 split; [ reflexivity | ]; split.
    rewrite app_nil_r in Htyp.
    now constructor. split. eapply QualLeq_Refl.
    split.
    {
      eapply HasTypeInstruction_QualValid; eauto.
    }
    split.
    {
      eapply HasTypeInstruction_QualValid; eauto.
    }
    split. rewrite app_nil_r in *. destruct F; simpl in *.
    rewrite set_get_hd.  eassumption.

    split. 
    eapply HasTypeInstruction_empty_list.
    5:{ eapply SplitStoreTypings_EmptyHeapTyping_r. }
    -- destruct S; reflexivity.
    -- eapply LocalCtxValid_Function_Ctx.
       1:{ eapply HasTypeInstruction_SecondLocalValid; eauto. }
       all: destruct F; subst; simpl in *; auto.
    -- eapply Forall_TypeValid_Function_Ctx.
       1:{ eapply HasTypeInstruction_OutputTypesValid; eauto. }
       all: destruct F; subst; simpl in *; auto.
    -- eapply HasTypeInstruction_QualValid_usable; eauto.
       all: destruct F; simpl; auto.
       rewrite get_set_hd; auto.

  - intros e es IH S M F L1 es_ ts1 ts2 L2 Htyp.
    simpl in *. rewrite app_assoc in Htyp. 
    edestruct composition_typing_single_strong. eassumption. destructAll.
    destruct F; simpl in *. destructAll.
    destruct (HasTypeInstruction_local_is_tl _ _ _ _ _ _ _ H).
    destructAll.
    edestruct IH.
    eapply ChangeEndLocalTyp; eauto.
    { apply LCEffEqual_sym; eauto. }
    destructAll.
    simpl in *. rewrite set_set_hd in *.

    edestruct SplitStoreTypings_assoc.
    match goal with
    | [ H : SplitStoreTypings [?S1; ?S2] ?S3,
        H' : SplitStoreTypings [?S3; _] _ |- _ ] => exact H
    end.
    eassumption. destructAll. 

    do 8 eexists. split; [ | split; [ | split; [ | split; [ | split; [ | split; [ | split; [ | split ]]]]]]]. 

    8:{ eapply ConsTyp; [ | | eassumption ].
        2:{ eapply FrameTyp. reflexivity.
            simpl. eassumption. simpl. eassumption.
            simpl. rewrite set_set_hd.
            eapply ChangeEndLocalTyp; [ | eauto | ]; [ | eauto ].
            {
              eapply LocalCtxValid_Function_Ctx.
              eapply HasTypeInstruction_FirstLocalValid; eauto.
              all: simpl; auto.
            }

            {
              simpl.
              rewrite get_set_hd in *.
              auto.
            }
            auto.
            
            eapply proj1.
            eapply Forall_app.
            eapply Forall_TypeValid_Function_Ctx.
            1:{ eapply HasTypeInstruction_InputTypesValid; eauto. }
            all: auto. }
        eassumption. } 

    7:{ eapply FrameTyp. reflexivity.
        simpl. eassumption. simpl. eassumption.
        simpl. rewrite set_set_hd. eassumption.
        {
          simpl.
          rewrite get_set_hd in *.
          auto.
        }
        auto.
        eapply proj1.
        eapply Forall_app.
        eapply Forall_TypeValid_Function_Ctx.
        1:{ eapply HasTypeInstruction_InputTypesValid; eauto. }
        all: auto. }

    reflexivity. reflexivity.
    eassumption. eassumption.
    eassumption. 
    eassumption.
    auto.
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
  - inv H0.
    destruct x1. destruct x2.
    simpl in *. inv H.
    eauto.
  - inv H0.
    assert (IH := IHl1 l').
    destruct a. destruct y.
    simpl in *.
    destruct (split (l1 ++ [x1])).
    destruct (split (l' ++ [x2])).
    simpl in *.
    inv H.
    destruct (split l1).
    destruct (split l').
    simpl in *.
    assert (IH' := IH (eq_refl _) H5).
    destructAll.
    split; [f_equal |]; eassumption.
Qed.

Lemma add_constraints_snoc : forall {kvs F kv},
    add_constraints F (kvs ++ [kv]) =
    add_constraint (add_constraints F kvs) kv.
Proof.
  induction kvs; intros; auto.
  rewrite <-app_comm_cons.
  simpl.
  rewrite IHkvs.
  auto.
Qed.

Lemma pretype_weak_no_effect_on_size : forall sz,
    subst.subst'_size
      (debruijn.subst'_of (debruijn.weak subst.SPretype)) sz
    =
    sz.
Proof.
  induction sz; auto.
  simpl.
  match goal with
  | [ H : _ = _, H' : _ = _ |- _ ] => rewrite H; rewrite H'
  end.
  auto.
Qed.

Lemma pretype_weak_no_effect_on_sizes : forall szs,
    subst.subst'_sizes
      (debruijn.subst'_of (debruijn.weak subst.SPretype)) szs
    =
    szs.
Proof.
  induction szs; auto.
  simpl.
  rewrite pretype_weak_no_effect_on_size.
  rewrite IHszs; auto.
Qed.

Lemma pretype_weak_no_effect_on_qual : forall q,
    subst.subst'_qual
      (debruijn.subst'_of (debruijn.weak subst.SPretype)) q
    =
    q.
Proof.
  destruct q; auto.
Qed.

Lemma loc_weak_no_effect_on_size : forall sz,
    subst.subst'_size
      (debruijn.subst'_of (debruijn.weak subst.SLoc)) sz
    =
    sz.
Proof.
  induction sz; auto.
  simpl.
  match goal with
  | [ H : _ = _, H' : _ = _ |- _ ] => rewrite H; rewrite H'
  end.
  auto.
Qed.

Lemma loc_weak_no_effect_on_sizes : forall szs,
    subst.subst'_sizes
      (debruijn.subst'_of (debruijn.weak subst.SLoc)) szs
    =
    szs.
Proof.
  induction szs; auto.
  simpl.
  rewrite loc_weak_no_effect_on_size.
  rewrite IHszs; auto.
Qed.

Lemma loc_weak_no_effect_on_qual : forall q,
    subst.subst'_qual
      (debruijn.subst'_of (debruijn.weak subst.SLoc)) q
    =
    q.
Proof.
  destruct q; auto.
Qed.

Lemma qual_weak_no_effect_on_size : forall sz,
    subst.subst'_size
      (debruijn.subst'_of (debruijn.weak subst.SQual)) sz
    =
    sz.
Proof.
  induction sz; auto.
  simpl.
  match goal with
  | [ H : _ = _, H' : _ = _ |- _ ] => rewrite H; rewrite H'
  end.
  auto.
Qed.

Lemma qual_weak_no_effect_on_sizes : forall szs,
    subst.subst'_sizes
      (debruijn.subst'_of (debruijn.weak subst.SQual)) szs
    =
    szs.
Proof.
  induction szs; auto.
  simpl.
  rewrite qual_weak_no_effect_on_size.
  rewrite IHszs; auto.
Qed.

Lemma pretype_weak_no_effect_on_size_field : forall F,
    size (subst_ext (weak SPretype) F) = size F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  induction size; simpl in *; auto.
  match goal with
  | [ X : _ * _ |- _ ] => destruct X
  end.
  repeat rewrite pretype_weak_no_effect_on_sizes.
  rewrite IHsize; auto.
Qed.

Lemma pretype_weak_no_effect_on_type_field : forall F,
    type (subst_ext (weak SPretype) F) = type F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  induction type; simpl in *; auto.
  repeat match goal with
         | [ X : _ * _ |- _ ] => destruct X
         end.
  rewrite pretype_weak_no_effect_on_size.
  rewrite pretype_weak_no_effect_on_qual.
  rewrite IHtype; auto.
Qed.

Lemma update_location_ctx_no_effect_on_size_field : forall F lctx,
    size (update_location_ctx lctx F) = size F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_location_ctx_no_effect_on_type_field : forall F lctx,
    type (update_location_ctx lctx F) = type F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_qual_ctx_no_effect_on_size_field : forall F qctx,
    size (update_qual_ctx qctx F) = size F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_qual_ctx_no_effect_on_type_field : forall F qctx,
    type (update_qual_ctx qctx F) = type F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_type_ctx_no_effect_on_size_field : forall F tctx,
    size (update_type_ctx tctx F) = size F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_type_ctx_no_effect_on_location_field : forall F tctx,
    location (update_type_ctx tctx F) = location F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma location_update_location_ctx : forall F lctx,
    location (update_location_ctx lctx F) = lctx.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma type_update_type_ctx : forall F tctx,
    type (update_type_ctx tctx F) = tctx.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma size_update_size_ctx : forall F szctx,
    size (update_size_ctx szctx F) = szctx.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma update_size_ctx_no_effect_on_type_field : forall F szctx,
    type (update_size_ctx szctx F) = type F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Definition KindVarValidForSize C kv :=
  match kv with
  | LOC => True
  | QUAL qs1 qs2 => True
  | SIZE ss1 ss2 => Forall (SizeValid (size C)) ss1 /\ Forall (SizeValid (size C)) ss2
  | TYPE s q hc => SizeValid (size C) s
  end.
Inductive KindVarsValidForSize : Function_Ctx -> list KindVar -> Prop :=
| KindVarsValidForSizeNil : forall C, KindVarsValidForSize C []
| KindVarsValidForSizeCons :
    forall C kv kvs,
      KindVarValidForSize C kv ->
      KindVarsValidForSize (add_constraint C kv) kvs ->
      KindVarsValidForSize C (kv :: kvs).

Lemma KindVarValid_imp_KindVarValidForSize : forall {kv C},
    KindVarValid C kv ->
    KindVarValidForSize C kv.
Proof.
  intros.
  destruct kv.
  all:
    match goal with
    | [ H : KindVarValid _ _ |- _ ] =>
      inversion H; subst; simpl in *; destructAll; auto
    end.
Qed.

Lemma KindVarsValid_imp_KindVarsValidForSize : forall {kv C},
    KindVarsValid C kv ->
    KindVarsValidForSize C kv.
Proof.
  induction kv; intros; simpl in *; constructor.
  all:
    match goal with
    | [ H : KindVarsValid _ (_ :: _) |- _ ] =>
      inversion H; subst; simpl in *; eauto
    end.
  apply KindVarValid_imp_KindVarValidForSize; auto.
Qed.  

Lemma KindVarsValidForSize_snoc : forall {cnstr C kv},
    KindVarsValidForSize C (cnstr ++ [kv]) <->
    (KindVarsValidForSize C cnstr /\
     KindVarValidForSize (add_constraints C cnstr) kv).
Proof.
  induction cnstr.
  - intros; simpl in *; auto.
    constructor; auto.
    -- intro H; inversion H; subst.
       split; auto.
       constructor.
    -- intros; destructAll.
       constructor; auto.
       constructor.
  - intros; simpl in *.
    split; intros.
    -- match goal with
       | [ H : KindVarsValidForSize _ (_ :: _) |- _ ] =>
         inversion H; subst; simpl in *
       end.
       rewrite IHcnstr in *.
       destructAll.
       split; auto.
       constructor; auto.
    -- destructAll.
       match goal with
       | [ H : KindVarsValidForSize _ (_ :: _) |- _ ] =>
         inversion H; subst; simpl in *
       end.
       constructor; auto.
       rewrite IHcnstr; auto.
Qed.

Lemma nth_error_map: forall {T U} l x i (f: T -> U),
    nth_error l i = Some x ->
    nth_error (map f l) i = Some (f x).
Proof.
  intros. generalize dependent i. induction l; intros; destruct i; try inversion H; simpl; auto.
Qed.

Lemma SizeValid_apply_weak : forall {sz szctx} l0 l1,
    SizeValid szctx sz ->
    SizeValid
      (map
         (fun '(ss1, ss2) =>
            (subst'_sizes (subst'_of (weak SSize)) ss1,
             subst'_sizes (subst'_of (weak SSize)) ss2))
         ((l0, l1) :: szctx))
      (subst'_size (subst'_of (weak SSize)) sz).
Proof.
  induction sz.
  - intros.
    simpl in *.
    unfold get_var'.
    simpl.
    unfold get_var'.
    unfold weaks'.
    simpl.
    unfold var.
    simpl.
    match goal with
    | [ H : SizeValid _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    -- match goal with
       | [ H : SizeVar _ = SizeConst _ |- _ ] =>
         inversion H
       end.
    -- match goal with
       | [ H : SizeVar _ = SizePlus _ _ |- _ ] =>
         inversion H
       end.
    -- match goal with
       | [ H : SizeVar _ = SizeVar _ |- _ ] =>
         inversion H; subst
       end.
       eapply SizeVarValid; eauto.
       simpl.
       apply nth_error_map; eauto.
  - intros.
    simpl in *.
    match goal with
    | [ H : SizeValid _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    1:{
      match goal with
      | [ H : SizePlus _ _ = SizeConst _ |- _ ] =>
        inversion H
      end.
    }
    2:{
      match goal with
      | [ H : SizePlus _ _ = SizeVar _ |- _ ] =>
        inversion H
      end.
    }
    match goal with
    | [ H : SizePlus _ _ = SizePlus _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    eapply SizePlusValid; eauto.
  - intros; simpl in *.
    eapply SizeConstValid; eauto.
Qed.    

Lemma SizeOfTypevar_valid : forall {cnstr v sz q c},
  KindVarsValidForSize empty_Function_Ctx cnstr ->
  nth_error (type (add_constraints empty_Function_Ctx cnstr)) v = Some (sz, q, c) ->
  SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz.
Proof.
  apply
    (rev_ind
       (fun cnstr =>
          forall v sz q c,
            KindVarsValidForSize empty_Function_Ctx cnstr ->
            nth_error (type (add_constraints empty_Function_Ctx cnstr)) v = Some (sz, q, c) ->
            SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz)).
  - intros; simpl in *.
    destruct v; simpl in *;
      match goal with | [ H : None = Some _ |- _ ] => inversion H end.
  - intros; simpl in *.
    rewrite add_constraints_snoc in *.
    match goal with
    | [ H : KindVarsValidForSize _ (_ ++ [_]) |- _ ] =>
      rewrite KindVarsValidForSize_snoc in H
    end.
    destructAll.
    match goal with
    | [ |- context[add_constraint _ ?KV] ] => destruct KV
    end.
    all: simpl in *.
    -- match goal with
       | [ H : context[map ?F ?L] |- _ ] =>
         let H' := fresh "H" in
         assert (H' : map F L = L);
         [ | rewrite H' in H; clear H' ]
       end.
       { rewrite <-map_id.
         apply map_ext_in.
         intros.
         repeat match goal with
                | [ X : _ * _ |- _ ] => destruct X
                end.
         rewrite loc_weak_no_effect_on_size.
         rewrite loc_weak_no_effect_on_qual; auto. }
       match goal with
       | [ |- context[map ?F ?L] ] =>
         let H' := fresh "H" in
         assert (H' : map F L = L);
         [ | rewrite H'; clear H' ]
       end.
       { rewrite <-map_id.
         apply map_ext_in.
         intros.
         repeat match goal with
                | [ X : _ * _ |- _ ] => destruct X
                end.
         repeat rewrite loc_weak_no_effect_on_sizes; auto. }
       rewrite update_location_ctx_no_effect_on_size_field.
       rewrite update_location_ctx_no_effect_on_type_field in *.
       eauto.
    -- match goal with
       | [ |- context[map ?F ?L] ] =>
         let H' := fresh "H" in
         assert (H' : map F L = L);
         [ | rewrite H'; clear H' ]
       end.
       { rewrite <-map_id.
         apply map_ext_in.
         intros.
         repeat match goal with
                | [ X : _ * _ |- _ ] => destruct X
                end.
         repeat rewrite qual_weak_no_effect_on_sizes; auto. }
       rewrite update_qual_ctx_no_effect_on_size_field.
       rewrite update_qual_ctx_no_effect_on_type_field in *.
       match goal with
       | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
         apply nth_error_map_inv in H
       end.
       destructAll.
       repeat match goal with
              | [ X : _ * _ |- _ ] => destruct X
              end.
       rewrite qual_weak_no_effect_on_size in *.
       match goal with
       | [ H : (_, _, _) = (_, _, _) |- _ ] =>
         inversion H; subst; simpl in *
       end.
       eauto.
    -- rewrite size_update_size_ctx.
       rewrite update_size_ctx_no_effect_on_type_field in *.
       match goal with
       | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
         apply nth_error_map_inv in H
       end.
       destructAll.
       repeat match goal with
              | [ X : _ * _ |- _ ] => destruct X
              end.
       match goal with
       | [ H : (_, _, _) = (_, _, _) |- _ ] =>
         inversion H; subst; simpl in *
       end.
       match goal with
       | [ |- SizeValid ((?F1 ?A, ?F2 ?B) :: (map ?F ?L)) _ ] =>
         let H := fresh "H" in
         assert (H : (F1 A, F2 B) :: (map F L) = (map F ((A, B) :: L)));
         [ | rewrite H; clear H ]
       end.
       { simpl; auto. }
       apply SizeValid_apply_weak; eauto.
    -- match goal with
       | [ H : context[map ?F ?L] |- _ ] =>
         let H' := fresh "H" in
         assert (H' : map F L = L);
         [ | rewrite H' in H; clear H' ]
       end.
       { rewrite <-map_id.
         apply map_ext_in.
         intros.
         repeat match goal with
                | [ X : _ * _ |- _ ] => destruct X
                end.
         rewrite pretype_weak_no_effect_on_size.
         rewrite pretype_weak_no_effect_on_qual; auto. }
       match goal with
       | [ |- context[map ?F ?L] ] =>
         let H' := fresh "H" in
         assert (H' : map F L = L);
         [ | rewrite H'; clear H' ]
       end.
       { rewrite <-map_id.
         apply map_ext_in.
         intros.
         repeat match goal with
                | [ X : _ * _ |- _ ] => destruct X
                end.
         repeat rewrite pretype_weak_no_effect_on_sizes; auto. }
       rewrite update_type_ctx_no_effect_on_size_field.
       rewrite type_update_type_ctx in *.
       match goal with
       | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
         destruct IDX; simpl in *; eauto
       end.
       match goal with
       | [ H : Some _ = Some _ |- _ ] =>
         inversion H; subst; auto
       end.
Qed.

Lemma SizeOfPretype_valid : forall {pt cnstr sz},
  KindVarsValidForSize empty_Function_Ctx cnstr ->
  sizeOfPretype (type (add_constraints empty_Function_Ctx cnstr)) pt = Some sz ->
  SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall cnstr sz,
            KindVarsValidForSize empty_Function_Ctx cnstr ->
            sizeOfPretype (type (add_constraints empty_Function_Ctx cnstr)) pt = Some sz ->
            SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz)
       (fun t =>
          forall cnstr sz,
            KindVarsValidForSize empty_Function_Ctx cnstr ->
            sizeOfType (type (add_constraints empty_Function_Ctx cnstr)) t = Some sz ->
            SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz)
       (fun ft => True)
       (fun ht => True)
       (fun atyp => True)).
  all: auto.
  all: intros; simpl in *.

  - destruct n; try destruct i; try destruct f; simpl in *.
    all:
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst
      end.
    all: econstructor; eauto.
  - match goal with
    | [ H : option_map _ ?OBJ = _ |- _ ] =>
      revert H;
      remember OBJ as obj; generalize (eq_sym Heqobj);
      case obj; intros
    end.
    all: simpl in *.
    2:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    repeat match goal with
           | [ X : _ * _ |- _ ] => destruct X
           end.
    match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    eapply SizeOfTypevar_valid; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
  - match goal with
    | [ H : fold_size (map _ ?L) = Some ?SZ, H' : context[?L] |- _ ] =>
      revert H; revert H'; revert SZ; induction L
    end.
    -- intros; simpl in *.
       match goal with
       | [ H : Some _ = Some _ |- _ ] =>
         inversion H; subst
       end.
       econstructor; eauto.
    -- intros; simpl in *.
       match goal with
       | [ H : Forall _ _ |- _ ] =>
         inversion H; subst; simpl in *
       end.
       match goal with
       | [ H : context[sizeOfType ?T ?A] |- _ ] =>
         revert H;
         remember (sizeOfType T A) as obj;
         generalize (eq_sym Heqobj); case obj; intros
       end.
       2:{
         match goal with | [ H : None = Some _ |- _ ] => inversion H end.
       }
       match goal with
       | [ H : context[fold_size (map ?F ?L)] |- _ ] =>
         revert H;
         remember (fold_size (map F L)) as obj2;
         generalize (eq_sym Heqobj2); case obj2; intros
       end.
       2:{
         match goal with | [ H : None = Some _ |- _ ] => inversion H end.
       }
       match goal with
       | [ H : Some _ = Some _ |- _ ] => inversion H; subst
       end.
       eapply SizePlusValid; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
  - match goal with
    | [ H : sizeOfType ((?A, ?B, ?C) :: _) _ = Some ?SZ,
        H' : forall _ _, _
        |- context[add_constraints _ ?KV] ] =>
      specialize (H' (KV ++ [TYPE A B C]) SZ)
    end.
    repeat match goal with
           | [ H : context[add_constraints _ (_ ++ [_])] |- _ ] =>
             rewrite add_constraints_snoc in H
           end.
    unfold add_constraint in *.
    rewrite pretype_weak_no_effect_on_size_field in *.
    rewrite pretype_weak_no_effect_on_type_field in *.
    rewrite update_type_ctx_no_effect_on_size_field in *.
    rewrite type_update_type_ctx in *.
    match goal with
    | [ H : _ -> _ -> _ |- _ ] => apply H; auto
    end.
    rewrite KindVarsValidForSize_snoc.
    split; auto.
    econstructor; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    econstructor; eauto.
Qed.        

Lemma SizeOfType_valid : forall {tau cnstr sz},
  KindVarsValidForSize empty_Function_Ctx cnstr ->
  sizeOfType (type (add_constraints empty_Function_Ctx cnstr)) tau = Some sz ->
  SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz.
Proof.
  intros.
  destruct tau.
  simpl in *.
  eapply SizeOfPretype_valid; eauto.
Qed.        

Lemma SizeOfType_valid_KindVarsValid : forall {tau cnstr sz},
  KindVarsValid empty_Function_Ctx cnstr ->
  sizeOfType (type (add_constraints empty_Function_Ctx cnstr)) tau = Some sz ->
  SizeValid (size (add_constraints empty_Function_Ctx cnstr)) sz.
Proof.
  intros.
  eapply SizeOfType_valid; eauto.
  apply KindVarsValid_imp_KindVarsValidForSize; auto.
Qed.

Lemma SizeOfType_empty_valid : forall {tau sz},
  sizeOfType [] tau = Some sz ->
  SizeValid [] sz.
Proof.
  intros.
  specialize (SizeOfType_valid_KindVarsValid (tau:=tau) (cnstr:=[]) (sz:=sz)).
  intro Himp.
  assert (Hassump1 : KindVarsValid empty_Function_Ctx []) by constructor.
  simpl in *; eauto.
Qed.

Lemma SizeOfStruct_Typecheck_Actual : forall vs S F tauszs taus szs,
    HasHeapType S F (Struct vs) (StructType tauszs) ->
    split tauszs = (taus, szs) ->
    (size F) = [] ->
    type F = [] ->
    (term.size (Struct vs) <= fold_left (fun (acc : nat) (sz : Size) =>
                                           match size_to_nat sz with
                                           | Some n => acc + n
                                           | None => acc
                                           end) szs 0)%nat.
Proof.
  induction vs; intros.
  - simpl; lia.
  - inv H.
    inv H9. inv H2.
    destructAll.
    assert (H_ := H3).
    rewrite H0 in H3. inv H3. inv H6. inv H2. symmetry in H0.
    eapply cons_split in H0.
    destruct H0 as [tauszs' H20].
    symmetry in H20.
    eapply SplitStoreTypings_cons in H5.
    destruct H5 as [S' H21].
    inv H.
    assert (IH := IHvs S' F tauszs' l'' l').
    assert (HasHeapType S' F (Struct vs) (StructType tauszs')).
    1 : { eapply StructHT.
          + exact H21.
          + eauto.
          + symmetry in H20. exact H20.
          + split. eassumption. eassumption.
    }
    assert (IH' := IH H H20 H1).
    simpl.
    (* destruct H3 as [sztau [H30 [H31 H32]]]. *)
    rewrite H1 in H3.
    simpl in IH'.
    eapply size_valid_empty_implies_to_nat in H3.
    destruct H3 as [n H31].
    rewrite H31.
    specialize (IH' H4).
    eapply (fold_leq_holds_under_base_accumulator _ _ _ _ IH').
    simpl in *.
    destructAll.
    rewrite H4 in H0.
    specialize (SizeOfType_empty_valid H0).
    intro H50.
    apply size_valid_empty_implies_to_nat in H50.
    destructAll.
    rewrite H1 in H2.
    rewrite H1 in H3.
    match goal with
    | [ H : size_to_nat ?SZ1 = Some _,
        H' : size_to_nat ?SZ2 = Some _,
        H'' : SizeLeq [] ?SZ1 ?SZ2 = Some true |- _ ] =>
      specialize (SizeLeq_Const _ _ _ _ H H' H'')
    end.
    intros.
    match goal with
    | [ H : HasTypeValue _ _ _ _,
        H' : sizeOfType [] _ = Some ?SZ,
        H'' : type _ = [],
        H''' : size _ = [],
        H'''' : size_to_nat ?SZ = Some _ |- _ ] =>
      rewrite <-H'' in H';
      assert (H50 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H H' H''' H'''')
    end.
    lia.
Qed.

Lemma struct_typing_implies_size : forall vs S tauszs taus szs,
    HasHeapType S empty_Function_Ctx (Struct vs) (StructType tauszs) ->
    split tauszs = (taus, szs) ->
    Forall2 (fun v sz => exists n,
                 size_to_nat sz= Some n /\ (size_val v <= n))
            vs szs.
Proof.
  induction vs; intros.
  - inv H.
    inv H4. destructAll.
    inv H1.
    rewrite H0 in H7.
    inv H7.
    eauto.
  - inv H.
    inv H4. destructAll.
    inv H1. inv H. destructAll.
    destruct (cons_split _ _ _ _ _ _ _ H7) as [tauszs' H30].
    rewrite H0 in H7.
    inv H7.
    eapply SplitStoreTypings_cons in H3.
    destruct H3 as [S' H3].
    assert (H40 := StructHT _ _ _ _ _ _ _ H3 H9 H30 (conj H8 H10)).
    symmetry in H30.
    assert (IH := IHvs _ _ _ _ H40 H30).
    eapply Forall2_cons; try exact IH.
    simpl in *.
    specialize (SizeOfType_empty_valid H).
    intro H100.
    eapply size_valid_empty_implies_to_nat in H100.
    destruct H100 as [n1 H60].
    eapply size_valid_empty_implies_to_nat in H4.
    destruct H4 as [n2 H61].
    match goal with
    | [ H : size_to_nat ?SZ1 = Some _,
        H' : size_to_nat ?SZ2 = Some _,
        H'' : SizeLeq [] ?SZ1 ?SZ2 = Some true |- _ ] =>
      specialize (SizeLeq_Const _ _ _ _ H H' H'')
    end.
    intro H62.
    exists n2.
    split; try exact H61.
    assert (H70 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H5 H (eq_refl _) H60).
    lia.
Qed.

Lemma update_ret_ctx_size F st :
  size (update_ret_ctx st F) = size F.
Proof.
  destruct F. reflexivity.
Qed.

Lemma related_subst_conds_under_knd : forall {f1 f2 kndspec obj1 obj2 knd},
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    related_subst_conds
      (debruijn.under' knd f1)
      (debruijn.under' knd f2)
      kndspec obj1 obj2.
Proof.
  intros.
  unfold related_subst_conds in *.
  destructAll.
  do 2 eexists; split.
  all: eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma related_subst_conds_under_kindvars : forall {f1 f2 kndspec obj1 obj2 kvs},
    related_subst_conds f1 f2 kndspec obj1 obj2 ->
    related_subst_conds
      (subst.under_kindvars' kvs f1)
      (subst.under_kindvars' kvs f2)
      kndspec obj1 obj2.
Proof.
  intros.
  unfold related_subst_conds in *.
  destructAll.
  do 2 eexists; split.
  all: eapply debruijn_subst_ext_under_kindvars; eauto.
Qed.

Lemma minusone_noneq : forall {b a},
    0 < a ->
    a <> Datatypes.S b -> a - 1 <> b.
Proof.
  induction b; induction a; intros.
  - match goal with | [ H : 0 < 0 |- _ ] => inversion H end.
  - destruct a.
    -- intro.
       match goal with | [ H : 1 <> 1 |- _ ] => apply H end.
       auto.
    -- intro.
       simpl in *.
       match goal with
       | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
       end.
  - match goal with | [ H : 0 < 0 |- _ ] => inversion H end.
  - match goal with
    | [ H : Datatypes.S ?A <> Datatypes.S ?B |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A <> B)
    end.
    { intro; subst.
      match goal with | [ H : ?A <> ?A |- _ ] => apply H end.
      auto. }
    simpl.
    rewrite Nat.sub_0_r; auto.
Qed.

Lemma minusone_lt : forall {a b},
    0 < a ->
    a <? Datatypes.S b = (a - 1 <? b).
Proof.
  induction a; induction b; intros.
  all: try match goal with | [ H : 0 < 0 |- _ ] => inversion H end.
  - unfold Nat.ltb.
    simpl; auto.
  - unfold Nat.ltb.
    simpl.
    rewrite Nat.sub_0_r; auto.
Qed.

Lemma subst_subst_kindvars_does_not_change_kind : forall {l f},
    map subst.kind_of_kindvar (subst.subst'_kindvars f l)
    =
    map subst.kind_of_kindvar l.
Proof.
  induction l; simpl; auto.
  intros.
  destruct a; simpl.
  all: rewrite IHl; auto.
Qed.

Lemma subst_weak_comp' : forall {knd obj},
    (debruijn.subst'_of (debruijn.ext knd obj debruijn.id))
      ∘'
      (debruijn.subst'_of (debruijn.weak knd))
    =
    var'.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x.
  all: simpl.
  all: unfold get_var'.
  all: unfold under_ks'.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false; auto
    end.
  all: unfold zero.
  all: rewrite Nat.add_0_r.
  all:
    try match goal with
        | [ |- false = _ ] =>
          apply eq_sym; rewrite Nat.ltb_ge; lia
        end.
  all: simpl.
  all: unfold ext.
  all: destruct knd; simpl.
  all:
    try match goal with
        | [ |- context[dec_eq ?A ?B] ] =>
          destruct (dec_eq A B)
        end.
  all:
    try match goal with
        | [ H : _ = 0 |- _ ] => lia
        end.
  all: simpl.
  all: unfold get_var'.
  all: unfold weaks'.
  all: unfold var'.
  all: unfold var.
  all: simpl.
  all: unfold plus.
  all: unfold zero.
  all:
    match goal with
    | [ |- ?F ?A = ?F ?B ] => replace A with B at 1 by lia; auto
    end.
Qed.

Ltac solve_debruijn_subst_weak S :=
  intros;
  repeat match goal with
         | [ |- context[S ?F ?HT] ] =>
           replace (S F HT) with (subst_ext' F HT) by auto
         end;
  rewrite subst_ext'_assoc;
  rewrite subst_weak_comp';
  rewrite subst_ext'_var_e; auto.

Lemma HeapTypeValid_debruijn_subst_weak : forall {ht kndspec obj},
    subst.subst'_heaptype
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_heaptype
         (debruijn.subst'_of (debruijn.weak kndspec)) ht)
    =
    ht.
Proof.
  solve_debruijn_subst_weak subst'_heaptype.
Qed.

Lemma HeapTypeValid_debruijn_subst_SLoc_weak : forall {obj ht},
    subst.subst'_heaptype
      (debruijn.subst'_of
         (debruijn.ext subst.SLoc obj debruijn.id))
      (subst.subst'_heaptype
         (debruijn.subst'_of (debruijn.weak subst.SLoc)) ht)
    =
    ht.
Proof.
  intros; apply HeapTypeValid_debruijn_subst_weak.
Qed.

Lemma pretype_debruijn_subst_weak : forall {pt kndspec obj},
    subst.subst'_pretype
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_pretype
         (debruijn.subst'_of (debruijn.weak kndspec)) pt)
    =
    pt.
Proof.
  solve_debruijn_subst_weak subst'_pretype.
Qed.  

Lemma type_debruijn_subst_weak : forall {t kndspec obj},
    subst.subst'_type
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_type
         (debruijn.subst'_of (debruijn.weak kndspec)) t)
    =
    t.
Proof.
  solve_debruijn_subst_weak subst'_type.
Qed.

Lemma types_debruijn_subst_weak : forall {ts kndspec obj},
    subst.subst'_types
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_types
         (debruijn.subst'_of (debruijn.weak kndspec)) ts)
    =
    ts.
Proof.
  solve_debruijn_subst_weak subst'_types.
Qed.

Lemma size_debruijn_subst_weak : forall {s kndspec obj},
    subst.subst'_size
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_size
         (debruijn.subst'_of (debruijn.weak kndspec)) s)
    =
    s.
Proof.
  solve_debruijn_subst_weak subst'_size.
Qed.

Lemma sizes_debruijn_subst_weak : forall {szs kndspec obj},
    subst.subst'_sizes
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_sizes
         (debruijn.subst'_of (debruijn.weak kndspec)) szs)
    =
    szs.
Proof.
  solve_debruijn_subst_weak subst'_sizes.
Qed.

Lemma qual_debruijn_subst_weak : forall {q kndspec obj},
    subst.subst'_qual
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_qual
         (debruijn.subst'_of (debruijn.weak kndspec)) q)
    =
    q.
Proof.
  solve_debruijn_subst_weak subst'_qual.
Qed.

Lemma quals_debruijn_subst_weak : forall {qs kndspec obj},
    subst.subst'_quals
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst.subst'_quals
         (debruijn.subst'_of (debruijn.weak kndspec)) qs)
    =
    qs.
Proof.
  solve_debruijn_subst_weak subst'_quals.
Qed.

Lemma local_ctx_debruijn_subst_weak : forall {L kndspec obj},
    subst'_local_ctx
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst'_local_ctx
         (debruijn.subst'_of (debruijn.weak kndspec)) L)
    =
    L.
Proof.
  solve_debruijn_subst_weak subst'_local_ctx.
Qed.

Lemma pmap_pmap : forall {A B C} {f : A -> B} {g : B -> C} {l},
    pmap g (pmap f l) = pmap (fun x => g (f x)) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma pmap_id : forall {A} (l : plist A),
    l = pmap (fun x => x) l.
Proof.
  induction l; intros; simpl in *; auto.
  rewrite IHl at 1; auto.
Qed.

Lemma pmap_ext : forall {A B} {f1 : A -> B} {f2 l},
    (forall x, f1 x = f2 x) ->
    pmap f1 l = pmap f2 l.
Proof.
  induction l; intros; simpl in *; auto.
  - rewrite H; auto.
  - rewrite H.
    rewrite IHl; auto.
Qed.

Lemma Forall2_eq : forall {A} {l1 : list A} {l2},
    Forall2 (fun a b => a = b) l1 l2 ->
    l1 = l2.
Proof.
  induction l1; intros; simpl in *.
  all:
    match goal with
    | [ H : Forall2 _ _ _ |- _ ] => inversion H; subst; simpl in *
    end.
  - auto.
  - erewrite IHl1; eauto.
Qed.

Lemma function_ctx_debruijn_subst_weak : forall {F kndspec obj},
    subst'_function_ctx
      (debruijn.subst'_of
         (debruijn.ext kndspec obj debruijn.id))
      (subst'_function_ctx
         (debruijn.subst'_of (debruijn.weak kndspec)) F)
    =
    F.
Proof.
  solve_debruijn_subst_weak subst'_function_ctx.
Qed.

Lemma weak_loc_no_effect_on_qual : forall {f ks q},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    subst.subst'_qual f q = q.
Proof.
  destruct q; simpl; auto.
  unfold get_var'.
  intros.
  erewrite weak_no_effect_on_other_vars; eauto.
  solve_ineqs.
Qed.

Lemma weak_loc_no_effect_on_quals : forall {f ks qs},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    subst.subst'_quals f qs = qs.
Proof.
  induction qs; simpl in *; auto.
  intros.
  erewrite weak_loc_no_effect_on_qual; eauto.
  erewrite IHqs; eauto.
Qed.

Lemma weak_loc_no_effect_on_size : forall {sz f ks},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    subst.subst'_size f sz = sz.
Proof.
  induction sz.
  - intros.
    simpl in *.
    unfold get_var'.
    erewrite weak_no_effect_on_other_vars; eauto.
    solve_ineqs.
  - intros; simpl.
    erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
  - intros; simpl; auto.
Qed.

Lemma weak_loc_no_effect_on_sizes : forall {szs f ks},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    subst.subst'_sizes f szs = szs.
Proof.
  induction szs; intros; simpl in *; auto.
  erewrite weak_loc_no_effect_on_size; eauto.
  erewrite IHszs; eauto.
Qed.

Lemma weak_loc_no_effect_on_valid_locs : forall {F f ks l},
    debruijn_weaks_conds f ks (sing SLoc 1) ->
    ks SLoc >= location F ->
    LocValid (location F) l ->
    subst'_loc f l = l.
Proof.
  intros.
  match goal with
  | [ X : Loc |- _ ] => destruct X; simpl in *; auto
  end.
  unfold get_var'.
  unfold debruijn_weaks_conds in *.
  match goal with
  | [ H : LocValid _ _ |- _ ] => inversion H; subst; simpl in *
  end.
  1:{
    match goal with
    | [ H : LocV _ = LocP _ _ |- _ ] => inversion H
    end.
  }
  destructAll.
  match goal with
  | [ H : context[_ < _] |- _ ] => erewrite H; eauto
  end.
  match goal with
  | [ H : LocV _ = LocV _ |- _ ] => inversion H; subst
  end.
  eapply Nat.lt_le_trans; eauto.
Qed.

Lemma location_add_constraint : forall {kv F},
    location (add_constraint F kv) =
    sing (kind_of_kindvar kv) 1 SLoc + location F.
Proof.
  destruct kv; simpl in *; intro F;
    destruct F; subst; simpl in *; auto.
  rewrite Nat.add_1_r; auto.
Qed.

Lemma location_add_constraints : forall {kvs F},
    location (add_constraints F kvs) =
    fold_left
      (fun lctx kv =>
         sing (kind_of_kindvar kv) 1 SLoc + lctx)
      kvs
      (location F).
Proof.
  induction kvs; intros; simpl in *; auto.
  rewrite IHkvs.
  rewrite location_add_constraint.
  auto.
Qed.

Lemma fold_right_plus_comm : forall {kvs ks'' ks knd},
    fold_right
      (fun kv ks' => plus (sing (kind_of_kindvar kv) 1) ks')
      (plus ks'' ks) kvs knd
    =
    ks'' knd
    +
    fold_right
      (fun kv ks' => plus (sing (kind_of_kindvar kv) 1) ks')
      ks kvs knd.
Proof.
  induction kvs; intros; simpl in *; auto.
  unfold plus at 1.
  rewrite IHkvs.
  unfold plus.
  repeat rewrite Nat.add_assoc.
  match goal with
  | [ |- ?A + _ = ?B + _ ] =>
    let H := fresh "H" in
    assert (H : A = B); [ | rewrite H; auto ]
  end.
  apply Nat.add_comm.
Qed.

Lemma location_add_constraints_ineq : forall {kvs F ks},
    ks SLoc >= location F ->
    fold_right
      (fun kv ks' => plus (sing (kind_of_kindvar kv) 1) ks')
      ks kvs SLoc
    >=
    location (add_constraints F kvs).
Proof.
  intros.
  rewrite location_add_constraints.
  revert F ks H.
  induction kvs; intros; simpl in *; auto.
  unfold plus.
  specialize (IHkvs (add_constraint F a) (plus (sing (kind_of_kindvar a) 1) ks)).
  rewrite location_add_constraint in IHkvs.
  rewrite fold_right_plus_comm in IHkvs.
  apply IHkvs.
  unfold plus.
  apply Nat.add_le_mono_l; auto.
Qed.

Lemma weak_loc_no_effect_on_valid_kindvar : forall {kv F f ks},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    ks subst.SLoc >= location F ->
    KindVarValid F kv ->
    subst'_kindvar f kv = kv.
Proof.
  intros.
  destruct kv; simpl in *; auto.
  - do 2 ltac:(erewrite weak_loc_no_effect_on_quals; eauto).
  - do 2 ltac:(erewrite weak_loc_no_effect_on_sizes; eauto).
  - erewrite weak_loc_no_effect_on_size; eauto.
    erewrite weak_loc_no_effect_on_qual; eauto.
Qed.

Lemma weak_loc_no_effect_on_valid_kindvars : forall {kvs F f ks},
    debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
    ks subst.SLoc >= location F ->
    KindVarsValid F kvs ->
    subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; intros; simpl in *; auto.
  match goal with
  | [ H : KindVarsValid _ (_ :: _) |- _ ] =>
    inversion H; subst; simpl in *
  end.
  erewrite weak_loc_no_effect_on_valid_kindvar; eauto.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all:
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => erewrite H; auto
    end.
  all: unfold under_kindvar'.
  all: try eapply debruijn_weaks_conds_under_knd.
  all:
    try match goal with
        | [ |- debruijn_weaks_conds _ _ _ ] => eauto
        | [ |- KindVarsValid _ _ ] => eauto
        end.
  all: unfold plus.
  all: rewrite location_add_constraint.
  all: apply Nat.add_le_mono_l; auto.
Qed.

Lemma weak_loc_no_effect_on_valid_typs :
  (forall F t,
      TypeValid F t ->
      forall f ks,
        debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
        ks subst.SLoc >= location F ->
        subst.subst'_type f t = t) /\
  (forall F ht,
      HeapTypeValid F ht ->
      forall f ks,
        debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
        ks subst.SLoc >= location F ->
        subst.subst'_heaptype f ht = ht) /\
  (forall F atyp,
      ArrowTypeValid F atyp ->
      forall f ks,
        debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
        ks subst.SLoc >= location F ->
        subst.subst'_arrowtype f atyp = atyp) /\
  (forall F ft,
      FunTypeValid F ft ->
      forall f ks,
        debruijn_weaks_conds f ks (debruijn.sing subst.SLoc 1) ->
        ks subst.SLoc >= location F ->
        subst.subst'_funtype f ft = ft).
Proof.
  Ltac solve_map_obligation :=
    rewrite <-map_id;
    apply map_ext_in;
    intros;
    rewrite Forall_forall in *;
    match goal with
    | [ H : forall _, _ |- _ ] => eapply H; eauto
    end.
  Ltac gen_and_solve_map_obligation :=
    match goal with
    | [ |- context[map ?F ?L] ] =>
      let H := fresh "H" in
      assert (H : map F L = L);
      [ try match goal with
            | [ H : Forall _ _, H' : Forall _ L |- _ ] =>
              clear H
            end;
        solve_map_obligation | rewrite H; auto ]
    end.

  eapply TypesValid_ind'.
  all: intros; simpl in *.
  - erewrite weak_loc_no_effect_on_qual; eauto.
  - unfold get_var'.
    erewrite weak_loc_no_effect_on_qual; eauto.
    erewrite weak_no_effect_on_other_vars; eauto.
    solve_ineqs.
  - do 2 ltac:(erewrite (weak_loc_no_effect_on_qual (f:=f)); eauto).
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite update_type_ctx_no_effect_on_location_field; auto.
  - erewrite weak_loc_no_effect_on_qual; eauto.
  - erewrite weak_loc_no_effect_on_qual; eauto.
    gen_and_solve_map_obligation.
  - erewrite weak_loc_no_effect_on_qual; eauto.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite weak_loc_no_effect_on_qual; eauto.
    erewrite weak_loc_no_effect_on_valid_locs; eauto.
  - erewrite weak_loc_no_effect_on_valid_locs; eauto.
    erewrite weak_loc_no_effect_on_qual; eauto.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite weak_loc_no_effect_on_valid_locs; eauto.
    erewrite weak_loc_no_effect_on_qual; eauto.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite (weak_loc_no_effect_on_qual (f:=f)); eauto.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite location_update_location_ctx.
       rewrite Nat.add_1_r.
       apply Peano.le_n_S; auto.
  - erewrite weak_loc_no_effect_on_valid_locs; eauto.
    erewrite weak_loc_no_effect_on_qual; eauto.
  - gen_and_solve_map_obligation.
  - match goal with
    | [ |- context[map ?F ?L] ] =>
      let H := fresh "H" in
      assert (H : map F L = L); [ | rewrite H; auto ]
    end.
    rewrite <-map_id.
    apply map_ext_in.
    intros.
    rewrite Forall_forall in *.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    erewrite weak_loc_no_effect_on_size; eauto.
    match goal with
    | [ H : forall _, List.In _ _ -> _, H' : List.In _ _ |- _ ] =>
      specialize (H _ H')
    end.
    destructAll; simpl in *.
    match goal with
    | [ H : context[_ -> subst'_type _ _ = _] |- _ ] =>
      erewrite H; eauto
    end.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite weak_loc_no_effect_on_size; eauto.
    erewrite weak_loc_no_effect_on_qual; eauto.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite update_type_ctx_no_effect_on_location_field; auto.
  - do 2 gen_and_solve_map_obligation.
  - erewrite weak_loc_no_effect_on_valid_kindvars; eauto.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_kindvars; eauto.
    -- apply location_add_constraints_ineq; auto.
Qed.

Lemma weak_loc_no_effect_on_valid_typ_empty_Function_Ctx : forall {F pt q},
    TypeValid F (QualT pt q) ->
    location F = 0 ->
    subst.subst'_pretype (under' subst.SPretype (subst'_of (weak subst.SLoc))) pt = pt.
Proof.
  intros.
  assert (H' : subst.subst'_type (under' subst.SPretype (subst'_of (weak subst.SLoc))) (QualT pt q) = (QualT pt q)).
  2:{
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] =>
      inversion H
    end.
    repeat match goal with
           | [ H : ?A = _ |- context[?A] ] => rewrite H; auto
           end.
  }
  specialize weak_loc_no_effect_on_valid_typs.
  let H' := fresh "H" in
  intro H'; destruct H' as [H']; eapply H'; eauto.
  - eapply debruijn_weaks_conds_under_knd.
    apply single_weak_debruijn_weak_conds.
  - unfold plus.
    simpl.
    unfold zero.
    match goal with
    | [ H : ?A = _ |- _ >= ?A ] => rewrite H
    end.
    auto.
Qed.

Ltac handle_qual_subst :=
  erewrite qual_debruijn_subst_ext;
    [ | | eauto ];
    solve_ineqs.
Ltac handle_quals_subst :=
  erewrite quals_debruijn_subst_ext;
    [ | | eauto ];
    solve_ineqs.
Ltac handle_size_subst :=
  erewrite size_debruijn_subst_ext;
    [ | | eauto ];
    solve_ineqs.
Ltac handle_sizes_subst :=
  erewrite sizes_debruijn_subst_ext;
    [ | | eauto ];
    solve_ineqs.

Lemma subst_loc_no_effect_on_valid_kindvar : forall {kv F f ks l},
    debruijn_subst_ext_conds f ks subst.SLoc l ->
    ks subst.SLoc >= location F ->
    KindVarValid F kv ->
    subst'_kindvar f kv = kv.
Proof.
  intros.
  destruct kv; simpl in *; auto.
  - do 2 handle_quals_subst; eauto.
  - do 2 handle_sizes_subst; eauto.
  - handle_size_subst.
    handle_qual_subst; auto.
Qed.

Lemma subst_loc_no_effect_on_valid_kindvars : forall {kvs F f ks l},
    debruijn_subst_ext_conds f ks subst.SLoc l ->
    ks subst.SLoc >= location F ->
    KindVarsValid F kvs ->
    subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; intros; simpl in *; auto.
  match goal with
  | [ H : KindVarsValid _ (_ :: _) |- _ ] =>
    inversion H; subst; simpl in *
  end.
  erewrite subst_loc_no_effect_on_valid_kindvar; eauto.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all:
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => erewrite H; auto
    end.
  all: unfold under_kindvar'.
  all: try eapply debruijn_subst_ext_under_knd.
  all:
    try match goal with
        | [ |- debruijn_subst_ext_conds _ _ _ _ ] => eauto
        | [ |- KindVarsValid _ _ ] => eauto
        end.
  all: unfold plus.
  all: rewrite location_add_constraint.
  all: apply Nat.add_le_mono_l; auto.
Qed.

Lemma subst_no_effect_on_other_vars : forall {f ks knd knd' ks' v obj},
    debruijn_subst_ext_conds f ks knd obj ->
    knd <> knd' ->
    f knd' v ks' =
    subst.VarKind knd' (ks' knd' + v).
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ H : context[_ <> _ -> _] |- _ ] => rewrite H; auto
  end.
Qed.

Lemma subst_loc_no_effect_on_valid_locs : forall {F f ks l' l},
    debruijn_subst_ext_conds f ks SLoc l' ->
    ks SLoc >= location F ->
    LocValid (location F) l ->
    subst'_loc f l = l.
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ |- _ = ?L ] => destruct L; simpl in *; auto
  end.
  unfold get_var'.
  match goal with
  | [ H : ?A >= location _, H' : LocValid _ (LocV ?V) |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : V < A)
  end.
  { match goal with
    | [ H : LocValid _ _ |- _ ] => inversion H; subst; simpl in *
    end.
    - match goal with
      | [ H : LocV _ = LocP _ _ |- _ ] => inversion H
      end.
    - match goal with
      | [ H : LocV _ = LocV _ |- _ ] => inversion H; subst
      end.
      unfold Peano.ge in *.
      eapply Nat.lt_le_trans; eauto. }

  match goal with
  | [ H : context[_ <> _ SLoc -> _] |- _ ] => rewrite H
  end.
  - unfold shift_down_after.
    unfold zero.
    repeat rewrite Nat.add_0_l.
    rewrite <-Nat.ltb_lt in *.
    match goal with
    | [ H : _ = true |- _ ] => rewrite H; auto
    end.
  - apply Nat.lt_neq; auto.
Qed.

Lemma subst_loc_no_effect_on_valid_typs :
  (forall F t,
      TypeValid F t ->
      forall f ks l,
        debruijn_subst_ext_conds f ks subst.SLoc l ->
        ks subst.SLoc >= location F ->
        subst.subst'_type f t = t) /\
  (forall F ht,
      HeapTypeValid F ht ->
      forall f ks l,
        debruijn_subst_ext_conds f ks subst.SLoc l ->
        ks subst.SLoc >= location F ->
        subst.subst'_heaptype f ht = ht) /\
  (forall F atyp,
      ArrowTypeValid F atyp ->
      forall f ks l,
        debruijn_subst_ext_conds f ks subst.SLoc l ->
        ks subst.SLoc >= location F ->
        subst.subst'_arrowtype f atyp = atyp) /\
  (forall F ft,
      FunTypeValid F ft ->
      forall f ks l,
        debruijn_subst_ext_conds f ks subst.SLoc l ->
        ks subst.SLoc >= location F ->
        subst.subst'_funtype f ft = ft).
Proof.
  Ltac handle_specific_quals f :=
    repeat match goal with
           | [ |- context[subst'_qual f ?Q] ] =>
             replace (subst'_qual f Q) with Q
               by ltac:(handle_qual_subst; auto)
           end.

  eapply TypesValid_ind'.
  all: intros; simpl in *.
  - handle_qual_subst; auto.
  - unfold get_var'.
    handle_qual_subst; auto.
    erewrite subst_no_effect_on_other_vars; eauto.
    solve_ineqs.
  - handle_specific_quals f.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite update_type_ctx_no_effect_on_location_field; auto.
  - handle_qual_subst; auto.
  - handle_qual_subst; auto.
    gen_and_solve_map_obligation.
  - handle_qual_subst; auto.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - handle_qual_subst; auto.
    erewrite subst_loc_no_effect_on_valid_locs; eauto.
  - erewrite subst_loc_no_effect_on_valid_locs; eauto.
    handle_qual_subst.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite subst_loc_no_effect_on_valid_locs; eauto.
    handle_qual_subst.
    match goal with
    | [ H : forall _, _ |- _ ] => erewrite H; eauto
    end.
  - handle_specific_quals f.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite location_update_location_ctx.
       rewrite Nat.add_1_r.
       apply Peano.le_n_S; auto.
  - erewrite subst_loc_no_effect_on_valid_locs; eauto.
    handle_qual_subst; auto.
  - gen_and_solve_map_obligation.
  - match goal with
    | [ |- context[map ?F ?L] ] =>
      let H := fresh "H" in
      assert (H : map F L = L); [ | rewrite H; auto ]
    end.
    rewrite <-map_id.
    apply map_ext_in.
    intros.
    rewrite Forall_forall in *.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    handle_size_subst.
    match goal with
    | [ H : forall _, List.In _ _ -> _, H' : List.In _ _ |- _ ] =>
      specialize (H _ H')
    end.
    destructAll; simpl in *.
    match goal with
    | [ H : context[_ -> subst'_type _ _ = _] |- _ ] =>
      erewrite H; eauto
    end.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - handle_size_subst.
    handle_qual_subst.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- unfold plus.
       simpl.
       rewrite update_type_ctx_no_effect_on_location_field; auto.
  - do 2 gen_and_solve_map_obligation.
  - erewrite subst_loc_no_effect_on_valid_kindvars; eauto.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    -- eapply debruijn_subst_ext_under_kindvars; eauto.
    -- apply location_add_constraints_ineq; auto.
Qed.

Lemma subst_loc_no_effect_on_valid_typ_empty_Function_Ctx : forall {F tau loc},
    TypeValid F tau ->
    location F = 0 ->
    subst.subst'_type
      (subst'_of (ext subst.SLoc loc id))
      tau
    =
    tau.
Proof.
  intros.
  specialize subst_loc_no_effect_on_valid_typs.
  let H' := fresh "H" in
  intro H'; destruct H' as [H']; eapply H'; eauto.
  apply simpl_debruijn_subst_ext_conds.
  match goal with
  | [ H : ?A = 0 |- _ >= ?A ] => rewrite H
  end.
  unfold zero; auto.
Qed.

Lemma subst_index_sizes : forall {idx} {l : list Size},
    subst.subst_index idx l =
    map (subst.subst_index idx) l.
Proof.
  induction l; simpl; auto.
  - destruct idx; simpl; auto.
  - destruct idx; simpl in *.
    all: rewrite IHl; auto.
Qed.

Lemma subst_in_size_eq_map : forall {idxs szs},
    subst_in_size idxs szs =
    map (subst.subst_indices idxs) szs.
Proof.
  induction idxs; simpl; auto.
  - intros; rewrite map_id; auto.
  - intros.
    rewrite <-map_map.
    rewrite IHidxs.
    rewrite subst_index_sizes; auto.
Qed.

Lemma under_kindvars_id : forall {kvs},
    subst.under_kindvars' kvs (debruijn.subst'_of debruijn.id) = (debruijn.subst'_of debruijn.id).
Proof.
  induction kvs; simpl; auto.
  rewrite IHkvs.
  unfold debruijn.Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct a; destruct x.
  all: simpl.
  all: unfold subst.under_kindvar'.
  all: simpl.
  all: unfold debruijn.under'.
  all: unfold debruijn.under_ks'.
  all: simpl.
  all: unfold debruijn.get_var'.
  all: unfold debruijn.weaks'.
  all: unfold debruijn.var.
  all: simpl.
  all: unfold debruijn.plus.
  all: unfold debruijn.sing.
  all: simpl.
  all: unfold debruijn.zero.
  all: repeat rewrite Nat.add_0_r.
  all: try rewrite Nat.add_0_l.
  all: try rewrite Nat.sub_0_r.
  all: auto.
  all: rewrite Nat.add_comm.
  all: unfold debruijn.var'.
  all: unfold debruijn.var.
  all: simpl.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
      generalize (eq_sym Heqb); case b; intros; auto
    end.
  all: rewrite Nat.ltb_ge in *.
  all: rewrite Nat.add_comm.
  all: rewrite <-Nat.add_1_r.
  all: rewrite <-Nat.add_assoc.
  all: rewrite Nat.sub_add; auto.
Qed.

Lemma kind_of_kindvar_surjective : forall knd,
    exists kv,
      subst.kind_of_kindvar kv = knd.
Proof.
  destruct knd.
  - exists LOC; simpl; auto.
  - exists (QUAL [] []); simpl; auto.
  - exists (SIZE [] []); simpl; auto.
  - exists (TYPE (SizeConst 0) (QualConst Unrestricted) Heapable); simpl; auto.
Qed.

Lemma under_knd_id : forall {knd},
    debruijn.under' knd (debruijn.subst'_of debruijn.id) = (debruijn.subst'_of debruijn.id).
Proof.
  intros knd.
  specialize (kind_of_kindvar_surjective knd).
  intros H.
  destruct H as [kv].
  rewrite <-H.
  replace (debruijn.under' (subst.kind_of_kindvar kv) (debruijn.subst'_of debruijn.id)) with (subst.under_kindvars' [kv] (debruijn.subst'_of debruijn.id)).
  2:{
    simpl.
    unfold subst.under_kindvar'; auto.
  }
  apply under_kindvars_id.
Qed.

Lemma under_ks_id : forall ks,
    debruijn.under_ks' ks (debruijn.subst'_of debruijn.id) = debruijn.subst'_of debruijn.id.
Proof.
  intros.
  unfold debruijn.Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn.under_ks'.
  simpl.
  destruct x.
  all: simpl.
  all: unfold debruijn.get_var'.
  all: unfold debruijn.weaks'.
  all: unfold debruijn.var.
  all: simpl.
  all: unfold debruijn.plus.
  all: unfold debruijn.zero.
  all: repeat rewrite Nat.add_0_r.
  all: unfold debruijn.var'.
  all: unfold debruijn.var.
  all: simpl.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b; generalize (eq_sym Heqb);
      case b; intros; auto
    end.
  all: rewrite Nat.add_comm.
  all: rewrite Nat.add_assoc.
  all: rewrite Nat.sub_add; [ rewrite Nat.add_comm; auto | ].
  all: rewrite Nat.ltb_ge in *; auto.
Qed.

Lemma id_eq_var' : subst'_of id = var'.
Proof.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  simpl.
  destruct x.
  all: simpl.
  all: unfold get_var'.
  all: unfold weaks'.
  all: unfold var'.
  all: unfold zero.
  all: rewrite Nat.add_0_r; auto.
Qed.

Ltac solve_id_no_effect :=
  rewrite id_eq_var';
  intros;
  match goal with
  | [ |- ?F ?A ?B = _ ] =>
    replace (F A B) with (subst_ext' A B) by auto
  end;
  rewrite subst_ext'_var_e; auto.

Lemma id_no_effect_on_qual : forall {q},
    subst.subst'_qual (debruijn.subst'_of debruijn.id) q = q.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_quals : forall {qs},
    subst.subst'_quals (debruijn.subst'_of debruijn.id) qs = qs.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_size : forall {sz},
    subst.subst'_size (debruijn.subst'_of debruijn.id) sz = sz.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_sizes : forall {szs},
    subst.subst'_sizes (debruijn.subst'_of debruijn.id) szs = szs.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_loc : forall {l},
    subst.subst'_loc (debruijn.subst'_of debruijn.id) l = l.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_kvs : forall kvs,
    subst.subst'_kindvars (debruijn.subst'_of debruijn.id) kvs = kvs.
Proof.
  solve_id_no_effect.
Qed.

Lemma Forall_eq : forall {A} {f : A -> A} {l},
    Forall (fun x => f x = x) l ->
    map f l = l.
Proof.
  induction l; simpl in *; auto.
  intros.
  inversion H; subst.
  rewrite H2.
  rewrite IHl; auto.
Qed.

Lemma id_no_effect_on_type : forall {t},
    subst.subst'_type (debruijn.subst'_of debruijn.id) t = t.
Proof.
  solve_id_no_effect.
Qed.

Lemma id_no_effect_on_types : forall {ts},
    subst.subst'_types (debruijn.subst'_of debruijn.id) ts = ts.
Proof.
  solve_id_no_effect.
Qed.

Definition ks_of_kvs (kvs : list KindVar) :=
  fold_right
    (fun kv acc =>
       (debruijn.plus (debruijn.sing (subst.kind_of_kindvar kv) 1) acc))
    debruijn.zero
    kvs.

Lemma fold_left_snoc : forall {A B} {f : A -> B -> A} l el base,
    fold_left f (l ++ [el]) base =
    f (fold_left f l base) el.
Proof.
  induction l; simpl in *; auto.
Qed.

Lemma ks_of_kvs_snoc : forall kvs kv,
    ks_of_kvs (kvs ++ [kv]) =
    (debruijn.plus (debruijn.sing (subst.kind_of_kindvar kv) 1)
                   (ks_of_kvs kvs)).
Proof.
  induction kvs; simpl in *; auto.
  intros.
  rewrite IHkvs.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn.plus.
  lia.
Qed.

Lemma weaks_zero_eq_id : debruijn.weaks' debruijn.zero = debruijn.subst'_of debruijn.id.
Proof.
  unfold debruijn.Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  simpl.
  destruct x.
  all: simpl.
  all: unfold debruijn.weaks'.
  all: unfold debruijn.get_var'.
  all: unfold debruijn.var.
  all: simpl.
  all: unfold debruijn.zero.
  all: simpl.
  all: rewrite Nat.add_0_r; auto.
Qed.

Lemma weaks_zero_no_effect_on_qual : forall q,
    subst.subst'_qual (debruijn.weaks' debruijn.zero) q = q.
Proof.
  intros; rewrite weaks_zero_eq_id; rewrite id_no_effect_on_qual; auto.
Qed.

Lemma weaks_zero_no_effect_on_quals : forall qs,
    subst.subst'_quals (debruijn.weaks' debruijn.zero) qs = qs.
Proof.
  intros; rewrite weaks_zero_eq_id; rewrite id_no_effect_on_quals; auto.
Qed.

Lemma weaks_zero_no_effect_on_size : forall sz,
    subst.subst'_size (debruijn.weaks' debruijn.zero) sz = sz.
Proof.
  intros; rewrite weaks_zero_eq_id; rewrite id_no_effect_on_size; auto.
Qed.

Lemma weaks_zero_no_effect_on_sizes : forall szs,
    subst.subst'_sizes (debruijn.weaks' debruijn.zero) szs = szs.
Proof.
  intros; rewrite weaks_zero_eq_id; rewrite id_no_effect_on_sizes; auto.
Qed.

Lemma weaks_zero_no_effect_on_types : forall taus,
    subst.subst'_types (debruijn.weaks' debruijn.zero) taus = taus.
Proof.
  intros; rewrite weaks_zero_eq_id; rewrite id_no_effect_on_types; auto.
Qed.

Lemma weaks_zero_no_effect_on_local_ctx : forall L,
    subst'_local_ctx (debruijn.weaks' debruijn.zero) L = L.
Proof.
  rewrite weaks_zero_eq_id.
  induction L; simpl in *; auto.
  match goal with
  | [ X : _ * _ |- _ ] => destruct X
  end.
  rewrite id_no_effect_on_type.
  rewrite id_no_effect_on_size.
  rewrite IHL; auto.
Qed.

Lemma compose_weak_weaks : forall knd ks,
    debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks) =
    debruijn.comp'
      (debruijn.subst'_of (debruijn.weak knd))
      (debruijn.weaks' ks).
Proof.
  intros.
  unfold debruijn.Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x.
  all: simpl.
  all: unfold debruijn.weaks'.
  all: unfold debruijn.var.
  all: simpl.
  all: unfold debruijn.get_var'.
  all: unfold debruijn.under_ks'.
  all: simpl.
  all: unfold debruijn.get_var'.
  all: unfold debruijn.weaks'.
  all: unfold debruijn.var'.
  all: unfold debruijn.var.
  all: simpl.
  all: unfold debruijn.zero.
  all: unfold debruijn.plus.
  all: repeat rewrite Nat.add_0_l.
  all: repeat rewrite Nat.add_0_r.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      assert (H : B = false); [ | rewrite H ]
    end.
  1,3,5,7: rewrite Nat.ltb_ge.
  1-4: rewrite <-Nat.add_assoc.
  1-4: rewrite Nat.add_comm.
  1-4: rewrite <-Nat.add_assoc.
  1-4: apply le_plus_l.

  all:
    match goal with
    | [ |- context[?A + ?B + ?C - _] ] =>
      rewrite <-(Nat.add_assoc A B C);
      rewrite (Nat.add_comm B C);
      rewrite (Nat.add_assoc A C B)
    end.
  all: rewrite Nat.add_sub.
  all:
    match goal with
    | [ |- _ = _ (?A + ?B) ] =>
      rewrite (Nat.add_comm A B)
    end.

  all: repeat rewrite <-Nat.add_assoc.
  all:
    match goal with
    | [ |- _ (_ + (_ + (?A + ?B))) = _ ] =>
      rewrite (Nat.add_comm A B); auto
    end.
Qed.

Ltac solve_weak_weaks :=
  intros;
  match goal with
  | [ |- ?F ?A (?F ?B ?C) = _ ] =>
    replace (F A (F B C)) with (debruijn.subst_ext' A (debruijn.subst_ext' B C)) by auto
  end;
  rewrite debruijn.subst_ext'_assoc;
  match goal with
  | [ |- _ ?A _ = _ ?B _ ] =>
    replace A with B; auto
  end;
  apply compose_weak_weaks.

Lemma compose_weak_weaks_qual : forall ks knd q,
    subst.subst'_qual
      (debruijn.subst'_of (debruijn.weak knd))
      (subst.subst'_qual
         (debruijn.weaks' ks) q)
    =
    subst.subst'_qual
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      q.
Proof.
  solve_weak_weaks.
Qed.

Lemma compose_weak_weaks_size : forall ks knd sz,
    subst.subst'_size
      (debruijn.subst'_of (debruijn.weak knd))
      (subst.subst'_size
         (debruijn.weaks' ks) sz)
    =
    subst.subst'_size
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      sz.
Proof.
  solve_weak_weaks.
Qed.

Lemma compose_weak_weaks_quals : forall ks knd qs,
    subst.subst'_quals
      (debruijn.subst'_of (debruijn.weak knd))
      (subst.subst'_quals
         (debruijn.weaks' ks) qs)
    =
    subst.subst'_quals
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      qs.
Proof.
  solve_weak_weaks.
Qed.

Lemma compose_weak_weaks_sizes : forall ks knd szs,
    subst.subst'_sizes
      (debruijn.subst'_of (debruijn.weak knd))
      (subst.subst'_sizes
         (debruijn.weaks' ks) szs)
    =
    subst.subst'_sizes
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      szs.
Proof.
  solve_weak_weaks.
Qed.

Lemma compose_weak_weaks_types : forall ks knd taus,
    subst.subst'_types
      (debruijn.subst'_of (debruijn.weak knd))
      (subst.subst'_types
         (debruijn.weaks' ks) taus)
    =
    subst.subst'_types
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      taus.
Proof.
  solve_weak_weaks.
Qed.

Lemma compose_weak_weaks_local_ctx : forall ks knd L,
    subst'_local_ctx
      (debruijn.subst'_of (debruijn.weak knd))
      (subst'_local_ctx
         (debruijn.weaks' ks) L)
    =
    subst'_local_ctx
      (debruijn.weaks' (debruijn.plus (debruijn.sing knd 1) ks))
      L.
Proof.
  solve_weak_weaks.
Qed.

Definition add_constraint_to_qctx (qctx : list (list Qual * list Qual)) (kv : KindVar) :=
  match kv with
  | QUAL qs0 qs1 =>
    map
      (fun '(qs0, qs1) =>
         (subst.subst'_quals
            (debruijn.subst'_of (debruijn.weak subst.SQual)) qs0,
          subst.subst'_quals
            (debruijn.subst'_of (debruijn.weak subst.SQual)) qs1))
      ((qs0, qs1) :: qctx)
  | _ => qctx
  end.

Definition collect_qctx (kvs : list KindVar) :=
  fold_left add_constraint_to_qctx kvs [].

Lemma collect_qctx_snoc : forall kvs kv,
    collect_qctx (kvs ++ [kv]) =
    add_constraint_to_qctx (collect_qctx kvs) kv.
Proof.
  intros; unfold collect_qctx; rewrite fold_left_snoc; auto.
Qed.

Definition add_constraint_to_szctx (szctx : list (list Size * list Size)) (kv : KindVar) :=
  match kv with
  | SIZE szs0 szs1 =>
    map
      (fun '(szs0, szs1) =>
         (subst.subst'_sizes
            (debruijn.subst'_of (debruijn.weak subst.SSize)) szs0,
          subst.subst'_sizes
            (debruijn.subst'_of (debruijn.weak subst.SSize)) szs1))
      ((szs0, szs1) :: szctx)
  | _ => szctx
  end.

Definition collect_szctx (kvs : list KindVar) :=
  fold_left add_constraint_to_szctx kvs [].

Lemma collect_szctx_snoc : forall kvs kv,
    collect_szctx (kvs ++ [kv]) =
    add_constraint_to_szctx (collect_szctx kvs) kv.
Proof.
  intros; unfold collect_szctx; rewrite fold_left_snoc; auto.
Qed.

Definition add_constraint_to_tctx (tctx : list (Size * Qual * HeapableConstant)) (kv : KindVar) :=
  match kv with
  | QUAL _ _ =>
    map
      (fun '(sz, q, hc) =>
         (sz,
          subst.subst'_qual (debruijn.subst'_of (debruijn.weak subst.SQual)) q,
          hc))
      tctx
  | SIZE _ _ =>
    map
      (fun '(sz, q, hc) =>
         (subst.subst'_size (debruijn.subst'_of (debruijn.weak subst.SSize)) sz,
          q,
          hc))
      tctx
  | TYPE sz q hc => (sz, q, hc) :: tctx
  | _ => tctx
  end.

Definition collect_tctx (kvs : list KindVar) :=
  fold_left add_constraint_to_tctx kvs [].

Lemma collect_tctx_snoc : forall kvs kv,
    collect_tctx (kvs ++ [kv]) =
    add_constraint_to_tctx (collect_tctx kvs) kv.
Proof.
  intros; unfold collect_tctx; rewrite fold_left_snoc; auto.
Qed.

Definition add_constraints_to_ks_of_kvs_stmt (kvs : list KindVar) :=
  forall F,
    add_constraints F kvs =
    {|
      label :=
        map
          (fun '(ts, lctx) =>
             (subst.subst'_types
                (debruijn.weaks' (ks_of_kvs kvs))
                ts,
              subst'_local_ctx
                (debruijn.weaks' (ks_of_kvs kvs))
                lctx))
          (label F);
      ret :=
        option_map
          (subst.subst'_types
             (debruijn.weaks' (ks_of_kvs kvs)))
          (ret F);
      qual :=
        (collect_qctx kvs) ++
             map
             (fun '(qs0, qs1) =>
                (subst.subst'_quals
                   (debruijn.weaks' (ks_of_kvs kvs)) qs0,
                 subst.subst'_quals
                   (debruijn.weaks' (ks_of_kvs kvs)) qs1))
             (qual F);
      size :=
        (collect_szctx kvs) ++
              map
              (fun '(szs0, szs1) =>
                 (subst.subst'_sizes
                    (debruijn.weaks' (ks_of_kvs kvs)) szs0,
                  subst.subst'_sizes
                    (debruijn.weaks' (ks_of_kvs kvs)) szs1))
              (size F);
      type :=
        (collect_tctx kvs) ++
             map
             (fun '(sz, q, hc) =>
                (subst.subst'_size
                   (debruijn.weaks' (ks_of_kvs kvs)) sz,
                 subst.subst'_qual
                   (debruijn.weaks' (ks_of_kvs kvs)) q,
                 hc))
             (type F);
      location := location F + (ks_of_kvs kvs subst.SLoc);
      linear :=
        pmap
          (subst.subst'_qual
             (debruijn.weaks' (ks_of_kvs kvs)))
          (linear F)
    |}.

Lemma add_constraints_to_ks_of_kvs : forall kvs,
    add_constraints_to_ks_of_kvs_stmt kvs.
Proof.
  Ltac solve_map_map :=
    rewrite map_map;
    apply map_ext;
    intros;
    destruct_prs;
    repeat rewrite compose_weak_weaks_qual;
    repeat rewrite compose_weak_weaks_size;
    repeat rewrite compose_weak_weaks_quals;
    repeat rewrite compose_weak_weaks_sizes;
    repeat rewrite compose_weak_weaks_types;
    repeat rewrite compose_weak_weaks_local_ctx;
    auto.

  Ltac handle_weak_qual :=
    erewrite weak_non_qual_no_effect_on_qual;
      [ | | apply single_weak_debruijn_weak_conds ];
      solve_ineqs.
  Ltac handle_weak_size :=
    erewrite weak_non_size_no_effect_on_size;
      [ | | apply single_weak_debruijn_weak_conds ];
      solve_ineqs.
  Ltac handle_weak_sizes :=
    erewrite weak_non_size_no_effect_on_sizes;
      [ | | apply single_weak_debruijn_weak_conds ];
      solve_ineqs.
  Ltac handle_weak_quals :=
    erewrite weak_non_qual_no_effect_on_quals;
      [ | | apply single_weak_debruijn_weak_conds ];
      solve_ineqs.

  Ltac start_map_app :=
    rewrite map_app;
    match goal with
    | [ |- _ ++ ?A = _ ++ ?B ] =>
      replace A with B by solve_map_map
    end;
    match goal with
    | [ |- ?A ++ _ = ?B ++ _ ] =>
      replace A with B at 1; auto
    end.
  Ltac solve_map_app :=
    start_map_app;
    match goal with
    | [ |- ?A = _ ] => rewrite <-(map_id A) at 1
    end;
    apply map_ext;
    intros;
    destruct_prs;
    repeat handle_weak_qual;
    repeat handle_weak_size;
    repeat handle_weak_quals;
    repeat handle_weak_sizes; auto.

  Ltac solve_omap_omap :=
    match goal with
    | [ |- _ = option_map _ ?O ] =>
      remember O as obj; case obj; intros; auto
    end;
    simpl;
    rewrite compose_weak_weaks_types;
    auto.

  Ltac solve_pmap_pmap :=
    rewrite pmap_pmap;
    apply pmap_ext;
    intros;
    rewrite compose_weak_weaks_qual;
    auto.

  Ltac solve_loc_obligation :=
    unfold debruijn.plus; simpl; unfold debruijn.sing; simpl; auto.

  Ltac apply_IH :=
    intros;
    rewrite add_constraints_snoc;
    match goal with
    | [ H : context[add_constraints _ _ = _] |- _ ] =>
      rewrite H; simpl
    end;
    unfold subst'_function_ctx; simpl in *;
    apply function_ctx_eq; simpl in *;
    repeat rewrite ks_of_kvs_snoc;
    repeat rewrite collect_qctx_snoc;
    repeat rewrite collect_szctx_snoc;
    repeat rewrite collect_tctx_snoc.

  eapply rev_ind.
  all: unfold add_constraints_to_ks_of_kvs_stmt.
  - simpl in *.
    unfold debruijn.zero.
    intros.
    apply function_ctx_eq; simpl in *; auto.
    1,3-5:
      match goal with
      | [ |- ?A = _ ] => rewrite <-(map_id A) at 1
      end.
    1-4: apply map_ext.
    1-4: intros.
    1-4:
      repeat match goal with
             | [ X : _ * _ |- _ ] => destruct X
             end.
    1-4: repeat rewrite weaks_zero_no_effect_on_size.
    1-4: repeat rewrite weaks_zero_no_effect_on_qual.
    1-4: repeat rewrite weaks_zero_no_effect_on_sizes.
    1-4: repeat rewrite weaks_zero_no_effect_on_quals.
    1-4: repeat rewrite weaks_zero_no_effect_on_types.
    1-4: repeat rewrite weaks_zero_no_effect_on_local_ctx; auto.

    -- remember (ret F) as obj.
       case obj; intros; auto.
       simpl.
       rewrite weaks_zero_no_effect_on_types; auto.
    -- generalize (linear F).
       intro l; induction l; simpl.
       --- rewrite weaks_zero_no_effect_on_qual; auto.
       --- rewrite weaks_zero_no_effect_on_qual.
           rewrite <-IHl; auto.
  - intros.
    match goal with
    | [ X : KindVar |- _ ] => destruct X
    end.
    -- apply_IH.
       --- solve_map_map.
       --- solve_omap_omap.
       --- solve_map_app.
       --- solve_map_app.
       --- solve_map_app.
       --- unfold debruijn.plus.
           unfold debruijn.sing.
           simpl.
           rewrite <-Nat.add_assoc.
           rewrite Nat.add_1_r; auto.
       --- solve_pmap_pmap.
    -- apply_IH.
       --- solve_map_map.
       --- solve_omap_omap.
       --- simpl.
           rewrite map_app.
           match goal with
           | [ |- _ :: _ ++ ?A = _ :: _ ++ ?B ] =>
             replace A with B; auto
           end.
           solve_map_map.
       --- solve_map_app.
       --- start_map_app.
           simpl.
           apply map_ext_in.
           intros.
           destruct_prs.
           handle_weak_size; auto.
       --- solve_loc_obligation.
       --- solve_pmap_pmap.
    -- apply_IH.
       --- solve_map_map.
       --- solve_omap_omap.
       --- solve_map_app.
       --- simpl.
           rewrite map_app.
           match goal with
           | [ |- _ :: _ ++ ?A = _ :: _ ++ ?B ] =>
             replace A with B; auto
           end.
           solve_map_map.
       --- start_map_app.
           simpl.
           apply map_ext_in.
           intros.
           destruct_prs.
           handle_weak_qual; auto.
       --- solve_loc_obligation.
       --- solve_pmap_pmap.
    -- apply_IH.
       --- solve_map_map.
       --- solve_omap_omap.
       --- solve_map_app.
       --- solve_map_app.
       --- handle_weak_size.
           handle_weak_qual.
           simpl.
           match goal with
           | [ |- _ :: ?A = _ :: ?B ] =>
             replace A with B; auto
           end.
           start_map_app.
           rewrite <-map_id.
           apply map_ext.
           intros.
           destruct_prs.
           handle_weak_size.
           handle_weak_qual; auto.
       --- solve_loc_obligation.
       --- solve_pmap_pmap.
Qed.

Lemma InstInds_some : forall {idxs acc kvs' tau1' tau2'},
    fold_left
      (fun maybe_ft idx =>
         match maybe_ft with
         | Some ft => InstInd ft idx
         | None => None
         end) idxs acc =
    Some (FunT kvs' (Arrow tau1' tau2')) ->
    exists acc', acc = Some acc'.
Proof.
  induction idxs; intros; simpl in *; subst; eauto.
  destruct acc; eauto.
Qed.

Lemma InstInds_cons_inv : forall {idxs idx kvs tau1 tau2 kvs' tau1' tau2'},
    InstInds (FunT kvs (Arrow tau1 tau2)) (idx :: idxs) =
    Some (FunT kvs' (Arrow tau1' tau2')) ->
    exists kvs'' tau1'' tau2'',
      InstInd (FunT kvs (Arrow tau1 tau2)) idx =
      Some (FunT kvs'' (Arrow tau1'' tau2'')) /\
      InstInds (FunT kvs'' (Arrow tau1'' tau2'')) idxs =
      Some (FunT kvs' (Arrow tau1' tau2')).
Proof.
  intros.
  unfold InstInds in *.
  match goal with
  | [ H : context[fold_left ?F (?B :: ?T) ?A] |- _ ] =>
    replace (fold_left F (B :: T) A) with (fold_left F T (F A B)) in H by auto
  end.
  specialize (InstInds_some H).
  intros; destructAll.
  match goal with
  | [ X : FunType |- _ ] => destruct X
  end.
  match goal with
  | [ X : ArrowType |- _ ] => destruct X
  end.
  do 3 eexists; split; eauto.
  rewrite <-H0; auto.
Qed.

Lemma InstInd_inv_to_empty : forall {idx kvs tau1 tau2 tau1' tau2'},
    InstInd (FunT kvs (Arrow tau1 tau2)) idx =
    Some (FunT [] (Arrow tau1' tau2')) ->
    exists kv', kvs = [kv'].
Proof.
  intros.
  destruct kvs; simpl in *.
  - match goal with
    | [ H : None = Some _ |- _ ] => inversion H
    end.
  - destruct k; destruct idx; simpl in *.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; clear H
      end.
    all: destruct kvs; simpl in *; eauto.
    all:
      match goal with
      | [ H : _ :: _ = [] |- _ ] => inversion H
      end.
Qed.

Lemma InstInds_compute_cons : forall {idxs idx foralls tau1 tau2 foralls' tau1' tau2' foralls'' tau1'' tau2''},
    InstInd (FunT foralls (Arrow tau1 tau2)) idx =
    Some (FunT foralls' (Arrow tau1' tau2')) ->
    InstInds (FunT foralls' (Arrow tau1' tau2')) idxs =
    Some (FunT foralls'' (Arrow tau1'' tau2'')) ->
    InstInds (FunT foralls (Arrow tau1 tau2)) (idx :: idxs) =
    Some (FunT foralls'' (Arrow tau1'' tau2'')).
Proof.
  intros; simpl in *.
  unfold InstInds in *.
  simpl.
  rewrite H; auto.
Qed.

Lemma InstInds_arrowtype_no_effect_on_kindvars : forall {idxs kvs atyp kvs' atyp' atyp2},
    InstInds (FunT kvs atyp) idxs = Some (FunT kvs' atyp') ->
    exists atyp2',
      InstInds (FunT kvs atyp2) idxs = Some (FunT kvs' atyp2').
Proof.
  induction idxs; intros;
    repeat match goal with
           | [ X : ArrowType |- _ ] => destruct X
           end.
  - unfold InstInds in *.
    simpl in *.
    match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst
    end.
    eauto.
  - match goal with
    | [ H : InstInds _ (_ :: _) = Some _ |- _ ] =>
      specialize (InstInds_cons_inv H)
    end.
    intros; destructAll.
    match goal with
    | [ H : InstInd _ _ = Some _ |- context[FunT _ ?ATYP2] ] =>
      specialize
        (InstInd_arrowtype_no_effect_on_kindvars
           (atyp2:=ATYP2)
           H)
    end.
    intros; destructAll.
    match goal with
    | [ H : forall _ _ _ _ _, _ -> _,
        H' : InstInds _ _ = Some _,
        H'' : InstInd (FunT _ ?ATYP2B) _ = Some (FunT _ ?ATYP2A)
        |- context[FunT _ ?ATYP2B] ] =>
      specialize (H _ _ _ _ ATYP2A H')
    end.
    destructAll.
    repeat match goal with
           | [ X : ArrowType |- _ ] => destruct X
           end.
    match goal with
    | [ H : InstInd (FunT _ ?ATYP2) _ = Some ?FT,
        H' : InstInds ?FT _ = Some _
        |- context[FunT _ ?ATYP2] ] =>
      specialize (InstInds_compute_cons H H')
    end.
    eauto.
Qed.

Lemma InstInd_subst_index : forall {kvs atyp idx kvs' atyp'},
    InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp') ->
    exists kv kvs'',
      kvs = kv :: kvs'' /\
      kvs' = subst.subst_index idx kvs''.
Proof.
  intros.
  destruct idx; destruct kvs; simpl in *.
  all:
    try match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        end.
  all:
    match goal with
    | [ X : KindVar |- _ ] => destruct X
    end.
  all:
    match goal with
    | [ H : None = Some _ |- _ ] => inversion H
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst; simpl in *; clear H
    end.
  all: eauto.
Qed.

Lemma map_kind_of_kindvar_subst_index : forall idx kvs,
    map subst.kind_of_kindvar (subst.subst_index idx kvs) =
    map subst.kind_of_kindvar kvs.
Proof.
  destruct kvs; intros; destruct idx; simpl in *; auto.
  all:
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl
    end.
  all: rewrite subst_subst_kindvars_does_not_change_kind; auto.
Qed.

Lemma map_eq_one : forall {A B} {f : A -> B} {l el},
    map f l = [el] ->
    exists el', l = [el'].
Proof.
  intros.
  destruct l; simpl in *.
  - inversion H.
  - inversion H; subst.
    destruct l; simpl in *; eauto.
    inversion H2.
Qed.

Lemma length_subst_kindvars : forall kvs su,
    length (subst.subst'_kindvars su kvs) = length kvs.
Proof.
  induction kvs; simpl in *; auto.
Qed.

Lemma subst_kindvars_remove_snoc : forall {kvs kv kvs' kv' su},
    subst.subst'_kindvars su (kvs ++ [kv]) = kvs' ++ [kv'] ->
    subst.subst'_kindvars su kvs = kvs'.
Proof.
  induction kvs; intros; simpl in *.
  - destruct kvs'; simpl in *; auto.
    inversion H.
    destruct kvs'; simpl in *; inversion H2.
  - destruct kvs'; simpl in *.
    -- inversion H.
       match goal with
       | [ H : subst.subst'_kindvars ?SU ?KVS = [] |- _ ] =>
         specialize (length_subst_kindvars KVS SU); rewrite H
       end.
       rewrite snoc_length.
       simpl.
       intro H'; inversion H'.
    -- inversion H; subst.
       specialize (IHkvs _ _ _ _ H2).
       rewrite IHkvs; auto.
Qed.       

Lemma InstInd_remove_snoc : forall {kvs kv kvs' kv' atyp atyp' idx},
    InstInd (FunT (kvs ++ [kv]) atyp) idx =
    Some (FunT (kvs' ++ [kv']) atyp') ->
    exists atyp'',
      InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp'').
Proof.
  intros.
  specialize (InstInd_subst_index H).
  intros; destructAll.
  destruct kvs.
  - match goal with
    | [ H : [] ++ _ = _ |- _ ] =>
      simpl in H; inversion H; subst
    end.
    destruct idx; simpl in *.
    all:
      match goal with
      | [ H : ?L ++ _ = [] |- _ ] =>
        destruct L; inversion H
      end.
  - rewrite <-app_comm_cons in *.
    all:
      match goal with
      | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst
      end.
    match goal with
    | [ |- exists _, InstInd (FunT (?KV :: _) _) ?IDX = Some _ ] =>
      destruct KV; destruct IDX; simpl in *
    end.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; clear H
      end.
    all:
      match goal with
      | [ H : subst.subst'_kindvars _ _ = _ ++ _ |- _ ] =>
        specialize (subst_kindvars_remove_snoc H)
      end.
    all: intros; subst.
    all: eauto.
Qed.

Lemma InstInds_snoc_inv_to_empty : forall {idxs idx kvs atyp atyp'},
    InstInds (FunT kvs atyp) (idxs ++ [idx]) = Some (FunT [] atyp') ->
    exists kvs' kv,
      kvs = kvs' ++ [kv] /\
      (forall atyp'',
          exists atyp''',
            InstInds (FunT kvs' atyp'') idxs = Some (FunT [] atyp''')) /\
      (forall atyp'',
          exists atyp''',
            InstInd (FunT [kv] atyp'') idx = Some (FunT [] atyp''')).
Proof.
  induction idxs; intros;
    repeat match goal with
           | [ X : ArrowType |- _ ] => destruct X
           end.
  - match goal with
    | [ H : InstInds _ ([] ++ [?IDX]) = Some _ |- _ ] =>
      simpl in H;
      specialize (InstInds_cons_inv H)
    end.
    intros; destructAll.
    match goal with
    | [ H : InstInds _ [] = Some _ |- _ ] =>
      unfold InstInds in H; simpl in H; inversion H; subst
    end.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      specialize (InstInd_inv_to_empty H)
    end.
    intros; destructAll.
    match goal with
    | [ |- context[[?KV] = _ ++ _] ] =>
      exists [], KV
    end.
    split; auto.
    split; intros.
    -- eapply InstInds_arrowtype_no_effect_on_kindvars; eauto.
    -- eapply InstInd_arrowtype_no_effect_on_kindvars; eauto.
  - match goal with
    | [ H : context[(_ :: _) ++ _] |- _ ] =>
      rewrite <-app_comm_cons in H;
      specialize (InstInds_cons_inv H)
    end.
    intros; destructAll.
    match goal with
    | [ H : forall _ _ _ _, _ -> _,
        H' : InstInds _ (_ ++ _) = Some _ |- _ ] =>
      specialize (H _ _ _ _ H')
    end.
    intros; destructAll.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      specialize (InstInd_subst_index H)
    end.
    intros; destructAll.
    match goal with
    | [ H : context[subst.subst_index ?IDX ?KV] |- _ ] =>
      specialize (map_kind_of_kindvar_subst_index IDX KV)
    end.
    intros.
    match goal with
    | [ H : _ ++ _ = ?A, H' : map _ ?A = _ |- _ ] =>
      rewrite <-H in H'; rewrite map_app in H'
    end.
    match goal with
    | [ H : _ ++ _ = map _ _ |- _ ] =>
      specialize (map_eq_app _ _ _ _ (eq_sym H))
    end.
    intros; destructAll.
    match goal with
    | [ H : context[map _ [_]] |- _ ] => simpl in H
    end.
    match goal with
    | [ H : _ = [_] |- _ ] =>
      specialize (map_eq_one H)
    end.
    intros; destructAll.
    match goal with
    | [ H : _ = [_] |- _ ] =>
      simpl in H; inversion H; subst
    end.
    match goal with
    | [ H : context[?A :: ?B ++ [?C]] |- _ ] =>
      exists (A :: B), C
    end.
    split; auto.
    split; intros.
    -- match goal with
       | [ H : InstInd (FunT (_ :: _ ++ _) _) _ = Some _ |- _ ] =>
         rewrite app_comm_cons in H;
         specialize (InstInd_remove_snoc H)
       end.
       intros; destructAll.
       match goal with
       | [ H : InstInd (FunT ?ST _) _ = Some _
           |- context[InstInds (FunT ?ST ?ATYP)] ] =>
         specialize (InstInd_arrowtype_no_effect_on_kindvars (atyp2:=ATYP) H)
       end.
       intros; destructAll.
       match goal with
       | [ H : InstInd (FunT ?ST ?OATYP) _ = Some (FunT ?INT ?ATYP),
           H' : context[InstInds (FunT ?INT _)]
           |- context[InstInds (FunT ?ST ?OATYP)] ] =>
         specialize (H' ATYP); destructAll
       end.
       repeat match goal with
              | [ X : ArrowType |- _ ] => destruct X
              end.
       match goal with
       | [ H : InstInd (FunT ?ST _) _ = Some (FunT ?INT ?ATYP),
           H' : InstInds (FunT ?INT ?ATYP) _ = Some _
           |- context[InstInds (FunT ?ST _)] ] =>
         specialize (InstInds_compute_cons H H')
       end.
       eauto.
    -- match goal with
       | [ H : context[InstInd (FunT [?OKV] _)],
               H' : subst.kind_of_kindvar ?NKV =
                    subst.kind_of_kindvar ?OKV
           |- context[InstInd (FunT [?NKV] ?ATYP)] ] =>
         specialize (H ATYP); destructAll;
         destruct OKV; destruct NKV; simpl in *;
         try rewrite H; eauto
       end.
       all:
         match goal with
         | [ H : @Logic.eq subst.Ind _ _ |- _ ] =>
           inversion H
         end.
Qed.

Lemma InstIndValid_remove_snoc : forall {kv' idx kvs kv atyp F},
    InstIndValid F (FunT (kv' :: kvs ++ [kv]) atyp) idx ->
    InstIndValid F (FunT (kv' :: kvs) atyp) idx.
Proof.
  destruct kv'; destruct idx; intros; simpl in *;
    match goal with
    | [ H : InstIndValid _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  all: econstructor; eauto.
Qed.

Lemma InstInd_snoc_input_to_snoc_output : forall {kv' idx kvs kv kvs' atyp atyp'},
    InstInd (FunT (kv' :: kvs ++ [kv]) atyp) idx = Some (FunT kvs' atyp') ->
    exists kvs'' kv'',
      kvs' = kvs'' ++ [kv''] /\
      length kvs'' = length kvs.
Proof.
  destruct kv'; destruct idx; intros; simpl in *;
    match goal with
    | [ H : _ = Some _ |- _ ] =>
      inversion H; subst; simpl in *; clear H
    end.
  all:
    match goal with
    | [ |- context[?L = _ /\ _] ] =>
      let H0 := fresh "H" in
      assert (H0 : exists a b, L = a ++ [b]);
      [ apply snoc_exists | ]
    end.
  all: try rewrite length_subst_kindvars.
  all: try rewrite snoc_length.
  all: try apply gt_Sn_O.

  all: destructAll.
  all: match goal with
       | [ H : ?A = _ |- context[?A] ] => rewrite H
       end.
  all: do 2 eexists; split; auto.
  all: match goal with
       | [ H : _ = _ |- _ ] =>
         specialize (subst_kindvars_remove_snoc H)
       end.
  all: intros; subst.
  all: apply length_subst_kindvars.
Qed.

Lemma InstIndsValid_length_ineq : forall {idxs kvs atyp F},
    InstIndsValid F (FunT kvs atyp) idxs ->
    length kvs >= length idxs.
Proof.
  induction idxs.
  - intros.
    simpl.
    unfold Peano.ge.
    apply Nat.le_0_l.
  - intros; simpl.
    match goal with
    | [ X : ArrowType |- _ ] => destruct X
    end.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] =>
      apply InstIndsValid_cons_inv in H
    end.
    destructAll.
    match goal with
    | [ H : InstInd (FunT ?KVS _) ?IDX = Some _ |- _ ] =>
      destruct KVS; [ simpl in *; inversion H | ]
    end.
    match goal with
    | [ H : InstInd (FunT (?KV :: _) _) ?IDX = Some _ |- _ ] =>
      destruct KV; destruct IDX; simpl in *;
      inversion H; subst; simpl in *; clear H
    end.
    all: apply Peano.le_n_S.
    all:
      match goal with
      | [ H : InstIndsValid _ (FunT ?KVS _) _ |- _ <= ?B ] =>
        replace B with (length KVS)
      end.
    all:
      try match goal with
          | [ |- _ = _ ] =>
            rewrite length_subst_kindvars; auto
          end.
    all: eapply IHidxs; eauto.
Qed.    

Lemma InstIndsValid_remove_snoc : forall {idxs idx kvs kv atyp F},
    InstIndsValid F (FunT (kvs ++ [kv]) atyp) (idxs ++ [idx]) ->
    InstIndsValid F (FunT kvs atyp) idxs.
Proof.
  induction idxs; intros; simpl in *.  
  - constructor.
  - destruct kvs; simpl in *;
      match goal with
      | [ H : InstIndsValid _ _ _ |- _ ] =>
        inversion H; subst
      end.
    1:{
      match goal with
      | [ H : InstInd (FunT [?KV] _) ?IDX = Some _ |- _ ] =>
        destruct KV; destruct IDX; simpl in *;
        inversion H; subst; simpl in *; clear H
      end.
      all:
        match goal with
        | [ H : InstIndsValid _ _ _ |- _ ] =>
          apply InstIndsValid_length_ineq in H;
          rewrite snoc_length in H; simpl in H;
          inversion H
        end.
    }
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      rewrite app_comm_cons in H;
      specialize (InstInd_snoc_input_to_snoc_output H)
    end.
    intros; destructAll.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      specialize (InstInd_remove_snoc H)
    end.
    intros; destructAll.
    econstructor; eauto.
    -- eapply InstIndValid_remove_snoc; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _,
           H' : InstIndsValid _ (FunT (?KVS ++ _) _) _ |- _ ] =>
         specialize (H _ _ _ _ _ H')
       end.
       eapply InstIndsValid_Function_Ctx_stronger; eauto.
Qed.

Lemma InstInd_length_eq : forall {kv idx kvs atyp kvs' atyp'},
    InstInd (FunT (kv :: kvs) atyp) idx = Some (FunT kvs' atyp') ->
    length kvs = length kvs'.
Proof.
  destruct kv; destruct idx; simpl in *; intros;
    match goal with
    | [ H : _ = Some _ |- _ ] =>
      inversion H; subst; simpl in *; clear H
    end.
  all: rewrite length_subst_kindvars; auto.
Qed.

Lemma InstInds_to_empty_length_eq : forall {idxs kvs atyp atyp'},
    InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp') ->
    length kvs = length idxs.
Proof.
  induction idxs.
  - intros.
    destruct kvs; auto.
    unfold InstInds in *.
    simpl in *.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H
    end.
  - intros.
    repeat match goal with
           | [ X : ArrowType |- _ ] => destruct X
           end.
    match goal with
    | [ H : InstInds _ (_ :: _) = Some _ |- _ ] =>
      specialize (InstInds_cons_inv H)
    end.
    intros; destructAll.

    destruct kvs.
    1:{
      simpl in *.
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    simpl.
    match goal with
    | [ H : forall _ _ _, _,
        H' : InstInds _ _ = Some _ |- _ ] =>
      specialize (H _ _ _ H'); rewrite <-H
    end.
    erewrite InstInd_length_eq; eauto.
Qed.

Lemma subst_indices_snoc_size : forall idxs idx (sz : Size),
    subst.subst_indices (idxs ++ [idx]) sz =
    subst.subst_indices idxs (subst.subst_index idx sz).
Proof.
  induction idxs; intros; simpl in *; auto.
  rewrite IHidxs; auto.
Qed.

Lemma InstIndsValid_SizeValid_provable : forall {idx idxs sz ft F},
  InstIndsValid F ft idxs ->
  nth_error idxs idx = Some (SizeI sz) ->
  SizeValid (size F) sz.
Proof.
  induction idx;
    intros; simpl in *;
    destruct idxs;
    try match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        | [ H : Some _ = Some _ |- _ ] => inversion H; subst
        end;
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inversion H; subst
    end.
  - match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inversion H; subst; auto
    end.
  - eauto.
Qed.

Lemma InstIndsValid_SizeValid : forall {idxs sz ft F},
  InstIndsValid F ft idxs ->
  List.In (SizeI sz) idxs ->
  SizeValid (size F) sz.
Proof.
  intros.
  match goal with
  | [ H : List.In _ _ |- _ ] => apply In_nth_error in H
  end.
  destructAll.
  eapply InstIndsValid_SizeValid_provable; eauto.
Qed.

Lemma SizeValid_empty_imp_all_SizeValid : forall {sz} szctx,
    SizeValid [] sz ->
    SizeValid szctx sz.
Proof.
  induction sz; intros; simpl in *;
    match goal with
    | [ H : SizeValid _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end;
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  - match goal with
    | [ H : context[nth_error [] ?IDX] |- _ ] =>
      destruct IDX; simpl in *; inversion H
    end.
  - eapply SizePlusValid; eauto.
  - econstructor; eauto.
Qed.  

Lemma SizeValid_subst_ind : forall {sz sz' ft idxs szctx sztpl},
  SizeValid (sztpl :: szctx) sz ->
  InstIndsValid empty_Function_Ctx ft idxs ->
  List.In (SizeI sz') idxs ->
  SizeValid
    szctx
    (subst.subst'_size
       (debruijn.subst'_of
          (debruijn.ext subst.SSize sz' debruijn.id))
       sz).
Proof.
  induction sz; intros; simpl in *;
    match goal with
    | [ H : SizeValid _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end;
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  - unfold debruijn.get_var'.
    simpl.
    unfold debruijn.ext.
    simpl.
    rewrite weaks_zero_no_effect_on_size.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
      generalize (eq_sym Heqb); case b; intros
    end.
    -- match goal with
       | [ H : InstIndsValid _ _ _,
           H' : List.In _ _ |- _ ] =>
         specialize (InstIndsValid_SizeValid H H')
       end.
       intros; simpl in *.
       eapply SizeValid_empty_imp_all_SizeValid; eauto.
    -- unfold id.
       unfold debruijn.var.
       simpl.
       match goal with
       | [ H : SizeValid _ _ |- _ ] =>
         inversion H; subst; simpl in *
       end;
       match goal with
       | [ H : @Logic.eq Size _ _ |- _ ] =>
         inversion H; subst; simpl in *
       end.
       match goal with
       | [ H : ?X <> 0 |- _ ] =>
         destruct X; [ exfalso; apply H; auto | ]
       end.
       simpl in *.
       rewrite Nat.sub_0_r.
       eapply SizeVarValid; eauto.
  - eapply SizePlusValid; eauto.
  - econstructor; eauto.
Qed.

Lemma SizeValid_length : forall {sz szctx szctx'},
    SizeValid szctx sz ->
    length szctx = length szctx' ->
    SizeValid szctx' sz.
Proof.
  induction sz; intros; simpl in *;
    match goal with
    | [ H : SizeValid _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end;
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  - match goal with
    | [ H : nth_error ?L ?IDX = Some _,
        H' : length ?L = length ?LP |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : exists v, nth_error LP IDX = Some v);
      [ apply nth_error_some_exists; rewrite <-H' | ]
    end.
    { eapply nth_error_Some_length; eauto. }
    destructAll.
    eapply SizeVarValid; eauto.
  - eapply SizePlusValid; eauto.
  - econstructor; eauto.
Qed.

Definition InstFunctionCtxInd (F : Function_Ctx) (i : Index) :=
  match i with
  | LocI l =>
    match (location F) with
    | Datatypes.S n =>
      Some (subst_ext
              (ext subst.SLoc l id)
              (update_location_ctx n F))
    | _ => None
    end
  | QualI q =>
    match (qual F) with
    | _ :: qctx =>
      Some (subst_ext
              (ext subst.SQual q id)
              (update_qual_ctx qctx F))
    | _ => None
    end
  | SizeI sz =>
    match (size F) with
    | _ :: szctx =>
      Some (subst_ext
              (ext subst.SSize sz id)
              (update_size_ctx szctx F))
    | _ => None
    end
  | PretypeI pt =>
    match (type F) with
    | _ :: tctx =>
      Some (subst_ext
              (ext subst.SPretype pt id)
              (update_type_ctx tctx F))
    | _ => None
    end
  end.

Definition InstFunctionCtxInds (F : Function_Ctx) (is : list Index) :=
  fold_right
    (fun i maybe_ft =>
       match maybe_ft with
       | Some F' => InstFunctionCtxInd F' i
       | None => None
       end)
    (Some F)
    is.

Lemma InstFunctionCtxInd_update_ret_ctx : forall {idx F F' maybe_ret},
    InstFunctionCtxInd F idx = Some F' ->
    InstFunctionCtxInd
      (update_ret_ctx maybe_ret F)
      idx
    =
    Some (update_ret_ctx
            (option_map (subst.subst_index idx) maybe_ret)
            F').
Proof.
  Ltac simpl_ifci_goal F :=
    match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    end;
    destruct F; subst; simpl in *; subst; simpl in *;
    unfold subst'_function_ctx; simpl in *;
    match goal with
    | [ |- Some ?A = Some ?B ] => replace A with B; auto
    end.

  destruct idx; intros; simpl in *.
  - revert H.
    remember (location F) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    simpl_ifci_goal F.
  - revert H.
    remember (size F) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    simpl_ifci_goal F.
  - revert H.
    remember (qual F) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    simpl_ifci_goal F.
  - revert H.
    remember (type F) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    simpl_ifci_goal F.
Qed.   

Lemma option_map_option_map : forall {A B C} {f : A -> B} {g : B -> C} {maybe_obj},
    option_map g (option_map f maybe_obj) =
    option_map (fun x => g (f x)) maybe_obj.
Proof.
  intros.
  destruct maybe_obj; simpl; auto.
Qed. 

Lemma InstFunctionCtxInds_update_ret_ctx : forall {idxs F F' maybe_ret},
    InstFunctionCtxInds F idxs = Some F' ->
    InstFunctionCtxInds
      (update_ret_ctx maybe_ret F)
      idxs
    =
    Some (update_ret_ctx
            (option_map (subst.subst_indices idxs) maybe_ret)
            F').
Proof.
  induction idxs; intros; simpl in *.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst
    end.
    destruct maybe_ret; simpl; auto.
  - match goal with
    | [ H : context[InstFunctionCtxInds ?F ?IDXS] |- _ ] =>
      remember (InstFunctionCtxInds F IDXS) as obj;
      revert H; generalize (eq_sym Heqobj); case obj; intros
    end.
    2:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    match goal with
    | [ H : forall _ _ _, _,
        H' : InstFunctionCtxInds _ _ = Some _
        |- context[InstFunctionCtxInds (update_ret_ctx ?MR _)] ] =>
      specialize (H _ _ MR H'); rewrite H
    end.
    erewrite InstFunctionCtxInd_update_ret_ctx; eauto.
    rewrite option_map_option_map.
    auto.
Qed.

Lemma fold_right_snoc : forall {A B} {f : B -> A -> A} l el base,
    fold_right f base (l ++ [el]) =
    fold_right f (f el base) l.
Proof.
  induction l; intros; simpl in *; auto.
  rewrite IHl; auto.
Qed.

Lemma InstFunctionCtxInds_snoc : forall {F idxs idx},
    InstFunctionCtxInds F (idxs ++ [idx]) =
    match InstFunctionCtxInd F idx with
    | Some F' => InstFunctionCtxInds F' idxs
    | None => None
    end.
Proof.
  intros.
  unfold InstFunctionCtxInds.
  rewrite fold_right_snoc.
  generalize (InstFunctionCtxInd F idx).
  let x := fresh "x" in intro x; case x; intros; auto.
  induction idxs; simpl in *; auto.
  rewrite IHidxs; auto.
Qed.

Lemma InstInd_InstFunctionCtx : forall {idx kv kvs kvs' F atyp atyp'},
    InstInd (FunT (kv :: kvs) atyp) idx = Some (FunT kvs' atyp') ->
    InstFunctionCtxInd (add_constraint F kv) idx =
    Some F.
Proof.
  Ltac simpl_ifci_goal_one F :=
    match goal with
    | [ |- Some ?A = Some ?B ] => replace A with B; auto
    end;
    match goal with
    | [ |- context[ext ?KND ?O id] ] =>
      rewrite <-(function_ctx_debruijn_subst_weak (F:=F) (kndspec:=KND) (obj:=O)) at 1
    end;
    destruct F; subst; simpl in *;
    unfold subst'_function_ctx; simpl in *;
    apply function_ctx_eq; auto.

  destruct idx; destruct kv; intros;
    match goal with
    | [ H : _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    end.
  all: unfold InstFunctionCtxInd.
  all: unfold add_constraint.
  - replace (location (subst_ext (weak subst.SLoc) (update_location_ctx (location F + 1) F))) with (location F + 1).
    2:{
      destruct F; subst; simpl in *; auto.
    }
    rewrite Nat.add_1_r.
    simpl_ifci_goal_one F.
  - replace (size (subst_ext (weak subst.SSize) (update_size_ctx ((l, l0) :: size F) F))) with ((subst.subst'_sizes (subst'_of (weak subst.SSize)) l, subst.subst'_sizes (subst'_of (weak subst.SSize)) l0) :: (map (fun '(szs0, szs1) => (subst.subst'_sizes (subst'_of (weak subst.SSize)) szs0, subst.subst'_sizes (subst'_of (weak subst.SSize)) szs1)) (size F))).
    2:{
      destruct F; subst; simpl in *; auto.
    }
    simpl_ifci_goal_one F.
  - replace (qual (subst_ext (weak subst.SQual) (update_qual_ctx ((l, l0) :: qual F) F))) with ((subst.subst'_quals (subst'_of (weak subst.SQual)) l, subst.subst'_quals (subst'_of (weak subst.SQual)) l0) :: (map (fun '(szs0, szs1) => (subst.subst'_quals (subst'_of (weak subst.SQual)) szs0, subst.subst'_quals (subst'_of (weak subst.SQual)) szs1)) (qual F))).
    2:{
      destruct F; subst; simpl in *; auto.
    }
    simpl_ifci_goal_one F.
  - replace (type (subst_ext (weak subst.SPretype) (update_type_ctx ((s, q, h) :: type F) F))) with ((s, q, h) :: (map (fun '(sz, q, hc) => (subst.subst'_size (subst'_of (weak subst.SPretype)) sz, subst.subst'_qual (subst'_of (weak subst.SPretype)) q, hc)) (type F))).
    2:{
      destruct F; subst; simpl in *; auto.
      rewrite pretype_weak_no_effect_on_size.
      rewrite pretype_weak_no_effect_on_qual.
      auto.
    }
    simpl_ifci_goal_one F.
Qed.

Lemma InstInds_to_empty_InstFunctionCtxInds : forall {idxs kvs F atyp atyp'},
    InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp') ->
    InstFunctionCtxInds (add_constraints F kvs) idxs =
    Some F.
Proof.
  apply
    (rev_ind
       (fun idxs =>
          forall kvs F atyp atyp',
            InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp') ->
            InstFunctionCtxInds (add_constraints F kvs) idxs
            = Some F)).
  - intros; simpl in *.
    specialize (InstInds_to_empty_length_eq H).
    intros.
    destruct kvs; simpl in *; auto.
    match goal with
    | [ H : Datatypes.S _ = 0 |- _ ] =>
      inversion H
    end.
  - intros.
    match goal with
    | [ H : InstInds _ _ = Some _ |- _ ] =>
      specialize (InstInds_snoc_inv_to_empty H)
    end.
    intros; destructAll.
    rewrite add_constraints_snoc.
    rewrite InstFunctionCtxInds_snoc.
    repeat match goal with
           | [ H : forall _, exists _, _ |- _ ] =>
             specialize (H (Arrow [] []))
           end.
    destructAll.
    erewrite InstInd_InstFunctionCtx; eauto.
Qed.

Ltac solve_forallb_subgoal :=
  rewrite forallb_forall;
  intros;
  match goal with
  | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
  end;
  destructAll;
  match goal with
  | [ H : forallb _ ?L = true, H' : List.In _ ?L |- _ ] =>
    rewrite forallb_forall in H; specialize (H _ H')
  end;
  match goal with
  | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
    rewrite Forall_forall in H; eapply H; eauto
  end.

Lemma NoCaps_subst_SLoc_provable : forall {t hc f ks l},
    debruijn_subst_ext_conds f ks SLoc l ->
    NoCapsTyp hc t = true ->
    NoCapsTyp hc (subst'_type f t) = true.
Proof.
  apply
    (Typ_ind'
       (fun pt =>
          forall hc f ks l,
            debruijn_subst_ext_conds f ks SLoc l ->
            NoCapsPretype hc pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks l,
            debruijn_subst_ext_conds f ks SLoc l ->
            NoCapsTyp hc t = true ->
            NoCapsTyp hc (subst'_type f t) = true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> SLoc] |- _ ] => rewrite H; solve_ineqs
    end.
    simpl; auto.
  - solve_forallb_subgoal.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_subst_ext_under_knd; eauto.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma NoCaps_subst_SLoc : forall {t C} l,
  NoCapsTyp (heapable C) t = true ->
  NoCapsTyp (heapable C) (subst'_type (subst'_of (ext SLoc l id)) t) = true.
Proof.
  intros.
  eapply NoCaps_subst_SLoc_provable; eauto.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma NoCapsPretype_subst_weak_SLoc_provable : forall {pt hc f ks},
    debruijn_weaks_conds f ks (sing SLoc 1) ->
    NoCapsPretype hc pt = true ->
    NoCapsPretype hc (subst'_pretype f pt) = true.
Proof.
  eapply
    (Pretype_ind'
       (fun pt =>
          forall hc f ks,
            debruijn_weaks_conds f ks (sing SLoc 1) ->
            NoCapsPretype hc pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks,
            debruijn_weaks_conds f ks (sing SLoc 1) ->
            NoCapsTyp hc t = true ->
            NoCapsTyp hc (subst'_type f t) = true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    erewrite weak_no_effect_on_other_vars; eauto.
    solve_ineqs.
  - solve_forallb_subgoal.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma NoCapsPretype_subst_weak_SLoc : forall {pt hc},
    NoCapsPretype hc pt = true ->
    NoCapsPretype
      hc
      (subst'_pretype (subst'_of (weak SLoc)) pt)
    = true.
Proof.
  intros.
  eapply NoCapsPretype_subst_weak_SLoc_provable; eauto.
  apply single_weak_debruijn_weak_conds.
Qed.

Lemma NoCapsPretype_subst_weak_provable : forall {pt hc f ks},
    debruijn_weaks_conds f ks (sing SPretype 1) ->
    NoCapsPretype (remove_nth hc (ks SPretype)) pt = true ->
    NoCapsPretype hc (subst'_pretype f pt) = true.
Proof.
  eapply
    (Pretype_ind'
       (fun pt =>
          forall hc f ks,
            debruijn_weaks_conds f ks (sing SPretype 1) ->
            NoCapsPretype (remove_nth hc (ks SPretype)) pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks,
            debruijn_weaks_conds f ks (sing SPretype 1) ->
            NoCapsTyp (remove_nth hc (ks SPretype)) t = true ->
            NoCapsTyp hc (subst'_type f t) = true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    unfold debruijn_weaks_conds in *; destructAll.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V)
             by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       match goal with
       | [ H : context[nth_error _ ?V], H' : ?V < ?V2 |- _ ] =>
         replace V with (shift_down_after V V2 0) in H;
         [ rewrite nth_error_shift_down in H | ]
       end.
       3:{
         unfold shift_down_after.
         rewrite <-Nat.ltb_lt in *.
         match goal with
         | [ H : ?A = _ |- context[?A] ] => rewrite H
         end.
         auto.
       }
       2:{
         apply Nat.lt_neq; auto.
       }
       auto.
    -- match goal with
       | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       match goal with
       | [ H : context[nth_error (remove_nth ?L ?V) ?V2] |- _ ] =>
         replace (nth_error (remove_nth L V) V2) with
             (nth_error
                (remove_nth (Heapable :: L) (Datatypes.S V))
                (Datatypes.S V2))
           in H by auto
       end.
       match goal with
       | [ H : context[nth_error _ (Datatypes.S ?V)], H' : ?V2 <= ?V |- _ ] =>
         replace (Datatypes.S V) with (shift_down_after (Datatypes.S (Datatypes.S V)) (Datatypes.S V2) 0) in H;
         [ rewrite nth_error_shift_down in H | ]
       end.
       3:{
         unfold shift_down_after.
         rewrite <-Nat.ltb_ge in *.
         match goal with
         | [ |- context[if ?B then _ else _] ] =>
           replace B with false; auto
         end.
         apply eq_sym.
         rewrite Nat.ltb_ge in *.
         apply le_n_S; auto.
       }
       2:{ intro; lia. }
       simpl in *; auto.
  - solve_forallb_subgoal.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- simpl; auto.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- simpl; auto.
Qed.    

Lemma NoCapsPretype_subst_weak : forall {pt hc c},
    NoCapsPretype hc pt = true ->
    NoCapsPretype
      (c :: hc)
      (subst'_pretype (subst'_of (weak SPretype)) pt)
    = true.
Proof.
  intros; eapply NoCapsPretype_subst_weak_provable.
  - eapply single_weak_debruijn_weak_conds.
  - simpl; auto.
Qed.

Lemma NoCapsPretype_subst_provable : forall {pt' pt hc f ks hc'},
    debruijn_subst_ext_conds f ks SPretype pt ->
    nth_error hc (ks SPretype) = Some hc' ->
    NoCapsPretype hc pt' = true ->
    (hc' = Heapable ->
     NoCapsPretype (remove_nth hc (ks SPretype))
                   (subst'_pretype (weaks' ks) pt) = true) ->
    NoCapsPretype
      (remove_nth hc (ks SPretype))
      (subst.subst'_pretype f pt')
    = true.
Proof.
  apply
    (Pretype_ind'
       (fun pt' =>
          forall pt hc f ks hc',
            debruijn_subst_ext_conds f ks SPretype pt ->
            nth_error hc (ks SPretype) = Some hc' ->
            NoCapsPretype hc pt' = true ->
            (hc' = Heapable ->
             NoCapsPretype (remove_nth hc (ks SPretype))
                           (subst'_pretype (weaks' ks) pt) = true) ->
            NoCapsPretype
              (remove_nth hc (ks SPretype))
              (subst.subst'_pretype f pt')
            = true)
       (fun t =>
          forall pt hc f ks hc',
            debruijn_subst_ext_conds f ks SPretype pt ->
            nth_error hc (ks SPretype) = Some hc' ->
            NoCapsTyp hc t = true ->
            (hc' = Heapable ->
             NoCapsPretype (remove_nth hc (ks SPretype))
                           (subst'_pretype (weaks' ks) pt) = true) ->
            NoCapsTyp
              (remove_nth hc (ks SPretype))
              (subst.subst'_type f t)
            = true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> ?V2] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V = V2 \/ V <> V2) by apply eq_dec_nat;
      case H'; intros; subst
    end.
    -- match goal with
       | [ H : context[?F _ ?V _] |- context[?F _ ?V _] ] =>
         rewrite H
       end.
       simpl.
       rewrite plus_zero.
       match goal with
       | [ H : _ -> ?A |- ?A ] => apply H
       end.
       match goal with
       | [ |- ?X = _ ] => destruct X; auto
       end.
       match goal with
       | [ H : ?A = Some NotHeapable, H' : context[?A] |- _ ] =>
           rewrite H in H'; inv H'
       end.
    -- match goal with
       | [ H : context[_ <> _ _] |- _ ] => rewrite H; auto
       end.
       simpl.
       unfold zero.
       rewrite nth_error_shift_down; auto.
  - solve_forallb_subgoal.
  - match goal with
    | [ |- context[?A :: remove_nth ?L (?F ?KND)] ] =>
      replace (A :: remove_nth L (F KND)) with
          (remove_nth (A :: L)
                      ((plus (sing KND 1) F) KND)) by auto
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- apply debruijn_subst_ext_under_knd; eauto.
    -- simpl.
       rewrite compose_weak_weaks.
       match goal with
       | [ |- context[?F (?A ∘' ?B) ?PT] ] =>
         replace (F (A ∘' B) PT) with (subst_ext' (A ∘' B) PT) by auto
       end.
       rewrite <-subst_ext'_assoc.
       simpl.
       intros.
       match goal with
       | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
       end.
       apply NoCapsPretype_subst_weak; auto.
  - match goal with
    | [ |- context[remove_nth ?L (?F ?KND)] ] =>
      replace (remove_nth L (F KND)) with
          (remove_nth L
                      ((plus (sing SLoc 1) F) KND)) by auto
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- match goal with
       | [ |- context[plus ?A ?B ?C] ] =>
         replace (plus A B C) with (B C)
       end.
       2:{ unfold plus; unfold sing; auto. }
       rewrite compose_weak_weaks.
       match goal with
       | [ |- context[?F (?A ∘' ?B) ?PT] ] =>
         replace (F (A ∘' B) PT) with (subst_ext' (A ∘' B) PT) by auto
       end.
       rewrite <-subst_ext'_assoc.
       simpl.
       intros.
       match goal with
       | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
       end.
       apply NoCapsPretype_subst_weak_SLoc; auto.
Qed.

Lemma NoCapsPretype_subst F pt pt' hc' :
  NoCapsPretype (hc' :: F) pt' = true ->
  NoCapsPretype F pt = true ->
  NoCapsPretype F (subst.subst'_pretype (subst'_of (ext SPretype pt id)) pt') = true.
Proof.
  replace F with (remove_nth (hc' :: F) (zero SPretype)) by auto.
  intros.
  eapply NoCapsPretype_subst_provable; eauto.
  - apply simpl_debruijn_subst_ext_conds.
  - simpl.
    eauto.
  - rewrite weaks_zero_eq_id.
    rewrite id_eq_var'.
    replace (subst'_pretype var' pt) with (subst_ext' var' pt) by auto.
    rewrite subst_ext'_var_e.
    unfold zero in *.
    simpl in *.
    auto.
Qed.

Lemma NoCaps_subst F t pt hc' :
  NoCapsTyp (hc' :: F) t = true ->
  NoCapsPretype F pt = true ->
  NoCapsTyp F (subst.subst'_type (subst'_of (ext SPretype pt id)) t) = true.
Proof.
  destruct t; simpl.
  intros.
  eapply NoCapsPretype_subst; eauto.
Qed.

Lemma sloc_on_spretype_var : forall {f ks l} v,
    debruijn_subst_ext_conds f ks SLoc l ->
    f SPretype v zero = TVar v.
Proof.
  unfold debruijn_subst_ext_conds.
  intros; destructAll.
  rewrite H1; auto.
  solve_ineqs.
Qed.

Lemma RecVarUnderRefPretype_subst : forall {pt f ks knd obj n},
    debruijn_subst_ext_conds f ks knd obj ->
    knd <> SPretype ->
    RecVarUnderRefPretype (subst'_pretype f pt) n true ->
    RecVarUnderRefPretype pt n true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f ks knd obj n,
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            RecVarUnderRefPretype (subst'_pretype f pt) n true ->
            RecVarUnderRefPretype pt n true)
       (fun t =>
          forall f ks knd obj n,
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            RecVarUnderRefTyp (subst'_type f t) n true ->
            RecVarUnderRefTyp t n true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - constructor.
    match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    eauto.
  - unfold get_var' in *.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> _ _], H' : context[_ <> _],
        H'' : context[_ _ _ zero] |- _ ] =>
      rewrite H' in H''; auto
    end.
  - constructor.
    match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    rewrite Forall_forall; intros.
    match goal with
    | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
      specialize (in_map F _ _ H');
      let H'' := fresh "H" in intro H'';
      rewrite Forall_forall in H; specialize (H _ H'')
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    eauto.
  - constructor.
  - constructor.
    match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; [ | | eauto ]
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- auto.
  - constructor.
  - constructor.
    match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; [ | | eauto ]
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- auto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Inductive equal_in_first_comp {A B C : Type} : list (A * B *  C) -> list (A * B * C) -> Prop :=
| eifc_nil : equal_in_first_comp [] []
| eifc_cons :
    forall a b c b' c' l l',
      equal_in_first_comp l l' ->
      equal_in_first_comp ((a, b, c) :: l) ((a, b', c') :: l').

Lemma first_comp_eifc : forall {A B C} {idx} {l : list (A * B * C)} {l' : list (A * B * C)},
    equal_in_first_comp l l' ->
    option_map (fun '(sz, _, _) => sz) (nth_error l idx) =
    option_map (fun '(sz, _, _) => sz) (nth_error l' idx).
Proof.
  induction idx; intros; simpl in *.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
Qed.

Lemma eifc_refl : forall {A B C} {l : list (A * B * C)},
    equal_in_first_comp l l.
Proof.
  induction l; intros; simpl in *.
  - constructor.
  - destruct_prs.
    constructor; auto.
Qed.

Lemma sizeOfPretype_subst_no_effect_provable : forall {pt f ks knd obj tctx tctx'},
    debruijn_subst_ext_conds f ks knd obj ->
    knd <> SPretype ->
    equal_in_first_comp tctx tctx' ->
    sizeOfPretype tctx (subst'_pretype f pt) =
    sizeOfPretype tctx' pt.
Proof.
  eapply
    (Pretype_ind'
       (fun pt =>
          forall f ks knd obj tctx tctx',
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            equal_in_first_comp tctx tctx' ->
            sizeOfPretype tctx (subst'_pretype f pt) =
            sizeOfPretype tctx' pt)
       (fun t =>
          forall f ks knd obj tctx tctx',
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            equal_in_first_comp tctx tctx' ->
            sizeOfType tctx (subst'_type f t) =
            sizeOfType tctx' t)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> _ _], H' : context[_ <> _] |- _ ] =>
      rewrite H'; simpl; auto
    end.
    apply first_comp_eifc; auto.
  - match goal with
    | [ |- fold_size ?A = fold_size ?B ] =>
      replace B with A; auto
    end.
    rewrite map_map.
    apply map_ext_in.
    intros.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    eauto.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- auto.
    -- constructor; auto.
  - match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- auto.
    -- auto.
Qed.

Lemma sizeOfPretype_subst_no_effect : forall {pt f ks knd obj tctx},
    debruijn_subst_ext_conds f ks knd obj ->
    knd <> SPretype ->
    sizeOfPretype tctx (subst'_pretype f pt) =
    sizeOfPretype tctx pt.
Proof.
  intros.
  eapply sizeOfPretype_subst_no_effect_provable; eauto.
  apply eifc_refl.
Qed.

Lemma LocValid_subst_loc : forall {f ks l l' lctx},
    debruijn_subst_ext_conds f ks SLoc l' ->
    ks SLoc <= lctx ->
    LocValid lctx (subst'_loc f l) ->
    LocValid (lctx + 1) l.
Proof.
  intros.
  destruct l; simpl in *.
  2:{ econstructor; eauto. }
  unfold get_var' in *.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  assert (Hltgt : v = ks SLoc \/ v <> ks SLoc) by apply eq_dec_nat.
  case Hltgt; intros; subst.
  -- econstructor 2; eauto.
     lia.
  -- rewrite H2 in *; simpl in *; auto.
     unfold shift_down_after in *.
     unfold zero in *.
     simpl in *.
     match goal with
     | [ H : context[if ?B then _ else _] |- _ ] =>
       destruct B
     end.
     all:
       match goal with
       | [ H : LocValid _ _ |- _ ] => inversion H; subst
       end.
     all:
       match goal with
       | [ H : @Logic.eq Loc _ _ |- _ ] => inversion H; subst
       end.
     all: econstructor 2; eauto.
     all: lia.
Qed.

Lemma qual_fctx_subst_weak_loc' : forall {kvs label ret qual size type location linear},
    typing.qual
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
    =
    typing.qual
      (add_constraints
         {|
           label := label;
           ret := ret;
           qual := qual;
           size := size;
           type := type;
           location := location;
           linear := linear
         |} kvs).
Proof.
  intros.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_loc_no_effect_on_quals; [ | apply single_weak_debruijn_weak_conds ].
  erewrite weak_loc_no_effect_on_quals; [ | apply single_weak_debruijn_weak_conds ].
  auto.
Qed.

Lemma type_fctx_subst_weak_loc' : forall {kvs label ret qual size type location linear},
    typing.type
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
    =
    typing.type
      (add_constraints
         {|
           label := label;
           ret := ret;
           qual := qual;
           size := size;
           type := type;
           location := location;
           linear := linear
         |} kvs).
Proof.
  intros.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_loc_no_effect_on_size; [ | apply single_weak_debruijn_weak_conds ].
  erewrite weak_loc_no_effect_on_qual; [ | apply single_weak_debruijn_weak_conds ].
  auto.
Qed.

Lemma size_fctx_subst_weak_loc' : forall {kvs label ret qual size type location linear},
    typing.size
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
    =
    typing.size
      (add_constraints
         {|
           label := label;
           ret := ret;
           qual := qual;
           size := size;
           type := type;
           location := location;
           linear := linear
         |} kvs).
Proof.
  intros.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_loc_no_effect_on_sizes; [ | apply single_weak_debruijn_weak_conds ].
  erewrite weak_loc_no_effect_on_sizes; [ | apply single_weak_debruijn_weak_conds ].
  auto.
Qed.

Lemma location_fctx_subst_weak_loc : forall {kvs label ret qual size type location linear},
    typing.location
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
    =
    (typing.location
       (add_constraints
          {|
            label := label;
            ret := ret;
            qual := qual;
            size := size;
            type := type;
            location := location;
            linear := linear
          |} kvs)
       + 1).
Proof.
  intros.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  lia.
Qed.

Lemma KindVarValid_subst_weak_loc : forall {kv kvs label ret qual size type location linear},
    KindVarValid
      (add_constraints
         {|
           label := label;
           ret := ret;
           qual := qual;
           size := size;
           type := type;
           location := location;
           linear := linear
         |} kvs)
      kv ->
    KindVarValid
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
      kv.
Proof.
  intros.
  destruct kv; simpl in *; auto.
  - rewrite qual_fctx_subst_weak_loc'; auto.
  - rewrite size_fctx_subst_weak_loc'; auto.
  - rewrite qual_fctx_subst_weak_loc'.
    rewrite size_fctx_subst_weak_loc'; auto.
Qed.

Lemma KindVarsValid_subst_weak_loc : forall {kvs' kvs label ret qual size type location linear},
    KindVarsValid
      (add_constraints
         {|
           label := label;
           ret := ret;
           qual := qual;
           size := size;
           type := type;
           location := location;
           linear := linear
         |} kvs)
      kvs' ->
    KindVarsValid
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            {|
              label := label;
              ret := ret;
              qual := qual;
              size := size;
              type := type;
              location := location + 1;
              linear := linear
            |}) kvs)
      kvs'.
Proof.
  induction kvs'; intros; simpl in *; constructor; inversion H; subst.
  - apply KindVarValid_subst_weak_loc; auto.
  - rewrite <-add_constraints_snoc.
    eapply IHkvs'.
    rewrite add_constraints_snoc; auto.
Qed.

Lemma add_constraints_app : forall {kvs2 F kvs1},
    add_constraints (add_constraints F kvs1) kvs2 =
    add_constraints F (kvs1 ++ kvs2).
Proof.
  apply
    (rev_ind
       (fun kvs2 =>
          forall F kvs1,
            add_constraints (add_constraints F kvs1) kvs2 =
            add_constraints F (kvs1 ++ kvs2))).
  all: intros; simpl in *.

  - rewrite app_nil_r; auto.
  - rewrite add_constraints_snoc.
    rewrite app_assoc.
    rewrite add_constraints_snoc.
    rewrite H; auto.
Qed.

Lemma ks_of_kvs_app : forall {kvs2 kvs1},
    ks_of_kvs (kvs1 ++ kvs2) =
    fold_right
      (fun kv ks' =>
         plus (sing (kind_of_kindvar kv) 1) ks')
      (ks_of_kvs kvs1)
      kvs2.
Proof.
  apply
    (rev_ind
       (fun kvs2 =>
          forall kvs1,
            ks_of_kvs (kvs1 ++ kvs2) =
            fold_right
              (fun kv ks' =>
                 plus (sing (kind_of_kindvar kv) 1) ks')
              (ks_of_kvs kvs1)
              kvs2)).
  all: intros; simpl in *.

  - rewrite app_nil_r; auto.
  - rewrite fold_right_snoc.
    rewrite app_assoc.
    rewrite ks_of_kvs_snoc.
    rewrite H.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    rewrite fold_right_plus_comm.
    unfold plus.
    auto.
Qed.

Lemma TypeValid_subst_loc_provable :
  (forall F t,
      TypeValid F t ->
      forall f kvs l F' F'' t',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        t = subst_ext' f t' ->
        F = add_constraints F'' kvs ->
        F' = add_constraints F'' (LOC :: kvs) ->
        TypeValid F' t') /\
  (forall F t,
      HeapTypeValid F t ->
      forall f kvs l F' F'' t',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        t = subst_ext' f t' ->
        F = add_constraints F'' kvs ->
        F' = add_constraints F'' (LOC :: kvs) ->
        HeapTypeValid F' t') /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f kvs l F' F'' t',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        t = subst_ext' f t' ->
        F = add_constraints F'' kvs ->
        F' = add_constraints F'' (LOC :: kvs) ->
        ArrowTypeValid F' t') /\
  (forall F t,
      FunTypeValid F t ->
      forall f kvs l F' F'' t',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        t = subst_ext' f t' ->
        F = add_constraints F'' kvs ->
        F' = add_constraints F'' (LOC :: kvs) ->
        FunTypeValid F' t').
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.

  Ltac start_tsl_subgoal :=
    destyp; simpl in *;
    match goal with
    | [ H : QualT _ _ = _ |- _ ] => inversion H; subst
    end;
    match goal with
    | [ X : Pretype |- _ ] => destruct X; simpl in *
    end;
    match goal with
    | [ H : @Logic.eq Pretype _ _ |- _ ] =>
      inversion H; subst;
      try unfold get_var' in H;
      try erewrite sloc_on_spretype_var in H; eauto;
      inversion H; subst
    end.
  Ltac simpl_under_qual :=
    match goal with
    | [ H : context[subst'_qual (under' _ _) _] |- _ ] =>
      erewrite qual_debruijn_subst_ext in H;
        [ | | eapply debruijn_subst_ext_under_knd ];
        eauto; solve_ineqs
    end.
  Ltac simpl_normal_qual H :=
    erewrite qual_debruijn_subst_ext in H;
    eauto; solve_ineqs.
  Ltac simpl_normal_size H :=
    erewrite size_debruijn_subst_ext in H;
    eauto; solve_ineqs.
  Ltac simpl_qualvalid :=
    match goal with
    | [ H : QualValid _ (subst'_qual _ _) |- _ ] =>
      simpl_normal_qual H
    end.
  Ltac simpl_qualleq :=
    match goal with
    | [ H : QualLeq _ (subst'_qual _ _) _ = Some _ |- _ ] =>
      simpl_normal_qual H
    | [ H : QualLeq _ _ (subst'_qual _ _) = Some _ |- _ ] =>
      simpl_normal_qual H
    end.

  all: try start_tsl_subgoal.

  Ltac handle_qctx :=
    rewrite qual_fctx_subst_weak_loc'; eauto.
  Ltac handle_tctx :=
    rewrite type_fctx_subst_weak_loc'; eauto.
  Ltac handle_szctx :=
    rewrite size_fctx_subst_weak_loc'; eauto.
  all: destruct F''; subst; simpl in *.

  - econstructor; eauto.
    simpl_qualvalid.
    handle_qctx.
  - simpl_qualvalid.
    simpl_qualleq.
    econstructor; simpl in *.
    3:{
      handle_tctx.
    }
    -- handle_qctx.
    -- handle_qctx.
    -- handle_qctx.
  - destyp.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = _ |- _ ] => inversion H; subst
    end.
    simpl_qualvalid.
    simpl_qualvalid.
    repeat simpl_under_qual.
    simpl_qualleq.
    simpl_qualleq.
    match goal with
    | [ H : sizeOfPretype _ _ = _ |- _ ] => simpl_normal_qual H
    end.
    econstructor; eauto; simpl in *; auto.
    -- handle_qctx.
    -- handle_qctx.
    -- handle_qctx.
    -- handle_qctx.
    -- handle_qctx.
    -- eapply RecVarUnderRefPretype_subst; [ | | eauto ].
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- handle_tctx.
       erewrite <-sizeOfPretype_subst_no_effect; [ eauto | | ].
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- handle_szctx.
    -- match goal with
       | [ H : forall _ _ _ _, _ |- _ ] => eapply H
       end.
       --- match goal with
           | [ H : debruijn_subst_ext_conds ?F (ks_of_kvs ?KVS) _ ?L |- _ ] =>
             let H' := fresh "H" in
             assert (H' : debruijn_subst_ext_conds (under' SPretype F) (ks_of_kvs (KVS ++ [TYPE sz q Heapable])) SLoc L); eauto
           end.
           rewrite ks_of_kvs_snoc.
           simpl.
           eapply debruijn_subst_ext_under_knd; eauto.
       --- simpl.
           erewrite qual_debruijn_subst_ext;
             [ | | eapply debruijn_subst_ext_under_knd ];
             eauto; solve_ineqs.
       --- rewrite add_constraints_snoc.
           simpl.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       --- rewrite add_constraints_snoc; simpl.
           auto.
  - econstructor; eauto.
    simpl.
    handle_qctx.
    simpl_qualvalid.
  - econstructor; eauto; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- handle_qctx.
       rewrite Forall_forall.
       intros.
       destyp.
       match goal with
       | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
         specialize (in_map F _ _ H');
         let H'' := fresh "H" in intro H'';
         rewrite Forall_forall in H; specialize (H _ H'')
       end.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H;
         specialize (H _ H')
       end.
       simpl in *.
       simpl_qualleq.
       simpl_qualleq.
    -- prepare_Forall.
       match goal with
       | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
         specialize (in_map F _ _ H');
         let H'' := fresh "H" in intro H'';
         rewrite Forall_forall in H; specialize (H _ H'')
       end.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H; specialize (H _ H')
       end.
       match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
  - constructor; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
  - constructor; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- rewrite location_fctx_subst_weak_loc.
       eapply LocValid_subst_loc; eauto.
       rewrite add_constraints_to_ks_of_kvs; simpl.
       lia.
  - constructor; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- rewrite location_fctx_subst_weak_loc.
       eapply LocValid_subst_loc; eauto.
       rewrite add_constraints_to_ks_of_kvs; simpl.
       lia.
    -- match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
  - constructor; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- rewrite location_fctx_subst_weak_loc.
       eapply LocValid_subst_loc; eauto.
       rewrite add_constraints_to_ks_of_kvs; simpl.
       lia.
    -- match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
  - destyp.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    simpl_qualvalid.
    repeat simpl_under_qual.
    simpl_qualleq.
    econstructor; eauto; simpl in *.
    -- handle_qctx.
    -- handle_qctx.
    -- match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H
       end.
       --- match goal with
           | [ H : debruijn_subst_ext_conds ?F (ks_of_kvs ?KVS) _ ?L |- _ ] =>
             let H' := fresh "H" in
             assert (H' : debruijn_subst_ext_conds (under' SLoc F) (ks_of_kvs (KVS ++ [LOC])) SLoc L); eauto
           end.
           rewrite ks_of_kvs_snoc.
           simpl.
           eapply debruijn_subst_ext_under_knd; eauto.
       --- simpl.
           erewrite qual_debruijn_subst_ext;
             [ | | eapply debruijn_subst_ext_under_knd ];
             eauto; solve_ineqs.
       --- rewrite add_constraints_snoc; simpl; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - constructor; simpl.
    -- handle_qctx.
       simpl_qualvalid.
    -- handle_qctx.
       simpl_qualleq.
    -- rewrite location_fctx_subst_weak_loc.
       eapply LocValid_subst_loc; eauto.
       rewrite add_constraints_to_ks_of_kvs; simpl.
       lia.
  - Ltac start_htsl_subgoal :=
      match goal with
      | [ X : HeapType |- _ ] => destruct X; simpl in *
      end;
      match goal with
      | [ H : @Logic.eq HeapType _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    start_htsl_subgoal.
    econstructor; eauto.
    rewrite Forall_forall; intros.
    match goal with
    | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
      specialize (in_map F _ _ H');
      let H'' := fresh "H" in intro H'';
      rewrite Forall_forall in H; specialize (H _ H'')
    end.
    eauto.
  - start_htsl_subgoal.
    econstructor; eauto.
    rewrite Forall_forall; intros.
    match goal with
    | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
      specialize (in_map F _ _ H');
      let H'' := fresh "H" in intro H'';
      rewrite Forall_forall in H; specialize (H _ H'')
    end.
    destructAll.
    simpl in *.
    handle_tctx.
    handle_szctx.
    destruct_prs; simpl in *.
    match goal with
    | [ H : SizeValid _ _ |- _ ] => simpl_normal_size H
    end.
    match goal with
    | [ H : SizeLeq _ _ _ = _ |- _ ] => simpl_normal_size H
    end.
    destyp.
    simpl in *.
    eexists; repeat split.
    -- erewrite <-sizeOfPretype_subst_no_effect; [ eauto | | ].
       --- eauto.
       --- solve_ineqs.
    -- eauto.
    -- eauto.
    -- eauto.
    -- eauto.
  - start_htsl_subgoal.
    destyp.
    econstructor; eauto.
    simpl in *.
    handle_qctx.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    simpl_qualleq.
  - start_htsl_subgoal.
    econstructor; eauto; simpl in *.
    -- handle_szctx.
       match goal with
       | [ H : SizeValid _ _ |- _ ] => simpl_normal_size H
       end.
    -- handle_qctx.
       simpl_qualvalid.
    -- destyp.
       match goal with
       | [ H : forall _ _ _ _, _ |- _ ] => eapply H
       end.
       --- match goal with
           | [ H : debruijn_subst_ext_conds ?F (ks_of_kvs ?KVS) _ ?L |- _ ] =>
             let H' := fresh "H" in
             assert (H' : debruijn_subst_ext_conds (under' SPretype F) (ks_of_kvs (KVS ++ [TYPE s q Heapable])) SLoc L); eauto
           end.
           rewrite ks_of_kvs_snoc.
           simpl.
           eapply debruijn_subst_ext_under_knd; eauto.
       --- simpl.
           erewrite qual_debruijn_subst_ext;
             [ | | eapply debruijn_subst_ext_under_knd ];
             eauto; solve_ineqs.
       --- rewrite add_constraints_snoc; simpl; auto.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
           erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       --- rewrite add_constraints_snoc; simpl; auto.
  - match goal with
    | [ X : ArrowType |- _ ] => destruct X; simpl in *
    end.
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
    all: rewrite Forall_forall; intros.
    all:
      match goal with
      | [ H : Forall _ (map ?F _), H' : List.In _ _ |- _ ] =>
        specialize (in_map F _ _ H');
        let H'' := fresh "H" in intro H'';
        rewrite Forall_forall in H; specialize (H _ H'')
      end.
    all: eauto.
  - match goal with
    | [ X : FunType |- _ ] => destruct X; simpl in *
    end.
    match goal with
    | [ H : FunT _ _ = FunT _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
    -- match goal with
       | [ H : KindVarsValid _ (subst'_kindvars _ _) |- _ ] =>
         erewrite kindvars_debruijn_subst_ext in H; eauto; solve_ineqs
       end.
       eapply KindVarsValid_subst_weak_loc; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] => eapply H
       end.
       2: eauto.
       2:{
         erewrite kindvars_debruijn_subst_ext; [ | | | eauto ]; solve_ineqs.
         rewrite add_constraints_app; eauto.
       }
       2:{
         rewrite add_constraints_app; eauto.
       }
       rewrite ks_of_kvs_app.
       apply debruijn_subst_ext_under_kindvars; eauto.
Qed.

Lemma TypeValid_subst F tau l :
  TypeValid F (subst.subst'_type (debruijn.subst'_of (debruijn.ext subst.SLoc l debruijn.id)) tau) ->
  TypeValid (subst'_function_ctx (debruijn.subst'_of (debruijn.weak subst.SLoc)) (update_location_ctx (location F + 1) F)) tau.
Proof.
  intros.
  specialize TypeValid_subst_loc_provable.
  intro H'.
  destruct H' as [H' _].
  eapply H'; eauto.
  - assert (H'' : debruijn_subst_ext_conds (subst'_of (ext SLoc l id)) (ks_of_kvs []) SLoc l); eauto.
    apply simpl_debruijn_subst_ext_conds.
  - simpl; eauto.
  - simpl; auto.
Qed.

Lemma HeapTypeValid_debruijn_subst_SLoc : forall {F ht},
    HeapTypeValid F ht ->
    HeapTypeValid
      (debruijn.subst_ext (debruijn.weak subst.SLoc)
                          (update_location_ctx (location F + 1) F))
      (subst.subst'_heaptype
         (debruijn.subst'_of (debruijn.weak subst.SLoc)) ht).
Proof.
  intros.
  specialize TypeValid_subst_loc_provable.
  intro H'.
  destruct H' as [_ [H' _]].
  eapply H'; eauto.
  - assert (H'' : debruijn_subst_ext_conds (subst'_of (ext SLoc (LocV 0) id)) (ks_of_kvs []) SLoc (LocV 0)); eauto.
    apply simpl_debruijn_subst_ext_conds.
  - rewrite HeapTypeValid_debruijn_subst_weak; auto.
  - simpl; eauto.
  - simpl; auto.
Qed.

Lemma type_fctx_subst_weak_loc : forall {kvs F},
    type
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            (update_location_ctx (location F + 1) F)) kvs)
    =
    type (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_size_no_effect_on_size; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_qual_no_effect_on_qual; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma qual_fctx_subst_weak_pretype : forall {kvs sz q hc F},
    typing.qual
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SPretype))
            (update_type_ctx
               ((sz, q, hc) :: (type F)) F))
         kvs)
    =
    typing.qual
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma qual_fctx_subst_weak_loc : forall {kvs F},
    qual
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SLoc))
            (update_location_ctx (location F + 1) F)) kvs)
    =
    qual (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma size_fctx_subst_weak_pretype : forall {kvs sz q hc F},
    typing.size
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SPretype))
            (update_type_ctx
               ((sz, q, hc) :: (type F)) F))
         kvs)
    =
    typing.size
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_size_no_effect_on_sizes; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_size_no_effect_on_sizes; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma type_fctx_subst_weak_pretype : forall {kvs sz q hc F},
    typing.type
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SPretype))
            (update_type_ctx
               ((sz, q, hc) :: (type F)) F))
         kvs)
    =
    typing.type
      (add_constraints
         (update_type_ctx
            ((sz, q, hc) :: (type F)) F)
         kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B; auto
  end.
  2:{
    apply eq_sym.
    rewrite <-map_id.
    apply map_ext.
    intros.
    destruct_prs.
    erewrite weak_non_size_no_effect_on_size; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
    erewrite weak_non_qual_no_effect_on_qual; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
    auto.
  }
  erewrite (weak_non_size_no_effect_on_size (f:=(subst'_of (weak SPretype)))); [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite (weak_non_qual_no_effect_on_qual (f:=(subst'_of (weak SPretype)))); [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma size_fctx_subst_weak_loc : forall {kvs F},
    size
      (add_constraints
         (subst'_function_ctx (subst'_of (weak SLoc))
                              (update_location_ctx (location F + 1) F)) kvs)
    =
    size (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  match goal with
  | [ |- context[map _ (map ?F ?L)] ] =>
    replace (map F L) with L; auto
  end.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  replace (subst'_sizes (subst'_of (weak SLoc))) with (fun (x : list Size) => x); auto.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  rewrite loc_weak_no_effect_on_sizes; auto.
Qed.

Lemma loc_fctx_subst_weak_pretype : forall {kvs sz q hc F},
    typing.location
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SPretype))
            (update_type_ctx
               ((sz, q, hc) :: (type F)) F))
         kvs)
    =
    typing.location
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl; auto.
Qed.

Lemma loc_fctx_subst_weak_sloc : forall {kvs F},
    location
      (add_constraints
         (subst'_function_ctx (subst'_of (weak SLoc))
                              (update_location_ctx (location F + 1) F)) kvs)
    =
    (location (add_constraints F kvs)) + 1.
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl; lia.
Qed.

Lemma nth_error_shift_down_appliable : forall {v A} {l : list A} {v' l'},
    v <> v' ->
    l' = remove_nth l v' ->
    nth_error l' (shift_down_after v v' 0) = nth_error l v.
Proof.
  intros; subst.
  eapply nth_error_shift_down; eauto.
Qed.

Lemma remove_nth_prefix : forall {A} {l : list A} {el l'},
    remove_nth (l ++ (el :: l')) (length l) = l ++ l'.
Proof.
  induction l; simpl; auto.
  intros.
  rewrite IHl; auto.
Qed.

Lemma remove_nth_prefix_appliable : forall {idx} {A} {l : list A} {el l'},
    idx = length l ->
    remove_nth (l ++ (el :: l')) idx = l ++ l'.
Proof.
  intros; subst; eapply remove_nth_prefix; eauto.
Qed.

Lemma nth_error_prefix : forall {A} {l : list A} {el l'},
    nth_error (l ++ (el :: l')) (length l) = Some el.
Proof.
  induction l; simpl; auto.
Qed.

Lemma nth_error_prefix_appliable : forall {idx} {A} {l : list A} {el l'},
    idx = length l ->
    nth_error (l ++ (el :: l')) idx = Some el.
Proof.
  intros; subst; eapply nth_error_prefix; eauto.
Qed.

Lemma length_collect_tctx_gen : forall {kvs kvs'},
    length (fold_left add_constraint_to_tctx kvs kvs') =
    (length kvs') + (ks_of_kvs kvs SPretype).
Proof.
  induction kvs; simpl; auto.
  intros.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl; auto
  end.
  all: rewrite IHkvs; try rewrite map_length; unfold plus; simpl; auto.
Qed.

Lemma length_collect_tctx : forall kvs,
    length (collect_tctx kvs) = (ks_of_kvs kvs SPretype).
Proof.
  intros.
  unfold collect_tctx.
  match goal with
  | [ |- length (fold_left _ _ ?X) = ?A ] =>
    replace A with ((length X) + A) by ltac:(simpl; lia)
  end.
  apply length_collect_tctx_gen.
Qed.

Lemma length_collect_szctx_gen : forall {kvs kvs'},
    length (fold_left add_constraint_to_szctx kvs kvs') =
    (length kvs') + (ks_of_kvs kvs SSize).
Proof.
  induction kvs; simpl; auto.
  intros.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl; auto
  end.
  all: rewrite IHkvs; try rewrite map_length; unfold plus; simpl; auto.
  rewrite map_length.
  lia.
Qed.

Lemma length_collect_szctx : forall kvs,
    length (collect_szctx kvs) = (ks_of_kvs kvs SSize).
Proof.
  intros.
  unfold collect_szctx.
  match goal with
  | [ |- length (fold_left _ _ ?X) = ?A ] =>
    replace A with ((length X) + A) by ltac:(simpl; lia)
  end.
  apply length_collect_szctx_gen.
Qed.

Lemma nth_error_app_appliable : forall {A} {idx} {el : A} {l1 l2},
    idx = length l1 ->
    nth_error (l1 ++ el :: l2) idx = Some el.
Proof.
  induction idx; intros.
  - destruct l1; simpl in *; auto.
    match goal with
    | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
    end.
  - destruct l1; simpl in *; auto.
    match goal with
    | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
    end.
Qed.

Lemma weak_pretype_on_qctx : forall qctx,
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (subst'_of (weak SPretype)) qs1,
          subst'_quals (subst'_of (weak SPretype)) qs2))
      qctx
    =
    qctx.
Proof.
  intros.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_qual_no_effect_on_quals;
    [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_qual_no_effect_on_quals;
    [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma weak_pretype_on_tctx : forall {A} {tctx : list (Size * Qual * A)},
    map
      (fun '(s, q, hc) =>
         (subst'_size (subst'_of (weak SPretype)) s,
         subst'_qual (subst'_of (weak SPretype)) q,
          hc))
      tctx
    =
    tctx.
Proof.
  intros.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite subst_size_weak_id.
  rewrite pretype_weak_no_effect_on_qual; auto.
Qed.

Lemma weak_loc_on_tctx : forall {A} {tctx : list (Size * Qual * A)},
    map
      (fun '(s, q, hc) =>
         (subst'_size (subst'_of (weak SLoc)) s,
         subst'_qual (subst'_of (weak SLoc)) q,
          hc))
      tctx
    =
    tctx.
Proof.
  intros.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite loc_weak_no_effect_on_size.
  rewrite loc_weak_no_effect_on_qual; auto.
Qed.

Lemma compose_weaks_weak : forall {knd ks},
    weaks' (plus (sing knd 1) ks) =
    weaks' ks ∘' subst'_of (weak knd).
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x; destruct knd; simpl in *; auto.
  all: unfold get_var'.
  all: unfold under_ks'.
  all: unfold weaks'.
  all: unfold var'.
  all: unfold var; simpl.
  all: unfold zero; rewrite Nat.add_0_r.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false;
      [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
    end.
  all: unfold plus.
  all:
    match goal with
    | [ |- ?F ?A = ?F ?B ] =>
      replace B with A; auto
    end.
  all: unfold sing; simpl.
  all: lia.
Qed.

Lemma RecVarUnderRefPretype_subst_non_pretype : forall {pt f v ks knd obj},
    debruijn_subst_ext_conds f ks knd obj ->
    knd <> SPretype ->
    RecVarUnderRefPretype pt v true ->
    RecVarUnderRefPretype (subst.subst'_pretype f pt) v true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f v ks knd obj,
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            RecVarUnderRefPretype pt v true ->
            RecVarUnderRefPretype (subst'_pretype f pt) v true)
       (fun t =>
          forall f v ks knd obj,
            debruijn_subst_ext_conds f ks knd obj ->
            knd <> SPretype ->
            RecVarUnderRefTyp t v true ->
            RecVarUnderRefTyp (subst'_type f t) v true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all: try now ltac:(econstructor; eauto).

  - match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> _ -> _],
        H' : context[_ <> _ _ -> _] |- _ ] => rewrite H; eauto
    end.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    simpl in *; eauto.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_subst_ext_under_knd; eauto.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma RecVarUnderRefPretype_weaks_non_pretype : forall {pt f v ks ks'},
    debruijn_weaks_conds f ks' ks ->
    ks SPretype = 0 ->
    RecVarUnderRefPretype pt v true ->
    RecVarUnderRefPretype (subst.subst'_pretype f pt) v true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            ks SPretype = 0 ->
            RecVarUnderRefPretype pt v true ->
            RecVarUnderRefPretype (subst.subst'_pretype f pt) v true)
       (fun t =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            ks SPretype = 0 ->
            RecVarUnderRefTyp t v true ->
            RecVarUnderRefTyp (subst.subst'_type f t) v true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all: try now ltac:(econstructor; eauto).

  - match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
  - unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
       end.
    -- match goal with
       | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       unfold zero; rewrite Nat.add_0_r.
       match goal with
       | [ H : ?X = 0 |- _ ] => rewrite H; simpl; auto
       end.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    simpl in *; eauto.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma qual_update_type_ctx : forall {F tctx},
    qual (update_type_ctx tctx F) = qual F.
Proof.
  destruct F; subst; simpl in *; auto.
Qed.

Lemma qual_update_tctx_add_constraints : forall {F tctx kvs},
    (qual
       (add_constraints
          (update_type_ctx tctx F) kvs))
    =
    qual (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl; auto.
Qed.

Lemma TypeValid_QualLeq_gen :
  (forall F t,
      TypeValid F t ->
      TypeValid F t /\
      forall pt q q',
        t = QualT pt q ->
        QualValid (qual F) q' ->
        QualLeq (qual F) q q' = Some true ->
        TypeValid F (QualT pt q')) /\
  (forall F t,
      HeapTypeValid F t -> HeapTypeValid F t) /\
  (forall F t,
      ArrowTypeValid F t -> ArrowTypeValid F t) /\
  (forall F t,
      FunTypeValid F t -> FunTypeValid F t).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; auto.
  all: try split.
  all: try now ltac:(econstructor; eauto).
  all: intros; simpl in *; auto.
  all:
    try match goal with
        | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
        end.
  all: try now ltac:(econstructor; eauto).

  9-10: prepare_Forall; destructAll; auto.

  all: destructAll; auto.
  
  - econstructor.
    3: eauto.
    all: auto.
    eapply QualLeq_Trans; eauto.
  - econstructor; eauto.
    eapply QualLeq_Trans; [ | eauto ]; eauto.
  - econstructor; eauto.
    prepare_Forall.
    destructAll; auto.
  - econstructor; eauto.
    1:{
      prepare_Forall.
      eapply QualLeq_Trans; [ | eauto ]; eauto.
    }
    prepare_Forall.
    destructAll; auto.
  - econstructor; eauto.
    eapply QualLeq_Trans; [ | eauto ]; eauto.
  - econstructor; eauto.
    eapply QualLeq_Trans; [ | eauto ]; eauto.
  - econstructor; eauto.
    prepare_Forall.
    destructAll; auto.
  - econstructor; eauto.
    prepare_Forall.
    destructAll.
    destruct_prs.
    simpl in *.
    eexists.
    split; eauto.
Qed.

Lemma TypeValid_QualLeq : forall {F pt q q'},
    QualValid (qual F) q' ->
    QualLeq (qual F) q q' = Some true ->
    TypeValid F (QualT pt q) ->
    TypeValid F (QualT pt q').
Proof.
  intros.
  specialize TypeValid_QualLeq_gen.
  let H' := fresh "H" in
  intro H'; destruct H' as [H' _].
  match goal with
  | [ H : forall _, _, H' : TypeValid _ _ |- _ ] =>
    specialize (H _ _ H')
  end.
  destructAll; eauto.
Qed.

Definition debruijn_under_conds f ks :=
  forall knd v' ks',
    v' < ks knd ->
    f knd v' ks' =
    subst.VarKind knd (ks' knd + v').

Lemma trivial_debruijn_under_conds : forall f,
    debruijn_under_conds f debruijn.zero.
Proof.
  unfold debruijn_under_conds.
  unfold zero.
  intros.
  match goal with
  | [ H : _ < 0 |- _ ] => inversion H
  end.
Qed.

Lemma debruijn_under_under_knd : forall {f ks knd},
    debruijn_under_conds f ks ->
    debruijn_under_conds
      (debruijn.under' knd f)
      (debruijn.plus (debruijn.sing knd 1) ks).
Proof.
  unfold debruijn_under_conds.
  intros.
  unfold under'.
  unfold under_ks'.
  unfold var'.
  unfold var.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    remember B as b;
    generalize (eq_sym Heqb); case b; intros; auto
  end.
  match goal with
  | [ H : forall _ _ _, _ |- _ ] => rewrite H
  end.
  2:{
    match goal with
    | [ |- _ - ?A < _ ] =>
      rewrite (Nat.add_lt_mono_r _ _ A)
    end.
    rewrite Nat.sub_add; [ | rewrite <-Nat.ltb_ge; auto ].
    unfold plus in *.
    rewrite Nat.add_comm; auto.
  }
  unfold plus.
  rewrite Nat.add_comm.
  rewrite Nat.add_assoc.
  rewrite Nat.sub_add; [ | rewrite <-Nat.ltb_ge; auto ].
  rewrite Nat.add_comm; auto.
Qed.

Lemma RecVarUnderRefPretype_weaks_gen : forall {pt f v ks ks'},
    debruijn_weaks_conds f ks' ks ->
    ks' SPretype <= v ->
    v < ks' SPretype + ks SPretype ->
    RecVarUnderRefPretype (subst'_pretype f pt) v true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            ks' SPretype <= v ->
            v < ks' SPretype + ks SPretype ->
            RecVarUnderRefPretype (subst'_pretype f pt) v true)
       (fun t =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            ks' SPretype <= v ->
            v < ks' SPretype + ks SPretype ->
            RecVarUnderRefTyp (subst'_type f t) v true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all: try now ltac:(econstructor; eauto).
  - unfold get_var'.
    unfold debruijn_weaks_conds in *.
    unfold Peano.ge in *.
    destructAll.
    match goal with
    | [ H : context[?F _ <= _ -> _]
        |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V)
        by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       match goal with
       | [ |- _ (TVar ?X) ?Y ?B ] =>
         replace B with (negb (X =? Y)); try now constructor
       end.
       match goal with
       | [ |- negb ?B = _ ] =>
         remember B as obj; generalize (eq_sym Heqobj);
         case obj; intros; auto
       end.
       match goal with
       | [ H : (_ =? _) = true |- _ ] =>
         apply beq_nat_true in H; subst
       end.
       lia.
    -- match goal with
       | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       match goal with
       | [ |- _ (TVar ?X) ?Y ?B ] =>
         replace B with (negb (X =? Y)); try now constructor
       end.
       match goal with
       | [ |- negb ?B = _ ] =>
         remember B as obj; generalize (eq_sym Heqobj);
         case obj; intros; auto
       end.
       match goal with
       | [ H : (_ =? _) = true |- _ ] =>
         apply beq_nat_true in H; subst
       end.
       lia.
  - econstructor.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    eauto.
  - econstructor.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus; simpl; lia.
    -- unfold plus; simpl; lia.
  - econstructor; eauto.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus; simpl; lia.
    -- unfold plus; simpl; lia.
Qed.   

Lemma RecVarUnderRefPretype_weaks : forall {pt v ks},
    v < ks SPretype ->
    RecVarUnderRefPretype (subst'_pretype (weaks' ks) pt) v true.
Proof.
  intros.
  eapply RecVarUnderRefPretype_weaks_gen; eauto.
  - apply simpl_debruijn_weak_conds.
  - unfold zero; lia.
  - unfold zero; simpl; auto.
Qed.
    
Lemma RecVarUnderRefPretype_subst_fwd : forall {pt v f ks pt'},
    debruijn_subst_ext_conds f ks SPretype pt' ->
    v < ks SPretype ->
    RecVarUnderRefPretype pt v true ->
    RecVarUnderRefPretype (subst.subst'_pretype f pt) v true.
Proof.
  apply (Pretype_ind'
           (fun pt =>
              forall v f ks pt',
                debruijn_subst_ext_conds f ks SPretype pt' ->
                v < ks SPretype ->
                RecVarUnderRefPretype pt v true ->
                RecVarUnderRefPretype
                  (subst.subst'_pretype f pt) v true)
           (fun t =>
              forall v f ks pt',
                debruijn_subst_ext_conds f ks SPretype pt' ->
                v < ks SPretype ->
                RecVarUnderRefTyp t v true ->
                RecVarUnderRefTyp
                  (subst.subst'_type f t) v true)
           (fun _ => True)
           (fun _ => True)
           (fun _ => True)).
  all: intros; simpl in *; eauto.
  - constructor; eauto.
    match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    eauto.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> ?X] |- context[_ SPretype ?Y _] ] =>
      let H' := fresh "H" in
      assert (H' : X = Y \/ X <> Y) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : context[?A ?B ?C _] |- context[?A ?B ?C _] ] =>
         rewrite H
       end.
       simpl.
       rewrite plus_zero.
       apply RecVarUnderRefPretype_weaks; auto.
    -- simpl.
       match goal with
       | [ |- _ (TVar ?X) ?Y ?B ] =>
         replace B with (negb (X =? Y)); try now constructor
       end.
       unfold zero.
       unfold shift_down_after; simpl.
       match goal with
       | [ |- context[?X <? ?Y] ] =>
         remember (X <? Y) as obj;
         generalize (eq_sym Heqobj); case obj; intros
       end.
       --- match goal with
           | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
             inversion H; subst; auto
           end.
       --- match goal with
           | [ H : ?A < ?B |- context[?C =? ?A] ] =>
             assert (B <= C)
           end.
           { rewrite Nat.ltb_ge in *.
             match goal with
             | [ |- ?X <= ?Y ] =>
               specialize (Nat.lt_ge_cases Y X)
             end.
             let H' := fresh "H" in intro H'; case H'; auto.
             intros.
             lia. }
           match goal with
           | [ H : ?A < ?B, H' : ?B <= ?C |- _ ] =>
             specialize (Nat.lt_le_trans _ _ _ H H')
           end.
           intros.
           match goal with
           | [ |- context[?X =? ?Y] ] =>
             remember (X =? Y) as obj2;
             generalize (eq_sym Heqobj2);
             case obj2; intros; simpl; auto
           end.
           match goal with
           | [ H : (_ =? _) = true |- _ ] =>
             apply beq_nat_true in H; subst
           end.
           exfalso; eapply Nat.lt_irrefl; eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
      inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H'); auto
    end.
  - econstructor; eauto.
  - econstructor; eauto.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- unfold plus; simpl.
       rewrite Nat.add_1_r.
       rewrite <-Nat.succ_lt_mono; auto.
    -- match goal with
       | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
         inversion H; subst; auto
       end.
  - econstructor.
  - econstructor; eauto.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_subst_ext_under_knd; eauto.
    -- unfold plus; simpl; auto.
    -- match goal with
       | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
         inversion H; subst; auto
       end.
  - econstructor.
  - econstructor.
  - econstructor.
Qed.

Lemma subst_size_only_size_matters : forall {sz ks ks'},
    ks SSize = ks' SSize ->
    subst.subst'_size (weaks' ks) sz = subst.subst'_size (weaks' ks') sz.
Proof.
  induction sz; intros; simpl in *; auto.
  - unfold get_var'.
    unfold weaks'.
    rewrite H; auto.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma subst_size_only_size_matters_gen : forall {f f' sz ks1 ks2 ks1' ks2'},
    debruijn_weaks_conds f ks1 ks2 ->
    debruijn_weaks_conds f' ks1' ks2' ->
    ks1 SSize = ks1' SSize ->
    ks2 SSize = ks2' SSize ->
    subst.subst'_size f sz = subst.subst'_size f' sz.
Proof.
  induction sz; intros; simpl in *; auto.
  - unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ < ?F _ -> _] |- context[_ SSize ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SSize \/ F SSize <= V) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H; auto | ]
    end.
    -- simpl.
       match goal with
       | [ H : context[_ < _ -> ?F _ _ _ = _] |- context[?F _ _ _] ] =>
         rewrite H; auto
       end.
       lia.
    -- do 2 match goal with
            | [ H : context[_ >= _ -> ?F _ _ _ = _] |- context[?F _ _ _] ] =>
              rewrite H; [ | lia ]
            end.
       simpl.
       match goal with
       | [ |- ?F ?A = ?F ?B ] => replace B with A; auto
       end.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma subst_size_weaks_zero_gen : forall sz ks,
    ks SSize = 0 ->
    subst'_size (weaks' ks) sz = sz.
Proof.
  induction sz; intros; simpl in *; auto.
  - unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    unfold zero.
    rewrite H.
    simpl; auto.
  - rewrite IHsz1; auto; rewrite IHsz2; auto.
Qed.

Lemma subst_sizes_weaks_zero_gen : forall szs ks,
    ks SSize = 0 ->
    subst'_sizes (weaks' ks) szs = szs.
Proof.
  induction szs; intros; simpl in *; auto.
  rewrite subst_size_weaks_zero_gen; auto.
  rewrite IHszs; auto.
Qed.

Lemma model_satisfies_context_from_idx_app2 : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {model ctx1 ctx2 idx},
    model_satisfies_context_from_idx
      leq lift_model model (ctx1 ++ ctx2) idx ->
    model_satisfies_context_from_idx
      leq lift_model model ctx2 ((length ctx1) + idx).
Proof.
  induction ctx1; intros; simpl in *; auto.
  rewrite plus_n_Sm.
  match goal with
  | [ H : forall _ _, _ |- _ ] =>
    eapply H; eauto
  end.
  destruct_prs; destructAll; auto.
Qed.

Definition acts_as_weak
           {A B}
           (lift_model : (nat -> B) -> (A -> B))
           (f : A -> A)
           (idx : nat) :=
  forall model obj,
    lift_model model (f obj) =
    lift_model (fun v => model (v + idx)) obj.

Lemma interp_size_weaks : forall ks,
    acts_as_weak interp_size (subst'_size (weaks' ks)) (ks SSize).
Proof.
  intros.
  unfold acts_as_weak.
  intros.
  match goal with
  | [ X : Size |- _ ] => induction X; intros; simpl in *; auto
  end.
  unfold zero; rewrite Nat.add_0_r.
  rewrite Nat.add_comm; auto.
Qed.

Lemma model_satisfies_context_add_constraints_gen : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {szctx idx model f idx'},
    acts_as_weak lift_model f idx' ->
    model_satisfies_context_from_idx
      leq lift_model model
      (map
         (fun '(szs0, szs1) =>
            (map f szs0, map f szs1))
         szctx)
      (idx' + idx) ->
    model_satisfies_context_from_idx
      leq lift_model (fun v : nat => model (v + idx'))
      szctx idx.
Proof.
  induction szctx; intros; simpl in *; auto.
  destruct_prs.
  destructAll.
  split; [ | split ].
  1-2: prepare_Forall.
  1-2:
    match goal with
    | [ H : Forall _ (map ?F ?L), H' : List.In ?X ?L |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : List.In (F X) (map F L)) by ltac:(apply in_map; auto);
      rewrite Forall_forall in H;
      specialize (H _ H0)
    end.
  1-2:
    match goal with
    | [ H : ?F ?A ?B |- ?F ?C ?D ] =>
      replace C with A; [ replace D with B; auto | ]
    end.
  all: try now ltac:(rewrite Nat.add_comm; auto).
  all: try now ltac:(apply eq_sym; auto).

  match goal with
  | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
  end.
  match goal with
  | [ H : ?F ?A ?B ?C ?D ?E |- ?F ?A ?B ?C ?D ?G ] =>
    replace G with E; auto
  end.
Qed.  

Lemma model_satisfies_context_add_constraints : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {prf f idx szctx model},
    idx = length prf ->
    acts_as_weak lift_model f idx ->
    model_satisfies_context
      leq lift_model model
      (prf
         ++
         map
         (fun '(szs0, szs1) =>
            (map f szs0, map f szs1))
         szctx) ->
    model_satisfies_context
      leq lift_model (fun v => model (v + idx)) szctx.
Proof.
  intros.
  unfold model_satisfies_context in *.
  match goal with
  | [ H : model_satisfies_context_from_idx _ _ _ _ _ |- _ ] =>
    apply model_satisfies_context_from_idx_app2 in H
  end.
  match goal with
  | [ H : context[?X], H' : _ = ?X |- _ ] =>
    rewrite <-H' in H
  end.
  eapply model_satisfies_context_add_constraints_gen; eauto.
Qed.
  
Lemma SizeLeq_add_constraints_gen : forall {prf szctx sz sz' ks},
    SizeLeq szctx sz sz' = Some true ->
    length prf = ks SSize ->
    SizeLeq
      (prf
         ++
         map
         (fun '(szs0, szs1) =>
            (subst'_sizes (weaks' ks) szs0,
             subst'_sizes (weaks' ks) szs1))
         szctx)
      (subst'_size (weaks' ks) sz)
      (subst'_size (weaks' ks) sz') =
    Some true.
Proof.
  intros.
  rewrite SizeLeq_desc in *.
  unfold ctx_imp_leq in *.
  intros.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    eapply model_satisfies_context_add_constraints in H; eauto
  end.
  2:{
    match goal with
    | [ H : ?A = ?B |- context[?A] ] => rewrite H
    end.
    apply interp_size_weaks.
  }
  rewrite interp_size_weaks.
  rewrite interp_size_weaks.
  match goal with
  | [ H : forall _, _ |- _ ] => apply H
  end.
  match goal with
  | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
  end.
Qed.

Lemma SizeLeq_add_constraints : forall {kvs szctx sz sz'},
  SizeLeq szctx sz sz' = Some true ->
  SizeLeq
  ((collect_szctx kvs)
     ++
     map
     (fun '(szs0, szs1) =>
        (subst'_sizes (weaks' (ks_of_kvs kvs)) szs0,
         subst'_sizes (weaks' (ks_of_kvs kvs)) szs1))
     szctx)
  (subst'_size (weaks' (ks_of_kvs kvs)) sz)
  (subst'_size (weaks' (ks_of_kvs kvs)) sz') =
  Some true.
Proof.
  intros.
  eapply SizeLeq_add_constraints_gen; eauto.
  apply length_collect_szctx; auto.
Qed.

Lemma option_map_nth_error : forall {A B} {f : A -> B} {idx l},
    option_map f (nth_error l idx)
    =
    nth_error (map f l) idx.
Proof.
  induction idx; intros; simpl in *; destruct l; simpl; auto.
Qed.

Lemma option_map_fold_size : forall {f l},
    f (SizeConst 0) = SizeConst 0 ->
    (forall sz1 sz2, f (SizePlus sz1 sz2) = SizePlus (f sz1) (f sz2)) ->
    option_map f (fold_size l) = fold_size (map (option_map f) l).
Proof.
  induction l; intros; simpl in *; auto.
  - rewrite H; auto.
  - destruct a; simpl; auto.
    rewrite <-IHl; auto.
    destruct (fold_size l); simpl; auto.
    rewrite H0; auto.
Qed.

Lemma map_length_eq : forall {A B C} {f : A -> B} {f' : C -> B} {l l'},
    map f l = map f' l' ->
    length l = length l'.
Proof.
  intros.
  erewrite <-map_length.
  apply eq_sym.
  erewrite <-map_length.
  rewrite H.
  eauto.
Qed.

Lemma sizeOfPretype_weaks_even_more_gen : forall {pt prf newtctx newtctx' tctx tctx' f ks ks'},
    length prf = ks SPretype ->
    length newtctx = ks' SPretype ->
    debruijn_weaks_conds f ks' ks ->
    map (fun '(sz, _, _) => sz) newtctx' =
    map (fun '(sz, _, _) => subst'_size f sz) newtctx ->
    map (fun '(sz, _, _) => sz) tctx' =
    map (fun '(sz, _, _) => subst'_size f sz) tctx ->
    sizeOfPretype (newtctx' ++ prf ++ tctx')
                  (subst'_pretype f pt)
    =
    option_map
      (fun sz => subst'_size f sz)
      (sizeOfPretype (newtctx ++ tctx) pt).
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall prf newtctx newtctx' tctx tctx' f ks ks',
            length prf = ks SPretype ->
            length newtctx = ks' SPretype ->
            debruijn_weaks_conds f ks' ks ->
            map (fun '(sz, _, _) => sz) newtctx' =
            map (fun '(sz, _, _) => subst'_size f sz) newtctx ->
            map (fun '(sz, _, _) => sz) tctx' =
            map (fun '(sz, _, _) => subst'_size f sz) tctx ->
            sizeOfPretype (newtctx' ++ prf ++ tctx')
                          (subst'_pretype f pt)
            =
            option_map
              (fun sz => subst'_size f sz)
              (sizeOfPretype (newtctx ++ tctx) pt))
       (fun t =>
          forall prf newtctx newtctx' tctx tctx' f ks ks',
            length prf = ks SPretype ->
            length newtctx = ks' SPretype ->
            debruijn_weaks_conds f ks' ks ->
            map (fun '(sz, _, _) => sz) newtctx' =
            map (fun '(sz, _, _) => subst'_size f sz) newtctx ->
            map (fun '(sz, _, _) => sz) tctx' =
            map (fun '(sz, _, _) => subst'_size f sz) tctx ->
            sizeOfType (newtctx' ++ prf ++ tctx')
                          (subst'_type f t)
            =
            option_map
              (fun sz => subst'_size f sz)
              (sizeOfType (newtctx ++ tctx) t))
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.

  - match goal with
    | [ X : NumType |- _ ] => destruct X
    end.
    all:
      match goal with
      | [ X : IntType |- _ ] => destruct X
      | [ X : FloatType |- _ ] => destruct X
      end.
    all: simpl; auto.
  - unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    rewrite option_map_option_map.
    rewrite option_map_nth_error.
    match goal with
    | [ H : context[_ < ?F _ -> _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H; auto | ]
    end.
    -- simpl.
       rewrite option_map_nth_error.
       rewrite map_app.
       rewrite nth_error_app1.
       2:{
         rewrite map_length.
         erewrite map_length_eq; eauto.
         lia.
       }
       rewrite map_app.
       rewrite nth_error_app1.
       2:{ rewrite map_length; lia. }
       match goal with
       | [ |- nth_error ?A _ = nth_error ?B _ ] =>
         replace B with A; auto
       end.
       match goal with
       | [ H : ?A = map ?F ?B |- ?A = map ?F2 ?B ] =>
         replace F2 with F; auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       destruct_prs; auto.
    -- match goal with
       | [ H : context[_ >= _ -> _] |- _ ] =>
         rewrite H; [ | lia ]
       end.
       simpl.
       rewrite option_map_nth_error.
       unfold zero; rewrite Nat.add_0_r.
       rewrite map_app.
       rewrite nth_error_app2.
       2:{
         rewrite map_length.
         erewrite map_length_eq; eauto.
         lia.
       }
       rewrite map_length.
       
       rewrite map_app.
       rewrite nth_error_app2.
       2:{
         rewrite map_length.
         match goal with
         | [ H : map _ ?A = map _ ?B |- _ <= _ + _ - length ?A ] =>
           replace (length A) with (length B); [ lia | ]
         end.
         eapply map_length_eq; eauto.
       }
       rewrite map_length.
       match goal with
       | [ |- context[?A + ?B - ?C - ?D] ] =>
         replace (A + B - C - D) with (B - C) by lia
       end.

       rewrite map_app.
       rewrite nth_error_app2.
       2:{ rewrite map_length; lia. }
       rewrite map_length.

       match goal with
       | [ H : map _ ?L = map _ ?L2 |- context[length ?L2] ] =>
         replace (length L2) with (length L)
       end.
       2:{ eapply map_length_eq; eauto. }
       
       match goal with
       | [ |- nth_error ?A _ = nth_error ?B _ ] =>
         replace B with A; auto
       end.
       match goal with
       | [ H : ?A = _ |- ?A = _ ] => rewrite H
       end.
       apply map_ext.
       intros.
       destruct_prs.
       auto.
  - rewrite map_map.
    rewrite option_map_fold_size; simpl; auto.
    match goal with
    | [ |- fold_size ?L = fold_size ?L2 ] =>
      replace L2 with L; auto
    end.
    rewrite map_map.
    apply map_ext_Forall.
    prepare_Forall.
    eauto.
  - do 2 rewrite app_comm_cons.
    
    match goal with
    | [ |- context[subst'_size ?F] ] =>
      match goal with
      | [ |- context[subst'_type ?F2] ] =>
        replace (subst'_size F) with (subst'_size F2)
      end
    end.
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      eapply subst_size_only_size_matters_gen.
      - eapply debruijn_weaks_conds_under_knd.
        eauto.
      - eauto.
      - unfold plus; simpl; lia.
      - unfold plus; simpl; lia.
    }
    match goal with
    | [ H : forall _, _ |- _ ] => eapply H; eauto
    end.
    all:
      try match goal with
          | [ |- context[subst'_size (under' ?K ?F)] ] =>
            replace (subst'_size (under' K F)) with (subst'_size F)
          end.
    all: try apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all: try ltac:(eapply subst_size_only_size_matters_gen; [ eauto | | | ]).
    all: try eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus; simpl; lia.
    -- simpl.
       match goal with
       | [ H : ?A = ?B |- ?C :: ?A = ?C :: ?B ] =>
         rewrite H; auto
       end.
  - match goal with
    | [ |- context[subst'_size ?F] ] =>
      match goal with
      | [ |- context[subst'_type ?F2] ] =>
        replace (subst'_size F) with (subst'_size F2)
      end
    end.
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      eapply subst_size_only_size_matters_gen.
      - eapply debruijn_weaks_conds_under_knd.
        eauto.
      - eauto.
      - unfold plus; simpl; lia.
      - unfold plus; simpl; lia.
    }
    match goal with
    | [ H : forall _, _ |- _ ] => eapply H
    end.
    3:{ eapply debruijn_weaks_conds_under_knd; eauto. }
    all: auto.
    all:
      match goal with
      | [ |- context[subst'_size (under' ?K ?F)] ] =>
        replace (subst'_size (under' K F)) with (subst'_size F); auto
      end.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all: eapply subst_size_only_size_matters_gen; [ eauto | | | ].
    all: try eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma sizeOfPretype_weaks_gen : forall {pt prf newtctx newtctx' tctx tctx' f ks ks'},
    length prf = ks SPretype ->
    length newtctx = ks' SPretype ->
    debruijn_weaks_conds f ks' ks ->
    Forall2
      (fun '(sz1, _, _) '(sz2, _, _) =>
         subst'_size f sz1 = sz1 /\
         subst'_size f sz2 = sz2 /\
         sz1 = sz2)
      newtctx
      newtctx' ->
    map (fun '(sz, _, _) => sz) tctx' =
    map (fun '(sz, _, _) => subst'_size f sz) tctx ->
    sizeOfPretype (newtctx' ++ prf ++ tctx')
                  (subst'_pretype f pt)
    =
    option_map
      (fun sz => subst'_size f sz)
      (sizeOfPretype (newtctx ++ tctx) pt).
Proof.
  intros.
  eapply sizeOfPretype_weaks_even_more_gen; eauto.
  match goal with
  | [ H : Forall2 _ _ _ |- _ ] => revert H
  end.
  clear.
  let H := fresh "H" in intro H; induction H; simpl; auto.
  destruct_prs.
  destructAll.
  match goal with
  | [ H : _ = _, H' : _ = _ |- _ ] => rewrite H; rewrite H'; auto
  end.
Qed.

Lemma length_prf : forall {A} {n} {l : list A},
    length l >= n ->
    exists l' l'',
      l = l' ++ l'' /\
      length l' = n.
Proof.
  induction n; intros.
  1:{ exists [], l; simpl; auto. }
  destruct l; simpl in *.
  1:{ lia. }
  apply le_S_n in H.
  specialize (IHn _ H).
  destructAll.
  do 2 eexists.
  rewrite app_comm_cons.
  split; eauto.
Qed.

Lemma sizeOfPretype_weaks_less_gen : forall {f pt tctx ks ks'},
    debruijn_weaks_conds f ks ks' ->
    ks' SPretype = 0 ->
    length tctx >= ks SPretype ->
    sizeOfPretype
      (map
         (fun '(sz, q, hc) => (subst'_size f sz, q, hc))
         tctx)
      (subst'_pretype f pt)
    =
    option_map (subst'_size f)
               (sizeOfPretype tctx pt).
Proof.
  intros.
  match goal with
  | [ H : _ >= _ |- _ ] => specialize (length_prf H)
  end.
  intros; destructAll.
  match goal with
  | [ |- context[map _ (?A ++ ?B)] ] =>
    replace (A ++ B) with (A ++ [] ++ B) at 1 by auto
  end.
  repeat rewrite map_app.
  eapply sizeOfPretype_weaks_even_more_gen; simpl; eauto.
  all: clear.
  all:
    match goal with
    | [ X : list _ |- _ ] => induction X; auto
    end.
  all: simpl.
  all: destruct_prs.
  all:
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H; auto
    end.
Qed.

Lemma sizeOfPretype_weaks : forall {pt prf tctx tctx' ks},
    length prf = ks SPretype ->
    map (fun '(sz, _, _) => sz) tctx' =
    map (fun '(sz, _, _) => subst'_size (weaks' ks) sz) tctx ->
    sizeOfPretype (prf ++ tctx')
                  (subst'_pretype (weaks' ks) pt)
    =
    option_map
      (fun sz => subst'_size (weaks' ks) sz)
      (sizeOfPretype tctx pt).
Proof.
  intros.
  replace (prf ++ tctx') with ([] ++ prf ++ tctx') by auto.
  replace tctx with ([] ++ tctx) by auto.
  eapply sizeOfPretype_weaks_gen; eauto.
  2:{ apply simpl_debruijn_weak_conds. }
  auto.
Qed.

Lemma fold_size_Some : forall {l sz},
    fold_size l = Some sz ->
    Forall (fun obj => exists sz, obj = Some sz) l.
Proof.
  induction l; auto.
  intros; simpl in *.
  match goal with
  | [ X : option _ |- _ ] => destruct X; simpl in *
  end.
  2:{
    match goal with
    | [ H : None = Some _ |- _ ] => inv H
    end.
  }
  constructor; eauto.
  match goal with
  | [ H : context[fold_size ?L], H' : forall _, _ |- _ ] =>
    remember (fold_size L) as obj;
    generalize (eq_sym Heqobj); revert H H';
    case obj; intros; eauto
  end.
Qed.

Lemma fold_size_Some_exists : forall {l},
    Forall (fun obj => exists sz, obj = Some sz) l ->
    exists sz, fold_size l = Some sz.
Proof.
  induction l; intros; simpl in *; eauto.
  match goal with
  | [ H : Forall _ _ |- _ ] => inv H
  end.
  destructAll.
  match goal with
  | [ H : ?A -> _, H' : ?A |- _ ] => specialize (H H')
  end.
  destructAll.
  match goal with
  | [ H : ?A = Some _ |- _ ] => rewrite H
  end.
  eauto.
Qed.

Lemma SizeLeq_SizePlus : forall {szctx sz1 sz2 sz1' sz2'},
    SizeLeq szctx sz1 sz1' = Some true ->
    SizeLeq szctx sz2 sz2' = Some true ->
    SizeLeq szctx (SizePlus sz1 sz2) (SizePlus sz1' sz2')
    = Some true.
Proof.
  do 5 intro.
  repeat rewrite SizeLeq_desc.
  unfold ctx_imp_leq.
  intros.
  repeat match goal with
         | [ H : forall _, _,
             H' : model_satisfies_context _ _ _ _ |- _ ] =>
           specialize (H _ H')
         end.
  simpl.
  lia.
Qed.

Lemma SizeValid_apply_weaks : forall {sz szctx szctx' ks},
    SizeValid szctx sz ->
    length szctx' = ks SSize + length szctx ->
    SizeValid szctx' (subst'_size (weaks' ks) sz).
Proof.
  induction sz.
  all: intros.
  all:
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] => inv H
    end.
  - simpl.
    unfold get_var'.
    unfold weaks'.
    unfold debruijn.var.
    simpl.
    unfold zero.
    rewrite Nat.add_0_r.
    match goal with
    | [ |- SizeValid ?L (SizeVar ?V) ] =>
        assert (exists obj, nth_error L V = Some obj)
    end.
    {
      apply nth_error_some_exists.
      match goal with
      | [ H : ?A = _ |- context[?A] ] => rewrite H
      end.
      match goal with
      | [ |- ?A + ?B < ?A + ?C ] =>
          assert (B < C); [ | lia ]
      end.
      eapply nth_error_Some.
      match goal with
      | [ H : ?A = _ |- context[?A] ] => rewrite H
      end.
      solve_ineqs.
    }
    destructAll.
    econstructor 3; eauto.
  - simpl.
    econstructor 2; eauto.
  - simpl.
    econstructor 1; eauto.
Qed.

Lemma fold_size_SizeValid_inv : forall {l szctx sz},
    fold_size l = Some sz ->
    SizeValid szctx sz ->
    Forall
      (fun obj =>
         exists sz',
           obj = Some sz' /\
           SizeValid szctx sz')
      l.
Proof.
  induction l; auto.
  intros.
  simpl in *.
  match goal with
  | [ X : option Size |- _ ] => destruct X
  end.
  2:{
    match goal with
    | [ H : None = Some _ |- _ ] => inv H
    end.
  }
  match goal with
  | [ |- context[_ :: ?L] ] =>
      remember (fold_size L) as obj; destruct obj; intros
  end.
  2:{
    match goal with
    | [ H : None = Some _ |- _ ] => inv H
    end.
  }
  match goal with
  | [ H : Some _ = Some _ |- _ ] => inv H
  end.
  match goal with
  | [ H : SizeValid _ _ |- _ ] => inv H
  end.
  all:
    match goal with
    | [ H : SizePlus _ _ = _ |- _ ] => inv H
    end.
  match goal with
  | [ H : forall _ _, Some ?SZ = _ -> _,
      H' : SizeValid _ ?SZ |- _ ] =>
      specialize (H _ _ eq_refl H')
  end.
  constructor; auto.
  eauto.
Qed.

Lemma sizeOfPretype_subst : forall {pt ks newtctx tctx tctx' sz q hc partsz wholesz pt' szctxprf szctx f},
    debruijn_subst_ext_conds f ks SPretype pt' ->
    sizeOfPretype (newtctx ++ (subst'_size (weaks' ks) sz, q, hc) :: tctx') pt = Some wholesz ->
    SizeValid
        (szctxprf ++
             map
             (fun '(szs0, szs1) =>
                (subst'_sizes (weaks' ks) szs0,
                 subst'_sizes (weaks' ks) szs1))
             szctx)
        wholesz ->
    length szctxprf = ks SSize ->
    sizeOfPretype tctx pt' = Some partsz ->
    SizeValid szctx partsz ->
    SizeValid szctx sz ->
    SizeLeq szctx partsz sz = Some true ->
    length newtctx = ks SPretype ->
    map (fun '(sz, q, hc) => sz) tctx' =
    map (fun '(sz, q, hc) => subst.subst'_size (weaks' ks) sz)
        tctx ->
    exists newwholesz,
      sizeOfPretype (newtctx ++ tctx') (subst'_pretype f pt)
      =
      Some newwholesz /\
      SizeValid
        (szctxprf ++
             map
             (fun '(szs0, szs1) =>
                (subst'_sizes (weaks' ks) szs0,
                 subst'_sizes (weaks' ks) szs1))
             szctx)
        newwholesz /\
      SizeLeq
        (szctxprf ++
             map
             (fun '(szs0, szs1) =>
                (subst'_sizes (weaks' ks) szs0,
                 subst'_sizes (weaks' ks) szs1))
             szctx)
        newwholesz
        wholesz
      =
      Some true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall ks newtctx tctx tctx' sz q hc partsz wholesz pt' szctxprf szctx f,
            debruijn_subst_ext_conds f ks SPretype pt' ->
            sizeOfPretype (newtctx ++ (subst'_size (weaks' ks) sz, q, hc) :: tctx') pt = Some wholesz ->
            SizeValid
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                wholesz ->
            length szctxprf = ks SSize ->
            sizeOfPretype tctx pt' = Some partsz ->
            SizeValid szctx partsz ->
            SizeValid szctx sz ->
            SizeLeq szctx partsz sz = Some true ->
            length newtctx = ks SPretype ->
            map (fun '(sz, q, hc) => sz) tctx' =
            map (fun '(sz, q, hc) => subst.subst'_size (weaks' ks) sz)
                tctx ->
            exists newwholesz,
              sizeOfPretype (newtctx ++ tctx') (subst'_pretype f pt)
              =
              Some newwholesz /\
              SizeValid
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                newwholesz /\
              SizeLeq
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                newwholesz
                wholesz
              =
              Some true)
       (fun t =>
          forall ks newtctx tctx tctx' sz q hc partsz wholesz pt' szctxprf szctx f,
            debruijn_subst_ext_conds f ks SPretype pt' ->
            sizeOfType (newtctx ++ (subst'_size (weaks' ks) sz, q, hc) :: tctx') t = Some wholesz ->
            SizeValid
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                wholesz ->
            length szctxprf = ks SSize ->
            sizeOfPretype tctx pt' = Some partsz ->
            SizeValid szctx partsz ->
            SizeValid szctx sz ->
            SizeLeq szctx partsz sz = Some true ->
            length newtctx = ks SPretype ->
            map (fun '(sz, q, hc) => sz) tctx' =
            map (fun '(sz, q, hc) => subst.subst'_size (weaks' ks) sz)
                tctx ->
            exists newwholesz,
              sizeOfType (newtctx ++ tctx') (subst'_type f t)
              =
              Some newwholesz /\
              SizeValid
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                newwholesz /\
              SizeLeq
                (szctxprf ++
                     map
                     (fun '(szs0, szs1) =>
                        (subst'_sizes (weaks' ks) szs0,
                         subst'_sizes (weaks' ks) szs1))
                     szctx)
                newwholesz
                wholesz
              =
              Some true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.

  all: try now ltac:(eexists; split; eauto; split; auto; apply SizeLeq_Refl).
  
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> ?V2 -> _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V = V2 \/ V <> V2) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : context[?A ?B ?C _] |- context[?A ?B ?C _] ] =>
         rewrite H
       end.
       simpl.
       rewrite plus_zero.
       erewrite sizeOfPretype_weaks; eauto.
       match goal with
       | [ H : ?X = Some _ |- context[?X] ] => rewrite H; simpl
       end.
       eexists; split; eauto.
       split.
       --- eapply SizeValid_apply_weaks; eauto.
           rewrite app_length.
           rewrite map_length.
           lia.
       --- match goal with
           | [ H : option_map _ ?X = Some _ |- _ ] =>
             remember X as obj; revert H; generalize (eq_sym Heqobj);
             case obj; intros; simpl in *;
             match goal with
             | [ H' : _ = Some _ |- _ ] => inv H'
             end
           end.
           destruct_prs.
           match goal with
           | [ H : nth_error _ _ = Some _ |- _ ] =>
             rewrite nth_error_prefix_appliable in H; auto; inv H
           end.
           apply SizeLeq_add_constraints_gen; auto.
    -- simpl.
       erewrite nth_error_shift_down_appliable; auto.
       2:{
         match goal with
         | [ H : ?A = ?B |- context[?B] ] => rewrite <-H
         end.
         apply eq_sym.
         eapply remove_nth_prefix.
       }
       match goal with
       | [ H : option_map _ _ = Some ?X |- _ ] => exists X
       end.
       split; eauto.
       split; auto.
       apply SizeLeq_Refl.
  - rewrite map_map.
    match goal with
    | [ H : context[fold_size (map ?F ?L)],
        H'' : debruijn_subst_ext_conds _ ?KS _ _
        |- context[fold_size (map ?F2 ?L)] ] =>
      match goal with
      | [ |- context[SizeLeq ?CTX _ _] ] =>
        let H' := fresh "H" in
        assert (H' :
                  Forall
                    (fun t =>
                       exists subsz,
                         F t = Some subsz /\
                         exists newsubsz,
                           F2 t = Some newsubsz /\
                           SizeValid CTX newsubsz /\
                           SizeLeq CTX newsubsz subsz
                           =
                           Some true)
                    L);
        [ | revert H' ]
      end
    end.
    { prepare_Forall.
      match goal with
      | [ H : fold_size _ = Some ?SZ, H' : SizeValid _ ?SZ |- _ ] =>
        specialize (fold_size_SizeValid_inv H H')
      end.
      intros.
      match goal with
      | [ H : Forall _ (map ?F ?L), H' : List.In ?X ?L |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : List.In (F X) (map F L)) by ltac:(apply in_map; auto);
        rewrite Forall_forall in H; specialize (H _ H0)
      end.
      destructAll.
      eexists; split; eauto. }
    match goal with
    | [ H : fold_size _ = Some ?X |- _ ] => revert H
    end.
    match goal with
    | [ H : SizeValid _ ?SZ |- context[SizeLeq _ _ ?SZ] ] =>
        revert H; revert SZ
    end.
    clear.
    match goal with
    | [ |- forall _, _ -> _ -> Forall _ ?L -> _ ] =>
      induction L; intros; simpl in *
    end.
    1:{
      eexists; split; eauto.
      split; auto.
      apply SizeLeq_Refl.
    }
    match goal with
    | [ H : Forall _ _ |- _ ] => inv H
    end.
    destructAll.
    match goal with
    | [ H : ?X = Some _ |- context[?X] ] => rewrite H
    end.
    match goal with
    | [ H : context[?X], H' : ?X = Some _ |- _ ] =>
      rewrite H' in H
    end.
    match goal with
    | [ H : context[SizePlus] |- _ ] =>
      match type of H with
      | context[fold_size ?L] =>
        remember (fold_size L) as obj;
        revert H; generalize (eq_sym Heqobj); case obj; intros;
        match goal with
        | [ H' : _ = Some _ |- _ ] => inv H'
        end
      end
    end.
    match goal with
    | [ H : SizeValid _ (SizePlus _ _) |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizePlus _ _ = _ |- _ ] => inv H
      end.
    match goal with
    | [ H : forall _, _ -> _, H''' : SizeValid _ ?SZ,
        H' : fold_size _ = Some ?SZ, H'' : Forall _ _ |- _ ] =>
      specialize (H _ H''' H' H'')
    end.
    destructAll.
    match goal with
    | [ H : ?X = Some _ |- _ ] => rewrite H
    end.
    eexists; split; eauto; intros.
    split.
    -- econstructor 2; eauto.
    -- apply SizeLeq_SizePlus; auto.
  - rewrite app_comm_cons.
    match goal with
    | [ H : context[?F SSize] |- _ ] =>
      replace (F SSize) with
          ((plus (sing SPretype 1) F) SSize)
    end.
    2:{ unfold plus; simpl; lia. }
    match goal with
    | [ |- context[subst'_sizes (weaks' ?F)] ] =>
      replace (subst'_sizes (weaks' F)) with
          (subst'_sizes (weaks' (plus (sing SPretype 1) F)))
    end.
    2:{
      unfold subst'_sizes.
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      apply map_ext.
      intros.
      apply subst_size_only_size_matters.
      unfold plus; simpl; lia.
    }
    match goal with
    | [ H : forall _ _, _ |- _ ] => eapply H; eauto
    end.
    -- apply debruijn_subst_ext_under_knd; auto.
    -- rewrite <-app_comm_cons.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       match goal with
       | [ |- context[subst'_size (weaks' (plus (sing SPretype 1) ?F))] ] =>
         replace (subst'_size (@weaks' Ind Kind VarKind (plus (@sing Ind EqI SPretype 1) F))) with (subst'_size (weaks' F)); eauto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
    -- match goal with
       | [ |- context[subst'_sizes (weaks' (plus (sing SPretype 1) ?F))] ] =>
         replace (subst'_sizes (@weaks' Ind Kind VarKind (plus (@sing Ind EqI SPretype 1) F))) with (subst'_sizes (weaks' F)); eauto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       unfold subst'_sizes.
       apply map_ext.
       intros.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
    -- unfold plus; simpl.
       match goal with
       | [ H : ?A = _ |- context[?A] ] => rewrite H; auto
       end.
    -- match goal with
       | [ H : ?A = _ |- ?A = _ ] => rewrite H
       end.
       apply map_ext.
       intros.
       destruct_prs.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
  - match goal with
    | [ H : context[?F SSize] |- _ ] =>
      replace (F SSize) with
          ((plus (sing SLoc 1) F) SSize)
    end.
    2:{ unfold plus; simpl; lia. }
    match goal with
    | [ |- context[subst'_sizes (weaks' ?F)] ] =>
      replace (subst'_sizes (weaks' F)) with
          (subst'_sizes (weaks' (plus (sing SLoc 1) F)))
    end.
    2:{
      unfold subst'_sizes.
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      apply map_ext.
      intros.
      apply subst_size_only_size_matters.
      unfold plus; simpl; lia.
    }
    match goal with
    | [ H : forall _ _, _ |- _ ] => eapply H; eauto
    end.
    -- apply debruijn_subst_ext_under_knd; auto.
    -- match goal with
       | [ |- context[subst'_size (weaks' (plus (sing SLoc 1) ?F))] ] =>
         replace (subst'_size (@weaks' Ind Kind VarKind (plus (@sing Ind EqI SLoc 1) F))) with (subst'_size (weaks' F)); eauto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
    -- match goal with
       | [ |- context[subst'_sizes (weaks' (plus (sing ?KND 1) ?F))] ] =>
         replace (subst'_sizes (@weaks' Ind Kind VarKind (plus (@sing Ind EqI KND 1) F))) with (subst'_sizes (weaks' F)); eauto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       unfold subst'_sizes.
       apply map_ext.
       intros.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
    -- unfold plus; simpl.
       match goal with
       | [ H : ?A = _ |- context[?A] ] => rewrite H; auto
       end.
       apply map_ext.
       intros.
       destruct_prs.
       apply subst_size_only_size_matters.
       unfold plus; simpl; lia.
Qed.

Definition SizeLeq_tctx szctx (tctx' : list (Size * Qual * HeapableConstant)) (tctx : list (Size * Qual * HeapableConstant)) :=
  Forall2
    (fun '(sz1, q1, hc1) '(sz2, q2, hc2) =>
       SizeLeq szctx sz1 sz2 = Some true /\
       q1 = q2 /\
       hc1 = hc2)
    tctx'
    tctx.

Lemma SizeLeq_tctx_refl : forall szctx tctx,
    SizeLeq_tctx szctx tctx tctx.
Proof.
  intros.
  apply Forall_Forall2.
  prepare_Forall.
  destruct_prs.
  split; auto.
  apply SizeLeq_Refl.
Qed.

Lemma prove_using_unknown_lemma : forall {A B : Prop},
    B ->
    (B -> A /\ B) ->
    A.
Proof.
  intros.
  match goal with
  | [ H : ?B, H' : ?B -> _ |- _ ] => specialize (H' H)
  end.
  destructAll.
  auto.
Qed.

Lemma fold_size_SizeValid_SizeLeq_inv : forall {A} {l : list A} {szctx f1 f2 sz},
    fold_size (map f1 l) = Some sz ->
    Forall
      (fun obj =>
         exists sz' sz'',
           f1 obj = Some sz' /\
           SizeValid szctx sz' /\
           f2 obj = Some sz'' /\
           SizeValid szctx sz'' /\
           SizeLeq szctx sz'' sz' = Some true)
      l ->
    exists sz',
      fold_size (map f2 l) = Some sz' /\
      SizeValid szctx sz' /\
      SizeLeq szctx sz' sz = Some true.
Proof.
  induction l; intros; simpl in *.
  - eexists.
    split; eauto.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    split.
    -- econstructor; eauto.
    -- apply SizeLeq_Refl.
  - match goal with
    | [ X : ?A, F1 : ?A -> option _,
        H : context[map ?F] |- _ ] =>
        remember (F X) as obj; apply eq_sym in Heqobj; destruct obj
    end.
    2:{
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
    }
    match goal with
    | [ X : ?A, F1 : ?A -> option _,
        H : context[map ?F ?L] |- _ ] =>
        remember (fold_size (map F L)) as obj2; apply eq_sym in Heqobj2; destruct obj2
    end.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    match goal with
    | [ H : Forall _ _ |- _ ] => inv H
    end.
    eapply prove_using_unknown_lemma.
    {
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    intros.
    split; auto.
    destructAll.
    do 2 match goal with
         | [ H : ?A = _ |- context[?A] ] => rewrite H
         end.
    eexists; split; eauto.
    split.
    -- econstructor 2; eauto.
    -- match goal with
       | [ H : ?A = _, H' : ?A = _ |- _ ] =>
           rewrite H in H'; inv H'
       end.
       apply SizeLeq_SizePlus; auto.
Qed.

Definition sizes_substitutable szctx sz1 sz2 :=
  sz1 = sz2 \/ (SizeLeq szctx sz1 (SizeConst 0) = Some true /\ SizeValid szctx sz1) \/ (SizeValid szctx sz1 /\ SizeValid szctx sz2).

Lemma sizeOfPretype_SizeLeq_ctx : forall {pt szctx tctx tctx' sz},
    SizeLeq_tctx szctx tctx' tctx ->
    Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable szctx sz1 sz2) tctx' tctx ->
    sizeOfPretype tctx pt = Some sz ->
    SizeValid szctx sz ->
    exists sz',
      sizeOfPretype tctx' pt = Some sz' /\
      SizeValid szctx sz' /\
      SizeLeq szctx sz' sz = Some true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall szctx tctx tctx' sz,
            SizeLeq_tctx szctx tctx' tctx ->
            Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable szctx sz1 sz2) tctx' tctx ->
            sizeOfPretype tctx pt = Some sz ->
            SizeValid szctx sz ->
            exists sz',
              sizeOfPretype tctx' pt = Some sz' /\
              SizeValid szctx sz' /\
              SizeLeq szctx sz' sz = Some true)
       (fun t =>
          forall szctx tctx tctx' sz,
            SizeLeq_tctx szctx tctx' tctx ->
            Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable szctx sz1 sz2) tctx' tctx ->
            sizeOfType tctx t = Some sz ->
            SizeValid szctx sz ->
            exists sz',
              sizeOfType tctx' t = Some sz' /\
              SizeValid szctx sz' /\
              SizeLeq szctx sz' sz = Some true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all:
    try now
        ltac:(
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inv H; auto
      end;
      eexists; repeat split; eauto;
      try apply SizeLeq_Refl; try econstructor; eauto).

  - match goal with
    | [ X : NumType |- _ ] => destruct X
    end.
    1:
      match goal with
      | [ X : IntType |- _ ] => destruct X
      end.
    3:
      match goal with
      | [ X : FloatType |- _ ] => destruct X
      end.
    all:
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inv H
      end.
    all: eexists; split; eauto.
    all: split; [ | apply SizeLeq_Refl ].
    all: econstructor; eauto.
  - match goal with
    | [ H : option_map _ ?X = _ |- _ ] =>
      remember X as obj; generalize (eq_sym Heqobj); revert H;
      case obj; intros; simpl in *
    end.
    destruct_prs.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    match goal with
    | [ H : SizeLeq_tctx _ ?A ?B,
        H' : nth_error ?B ?V = _ |- _ ] =>
      let H'' := fresh "H" in
      assert (H'' : exists y, nth_error A V = Some y)
    end.
    { apply nth_error_some_exists.
      match goal with
      | [ H : SizeLeq_tctx _ ?A ?B |- _ ] =>
        replace (length A) with (length B)
      end.
      2:{ apply eq_sym; eapply Forall2_length; eauto. }
      eapply nth_error_Some_length; eauto. }
    destructAll.
    match goal with
    | [ H : ?X = _ |- _ ] => rewrite H
    end.
    simpl.
    destruct_prs.
    eexists; split; eauto.
    unfold SizeLeq_tctx in *.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H''' : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = _,
        H'' : nth_error ?L2 _ = _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'');
      specialize (forall2_nth_error _ _ _ _ _ _ H''' H' H'')
    end.
    intros; simpl in *; destructAll.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    split; auto.
    match goal with
    | [ H : sizes_substitutable _ _ _ |- _ ] => inv H; auto
    end.
    match goal with
    | [ H : _ \/ _ |- _ ] => inv H
    end.
    all: destructAll; auto.
  - eapply fold_size_SizeValid_SizeLeq_inv; eauto.
    match goal with
    | [ H : fold_size _ = Some ?SZ, H' : SizeValid _ ?SZ |- _ ] =>
        specialize (fold_size_SizeValid_inv H H')
    end.
    intros.
    prepare_Forall.
    match goal with
    | [ H : Forall _ (map ?F _), H' : List.In ?EL ?L |- _ ] =>
        specialize (in_map F _ _ H')
    end.
    intros.
    rewrite Forall_forall in *.
    match goal with
    | [ H : forall _, List.In _ ?L -> _, H' : List.In _ ?L |- _ ] =>
	  specialize (H _ H')
    end.
    destructAll.
    simpl in *.
    eapply prove_using_unknown_lemma.
    {
      match goal with
      | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    intros; split; auto.
    destructAll.
    do 2 eexists; eauto.
  - match goal with
    | [ H : forall _, _ |- _ ] => eapply H; eauto
    end.
    all: constructor; auto.
    -- split; auto.
       apply SizeLeq_Refl.
    -- left; auto.
Qed.

Lemma size_update_type_ctx : forall {F tctx},
    size (update_type_ctx tctx F) = size F.
Proof.
  destruct F; auto.
Qed.

Lemma location_update_type_ctx : forall {F tctx},
    location (update_type_ctx tctx F) = location F.
Proof.
  destruct F; auto.
Qed.

Lemma ks_of_kvs_subst_kindvars : forall {kvs su},
    ks_of_kvs (subst'_kindvars su kvs) =
    ks_of_kvs kvs.
Proof.
  induction kvs; simpl; auto.
  intros.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl
  end.
  all: rewrite IHkvs; auto.
Qed.

Lemma SizeValid_subst_weak_size : forall {sz f F kvs szs0 szs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
    SizeValid (size (add_constraints F kvs)) sz ->
    SizeValid
      (size
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SSize))
                                 (update_size_ctx ((szs0, szs1) :: size F) F))
            (subst'_kindvars (subst'_of (weak SSize)) kvs)))
      (subst'_size f sz).
Proof.
  induction sz.
  intros.
  - rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
    unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _],
        H'' : context[_ < ?KS _ -> ?F _ _ _ = _]
        |- SizeValid _ (?F ?KND ?V _) ] =>
      let H' := fresh "H" in
      assert (H' : V < KS KND \/ V >= KS KND) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H'' | rewrite H ]; auto
    end.
    all: simpl.
    all:
      match goal with
      | [ |- SizeValid ?L (SizeVar ?SZ) ] =>
        let H := fresh "H" in
        assert (H : SZ < length L);
        [ | apply nth_error_some_exists in H; destructAll;
            eapply SizeVarValid; eauto ]
      end.
    all: rewrite app_length.
    all: repeat rewrite map_length.
    all: rewrite length_collect_szctx.
    all: rewrite ks_of_kvs_subst_kindvars.
    -- lia.
    -- destruct F; subst; simpl in *.
       match goal with
       | [ H : SizeValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : SizeVar _ = _ |- _ ] => inv H
         end.
       match goal with
       | [ H : nth_error _ _ = Some _ |- _ ] =>
         apply nth_error_Some_length in H
       end.
       rewrite app_length in *.
       rewrite map_length in *.
       rewrite length_collect_szctx in *.
       lia.
  - intros.
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizePlus _ _ = _ |- _ ] => inv H
      end.
    eapply SizePlusValid; simpl; eauto.
  - econstructor; simpl; eauto.
Qed.

Lemma model_satisfies_context_from_idx_desc : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {model ctx idx},
    model_satisfies_context_from_idx leq lift_model model ctx idx <->
    (forall v l0 l1,
        nth_error ctx v = Some (l0, l1) ->
        Forall
          (fun obj =>
             leq (lift_model model obj) (model (idx + v)))
          l0 /\
        Forall
          (fun obj =>
             leq (model (idx + v)) (lift_model model obj))
          l1).
Proof.
  intros; split; revert idx; induction ctx; intros; simpl in *.
  - destruct v; simpl in *.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
  - destruct_prs; destructAll.
    destruct v; simpl in *.
    -- match goal with
       | [ H : Some _ = Some _ |- _ ] => inv H
       end.
       repeat rewrite Nat.add_0_r; auto.
    -- repeat rewrite <-Nat.add_succ_comm.
       apply IHctx; auto.
  - auto.
  - destruct_prs.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] =>
      generalize (H 0 _ _ eq_refl); intros; simpl in *
    end.
    destructAll.
    repeat rewrite Nat.add_0_r in *.
    split; auto.
    split; auto.
    apply IHctx; intros.
    repeat rewrite Nat.add_succ_comm.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => apply H
    end.
    simpl; auto.
Qed.

Lemma model_satisfies_context_desc : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {model ctx},
    model_satisfies_context leq lift_model model ctx <->
    (forall v l0 l1,
        nth_error ctx v = Some (l0, l1) ->
        Forall
          (fun obj =>
             leq (lift_model model obj) (model v))
          l0 /\
        Forall
          (fun obj =>
             leq (model v) (lift_model model obj))
          l1).
Proof.
  unfold model_satisfies_context.
  intros.
  rewrite model_satisfies_context_from_idx_desc.
  simpl; split; auto.
Qed.

Lemma ctx_imp_leq_map : forall {A B} {leq : B -> B -> Prop} {lift_model : (nat -> B) -> (A -> B)} {ctx ctx' obj1 obj2 f},
    (forall model,
        model_satisfies_context leq lift_model model ctx' ->
        exists model',
          model_satisfies_context leq lift_model model' ctx /\
          lift_model model' =
          (fun obj => lift_model model (f obj))) ->
    ctx_imp_leq leq lift_model ctx obj1 obj2 ->
    ctx_imp_leq leq lift_model ctx' (f obj1) (f obj2).
Proof.
  unfold ctx_imp_leq.
  intros.
  match goal with
  | [ H : forall _, model_satisfies_context _ _ _ _ -> _,
      H' : model_satisfies_context _ _ _ _ |- _ ] =>
    specialize (H _ H')
  end.
  destructAll.
  match goal with
  | [ H : forall _, model_satisfies_context _ _ _ ?A -> _,
      H' : model_satisfies_context _ _ _ ?A |- _ ] =>
    specialize (H _ H')
  end.
  match goal with
  | [ H : ?A = _, H' : context[?A] |- _ ] => rewrite H in H'; auto
  end.
Qed.

Lemma subst_weaks_weak_comm : forall {f ks knd},
    debruijn_weaks_conds f ks (sing knd 1) ->
    f ∘' (weaks' ks) =
    (weaks' ks) ∘' (subst'_of (weak knd)).
Proof.
  intros.
  unfold debruijn_weaks_conds in *.
  destructAll.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  simpl.
  unfold weak.
  unfold weaks.
  unfold weaks' at 1.
  destruct x; simpl.
  all: unfold get_var'.
  all: unfold under_ks'.
  all:
    do 2 match goal with
         | [ |- context[if ?A then _ else _] ] =>
           replace A with false; [ | apply eq_sym; rewrite OrdersEx.Nat_as_OT.ltb_ge; lia ]
         end.
  all: unfold weaks'; simpl.
  all:
    match goal with
    | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; try lia
    end.
  all: unfold var.
  all: simpl.
  all:
    match goal with
    | [ |- _ ?A = _ ?B ] => replace B with A; auto
    end.
  all: rewrite plus_zero.
  all: unfold zero.
  all: lia.
Qed.

Lemma SizeLeq_weaks_gen : forall {f ks' ks sz sz' szctx' prf szctx},
    debruijn_weaks_conds f ks' ks ->
    length szctx' = ks' SSize ->
    length prf = ks SSize ->
    SizeLeq (szctx' ++ szctx) sz sz' = Some true ->
    SizeLeq
      ((map
          (fun '(szs0, szs1) =>
             (subst'_sizes f szs0, subst'_sizes f szs1))
          szctx')
         ++
         prf
         ++
         map
         (fun '(szs2, szs3) =>
            (subst'_sizes f szs2, subst'_sizes f szs3))
         szctx)
      (subst'_size f sz)
      (subst'_size f sz') =
    Some true.
Proof.
  intros.
  rewrite SizeLeq_desc in *.
  eapply ctx_imp_leq_map; eauto.
  intros.
  match goal with
  | [ H : model_satisfies_context _ _ ?M _,
      H' : debruijn_weaks_conds _ ?KSP ?KS |- _ ] =>
    exists (fun v => M (if v <? KSP SSize then v else v + KS SSize))
  end.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B); [ | split; auto ]
  end.
  { apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with
    | [ H : debruijn_weaks_conds _ _ _ |- _ ] => revert H
    end.
    clear.
    match goal with
    | [ X : Size |- _ ] => induction X
    end.
    all: simpl in *; auto.
    unfold debruijn_weaks_conds.
    intros.
    destructAll.
    unfold get_var'.
    match goal with
    | [ |- context[?A <? ?B] ] =>
      remember (A <? B) as obj; specialize (eq_sym Heqobj); case obj; intros
    end.
    - rewrite OrdersEx.Nat_as_OT.ltb_lt in *.
      match goal with
      | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
      end.
    - rewrite OrdersEx.Nat_as_OT.ltb_ge in *.
      match goal with
      | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; auto
      end.
      simpl.
      unfold zero.
      rewrite <-plus_n_O.
      rewrite Nat.add_comm; auto. }
  
  rewrite model_satisfies_context_desc in *.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    rewrite model_satisfies_context_desc in H
  end.
  intros.
  match goal with
  | [ H : interp_size _ = _ |- _ ] => rewrite H
  end.
  match goal with
  | [ H : forall _ _ _, nth_error ?L _ = Some _ -> _,
      H' : nth_error _ ?IDX = Some (?L1, ?L2),
      H'' : debruijn_weaks_conds ?F ?KSP ?KS |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : nth_error
                   L
                   (if IDX <? KSP SSize then IDX else IDX + KS SSize)
                 =
                 Some
                   (subst'_sizes f L1,
                    subst'_sizes f L2));
    [ | specialize (H _ _ _ H0) ]
  end.
  { match goal with
    | [ |- context[?A <? ?B] ] =>
      remember (A <? B) as obj; specialize (eq_sym Heqobj); case obj; intros
    end.
    - rewrite OrdersEx.Nat_as_OT.ltb_lt in *.
      rewrite nth_error_app1 in *; try lia.
      2:{ rewrite map_length; lia. }
      erewrite nth_error_map; eauto.
      simpl; auto.
    - rewrite OrdersEx.Nat_as_OT.ltb_ge in *.
      rewrite nth_error_app2 in *; try lia.
      2:{ rewrite map_length; lia. }
      rewrite map_length.
      rewrite nth_error_app2 by lia.
      match goal with
      | [ H : nth_error _ ?IDX = Some _ 
          |- nth_error _ ?IDX2 = Some _ ] =>
        replace IDX2 with IDX by lia
      end.
      erewrite nth_error_map; eauto.
      simpl; auto. }
  destructAll.
  split; prepare_Forall.
  all: rewrite Forall_forall in *.
  all: unfold subst'_sizes in *.
  all:
    match goal with
    | [ H : context[List.In _ (map ?F ?B)], H' : List.In ?A ?B |- _ ] =>
      let H'' := fresh "H" in
      assert (H'' : List.In (F A) (map F B)) by ltac:(apply in_map; auto);
      specialize (H _ H''); auto
    end.
Qed.

Lemma SizeLeq_weaks : forall {ks sz sz' prf szctx},
    length prf = ks SSize ->
    SizeLeq szctx sz sz' = Some true ->
    SizeLeq
      (prf ++
           map
           (fun '(szs2, szs3) =>
              (subst'_sizes (weaks' ks) szs2,
               subst'_sizes (weaks' ks) szs3)) szctx)
      (subst'_size (weaks' ks) sz)
      (subst'_size (weaks' ks) sz') =
    Some true.
Proof.
  intros.
  match goal with
  | [ |- SizeLeq (?A ++ map ?F ?B) _ _ = _ ] =>
    replace (A ++ map F B) with (map F [] ++ A ++ map F B) by auto
  end.
  eapply SizeLeq_weaks_gen; eauto.
  - apply simpl_debruijn_weak_conds.
  - auto.
Qed.

Lemma TypeValid_SizeLeq_provable :
  (forall F t,
      TypeValid F t ->
      forall tctx,
        Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable (size F) sz1 sz2) tctx (type F) ->
        SizeLeq_tctx (size F) tctx (type F) ->
        TypeValid (update_type_ctx tctx F) t) /\
  (forall F t,
      HeapTypeValid F t ->
      forall tctx,
        Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable (size F) sz1 sz2) tctx (type F) ->
        SizeLeq_tctx (size F) tctx (type F) ->
        HeapTypeValid (update_type_ctx tctx F) t) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall tctx,
        Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable (size F) sz1 sz2) tctx (type F) ->
        SizeLeq_tctx (size F) tctx (type F) ->
        ArrowTypeValid (update_type_ctx tctx F) t) /\
  (forall F t,
      FunTypeValid F t ->
      forall tctx,
        Forall2 (fun '(sz1, _, _) '(sz2, _, _) => sizes_substitutable (size F) sz1 sz2) tctx (type F) ->
        SizeLeq_tctx (size F) tctx (type F) ->
        FunTypeValid (update_type_ctx tctx F) t).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl; subst; auto.
  - econstructor; eauto.
    rewrite qual_update_type_ctx; auto.
  - match goal with
    | [ H : nth_error ?L ?V = Some (?A, ?B, ?C),
        H' : SizeLeq_tctx _ ?LP ?L |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : exists y, nth_error LP V = Some (y, B, C))
    end.
    { match goal with
      | [ H : nth_error ?L ?V = Some (?A, ?B, ?C),
          H' : SizeLeq_tctx _ ?LP ?L |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : exists y, nth_error LP V = Some y)
      end.
      { unfold SizeLeq_tctx in *.
        apply nth_error_some_exists.
        match goal with
        | [ H : Forall2 _ _ _ |- _ ] =>
          apply Forall2_length in H; rewrite H
        end.
        eapply nth_error_Some_length; eauto. }
      destructAll.
      destruct_prs.
      unfold SizeLeq_tctx in *.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      intros; simpl in *.
      destructAll; subst.
      eexists; eauto. }
      
    destructAll.
    all: econstructor; eauto.
    all: try rewrite qual_update_type_ctx; eauto.
    rewrite type_update_type_ctx; eauto.
  - match goal with
    | [ H : sizeOfPretype (type ?F2) ?PT = Some ?SZ,
        H' : SizeLeq_tctx ?C _ _
        |- TypeValid ?F _ ] =>
      let H0 := fresh "H" in
      assert (H0 : exists sz',
                 sizeOfPretype (type F) PT = Some sz' /\
                 SizeValid (size F2) sz' /\
                 SizeLeq (size F2) sz' SZ = Some true)
    end.
    { eapply sizeOfPretype_SizeLeq_ctx; eauto.
      all: rewrite type_update_type_ctx; auto. }
    destructAll.
    econstructor; eauto.
    all: try rewrite qual_update_type_ctx; auto.
    1:{
      rewrite size_update_type_ctx; auto.
    } 
    rewrite type_update_type_ctx.
    match goal with
    | [ H : forall _, _ -> _ |- context[(?SZ, ?Q, ?HC) :: ?T] ] =>
      specialize (H ((SZ, Q, HC) :: T))
    end.
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { simpl.
      rewrite size_update_type_ctx.
      rewrite sizepairs_debruijn_weak_pretype.
      rewrite type_update_type_ctx.
      rewrite weak_pretype_on_tctx.
      constructor; auto.
      right; right.
      split; auto. }
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { simpl.
      rewrite size_update_type_ctx.
      rewrite sizepairs_debruijn_weak_pretype.
      rewrite type_update_type_ctx.
      rewrite weak_pretype_on_tctx.
      constructor; auto. }
    match goal with
    | [ H : TypeValid ?F ?T |- TypeValid ?F2 ?T ] =>
      replace F2 with F; auto
    end.
    match goal with
    | [ F : Function_Ctx |- _ ] => destruct F; subst; simpl in *
    end.
    unfold subst'_function_ctx in *.
    apply function_ctx_eq; simpl in *; auto.
    rewrite pretype_weak_no_effect_on_qual.
    rewrite pretype_weak_no_effect_on_size.
    rewrite weak_pretype_on_tctx; auto.
  - econstructor; eauto.
    rewrite qual_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- prepare_Forall.
       rewrite qual_update_type_ctx; auto.
    -- prepare_Forall.
       eauto.
  - econstructor; eauto.
    rewrite qual_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite location_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite location_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite location_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite qual_update_type_ctx; auto.
    -- match goal with
       | [ H : SizeLeq_tctx _ ?L _,
           H' : forall _, _ -> _ |- _ ] =>
         specialize (H' L)
       end.
       simpl in *.
       repeat rewrite sizepairs_debruijn_weak_loc in *.
       match goal with
       | [ H : ?A -> _ |- _ ] =>
         rewrite weak_loc_on_tctx in H
       end.
       rewrite update_location_ctx_no_effect_on_size_field in *.
       rewrite update_location_ctx_no_effect_on_type_field in *.
       match goal with
       | [ H : ?A -> _, H' : ?A |- _ ] =>
         specialize (H H')
       end.
       match goal with
       | [ H : ?A -> _, H' : ?A |- _ ] =>
         specialize (H H')
       end.
       match goal with
       | [ H : TypeValid ?F ?T |- TypeValid ?F2 ?T ] =>
         replace F2 with F; auto
       end.
       unfold subst'_function_ctx.
       match goal with
       | [ F : Function_Ctx |- _ ] => destruct F; subst; simpl in *
       end.
       apply function_ctx_eq; simpl in *; auto.
       --- rewrite sizepairs_debruijn_weak_loc; auto.
       --- rewrite weak_loc_on_tctx; auto.
  - econstructor; eauto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite qual_update_type_ctx; auto.
    -- rewrite location_update_type_ctx; auto.
  - econstructor; eauto.
    prepare_Forall.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    destructAll.
    rewrite type_update_type_ctx.
    rewrite size_update_type_ctx.
    destruct_prs; simpl in *.
    match goal with
    | [ X : Typ |- _ ] => destruct X; simpl in *
    end.
    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_SizeLeq_ctx; eauto.
    }
    intros; split; auto.
    destructAll.
    eexists; split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    eapply SizeLeq_Trans; eauto.
  - econstructor; eauto.
    rewrite qual_update_type_ctx; auto.
  - econstructor; eauto.
    -- rewrite size_update_type_ctx; auto.
    -- rewrite qual_update_type_ctx; auto.
    -- match goal with
       | [ H : forall _, _ -> _ |- context[(?SZ, ?Q, ?HC) :: ?T] ] =>
         specialize (H ((SZ, Q, HC) :: T))
       end.
       match goal with
       | [ H : ?A -> _ |- _ ] =>
         let H' := fresh "H" in
         assert (H' : A); [ | specialize (H H') ]
       end.
       { simpl.
         rewrite size_update_type_ctx.
         rewrite sizepairs_debruijn_weak_pretype.
         rewrite type_update_type_ctx.
         rewrite weak_pretype_on_tctx.
         rewrite type_update_type_ctx.
         constructor; auto.
         left; auto. }
       match goal with
       | [ H : ?A -> _ |- _ ] =>
         let H' := fresh "H" in
         assert (H' : A); [ | specialize (H H') ]
       end.
       { simpl.
         rewrite size_update_type_ctx.
         rewrite sizepairs_debruijn_weak_pretype.
         rewrite type_update_type_ctx.
         rewrite weak_pretype_on_tctx.
         rewrite type_update_type_ctx.
         constructor; auto.
         split; auto.
         apply SizeLeq_Refl. }
       match goal with
       | [ H : TypeValid ?F ?T |- TypeValid ?F2 ?T ] =>
         replace F2 with F; auto
       end.
       match goal with
       | [ F : Function_Ctx |- _ ] => destruct F; subst; simpl in *
       end.
       unfold subst'_function_ctx.
       apply function_ctx_eq; simpl in *; auto.
       rewrite pretype_weak_no_effect_on_qual.
       rewrite pretype_weak_no_effect_on_size.
       rewrite weak_pretype_on_tctx; auto.
  - econstructor; eauto.
    all: prepare_Forall; eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_Function_Ctx; eauto.
       --- rewrite qual_update_type_ctx; auto.
       --- rewrite size_update_type_ctx; auto.
    -- match goal with
       | [ H : forall _, _ -> _
           |- ArrowTypeValid (add_constraints (update_type_ctx ?L _) ?KVS) _ ] =>
         specialize
           (H
              ((collect_tctx KVS)
                 ++
                 (map
                    (fun '(sz, q, hc) =>
                       (subst'_size (weaks' (ks_of_kvs KVS)) sz,
                        subst'_qual (weaks' (ks_of_kvs KVS)) q,
                        hc))
                    L)))
       end.
       match goal with
       | [ H : ?A -> _ |- _ ] =>
         let H' := fresh "H" in assert (H' : A);
         [ | specialize (H H') ]
       end.
       {
         rewrite add_constraints_to_ks_of_kvs; simpl.
         apply Forall2_app.
         - apply forall2_nth_error_inv.
           2: auto.
           intros.
           match goal with
           | [ H : ?A = _, H' : ?A = _ |- _ ] =>
               rewrite H' in H; inv H
           end.
           destruct_prs.
           left; auto.
         - apply forall2_nth_error_inv.
           2: repeat rewrite map_length; eapply Forall2_length; eauto.
           intros.
           destruct_prs.
           do 2 match goal with
           | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
               apply nth_error_map_inv in H
           end.
           destructAll.
           destruct_prs.
           match goal with
           | [ H : (_,_,_) = (_,_,_), H' : (_,_,_) = (_,_,_) |- _ ] =>
               inv H; inv H'
           end.
           match goal with
           | [ H : Forall2 _ ?L1 ?L2,
               H' : nth_error ?L1 _ = _,
               H'' : nth_error ?L2 _ = _ |- _ ] =>
             specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
           end.
           intros; simpl in *.
           match goal with
           | [ H : sizes_substitutable _ _ _ |- _ ] => inv H
           end.
           1:{ left; auto. }
           destructAll.
           match goal with
           | [ H : _ \/ _ |- _ ] => inv H
           end.
           all: destructAll.
           -- right; left.
              split.
              --- match goal with
                  | [ |- SizeLeq _ (subst'_size ?SU _) ?SZ = _ ] =>
                      replace SZ with (subst'_size SU SZ) by auto
                  end.
                  apply SizeLeq_weaks; auto.
                  apply length_collect_szctx.
              --- eapply SizeValid_apply_weaks; eauto.
                  rewrite app_length.
                  rewrite length_collect_szctx.
                  rewrite map_length; auto.
           -- right; right.
              split.
              all: eapply SizeValid_apply_weaks; eauto.
              all: rewrite app_length.
              all: rewrite length_collect_szctx.
              all: rewrite map_length; auto.
       }
           
       match goal with
       | [ H : ?A -> _ |- _ ] =>
         let H' := fresh "H" in assert (H' : A);
         [ | specialize (H H') ]
       end.
       { rewrite add_constraints_to_ks_of_kvs; simpl.
         unfold SizeLeq_tctx.
         apply Forall2_app; [ apply SizeLeq_tctx_refl | ].
         apply forall2_nth_error_inv.
         2:{
           repeat rewrite map_length.
           eapply Forall2_length; eauto.
         }
         intros.
         destruct_prs.
         repeat match goal with
                | [ H : nth_error (map _ _) _ = _ |- _ ] =>
                  apply nth_error_map_inv in H
                end.
         destructAll.
         destruct_prs.
         repeat match goal with
                | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
                end.
         unfold SizeLeq_tctx in *.
         match goal with
         | [ H : Forall2 _ ?L1 ?L2,
             H' : nth_error ?L1 _ = _,
             H'' : nth_error ?L2 _ = _ |- _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
         end.
         simpl in *; auto.
         intros; destructAll; subst.
         split; auto.
         apply SizeLeq_add_constraints; auto. }
       match goal with
       | [ H : ArrowTypeValid ?F ?T |- ArrowTypeValid ?F2 ?T ] =>
         replace F2 with F; auto
       end.
       match goal with
       | [ F : Function_Ctx |- _ ] => destruct F; subst; simpl in *
       end.
       repeat rewrite add_constraints_to_ks_of_kvs.
       apply function_ctx_eq; simpl in *; auto.
Qed.

Lemma TypeValid_SizeLeq : forall {F sz sz' q hc tctx t},
    TypeValid F t ->
    type F = (sz, q, hc) :: tctx ->
    SizeLeq (size F) sz' sz = Some true ->
    sizes_substitutable (size F) sz' sz ->
    TypeValid (update_type_ctx ((sz', q, hc) :: tctx) F) t.
Proof.
  intros.
  specialize TypeValid_SizeLeq_provable.
  let H' := fresh "H" in intro H'; destruct H' as [H' _].
  match goal with
  | [ H : TypeValid _ _, H' : forall _ _, _ -> _ |- _ ] =>
    specialize (H' _ _ H); eapply H'; eauto
  end.
  - match goal with
    | [ H : ?X = _ |- context[?X] ] => rewrite H
    end.
    constructor; auto.
    apply forall2_nth_error_inv; auto.
    intros.
    match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] => rewrite H in H'; inv H'
    end.
    destruct_prs.
    left; auto.
  - match goal with
    | [ H : ?X = _ |- context[?X] ] => rewrite H
    end.
    constructor; auto.
    apply SizeLeq_tctx_refl.
Qed.  

Lemma pretype_subst_no_effect_on_kindvar : forall {kv f ks pt},
    debruijn_subst_ext_conds f ks SPretype pt ->
    subst.subst'_kindvar f kv = kv.
Proof.
  destruct kv.
  all: intros; simpl in *; auto.
  - do 2 ltac:(erewrite quals_debruijn_subst_ext; eauto; solve_ineqs).
  - do 2 ltac:(erewrite sizes_debruijn_subst_ext; eauto; solve_ineqs).
  - erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
Qed.
  
Lemma pretype_subst_no_effect_on_kindvars : forall {kvs f ks pt},
    debruijn_subst_ext_conds f ks SPretype pt ->
    subst.subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; simpl in *; auto.
  intros.
  erewrite pretype_subst_no_effect_on_kindvar; eauto.
  erewrite IHkvs; eauto.
  eapply debruijn_subst_ext_under_knd; eauto.
Qed.

Lemma sizeOfPretype_eifc : forall {pt tctx tctx'},
    equal_in_first_comp tctx tctx' ->
    sizeOfPretype tctx pt =
    sizeOfPretype tctx' pt.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall tctx tctx',
            equal_in_first_comp tctx tctx' ->
            sizeOfPretype tctx pt =
            sizeOfPretype tctx' pt)
       (fun t =>
          forall tctx tctx',
            equal_in_first_comp tctx tctx' ->
            sizeOfType tctx t =
            sizeOfType tctx' t)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.

  - match goal with
    | [ X : term.var |- _ ] => revert X
    end.
    match goal with
    | [ H : equal_in_first_comp _ _ |- _ ] => induction H; auto
    end.
    destruct v; simpl; auto.
  - match goal with
    | [ |- fold_size ?L = fold_size ?L2 ] =>
      replace L2 with L; auto
    end.
    apply map_ext_Forall.
    prepare_Forall; eauto.
  - eapply H.
    constructor; auto.
Qed.

Lemma sizeOfPretype_weaks_only_size_matters : forall {pt tctx f ks' ks},
    debruijn_weaks_conds f ks' ks ->
    ks SPretype = 0 ->
    sizeOfPretype tctx (subst'_pretype f pt) =
    sizeOfPretype tctx pt.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall tctx f ks' ks,
            debruijn_weaks_conds f ks' ks ->
            ks SPretype = 0 ->
            sizeOfPretype tctx (subst'_pretype f pt) =
            sizeOfPretype tctx pt)
       (fun t =>
          forall tctx f ks' ks,
            debruijn_weaks_conds f ks' ks ->
            ks SPretype = 0 ->
            sizeOfType tctx (subst'_type f t) =
            sizeOfType tctx t)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.

  - rewrite option_map_nth_error.
    unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H; auto | ]
    end.
    -- simpl.
       rewrite option_map_nth_error.
       auto.
    -- match goal with
       | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; [ | lia ]
       end.
       simpl.
       unfold zero; rewrite Nat.add_0_r.
       rewrite option_map_nth_error.
       match goal with
       | [ |- nth_error _ ?V = nth_error _ ?V2 ] =>
         replace V with V2; auto
       end.
       lia.
  - match goal with
    | [ |- fold_size ?L = fold_size ?L2 ] =>
      replace L2 with L; auto
    end.
    rewrite map_map.
    apply map_ext_Forall.
    prepare_Forall; eauto.
  - match goal with
    | [ |- sizeOfType ((?A, subst'_qual ?F ?B, ?C) :: ?L) ?T = _ ] =>
      replace (sizeOfType ((A, subst'_qual F B, C) :: L) T)
        with (sizeOfType ((A, B, C) :: L) T)
    end.
    2:{
      match goal with
      | [ X : Typ |- _ ] => destruct X; simpl
      end.
      apply sizeOfPretype_eifc.
      constructor; auto.
      apply eifc_refl.
    }
    match goal with
    | [ H : forall _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
  - match goal with
    | [ H : forall _, _ |- _ ] => eapply H; eauto
    end.
    eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma LocValid_subst_weak : forall {l f lctx lctx' ks' ks},
    LocValid lctx l ->
    debruijn_weaks_conds f ks' ks ->
    lctx' >= lctx + ks SLoc ->
    LocValid lctx' (subst'_loc f l).
Proof.
  intros.
  destruct l; simpl in *; auto.
  2:{ econstructor; eauto. }
  unfold get_var'.
  unfold debruijn_weaks_conds in *.
  destructAll.
  match goal with
  | [ H : LocValid _ _ |- _ ] =>
    inv H;
    match goal with
    | [ H : LocV _ = _ |- _ ] => inv H
    end
  end.
  match goal with
  | [ H : context[_ < ?F _ -> _] |- context[_ SLoc ?V _] ] =>
    let H' := fresh "H" in
    assert (H' : V < F SLoc \/ F SLoc <= V) by apply Nat.lt_ge_cases;
    case H'; intros; [ rewrite H; auto | ]
  end.
  - simpl.
    econstructor 2; eauto.
    lia.
  - match goal with
    | [ H : context[_ >= ?F _ -> _] |- context[_ SLoc ?V _] ] =>
      rewrite H; auto
    end.
    simpl.
    unfold zero; rewrite Nat.add_0_r.
    econstructor 2; eauto.
    lia.
Qed.

Lemma weak_loc_no_effect_on_kindvar : forall {kv ks f},
    debruijn_weaks_conds f ks (sing SLoc 1) ->
    subst'_kindvar f kv = kv.
Proof.
  destruct kv; simpl; auto.
  all: intros.
  all: repeat erewrite weak_loc_no_effect_on_qual; eauto.
  all: repeat erewrite weak_loc_no_effect_on_size; eauto.
  all: repeat erewrite weak_loc_no_effect_on_quals; eauto.
  all: repeat erewrite weak_loc_no_effect_on_sizes; eauto.
Qed.

Lemma weak_loc_no_effect_on_kindvars : forall {kvs ks f},
    debruijn_weaks_conds f ks (sing SLoc 1) ->
    subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; intros; simpl in *; auto.
  erewrite weak_loc_no_effect_on_kindvar; eauto.
  destruct a.
  all: erewrite IHkvs; auto.
  all: eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma size_update_location_ctx : forall {F lctx},
    size (update_location_ctx lctx F) = size F.
Proof.
  destruct F; auto.
Qed.

Lemma TypeValid_add_constraint_loc :
  (forall F t,
      TypeValid F t ->
      forall kvs f F'',
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SLoc 1) ->
        F = add_constraints F'' kvs ->
        TypeValid (add_constraints F'' (LOC :: kvs))
                  (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall kvs f F'',
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SLoc 1) ->
        F = add_constraints F'' kvs ->
        HeapTypeValid (add_constraints F'' (LOC :: kvs))
                      (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall kvs f F'',
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SLoc 1) ->
        F = add_constraints F'' kvs ->
        ArrowTypeValid (add_constraints F'' (LOC :: kvs))
                       (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall kvs f F'',
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SLoc 1) ->
        F = add_constraints F'' kvs ->
        FunTypeValid (add_constraints F'' (LOC :: kvs))
                     (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.
  all: try now ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs; econstructor; eauto; try rewrite qual_fctx_subst_weak_loc; auto).

  - unfold get_var'.
    all: try ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ]).
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    1:
      match goal with
      | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
      end.
    2:
      match goal with
      | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
      end.
    all: simpl.
    all: econstructor.
    4,8: rewrite qual_fctx_subst_weak_loc; eauto.
    all: try rewrite qual_fctx_subst_weak_loc; eauto.
    all: rewrite type_fctx_subst_weak_loc; eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_loc; eauto.
    -- erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- eapply RecVarUnderRefPretype_weaks_non_pretype; eauto.
       --- eapply debruijn_weaks_conds_under_knd; eauto.
       --- simpl; auto.
    -- rewrite type_fctx_subst_weak_loc; eauto.
       simpl.
       erewrite sizeOfPretype_weaks_only_size_matters; eauto.
       --- eapply debruijn_weaks_conds_under_knd; eauto.
       --- unfold sing; simpl; auto.
    -- rewrite add_constraints_to_ks_of_kvs in *.
       simpl in *.
       rewrite sizepairs_debruijn_weak_loc.
       rewrite size_update_location_ctx.
       auto.
    -- match goal with
       | [ H : forall _ _, _ |-
           context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)] ] =>
         match goal with
         | [ |- context[add_constraints _ ?KVS] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_pretype ?F _] ] =>
         match goal with
         | [ |- context[location ?C + 1] ] =>
           specialize (H F C)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc.
       all: simpl; auto.
       rewrite ks_of_kvs_app.
       simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_loc; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       erewrite weak_loc_no_effect_on_qual; eauto.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H; specialize (H _ H')
       end.
       simpl in *; auto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc; auto.
    -- rewrite loc_fctx_subst_weak_sloc.
       eapply LocValid_subst_weak; eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc; auto.
    -- rewrite loc_fctx_subst_weak_sloc.
       eapply LocValid_subst_weak; eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc; auto.
    -- rewrite loc_fctx_subst_weak_sloc.
       eapply LocValid_subst_weak; eauto.
  - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc.
       erewrite weak_loc_no_effect_on_qual; eauto.
    -- rewrite qual_fctx_subst_weak_loc.
       do 2 ltac:(try erewrite weak_loc_no_effect_on_qual; eauto).
       eapply debruijn_weaks_conds_under_knd; eauto.
    -- match goal with
       | [ H : forall _ _ _, _ |- context[add_constraints _ ?KVS] ] =>
         match goal with
         | [ |- context[subst'_pretype ?F _] ] =>
           match goal with
           | [ H' : QualValid (qual (add_constraints ?C _)) _ |- _ ] =>
             specialize (H (KVS ++ [LOC]) F C)
           end
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc; simpl; auto.
       rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc; auto.
    -- rewrite qual_fctx_subst_weak_loc; auto.
    -- rewrite loc_fctx_subst_weak_sloc.
       eapply LocValid_subst_weak; eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs; simpl.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    destructAll.
    rewrite type_fctx_subst_weak_loc.
    rewrite size_fctx_subst_weak_loc.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    erewrite sizeOfPretype_weaks_only_size_matters; eauto.
    eexists; split; eauto.
    erewrite weak_loc_no_effect_on_size; eauto.
  - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_loc.
       erewrite weak_loc_no_effect_on_qual; eauto.
  - econstructor; eauto.
    -- rewrite size_fctx_subst_weak_loc.
       erewrite weak_loc_no_effect_on_size; eauto.
    -- rewrite qual_fctx_subst_weak_loc.
       erewrite weak_loc_no_effect_on_qual; eauto.
    -- erewrite weak_loc_no_effect_on_size; eauto.
       erewrite weak_loc_no_effect_on_qual; eauto.
       match goal with
       | [ H : forall _ _, _ |-
           context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)] ] =>
         match goal with
         | [ |- context[add_constraints _ ?KVS] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_type ?F _] ] =>
         match goal with
         | [ |- context[location ?C + 1] ] =>
           specialize (H F C)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc; simpl; auto.
       rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
      end.
    all: eauto.
  - econstructor; eauto.
    -- erewrite weak_loc_no_effect_on_kindvars; eauto.
       eapply KindVarsValid_Function_Ctx; eauto.
       --- rewrite qual_fctx_subst_weak_loc; auto.
       --- rewrite size_fctx_subst_weak_loc; auto.
    -- erewrite weak_loc_no_effect_on_kindvars; eauto.
       rewrite add_constraints_app.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H
       end.
       --- rewrite ks_of_kvs_app.
           apply debruijn_weaks_conds_under_kindvars; auto.
       --- apply add_constraints_app.
Qed.

Lemma weak_pretype_no_effect_on_kindvar : forall {kv ks f},
    debruijn_weaks_conds f ks (sing SPretype 1) ->
    subst'_kindvar f kv = kv.
Proof.
  destruct kv; simpl; auto.
  all: intros.
  all: repeat erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  all: repeat erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
  all: repeat erewrite weak_non_qual_no_effect_on_quals; eauto; solve_ineqs.
  all: repeat erewrite weak_non_size_no_effect_on_sizes; eauto; solve_ineqs.
Qed.

Lemma weak_pretype_no_effect_on_kindvars : forall {kvs ks f},
    debruijn_weaks_conds f ks (sing SPretype 1) ->
    subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; intros; simpl in *; auto.
  erewrite weak_pretype_no_effect_on_kindvar; eauto.
  destruct a.
  all: erewrite IHkvs; auto.
  all: eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma RecVarUnderRefPretype_under_weaks_pretype pt f v ks ks':
  debruijn_weaks_conds f ks' ks ->
  v < ks' SPretype ->
  RecVarUnderRefPretype pt v true ->
  RecVarUnderRefPretype (subst'_pretype f pt) v true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            v < ks' SPretype ->
            RecVarUnderRefPretype pt v true ->
            RecVarUnderRefPretype (subst.subst'_pretype f pt) v true)
       (fun t =>
          forall f v ks ks',
            debruijn_weaks_conds f ks' ks ->
            v < ks' SPretype ->
            RecVarUnderRefTyp t v true ->
            RecVarUnderRefTyp (subst.subst'_type f t) v true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all: try now ltac:(econstructor; eauto).
  - match goal with
    | [ H : RecVarUnderRefTyp _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
  - unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
       end.
    -- match goal with
       | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
       end.
       simpl.
       unfold zero; rewrite Nat.add_0_r.
       match goal with
       | [ |- _ (TVar ?A) ?B _ ] =>
         replace true with (negb (A =? B))
       end.
       2:{
         apply Bool.eq_true_not_negb.
         rewrite OrdersEx.Nat_as_DT.eqb_eq.
         intro; subst.
         lia.
       }
       econstructor.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    simpl in *; eauto.
    - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus; simpl.
       lia.
  - match goal with
    | [ H : RecVarUnderRefPretype _ _ _ |- _ ] => inversion H; subst
    end.
    econstructor.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H
    end.
    -- eapply debruijn_weaks_conds_under_knd; eauto.
    -- unfold plus; lia.
    -- auto.
Qed.

Lemma TypeValid_add_constraint_pretype :
  (forall F t,
      TypeValid F t ->
      forall kvs f F'' sz q hc,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SPretype 1) ->
        F = add_constraints F'' kvs ->
        TypeValid (add_constraints F'' (TYPE sz q hc :: kvs))
                  (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall kvs f F'' sz q hc,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SPretype 1) ->
        F = add_constraints F'' kvs ->
        HeapTypeValid (add_constraints F'' (TYPE sz q hc :: kvs))
                      (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall kvs f F'' sz q hc,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SPretype 1) ->
        F = add_constraints F'' kvs ->
        ArrowTypeValid (add_constraints F'' (TYPE sz q hc :: kvs))
                       (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall kvs f F'' sz q hc,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SPretype 1) ->
        F = add_constraints F'' kvs ->
        FunTypeValid (add_constraints F'' (TYPE sz q hc :: kvs))
                     (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.
  all: try now ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs; econstructor; eauto; try rewrite qual_fctx_subst_weak_pretype; auto).

  - unfold get_var'.
    all: try ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ]).
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
      case H'; intros
    end.
    1:
      match goal with
      | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
      end.
    2:
      match goal with
      | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
      end.
    all: simpl.
    all: econstructor.
    4,8: rewrite qual_fctx_subst_weak_pretype; eauto.
    all: try ltac:(rewrite qual_fctx_subst_weak_pretype; eauto).
    all: rewrite type_fctx_subst_weak_pretype; eauto.
    -- rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
       rewrite nth_error_app1.
       2:{
         rewrite length_collect_tctx; auto.
       }
       rewrite nth_error_app1 in *.
       2:{
         rewrite length_collect_tctx; auto.
       }
       eauto.
    -- rewrite add_constraints_to_ks_of_kvs in *.
       match goal with
       | [ |- nth_error ?A _ = Some _ ] =>
         match goal with
         | [ |- context[collect_tctx ?X ++ ?Y] ] =>
           replace A with (collect_tctx X ++ Y) by auto
         end
       end.
       match goal with
       | [ H : nth_error _ _ = Some _ |- _ ] => simpl in H
       end.
       rewrite nth_error_app2.
       2:{
         rewrite length_collect_tctx.
         lia.
       }
       rewrite nth_error_app2 in *.
       2:{
         rewrite length_collect_tctx.
         lia.
       }
       match goal with
       | [ |- context[Datatypes.S ?A - ?B] ] =>
         replace (Datatypes.S A - B)
           with
             (Datatypes.S (A - B))
       end.
       2:{
         rewrite length_collect_tctx.
         lia.
       }
       rewrite type_update_type_ctx.
       simpl.
       eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    match goal with
    | [ H : sizeOfPretype _ _ = Some ?SZ |- TypeValid ?C (QualT ?A _) ] =>
      assert (sizeOfPretype (type C) A = Some SZ)
    end.
    { rewrite type_fctx_subst_weak_pretype; eauto.
      simpl.
      rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
      rewrite type_update_type_ctx in *.
      simpl.
      rewrite app_comm_cons in *.
      match goal with
      | [ |- context[_ ++ ?A :: ?B] ] =>
        replace (A :: B) with ([A] ++ B)
      end.
      erewrite sizeOfPretype_weaks_gen.
      4: eapply debruijn_weaks_conds_under_knd; eauto.
      1:{
        match goal with
        | [ H : sizeOfPretype _ _ = _ |- _ ] => rewrite H
        end.
        simpl.
        erewrite weak_non_size_no_effect_on_size; auto.
        2: eapply debruijn_weaks_conds_under_knd; eauto.
        solve_ineqs.
      }
      all: eauto.
      - unfold plus; simpl.
        rewrite length_collect_tctx; auto.
      - eapply forall2_nth_error_inv; auto.
        intros.
        destruct_prs.
        match goal with
        | [ H : ?A = _, H' : ?A = _ |- _ ] =>
          rewrite H in H'; inv H'
        end.
        split.
        { erewrite weak_non_size_no_effect_on_size; auto.
          2: eapply debruijn_weaks_conds_under_knd; eauto.
          solve_ineqs. }
        split.
        { erewrite weak_non_size_no_effect_on_size; auto.
          2: eapply debruijn_weaks_conds_under_knd; eauto.
          solve_ineqs. }
        auto.
      - match goal with
        | [ |- map ?A _ = map ?B _ ] => replace A with B; auto
        end.
        apply FunctionalExtensionality.functional_extensionality.
        intros.
        destruct_prs.
        erewrite weak_non_size_no_effect_on_size; auto.
        2: eapply debruijn_weaks_conds_under_knd; eauto.
        solve_ineqs. }
    
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_pretype; eauto.
    -- erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- eapply RecVarUnderRefPretype_under_weaks_pretype; eauto.
       --- eapply debruijn_weaks_conds_under_knd; eauto.
       --- unfold plus.
           simpl.
           lia.
    -- rewrite add_constraints_to_ks_of_kvs in *.
       simpl in *.
       rewrite sizepairs_debruijn_weak_pretype.
       rewrite size_update_type_ctx.
       auto.
    -- match goal with
       | [ H : forall _ _, _ |-
           context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)] ] =>
         match goal with
         | [ |- context[add_constraints _ ?KVS] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_pretype ?F _] ] =>
         match goal with
         | [ H' : context[qual (add_constraints ?C _)]
	         |- context[(?SZ, ?Q, ?HC) :: type ?C] ] =>
           specialize (H F C SZ Q HC)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc.
       all: simpl; auto.
       rewrite ks_of_kvs_app.
       simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_pretype; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       erewrite weak_non_qual_no_effect_on_qual; eauto.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H; specialize (H _ H')
       end.
       simpl in *; auto.
       solve_ineqs.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype; auto.
    -- rewrite loc_fctx_subst_weak_pretype.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype; auto.
    -- rewrite loc_fctx_subst_weak_pretype.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype; auto.
    -- rewrite loc_fctx_subst_weak_pretype.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- rewrite qual_fctx_subst_weak_pretype.
       do 2 ltac:(try erewrite weak_non_qual_no_effect_on_qual; eauto).
       3:{
         eapply debruijn_weaks_conds_under_knd; eauto.
       }
       all: solve_ineqs.
    -- match goal with
       | [ H : forall _ _ _, _ |- context[add_constraints _ ?KVS] ] =>
         match goal with
         | [ |- context[subst'_pretype ?F _] ] =>
           match goal with
           | [ H' : QualValid (qual (add_constraints ?C _)) _
               |- context[(?SZ, ?Q, ?HC) :: type ?C] ] =>
             specialize (H (KVS ++ [LOC]) F C SZ Q HC)
           end
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc; simpl; auto.
       rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype; auto.
    -- rewrite qual_fctx_subst_weak_pretype; auto.
    -- rewrite loc_fctx_subst_weak_pretype.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *.
    eauto.
  - econstructor.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs; simpl.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    destructAll.
    rewrite type_fctx_subst_weak_pretype.
    rewrite size_fctx_subst_weak_pretype.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : sizeOfPretype _ _ = Some ?SZ |- _ ] => exists SZ
    end.
    repeat split; auto.
    -- rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
       rewrite type_update_type_ctx in *.
       simpl.
       match goal with
       | [ |- context[_ ++ ?A :: ?B] ] =>
         replace (A :: B) with ([A] ++ B)
       end.
       erewrite sizeOfPretype_weaks_gen; eauto.
       1:{
         match goal with
         | [ H : sizeOfPretype _ _ = _ |- _ ] => rewrite H
         end.
         simpl.
         erewrite weak_non_size_no_effect_on_size; eauto.
         solve_ineqs.
       }
       all: eauto.
       --- rewrite length_collect_tctx; auto.
       --- eapply forall2_nth_error_inv; auto.
           intros.
           destruct_prs.
           match goal with
           | [ H : ?A = _, H' : ?A = _ |- _ ] =>
             rewrite H in H'; inv H'
           end.
           split.
           { erewrite weak_non_size_no_effect_on_size; eauto.
             solve_ineqs. }
           split.
           { erewrite weak_non_size_no_effect_on_size; eauto.
             solve_ineqs. }
           auto.
       --- match goal with
           | [ |- map ?A _ = map ?B _ ] => replace A with B; auto
           end.
           apply FunctionalExtensionality.functional_extensionality.
           intros.
           destruct_prs.
           erewrite weak_non_size_no_effect_on_size; eauto.
           solve_ineqs.
    -- erewrite weak_non_size_no_effect_on_size; eauto.
       solve_ineqs.
    -- erewrite weak_non_size_no_effect_on_size; eauto.
       solve_ineqs.
  - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_pretype.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  - econstructor; eauto.
    -- rewrite size_fctx_subst_weak_pretype.
       erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
    -- rewrite qual_fctx_subst_weak_pretype.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       match goal with
       | [ H : forall _ _, _ |-
           TypeValid
             (subst_ext _
                        (update_type_ctx ((?SZ, ?Q, ?HC) :: _) _))
             _ ] =>
         match goal with
         | [ |- context[add_constraints _ ?KVS] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_type ?F _] ] =>
         match goal with
         | [ H' : context[qual (add_constraints ?C _)]
             |- context[(?SZ, ?Q, ?HC) :: type ?C] ] =>
           specialize (H F C SZ Q HC)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       all: try rewrite add_constraints_snoc; simpl; auto.
       rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
      end.
    all: eauto.
  - econstructor; eauto.
    -- erewrite weak_pretype_no_effect_on_kindvars; eauto.
       eapply KindVarsValid_Function_Ctx; eauto.
       --- rewrite qual_fctx_subst_weak_pretype; auto.
       --- rewrite size_fctx_subst_weak_pretype; auto.
    -- erewrite weak_pretype_no_effect_on_kindvars; eauto.
       rewrite add_constraints_app.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H
       end.
       --- rewrite ks_of_kvs_app.
           apply debruijn_weaks_conds_under_kindvars; auto.
       --- apply add_constraints_app.
Qed.

Lemma weak_non_qual_no_effect_on_qual_gen : forall {q f ks ks'},
    debruijn_weaks_conds f ks ks' ->
    ks' SQual = 0 ->
    subst'_qual f q = q.
Proof.
  destruct q; simpl; auto.
  intros.
  unfold get_var'.
  unfold debruijn_weaks_conds in *.
  destructAll.
  match goal with
  | [ |- _ ?KND ?V _ = _ ] =>
    let H := fresh "H" in
    assert (H : V < ks KND \/ V >= ks KND) by apply Nat.lt_ge_cases;
    case H; intros
  end.
  -- match goal with
     | [ H : context[_ < _ -> _] |- _ ] =>
       erewrite H; eauto
     end.
  -- match goal with
     | [ H : context[_ >= _ -> _] |- _ ] =>
       erewrite H; eauto
     end.
     match goal with
     | [ H : _ = 0 |- _ ] => rewrite H
     end.
     unfold zero; simpl; auto.
Qed.

Lemma weak_non_qual_no_effect_on_quals_gen : forall {qs f ks ks'},
    debruijn_weaks_conds f ks ks' ->
    ks' SQual = 0 ->
    subst'_quals f qs = qs.
Proof.
  induction qs; simpl; auto.
  intros.
  erewrite IHqs; eauto.
  erewrite weak_non_qual_no_effect_on_qual_gen; eauto.
Qed.

Lemma add_constraint_weak_size : forall {f ks ks' kv qctx},
    debruijn_weaks_conds f ks ks' ->
    ks' SQual = 0 ->
    add_constraint_to_qctx
      qctx
      (subst'_kindvar f kv) =
    add_constraint_to_qctx qctx kv.
Proof.
  intros.
  destruct kv; simpl; auto.
  do 2 match goal with
       | [ H : debruijn_weaks_conds ?F _ _ |- context[subst'_quals ?F ?QS] ] =>
         replace (subst'_quals F QS) with QS; auto
       end.
  all: erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
Qed.

Lemma collect_qctx_weak_size_gen : forall {kvs f ks ks' qctx},
    debruijn_weaks_conds f ks ks' ->
    ks' SQual = 0 ->
    fold_left
      add_constraint_to_qctx
      (subst'_kindvars f kvs)
      qctx =
    fold_left add_constraint_to_qctx kvs qctx.
Proof.
  induction kvs; simpl; auto.
  intros.
  erewrite add_constraint_weak_size; eauto.
  eapply IHkvs; eauto.
  eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma collect_qctx_weak_size : forall {kvs},
    collect_qctx (subst'_kindvars (subst'_of (weak SSize)) kvs) =
    collect_qctx kvs.
Proof.
  intros.
  unfold collect_qctx.
  eapply collect_qctx_weak_size_gen; eauto.
  - apply single_weak_debruijn_weak_conds.
  - auto.
Qed.

Lemma qual_fctx_subst_weak_size : forall {F kvs szs0 szs1},
    qual
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SSize))
            (update_size_ctx ((szs0, szs1) :: size F) F))
         (subst'_kindvars (subst'_of (weak SSize)) kvs))
    =
    qual
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite collect_qctx_weak_size.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B
  end.
  1: rewrite ks_of_kvs_subst_kindvars; auto.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_qual_no_effect_on_quals; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma loc_fctx_subst_weak_size : forall {kvs sz1 sz2 F},
    location
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SSize))
            (update_size_ctx
               ((sz1, sz2) :: (size F)) F))
         (subst'_kindvars (subst'_of (weak SSize)) kvs))
    =
    location
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite ks_of_kvs_subst_kindvars; auto.
Qed.

Lemma nth_error_subst_weak_size : forall (type: list (Size * Qual *HeapableConstant)) kvs sz  hc n qa ,
    nth_error
         (map
            (fun '(sz, q, hc) =>
             (subst'_size (weaks' (ks_of_kvs kvs)) sz, subst'_qual (weaks' (ks_of_kvs kvs)) q,
             hc)) type) n = Some (sz, qa, hc) ->
    exists sz' hc', 
    nth_error
    (map
       (fun '(sz0, q0, hc0) =>
        (subst'_size (weaks' (ks_of_kvs kvs)) sz0, subst'_qual (weaks' (ks_of_kvs kvs)) q0, hc0))
       (map
          (fun '(s, q0, hc0) =>
           (subst'_size (subst'_of (weak SSize)) s, subst'_qual (subst'_of (weak SSize)) q0,
           hc0)) type))n =
      Some
        (sz', qa, hc').
Proof.
  intros type.
  induction type; destruct n; simpl; intros; inversion H; subst; eauto.
  destruct_prs.
  repeat eexists.
  repeat f_equal; eauto.
  auto.
  inversion H1. subst; eauto.
  f_equal.
  erewrite weak_non_qual_no_effect_on_qual; [ eauto | | apply single_weak_debruijn_weak_conds].
  solve_ineqs.
Qed.

Lemma type_update_size_ctx : forall {C F},
    type (update_size_ctx C F) = type F.
Proof.
  intros.
  destruct F; simpl in *; auto.
Qed.

Lemma pure_under_kindvars : forall kvs knd obj,
    debruijn_subst_ext_conds (under_kindvars' kvs (subst'_of (ext knd obj id))) (ks_of_kvs kvs) knd obj.
Proof.
  intros.
  unfold ks_of_kvs.
  apply debruijn_subst_ext_under_kindvars.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma pure_under_kindvars_weaks : forall {kvs knd},
    debruijn_weaks_conds (under_kindvars' kvs (subst'_of (weak knd))) (ks_of_kvs kvs) (sing knd 1).
Proof.
  intros.
  unfold ks_of_kvs.
  apply debruijn_weaks_conds_under_kindvars.
  apply single_weak_debruijn_weak_conds.
Qed.  

Lemma eq_dec_ind : forall {a a' : Ind},
    a = a' \/ a <> a'.
Proof.
  intros.
  case a; case a'.
  all:
    match goal with
    | [ |- ?A = ?A \/ _ ] => left; auto
    | [ |- _ ] => right; solve_ineqs
    end.
Qed.

Lemma debruijn_subst_ext_inj : forall {f f' ks knd obj},
    debruijn_subst_ext_conds f ks knd obj ->
    debruijn_subst_ext_conds f' ks knd obj ->
    f = f'.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ X : Ind, X' : Ind |- _ ] =>
    let H := fresh "H" in
    assert (H : X = X' \/ X <> X') by apply eq_dec_ind;
    case H; intros; subst
  end.
  - match goal with
    | [ H : context[_ <> ?F _ -> _] |- _ ?K ?V _ = _ ] =>
      let H' := fresh "H" in
      assert (H' : V = F K \/ V <> F K) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : forall _, _ = _, H' : forall _, _ = _ |- _ ] =>
         rewrite H; rewrite H'
       end.
       auto.
    -- match goal with
       | [ H : context[_ <> _ _ -> ?F _ _ _ = _]
           |- context[?F _ _ _] ] =>
         rewrite H; auto
       end.
  - match goal with
    | [ H''' : context[_ <> _ _ -> _],
        H'' : context[_ <> _ _ -> _],
        H : context[_ <> _ -> _],
        H' : context[_ <> _ -> _] |- _ ] =>
      rewrite H; auto; rewrite H'; auto
    end.
Qed.

Lemma debruijn_weaks_conds_inj : forall {f f' ks ks'},
    debruijn_weaks_conds f ks ks' ->
    debruijn_weaks_conds f' ks ks' ->
    f = f'.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn_weaks_conds in *.
  destructAll.
  match goal with
  | [ X : Ind, Y : nat |- _ ] =>
    let H := fresh "H" in
    assert (H : Y < ks X \/ Y >= ks X) by apply Nat.lt_ge_cases;
    case H; intros; subst
  end.
  - match goal with
    | [ H : context[_ < _ -> _], H' : context[_ < _ -> _] |- _ ] =>
      erewrite H; eauto; erewrite H'; eauto
    end.
  - match goal with
    | [ H : context[_ >= _ -> _], H' : context[_ >= _ -> _] |- _ ] =>
      erewrite H; eauto; erewrite H'; eauto
    end.
Qed.

Lemma subst'_kindvars_app : forall {kvs f knd obj kvsuff kvsuff'},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) knd obj ->
    kvsuff' = subst'_kindvars f kvsuff ->
    (subst'_kindvars (subst'_of (ext knd obj id)) kvs) ++ kvsuff' =
    subst'_kindvars (subst'_of (ext knd obj id)) (kvs ++ kvsuff).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall f knd obj kvsuff kvsuff',
            debruijn_subst_ext_conds f (ks_of_kvs kvs) knd obj ->
            kvsuff' = subst'_kindvars f kvsuff ->
            (subst'_kindvars (subst'_of (ext knd obj id)) kvs) ++ kvsuff' =
            subst'_kindvars (subst'_of (ext knd obj id)) (kvs ++ kvsuff))).
  - simpl.
    intros; subst.
    match goal with
    | [ |- subst'_kindvars ?X _  = subst'_kindvars ?Y _ ] =>
      replace Y with X; auto
    end.
    eapply debruijn_subst_ext_inj; eauto.
    apply simpl_debruijn_subst_ext_conds.
  - intros; subst.
    rewrite <-app_assoc.
    match goal with
    | [ H : debruijn_subst_ext_conds _ (ks_of_kvs (?L ++ _)) ?KND ?OBJ |- _ ] =>
      specialize (pure_under_kindvars L KND OBJ)
    end.
    intros.
    erewrite <-H; eauto.
    erewrite <-H; eauto.
    simpl.
    rewrite <-app_assoc; simpl.
    match goal with
    | [ |- _ ++ _ :: subst'_kindvars ?F _ =
           _ ++ _ :: subst'_kindvars ?F2 _ ] =>
      replace F2 with F; auto
    end.
    eapply debruijn_subst_ext_inj; eauto.
    rewrite ks_of_kvs_app; simpl.
    apply debruijn_subst_ext_under_knd; auto.
Qed.

Lemma subst'_kindvars_snoc : forall {f knd obj kv kv' kvs},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) knd obj ->
    kv' = subst'_kindvar f kv ->
    (subst'_kindvars (subst'_of (ext knd obj id)) kvs) ++ [kv'] =
    subst'_kindvars (subst'_of (ext knd obj id)) (kvs ++ [kv]).
Proof.
  intros; subst.
  erewrite subst'_kindvars_app; eauto.
Qed.

Lemma subst'_kindvars_app_weaks : forall {kvs f knd kvsuff kvsuff'},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing knd 1) ->
    kvsuff' = subst'_kindvars f kvsuff ->
    (subst'_kindvars (subst'_of (weak knd)) kvs) ++ kvsuff' =
    subst'_kindvars (subst'_of (weak knd)) (kvs ++ kvsuff).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall f knd kvsuff kvsuff',
            debruijn_weaks_conds f (ks_of_kvs kvs) (sing knd 1) ->
            kvsuff' = subst'_kindvars f kvsuff ->
            (subst'_kindvars (subst'_of (weak knd)) kvs) ++ kvsuff' =
            subst'_kindvars (subst'_of (weak knd)) (kvs ++ kvsuff))).
  - simpl.
    intros.
    subst.
    match goal with
    | [ |- subst'_kindvars ?A _ = subst'_kindvars ?B _ ] =>
      replace B with A; auto
    end.
    eapply debruijn_weaks_conds_inj; eauto.
    apply single_weak_debruijn_weak_conds.
  - intros; subst.
    rewrite <-app_assoc.
    match goal with
    | [ H : debruijn_weaks_conds _ (ks_of_kvs (?L ++ _)) (sing ?KND 1) |- _ ] =>
      specialize (pure_under_kindvars_weaks (kvs:=L) (knd:=KND))
    end.
    intros.
    match goal with
    | [ H : forall _ _ _, _ |- _ ] =>
      erewrite <-H; eauto;
      erewrite <-H; eauto
    end.
    simpl.
    rewrite <-app_assoc; simpl.
    match goal with
    | [ |- _ ++ _ :: subst'_kindvars ?F _ =
           _ ++ _ :: subst'_kindvars ?F2 _ ] =>
      replace F2 with F; auto
    end.
    eapply debruijn_weaks_conds_inj; eauto.
    rewrite ks_of_kvs_app; simpl.
    apply debruijn_weaks_conds_under_knd; auto.
Qed.

Lemma subst'_kindvars_snoc_weaks : forall {f knd kv kv' kvs},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing knd 1) ->
    kv' = subst'_kindvar f kv ->
    (subst'_kindvars (subst'_of (weak knd)) kvs) ++ [kv'] =
    subst'_kindvars (subst'_of (weak knd)) (kvs ++ [kv]).
Proof.
  intros; subst.
  erewrite subst'_kindvars_app_weaks; eauto.
Qed.

Lemma debruijn_weaks_conds_under_no_effect_gen : forall {f f' ks ks' ks''},
    debruijn_weaks_conds f ks ks'' ->
    debruijn_weaks_conds f' (plus ks' ks) ks'' ->
    (forall knd, ks' knd = 0 \/ ks'' knd = 0) ->
    f = f'.
Proof.
  intros.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn_weaks_conds in *.
  destructAll.
  match goal with
  | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _],
      H'' : context[_ < ?KS _ -> ?F _ _ _ = _]
      |- ?F ?KND ?V _ = _ ] =>
    let H' := fresh "H" in
    assert (H' : V < KS KND \/ V >= KS KND) by apply Nat.lt_ge_cases;
    case H'; intros; [ rewrite H'' | rewrite H ]; auto
  end.
  - match goal with
    | [ H : context[_ < _ -> ?F _ _ _ = _]
        |- _ = ?F _ _ _ ] =>
      rewrite H; auto
    end.
    unfold plus; lia.
  - match goal with
    | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _],
        H'' : context[_ < ?KS _ -> ?F _ _ _ = _]
        |- _ = ?F ?KND ?V _ ] =>
      let H' := fresh "H" in
      assert (H' : V < KS KND \/ V >= KS KND) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H'' | rewrite H ]; auto
    end.
    unfold plus in *.
    match goal with
    | [ |- VarKind _ ?A = VarKind _ ?B ] =>
      replace B with A; auto
    end.
    match goal with
    | [ H : forall _, _ \/ _, H' : _ < _ ?X + _ ?X |- _ ] =>
      specialize (H X); case H; intros; lia
    end.
Qed.

Lemma debruijn_weaks_conds_under_no_effect_sing : forall {f f' ks ks' knd},
    debruijn_weaks_conds f ks (sing knd 1) ->
    debruijn_weaks_conds f'
                         (plus ks' ks)
                         (sing knd 1) ->
    ks' knd = 0 ->
    f = f'.
Proof.
  intros.
  eapply debruijn_weaks_conds_under_no_effect_gen; eauto.
  intros.
  repeat match goal with
         | [ X : Ind |- _ ] => destruct X
         end.
  all: simpl in *; auto.
Qed.

Lemma debruijn_weaks_conds_under_no_effect : forall {f ks ks' knd},
    debruijn_weaks_conds f ks ks' ->
    ks' knd = 0 ->
    under' knd f = f.
Proof.
  intros.
  apply eq_sym.
  eapply debruijn_weaks_conds_under_no_effect_gen; eauto.
  - apply debruijn_weaks_conds_under_knd; auto.
  - intros.
    repeat match goal with
           | [ X : Ind |- _ ] => destruct X
           end.
    all: simpl in *; auto.
Qed.

Lemma type_update_location_ctx : forall {F lctx},
    type (update_location_ctx lctx F) = type F.
Proof.
  destruct F; simpl in *; auto.
Qed.

Lemma type_update_qual_ctx : forall {F lctx},
    type (update_qual_ctx lctx F) = type F.
Proof.
  destruct F; simpl in *; auto.
Qed.

Lemma comp'_right_id : forall su,
    subst'_of id ∘' su = su.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  simpl.
  destruct x.
  all: simpl.
  all: rewrite under_ks_id.
  - apply id_no_effect_on_loc.
  - apply id_no_effect_on_qual.
  - apply id_no_effect_on_size.
  - rewrite id_eq_var'.
    match goal with
    | [ |- ?F ?A ?B = _ ] =>
      replace (F A B) with (subst_ext' A B) by auto
    end.
    rewrite subst_ext'_var_e; auto.
Qed.

Lemma under_ks_weaks_comp' : forall {ks ks'},
    under_ks' ks' (weaks' ks) ∘' (weaks' ks')
    =
    weaks' (plus ks ks').
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x.
  all: simpl.
  all: unfold get_var'.
  all: unfold under_ks'.

  all:
    match goal with
    | [ |- context[if ?B then _ else _] ]=>
      let H := fresh "H" in
      assert (H : B = false); [ | rewrite H ]
    end.
  1,3,5,7: rewrite <-Nat.add_assoc.
  1-4: rewrite Nat.add_comm.
  1-4: rewrite <-Nat.add_assoc.
  1-4: rewrite Nat.ltb_ge.
  1-4: apply le_plus_l.

  all:
    match goal with
    | [ |- context[if ?B then _ else _] ]=>
      let H := fresh "H" in
      assert (H : B = false); [ | rewrite H ]
    end.
  1,3,5,7: rewrite Nat.ltb_ge.
  1-4: rewrite Nat.add_comm.
  1-4: rewrite Nat.add_assoc.
  1-4: rewrite Nat.add_sub.
  1-4: rewrite Nat.add_comm.
  1-4: apply le_plus_l.

  all: rewrite Nat.add_comm.
  all: rewrite <-Nat.sub_add_distr.
  all:
    match goal with
    | [ |- context[_ + _ - (?A + ?B)] ] =>
      rewrite (Nat.add_comm A B)
    end.
  all: rewrite Nat.add_sub.
  all: simpl.

  all: rewrite plus_zero.
  all: unfold weaks'.
  all: unfold var.
  all: simpl.
  all: unfold plus.
  all: repeat rewrite Nat.add_assoc; auto.
Qed.

Lemma weaks_subst_comm : forall {su ks},
  under_ks' ks (subst'_of su) ∘' weaks' ks =
  weaks' ks ∘' subst'_of su.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x.
  all: simpl.
  all: unfold get_var'.
  all: unfold under_ks' at 1.
  all: unfold under_ks' at 1.
  all:
    match goal with
    | [ |- context[if ?B then _ else _] ]=>
      let H := fresh "H" in
      assert (H : B = false); [ | rewrite H ]
    end.
  1,3,5,7: rewrite <-Nat.add_assoc.
  1-4: rewrite Nat.add_comm.
  1-4: rewrite <-Nat.add_assoc.
  1-4: rewrite Nat.ltb_ge.
  1-4: apply le_plus_l.

  all:
    match goal with
    | [ |- context[if ?B then _ else _] ]=>
      let H := fresh "H" in
      assert (H : B = false); [ | rewrite H ]
    end.
  1,3,5,7: rewrite Nat.ltb_ge.
  1-4: rewrite Nat.add_comm.
  1-4: rewrite Nat.add_assoc.
  1-4: rewrite Nat.add_sub.
  1-4: rewrite Nat.add_comm.
  1-4: apply le_plus_l.

  all: rewrite Nat.add_comm.
  all: rewrite <-Nat.sub_add_distr.
  all:
    match goal with
    | [ |- context[_ + _ - (?A + ?B)] ] =>
      rewrite (Nat.add_comm A B)
    end.
  all: rewrite Nat.add_sub.
  all: simpl.
  all:
    match goal with
    | [ |- _ = ?F ?A (?F ?B ?C) ] =>
      replace (F A (F B C)) with
          (subst_ext' A (subst_ext' B C))
        by auto
    end.
  all: rewrite subst_ext'_assoc.
  all: simpl.
  all: rewrite plus_zero.
  all: rewrite under_ks_weaks_comp'; auto.
Qed.

Lemma debruijn_weaks_comm : forall {f1 f2 f3 f4 ks knd knd'},
    debruijn_weaks_conds f1 zero (sing knd 1) ->
    debruijn_weaks_conds f2 ks (sing knd' 1) ->
    debruijn_weaks_conds f3 (plus (sing knd 1) ks) (sing knd' 1) ->
    debruijn_weaks_conds f4 zero (sing knd 1) ->
    f1 ∘' f2 = f3 ∘' f4.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn_weaks_conds in *.
  simpl.
  destructAll.
  match goal with
  | [ H : context[_ >= zero _ -> ?F _ _ _ = _]
      |- _ = subst'_rwasm _ _ (?F ?KND ?V _) ] =>
    rewrite H; [ | unfold zero; lia ]
  end.
  match goal with
  | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _],
      H'' : context[_ < ?KS _ -> ?F _ _ _ = _]
      |- subst'_rwasm _ _ (?F ?KND ?V _) = _ ] =>
    let H' := fresh "H" in
    assert (H' : V < KS KND \/ V >= KS KND) by apply Nat.lt_ge_cases;
    case H'; intros; [ rewrite H'' | rewrite H ]; auto
  end.
  all: destruct x; simpl.
  all: unfold get_var'.
  all: unfold under_ks'.
  all:
    do 2 match goal with
         | [ |- context[if ?A then _ else _] ] =>
           replace A with false;
           [ | apply eq_sym; rewrite OrdersEx.Nat_as_OT.ltb_ge; lia ]
         end.
  all:
    match goal with
    | [ H : context[_ >= zero _ -> ?F _ _ _ = _]
        |- ?F ?KND ?V _ = _ ] =>
      rewrite H; auto; [ | unfold zero; lia ]
    end.
  all:
    match goal with
    | [ H : context[_ < ?KS _ -> ?F _ _ _ = _], H' : _ < _
        |- _ = ?F _ _ _ ] =>
      rewrite H; [ | unfold plus; lia ]
    | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _], H' : _ >= _
        |- _ = ?F _ _ _ ] =>
      rewrite H; [ | unfold plus; lia ]
    end.
  all:
    match goal with
    | [ |- _ _ ?A = _ _ ?B ] => replace B with A; auto
    end.
  all: lia.
Qed.

Lemma type_fctx_subst_weak_size_helper : forall {F F' kv f f' ks},
    type F =
    map
      (fun '(sz, q, hc) => (subst'_size f sz, q, hc))
      (type F') ->
    debruijn_weaks_conds
      f
      ks
      (sing SSize 1) ->
    debruijn_weaks_conds
      f'
      (plus (sing (kind_of_kindvar kv) 1) ks)
      (sing SSize 1) ->
    type (add_constraint F (subst'_kindvar f kv)) =
    map
      (fun '(sz, q, hc) => (subst'_size f' sz, q, hc))
      (type (add_constraint F' kv)).
Proof.
  intros.
  destruct kv; simpl.
  - replace (fun '(s, q, hc) => (subst'_size (subst'_of (weak SLoc)) s, subst'_qual (subst'_of (weak SLoc)) q, hc)) with (fun (tpl : (Size * Qual * HeapableConstant)) => tpl).
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      destruct_prs.
      rewrite loc_weak_no_effect_on_size.
      rewrite loc_weak_no_effect_on_qual; auto.
    }
    repeat rewrite map_id.
    repeat rewrite type_update_location_ctx; auto.
    erewrite <-debruijn_weaks_conds_under_no_effect_sing; eauto.
  - repeat rewrite type_update_qual_ctx.
    rewrite map_map.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat rewrite qual_weak_no_effect_on_size.
    erewrite debruijn_weaks_conds_under_no_effect_sing; eauto.
  - repeat rewrite type_update_size_ctx.
    rewrite map_map.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat match goal with
           | [ |- context[subst'_size ?F ?SZ] ] =>
             replace (subst'_size F SZ) with (subst_ext' F SZ) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    simpl in *.
    erewrite debruijn_weaks_comm; eauto.
    all: apply single_weak_debruijn_weak_conds.
  - repeat rewrite type_update_type_ctx.
    rewrite map_map.
    simpl.
    repeat rewrite pretype_weak_no_effect_on_size.
    repeat rewrite pretype_weak_no_effect_on_qual.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    erewrite weak_non_qual_no_effect_on_qual_gen; eauto.
    match goal with
    | [ |- _ :: map ?F1 _ = _ :: map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    1:{ erewrite debruijn_weaks_conds_under_no_effect_sing; eauto. }
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat rewrite pretype_weak_no_effect_on_size.
    repeat rewrite pretype_weak_no_effect_on_qual.
    erewrite debruijn_weaks_conds_under_no_effect_sing; eauto.
Qed.

Lemma type_fctx_subst_weak_size : forall {kvs F szs0 szs1 f},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
    type
      (add_constraints
         (subst'_function_ctx (subst'_of (weak SSize))
                              (update_size_ctx ((szs0, szs1) :: size F) F))
         (subst'_kindvars (subst'_of (weak SSize)) kvs)) =
    map
      (fun '(sz, q, hc) =>
         (subst'_size f sz,
          q,
          hc))
      (type (add_constraints F kvs)).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall F szs0 szs1 f,
            debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
            type
              (add_constraints
                 (subst'_function_ctx (subst'_of (weak SSize))
                                      (update_size_ctx ((szs0, szs1) :: size F) F))
                 (subst'_kindvars (subst'_of (weak SSize)) kvs)) =
            map
              (fun '(sz, q, hc) =>
                 (subst'_size f sz,
                  q,
                  hc))
              (type (add_constraints F kvs)))).
  - intros; simpl.
    rewrite type_update_size_ctx.
    match goal with
    | [ |- map ?A _ = map ?B _ ] => replace A with B; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    erewrite weak_non_qual_no_effect_on_qual; [ eauto | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
    match goal with
    | [ |- (subst'_size ?F1 _, _, _) = (subst'_size ?F2 _, _, _) ] =>
      replace F1 with F2; auto
    end.
    eapply debruijn_weaks_conds_inj; eauto.
    simpl.
    apply single_weak_debruijn_weak_conds.
  - intros.
    match goal with
    | [ H : context[ks_of_kvs (?L ++ _)],
        H' : forall _ _ _ _, _
        |- context[(?SZS0, ?SZS1) :: size ?F] ] =>
      specialize (H' F SZS0 SZS1 (under_kindvars' L (subst'_of (weak SSize))))
    end.
    match goal with
    | [ H : ?A -> type _ = _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    1:{ eapply pure_under_kindvars_weaks; eauto. }

    rewrite add_constraints_snoc.
    erewrite <-subst'_kindvars_app_weaks; eauto.
    simpl.
    rewrite add_constraints_snoc.
    rewrite ks_of_kvs_snoc in *.
    eapply type_fctx_subst_weak_size_helper; eauto.
Qed.

Lemma collect_szctx_subst_weak_size : forall {kvs f},
  debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
  collect_szctx (subst'_kindvars (subst'_of (weak SSize)) kvs)
  =
  map (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1)) (collect_szctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall f,
            debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
            collect_szctx (subst'_kindvars (subst'_of (weak SSize)) kvs)
            =
            map (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1)) (collect_szctx kvs))).
  all: auto.
  intros.
  match goal with
  | [ |- context[collect_szctx (?A ++ _)] ] =>
    specialize (pure_under_kindvars_weaks (kvs:=A) (knd:=SSize))
  end.
  intros.
  erewrite <-subst'_kindvars_snoc_weaks; eauto.
  repeat rewrite collect_szctx_snoc.
  match goal with
  | [ H : forall _, _ -> _ |- _ ] => erewrite H; eauto
  end.
  all: rewrite ks_of_kvs_snoc in *.
  destruct x; simpl in *.
  all:
    try match goal with
        | [ H : debruijn_weaks_conds ?F1 _ _,
            H' : debruijn_weaks_conds ?F2 _ _
            |- map _ _ = map _ _ ] =>
          replace F1 with F2; auto
        end.
  all: try eapply debruijn_weaks_conds_under_no_effect_sing; eauto.
  repeat match goal with
         | [ |- context[subst'_sizes ?F ?SZ] ] =>
           replace (subst'_sizes F SZ) with (subst_ext' F SZ) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  match goal with
  | [ |- (subst_ext' ?F1 _, _) :: _ =
         (subst_ext' ?F2 _, _) :: _ ] =>
    replace F2 with F1; auto
  end.
  2:{ eapply debruijn_weaks_comm; eauto.
      all: apply single_weak_debruijn_weak_conds. }
  match goal with
  | [ |- _ :: ?A = _ :: ?B ] => replace B with A; auto
  end.
  repeat rewrite map_map.
  match goal with
  | [ |- map ?F1 _ = map ?F2 _ ] => replace F2 with F1; auto
  end.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct_prs.
  repeat match goal with
         | [ |- context[subst'_sizes ?F ?SZ] ] =>
           replace (subst'_sizes F SZ) with (subst_ext' F SZ) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  match goal with
  | [ |- (subst_ext' ?F1 _, _) =
         (subst_ext' ?F2 _, _) ] =>
    replace F2 with F1; auto
  end.
  eapply debruijn_weaks_comm; eauto.
  all: apply single_weak_debruijn_weak_conds.
Qed.

Lemma SizeLeq_subst_weak_size : forall {f F kvs sz1 sz2 szs0 szs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
    SizeLeq (size (add_constraints F kvs)) sz1 sz2 = Some true ->
    SizeLeq
      (size
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SSize))
                                 (update_size_ctx ((szs0, szs1) :: size F) F))
            (subst'_kindvars (subst'_of (weak SSize)) kvs)))
      (subst'_size f sz1)
      (subst'_size f sz2)
    =
    Some true.
Proof.
  intros.
  rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  rewrite ks_of_kvs_subst_kindvars.
  rewrite size_update_size_ctx.
  simpl.
  rewrite map_map.
  match goal with
  | [ H : context[_ ++ ?A] |- context[_ :: ?B] ] =>
    replace B with (map (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1)) A)
  end.
  2:{
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat match goal with
           | [ |- context[subst'_sizes ?A ?B] ] =>
             replace (subst'_sizes A B) with (subst_ext' A B) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    erewrite subst_weaks_weak_comm; eauto.
  }
  erewrite collect_szctx_subst_weak_size; eauto.
  match goal with
  | [ |- context[?A :: ?B] ] => replace (A :: B) with ([A] ++ B) by auto
  end.
  eapply SizeLeq_weaks_gen; eauto.
  rewrite length_collect_szctx; auto.
Qed.

Ltac prepare_Forall_with_map :=
  prepare_Forall;
  match goal with
  | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
  end;
  destructAll;
  destruct_prs;
  try match goal with
      | [ X : Typ |- _ ] => destruct X
      end;
  simpl in *;
  try match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end;
  repeat match goal with
         | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
         end;
  simpl in *.

Lemma length_collect_qctx : forall kvs,
    length (collect_qctx kvs) = ks_of_kvs kvs SQual.
Proof.
  apply
    (rev_ind
       (fun kvs => length (collect_qctx kvs) = ks_of_kvs kvs SQual)).
  all: intros; simpl in *; auto.
  rewrite collect_qctx_snoc.
  rewrite ks_of_kvs_app; simpl.
  unfold plus.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all: simpl; auto.
  rewrite map_length.
  lia.
Qed.

Lemma QualValid_subst_weak_size : forall {q f F kvs szs0 szs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
    QualValid (qual (add_constraints F kvs)) q ->
    QualValid
      (qual
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SSize))
                                 (update_size_ctx ((szs0, szs1) :: size F) F))
            (subst'_kindvars (subst'_of (weak SSize)) kvs)))
      (subst'_qual f q).
Proof.
  intros.
  erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  match goal with
  | [ X : Qual |- _ ] => destruct X; simpl in *
  end.
  all: try now ltac:(eapply QualConstValid; eauto).
  rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  match goal with
  | [ H : QualValid _ _ |- _ ] => inv H
  end.
  all:
    match goal with
    | [ H : QualVar _ = _ |- _ ] => inv H
    end.
  match goal with
  | [ |- QualValid ?L (QualVar ?V) ] =>
    assert (exists q, nth_error L V = Some q);
    [ | destructAll; eapply QualVarValid; eauto ]
  end.
  apply nth_error_some_exists.
  match goal with
  | [ H : nth_error _ _ = Some _ |- _ ] =>
    apply nth_error_Some_length in H
  end.
  rewrite app_length in *.
  rewrite length_collect_qctx in *.
  rewrite ks_of_kvs_subst_kindvars.
  repeat rewrite map_length in *.
  destruct F; subst; simpl in *; auto.
Qed.

Lemma KindVarsValid_subst_weak_size : forall {kvs' f kvs F szs0 szs1},
  KindVarsValid (add_constraints F kvs) kvs' ->
  debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
  KindVarsValid
    (add_constraints
       (subst'_function_ctx (subst'_of (weak SSize))
          (update_size_ctx ((szs0, szs1) :: size F) F))
       (subst'_kindvars (subst'_of (weak SSize)) kvs))
    (subst'_kindvars f kvs').
Proof.
  induction kvs'; [ econstructor | ].
  intros.
  simpl.
  econstructor.
  - match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
    match goal with
    | [ |- KindVarValid _ (subst'_kindvar _ ?KV) ] =>
      destruct KV; simpl in *; auto
    end.
    -- destructAll.
       split.
       all: unfold subst'_quals.
       all: prepare_Forall_with_map.
       all: eapply QualValid_subst_weak_size; eauto.
    -- destructAll.
       split.
       all: unfold subst'_sizes.
       all: prepare_Forall_with_map.
       all: eapply SizeValid_subst_weak_size; eauto.
    -- destructAll.
       split.
       --- eapply SizeValid_subst_weak_size; eauto.
       --- eapply QualValid_subst_weak_size; eauto.
  - rewrite <-add_constraints_snoc.
    erewrite subst'_kindvars_snoc_weaks; eauto.
    eapply IHkvs'; eauto.
    -- match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       rewrite add_constraints_snoc; auto.
    -- rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
Qed.

Lemma TypeValid_add_constraint_size :
  (forall F t,
      TypeValid F t ->
      forall kvs f F'' szs0 szs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
        F = add_constraints F'' kvs ->
        TypeValid (add_constraints F'' (SIZE szs0 szs1 :: (subst_ext (weak SSize) kvs)))
                  (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall kvs f F'' szs0 szs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
        F = add_constraints F'' kvs ->
        HeapTypeValid (add_constraints F'' (SIZE szs0 szs1 :: (subst_ext (weak SSize) kvs)))
                      (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall kvs f F'' szs0 szs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
        F = add_constraints F'' kvs ->
        ArrowTypeValid (add_constraints F'' (SIZE szs0 szs1 :: (subst_ext (weak SSize) kvs)))
                       (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall kvs f F'' szs0 szs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SSize 1) ->
        F = add_constraints F'' kvs ->
        FunTypeValid (add_constraints F'' (SIZE szs0 szs1 :: (subst_ext (weak SSize) kvs)))
                     (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.
  all: try now ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs; econstructor; eauto; try erewrite qual_fctx_subst_weak_size; auto).
  - unfold get_var'.
    all: try ltac:(erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ]).
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ |- context[QualT (?F SPretype ?A zero) _] ] =>
      replace (F SPretype A zero) with (TVar A)
    end.
    2:{
      match goal with
      | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
        let H' := fresh "H" in
        assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
        case H'; intros
      end.
      - match goal with
        | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
        end.
      - match goal with
        | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
        end.
    }
    
    simpl.
    destructAll.
    econstructor.
    4: rewrite qual_fctx_subst_weak_size; eauto.
    all: try rewrite qual_fctx_subst_weak_size; auto.
    erewrite type_fctx_subst_weak_size.
    2:{
      constructor; eauto.
    }
    erewrite nth_error_map; do 2 eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_size; eauto.
    -- erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual;
         [ | | eapply debruijn_weaks_conds_under_knd ];
         eauto; solve_ineqs.
    -- eapply RecVarUnderRefPretype_weaks_non_pretype; eauto.
       --- eapply debruijn_weaks_conds_under_knd; eauto.
       --- simpl; auto.
    -- simpl.
       erewrite type_fctx_subst_weak_size; eauto.
       match goal with
       | [ |- sizeOfPretype (?A :: map ?F ?B) _ = _ ] =>
         replace (A :: map F B) with (map F (A :: B)) by auto
       end.
       erewrite debruijn_weaks_conds_under_no_effect; eauto.
       erewrite sizeOfPretype_weaks_less_gen; eauto.
       --- match goal with
           | [ H : ?A = _ |- context[?A] ] => rewrite H
           end.
           simpl; eauto.
       --- simpl.
           rewrite add_constraints_to_ks_of_kvs; simpl.
           rewrite app_length.
           rewrite length_collect_tctx.
           lia.
    -- eapply SizeValid_subst_weak_size; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] =>
         match goal with
         | [ H' : context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)]
             |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_pretype ?F _] ] =>
         match goal with
         | [ |- context[(?SZ1, ?SZ2) :: size ?C] ] =>
           specialize (H F C SZ1 SZ2)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_weaks_conds_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
       --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
           rewrite add_constraints_snoc.
           simpl.
           match goal with
           | [ |- context[subst'_qual ?F ?Q] ] =>
             replace (subst'_qual F Q) with Q; auto
           end.
           erewrite weak_non_qual_no_effect_on_qual; eauto.
           solve_ineqs.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    all: try rewrite qual_fctx_subst_weak_size; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       erewrite weak_non_qual_no_effect_on_qual; eauto.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H; specialize (H _ H')
       end.
       simpl in *; auto.
       solve_ineqs.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       eauto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size; auto.
    -- rewrite loc_fctx_subst_weak_size.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size; auto.
    -- rewrite loc_fctx_subst_weak_size.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size; auto.
    -- rewrite loc_fctx_subst_weak_size.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
 - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- rewrite qual_fctx_subst_weak_size.
       do 2 ltac:(try erewrite weak_non_qual_no_effect_on_qual; eauto).
       3:{
         eapply debruijn_weaks_conds_under_knd; eauto.
       }
       all: solve_ineqs.
    -- match goal with
       | [ H : forall _ _ _, _ |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
         match goal with
         | [ |- context[subst'_pretype ?F _] ] =>
           match goal with
           | [ H' : QualValid (qual (add_constraints ?C _)) _
               |- context[(?SZ1, ?SZ2) :: size ?C] ] =>
             specialize (H (KVS ++ [LOC]) F C SZ1 SZ2)
           end
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_weaks_conds_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
       --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
           rewrite add_constraints_snoc.
           simpl; auto.
  - erewrite weak_non_qual_no_effect_on_qual; eauto; [ | now solve_ineqs ].
    econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size; auto.
    -- rewrite qual_fctx_subst_weak_size; auto.
    -- rewrite loc_fctx_subst_weak_size.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs; simpl.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    destructAll.

    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    erewrite type_fctx_subst_weak_size; eauto.
    erewrite sizeOfPretype_weaks_less_gen; eauto.
    2:{
      rewrite add_constraints_to_ks_of_kvs.
      simpl.
      rewrite app_length.
      rewrite length_collect_tctx.
      lia.
    }
    match goal with
    | [ H : ?A = _ |- context[?A] ] => rewrite H
    end.
    simpl; auto.
    eexists; split; eauto.
    repeat split; eauto.
    -- eapply SizeValid_subst_weak_size; eauto.
    -- eapply SizeValid_subst_weak_size; eauto.
    -- eapply SizeLeq_subst_weak_size; eauto.
  - econstructor; eauto.
    -- rewrite qual_fctx_subst_weak_size.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  - econstructor; eauto.
    -- eapply SizeValid_subst_weak_size; eauto.
    -- rewrite qual_fctx_subst_weak_size.
       erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    -- erewrite weak_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       match goal with
       | [ H : forall _ _, _ |- _ ] =>
         match goal with
         | [ H' : context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)]
             |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_type ?F _] ] =>
         match goal with
         | [ H' : context[qual (add_constraints ?C _)]
             |- context[(?SZ1,?SZ2) :: size ?C] ] =>
           specialize (H F C SZ1 SZ2)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_weaks_conds_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
       --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
           rewrite add_constraints_snoc.
           simpl.
           match goal with
           | [ |- context[subst'_qual ?F ?Q] ] =>
             replace (subst'_qual F Q) with Q; auto
           end.
           erewrite weak_non_qual_no_effect_on_qual; eauto.
           solve_ineqs.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
      end.
    all: eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_subst_weak_size; eauto.
    -- match goal with
       | [ |- context[add_constraints (add_constraints ?F ?KVS1) ?KVS2] ] =>
         replace
           (add_constraints (add_constraints F KVS1) KVS2)
           with
             (add_constraints F (KVS1 ++ KVS2))
       end.
       2:{ rewrite add_constraints_app; auto. }
       erewrite subst'_kindvars_app_weaks; eauto.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       2:{ rewrite add_constraints_app; auto. }
       rewrite ks_of_kvs_app.
       apply debruijn_weaks_conds_under_kindvars; auto.
Qed.

Lemma weak_non_size_no_effect_on_size_gen : forall {sz f ks ks'},
    debruijn_weaks_conds f ks ks' ->
    ks' SSize = 0 ->
    subst'_size f sz = sz.
Proof.
  induction sz; simpl; auto.
  intros.
  unfold get_var'.
  unfold debruijn_weaks_conds in *.
  destructAll.
  match goal with
  | [ |- _ ?KND ?V _ = _ ] =>
    let H := fresh "H" in
    assert (H : V < ks KND \/ V >= ks KND) by apply Nat.lt_ge_cases;
    case H; intros
  end.
  -- match goal with
     | [ H : context[_ < _ -> _] |- _ ] =>
       erewrite H; eauto
     end.
  -- match goal with
     | [ H : context[_ >= _ -> _] |- _ ] =>
       erewrite H; eauto
     end.
     match goal with
     | [ H : _ = 0 |- _ ] => rewrite H
     end.
     unfold zero; simpl; auto.
  -- intros.
     erewrite IHsz1; eauto.
     erewrite IHsz2; eauto.
Qed.

Lemma weak_non_size_no_effect_on_sizes_gen : forall {szs f ks ks'},
    debruijn_weaks_conds f ks ks' ->
    ks' SSize = 0 ->
    subst'_sizes f szs = szs.
Proof.
  induction szs; simpl; auto.
  intros.
  erewrite IHszs; eauto.
  erewrite weak_non_size_no_effect_on_size_gen; eauto.
Qed.

Lemma add_constraint_weak_qual : forall {f ks ks' kv szctx},
    debruijn_weaks_conds f ks ks' ->
    ks' SSize = 0 ->
    add_constraint_to_szctx
      szctx
      (subst'_kindvar f kv) =
    add_constraint_to_szctx szctx kv.
Proof.
  intros.
  destruct kv; simpl; auto.
  do 2 match goal with
       | [ H : debruijn_weaks_conds ?F _ _ |- context[subst'_sizes ?F ?SZS] ] =>
         replace (subst'_sizes F SZS) with SZS; auto
       end.
  all: erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
Qed.

Lemma collect_szctx_weak_qual_gen : forall {kvs f ks ks' szctx},
    debruijn_weaks_conds f ks ks' ->
    ks' SSize = 0 ->
    fold_left
      add_constraint_to_szctx
      (subst'_kindvars f kvs)
      szctx =
    fold_left add_constraint_to_szctx kvs szctx.
Proof.
  induction kvs; simpl; auto.
  intros.
  erewrite add_constraint_weak_qual; eauto.
  eapply IHkvs; eauto.
  eapply debruijn_weaks_conds_under_knd; eauto.
Qed.

Lemma collect_szctx_weak_qual : forall {kvs},
    collect_szctx (subst'_kindvars (subst'_of (weak SQual)) kvs) =
    collect_szctx kvs.
Proof.
  intros.
  unfold collect_szctx.
  eapply collect_szctx_weak_qual_gen; eauto.
  - apply single_weak_debruijn_weak_conds.
  - auto.
Qed.

Lemma size_fctx_subst_weak_qual : forall {F kvs qs0 qs1},
    size
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SQual))
            (update_qual_ctx ((qs0, qs1) :: qual F) F))
         (subst'_kindvars (subst'_of (weak SQual)) kvs))
    =
    size
      (add_constraints F kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  do 2 rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite collect_szctx_weak_qual.
  match goal with
  | [ |- context[map _ (map ?A ?B)] ] =>
    replace (map A B) with B
  end.
  1: rewrite ks_of_kvs_subst_kindvars; auto.
  apply eq_sym.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite weak_non_size_no_effect_on_sizes; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  erewrite weak_non_size_no_effect_on_sizes; [ | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
  auto.
Qed.

Lemma QualValid_subst_weak_qual : forall {q f F kvs qs0 qs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
    QualValid (qual (add_constraints F kvs)) q ->
    QualValid
      (qual
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SQual))
                                 (update_qual_ctx ((qs0, qs1) :: qual F) F))
            (subst'_kindvars (subst'_of (weak SQual)) kvs)))
      (subst'_qual f q).
Proof.
  destruct q; intros.
  - rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
    unfold get_var'.
    unfold debruijn_weaks_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ >= ?KS _ -> ?F _ _ _ = _],
        H'' : context[_ < ?KS _ -> ?F _ _ _ = _]
        |- QualValid _ (?F ?KND ?V _) ] =>
      let H' := fresh "H" in
      assert (H' : V < KS KND \/ V >= KS KND) by apply Nat.lt_ge_cases;
      case H'; intros; [ rewrite H'' | rewrite H ]; auto
    end.
    all: simpl.
    all:
      match goal with
      | [ |- QualValid ?L (QualVar ?SZ) ] =>
        let H := fresh "H" in
        assert (H : SZ < length L);
        [ | apply nth_error_some_exists in H; destructAll;
            eapply QualVarValid; eauto ]
      end.
    all: rewrite app_length.
    all: repeat rewrite map_length.
    all: rewrite length_collect_qctx.
    all: rewrite ks_of_kvs_subst_kindvars.
    -- lia.
    -- destruct F; subst; simpl in *.
       match goal with
       | [ H : QualValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : QualVar _ = _ |- _ ] => inv H
         end.
       match goal with
       | [ H : nth_error _ _ = Some _ |- _ ] =>
         apply nth_error_Some_length in H
       end.
       rewrite app_length in *.
       rewrite map_length in *.
       rewrite length_collect_qctx in *.
       lia.
  - econstructor; simpl; eauto.
Qed.

Lemma QualLeq_weaks_gen : forall {f ks' ks q q' qctx' prf qctx},
    debruijn_weaks_conds f ks' ks ->
    length qctx' = ks' SQual ->
    length prf = ks SQual ->
    QualLeq (qctx' ++ qctx) q q' = Some true ->
    QualLeq
      ((map
          (fun '(qs0, qs1) =>
             (subst'_quals f qs0, subst'_quals f qs1))
          qctx')
         ++
         prf
         ++
         map
         (fun '(qs2, qs3) =>
            (subst'_quals f qs2, subst'_quals f qs3))
         qctx)
      (subst'_qual f q)
      (subst'_qual f q') =
    Some true.
Proof.
  intros.
  rewrite QualLeq_desc in *.
  eapply ctx_imp_leq_map; eauto.
  intros.
  match goal with
  | [ H : model_satisfies_context _ _ ?M _,
      H' : debruijn_weaks_conds _ ?KSP ?KS |- _ ] =>
    exists (fun v => M (if v <? KSP SQual then v else v + KS SQual))
  end.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B); [ | split; auto ]
  end.
  { apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with
    | [ |- context[subst'_qual _ ?X] ] => destruct X
    end.
    all: simpl in *; auto.
    unfold debruijn_weaks_conds in *.
    destructAll.
    unfold get_var'.
    match goal with
    | [ |- context[?A <? ?B] ] =>
      remember (A <? B) as obj; specialize (eq_sym Heqobj); case obj; intros
    end.
    - rewrite OrdersEx.Nat_as_OT.ltb_lt in *.
      match goal with
      | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
      end.
    - rewrite OrdersEx.Nat_as_OT.ltb_ge in *.
      match goal with
      | [ H : context[_ >= _ -> _] |- _ ] => rewrite H; auto
      end.
      simpl.
      unfold zero.
      rewrite <-plus_n_O.
      rewrite Nat.add_comm; auto. }
  
  rewrite model_satisfies_context_desc in *.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    rewrite model_satisfies_context_desc in H
  end.
  intros.
  match goal with
  | [ H : interp_qual _ = _ |- _ ] => rewrite H
  end.
  match goal with
  | [ H : forall _ _ _, nth_error ?L _ = Some _ -> _,
      H' : nth_error _ ?IDX = Some (?L1, ?L2),
      H'' : debruijn_weaks_conds ?F ?KSP ?KS |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : nth_error
                   L
                   (if IDX <? KSP SQual then IDX else IDX + KS SQual)
                 =
                 Some
                   (subst'_quals f L1,
                    subst'_quals f L2));
    [ | specialize (H _ _ _ H0) ]
  end.
  { match goal with
    | [ |- context[?A <? ?B] ] =>
      remember (A <? B) as obj; specialize (eq_sym Heqobj); case obj; intros
    end.
    - rewrite OrdersEx.Nat_as_OT.ltb_lt in *.
      rewrite nth_error_app1 in *; try lia.
      2:{ rewrite map_length; lia. }
      erewrite nth_error_map; eauto.
      simpl; auto.
    - rewrite OrdersEx.Nat_as_OT.ltb_ge in *.
      rewrite nth_error_app2 in *; try lia.
      2:{ rewrite map_length; lia. }
      rewrite map_length.
      rewrite nth_error_app2 by lia.
      match goal with
      | [ H : nth_error _ ?IDX = Some _ 
          |- nth_error _ ?IDX2 = Some _ ] =>
        replace IDX2 with IDX by lia
      end.
      erewrite nth_error_map; eauto.
      simpl; auto. }
  destructAll.
  split; prepare_Forall.
  all: rewrite Forall_forall in *.
  all: unfold subst'_quals in *.
  all:
    match goal with
    | [ H : context[List.In _ (map ?F ?B)], H' : List.In ?A ?B |- _ ] =>
      let H'' := fresh "H" in
      assert (H'' : List.In (F A) (map F B)) by ltac:(apply in_map; auto);
      specialize (H _ H''); auto
    end.
Qed.

Lemma collect_qctx_subst_weak_qual : forall {kvs f},
  debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
  collect_qctx (subst'_kindvars (subst'_of (weak SQual)) kvs)
  =
  map (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1)) (collect_qctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall f,
            debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
            collect_qctx (subst'_kindvars (subst'_of (weak SQual)) kvs)
            =
            map (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1)) (collect_qctx kvs))).
  all: auto.
  intros.
  match goal with
  | [ |- context[collect_qctx (?A ++ _)] ] =>
    specialize (pure_under_kindvars_weaks (kvs:=A) (knd:=SQual))
  end.
  intros.
  erewrite <-subst'_kindvars_snoc_weaks; eauto.
  repeat rewrite collect_qctx_snoc.
  match goal with
  | [ H : forall _, _ -> _ |- _ ] => erewrite H; eauto
  end.
  all: rewrite ks_of_kvs_snoc in *.
  destruct x; simpl in *.
  all:
    try match goal with
        | [ H : debruijn_weaks_conds ?F1 _ _,
            H' : debruijn_weaks_conds ?F2 _ _
            |- map _ _ = map _ _ ] =>
          replace F1 with F2; auto
        end.
  all: try eapply debruijn_weaks_conds_under_no_effect_sing; eauto.
  repeat match goal with
         | [ |- context[subst'_quals ?F ?SZ] ] =>
           replace (subst'_quals F SZ) with (subst_ext' F SZ) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  match goal with
  | [ |- (subst_ext' ?F1 _, _) :: _ =
         (subst_ext' ?F2 _, _) :: _ ] =>
    replace F2 with F1; auto
  end.
  2:{ eapply debruijn_weaks_comm; eauto.
      all: apply single_weak_debruijn_weak_conds. }
  match goal with
  | [ |- _ :: ?A = _ :: ?B ] => replace B with A; auto
  end.
  repeat rewrite map_map.
  match goal with
  | [ |- map ?F1 _ = map ?F2 _ ] => replace F2 with F1; auto
  end.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct_prs.
  repeat match goal with
         | [ |- context[subst'_quals ?F ?SZ] ] =>
           replace (subst'_quals F SZ) with (subst_ext' F SZ) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  match goal with
  | [ |- (subst_ext' ?F1 _, _) =
         (subst_ext' ?F2 _, _) ] =>
    replace F2 with F1; auto
  end.
  eapply debruijn_weaks_comm; eauto.
  all: apply single_weak_debruijn_weak_conds.
Qed.

Lemma qual_update_qual_ctx : forall F qctx,
    qual (update_qual_ctx qctx F) = qctx.
Proof.
  intros.
  destruct F; subst; simpl in *.
  auto.
Qed.

Lemma QualLeq_subst_weak_qual : forall {q1 q2 f F kvs qs0 qs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
    QualLeq (qual (add_constraints F kvs)) q1 q2 = Some true ->
    QualLeq
      (qual
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SQual))
                                 (update_qual_ctx ((qs0, qs1) :: qual F) F))
            (subst'_kindvars (subst'_of (weak SQual)) kvs)))
      (subst'_qual f q1)
      (subst'_qual f q2)
    =
    Some true.
Proof.
  intros.
  rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  rewrite ks_of_kvs_subst_kindvars.
  rewrite qual_update_qual_ctx.
  simpl.
  rewrite map_map.
  match goal with
  | [ H : context[_ ++ ?A] |- context[_ :: ?B] ] =>
    replace B with (map (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1)) A)
  end.
  2:{
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat match goal with
           | [ |- context[subst'_quals ?A ?B] ] =>
             replace (subst'_quals A B) with (subst_ext' A B) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    erewrite subst_weaks_weak_comm; eauto.
  }
  erewrite collect_qctx_subst_weak_qual; eauto.
  match goal with
  | [ |- context[?A :: ?B] ] => replace (A :: B) with ([A] ++ B) by auto
  end.
  eapply QualLeq_weaks_gen; eauto.
  rewrite length_collect_qctx; auto.
Qed.

Lemma size_weak_no_effect_on_qual : forall q,
    subst.subst'_qual
      (debruijn.subst'_of (debruijn.weak subst.SSize)) q
    =
    q.
Proof.
  destruct q; auto.
Qed.

Lemma type_fctx_subst_weak_qual_helper : forall {F F' kv f f' ks},
    type F =
    map
      (fun '(sz, q, hc) => (sz, subst'_qual f q, hc))
      (type F') ->
    debruijn_weaks_conds
      f
      ks
      (sing SQual 1) ->
    debruijn_weaks_conds
      f'
      (plus (sing (kind_of_kindvar kv) 1) ks)
      (sing SQual 1) ->
    type (add_constraint F (subst'_kindvar f kv)) =
    map
      (fun '(sz, q, hc) => (sz, subst'_qual f' q, hc))
      (type (add_constraint F' kv)).
Proof.
  intros.
  destruct kv; simpl.
  - replace (fun '(s, q, hc) => (subst'_size (subst'_of (weak SLoc)) s, subst'_qual (subst'_of (weak SLoc)) q, hc)) with (fun (tpl : (Size * Qual * HeapableConstant)) => tpl).
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      destruct_prs.
      rewrite loc_weak_no_effect_on_size.
      rewrite loc_weak_no_effect_on_qual; auto.
    }
    repeat rewrite map_id.
    repeat rewrite type_update_location_ctx; auto.
    erewrite <-debruijn_weaks_conds_under_no_effect_sing; eauto.
  - repeat rewrite type_update_qual_ctx.
    rewrite map_map.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat match goal with
           | [ |- context[subst'_qual ?F ?SZ] ] =>
             replace (subst'_qual F SZ) with (subst_ext' F SZ) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    simpl in *.
    erewrite debruijn_weaks_comm; eauto.
    all: apply single_weak_debruijn_weak_conds.
  - repeat rewrite type_update_size_ctx.
    rewrite map_map.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat rewrite size_weak_no_effect_on_qual.
    match goal with
    | [ |- (_, ?Q1, _) = (_, ?Q2, _) ] =>
      replace Q2 with Q1; auto
    end.
    erewrite debruijn_weaks_conds_under_no_effect_sing; eauto.
  - repeat rewrite type_update_type_ctx.
    rewrite map_map.
    simpl.
    repeat rewrite pretype_weak_no_effect_on_size.
    repeat rewrite pretype_weak_no_effect_on_qual.
    match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end.
    rewrite map_map.
    erewrite weak_non_size_no_effect_on_size_gen; eauto.
    match goal with
    | [ |- _ :: map ?F1 _ = _ :: map ?F2 _ ] =>
      replace F2 with F1; auto
    end.
    1:{ erewrite debruijn_weaks_conds_under_no_effect_sing; eauto. }
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    repeat rewrite pretype_weak_no_effect_on_size.
    repeat rewrite pretype_weak_no_effect_on_qual.
    erewrite debruijn_weaks_conds_under_no_effect_sing; eauto.
Qed.

Lemma type_fctx_subst_weak_qual : forall {kvs F qs0 qs1 f},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
    type
      (add_constraints
         (subst'_function_ctx (subst'_of (weak SQual))
                              (update_qual_ctx ((qs0, qs1) :: qual F) F))
         (subst'_kindvars (subst'_of (weak SQual)) kvs)) =
    map
      (fun '(sz, q, hc) =>
         (sz,
          subst'_qual f q,
          hc))
      (type (add_constraints F kvs)).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall F qs0 qs1 f,
            debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
            type
              (add_constraints
                 (subst'_function_ctx (subst'_of (weak SQual))
                                      (update_qual_ctx ((qs0, qs1) :: qual F) F))
                 (subst'_kindvars (subst'_of (weak SQual)) kvs)) =
            map
              (fun '(sz, q, hc) =>
                 (sz,
                  subst'_qual f q,
                  hc))
              (type (add_constraints F kvs)))).
  - intros; simpl.
    rewrite type_update_qual_ctx.
    match goal with
    | [ |- map ?A _ = map ?B _ ] => replace A with B; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    destruct_prs.
    erewrite weak_non_size_no_effect_on_size; [ eauto | | apply single_weak_debruijn_weak_conds ]; solve_ineqs.
    match goal with
    | [ |- (_, subst'_qual ?F1 _, _) = (_, subst'_qual ?F2 _, _) ] =>
      replace F1 with F2; auto
    end.
    eapply debruijn_weaks_conds_inj; eauto.
    simpl.
    apply single_weak_debruijn_weak_conds.
  - intros.
    match goal with
    | [ H : context[ks_of_kvs (?L ++ _)],
        H' : forall _ _ _ _, _
        |- context[(?QS0, ?QS1) :: qual ?F] ] =>
      specialize (H' F QS0 QS1 (under_kindvars' L (subst'_of (weak SQual))))
    end.
    match goal with
    | [ H : ?A -> type _ = _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    1:{ eapply pure_under_kindvars_weaks; eauto. }

    rewrite add_constraints_snoc.
    erewrite <-subst'_kindvars_app_weaks; eauto.
    simpl.
    rewrite add_constraints_snoc.
    rewrite ks_of_kvs_snoc in *.
    eapply type_fctx_subst_weak_qual_helper; eauto.
Qed.

Lemma eifc_map_second_comp : forall {A B C} {l : list (A * B * C)} {f},
    equal_in_first_comp (map (fun '(sz0, q0, hc) => (sz0, f q0, hc)) l) l.
Proof.
  induction l; intros; simpl.
  1:{ apply eifc_nil. }
  destruct_prs.
  apply eifc_cons.
  eauto.
Qed.

Lemma loc_fctx_subst_weak_qual : forall {kvs qs1 qs2 F},
    location
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SQual))
            (update_qual_ctx
               ((qs1, qs2) :: (qual F)) F))
         (subst'_kindvars (subst'_of (weak SQual)) kvs))
    =
    location
      (add_constraints F kvs).
Proof.
  intros.
  rewrite add_constraints_to_ks_of_kvs; simpl.
  rewrite ks_of_kvs_subst_kindvars.
  rewrite add_constraints_to_ks_of_kvs; simpl.
  destruct F; simpl; auto.
Qed.

Lemma SizeValid_subst_weak_qual : forall {sz f F kvs qs0 qs1},
    debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
    SizeValid (size (add_constraints F kvs)) sz ->
    SizeValid
      (size
         (add_constraints
            (subst'_function_ctx (subst'_of (weak SQual))
                                 (update_qual_ctx ((qs0, qs1) :: qual F) F))
            (subst'_kindvars (subst'_of (weak SQual)) kvs)))
      (subst'_size f sz).
Proof.
  intros.
  erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
  match goal with
  | [ X : Size |- _ ] => induction X
  end.
  all: try now ltac:(eapply SizeConstValid; eauto).
  - rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizeVar _ = _ |- _ ] => inv H
      end.
    match goal with
    | [ |- SizeValid ?L (SizeVar ?V) ] =>
      assert (exists q, nth_error L V = Some q);
      [ | destructAll; eapply SizeVarValid; eauto ]
    end.
    apply nth_error_some_exists.
    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] =>
      apply nth_error_Some_length in H
    end.
    rewrite app_length in *.
    rewrite length_collect_szctx in *.
    rewrite ks_of_kvs_subst_kindvars.
    repeat rewrite map_length in *.
    destruct F; subst; simpl in *; auto.
  - match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizePlus _ _ = _ |- _ ] => inv H
      end.
    eapply SizePlusValid; eauto.
Qed.

Lemma KindVarsValid_subst_weak_qual : forall {kvs' f kvs F qs0 qs1},
  KindVarsValid (add_constraints F kvs) kvs' ->
  debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
  KindVarsValid
    (add_constraints
       (subst'_function_ctx (subst'_of (weak SQual))
          (update_qual_ctx ((qs0, qs1) :: qual F) F))
       (subst'_kindvars (subst'_of (weak SQual)) kvs))
    (subst'_kindvars f kvs').
Proof.
  induction kvs'; [ econstructor | ].
  intros.
  simpl.
  econstructor.
  - match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
    match goal with
    | [ |- KindVarValid _ (subst'_kindvar _ ?KV) ] =>
      destruct KV; simpl in *; auto
    end.
    -- destructAll.
       split.
       all: unfold subst'_quals.
       all: prepare_Forall_with_map.
       all: eapply QualValid_subst_weak_qual; eauto.
    -- destructAll.
       split.
       all: unfold subst'_sizes.
       all: prepare_Forall_with_map.
       all: eapply SizeValid_subst_weak_qual; eauto.
    -- destructAll.
       split.
       --- eapply SizeValid_subst_weak_qual; eauto.
       --- eapply QualValid_subst_weak_qual; eauto.
  - rewrite <-add_constraints_snoc.
    erewrite subst'_kindvars_snoc_weaks; eauto.
    eapply IHkvs'; eauto.
    -- match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       rewrite add_constraints_snoc; auto.
    -- rewrite ks_of_kvs_app; simpl.
       apply debruijn_weaks_conds_under_knd; auto.
Qed.

Lemma TypeValid_add_constraint_qual :
  (forall F t,
      TypeValid F t ->
      forall kvs f F'' qs0 qs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
        F = add_constraints F'' kvs ->
        TypeValid (add_constraints F'' (QUAL qs0 qs1 :: (subst'_kindvars (subst'_of (weak SQual)) kvs)))
                  (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall kvs f F'' qs0 qs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
        F = add_constraints F'' kvs ->
        HeapTypeValid (add_constraints F'' (QUAL qs0 qs1 :: (subst'_kindvars (subst'_of (weak SQual)) kvs)))
                      (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall kvs f F'' qs0 qs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
        F = add_constraints F'' kvs ->
        ArrowTypeValid (add_constraints F'' (QUAL qs0 qs1 :: (subst'_kindvars (subst'_of (weak SQual)) kvs)))
                       (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall kvs f F'' qs0 qs1,
        debruijn_weaks_conds f (ks_of_kvs kvs) (sing SQual 1) ->
        F = add_constraints F'' kvs ->
        FunTypeValid (add_constraints F'' (QUAL qs0 qs1 :: (subst'_kindvars (subst'_of (weak SQual)) kvs)))
                     (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.
  - econstructor; eauto.
    eapply QualValid_subst_weak_qual; eauto.
  - unfold get_var'.
    match goal with
    | [ H : debruijn_weaks_conds _ _ _ |- _ ] =>
      generalize H; destruct H; intros
    end.
    destructAll.
    unfold Peano.ge in *.
    match goal with
    | [ |- context[QualT (?F SPretype ?A zero) _] ] =>
      replace (F SPretype A zero) with (TVar A)
    end.
    2:{
      match goal with
      | [ H : context[_ < ?F _] |- context[_ SPretype ?V _] ] =>
        let H' := fresh "H" in
        assert (H' : V < F SPretype \/ F SPretype <= V) by apply Nat.lt_ge_cases;
        case H'; intros
      end.
      - match goal with
        | [ H : context[_ < _ -> _] |- _ ] => rewrite H; auto
        end.
      - match goal with
        | [ H : context[_ <= _ -> _] |- _ ] => rewrite H; auto
        end.
    }
    
    simpl.
    econstructor.
    4: eapply QualLeq_subst_weak_qual; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- erewrite type_fctx_subst_weak_qual; eauto.
       erewrite nth_error_map; do 2 eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- erewrite debruijn_weaks_conds_under_no_effect; eauto.
       eapply QualValid_subst_weak_qual; eauto.
    -- erewrite debruijn_weaks_conds_under_no_effect; eauto.
       eapply QualLeq_subst_weak_qual; eauto.
    -- erewrite debruijn_weaks_conds_under_no_effect; eauto.
       eapply QualLeq_subst_weak_qual; eauto.
    -- eapply RecVarUnderRefPretype_weaks_non_pretype; eauto.
       --- eapply debruijn_weaks_conds_under_knd; eauto.
       --- simpl; auto.
    -- erewrite type_fctx_subst_weak_qual; eauto.
       simpl.
       erewrite sizeOfPretype_weaks_only_size_matters; eauto.
       erewrite sizeOfPretype_eifc; eauto.
       2:{ eapply debruijn_weaks_conds_under_knd; eauto. }
       2:{ auto. }
       constructor; auto.
       eapply eifc_map_second_comp; eauto.
    -- match goal with
       | [ H : debruijn_weaks_conds ?F _ _ |- SizeValid _ ?SZ ] =>
           replace SZ with (subst'_size F SZ)
       end.
       2:{
         erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
       }
       eapply SizeValid_subst_weak_qual; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] =>
         match goal with
         | [ H' : context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)]
             |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_pretype ?F _] ] =>
         match goal with
         | [ |- context[(?QS1, ?QS2) :: qual ?C] ] =>
           specialize (H F C QS1 QS2)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_weaks_conds_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
       --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
           rewrite add_constraints_snoc.
           simpl.
           match goal with
           | [ |- context[subst'_size ?F ?SZ] ] =>
             replace (subst'_size F SZ) with SZ; auto
           end.
           erewrite weak_non_size_no_effect_on_size; eauto.
           solve_ineqs.
  - econstructor; eauto.
    eapply QualValid_subst_weak_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       eapply QualLeq_subst_weak_qual; eauto.
       match goal with
       | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
         rewrite Forall_forall in H; specialize (H _ H')
       end.
       simpl in *; auto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       eauto.
  - econstructor; eauto.
    eapply QualValid_subst_weak_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- rewrite loc_fctx_subst_weak_qual.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- rewrite loc_fctx_subst_weak_qual.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- rewrite loc_fctx_subst_weak_qual.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
 - econstructor; eauto.
   -- eapply QualValid_subst_weak_qual; eauto.
   -- erewrite debruijn_weaks_conds_under_no_effect; eauto.
      eapply QualLeq_subst_weak_qual; eauto.
   -- match goal with
      | [ H : forall _ _ _, _ |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
        match goal with
        | [ |- context[subst'_pretype ?F _] ] =>
          match goal with
          | [ H' : QualValid (qual (add_constraints ?C _)) _
              |- context[(?QS1, ?QS2) :: qual ?C] ] =>
            specialize (H (KVS ++ [LOC]) F C QS1 QS2)
          end
        end
      end.
      match goal with
      | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
        replace F2 with F; [ apply H | ]
      end.
      --- rewrite ks_of_kvs_app.
          simpl.
          apply debruijn_weaks_conds_under_knd; auto.
      --- rewrite add_constraints_snoc.
          simpl; auto.
      --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
          rewrite add_constraints_snoc.
          simpl; auto.
  - econstructor; eauto.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- match goal with
       | [ |- context[subst'_qual ?F _] ] =>
         replace (QualConst Linear) with (subst'_qual F Linear) by auto
       end.
       eapply QualLeq_subst_weak_qual; eauto.
    -- rewrite loc_fctx_subst_weak_qual.
       eapply LocValid_subst_weak; eauto.
       unfold sing; unfold dec_eq; simpl; lia.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs; simpl.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    destructAll.

    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    erewrite type_fctx_subst_weak_qual; eauto.
    erewrite sizeOfPretype_eifc; eauto.
    2:{ apply eifc_map_second_comp. }
    erewrite sizeOfPretype_weaks_only_size_matters; eauto.
    eexists; split; eauto.
    split; [ | split ]; eauto.
    -- rewrite size_fctx_subst_weak_qual.
       erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
    -- rewrite size_fctx_subst_weak_qual.
       auto.
    -- rewrite size_fctx_subst_weak_qual.
       erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
  - econstructor; eauto.
    match goal with
    | [ |- context[subst'_qual ?F _] ] =>
      replace (QualConst Unrestricted) with (subst'_qual F Unrestricted) by auto
    end.
    eapply QualLeq_subst_weak_qual; eauto.
  - econstructor; eauto.
    -- rewrite size_fctx_subst_weak_qual.
       erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
    -- eapply QualValid_subst_weak_qual; eauto.
    -- erewrite weak_non_size_no_effect_on_size; eauto; solve_ineqs.
       match goal with
       | [ H : forall _ _, _ |- _ ] =>
         match goal with
         | [ H' : context[update_type_ctx ((?SZ, ?Q, ?HC) :: _)]
             |- context[add_constraints _ (subst'_kindvars _ ?KVS)] ] =>
           specialize (H (KVS ++ [TYPE SZ Q HC]))
         end
       end.
       match goal with
       | [ H : forall _ _, _ |- context[subst'_type ?F _] ] =>
         match goal with
         | [ H' : context[qual (add_constraints ?C _)]
             |- context[(?QS1, ?QS2) :: qual ?C] ] =>
           specialize (H F C QS1 QS2)
         end
       end.
       match goal with
       | [ H : context[TypeValid ?F _] |- TypeValid ?F2 _ ] =>
         replace F2 with F; [ apply H | ]
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_weaks_conds_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
       --- erewrite <-subst'_kindvars_snoc_weaks; eauto.
           rewrite add_constraints_snoc.
           simpl.
           match goal with
           | [ |- context[subst'_size ?F ?SZ] ] =>
             replace (subst'_size F SZ) with SZ; auto
           end.
           erewrite weak_non_size_no_effect_on_size; eauto.
           solve_ineqs.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
      end.
    all: eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_subst_weak_qual; eauto.
    -- match goal with
       | [ |- context[add_constraints (add_constraints ?F ?KVS1) ?KVS2] ] =>
         replace
           (add_constraints (add_constraints F KVS1) KVS2)
           with
             (add_constraints F (KVS1 ++ KVS2))
       end.
       2:{ rewrite add_constraints_app; auto. }
       erewrite subst'_kindvars_app_weaks; eauto.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       2:{ rewrite add_constraints_app; auto. }
       rewrite ks_of_kvs_app.
       apply debruijn_weaks_conds_under_kindvars; auto.
Qed.

Lemma TypeValid_add_constraints : forall {kvs F pt q},
  TypeValid F (QualT pt q) ->
  TypeValid
    (add_constraints F kvs)
    (QualT
       (subst'_pretype (weaks' (ks_of_kvs kvs)) pt)
       (subst'_qual (weaks' (ks_of_kvs kvs)) q)).
Proof.
  induction kvs; simpl; auto.
  - intros.
    repeat rewrite weaks_zero_eq_id.
    rewrite id_no_effect_on_qual.
    repeat rewrite id_eq_var'.
    match goal with
    | [ |- context[?F var' ?B] ] =>
      replace (F var' B) with (subst_ext' var' B) by auto
    end.
    rewrite subst_ext'_var_e; auto.
  - intros.
    rewrite compose_weaks_weak.
    match goal with
    | [ |- context[subst'_pretype (?A ∘' ?B) ?C] ] =>
      replace (subst'_pretype (A ∘' B) C)
        with (subst_ext' (A ∘' B) C) by auto
    end.
    match goal with
    | [ |- context[subst'_qual (?A ∘' ?B) ?C] ] =>
      replace (subst'_qual (A ∘' B) C)
        with (subst_ext' (A ∘' B) C) by auto
    end.
    repeat rewrite <-subst_ext'_assoc.
    simpl.
    apply IHkvs.
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl
    end.
    1: specialize TypeValid_add_constraint_loc.
    2: specialize TypeValid_add_constraint_qual.
    3: specialize TypeValid_add_constraint_size.
    4: specialize TypeValid_add_constraint_pretype.
    all:
      let H' := fresh "H" in
      intro H'; destruct H' as [H' _].
    all:
      match goal with
      | [ H : TypeValid _ _,
          H' : forall _ _, _ -> _ |- _ ] =>
        specialize (H' _ _ H []); simpl in *; eapply H'; eauto
      end.
    all: apply single_weak_debruijn_weak_conds.
Qed.

Lemma TypeValid_debruijn_subst_provable :
  (forall F t,
      TypeValid F t ->
      forall f kvs pt sz sz' q hc F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SPretype pt ->
        sizeOfPretype (type F'') pt = Some sz' ->
        SizeValid (size F'') sz' ->
        SizeValid (size F'') sz ->
        SizeLeq (size F'') sz' sz = Some true ->
        TypeValid F'' (QualT pt q) ->
        F = add_constraints F'' (TYPE sz q hc :: kvs) ->
        F' = add_constraints F'' kvs ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f kvs pt sz sz' q hc F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SPretype pt ->
        sizeOfPretype (type F'') pt = Some sz' ->
        SizeValid (size F'') sz' ->
        SizeValid (size F'') sz ->
        SizeLeq (size F'') sz' sz = Some true ->
        TypeValid F'' (QualT pt q) ->
        F = add_constraints F'' (TYPE sz q hc :: kvs) ->
        F' = add_constraints F'' kvs ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f kvs pt sz sz' q hc F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SPretype pt ->
        sizeOfPretype (type F'') pt = Some sz' ->
        SizeValid (size F'') sz' ->
        SizeValid (size F'') sz ->
        SizeLeq (size F'') sz' sz = Some true ->
        TypeValid F'' (QualT pt q) ->
        F = add_constraints F'' (TYPE sz q hc :: kvs) ->
        F' = add_constraints F'' kvs ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f kvs pt sz sz' q hc F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SPretype pt ->
        sizeOfPretype (type F'') pt = Some sz' ->
        SizeValid (size F'') sz' ->
        SizeValid (size F'') sz ->
        SizeLeq (size F'') sz' sz = Some true ->
        TypeValid F'' (QualT pt q) ->
        F = add_constraints F'' (TYPE sz q hc :: kvs) ->
        F' = add_constraints F'' kvs ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.

  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    erewrite <-qual_fctx_subst_weak_pretype; eauto.
  - unfold get_var'.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> ?F ?KND] |- context[_ SPretype ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V = F KND \/ V <> F KND) by apply eq_dec_nat;
      case H'; intros; subst
    end.
    -- match goal with
       | [ H : context[_ SPretype ?V _] |- context[_ SPretype ?V _] ] =>
         rewrite H
       end.
       simpl.
       rewrite plus_zero.
       match goal with
       | [ H : nth_error _ _ = _ |- _ ] =>
         rewrite add_constraints_to_ks_of_kvs in H; simpl in H;
         rewrite weak_pretype_on_tctx in H;
         rewrite type_update_type_ctx in H; simpl in H;
         erewrite nth_error_app_appliable in H; eauto;
         [ inversion H; subst; simpl in * | ]
       end.
       2:{ apply eq_sym; apply length_collect_tctx; auto. }
       match goal with
       | [ H : QualLeq _ _ _ = _ |- _ ] =>
         rewrite qual_fctx_subst_weak_pretype in H
       end.
       eapply TypeValid_QualLeq; eauto.
       --- erewrite <-qual_fctx_subst_weak_pretype; eauto.
       --- apply TypeValid_add_constraints; auto.
    -- match goal with
       | [ H : context[_ <> _ _] |- _ ] => rewrite H; auto
       end.
       simpl.
       econstructor.
       4: erewrite <-qual_fctx_subst_weak_pretype; eauto.
       --- erewrite <-qual_fctx_subst_weak_pretype; eauto.
       --- erewrite <-qual_fctx_subst_weak_pretype; eauto.
       --- rewrite add_constraints_to_ks_of_kvs; simpl.
           match goal with
           | [ H : nth_error _ _ = _ |- _ ] =>
             rewrite add_constraints_to_ks_of_kvs in H; simpl in H
           end.
           erewrite nth_error_shift_down_appliable; eauto.
           match goal with
           | [ |- context[map _ (map ?F ?L)] ] =>
             replace (map F L) with L by ltac:(apply eq_sym; apply weak_pretype_on_tctx)
           end.
           rewrite type_update_type_ctx.
           simpl.
           apply eq_sym.
           eapply remove_nth_prefix_appliable; eauto.
           rewrite length_collect_tctx; auto.
  - match goal with
    | [ H : sizeOfPretype _ _ = Some _ |- _ ] =>
      rewrite add_constraints_to_ks_of_kvs in H;
      simpl in H; rewrite weak_pretype_on_tctx in H;
      rewrite type_update_type_ctx in H; simpl in H;
      rewrite app_comm_cons in H
    end.
    match goal with
    | [ H : debruijn_subst_ext_conds ?F ?KS SPretype ?PT |- _ ] =>
      let H' := fresh "H" in
      assert (H' : debruijn_subst_ext_conds (under' SPretype F) (plus (sing SPretype 1) KS) SPretype PT)
    end.
    { apply debruijn_subst_ext_under_knd; auto. }

    match goal with
    | [ H : sizeOfPretype (_ ++ (subst'_size ?F ?SZ, _, _) :: _) _ = Some _,
        H' : debruijn_subst_ext_conds (under' _ _) ?KS _ _ |- _ ] =>
      replace (subst'_size F SZ) with (subst'_size (weaks' KS) SZ) in H
    end.
    2:{
      apply subst_size_only_size_matters.
      unfold plus.
      simpl; auto.
    }

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst.
      1-2,5,8: eauto.
      all: auto.
      - match goal with
        | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
            replace F2 with F; auto
        end.
        rewrite add_constraints_to_ks_of_kvs.
        simpl.
        rewrite size_update_type_ctx.
        match goal with
        | [ |- ?A ++ ?B = _ ++ ?C ] =>
            replace C with B; eauto
        end.
        rewrite map_map.
        apply map_ext.
        intros.
        destruct_prs.
        unfold subst'_sizes.
        repeat rewrite map_map.
        match goal with
        | [ |- (map ?F _, _) = (map ?F2 _, _) ] =>
            replace F2 with F; auto
        end.
        apply FunctionalExtensionality.functional_extensionality.
        intros.
        rewrite pretype_weak_no_effect_on_size.
        apply subst_size_only_size_matters.
        unfold plus; simpl; auto.
      - rewrite length_collect_szctx.
        unfold plus; simpl; auto.
      - simpl.
        rewrite length_collect_tctx.
        unfold plus; simpl; auto.
      - rewrite map_map.
        apply map_ext.
        intros.
        destruct_prs.
        apply subst_size_only_size_matters.
        unfold plus; simpl; auto.
    }
    intros.
    split; auto.
    destructAll.

    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- eapply RecVarUnderRefPretype_subst_fwd; eauto.
       unfold plus; simpl; lia.
    -- simpl.
       rewrite add_constraints_to_ks_of_kvs; simpl.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- rewrite add_constraints_to_ks_of_kvs; simpl.
       match goal with
       | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
           replace F2 with F; auto
       end.
       simpl.
       match goal with
       | [ |- ?A ++ ?B = _ ++ ?C ] =>
           replace C with B; eauto
       end.
       apply map_ext.
       intros.
       destruct_prs.
       unfold subst'_sizes.
       match goal with
       | [ |- (map ?F _, _) = (map ?F2 _, _) ] =>
           replace F2 with F; auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply subst_size_only_size_matters.
       unfold plus; simpl; auto.
    -- match goal with
       | [ H : context[SizeLeq _ ?SZ ?SZP] |- TypeValid (subst_ext ?W (update_type_ctx ((?SZ, ?Q, ?HC) :: type ?F) ?F)) _ ] =>
         replace (subst_ext W (update_type_ctx ((SZ, Q, HC) :: type F) F)) with (update_type_ctx ((SZ, Q, HC) :: type F) (subst_ext W (update_type_ctx ((SZP, Q, HC) :: type F) F)));
         [ | destruct F; subst; simpl in * ]
       end.
       2:{
         simpl in *.
         unfold subst'_function_ctx.
         apply function_ctx_eq; simpl; auto.
         match goal with
         | [ |- ?TPL :: _ = ?TPL2 :: map ?F ?L ] =>
           replace (TPL2 :: map F L) with (map F (TPL :: L))
         end.
         2:{ simpl; auto. }
         rewrite weak_pretype_on_tctx; auto.
       }

       eapply TypeValid_SizeLeq.
       2:{
         match goal with
         | [ |- _ = _ :: type ?F ] => destruct F; subst; simpl in *
         end.
         match goal with
         | [ |- (subst'_size _ ?SZ, subst'_qual _ ?Q, ?HC) :: map ?F ?L = _ ] =>
           match goal with
           | [ |- ?A = _ ] =>
             replace A with (map F ((SZ, Q, HC) :: L))
           end
         end.
         2:{ simpl; auto. }
         rewrite weak_pretype_on_tctx; auto.
       }
       2:{
         match goal with
         | [ |- SizeLeq (size (subst_ext _ (update_type_ctx ((?SZ, ?Q, ?HC) :: _) (add_constraints ?F ?KVS)))) _ _ = _ ] =>
           match goal with
           | [ |- SizeLeq (size ?A) _ _ = _ ] =>
             replace A with (add_constraints F (KVS ++ [TYPE SZ Q HC]))
           end
         end.
         2:{ rewrite add_constraints_snoc; simpl; auto. }
         rewrite add_constraints_to_ks_of_kvs; simpl.
         match goal with
         | [ H : context[subst'_sizes (weaks' ?KS) _]
             |- context[subst'_sizes (weaks' ?KS2) _] ] =>
           replace KS2 with KS
         end.
         2:{
           rewrite ks_of_kvs_app.
           simpl.
           unfold plus; auto.
         }
         rewrite collect_szctx_snoc.
         simpl.
         auto.
       } 
         
       match goal with
       | [ H : forall _, _ |- _ ] =>
         eapply H; eauto
       end.
       3:{
         match goal with
         | [ |- subst_ext _ (update_type_ctx ((?SZ, ?Q, ?HC) :: ?T) (add_constraints ?F ?KVS)) = _ ] =>
           match goal with
           | [ |- ?A = _ ] =>
             replace A with (add_constraints F (KVS ++ [TYPE SZ Q HC])); eauto
           end
         end.
         rewrite add_constraints_snoc.
         simpl; auto.
       }
       --- match goal with
           | [ H : debruijn_subst_ext_conds ?F ?KS _ _
               |- debruijn_subst_ext_conds ?F ?KS2 _ _ ] =>
             replace KS2 with KS; auto
           end.
           rewrite ks_of_kvs_app.
           simpl; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       --- right; right.
           split; auto.
           ---- rewrite pretype_weak_no_effect_on_size_field.
                rewrite size_update_type_ctx.
                rewrite add_constraints_to_ks_of_kvs; simpl.
                match goal with
                | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
                    replace F2 with F; auto
                end.
                match goal with
                | [ |- ?A ++ ?B = _ ++ ?C ] =>
                    replace C with B; eauto
                end.
                apply map_ext.
                intros.
                destruct_prs.
                unfold subst'_sizes.
                match goal with
                | [ |- (map ?F _, _) = (map ?F2 _, _) ] =>
                    replace F2 with F; auto
                end.
                apply FunctionalExtensionality.functional_extensionality.
                intros.
                apply subst_size_only_size_matters.
                unfold plus; simpl; auto.
           ---- rewrite pretype_weak_no_effect_on_size_field.
                rewrite size_update_type_ctx.
                match goal with
                | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
                    replace F2 with F; auto
                end.
                rewrite add_constraints_to_ks_of_kvs; simpl.
                rewrite add_constraints_to_ks_of_kvs; simpl.
                match goal with
                | [ |- ?A ++ ?B = _ ++ ?C ] =>
                    replace C with B; eauto
                end.
                rewrite size_update_type_ctx.
                match goal with
                | [ |- map _ ?L = map _ ?L2 ] =>
                    replace L with L2; auto
                end.
                apply eq_sym.
                rewrite <-map_id.
                apply map_ext.
                intros.
                destruct_prs.
                unfold subst'_sizes.
                match goal with
                | [ |- context[map ?F] ] =>
                    replace (map F) with (fun (s : list Size) => s); auto
                end.
                apply FunctionalExtensionality.functional_extensionality.
                intros.
                apply eq_sym.
                rewrite <-map_id.
                apply map_ext.
                intros.
                apply pretype_weak_no_effect_on_size.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_pretype; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] =>
         apply in_map_inv in H; destructAll
       end.
       repeat match goal with
              | [ H : Forall _ ?TS, H' : List.In _ ?TS |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] =>
         inversion H; subst
       end.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] =>
         apply in_map_inv in H; destructAll
       end.
       repeat match goal with
              | [ H : Forall _ ?TS, H' : List.In _ ?TS |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       match goal with
       | [ H : ?X = _ |- TypeValid _ ?X ] => rewrite H
       end.
       match goal with
       | [ H : forall _ _ _ _ _ _, _ |- _ ] =>
         eapply H; eauto
       end.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-loc_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-loc_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-loc_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto;
         [ | | eapply debruijn_subst_ext_under_knd; eauto ];
         solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- match goal with
       | [ |- TypeValid (subst_ext _ (update_location_ctx _ (add_constraints ?F ?KVS))) _ ] =>
         match goal with
         | [ |- TypeValid ?FP _ ] =>
           replace FP with (add_constraints F (KVS ++ [LOC]))
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc.
           simpl; auto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-loc_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    rewrite Forall_forall.
    intros.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] =>
      apply in_map_inv in H; destructAll
    end.
    match goal with
    | [ H : Forall _ ?TS, H' : List.In _ ?TS |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] =>
      inversion H; subst
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
  - econstructor; eauto.
    rewrite Forall_forall.
    intros.
    destruct_prs.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] =>
      apply in_map_inv in H; destructAll
    end.
    destruct_prs.
    repeat match goal with
           | [ X : Typ |- _ ] => destruct X
           end.
    simpl in *.
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] =>
      inversion H; subst; simpl in *
    end.
    match goal with
    | [ H : Forall _ ?TS, H' : List.In _ ?TS |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H'); destructAll
    end.
    simpl in *.

    match goal with
    | [ H : sizeOfPretype (type (add_constraints _ _)) _ = _ |- _ ] =>
      rewrite add_constraints_to_ks_of_kvs in H;
      simpl in H;
      rewrite weak_pretype_on_tctx in H;
      rewrite type_update_type_ctx in H;
      simpl in H
    end.
        
    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst.
      1-2,5,8: eauto.
      all: auto.
      - match goal with
        | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
            replace F2 with F; auto
        end.
        rewrite add_constraints_to_ks_of_kvs; simpl.
        match goal with
        | [ |- ?A ++ ?B = _ ++ ?C ] =>
            replace C with B; eauto
        end.
        rewrite size_update_type_ctx.
        match goal with
        | [ |- map _ ?L = map _ ?L2 ] =>
            replace L with L2; auto
        end.
        apply eq_sym.
        rewrite <-map_id.
        apply map_ext.
        intros.
        destruct_prs.
        unfold subst'_sizes.
        match goal with
        | [ |- context[map ?F] ] =>
            replace (map F) with (fun (s : list Size) => s); auto
        end.
        apply FunctionalExtensionality.functional_extensionality.
        intros.
        apply eq_sym.
        rewrite <-map_id.
        apply map_ext.
        intros.
        apply pretype_weak_no_effect_on_size.
      - apply length_collect_szctx.
      - apply length_collect_tctx.
      - rewrite map_map.
        apply map_ext.
        intros.
        destruct_prs; auto.
    }
    intros; split; auto.
    destructAll.

    eexists.
    split.
    { rewrite add_constraints_to_ks_of_kvs; simpl; eauto. }
    split.
    { erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
      rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
      rewrite update_type_ctx_no_effect_on_size_field in *.
      rewrite sizepairs_debruijn_weak_pretype in *.
      auto. }
    split.
    { rewrite add_constraints_to_ks_of_kvs; simpl; auto. }
    split.
    2:{
      erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
      rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
      rewrite update_type_ctx_no_effect_on_size_field in *.
      rewrite sizepairs_debruijn_weak_pretype in *.
      eapply SizeLeq_Trans; [ | eauto ].
      auto.
    }
    match goal with
    | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_pretype; eauto.
  - econstructor; eauto.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-size_fctx_subst_weak_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_pretype; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- match goal with
           | [ H : context[subst'_function_ctx _ (update_type_ctx ((?SZ, ?Q, ?HC) :: _) _) = _],
               H' : debruijn_subst_ext_conds _ (ks_of_kvs ?KVS) _ _
               |- debruijn_subst_ext_conds _ ?KS _ _ ] =>
             replace KS with (ks_of_kvs (KVS ++ [TYPE SZ Q HC])) by eauto
           end.
           rewrite ks_of_kvs_app.
           simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
           erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
  - econstructor; eauto.
    all: rewrite Forall_forall.
    all: intros.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    all:
      match goal with
      | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
      end.        
    all:
      match goal with
      | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
      end.
  - econstructor; eauto.
    -- erewrite pretype_subst_no_effect_on_kindvars; eauto.
       eapply KindVarsValid_Function_Ctx; eauto.
       --- erewrite qual_fctx_subst_weak_pretype; eauto.
       --- erewrite size_fctx_subst_weak_pretype; eauto.
    -- rewrite add_constraints_app.
       match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app.
           erewrite pretype_subst_no_effect_on_kindvars; eauto.
           apply debruijn_subst_ext_under_kindvars; auto.
       --- erewrite pretype_subst_no_effect_on_kindvars; eauto.
           rewrite add_constraints_app; auto.
Qed.

Lemma TypeValid_debruijn_subst_nonfree_var F tau sz q pt sz' hc :
  TypeValid
    (subst'_function_ctx
       (debruijn.subst'_of (debruijn.weak subst.SPretype))
       (update_type_ctx ((sz, q, hc) :: type F) F))
    tau ->
  sizeOfPretype (type F) pt = Some sz' ->
  SizeValid (size F) sz' ->
  SizeValid (size F) sz ->
  SizeLeq (size F) sz' sz = Some true ->
  TypeValid F (QualT pt q) ->
  TypeValid
    F
    (subst.subst'_type
       (debruijn.subst'_of
          (debruijn.ext subst.SPretype pt debruijn.id))
       tau).
Proof.
  intros.
  specialize TypeValid_debruijn_subst_provable.
  let H := fresh "H" in intro H; destruct H as [H _]; eapply H; eauto.
  3:{
    replace F with (add_constraints F []) at 1; eauto.
  }
  2:{
    simpl; auto.
  }
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma LocValid_subst_loc_fwd : forall {f kvs F l l'},
  LocValid
    (location
       (add_constraints
          (subst'_function_ctx
             (subst'_of (weak SLoc))
             (update_location_ctx (location F + 1) F))
          kvs)) l ->
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l' ->
  LocValid (location F) l' ->
  LocValid (location (add_constraints F kvs)) (subst'_loc f l).
Proof.
  intros.
  simpl in *.
  destruct F; subst; simpl in *.
  match goal with
  | [ H : LocValid _ _ |- _ ] =>
    erewrite location_fctx_subst_weak_loc in H
  end.
  rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  destruct l; simpl in *.
  2: econstructor; eauto.
  unfold get_var'.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ H : LocValid _ (LocV _) |- _ ] =>
    inv H;
    match goal with
    | [ H : LocV _ = _ |- _ ] => inv H
    end
  end.
  match goal with
  | [ H : context[_ <> ?V2 -> _ SLoc _ _ = _]
      |- context[_ SLoc ?V _] ] =>
    let H' := fresh "H" in
    assert (H' : V = V2 \/ V <> V2) by apply eq_dec_nat;
    case H'; intros; subst
  end.
  - match goal with
    | [ H : context[_ SLoc ?V _] |- context[_ SLoc ?V _] ] =>
      rewrite H
    end.
    simpl.
    rewrite plus_zero.
    match goal with
    | [ H : LocValid _ _ |- _ ] =>
      inv H; simpl; [ econstructor; eauto | ]
    end.
    unfold get_var'.
    unfold weaks'.
    unfold debruijn.var.
    simpl.
    unfold zero; rewrite Nat.add_0_r.
    econstructor 2; eauto.
    lia.
  - match goal with
    | [ H : context[_ <> _ -> _ SLoc _ _ = _] |- _ ] =>
      rewrite H; auto
    end.
    simpl.
    econstructor 2; eauto.
    unfold zero.
    unfold shift_down_after.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as obj; generalize (eq_sym Heqobj);
      case obj; intros
    end.
    -- rewrite Nat.ltb_lt in *.
       lia.
    -- rewrite Nat.ltb_ge in *.
       lia.
Qed.

Lemma TypeValid_debruijn_subst_loc_provable :
  (forall F t,
      TypeValid F t ->
      forall f kvs l F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        LocValid (location F'') l ->
        F = add_constraints F'' (LOC :: kvs) ->
        F' = add_constraints F'' kvs ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f kvs l F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        LocValid (location F'') l ->
        F = add_constraints F'' (LOC :: kvs) ->
        F' = add_constraints F'' kvs ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f kvs l F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        LocValid (location F'') l ->
        F = add_constraints F'' (LOC :: kvs) ->
        F' = add_constraints F'' kvs ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f kvs l F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SLoc l ->
        LocValid (location F'') l ->
        F = add_constraints F'' (LOC :: kvs) ->
        F' = add_constraints F'' kvs ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst; auto.

  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    erewrite <-qual_fctx_subst_weak_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> SLoc -> _] |- _ ] => rewrite H; solve_ineqs
    end.
    simpl.
    econstructor.
    4: erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- erewrite <-type_fctx_subst_weak_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    match goal with
    | [ |- TypeValid _ (QualT _ (subst'_qual _ ?Q)) ] =>
      erewrite (qual_debruijn_subst_ext (q:=Q)); eauto; solve_ineqs
    end.
    econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- eapply RecVarUnderRefPretype_subst_non_pretype; auto.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- simpl.
       erewrite sizeOfPretype_subst_no_effect;
         [ | eapply debruijn_subst_ext_under_knd | ];
         eauto; solve_ineqs.
       erewrite <-type_fctx_subst_weak_loc; eauto.
    -- match goal with
       | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
           replace F2 with F; auto
       end.
       repeat rewrite add_constraints_to_ks_of_kvs; simpl.
       match goal with
       | [ |- ?A ++ ?B = _ ++ ?C ] =>
           replace C with B; eauto
       end.
       rewrite size_update_location_ctx.
       match goal with
       | [ |- map _ ?L = map _ ?L2 ] =>
           replace L with L2; auto
       end.
       apply eq_sym.
       rewrite <-map_id.
       apply map_ext.
       intros.
       destruct_prs.
       unfold subst'_sizes.
       match goal with
       | [ |- context[map ?F] ] =>
           replace (map F) with (fun (s : list Size) => s); auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply eq_sym.
       rewrite <-map_id.
       apply map_ext.
       intros.
       apply loc_weak_no_effect_on_size.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           match goal with
           | [ |- context[(?SZ, ?Q, ?HC)] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
    -- prepare_Forall.
       erewrite <-qual_fctx_subst_weak_loc; eauto.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
       end.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       simpl in *.
       auto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_loc; eauto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_loc_fwd; eauto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_loc_fwd; eauto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_loc_fwd; eauto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           replace F with (add_constraints FP (KVS ++ [LOC]))
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_loc_fwd; eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
    end.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    simpl in *.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    destructAll.
    simpl in *.
    erewrite <-type_fctx_subst_weak_loc; eauto.
    erewrite <-size_fctx_subst_weak_loc; eauto.
    eexists; split.
    { erewrite sizeOfPretype_subst_no_effect; eauto; solve_ineqs. }
    split.
    { erewrite size_debruijn_subst_ext; eauto; solve_ineqs. }
    split; auto.
    split.
    { match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end. }
    erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
  - econstructor; eauto.
    erewrite <-qual_fctx_subst_weak_loc; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
  - econstructor; eauto.
    -- erewrite <-size_fctx_subst_weak_loc; eauto.
       erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[(?SZ, ?Q, ?HC)] ] =>
           match goal with
           | [ |- context[add_constraints ?FP ?KVS] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      repeat match goal with
             | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
               rewrite Forall_forall in H; specialize (H _ H')
             end.
    all:
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
  - econstructor; eauto.
    -- erewrite kindvars_debruijn_subst_ext; eauto; solve_ineqs.
       eapply KindVarsValid_Function_Ctx; eauto.
       --- erewrite qual_fctx_subst_weak_loc; eauto.
       --- erewrite size_fctx_subst_weak_loc; eauto.
    -- match goal with
       | [ |- context[add_constraints (add_constraints ?F ?KVS1) ?KVS2] ] =>
         replace
           (add_constraints (add_constraints F KVS1) KVS2)
           with
             (add_constraints F (KVS1 ++ KVS2))
       end.
       2:{ rewrite add_constraints_app; auto. }
       erewrite kindvars_debruijn_subst_ext; eauto; solve_ineqs.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- rewrite ks_of_kvs_app.
           apply debruijn_subst_ext_under_kindvars; auto.
       --- rewrite add_constraints_app; auto.
Qed.

Lemma debruijn_subst_ext_only_qual_matters : forall {f ks ks' q},
    debruijn_subst_ext_conds f ks SQual q ->
    ks SQual = ks' SQual ->
    debruijn_subst_ext_conds f ks' SQual q.
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  split; intros.
  { rewrite <-H0.
    rewrite H.
    destruct q; simpl; auto.
    unfold get_var'.
    unfold weaks'.
    unfold plus.
    rewrite H0; auto. }
  split; intros.
  - rewrite H1; auto.
    rewrite H0; auto.
  - rewrite H2; auto.
Qed.

Lemma subst_ext'_comm_qual : forall {obj f f' ks},
    debruijn_subst_ext_conds f (plus (sing SQual 1) ks) SQual obj ->
    debruijn_subst_ext_conds f' ks SQual obj ->
    (subst'_of (weak SQual)) ∘' f' =
    f ∘' (subst'_of (weak SQual)).
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold comp'.
  match goal with
  | [ X : Ind |- _ ] =>
    let H := fresh "H" in
	assert (H : X = SQual \/ X <> SQual) by apply eq_dec_ind;
    case H; intros; subst
  end.
  - match goal with
    | [ H : context[_ <> ?KS _ -> ?F _ _ _ = _] |- context[?F ?K ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V = KS K \/ V <> KS K) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : context[?F ?K ?V _] |- context[?F ?K ?V _] ] =>
         rewrite H
       end.
       simpl.
       unfold get_var'.
       unfold under_ks'.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
       end.
       unfold plus in *; simpl in *.
       unfold zero.
       match goal with
       | [ |- _ = _ _ (?A + ?B + ?C - ?D) _ ] =>
         replace (A + B + C - D) with C by lia
       end.
       match goal with
       | [ H : context[?F ?K ?V _] |- context[?F ?K ?V _] ] =>
         rewrite H
       end.
       match goal with
       | [ X : Qual |- _ ] => destruct X; simpl; auto
       end.
       unfold get_var'.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
       end.
       simpl.
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.
       match goal with
       | [ |- QualVar ?A = QualVar ?B ] => replace B with A; auto
       end.
       unfold zero; lia.
    -- simpl.
       unfold get_var'.
       unfold under_ks'.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with false
       end.
       2:{
         apply eq_sym.
         rewrite Nat.ltb_ge.
         unfold shift_down_after.
         match goal with
         | [ |- context[if ?B then _ else _] ] =>
           remember B as obj2; generalize (eq_sym Heqobj2);
           case obj2; intros; try lia
         end.
         rewrite Nat.ltb_ge in *.
         lia.
       }
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
       end.
       rewrite plus_zero.
       unfold subst'_of.
       unfold shifts'.
       unfold subst'.
       simpl.
       unfold zero.
       match goal with
       | [ |- _ = _ _ (?A + ?B + ?C - ?D) _ ] =>
         replace (A + B + C - D) with C by lia
       end.
       unfold get_var'.
       unfold weaks'.
       unfold plus in *.
       simpl in *.
       match goal with
       | [ H : context[_ <> Datatypes.S _ -> _] |- _ ] =>
         rewrite H by lia
       end.
       unfold var.
       simpl.
       match goal with
       | [ |- QualVar ?A = QualVar ?B ] => replace B with A; auto
       end.
       unfold zero; unfold shift_down_after.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         remember B as obj3; generalize (eq_sym Heqobj3);
         case obj3; intros; subst
       end.
       --- match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with true
           end.
           lia.
       --- match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with false
           end.
           rewrite Nat.ltb_ge in *.
           lia.
  - match goal with
    | [ H : context[_ <> SQual -> _],
        H' : context[_ <> SQual -> _] |- _ ] =>
      try rewrite H; auto; try rewrite H'; auto
    end.
    match goal with
    | [ X : Ind |- _ ] => destruct X; solve_impossibles
    end.
    all: simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all: unfold zero; rewrite Nat.add_0_r.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
      end.
    all:
      match goal with
      | [ H : context[_ <> SQual -> _],
          H' : context[_ <> SQual -> _] |- _ ] =>
        try rewrite H; auto; try rewrite H'; auto
      end.
    all: simpl.
    all: unfold get_var'.
    all: unfold weaks'.
    all: unfold var.
    all: simpl.
    all:
      match goal with
      | [ |- ?F ?A = ?F ?B ] => replace B with A; auto
      end.
Qed.

Lemma collect_tctx_subst_qual : forall {kvs q f},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
  collect_tctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs)
  =
  map
    (fun '(sz, q', hc) =>
       (sz,
        subst'_qual f q',
        hc))
    (collect_tctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall q f,
            debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
            collect_tctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs)
            =
            map
              (fun '(sz, q', hc) =>
                 (sz,
                  subst'_qual f q',
                  hc))
              (collect_tctx kvs))).
  all: simpl; auto.
  intros.
  match goal with
  | [ H : debruijn_subst_ext_conds _ (ks_of_kvs (?L ++ _)) ?KND ?OBJ |- _ ] =>
    specialize (pure_under_kindvars L KND OBJ)
  end.
  intros.
  erewrite <-subst'_kindvars_snoc; eauto.
  do 2 rewrite collect_tctx_snoc.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl
  end.
  - match goal with
    | [ H : forall _, _ |- _ ] => apply H
    end.
    eapply debruijn_subst_ext_only_qual_matters; eauto.
    rewrite ks_of_kvs_app; simpl.
    unfold plus; simpl; auto.
  - erewrite H; eauto.
    repeat rewrite map_map.
    apply map_ext.
    intros.
    destruct_prs.
    match goal with
    | [ |- (_, ?A, _) = (_, ?B, _) ] => replace B with A; auto
    end.
    match goal with
    | [ H : context[ks_of_kvs (_ ++ _)] |- _ ] =>
      rewrite ks_of_kvs_app in H; simpl in H
    end.
    repeat match goal with
           | [ |- context[subst'_qual ?F (subst'_qual ?F2 ?Q)] ] =>
             replace (subst'_qual F (subst'_qual F2 Q))
               with
                 (subst_ext' F (subst_ext' F2 Q)) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    erewrite subst_ext'_comm_qual; eauto.
  - erewrite H; eauto.
    repeat rewrite map_map.
    apply map_ext.
    intros.
    destruct_prs; auto.
    match goal with
    | [ |- (_, ?A, _) = (_, ?B, _) ] => replace B with A; auto
    end.
    match goal with
    | [ |- subst'_qual ?F _ =
           subst'_qual ?F2 _ ] =>
      replace F with F2; auto
    end.
    eapply debruijn_subst_ext_inj; eauto.
    eapply debruijn_subst_ext_only_qual_matters; eauto.
    rewrite ks_of_kvs_app; simpl.
    unfold plus; simpl; auto.
  - erewrite H; eauto.
    match goal with
    | [ H : debruijn_subst_ext_conds ?F _ _ _,
        H' : debruijn_subst_ext_conds ?F2 _ _ _ |- _ ] =>
      replace F2 with F; auto
    end.
    2:{
      eapply debruijn_subst_ext_inj; eauto.
      eapply debruijn_subst_ext_only_qual_matters; eauto.
      rewrite ks_of_kvs_app; simpl.
      unfold plus; simpl; auto.
    }
    erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
Qed.

Lemma subst_weaks_weak_qual : forall {f kvs q q0},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
    subst'_qual (weaks' (ks_of_kvs kvs)) q0 = subst'_qual f (subst'_qual (weaks' (ks_of_kvs kvs)) (subst'_qual (subst'_of (weak SQual)) q0)).
Proof.
  intros.
  match goal with
  | [ |- subst'_qual _ ?Q = _ ] => destruct Q; simpl; auto
  end.
  unfold get_var'.
  unfold under_kindvars'.
  unfold zero; rewrite Nat.add_0_r.
  unfold weaks'.
  unfold var.
  simpl; rewrite Nat.add_0_r.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ H : context[_ <> _ SQual -> _] |- _ ] => rewrite H by lia
  end.
  simpl.
  match goal with
  | [ |- QualVar ?A = QualVar ?B ] => replace B with A; auto
  end.
  unfold shift_down_after.
  match goal with
  | [ |- _ = if ?B then _ else _ ] =>
    replace B with false
  end.
  2:{
    apply eq_sym.
    rewrite Nat.ltb_ge.
    lia.
  }
  simpl; lia.
Qed.  

Lemma subst_weaks_weak_quals : forall {qs f kvs q},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
    subst'_quals (weaks' (ks_of_kvs kvs)) qs = subst'_quals f (subst'_quals (weaks' (ks_of_kvs kvs)) (subst'_quals (subst'_of (weak SQual)) qs)).
Proof.
  induction qs; intros; simpl in *; auto.
  erewrite subst_weaks_weak_qual; eauto.
  erewrite IHqs; eauto.
Qed.

Lemma type_subst_qual : forall {F f q qs0 qs1 kvs},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
  type
    (add_constraints
       F
       (subst'_kindvars
          (subst'_of (ext SQual q id))
          kvs))
  =
  map
    (fun '(sz, q', hc) =>
       (sz, subst'_qual f q', hc))
    (type
       (add_constraints
          (subst'_function_ctx
             (subst'_of (weak SQual))
             (update_qual_ctx
                ((qs0, qs1) :: qual F) F))
          kvs)).
Proof.
  intros.
  repeat rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite map_app.
  repeat rewrite map_map.
  erewrite collect_tctx_subst_qual; eauto.
  match goal with
  | [ |- _ ++ ?X = _ ++ ?Y ] => replace Y with X; auto
  end.
  destruct F; subst; simpl in *.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite qual_weak_no_effect_on_size.
  rewrite ks_of_kvs_subst_kindvars.
  match goal with
  | [ |- (_, ?A, _) = (_, ?B, _) ] => replace B with A; auto
  end.
  eapply subst_weaks_weak_qual; eauto.
Qed.

Lemma nth_error_type_subst_qual : forall {F f q qs0 qs1 sz qa hc kvs idx},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
    nth_error
      (type
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SQual))
               (update_qual_ctx
                  ((qs0, qs1) :: qual F) F))
            kvs))
      idx
    =
    Some (sz, qa, hc) ->
    nth_error
      (type
         (add_constraints
            F
            (subst'_kindvars
               (subst'_of (ext SQual q id))
               kvs)))
      idx
    =
    Some (sz, subst'_qual f qa, hc).
Proof.
  intros.
  erewrite type_subst_qual; eauto.
  erewrite map_nth_error; eauto.
  simpl; auto.
Qed.

Lemma under_non_qual_no_effect_on_qual : forall {f ks knd' obj q knd},
    debruijn_subst_ext_conds f ks knd' obj ->
    knd <> SQual ->
    subst'_qual (under' knd f) q = subst'_qual f q.
Proof.
  intros.
  destruct q; simpl; auto.
  unfold get_var'.
  unfold under'.
  unfold under_ks'.
  unfold sing.
  destruct knd; solve_impossibles; simpl.
  all: rewrite Nat.sub_0_r.
  all: unfold debruijn_subst_ext_conds in *.
  all: destructAll.
  all: destruct knd'; simpl.
  all:
    match goal with
    | [ H : context[_ <> SQual -> _] |- _ ] => idtac
    | [ H : context[_ <> _ -> _] |- _ ] =>
      do 2 ltac:(rewrite H; simpl; solve_ineqs); auto
    end.
  all: simpl in *.
  all:
    match goal with
    | [ H : context[_ <> ?F SQual -> _] |- _ _ ?V _ = _ ] =>
      let H' := fresh "H" in
      assert (H' : V = F SQual \/ V <> F SQual) by apply eq_dec_nat;
        case H'; intros; subst;
          [ | do 2 ltac:(rewrite H; auto; unfold plus; simpl) ]
    end.
  all:
    match goal with
    | [ H : forall _, _ = _ |- _ ] => do 2 rewrite H
    end.
  all:
    match goal with
    | [ X : Qual |- _ ] => destruct X; simpl; auto
    end.
Qed.

Lemma eifc_subst_qual : forall {F q qs0 qs1 kvs},
  equal_in_first_comp
    (type
       (add_constraints F
          (subst'_kindvars (subst'_of (ext SQual q id)) kvs)))
    (type
       (add_constraints
          (subst'_function_ctx (subst'_of (weak SQual))
                               (update_qual_ctx ((qs0, qs1) :: qual F) F)) kvs)).
Proof.
  intros.
  erewrite type_subst_qual; eauto.
  2:{ apply pure_under_kindvars. }
  match goal with
  | [ |- equal_in_first_comp (map _ ?X) ?Y ] =>
    replace X with Y by auto;
    remember Y as obj; clear Heqobj; induction obj
  end.
  - simpl; constructor.
  - simpl.
    destruct_prs.
    constructor; auto.
Qed.

Lemma LocValid_subst_qual : forall {F l f ks kvs q qs0 qs1},
    debruijn_subst_ext_conds f ks SQual q ->
    LocValid
      (location
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SQual))
               (update_qual_ctx
                  ((qs0, qs1) :: (qual F))
                  F))
            kvs))
      l ->
    LocValid
      (location
         (add_constraints
            F
            (subst'_kindvars
               (subst'_of (ext SQual q id))
               kvs)))
      (subst'_loc f l).
Proof.
  intros.
  destruct F; subst; simpl in *.
  repeat rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  match goal with
  | [ H : LocValid _ _ |- _ ] => inv H; simpl
  end.
  - econstructor; eauto.
  - unfold get_var'.
    rewrite ks_of_kvs_subst_kindvars.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> SQual -> _] |- _ ] =>
      rewrite H; solve_ineqs
    end.
    simpl.
    econstructor 2; eauto.
Qed.

Lemma collect_szctx_subst_qual : forall {kvs q},
    collect_szctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs) =
    collect_szctx kvs.
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall q,
            collect_szctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs) =
            collect_szctx kvs)).
  all: intros; simpl in *; auto.

  erewrite <-subst'_kindvars_snoc; eauto.
  2:{ apply pure_under_kindvars. }
  repeat rewrite collect_szctx_snoc.
  rewrite H.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl; auto
  end.
  match goal with
  | [ |- context[subst'_sizes _ (subst'_sizes ?F ?SZ)] ] =>
    erewrite (sizes_debruijn_subst_ext (f:=F))
  end.
  3:{ apply pure_under_kindvars. }
  all: solve_ineqs.
  match goal with
  | [ |- context[subst'_sizes _ (subst'_sizes ?F ?SZ)] ] =>
    erewrite (sizes_debruijn_subst_ext (f:=F))
  end.
  3:{ apply pure_under_kindvars. }
  all: solve_ineqs.
  auto.
Qed.

Lemma size_fctx_subst_qual : forall {F qs0 qs1 q kvs},
    size
      (add_constraints
         F
         (subst'_kindvars
            (subst'_of (ext SQual q id))
            kvs))
    =
    size
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SQual))
            (update_qual_ctx
               ((qs0, qs1) :: qual F)
               F))
         kvs).
Proof.
  intros.
  destruct F; subst; simpl in *.
  repeat rewrite add_constraints_to_ks_of_kvs; simpl.
  rewrite ks_of_kvs_subst_kindvars.
  match goal with
  | [ |- context[map _ (map ?F ?L)] ] =>
    replace (map F L) with L
  end.
  2:{
    apply eq_sym.
    rewrite <-map_id.
    apply map_ext.
    intros.
    destruct_prs.
    repeat rewrite qual_weak_no_effect_on_sizes; auto.
  }
  rewrite collect_szctx_subst_qual; auto.
Qed.

Lemma subst_quals_comm : forall {qs obj f f' ks},
    debruijn_subst_ext_conds f (plus (sing SQual 1) ks) SQual obj ->
    debruijn_subst_ext_conds f' ks SQual obj ->
    subst'_quals (subst'_of (weak SQual)) (subst'_quals f' qs) =
    subst'_quals f (subst'_quals (subst'_of (weak SQual)) qs).
Proof.
  induction qs; simpl; auto.
  intros.
  repeat match goal with
         | [ |- context[subst'_qual ?F (subst'_qual ?F2 ?Q)] ] =>
           replace (subst'_qual F (subst'_qual F2 Q))
             with
               (subst_ext' F (subst_ext' F2 Q)) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  erewrite subst_ext'_comm_qual; eauto.
  erewrite IHqs; eauto.
Qed.

Lemma collect_qctx_subst_qual : forall {kvs q f},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
  collect_qctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs)
  =
  map (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1)) (collect_qctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall q f,
            debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
            collect_qctx (subst'_kindvars (subst'_of (ext SQual q id)) kvs)
            =
            map (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1)) (collect_qctx kvs))).
  all: intros; simpl in *.

  - unfold collect_qctx; simpl; auto.
  - erewrite <-subst'_kindvars_snoc; eauto.
    2:{ apply pure_under_kindvars. }
    repeat rewrite collect_qctx_snoc.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H
    end.
    2:{ apply pure_under_kindvars. }
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl; auto
    end.
    2:{
      match goal with
      | [ H : context[ks_of_kvs (_ ++ _)] |- _ ] =>
        rewrite ks_of_kvs_app in H; simpl in H
      end.
      erewrite subst_quals_comm; eauto.
      2:{ apply pure_under_kindvars. }
      erewrite subst_quals_comm; eauto.
      2:{ apply pure_under_kindvars. }
      match goal with
      | [ |- _ :: ?A = _ :: ?B ] => replace B with A; auto
      end.
      repeat rewrite map_map.
      apply map_ext.
      intros.
      destruct_prs.
      erewrite subst_quals_comm; eauto.
      2:{ apply pure_under_kindvars. }
      erewrite subst_quals_comm; eauto.
      apply pure_under_kindvars.
    }
    all: apply map_ext.
    all: intros.
    all: destruct_prs.
    all:
      match goal with
      | [ |- (subst'_quals ?F _, _) = (subst'_quals ?F2 _, _) ] =>
        replace F2 with F; auto
      end.
    all: erewrite debruijn_subst_ext_inj; eauto.
    all: eapply debruijn_subst_ext_only_qual_matters.
    all: try apply pure_under_kindvars.
    all: rewrite ks_of_kvs_app; simpl.
    all: unfold plus; simpl; auto.
Qed.

Lemma subst_weak_comm_quals : forall {qs ks},
    subst'_quals (weaks' ks) (subst'_quals (subst'_of (weak SQual)) qs) =
    subst'_quals (subst'_of (weak SQual)) (subst'_quals (weaks' ks) qs).
Proof.
  induction qs; simpl; auto.
  intros.
  rewrite IHqs.
  match goal with
  | [ X : Qual |- _ ] => destruct X; simpl; auto
  end.
  unfold get_var'.
  simpl.
  unfold get_var'.
  unfold weaks'.
  unfold var.
  simpl.
  unfold zero.
  rewrite Nat.add_0_r.
  rewrite Nat.add_succ_r; auto.
Qed.

Lemma collect_qctx_subst_size : forall {kvs sz},
    collect_qctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) =
    collect_qctx kvs.
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall sz,
            collect_qctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) =
            collect_qctx kvs)).
  all: intros; simpl in *; auto.
  erewrite <-subst'_kindvars_snoc; eauto.
  2:{ apply pure_under_kindvars. }
  repeat rewrite collect_qctx_snoc.
  rewrite H.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl; auto
  end.
  match goal with
  | [ |- context[subst'_quals _ (subst'_quals ?F _)] ] =>
    replace (subst'_quals F) with (fun x : list Qual => x); auto
  end.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  erewrite quals_debruijn_subst_ext; eauto.
  2:{ apply pure_under_kindvars. }
  solve_ineqs.
Qed.

Lemma qual_fctx_subst_weak_size_subst_size : forall {F kvs szs0 szs1 sz},
    qual
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SSize))
            (update_size_ctx ((szs0, szs1) :: size F) F))
         kvs)
    =
    qual
      (add_constraints
         F
         (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)).
Proof.
  intros.
  repeat rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite collect_qctx_subst_size.
  match goal with
  | [ |- _ ++ ?A = _ ++ ?B ] => replace B with A; auto
  end.
  destruct F; subst; simpl in *.
  rewrite map_map.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite ks_of_kvs_subst_kindvars.
  match goal with
  | [ |- context[subst'_quals _ (subst'_quals ?F _)] ] =>
    replace (subst'_quals F) with (fun x : list Qual => x); auto
  end.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  erewrite weak_non_qual_no_effect_on_quals; eauto.
  2:{ apply single_weak_debruijn_weak_conds. }
  solve_ineqs.
Qed.

Lemma weaks_only_size_matters : forall {sz ks ks'},
    ks SSize = ks' SSize ->
    subst'_size (weaks' ks) sz =
    subst'_size (weaks' ks') sz.
Proof.
  induction sz; simpl; intros; auto.

  - unfold get_var'.
    unfold weaks'.
    simpl.
    rewrite H; auto.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma debruijn_subst_ext_only_size_matters : forall {f ks ks' sz},
    debruijn_subst_ext_conds f ks SSize sz ->
    ks SSize = ks' SSize ->
    debruijn_subst_ext_conds f ks' SSize sz.
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.

  split.
  { intros.
    rewrite <-H0.
    rewrite H.
    simpl.
    erewrite weaks_only_size_matters; eauto.
    unfold plus.
    rewrite H0; auto. }
  split; simpl; intros.
  { rewrite <-H0.
    rewrite H1; auto.
    rewrite H0; auto. }
  rewrite H2; auto.
Qed.

Lemma under_ks_weaks_comp : forall {knd ks ks'},
  under_ks' ks' (subst'_of (weak knd)) ∘' weaks' (plus ks ks') =
  weaks' (plus (plus (sing knd 1) ks) ks').
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold comp'.
  match goal with
  | [ X : Ind |- _ ] => destruct X; simpl
  end.
  all: unfold get_var'.
  all: unfold under_ks'.
  all: unfold plus.
  all:
    match goal with
    | [ |- (if ?B then _ else _) = _ ] =>
      replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
    end.
  all:
    match goal with
    | [ |- (if ?B then _ else _) = _ ] =>
      replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
    end.
  all: simpl.
  all: unfold get_var'.
  all: unfold weaks'.
  all: unfold var.
  all: simpl.
  all:
    match goal with
    | [ |- ?F ?A = ?F ?B ] => replace B with A; auto
    end.
  all: unfold zero; lia.
Qed.

Lemma subst_ext'_comm_size : forall {obj f f' ks},
    debruijn_subst_ext_conds f (plus (sing SSize 1) ks) SSize obj ->
    debruijn_subst_ext_conds f' ks SSize obj ->
    (subst'_of (weak SSize)) ∘' f' =
    f ∘' (subst'_of (weak SSize)).
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold comp'.
  match goal with
  | [ X : Ind |- _ ] =>
    let H := fresh "H" in
	assert (H : X = SSize \/ X <> SSize) by apply eq_dec_ind;
    case H; intros; subst; simpl
  end.
  - unfold get_var'.
    unfold under_ks' at 2.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false
    end.
    2:{
      apply eq_sym.
      rewrite Nat.ltb_ge.
      lia.
    }
    rewrite plus_zero.
    unfold zero.
    match goal with
    | [ |- context[?A + ?B + ?C - ?D] ] =>
      replace (A + B + C - D) with C by lia
    end.
    match goal with
    | [ H : context[_ <> ?KS _ -> ?F _ _ _ = _] |- context[?F ?K ?V _] ] =>
      let H' := fresh "H" in
      assert (H' : V = KS K \/ V <> KS K) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : forall _, _ _ (plus _ _ _) _ = _,
           H' : forall _, _ = _ |- _ ] =>
         unfold plus in H at 1;
         simpl in *; rewrite H; rewrite H'
       end.
       match goal with
       | [ |- context[subst'_size ?F (subst'_size ?F2 ?Q)] ] =>
         replace (subst'_size F (subst'_size F2 Q))
           with
             (subst_ext' F (subst_ext' F2 Q)) by auto
       end.
       rewrite subst_ext'_assoc.
       simpl.
       match goal with
       | [ |- subst'_size ?F _ = subst'_size ?F2 _ ] =>
         replace F2 with F; auto
       end.
       apply under_ks_weaks_comp.
    -- simpl.
       unfold get_var'.
       unfold under_ks'.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with false
       end.
       2:{
         apply eq_sym; rewrite Nat.ltb_ge.
         unfold shift_down_after.
         match goal with
         | [ |- context[if ?B then _ else _] ] =>
           remember B as b; generalize (eq_sym Heqb);
           case b; intros;
           [ rewrite Nat.ltb_lt in * | rewrite Nat.ltb_ge in * ];
           try lia
         end.
       }
       rewrite plus_zero.
       simpl.
       unfold get_var'.
       match goal with
       | [ H : context[_ <> _ _ -> ?F _ _ _ = _]
           |- context[?F _ _ _] ] =>
         rewrite H
       end.
       2:{ unfold plus; simpl; lia. }
       simpl.
       unfold weaks'.
       unfold var.
       simpl.
       unfold zero.
       match goal with
       | [ |- SizeVar ?A = SizeVar ?B ] =>
         replace B with A; auto
       end.
       unfold shift_down_after.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
         remember B as b; generalize (eq_sym Heqb);
         case b; intros;
         [ rewrite Nat.ltb_lt in * | rewrite Nat.ltb_ge in * ]
       end.
       --- unfold plus; simpl.
           match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with true; [ | apply eq_sym; rewrite Nat.ltb_lt; lia ]
           end.
           lia.
       --- unfold plus; simpl.
           match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
           end.
           lia.
  - match goal with
    | [ X : Ind |- _ ] => destruct X; solve_impossibles; simpl
    end.
    all:
      match goal with
      | [ H : context[_ <> SSize -> ?F _ _ _ = _]
          |- context[?F _ _ _] ] =>
        rewrite H; auto
      end.
    all: simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
      end.
    all: unfold zero.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
      end.
    all: simpl.
    all: unfold get_var'.
    all: unfold weaks'.
    all: unfold var.
    all: simpl.
    all:
      match goal with
      | [ H : context[_ <> SSize -> ?F _ _ _ = _]
          |- context[?F _ _ _] ] =>
        rewrite H; auto
      end.
Qed.

Lemma collect_tctx_subst_size : forall {kvs f sz},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
    collect_tctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)
    =
    map
      (fun '(sz0, q, hc) => (subst'_size f sz0, q, hc))
      (collect_tctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall f sz,
            debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
            collect_tctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)
            =
            map
              (fun '(sz0, q, hc) => (subst'_size f sz0, q, hc))
              (collect_tctx kvs))).
  all: intros; simpl in *; auto.

  erewrite <-subst'_kindvars_snoc; eauto.
  2:{ apply pure_under_kindvars. }
  repeat rewrite collect_tctx_snoc.
  erewrite H; eauto.
  2:{ apply pure_under_kindvars. }
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl
  end.
  - apply map_ext.
    intros.
    destruct_prs.
    match goal with
    | [ |- (?A, _, _) = (?B, _, _) ] =>
      replace B with A; auto
    end.
    match goal with
    | [ |- subst'_size ?F _ = subst'_size ?F2 _ ] =>
      replace F2 with F; auto
    end.
    eapply debruijn_subst_ext_inj; eauto.
    eapply debruijn_subst_ext_only_size_matters.
    -- apply pure_under_kindvars.
    -- rewrite ks_of_kvs_app; simpl.
       unfold plus; simpl; auto.
  - repeat rewrite map_map.
    apply map_ext.
    intros.
    destruct_prs.
    match goal with
    | [ |- (?A, _, _) = (?B, _, _) ] =>
      replace B with A; auto
    end.
    match goal with
    | [ |- subst'_size ?F _ = subst'_size ?F2 _ ] =>
      replace F2 with F; auto
    end.
    eapply debruijn_subst_ext_inj; eauto.
    eapply debruijn_subst_ext_only_size_matters.
    -- apply pure_under_kindvars.
    -- rewrite ks_of_kvs_app; simpl.
       unfold plus; simpl; auto.
  - repeat rewrite map_map.
    apply map_ext.
    intros.
    destruct_prs.
    match goal with
    | [ |- (?A, _, _) = (?B, _, _) ] =>
      replace B with A; auto
    end.
    repeat match goal with
           | [ |- context[subst'_size ?F (subst'_size ?F2 ?Q)] ] =>
             replace (subst'_size F (subst'_size F2 Q))
               with
                 (subst_ext' F (subst_ext' F2 Q)) by auto
           end.
    repeat rewrite subst_ext'_assoc.
    erewrite subst_ext'_comm_size; eauto.
    -- match goal with
       | [ H : context[ks_of_kvs (_ ++ _)] |- _ ] =>
         rewrite ks_of_kvs_app in H; simpl in H
       end.
       eauto.
    -- apply pure_under_kindvars.
  - match goal with
    | [ |- (subst'_size ?F _, _, _) :: _ =
           (subst'_size ?F2 _, _, _) :: _ ] =>
      replace F with F2; auto
    end.
    2:{
      eapply debruijn_subst_ext_inj; eauto.
      eapply debruijn_subst_ext_only_size_matters.
      - apply pure_under_kindvars.
      - rewrite ks_of_kvs_app; simpl.
        unfold plus; simpl; auto.
    }
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
Qed.

Lemma subst_weaks_weak_size : forall {sz f ks sz'},
  debruijn_subst_ext_conds f ks SSize sz' ->
  subst'_size (weaks' ks) sz =
  subst'_size
    f
    (subst'_size
       (weaks' ks)
       (subst'_size (subst'_of (weak SSize)) sz)).
Proof.
  induction sz; intros; simpl in *; auto.

  - unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    unfold zero.
    match goal with
    | [ H : context[_ <> _ _ -> _] |- _ ] =>
      rewrite H by lia
    end.
    simpl.
    unfold shift_down_after.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false; [ | apply eq_sym; rewrite Nat.ltb_ge; lia ]
    end.
    match goal with
    | [ |- SizeVar ?A = SizeVar ?B ] => replace B with A; auto
    end.
    lia.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma type_subst_size : forall {F f sz szs0 szs1 kvs},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
    type
      (add_constraints
         F
         (subst'_kindvars (subst'_of (ext SSize sz id)) kvs))
    =
    map
      (fun '(sz, q, hc) =>
         (subst'_size f sz, q, hc))
      (type
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SSize))
               (update_size_ctx ((szs0, szs1) :: size F) F))
            kvs)).
Proof.
  intros.
  repeat rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite map_app.
  repeat rewrite map_map.
  erewrite collect_tctx_subst_size; eauto.
  match goal with
  | [ |- _ ++ ?A = _ ++ ?B ] => replace B with A; auto
  end.
  destruct F; subst; simpl in *.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite ks_of_kvs_subst_kindvars.
  match goal with
  | [ |- context[subst'_qual _ (subst'_qual ?F ?Q)] ] =>
    replace (subst'_qual F Q) with Q; auto
  end.
  2:{
    erewrite weak_non_qual_no_effect_on_qual; eauto.
    2:{ apply single_weak_debruijn_weak_conds. }
    solve_ineqs.
  }
  match goal with
  | [ |- (?A, _, _) = (?B, _, _) ] => replace B with A; auto
  end.
  erewrite subst_weaks_weak_size; eauto.
Qed.

Lemma nth_error_type_subst_size : forall {F idx kvs f sz sz' szs0 szs1 qa hc},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
    nth_error
      (type
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SSize))
               (update_size_ctx ((szs0, szs1) :: size F) F))
            kvs))
      idx
    = Some (sz', qa, hc) ->
    nth_error
      (type
         (add_constraints
            F
            (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)))
      idx
    = Some (subst'_size f sz', qa, hc).
Proof.
  intros.
  erewrite type_subst_size; eauto.
  erewrite map_nth_error; eauto.
  simpl; auto.
Qed.

Lemma QualValid_subst : forall {F f q q' qs0 qs1 kvs},
    QualValid
      (qual
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SQual))
               (update_qual_ctx
                  ((qs0, qs1) :: qual F) F))
            kvs))
      q ->
    QualValid (qual F) q' ->
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q' ->
    QualValid
      (qual
         (add_constraints
            F
            (subst'_kindvars
               (subst'_of (ext SQual q' id))
               kvs)))
      (subst'_qual f q).
Proof.
  intros.
  destruct q; simpl.
  2:{ econstructor; eauto. }
  unfold get_var'.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  match goal with
  | [ H : context[_ <> ?F SQual -> _]
      |- context[_ SQual ?V zero] ] =>
    let H' := fresh "H" in
    assert (H' : V = F SQual \/ V <> F SQual) by apply eq_dec_nat;
    case H'; intros; subst; [ | rewrite H; auto ]
  end.
  - match goal with
    | [ H : context[?F _ = _] |- context[?F _] ] => rewrite H
    end.
    simpl.
    rewrite plus_zero.
    destruct q'; simpl.
    2:{ econstructor; eauto. }
    unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    unfold zero; rewrite Nat.add_0_r.
    rewrite add_constraints_to_ks_of_kvs; simpl.
    match goal with
    | [ |- QualValid ?L (QualVar ?V) ] =>
      let H := fresh "H" in
      assert (H : exists y, nth_error L V = Some y)
    end.
    { apply nth_error_some_exists.
      rewrite app_length.
      rewrite length_collect_qctx.
      rewrite ks_of_kvs_subst_kindvars.
      rewrite map_length.
      match goal with
      | [ H : QualValid _ (QualVar _) |- _ ] =>
        inv H;
        match goal with
        | [ H' : QualVar _ = _ |- _ ] => inv H'
        end
      end.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_Some_length in H
      end.
      lia. }
    destructAll.
    econstructor 2; eauto.
  - simpl.
    rewrite add_constraints_to_ks_of_kvs; simpl.
    match goal with
    | [ |- QualValid ?L (QualVar ?V) ] =>
      let H := fresh "H" in
      assert (H : exists y, nth_error L V = Some y)
    end.
    { apply nth_error_some_exists.
      rewrite app_length.
      rewrite length_collect_qctx.
      rewrite ks_of_kvs_subst_kindvars.
      rewrite map_length.
      unfold zero.
      match goal with
      | [ H : QualValid _ (QualVar _) |- _ ] =>
        inv H;
        match goal with
        | [ H' : QualVar _ = _ |- _ ] => inv H'
        end
      end.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_Some_length in H
      end.
      unfold shift_down_after.
      match goal with
      | [ |- (if ?B then _ else _) < _ ] =>
        remember B as b; generalize (eq_sym Heqb);
        case b; intros
      end.
      - rewrite Nat.ltb_lt in *.
        lia.
      - rewrite Nat.ltb_ge in *.
        rewrite add_constraints_to_ks_of_kvs in *.
        simpl in *.
        rewrite app_length in *.
        rewrite length_collect_qctx in *.
        repeat rewrite map_length in *.
        destruct F; subst; simpl in *.
        lia. }
    destructAll.
    econstructor 2; eauto.
Qed.

Lemma QualValid_ks_of_kvs : forall {F kvs kvs' q},
    QualValid (qual (add_constraints F kvs)) q ->
    ks_of_kvs kvs = ks_of_kvs kvs' ->
    QualValid (qual (add_constraints F kvs')) q.
Proof.
  intros.
  destruct q; simpl in *; auto.
  2:{ econstructor; eauto. }
  match goal with
  | [ H : QualValid _ (QualVar _) |- _ ] =>
    inv H;
    match goal with
    | [ H' : QualVar _ = _ |- _ ] => inv H'
    end
  end.
  match goal with
  | [ H : nth_error _ _ = Some _ |- _ ] =>
    apply nth_error_Some_length in H
  end.
  match goal with
  | [ |- QualValid ?L (QualVar ?V) ] =>
    let H := fresh "H" in
    assert (H : exists y, nth_error L V = Some y)
  end.
  { apply nth_error_some_exists.
    rewrite add_constraints_to_ks_of_kvs in *.
    simpl in *.
    rewrite app_length in *.
    rewrite length_collect_qctx in *.
    rewrite map_length in *.
    match goal with
    | [ H : ks_of_kvs _ = _ |- _ ] => rewrite <-H; auto
    end. }
  destructAll.
  econstructor 2; eauto.
Qed.

Lemma SizeValid_ks_of_kvs : forall {sz F kvs kvs'},
    SizeValid (size (add_constraints F kvs)) sz ->
    ks_of_kvs kvs = ks_of_kvs kvs' ->
    SizeValid (size (add_constraints F kvs')) sz.
Proof.
  induction sz; intros; simpl in *.
  - match goal with
    | [ |- SizeValid ?L (SizeVar ?V) ] =>
      let H := fresh "H" in
      assert (H : exists y, nth_error L V = Some y)
    end.
    { apply nth_error_some_exists.
      match goal with
      | [ H : SizeValid _ ?X |- _ ] =>
        inv H;
        match goal with
        | [ H' : X = _ |- _ ] => inv H'
        end
      end.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_Some_length in H
      end.
      rewrite add_constraints_to_ks_of_kvs in *.
      simpl in *.
      rewrite app_length in *.
      rewrite length_collect_szctx in *.
      rewrite map_length in *.
      match goal with
      | [ H : ks_of_kvs _ = _ |- _ ] => rewrite <-H; auto
      end. }
    destructAll.
    econstructor 3; eauto.
  - econstructor 2; eauto.
    all:
      match goal with
      | [ H : SizeValid _ ?X |- _ ] =>
        inv H;
        match goal with
        | [ H' : X = _ |- _ ] => inv H'; eauto
        end
      end.
  - econstructor; eauto.
Qed.

Lemma KindVarsValid_ks_of_kvs : forall {kvs'' F kvs kvs'},
    KindVarsValid (add_constraints F kvs) kvs'' ->
    ks_of_kvs kvs = ks_of_kvs kvs' ->
    KindVarsValid (add_constraints F kvs') kvs''.
Proof.
  induction kvs''; intros; simpl in *; constructor.
  all:
    match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
  - match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl in *; auto
    end.
    all: destructAll.
    all: split.
    all: try prepare_Forall.
    all: try eapply QualValid_ks_of_kvs; eauto.
    all: eapply SizeValid_ks_of_kvs; eauto.
  - rewrite <-add_constraints_snoc.
    match goal with
    | [ H : context[add_constraint (add_constraints _ _)] |- _ ] =>
      rewrite <-add_constraints_snoc in H
    end.
    eapply IHkvs''; eauto.
    repeat rewrite ks_of_kvs_app.
    match goal with
    | [ H : ?A = ?B |- context[?A] ] => rewrite H; auto
    end.
Qed.

Lemma KindVarsValid_subst_qual : forall {kvs' F f kvs kvs'' q' qs0 qs1},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q' ->
    QualValid (qual F) q' ->
    KindVarsValid
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SQual))
            (update_qual_ctx ((qs0, qs1) :: qual F) F)) kvs)
      kvs' ->
    ks_of_kvs kvs = ks_of_kvs kvs'' ->
    KindVarsValid
      (add_constraints
         F
         (subst'_kindvars (subst'_of (ext SQual q' id)) kvs''))
      (subst'_kindvars f kvs').
Proof.
  induction kvs'; intros; simpl in *; constructor.
  - match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl; auto
    end.
    -- unfold subst'_quals.
       split.
       all: prepare_Forall_with_map.
       all: eapply QualValid_ks_of_kvs.
       all: try eapply QualValid_subst; eauto.
       all: repeat rewrite ks_of_kvs_subst_kindvars; auto.
    -- unfold subst'_sizes.
       split.
       all: prepare_Forall_with_map.
       all: erewrite size_fctx_subst_qual; eauto.
       all: erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       all: eapply SizeValid_ks_of_kvs; eauto.
    -- match goal with
       | [ H : KindVarValid _ _ |- _ ] => inv H
       end.
       split.
       --- erewrite size_fctx_subst_qual; eauto.
           erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
           eapply SizeValid_ks_of_kvs; eauto.
       --- eapply QualValid_ks_of_kvs.
           all: try eapply QualValid_subst; eauto.
           repeat rewrite ks_of_kvs_subst_kindvars; auto.
  - rewrite <-add_constraints_snoc.
    erewrite subst'_kindvars_snoc; eauto.
    eapply IHkvs'.
    -- match goal with
       | [ H : debruijn_subst_ext_conds _ (ks_of_kvs ?KVS) _ _
           |- _ (under_kindvar' ?KV _) (ks_of_kvs ?X) _ _ ] =>
         replace (ks_of_kvs X) with (ks_of_kvs (KV :: KVS)) by auto
       end.
       simpl.
       apply debruijn_subst_ext_under_knd; auto.
    -- auto.
    -- match goal with
       | [ H : KindVarsValid _ (_ :: _) |- _ ] => inv H
       end.
       match goal with
       | [ H : context[add_constraint (add_constraints _ _)] |- _ ] =>
         rewrite <-add_constraints_snoc in H
       end.
       eapply KindVarsValid_ks_of_kvs; eauto.
       rewrite ks_of_kvs_app; simpl; auto.
    -- rewrite ks_of_kvs_app; simpl.
       match goal with
       | [ H : ?A = ?B |- context[?A] ] => rewrite H; auto
       end.
    -- match goal with
       | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
       end.
Qed.

Lemma fold_size_rel : forall {l1 l2 R},
    Forall2 R l1 l2 ->
    R None None ->
    (forall sz1, ~ R None (Some sz1) /\ ~ R (Some sz1) None) ->
    R (Some (SizeConst 0)) (Some (SizeConst 0)) ->
    (forall sz1 sz2 sz1' sz2',
        R (Some sz1) (Some sz1') ->
        R (Some sz2) (Some sz2') ->
        R (Some (SizePlus sz1 sz2)) (Some (SizePlus sz1' sz2'))) ->
    R (fold_size l1) (fold_size l2).
Proof.
  intros l1 l2 R H.
  induction H; intros; simpl in *; auto.
  match goal with
  | [ X : option Size, Y : option Size |- _ ] =>
    destruct X; destruct Y; auto
  end.
  2:{
    match goal with
    | [ H : R (Some ?A) None |- _ ] =>
      let H' := fresh "H" in
      assert (H' : ~ R (Some A) None); [ | exfalso; eauto ]
    end.
    eapply proj2; eauto.
  }
  2:{
    match goal with
    | [ H : R None (Some ?A) |- _ ] =>
      let H' := fresh "H" in
      assert (H' : ~ R None (Some A)); [ | exfalso; eauto ]
    end.
    eapply proj1; eauto.
  }
  specialize (IHForall2 H1 H2 H3 H4).
  match goal with
  | [ |- context[fold_size ?L] ] =>
    remember (fold_size L) as obj; generalize (eq_sym Heqobj);
    case obj; intros
  end.
  all:
    match goal with
    | [ |- context[fold_size ?L] ] =>
      remember (fold_size L) as obj2; generalize (eq_sym Heqobj2);
      case obj2; intros
    end.
  all: subst; auto.
  all:
    repeat match goal with
           | [ H : context[?A], H' : ?A = _ |- _ ] =>
             rewrite H' in H
           end.
  2:{
    match goal with
    | [ H : R (Some ?A) None |- _ ] =>
      let H' := fresh "H" in
      assert (H' : ~ R (Some A) None); [ | exfalso; eauto ]
    end.
    eapply proj2; eauto.
  }
  2:{
    match goal with
    | [ H : R None (Some ?A) |- _ ] =>
      let H' := fresh "H" in
      assert (H' : ~ R None (Some A)); [ | exfalso; eauto ]
    end.
    eapply proj1; eauto.
  }
  eauto.
Qed.

Lemma sizeOfPretype_subst_size : forall {pt f ks sz tctx ptsz},
    debruijn_subst_ext_conds f ks SSize sz ->
    sizeOfPretype tctx pt = Some ptsz ->
    sizeOfPretype
      (map
         (fun '(sz', q, hc) => (subst'_size f sz', q, hc))
         tctx)
      pt
    =
    Some (subst'_size f ptsz).
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall f ks sz tctx ptsz,
            debruijn_subst_ext_conds f ks SSize sz ->
            sizeOfPretype tctx pt = Some ptsz ->
            sizeOfPretype
              (map
                 (fun '(sz', q, hc) => (subst'_size f sz', q, hc))
                 tctx)
              pt
            =
            Some (subst'_size f ptsz))
       (fun pt =>
          forall f ks sz tctx ptsz,
            debruijn_subst_ext_conds f ks SSize sz ->
            sizeOfType tctx pt = Some ptsz ->
            sizeOfType
              (map
                 (fun '(sz', q, hc) => (subst'_size f sz', q, hc))
                 tctx)
              pt
            =
            Some (subst'_size f ptsz))
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; eauto.
  all:
    try now match goal with
            | [ H : Some _ = Some _ |- _ ] => inv H; auto
            end.

  - match goal with
    | [ X : NumType |- _ ] => destruct X
    end.
    all:
      match goal with
      | [ X : IntType |- _ ] => destruct X
      | [ X : FloatType |- _ ] => destruct X
      end.
    all:
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inv H
      end.
    all: simpl; auto.
  - match goal with
    | [ H : option_map _ ?X = Some _ |- _ ] =>
      remember X as obj; generalize (eq_sym Heqobj); revert H;
      case obj; intros; simpl in *;
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      | [ H : Some _ = Some _ |- _ ] => inv H
      end
    end.
    destruct_prs.
    erewrite map_nth_error; eauto.
    simpl; auto.
  - match goal with
    | [ |- _ = Some (subst'_size ?F ?SZ) ] =>
      replace (Some (subst'_size F SZ)) with
          (option_map (fun sz => subst'_size F sz) (Some SZ))
        by auto;
      match goal with
      | [ H : ?A = ?B |- context[?B] ] => rewrite <-H
      end;
      eapply (fold_size_rel (R:=(fun obj1 obj2 => obj2 = option_map (fun sz => subst'_size F sz) obj1))); eauto
    end.
    -- apply forall2_nth_error_inv; [ | repeat rewrite map_length; auto ].
       intros.
       match goal with
       | [ H : fold_size _ = Some _ |- _ ] =>
         apply fold_size_Some in H
       end.
       rewrite Forall_forall in *.
       match goal with
       | [ H : context[List.In _ ?L],
           H' : nth_error ?L _ = Some _ |- _ ] =>
         generalize H'; apply nth_error_In in H';
         specialize (H _ H')
       end.
       destructAll.
       intros.
       repeat match goal with
              | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
                apply nth_error_map_inv in H; destructAll
              end.
       simpl.
       match goal with
       | [ H : ?A = Some _, H' : ?B = Some _ |- _ ] =>
         rewrite H in H'; inv H'
       end.
       match goal with
       | [ H : Some _ = _ |- _ ] => apply eq_sym in H
       end.
       match goal with
       | [ H : forall _, _ -> forall _, _ |- _ ] => eapply H; eauto
       end.
       eapply nth_error_In; eauto.
    -- intros; simpl in *.
       let H := fresh "H" in split; intro H; inv H.
    -- intros.
       simpl in *.
       repeat match goal with
              | [ H : Some _ = Some _ |- _ ] => inv H; auto
              end.
  - match goal with
    | [ |- context[?A :: map ?F ?L] ] =>
      replace (A :: map F L) with (map F (A :: L)) by auto
    end.
    eauto.
Qed.

Lemma LocValid_subst_size : forall {f F kvs sz szs0 szs1 l},
    LocValid
      (location
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SSize))
               (update_size_ctx ((szs0, szs1) :: size F) F))
            kvs))
      l ->
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
    LocValid
      (location
         (add_constraints
            F
            (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)))
      (subst'_loc f l).
Proof.
  intros.
  erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
  match goal with
  | [ H : LocValid ?A _ |- LocValid ?B _ ] =>
    replace B with A; auto
  end.
  repeat rewrite add_constraints_to_ks_of_kvs; simpl.
  destruct F; subst; simpl in *.
  rewrite ks_of_kvs_subst_kindvars; auto.
Qed.

Lemma SizeValid_subst_weaks : forall {sz F kvs},
    SizeValid (size F) sz ->
    SizeValid
      (size (add_constraints F kvs))
      (subst'_size
         (weaks' (ks_of_kvs kvs))
         sz).
Proof.
  induction sz; intros; simpl in *; auto.
  - match goal with
    | [ H : SizeValid _ ?X |- _ ] =>
      inv H;
      match goal with
      | [ H' : X = _ |- _ ] => inv H'; eauto
      end
    end.
    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] =>
      apply nth_error_Some_length in H
    end.
    unfold get_var'.
    unfold weaks'.
    unfold debruijn.var.
    simpl.
    match goal with
    | [ |- SizeValid ?L (SizeVar ?V) ] =>
      let H := fresh "H" in
      assert (H : exists y, nth_error L V = Some y)
    end.
    { apply nth_error_some_exists.
      unfold zero.
      rewrite add_constraints_to_ks_of_kvs; simpl.
      rewrite app_length.
      rewrite length_collect_szctx.
      rewrite map_length.
      lia. }
    destructAll.
    econstructor 3; eauto.
  - match goal with
    | [ H : SizeValid _ ?X |- _ ] =>
      inv H;
      match goal with
      | [ H' : X = _ |- _ ] => inv H'; eauto
      end
    end.
    econstructor 2; eauto.
  - econstructor; eauto.
Qed.

Lemma SizeValid_subst : forall {sz' F szs0 szs1 kvs sz f},
   SizeValid
     (size
        (add_constraints
           (subst'_function_ctx
              (subst'_of (weak SSize))
              (update_size_ctx ((szs0, szs1) :: size F) F))
           kvs))
     sz' ->
   debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
   SizeValid (size F) sz ->
   SizeValid
     (size
        (add_constraints
           F
           (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)))
     (subst'_size f sz').
Proof.
  induction sz'; intros; simpl in *.
  - unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> ?F SSize -> _]
        |- context[_ SSize ?V zero] ] =>
      let H' := fresh "H" in
      assert (H' : V = F SSize \/ V <> F SSize) by apply eq_dec_nat;
      case H'; intros; subst; [ | rewrite H; auto ]
    end.
    -- match goal with
       | [ H : context[?F _ = _] |- context[?F _] ] => rewrite H
       end.
       simpl.
       rewrite plus_zero.
       match goal with
       | [ |- context[add_constraints _ ?KVS] ] =>
         match goal with
         | [ |- context[ks_of_kvs ?KVS2] ] =>
           replace (ks_of_kvs KVS2) with (ks_of_kvs KVS)
             by apply ks_of_kvs_subst_kindvars
         end
       end.
       apply SizeValid_subst_weaks; auto.
    -- simpl.
       match goal with
       | [ |- SizeValid ?L (SizeVar ?V) ] =>
         let H := fresh "H" in
         assert (H : exists y, nth_error L V = Some y)
       end.
       { apply nth_error_some_exists.
         unfold zero.
         match goal with
         | [ H : SizeValid _ ?X |- _ ] =>
           inv H;
           match goal with
           | [ H' : X = _ |- _ ] => inv H'; eauto
           end
         end.
         match goal with
         | [ H : nth_error _ _ = Some _ |- _ ] =>
           apply nth_error_Some_length in H
         end.
         rewrite add_constraints_to_ks_of_kvs in *.
         simpl in *.
         rewrite app_length in *.
         rewrite length_collect_szctx in *.
         rewrite ks_of_kvs_subst_kindvars.
         repeat rewrite map_length in *.
         destruct F; subst; simpl in *.
         unfold shift_down_after.
         match goal with
         | [ |- (if ?B then _ else _) < _ ] =>
           remember B as b; generalize (eq_sym Heqb);
           case b; intros; try lia
         end.
         rewrite Nat.ltb_lt in *.
         lia. }
       destructAll.
       econstructor 3; eauto.
  - match goal with
    | [ H : SizeValid _ ?X |- _ ] =>
      inv H;
      match goal with
      | [ H' : X = _ |- _ ] => inv H'; eauto
      end
    end.
    econstructor 2; eauto.
  - econstructor; eauto.
Qed.

Lemma KindVarsValid_subst_size : forall {kvs' F f kvs kvs'' sz' szs0 szs1},
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz' ->
    SizeValid (size F) sz' ->
    KindVarsValid
      (add_constraints
         (subst'_function_ctx
            (subst'_of (weak SSize))
            (update_size_ctx ((szs0, szs1) :: size F) F)) kvs)
      kvs' ->
    ks_of_kvs kvs = ks_of_kvs kvs'' ->
    KindVarsValid
      (add_constraints
         F
         (subst'_kindvars (subst'_of (ext SSize sz' id)) kvs''))
      (subst'_kindvars f kvs').
Proof.
  induction kvs'; intros; simpl in *; constructor.
  all:
    match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
  - match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl in *; auto
    end.
    -- unfold subst'_quals.
       split.
       all: prepare_Forall_with_map.
       all: erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       all: erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       all: eapply QualValid_ks_of_kvs; eauto.
    -- unfold subst'_sizes.
       split.
       all: prepare_Forall_with_map.
       all: eapply SizeValid_ks_of_kvs.
       all: try eapply SizeValid_subst; eauto.
       all: repeat rewrite ks_of_kvs_subst_kindvars; auto.
    -- destructAll.
       split.
       --- eapply SizeValid_ks_of_kvs.
           all: try eapply SizeValid_subst; eauto.
           repeat rewrite ks_of_kvs_subst_kindvars; auto.
       --- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
           eapply QualValid_ks_of_kvs; eauto.
  - rewrite <-add_constraints_snoc.
    erewrite subst'_kindvars_snoc; eauto.
    eapply IHkvs'.
    -- match goal with
       | [ H : debruijn_subst_ext_conds _ (ks_of_kvs ?KVS) _ _
           |- _ (under_kindvar' ?KV _) (ks_of_kvs ?X) _ _ ] =>
         replace (ks_of_kvs X) with (ks_of_kvs (KV :: KVS)) by auto
       end.
       simpl.
       apply debruijn_subst_ext_under_knd; auto.
    -- auto.
    -- match goal with
       | [ H : context[add_constraint (add_constraints _ _)] |- _ ] =>
         rewrite <-add_constraints_snoc in H
       end.
       eapply KindVarsValid_ks_of_kvs; eauto.
       rewrite ks_of_kvs_app; simpl; auto.
    -- rewrite ks_of_kvs_app; simpl.
       match goal with
       | [ H : ?A = ?B |- context[?A] ] => rewrite H; auto
       end.
    -- match goal with
       | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
       end.
Qed.

Lemma model_satisfies_context_QualLeq_quotient : forall {idx f qctx q model model' qctx' qs0' qs1'},
    (forall qc, f (QualConst qc) = QualConst qc) ->
    (forall v,
        v <> idx ->
        f (QualVar v) = QualVar (shift_down_after v idx 0)) ->
    f (QualVar idx) = q ->
    nth_error qctx idx = Some (qs0', qs1') ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           (f q')
           q
         = Some true)
      qs0' ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           q
           (f q')
         = Some true)
      qs1' ->
    qctx'
    =
    (remove_nth
       (map
          (fun '(qs0, qs1) =>
             (map f qs0, map f qs1))
          qctx)
       idx) ->
    model_satisfies_context
      le_qualconst interp_qual
      model qctx' ->
    model'
    =
    (fun v =>
       if Nat.eq_dec v idx
       then interp_qual model q
       else model (shift_down_after v idx 0)) ->
    model_satisfies_context
      le_qualconst interp_qual
      model' qctx /\
    interp_qual model' =
    (fun q => interp_qual model (f q)).
Proof.
  intros.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B)
  end.
  { apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with | [ X : Qual |- _ ] => destruct X end.
    all: simpl in *.
    - match goal with
      | [ |- context[if ?B then _ else _] ] =>
        remember B as obj; generalize (eq_sym Heqobj);
        case obj; intros; subst; auto
      end.
      match goal with
      | [ H : context[_ <> _ -> _] |- _ ] => rewrite H; auto
      end.
    - match goal with
      | [ H : forall _, _ = _ |- _ ] => rewrite H; auto
      end. }
  split; auto.
  rewrite model_satisfies_context_desc; intros.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    generalize H;
    rewrite model_satisfies_context_desc in H; intros
  end.
  subst.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    remember B as obj; generalize (eq_sym Heqobj);
    case obj; intros; subst; auto
  end.
  - match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inv H'
    end.
    split; prepare_Forall.
    all:
      match goal with
      | [ H : interp_qual _ = _ |- _ ] =>
        repeat rewrite H
      end.
    all:
      match goal with
      | [ H : QualLeq _ _ _ = Some _,
          H' : model_satisfies_context _ _ _ _ |- _ ] =>
        rewrite QualLeq_desc in H; unfold ctx_imp_leq in H;
        specialize (H _ H'); auto
      end.
  - match goal with
    | [ H : interp_qual _ = _ |- _ ] =>
      repeat rewrite H
    end.
    match goal with
    | [ H : _ <> _, H' : context[remove_nth ?L] |- _ ] =>
      specialize (nth_error_shift_down (l:=L) H)
    end.
    erewrite map_nth_error; eauto.
    simpl.
    intros.
    match goal with
    | [ H : forall _ _ _, nth_error ?L _ = Some _ -> _,
        H' : nth_error ?L _ = Some _ |- _ ] =>
      specialize (H _ _ _ H')
    end.
    destructAll.
    split; prepare_Forall.
    all: rewrite Forall_forall in *.
    all:
      match goal with
      | [ H : context[List.In _ (map ?F ?B)], H' : List.In ?A ?B |- _ ] =>
        let H'' := fresh "H" in
        assert (H'' : List.In (F A) (map F B)) by ltac:(apply in_map; auto);
        specialize (H _ H''); auto
      end.
Qed.

Lemma QualLeq_quotient : forall {f idx qctx qctx' qs0' qs1' q q1 q2},
    (forall qc, f (QualConst qc) = QualConst qc) ->
    (forall v,
        v <> idx ->
        f (QualVar v) = QualVar (shift_down_after v idx 0)) ->
    f (QualVar idx) = q ->
    qctx'
    =
    remove_nth
      (map
         (fun '(qs0, qs1) =>
            (map f qs0, map f qs1))
         qctx)
      idx ->
    QualLeq qctx q1 q2 = Some true ->
    nth_error qctx idx = Some (qs0', qs1') ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           (f q')
           q
         = Some true)
      qs0' ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           q
           (f q')
         = Some true)
      qs1' ->
    QualLeq
      qctx'
      (f q1)
      (f q2)
    =
    Some true.
Proof.
  intros.
  rewrite QualLeq_desc in *.
  eapply ctx_imp_leq_map; eauto.
  intros.
  eexists.
  eapply model_satisfies_context_QualLeq_quotient; eauto.
  match goal with
  | [ |- ?A = ?X ] => replace A with X; auto
  end.
Qed.

Lemma QualLeq_subst : forall {f ks qctx qctx' qs0' qs1' q q1 q2},
    debruijn_subst_ext_conds f ks SQual q ->
    qctx'
    =
    remove_nth
      (map
         (fun '(qs0, qs1) =>
            (subst'_quals f qs0, subst'_quals f qs1))
         qctx)
      (ks SQual) ->
    QualLeq qctx q1 q2 = Some true ->
    nth_error qctx (ks SQual) = Some (qs0', qs1') ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           (subst'_qual f q')
           (subst'_qual (weaks' ks) q)
         = Some true)
      qs0' ->
    Forall
      (fun q' =>
         QualLeq
           qctx'
           (subst'_qual (weaks' ks) q)
           (subst'_qual f q')
         = Some true)
      qs1' ->
    QualLeq
      qctx'
      (subst'_qual f q1)
      (subst'_qual f q2)
    =
    Some true.
Proof.
  intros.
  unfold subst'_quals in *.
  unfold debruijn_subst_ext_conds in *; destructAll.
  eapply QualLeq_quotient.
  1,4-8: eauto.
  - intros.
    simpl.
    unfold get_var'.
    match goal with
    | [ H : context[_ <> _ SQual -> _] |- _ ] => rewrite H; auto
    end.
  - simpl.
    unfold get_var'.
    match goal with
    | [ H : forall _, _ = _ |- _ ] => rewrite H
    end.
    simpl.
    rewrite plus_zero; auto.
Qed.

Lemma qual_subst_qual : forall {F f q qs0 qs1 kvs},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
  qual
    (add_constraints
       F
       (subst'_kindvars
          (subst'_of (ext SQual q id))
          kvs))
  =
  remove_nth
    (map
       (fun '(qs0, qs1) => (subst'_quals f qs0, subst'_quals f qs1))
       (qual
          (add_constraints
             (subst'_function_ctx
                (subst'_of (weak SQual))
                (update_qual_ctx
                   ((qs0, qs1) :: qual F) F))
             kvs)))
    (ks_of_kvs kvs SQual).
Proof.
  intros.
  repeat rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite map_app.
  repeat rewrite map_map.
  erewrite collect_qctx_subst_qual; eauto.
  destruct F; subst; simpl in *.
  erewrite remove_nth_prefix_appliable; eauto.
  2:{
    rewrite map_length.
    rewrite length_collect_qctx; auto.
  }
  match goal with
  | [ |- _ ++ ?X = _ ++ ?Y ] => replace Y with X; auto
  end.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite ks_of_kvs_subst_kindvars.
  erewrite subst_weaks_weak_quals; eauto.
  match goal with
  | [ |- (_, ?A) = (_, ?B) ] => replace B with A; auto
  end.
  eapply subst_weaks_weak_quals; eauto.
Qed.

Lemma QualLeq_weaks : forall {prf qctx ks model model'},
    length prf = ks SQual ->
    model_satisfies_context le_qualconst interp_qual model
    (prf ++
         map
         (fun '(qs2, qs3) =>
            (subst'_quals (weaks' ks) qs2,
             subst'_quals (weaks' ks) qs3))
         qctx) ->
    model' =
    (fun v => model (v + ks SQual)) ->
    model_satisfies_context le_qualconst interp_qual model' qctx /\
    interp_qual model' =
    (fun obj : Qual =>
       interp_qual model (subst'_qual (weaks' ks) obj)).
Proof.
  intros.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B)
  end.
  { apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with
    | [ X : Qual |- _ ] => destruct X; simpl in *; auto
    end.
    unfold zero.
    rewrite Nat.add_0_r.
    rewrite Nat.add_comm; auto. }
  split; auto.
  rewrite model_satisfies_context_desc in *.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    rewrite model_satisfies_context_desc in H
  end.
  intros.
  match goal with
  | [ H : interp_qual _ = _ |- _ ] => rewrite H
  end.
  subst.
  match goal with
  | [ KS : Ind -> nat,
      H : forall _ _ _, nth_error ?L _ = Some _ -> _,
      H' : nth_error _ ?IDX = Some (?L1, ?L2) |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : nth_error L (IDX + KS SQual)
                 =
                 Some
                   (subst'_quals (weaks' KS) L1,
                    subst'_quals (weaks' KS) L2));
    [ | specialize (H _ _ _ H0) ]
  end.
  { rewrite nth_error_app2 by lia.
    match goal with
    | [ H : ?A = _ |- context[?A] ] => rewrite H
    end.
    rewrite Nat.add_sub.
    erewrite map_nth_error; eauto.
    simpl; auto. }
  destructAll.
  split; prepare_Forall.
  all: rewrite Forall_forall in *.
  all: unfold subst'_quals in *.
  all:
    match goal with
    | [ H : context[List.In _ (map ?F ?B)], H' : List.In ?A ?B |- _ ] =>
      let H'' := fresh "H" in
      assert (H'' : List.In (F A) (map F B)) by ltac:(apply in_map; auto);
      specialize (H _ H''); auto
    end.
Qed.

Lemma QualLeq_subst' : forall {F f q0 q1 q' qs0 qs1 kvs},
    QualLeq
      (qual
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SQual))
               (update_qual_ctx
                  ((qs0, qs1) :: qual F) F))
            kvs))
      q0 q1
    =
    Some true ->
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q' ->
    QualValid (qual F) q' ->
    Forall (fun q'' => QualLeq (qual F) q'' q' = Some true) qs0 ->
    Forall (fun q'' => QualLeq (qual F) q' q'' = Some true) qs1 ->
    QualLeq
      (qual
         (add_constraints
            F
            (subst'_kindvars
               (subst'_of (ext SQual q' id))
               kvs)))
      (subst'_qual f q0)
      (subst'_qual f q1)
    =
    Some true.
Proof.
  intros.
  erewrite qual_subst_qual; eauto.
  eapply QualLeq_subst; [ eauto | eauto | eauto | | | ].
  1:{
    rewrite add_constraints_to_ks_of_kvs; simpl.
    rewrite map_map.
    destruct F; subst; simpl in *.
    erewrite nth_error_app_appliable; eauto.
    rewrite length_collect_qctx; auto.
  }
  all: unfold subst'_quals.
  all: rewrite map_map.
  all: prepare_Forall_with_map.
  all: rewrite add_constraints_to_ks_of_kvs; simpl.
  all: destruct F; subst; simpl in *.
  all: rewrite map_app; simpl.
  all: erewrite remove_nth_prefix_appliable; eauto.
  all: try now ltac:(repeat rewrite map_length; rewrite length_collect_qctx; auto).
  all: erewrite <-subst_weaks_weak_qual; eauto.
  all: repeat rewrite map_map.
  all:
    match goal with
    | [ |- context[ks_of_kvs ?KVS] ] =>
      match goal with
      | [ |- context[_ ++ map ?F _] ] =>
        replace F with
            (fun '(qs0, qs1) =>
               (subst'_quals (weaks' (ks_of_kvs KVS)) qs0,
                subst'_quals (weaks' (ks_of_kvs KVS)) qs1))
      end
    end.
  2,4: apply FunctionalExtensionality.functional_extensionality.
  2-3: intros.
  2-3: destruct_prs.
  2-3: erewrite subst_weaks_weak_quals; eauto.
  2-3:
    match goal with
    | [ |- (_, ?A) = (_, ?B) ] => replace B with A; auto
    end.
  2-3: erewrite subst_weaks_weak_quals; eauto.
  2-3: unfold subst'_quals; auto.
  
  all: rewrite QualLeq_desc in *.
  all: eapply ctx_imp_leq_map; eauto.
  all: intros.
  all: eexists.
  all: eapply QualLeq_weaks; eauto.
  all: try rewrite map_length.
  all: try apply length_collect_qctx.
  all:
    match goal with
    | [ |- ?A = ?B ] => replace A with B; auto
    end.
Qed.

Lemma size_update_qual_ctx : forall {F qctx},
    size (update_qual_ctx qctx F) = size F.
Proof.
  destruct F; simpl; auto.
Qed.

Lemma TypeValid_debruijn_subst_qual_provable :
  (forall F t,
      TypeValid F t ->
      forall f kvs qs0 qs1 q F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
        QualValid (qual F'') q ->
        Forall
          (fun q' => QualLeq (qual F'') q' q = Some true) qs0 ->
        Forall
          (fun q' => QualLeq (qual F'') q q' = Some true) qs1 ->
        F = add_constraints F'' (QUAL qs0 qs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SQual q id)) kvs) ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f kvs qs0 qs1 q F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
        QualValid (qual F'') q ->
        Forall
          (fun q' => QualLeq (qual F'') q' q = Some true) qs0 ->
        Forall
          (fun q' => QualLeq (qual F'') q q' = Some true) qs1 ->
        F = add_constraints F'' (QUAL qs0 qs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SQual q id)) kvs) ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f kvs qs0 qs1 q F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
        QualValid (qual F'') q ->
        Forall
          (fun q' => QualLeq (qual F'') q' q = Some true) qs0 ->
        Forall
          (fun q' => QualLeq (qual F'') q q' = Some true) qs1 ->
        F = add_constraints F'' (QUAL qs0 qs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SQual q id)) kvs) ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f kvs qs0 qs1 q F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SQual q ->
        QualValid (qual F'') q ->
        Forall
          (fun q' => QualLeq (qual F'') q' q = Some true) qs0 ->
        Forall
          (fun q' => QualLeq (qual F'') q q' = Some true) qs1 ->
        F = add_constraints F'' (QUAL qs0 qs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SQual q id)) kvs) ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst.

  - econstructor; eauto.
    eapply QualValid_subst; eauto.
  - unfold get_var'.
    match goal with
    | [ |- context[?F SPretype ?V zero] ] =>
      replace (F SPretype V zero) with (TVar V)
    end.
    2:{
      unfold debruijn_subst_ext_conds in *.
      destructAll.
      match goal with
      | [ H : context[_ <> SQual -> _] |- _ ] =>
        rewrite H; solve_ineqs
      end.
      simpl; auto.
    }
    econstructor.
    4: eapply QualLeq_subst'; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply nth_error_type_subst_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply QualValid_subst; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualValid_subst; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst'; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst'; eauto.
    -- eapply RecVarUnderRefPretype_subst_non_pretype; auto.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- simpl.
       erewrite sizeOfPretype_subst_no_effect;
         [ | eapply debruijn_subst_ext_under_knd | ];
         eauto; solve_ineqs.
       erewrite sizeOfPretype_eifc; eauto.
       constructor.
       apply eifc_subst_qual.
    -- match goal with
       | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
           replace F2 with F; auto
       end.
       repeat rewrite add_constraints_to_ks_of_kvs; simpl.
       rewrite collect_szctx_subst_qual.
       match goal with
       | [ |- ?A ++ ?B = _ ++ ?C ] =>
           replace C with B; eauto
       end.
       rewrite ks_of_kvs_subst_kindvars.
       match goal with
       | [ |- map _ ?L = map _ ?L2 ] =>
           replace L with L2; auto
       end.
       apply eq_sym.
       rewrite <-map_id.
       rewrite size_update_qual_ctx.
       apply map_ext.
       intros.
       destruct_prs.
       unfold subst'_sizes.
       match goal with
       | [ |- context[map ?F] ] =>
           replace (map F) with (fun (s : list Size) => s); auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply eq_sym.
       rewrite <-map_id.
       apply map_ext.
       intros.
       apply qual_weak_no_effect_on_size.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           match goal with
           | [ |- context[(?SZ, ?Q, ?HC)] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- TYPE ?SZ (subst'_qual ?F ?Q) ?HC = _ ] =>
           replace (TYPE SZ (subst'_qual F Q) HC)
             with
               (subst'_kindvar F (TYPE SZ Q HC)); eauto
         end.
         simpl.
         erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    eapply QualValid_subst; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       simpl in *.
       eapply QualLeq_subst'; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       match goal with
       | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
       end.
       repeat match goal with
              | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
                rewrite Forall_forall in H; specialize (H _ H')
              end.
       simpl in *.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - econstructor; eauto.
    eapply QualValid_subst; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply LocValid_subst_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply LocValid_subst_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- eapply LocValid_subst_qual; eauto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst'; eauto.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           replace F with (add_constraints FP (KVS ++ [LOC]))
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- _ = subst'_kindvar ?F ?X ] =>
           replace (subst'_kindvar F X) with (subst'_kindvar F LOC) by auto
         end.
         simpl; auto.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    -- eapply QualValid_subst; eauto.
    -- match goal with
       | [ |- QualLeq _ (QualConst Linear) (subst'_qual ?F _) = _ ] =>
         replace (QualConst Linear) with (subst'_qual F Linear) by auto
       end.
       eapply QualLeq_subst'; eauto.
    -- eapply LocValid_subst_qual; eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    match goal with
    | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
    end.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    simpl in *.
    eauto.
  - econstructor; eauto.
    prepare_Forall.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
    end.
    destructAll.
    destruct_prs.
    match goal with
    | [ X : Typ |- _ ] => destruct X
    end.
    simpl in *.
    repeat match goal with
           | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
             rewrite Forall_forall in H; specialize (H _ H')
           end.
    destructAll.
    simpl in *.
    eexists.
    split.
    { erewrite sizeOfPretype_subst_no_effect; eauto; solve_ineqs.
      erewrite sizeOfPretype_eifc; eauto.
      apply eifc_subst_qual. }
    erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    split.
    { erewrite size_fctx_subst_qual; eauto. }
    split.
    {
      match goal with
      | [ H : SizeValid ?F ?SZ |- SizeValid ?F2 ?SZ ] =>
          replace F2 with F; auto
      end.
      repeat rewrite add_constraints_to_ks_of_kvs; simpl.
      rewrite collect_szctx_subst_qual.
      match goal with
      | [ |- ?A ++ ?B = _ ++ ?C ] =>
          replace C with B; eauto
      end.
      rewrite ks_of_kvs_subst_kindvars.
      match goal with
      | [ |- map _ ?L = map _ ?L2 ] =>
          replace L with L2; auto
      end.
      apply eq_sym.
      rewrite <-map_id.
      rewrite size_update_qual_ctx.
      apply map_ext.
      intros.
      destruct_prs.
      unfold subst'_sizes.
      match goal with
      | [ |- context[map ?F] ] =>
          replace (map F) with (fun (s : list Size) => s); auto
      end.
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      apply eq_sym.
      rewrite <-map_id.
      apply map_ext.
      intros.
      apply qual_weak_no_effect_on_size.
    }
    split; eauto.
    erewrite size_fctx_subst_qual; eauto.
  - econstructor; eauto.
    match goal with
    | [ |- QualLeq _ (subst'_qual ?F _) _ = _ ] =>
      replace (QualConst Unrestricted) with (subst'_qual F Unrestricted) by auto
    end.
    eapply QualLeq_subst'; eauto.
  - econstructor; eauto.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite size_fctx_subst_qual; eauto.
    -- eapply QualValid_subst; eauto.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[(?SZ, ?Q, ?HC)] ] =>
           match goal with
           | [ |- context[add_constraints ?FP ?KVS] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- TYPE (subst'_size ?F ?SZ)
                     (subst'_qual _ ?Q)
                     ?HC = _ ] =>
           replace
             (TYPE
                (subst'_size F SZ) (subst'_qual F Q) HC)
             with
               (subst'_kindvar F (TYPE SZ Q HC)) by auto
         end.
         eauto.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    all: prepare_Forall.
    all:
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] => apply in_map_inv in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ X : Typ |- _ ] => destruct X
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
      end.
    all:
      repeat match goal with
             | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
               rewrite Forall_forall in H; specialize (H _ H')
             end.
    all: eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_subst_qual; eauto.
    -- match goal with
       | [ |- context[add_constraints (add_constraints ?F ?KVS1) ?KVS2] ] =>
         replace
           (add_constraints (add_constraints F KVS1) KVS2)
           with
             (add_constraints F (KVS1 ++ KVS2))
       end.
       2:{ rewrite add_constraints_app; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       2:{ rewrite add_constraints_app; auto. }
       --- rewrite ks_of_kvs_app.
           apply debruijn_subst_ext_under_kindvars; auto.
       --- erewrite subst'_kindvars_app; eauto.
Qed.

Lemma subst_sizes_comm : forall {szs obj f f' ks},
    debruijn_subst_ext_conds f (plus (sing SSize 1) ks) SSize obj ->
    debruijn_subst_ext_conds f' ks SSize obj ->
    subst'_sizes (subst'_of (weak SSize)) (subst'_sizes f' szs) =
    subst'_sizes f (subst'_sizes (subst'_of (weak SSize)) szs).
Proof.
  induction szs; simpl; auto.
  intros.
  repeat match goal with
         | [ |- context[subst'_size ?F (subst'_size ?F2 ?SZ)] ] =>
           replace (subst'_size F (subst'_size F2 SZ))
             with
               (subst_ext' F (subst_ext' F2 SZ)) by auto
         end.
  repeat rewrite subst_ext'_assoc.
  erewrite subst_ext'_comm_size; eauto.
  erewrite IHszs; eauto.
Qed.

Lemma collect_szctx_subst_size : forall {kvs sz f},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
  collect_szctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)
  =
  map (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1)) (collect_szctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs =>
          forall sz f,
            debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
            collect_szctx (subst'_kindvars (subst'_of (ext SSize sz id)) kvs)
            =
            map (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1)) (collect_szctx kvs))).
  all: intros; simpl in *.

  - unfold collect_szctx; simpl; auto.
  - erewrite <-subst'_kindvars_snoc; eauto.
    2:{ apply pure_under_kindvars. }
    repeat rewrite collect_szctx_snoc.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H
    end.
    2:{ apply pure_under_kindvars. }
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl; auto
    end.
    3:{
      match goal with
      | [ H : context[ks_of_kvs (_ ++ _)] |- _ ] =>
        rewrite ks_of_kvs_app in H; simpl in H
      end.
      erewrite subst_sizes_comm; eauto.
      2:{ apply pure_under_kindvars. }
      erewrite subst_sizes_comm; eauto.
      2:{ apply pure_under_kindvars. }
      match goal with
      | [ |- _ :: ?A = _ :: ?B ] => replace B with A; auto
      end.
      repeat rewrite map_map.
      apply map_ext.
      intros.
      destruct_prs.
      erewrite subst_sizes_comm; eauto.
      2:{ apply pure_under_kindvars. }
      erewrite subst_sizes_comm; eauto.
      apply pure_under_kindvars.
    }
    all: apply map_ext.
    all: intros.
    all: destruct_prs.
    all:
      match goal with
      | [ |- (subst'_sizes ?F _, _) = (subst'_sizes ?F2 _, _) ] =>
        replace F2 with F; auto
      end.
    all: erewrite debruijn_subst_ext_inj; eauto.
    all: eapply debruijn_subst_ext_only_size_matters.
    all: try apply pure_under_kindvars.
    all: rewrite ks_of_kvs_app; simpl.
    all: unfold plus; simpl; auto.
Qed.

Lemma subst_weaks_weak_sizes : forall {szs f ks sz'},
  debruijn_subst_ext_conds f ks SSize sz' ->
  subst'_sizes (weaks' ks) szs =
  subst'_sizes
    f
    (subst'_sizes
       (weaks' ks)
       (subst'_sizes (subst'_of (weak SSize)) szs)).
Proof.
  induction szs; intros; simpl in *; auto.
  erewrite subst_weaks_weak_size; eauto.
  erewrite IHszs; eauto.
Qed.

Lemma size_subst_size : forall {F f sz szs0 szs1 kvs},
  debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
  size
    (add_constraints
       F
       (subst'_kindvars
          (subst'_of (ext SSize sz id))
          kvs))
  =
  remove_nth
    (map
       (fun '(szs0, szs1) => (subst'_sizes f szs0, subst'_sizes f szs1))
       (size
          (add_constraints
             (subst'_function_ctx
                (subst'_of (weak SSize))
                (update_size_ctx
                   ((szs0, szs1) :: size F) F))
             kvs)))
    (ks_of_kvs kvs SSize).
Proof.
  intros.
  repeat rewrite add_constraints_to_ks_of_kvs.
  simpl.
  rewrite map_app.
  repeat rewrite map_map.
  erewrite collect_szctx_subst_size; eauto.
  destruct F; subst; simpl in *.
  erewrite remove_nth_prefix_appliable; eauto.
  2:{
    rewrite map_length.
    rewrite length_collect_szctx; auto.
  }
  match goal with
  | [ |- _ ++ ?X = _ ++ ?Y ] => replace Y with X; auto
  end.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite ks_of_kvs_subst_kindvars.
  erewrite subst_weaks_weak_sizes; eauto.
  match goal with
  | [ |- (_, ?A) = (_, ?B) ] => replace B with A; auto
  end.
  eapply subst_weaks_weak_sizes; eauto.
Qed.

Lemma model_satisfies_context_SizeLeq_quotient : forall {idx f szctx sz model model' szctx' szs0' szs1'},
    (forall szc, f (SizeConst szc) = SizeConst szc) ->
    (forall v,
        v <> idx ->
        f (SizeVar v) = SizeVar (shift_down_after v idx 0)) ->
    f (SizeVar idx) = sz ->
    (forall sz1 sz2, f (SizePlus sz1 sz2) = SizePlus (f sz1) (f sz2)) ->
    nth_error szctx idx = Some (szs0', szs1') ->
    Forall
      (fun sz' =>
         SizeLeq
           szctx'
           (f sz')
           sz
         = Some true)
      szs0' ->
    Forall
      (fun sz' =>
         SizeLeq
           szctx'
           sz
           (f sz')
         = Some true)
      szs1' ->
    szctx'
    =
    (remove_nth
       (map
          (fun '(szs0, szs1) =>
             (map f szs0, map f szs1))
          szctx)
       idx) ->
    model_satisfies_context
      Peano.le interp_size
      model szctx' ->
    model'
    =
    (fun v =>
       if Nat.eq_dec v idx
       then interp_size model sz
       else model (shift_down_after v idx 0)) ->
    model_satisfies_context
      Peano.le interp_size
      model' szctx /\
    interp_size model' =
    (fun sz => interp_size model (f sz)).
Proof.
  intros.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B)
  end.
  { apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with
    | [ H : context[model_satisfies_context] |- _ ] => clear H
    end.
    repeat match goal with
           | [ H : context[SizeLeq] |- _ ] => clear H
           end.
    match goal with
    | [ F : Size -> Size |- _ ] =>
      repeat match goal with
             | [ H : context[F] |- _ ] => revert H
             end
    end.
    clear.
    match goal with
    | [ X : Size |- _ ] => induction X
    end.
    all: intros; simpl in *; auto.
    - match goal with
      | [ |- context[if ?B then _ else _] ] =>
        remember B as obj; generalize (eq_sym Heqobj);
        case obj; intros; subst; auto
      end.
      match goal with
      | [ H : context[_ <> _ -> _] |- _ ] => rewrite H; auto
      end.
    - match goal with
      | [ H : forall _ _, _ (SizePlus _ _) = _ |- _ ] =>
        rewrite H; auto
      end.
      simpl; auto.
    - match goal with
      | [ H : forall _, _ = _ |- _ ] => rewrite H; auto
      end. }
  split; auto.
  rewrite model_satisfies_context_desc; intros.
  match goal with
  | [ H : model_satisfies_context _ _ _ _ |- _ ] =>
    generalize H;
    rewrite model_satisfies_context_desc in H; intros
  end.
  subst.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    remember B as obj; generalize (eq_sym Heqobj);
    case obj; intros; subst; auto
  end.
  - match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inv H'
    end.
    split; prepare_Forall.
    all:
      match goal with
      | [ H : interp_size _ = _ |- _ ] =>
        repeat rewrite H
      end.
    all:
      match goal with
      | [ H : SizeLeq _ _ _ = Some _,
          H' : model_satisfies_context _ _ _ _ |- _ ] =>
        rewrite SizeLeq_desc in H; unfold ctx_imp_leq in H;
        specialize (H _ H'); auto
      end.
  - match goal with
    | [ H : interp_size _ = _ |- _ ] =>
      repeat rewrite H
    end.
    match goal with
    | [ H : _ <> _, H' : context[remove_nth ?L] |- _ ] =>
      specialize (nth_error_shift_down (l:=L) H)
    end.
    erewrite map_nth_error; eauto.
    simpl.
    intros.
    match goal with
    | [ H : forall _ _ _, nth_error ?L _ = Some _ -> _,
        H' : nth_error ?L _ = Some _ |- _ ] =>
      specialize (H _ _ _ H')
    end.
    destructAll.
    split; prepare_Forall.
    all: rewrite Forall_forall in *.
    all:
      match goal with
      | [ H : context[List.In _ (map ?F ?B)], H' : List.In ?A ?B |- _ ] =>
        let H'' := fresh "H" in
        assert (H'' : List.In (F A) (map F B)) by ltac:(apply in_map; auto);
        specialize (H _ H''); auto
      end.
Qed.

Lemma SizeLeq_quotient : forall {f idx szctx szctx' szs0' szs1' sz sz1 sz2},
    (forall szc, f (SizeConst szc) = SizeConst szc) ->
    (forall v,
        v <> idx ->
        f (SizeVar v) = SizeVar (shift_down_after v idx 0)) ->
    f (SizeVar idx) = sz ->
    (forall sz1 sz2, f (SizePlus sz1 sz2) = SizePlus (f sz1) (f sz2)) ->
    szctx'
    =
    remove_nth
      (map
         (fun '(szs0, szs1) =>
            (map f szs0, map f szs1))
         szctx)
      idx ->
    SizeLeq szctx sz1 sz2 = Some true ->
    nth_error szctx idx = Some (szs0', szs1') ->
    Forall
      (fun sz' =>
         SizeLeq
           szctx'
           (f sz')
           sz
         = Some true)
      szs0' ->
    Forall
      (fun sz' =>
         SizeLeq
           szctx'
           sz
           (f sz')
         = Some true)
      szs1' ->
    SizeLeq
      szctx'
      (f sz1)
      (f sz2)
    =
    Some true.
Proof.
  intros.
  rewrite SizeLeq_desc in *.
  eapply ctx_imp_leq_map; eauto.
  intros.
  eexists.
  eapply model_satisfies_context_SizeLeq_quotient; eauto.
  match goal with
  | [ |- ?A = ?X ] => replace A with X; auto
  end.
Qed.

Lemma SizeLeq_subst : forall {F f sz'' szs0 szs1 sz0 sz1 kvs},
    SizeLeq
      (size
         (add_constraints
            (subst'_function_ctx
               (subst'_of (weak SSize))
               (update_size_ctx ((szs0, szs1) :: size F) F))
            kvs))
      sz0
      sz1
    = Some true ->
    debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz'' ->
    SizeValid (size F) sz'' ->
    Forall
      (fun sz' : Size => SizeLeq (size F) sz' sz'' = Some true)
      szs0 ->
    Forall
      (fun sz' : Size => SizeLeq (size F) sz'' sz' = Some true)
      szs1 ->
    SizeLeq
      (size
         (add_constraints
            F
            (subst'_kindvars (subst'_of (ext SSize sz'' id)) kvs)))
      (subst'_size f sz0)
      (subst'_size f sz1)
    = Some true.
Proof.
  intros.
  erewrite size_subst_size; eauto.
  eapply SizeLeq_quotient.
  6: eauto.
  5: eauto.
  5:{
    rewrite add_constraints_to_ks_of_kvs; simpl.
    destruct F; subst; simpl in *.
    erewrite nth_error_prefix_appliable; eauto.
    rewrite length_collect_szctx; auto.
  }
  all: eauto.
  1:{
    intros.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    simpl.
    unfold get_var'.
    match goal with
    | [ H : context[_ <> _ SSize -> _] |- _ ] =>
      rewrite H; auto
    end.
  }
  all: unfold subst'_sizes.
  all: rewrite map_map.
  all: prepare_Forall_with_map.
  all: erewrite <-subst_weaks_weak_size; eauto.
  all: unfold get_var'.
  all:
    match goal with
    | [ H : debruijn_subst_ext_conds _ _ _ _ |- _ ] =>
      generalize H;
      unfold debruijn_subst_ext_conds in H; destructAll; intros
    end.
  all:
    match goal with
    | [ H : forall _, _ = _ |- _ ] => rewrite H
    end.
  all: simpl.
  all: rewrite plus_zero.
  all: rewrite add_constraints_to_ks_of_kvs; simpl.
  all: rewrite map_app.
  all: destruct F; subst; simpl in *.
  all: erewrite remove_nth_prefix_appliable; eauto.
  all: try rewrite map_length.
  all: try rewrite length_collect_szctx; auto.
  all: repeat rewrite map_map.
  all:
    match goal with
    | [ |- context[_ ++ map ?F _] ] =>
      match goal with
      | [ |- context[ks_of_kvs ?KVS] ] =>
        replace F with
            (fun '(szs0, szs1) =>
               (subst'_sizes (weaks' (ks_of_kvs KVS)) szs0,
                subst'_sizes (weaks' (ks_of_kvs KVS)) szs1))
      end
    end.
  all: try apply FunctionalExtensionality.functional_extensionality.
  all: intros.
  all: destruct_prs; simpl.
  all: try erewrite subst_weaks_weak_sizes; eauto.
  all:
    try match goal with
        | [ |- (_, ?A) = (_, ?B) ] => replace B with A; auto
        end.
  all: try erewrite subst_weaks_weak_sizes; eauto.
  all: try now ltac:(unfold subst'_sizes; auto).
  all: eapply SizeLeq_weaks; eauto.
  all: rewrite map_length.
  all: apply length_collect_szctx.
Qed.

Lemma TypeValid_debruijn_subst_size_provable :
  (forall F t,
      TypeValid F t ->
      forall f kvs szs0 szs1 sz F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
        SizeValid (size F'') sz ->
        Forall
          (fun sz' => SizeLeq (size F'') sz' sz = Some true) szs0 ->
        Forall
          (fun sz' => SizeLeq (size F'') sz sz' = Some true) szs1 ->
        F = add_constraints F'' (SIZE szs0 szs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f kvs szs0 szs1 sz F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
        SizeValid (size F'') sz ->
        Forall
          (fun sz' => SizeLeq (size F'') sz' sz = Some true) szs0 ->
        Forall
          (fun sz' => SizeLeq (size F'') sz sz' = Some true) szs1 ->
        F = add_constraints F'' (SIZE szs0 szs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f kvs szs0 szs1 sz F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
        SizeValid (size F'') sz ->
        Forall
          (fun sz' => SizeLeq (size F'') sz' sz = Some true) szs0 ->
        Forall
          (fun sz' => SizeLeq (size F'') sz sz' = Some true) szs1 ->
        F = add_constraints F'' (SIZE szs0 szs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f kvs szs0 szs1 sz F' F'',
        debruijn_subst_ext_conds f (ks_of_kvs kvs) SSize sz ->
        SizeValid (size F'') sz ->
        Forall
          (fun sz' => SizeLeq (size F'') sz' sz = Some true) szs0 ->
        Forall
          (fun sz' => SizeLeq (size F'') sz sz' = Some true) szs1 ->
        F = add_constraints F'' (SIZE szs0 szs1 :: kvs) ->
        F' = add_constraints
               F'' (subst'_kindvars (subst'_of (ext SSize sz id)) kvs) ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *; subst.

  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
  - unfold get_var'.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    match goal with
    | [ H : debruijn_subst_ext_conds _ _ _ _ |- _ ] =>
      generalize H;
      unfold debruijn_subst_ext_conds in H; destructAll;
      intros
    end.
    match goal with
    | [ H : context[_ <> SSize -> _] |- _ ] =>
      erewrite H; eauto; solve_ineqs
    end.
    simpl.
    econstructor.
    4: erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- eapply nth_error_type_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply RecVarUnderRefPretype_subst_non_pretype; auto.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- simpl.
       erewrite sizeOfPretype_subst_no_effect;
         [ | eapply debruijn_subst_ext_under_knd | ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite type_subst_size; eauto.
       match goal with
       | [ |- context[?A :: map ?F ?L] ] =>
         replace (A :: map F L) with (map F (A :: L)) by auto
       end.
       erewrite sizeOfPretype_subst_size; eauto.
    -- eapply SizeValid_subst; eauto.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           match goal with
           | [ |- context[(?SZ, ?Q, ?HC)] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- TYPE (subst'_size ?F ?SZ) (subst'_qual ?F ?Q) ?HC = _ ] =>
           replace (TYPE (subst'_size F SZ) (subst'_qual F Q) HC)
             with
               (subst'_kindvar F (TYPE SZ Q HC)); eauto
         end.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- prepare_Forall_with_map.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- prepare_Forall_with_map.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- eapply LocValid_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- eapply LocValid_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- eapply LocValid_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           replace F with (add_constraints FP (KVS ++ [LOC]))
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- _ = subst'_kindvar ?F ?X ] =>
           replace (subst'_kindvar F X) with (subst'_kindvar F LOC) by auto
         end.
         simpl; auto.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- eapply LocValid_subst_size; eauto.
  - econstructor; eauto.
    prepare_Forall_with_map.
    eauto.
  - econstructor; eauto.
    prepare_Forall_with_map.
    destructAll.
    eexists.
    split.
    { erewrite sizeOfPretype_subst_no_effect; eauto; solve_ineqs.
      erewrite type_subst_size; eauto.
      erewrite sizeOfPretype_subst_size; eauto. }
    split.
    { eapply SizeValid_subst; eauto. }
    split.
    { eapply SizeValid_subst; eauto. }
    split; eauto.
    eapply SizeLeq_subst; eauto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
  - econstructor; eauto.
    -- eapply SizeValid_subst; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite <-qual_fctx_subst_weak_size_subst_size; eauto.
    -- match goal with
       | [ |- TypeValid ?F _ ] =>
         match goal with
         | [ |- context[add_constraints ?FP ?KVS] ] =>
           match goal with
           | [ |- context[(?SZ, ?Q, ?HC)] ] =>
             replace F with (add_constraints FP (KVS ++ [TYPE SZ Q HC]))
           end
         end
       end.
       2:{ rewrite add_constraints_snoc; simpl; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       3:{
         erewrite subst'_kindvars_snoc; eauto.
         match goal with
         | [ |- TYPE (subst'_size ?F ?SZ) (subst'_qual ?F ?Q) ?HC = _ ] =>
           replace (TYPE (subst'_size F SZ) (subst'_qual F Q) HC)
             with
               (subst'_kindvar F (TYPE SZ Q HC)); eauto
         end.
       }
       --- rewrite ks_of_kvs_app; simpl.
           apply debruijn_subst_ext_under_knd; auto.
       --- rewrite add_constraints_snoc; simpl; auto.
  - econstructor; eauto.
    all: prepare_Forall_with_map.
    all: eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_subst_size; eauto.
    -- match goal with
       | [ |- context[add_constraints (add_constraints ?F ?KVS1) ?KVS2] ] =>
         replace
           (add_constraints (add_constraints F KVS1) KVS2)
           with
             (add_constraints F (KVS1 ++ KVS2))
       end.
       2:{ rewrite add_constraints_app; auto. }
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       2:{ rewrite add_constraints_app; auto. }
       --- rewrite ks_of_kvs_app.
           apply debruijn_subst_ext_under_kindvars; auto.
       --- erewrite subst'_kindvars_app; eauto.
Qed.

Lemma FunTypeValid_InstInd F ft ft' a:
  InstIndValid F ft a ->
  InstInd ft a = Some ft' ->
  FunTypeValid F ft ->
  FunTypeValid F ft'.
Proof.
  intros.
  destruct ft; destruct a; simpl in *.
  all: destruct l.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all: destruct k.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ |- FunTypeValid _ ?FT ] =>
      match goal with
      | [ |- FunTypeValid
               _
               (FunT (subst'_kindvars ?SU ?L)
                     (subst'_arrowtype _ ?ATYP)) ] =>
        replace FT with
            (subst'_funtype SU (FunT L ATYP)) by auto
      end
    end.
  - specialize TypeValid_debruijn_subst_loc_provable.
    let H' := fresh "H" in intro H'; destruct H' as [_ [_ [_ H']]]; eapply H'; eauto.
    -- match goal with
       | [ H : FunTypeValid _ (FunT _ _) |- _ ] => inv H
       end.
       simpl in *.
       match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       simpl in *.
       econstructor; eauto.
       all:
         match goal with
         | [ |- context[add_constraints ?F ?L] ] =>
           replace (add_constraints F L) with
               (add_constraints F []) by auto
         end.
       all: simpl; eauto.
    -- simpl; apply simpl_debruijn_subst_ext_conds.
    -- simpl; auto.
  - specialize TypeValid_debruijn_subst_size_provable.
    let H' := fresh "H" in intro H'; destruct H' as [_ [_ [_ H']]]; eapply H'.
    5:{
      eapply Forall_impl.
      2: eauto.
      intros.
      simpl in *.
      destructAll.
      eauto.
    }
    4:{
      eapply Forall_impl.
      2:{
        match goal with
        | [ H : SizeValid _ ?SZ, H' : context[SizeLeq _ _ ?SZ] |- _ ] =>
            exact H'
        end.
      }
      intros.
      simpl in *.
      destructAll.
      eauto.
    }
    all: eauto.
    -- match goal with
       | [ H : FunTypeValid _ (FunT _ _) |- _ ] => inv H
       end.
       simpl in *.
       match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       simpl in *.
       econstructor; eauto.
       all:
         match goal with
         | [ |- context[add_constraints ?F ?L] ] =>
           replace (add_constraints F L) with
               (add_constraints F []) by auto
         end.
       all: simpl; eauto.
    -- simpl; apply simpl_debruijn_subst_ext_conds.
    -- simpl; auto.
  - specialize TypeValid_debruijn_subst_qual_provable.
    let H' := fresh "H" in intro H'; destruct H' as [_ [_ [_ H']]]; eapply H'.
    5:{
      eapply Forall_impl.
      2: eauto.
      intros.
      simpl in *.
      destructAll.
      eauto.
    }
    4:{
      eapply Forall_impl.
      2:{
        match goal with
        | [ H : QualValid _ ?SZ, H' : context[QualLeq _ _ ?SZ] |- _ ] =>
            exact H'
        end.
      }
      intros.
      simpl in *.
      destructAll.
      eauto.
    }
    all: eauto.
    -- match goal with
       | [ H : FunTypeValid _ (FunT _ _) |- _ ] => inv H
       end.
       simpl in *.
       match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       simpl in *.
       econstructor; eauto.
       all:
         match goal with
         | [ |- context[add_constraints ?F ?L] ] =>
           replace (add_constraints F L) with
               (add_constraints F []) by auto
         end.
       all: simpl; eauto.
    -- simpl; apply simpl_debruijn_subst_ext_conds.
    -- simpl; auto.
  - specialize TypeValid_debruijn_subst_provable.
    let H' := fresh "H" in intro H'; destruct H' as [_ [_ [_ H']]]; eapply H'; eauto.
    -- match goal with
       | [ H : FunTypeValid _ (FunT _ _) |- _ ] => inv H
       end.
       simpl in *.
       match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H
       end.
       simpl in *.
       econstructor; eauto.
       all:
         match goal with
         | [ |- context[add_constraints ?F ?L] ] =>
           replace (add_constraints F L) with
               (add_constraints F []) by auto
         end.
       all: simpl; eauto.
    -- simpl; apply simpl_debruijn_subst_ext_conds.
    -- simpl; auto.
Qed.

Ltac des_arr_eq :=
  match goal with
  | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
  end.

Definition simple_fields_eq F F':=
  qual F = qual F' /\
  size F = size F' /\
  type F = type F' /\
  location F = location F'.

Lemma shift_down_after_S : forall n,
    shift_down_after (Datatypes.S n) 0 0 = n.
Proof.
  intros.
  unfold shift_down_after.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    replace B with false; try lia
  end.
  apply eq_sym.
  rewrite Nat.ltb_ge; lia.
Qed.

Lemma InstIndsValid_last : forall {idxs F kvs idx tau1 tau2},
    InstIndsValid F (FunT kvs (Arrow tau1 tau2)) (idxs ++ [idx]) ->
    exists kvs',
      InstIndValid F (FunT kvs' (Arrow tau1 tau2)) idx.
Proof.
  induction idxs; intros; simpl in *; auto.
  - eexists; eauto.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; eauto
    end.
  - match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; eauto
    end.
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    match goal with
    | [ X : ArrowType |- _ ] => destruct X
    end.
    match goal with
    | [ H : InstIndsValid _ _ _, H' : forall _ _ _, _ |- _ ] =>
      apply H' in H
    end.
    destructAll.
    eexists.
    eapply InstIndValid_Function_Ctx_stronger; eauto.
Qed.

Lemma subst_indices_snoc : forall {A H H0 H1 H2 idxs idx expr},
    @subst_indices A H H0 H1 H2 (idxs ++ [idx]) expr =
    @subst_indices A H H0 H1 H2 idxs
                   (subst_index idx expr).
Proof.
  induction idxs; intros; simpl in *; auto.
  rewrite IHidxs; auto.
Qed.
  
Lemma type_update_linear_ctx F L :
  type (update_linear_ctx L F) = type F.
Proof.
  destruct F. reflexivity.
Qed.

Lemma type_update_label_ctx F L :
  type (update_label_ctx L F) = type F.
Proof.
  destruct F. reflexivity.
Qed.

Lemma label_update_linear_ctx F L :
  label (update_linear_ctx L F) = label F.
Proof.
  destruct F. reflexivity.
Qed.

Lemma update_label_linear_ctx F L1 L2 :
  update_label_ctx L1 (update_linear_ctx L2 F) =
  update_linear_ctx L2 (update_label_ctx L1 F).
Proof.
  destruct F. reflexivity.
Qed.

Lemma update_linear_ctx_idempotent F L1 L2 :
  update_linear_ctx L1 (update_linear_ctx L2 F) =
  update_linear_ctx L1 F.
Proof.
  destruct F. reflexivity.
Qed.

Lemma linear_update_linear_ctx F L :
  linear (update_linear_ctx L F) = L.
Proof.
  destruct F. reflexivity.
Qed.

Lemma Forall_Forall {T} (P1 P2: T -> Prop) L :
  (forall x, P1 x -> P2 x) -> (Forall P1 L) -> (Forall P2 L).
Proof.
  intros.
  induction H0.
  - apply Forall_nil.
  - apply Forall_cons; auto.
Qed.

Lemma sizeOfType_empty_ctx t L sz:
  sizeOfType [] t = Some sz ->
  sizeOfType L t = Some sz.
Proof.
  intros.
  rewrite  <- app_nil_l with (l := L).
  apply sizeOfType_add_ctx.
  auto.
Qed.

Lemma sizeOfPretype_empty_ctx pt sz L :
  sizeOfPretype [] pt = Some sz ->
  sizeOfPretype L pt = Some sz.
Proof.
  revert sz L.
  induction pt; intros; auto.
  - simpl in H. destruct v; discriminate H.
  - simpl in *.
    generalize dependent sz. induction l; intros; auto; simpl in *.
    destruct (sizeOfType [] a) eqn:Eq.
    + erewrite sizeOfType_empty_ctx; eauto.
      destruct (fold_size (map (sizeOfType []) l)) eqn:Eq'.
      ++ erewrite IHl; eauto. 
      ++ discriminate H.
    + discriminate H.
  - simpl. rewrite cons_append. apply sizeOfType_add_ctx.
    auto.
  - eapply sizeOfType_empty_ctx. eauto.
Qed.

Lemma SizeLeq_empty_ctx sz sz' L :
  SizeLeq [] sz sz' = Some true ->
  SizeLeq L sz sz' = Some true.
Proof.
  intros.
  eapply SizeLeq_Bigger_Ctx; eauto.
  constructor.
Qed.

Lemma QualValid_empty_ctx_var v:
  ~ QualValid (qual empty_Function_Ctx) (QualVar v).
Proof.
  intros h.
  inversion h; subst.
  - discriminate H.
  - destruct var; discriminate H0.
Qed.

Lemma QualValid_empty_ctx q L:
  QualValid [] q -> QualValid L q.
Proof.
  intros. inversion H; subst. eapply QualConstValid; eauto. destruct var; discriminate H1.
Qed.

Lemma LocValid_empty_ctx v L:
  LocValid (location empty_Function_Ctx) v -> LocValid (location L) v.
Proof.
  intros.
  inversion H; subst. eapply LocPValid. eauto. eapply LocVValid; eauto. destruct var; simpl in H1; lia.
Qed.

Lemma Forall_QualValid_empty_ctx L l:
  (Forall (fun q => (QualValid [] q)) l) -> (Forall (fun q => (QualValid L q)) l).
Proof.
  intros.
  eapply Forall_Forall.
  intros. apply QualValid_empty_ctx. exact H0. auto.
Qed.

Lemma SizeValid_empty_ctx s L:
  SizeValid (size empty_Function_Ctx) s -> SizeValid (size L) s.
Proof.
  induction s; intros; inversion H; subst; try discriminate H0; injection H0 as h; subst.
  - destruct var; discriminate H1.
  - eapply SizePlusValid; eauto.
  - eapply SizeConstValid; eauto.
Qed.

Lemma Forall_SizeValid_empty_ctx L l:
  Forall (fun s => (SizeValid (size empty_Function_Ctx) s)) l ->
  Forall (fun s => (SizeValid (size L) s)) l.
Proof.
  intros.
  eapply Forall_Forall.
  intros. apply SizeValid_empty_ctx. exact H0. auto.
Qed.

Lemma KindVarValid_empty_ctx a F:
  KindVarValid empty_Function_Ctx a -> KindVarValid F a.
Proof.
  induction a; intros; auto; destruct H; split; try (apply Forall_QualValid_empty_ctx; auto).
  - apply Forall_SizeValid_empty_ctx. auto.
  - apply Forall_SizeValid_empty_ctx. auto.
  - apply SizeValid_empty_ctx. auto.
  - apply QualValid_empty_ctx. auto.
Qed.

Lemma InstIndValid_Function_Ctx_empty : forall {F F' kvs tau1 tau2 idx},
    Function_Ctx_empty F ->
    InstIndValid F (FunT kvs (Arrow tau1 tau2)) idx ->
    InstIndValid F' (FunT kvs (Arrow tau1 tau2)) idx.
Proof.
  intros.
  unfold Function_Ctx_empty in *.
  destructAll.
  destruct F; subst; simpl in *.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H; simpl in *
  end.
  - econstructor.
    match goal with
    | [ H : LocValid _ _ |- _ ] => inv H
    end.
    -- econstructor; eauto.
    -- match goal with
       | [ H : _ < 0 |- _ ] => inv H
       end.
  - econstructor.
    -- eapply sizeOfPretype_empty_ctx; eauto.
    -- eapply SizeValid_empty_ctx; eauto.
    -- eapply SizeValid_empty_ctx; eauto.
    -- eapply SizeLeq_Bigger_Ctx; eauto.
       constructor.
    -- eapply TypeValid_sub; eauto.
       repeat constructor.
       simpl; lia.
    -- intros.
       match goal with
       | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
       end.
       eapply NoCapsPretype_list_sub; eauto.
       unfold heapable.
       simpl.
       constructor.
  - econstructor.
    -- eapply QualValid_empty_ctx; eauto.
    -- prepare_Forall.
       destructAll.
       split.
       --- eapply QualValid_empty_ctx; eauto.
       --- eapply QualLeq_empty_ctx; eauto.
    -- prepare_Forall.
       destructAll.
       split.
       --- eapply QualValid_empty_ctx; eauto.
       --- eapply QualLeq_empty_ctx; eauto.
  - econstructor.
    -- eapply SizeValid_empty_ctx; eauto.
    -- prepare_Forall.
       destructAll.
       split.
       --- eapply SizeValid_empty_ctx; eauto.
       --- eapply SizeLeq_empty_ctx; eauto.
    -- prepare_Forall.
       destructAll.
       split.
       --- eapply SizeValid_empty_ctx; eauto.
       --- eapply SizeLeq_empty_ctx; eauto.
Qed.

Lemma InstInd_app_kvs : forall {kvs kvs' atyp kvsres atypres atyp' idx},
    InstInd (FunT kvs atyp) idx = Some (FunT kvsres atypres) ->
    exists kvsres' atypres',
      InstInd (FunT (kvs ++ kvs') atyp') idx =
      Some (FunT (kvsres ++ kvsres') atypres') /\
      length kvsres' = length kvs'.
Proof.
  intros.
  destruct kvs.
  - simpl in *.
    match goal with
    | [ H : None = Some _ |- _ ] => inv H
    end.
  - match goal with
    | [ X : KindVar, Y : Index |- _ ] =>
      destruct X; destruct Y; simpl in *
    end.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    all: do 2 eexists.
    all: split.
    all: try erewrite <-subst'_kindvars_app; eauto.
    all: try apply pure_under_kindvars.
    all: rewrite length_subst_kindvars; auto.
Qed.
    
Lemma InstIndsValid_unused_kvs : forall {idx kvs kvs' F atyp atyp' idxs},
    idx = length kvs ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    InstIndsValid F (FunT (kvs ++ kvs') atyp') idxs.
Proof.
  induction idx; simpl in *.
  - intros.
    destruct kvs; simpl in *.
    2:{
      match goal with
      | [ H : 0 = Datatypes.S _ |- _ ] => inv H
      end.
    }
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; try now constructor
    end.
    match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inv H
    end.
  - intros.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; try now constructor
    end.
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    destruct kvs.
    1:{
      simpl in *.
      match goal with
      | [ H : Datatypes.S _ = 0 |- _ ] => inv H
      end.
    }
    match goal with
    | [ H : Datatypes.S _ = _ |- _ ] => simpl in H; inv H
    end.
    simpl.
    match goal with
    | [ H : InstInd _ _ = Some _
        |- InstIndsValid _ (FunT (_ :: _ ++ ?A) ?B) _ ] =>
      specialize (InstInd_app_kvs (kvs':=A) (atyp':=B) H)
    end.
    intros; destructAll.
    econstructor; eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       all: econstructor; eauto.
    -- eapply IHidx; eauto.
       eapply InstInd_length_eq; eauto.
Qed.

Lemma empty_neq_snoc : forall {A} {l : list A} {el},
    [] <> l ++ [el].
Proof.
  destruct l; intro; intro H; inv H.
Qed.

Lemma InstInd_last_kind_preserved : forall {kvs kvs' kv kv' atyp atyp' idx},
    InstInd (FunT (kvs ++ [kv]) atyp) idx =
    Some (FunT (kvs' ++ [kv']) atyp') ->
    kind_of_kindvar kv = kind_of_kindvar kv'.
Proof.
  intros.
  destruct kvs; destruct idx; simpl in *.
  1-4:
    match goal with
    | [ |- kind_of_kindvar ?X = _ ] => destruct X; simpl in *
    end.
  1-16:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all: try now ltac:(exfalso; eapply empty_neq_snoc; eauto).
  all: destruct k.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ H : subst'_kindvars _ _ = _ |- _ ] =>
      erewrite <-subst'_kindvars_snoc in H; eauto
    end.
  all: try apply pure_under_kindvars.
  all:
    match goal with
    | [ H : _ ++ [_] = _ |- _ ] => apply snoc_inv in H; destructAll
    end.
  all:
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl; auto
    end.
Qed.  

Lemma InstIndsValid_snoc_inv : forall {idxs idx kvs atyp F},
    InstIndsValid F (FunT kvs atyp) (idxs ++ [idx]) ->
    length kvs = Datatypes.S (length idxs) ->
    exists kvs' kv kv',
      kvs = kvs' ++ [kv] /\
      kind_of_kindvar kv = kind_of_kindvar kv' /\
      InstIndValid F (FunT [kv'] atyp) idx /\
      InstIndsValid F (FunT kvs' atyp) idxs.
Proof.
  induction idxs; intros.
  - destruct kvs; simpl in *; auto.
    -- match goal with
       | [ H : 0 = 1 |- _ ] => inv H
       end.
    -- destruct kvs; simpl in *; auto.
       --- do 3 eexists.
           split.
           1:{
             match goal with
             | [ |- [?X] = ?A ++ [?B] ] =>
               replace (A ++ [B]) with ([] ++ [X]) by auto
             end.
             simpl; auto.
           }
           match goal with
           | [ H : InstIndsValid _ _ _ |- _ ] => inv H
           end.
           split.
           2:{
             split; eauto.
             constructor.
           }
           auto.
       --- match goal with
           | [ H : _ = 1 |- _ ] => inv H
           end.
  - rewrite <-app_comm_cons in *.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H
    end.
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => apply IHidxs in H
    end.
    2:{
      simpl in *.
      match goal with
      | [ H : length ?X = Datatypes.S _ |- _ ] =>
        destruct X; simpl in *
      end.
      1:{
        match goal with
        | [ H : None = Some _ |- _ ] => inv H
        end.
      }
      match goal with
      | [ X : KindVar |- _ ] => destruct X
      end.
      all:
        match goal with
        | [ H : InstIndValid _ _ ?A |- _ ] => destruct A
        end.
      all:
        match goal with
        | [ H : _ = Some _ |- _ ] => inv H
        end.
      all: rewrite length_subst_kindvars.
      all:
        match goal with
        | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
          inv H; auto
        end.
    }
    destructAll.
    match goal with
    | [ H : length ?A = Datatypes.S _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : length A > 0); [ rewrite H; lia | ];
      apply snoc_exists in H'
    end.
    destructAll.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      specialize (InstInd_last_kind_preserved H);
      apply InstInd_remove_snoc in H
    end.
    destructAll.
    do 3 eexists.
    split.
    2:{
      split.
      2:{
        split.
        - eapply InstIndValid_Function_Ctx_stronger; eauto.
        - econstructor; [ | eauto | ].
          -- match goal with
             | [ |- InstIndValid _ (FunT ?X _) _ ] =>
               destruct X; simpl in *
             end.
             --- match goal with
                 | [ H : None = Some _ |- _ ] => inv H
                 end.
             --- eapply InstIndValid_remove_snoc; eauto.
          -- eapply InstIndsValid_Function_Ctx_stronger; eauto.
      }
      shelve.
    }
    eauto.

    Unshelve.
    eapply eq_trans; eauto.
Qed.

Lemma app_no_eq : forall {A} {l l' l'' : list A} {el},
    length l = length l'' ->
    l <> l' ++ (el :: l'').
Proof.
  destruct l; intros; simpl in *.
  - destruct l'; intros; simpl in *; intro H'; inv H'.
  - intro.
    match goal with
    | [ H : ?A :: ?B = ?C |- _ ] =>
      let H' := fresh "H" in
      assert (H' : length (A :: B) = length C);
      [ rewrite H; auto | ]
    end.
    simpl in *.
    rewrite app_length in *.
    simpl in *.
    lia.
Qed.

Lemma empty_or_snoc : forall {A} (l : list A),
    l = [] \/ exists el' l', l = l' ++ [el'].
Proof.
  induction l; intros; simpl in *; auto.
  case IHl; intros; destructAll; subst.
  - right.
    eexists; exists [].
    simpl; eauto.
  - right.
    do 2 eexists.
    rewrite app_comm_cons; eauto.
Qed.

Lemma InstFunctionCtxInds_length_ineq : forall {idxs F F'},
    InstFunctionCtxInds F idxs = Some F' ->
    location F >= location F' /\
    length (qual F) >= length (qual F') /\
    length (size F) >= length (size F') /\
    length (type F) >= length (type F').
Proof.
  induction idxs; intros; simpl in *.
  - match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    lia.
  - remember (InstFunctionCtxInds F idxs) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros; subst.
    all:
      match goal with
      | [ H : ?A = _, H' : context[?A] |- _ ] =>
        rewrite H in H'; inv H'
      end.
    match goal with
    | [ H : InstFunctionCtxInds _ _ = Some _ |- _ ] =>
      apply IHidxs in H
    end.
    destructAll.
    match goal with
    | [ H : InstFunctionCtxInd ?F ?IDX = Some _ |- _ ] =>
      destruct F; destruct IDX; simpl in *
    end.
    -- destruct location;
         match goal with
         | [ H : _ = Some _ |- _ ] => inv H
         end.
       unfold subst'_function_ctx; simpl in *.
       repeat rewrite map_length.
       lia.
    -- destruct size;
         match goal with
         | [ H : _ = Some _ |- _ ] => inv H
         end.
       unfold subst'_function_ctx; simpl in *.
       repeat rewrite map_length.
       lia.
    -- destruct qual;
         match goal with
         | [ H : _ = Some _ |- _ ] => inv H
         end.
       unfold subst'_function_ctx; simpl in *.
       repeat rewrite map_length.
       lia.
    -- destruct type;
         match goal with
         | [ H : _ = Some _ |- _ ] => inv H
         end.
       unfold subst'_function_ctx; simpl in *.
       repeat rewrite map_length.
       lia.
Qed.

Lemma InstFunctionCtxInds_length : forall {idxs F F'},
    InstFunctionCtxInds F idxs = Some F' ->
    length idxs =
    location F - location F' +
    length (qual F) - length (qual F') +
    length (size F) - length (size F') +
    length (type F) - length (type F').
Proof.
  induction idxs.
  - intros; simpl in *.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    lia.
  - intros; simpl in *.
    remember (InstFunctionCtxInds F idxs) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros; subst.
    all:
      match goal with
      | [ H : ?A = _, H' : context[?A] |- _ ] =>
        rewrite H in H'; inv H'
      end.
    erewrite IHidxs; eauto.
    match goal with
    | [ H : InstFunctionCtxInd ?F ?A = Some _ |- _ ] =>
      destruct F; destruct A; simpl in *
    end.
    1: destruct location.
    3: destruct size.
    5: destruct qual.
    7: destruct type.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    all: unfold subst'_function_ctx; simpl in *.
    all: repeat rewrite map_length.
    all:
      match goal with
      | [ H : InstFunctionCtxInds _ _ = Some _ |- _ ] =>
        apply InstFunctionCtxInds_length_ineq in H
      end.
    all: simpl in *; lia.
Qed.

Lemma length_kindvars : forall {kvs : list KindVar},
    length kvs =
    ks_of_kvs kvs SLoc +
    ks_of_kvs kvs SQual +
    ks_of_kvs kvs SSize +
    ks_of_kvs kvs SPretype.
Proof.
  induction kvs; simpl in *; auto.
  match goal with
  | [ X : KindVar |- _ ] => destruct X; simpl in *
  end.
  all: unfold plus; simpl.
  all: rewrite IHkvs; lia.
Qed.

Lemma InstFunctionCtxInds_add_constraints : forall {kvs idxs F F' atyp},
    InstFunctionCtxInds F idxs = Some F' ->
    simple_fields_eq F (add_constraints F' kvs) ->
    InstIndsValid F' (FunT kvs atyp) idxs ->
    length kvs = length idxs.
Proof.
  intros.
  match goal with
  | [ H : InstFunctionCtxInds _ _ = Some _ |- _ ] =>
    apply InstFunctionCtxInds_length in H; rewrite H
  end.
  unfold simple_fields_eq in *.
  destructAll.
  rewrite add_constraints_to_ks_of_kvs in *; simpl in *.
  repeat match goal with
         | [ H : ?A = _ |- context[?A] ] => rewrite H
         end.
  repeat rewrite app_length.
  repeat rewrite map_length.
  rewrite length_collect_qctx.
  rewrite length_collect_szctx.
  rewrite length_collect_tctx.
  rewrite length_kindvars; lia.
Qed.

Lemma InstInd_length : forall {kvs atyp idx kvs' atyp'},
    InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp') ->
    length kvs = Datatypes.S (length kvs').
Proof.
  intros.
  match goal with
  | [ X : Index |- _ ] => destruct X
  end.
  all:
    match goal with
    | [ H : InstInd (FunT ?A _) _ = Some _ |- _ ] =>
      destruct A
    end.
  all: simpl in *.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ X : KindVar |- _ ] => destruct X
    end.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.
  all: rewrite length_subst_kindvars; auto.
Qed.

Lemma InstIndsValid_length_eq_to_InstInds : forall {idxs kvs F atyp},
    InstIndsValid F (FunT kvs atyp) idxs ->
    length kvs = length idxs ->
    exists atyp',
      InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp').
Proof.
  induction idxs.
  - intros.
    destruct kvs.
    -- eexists.
       unfold InstInds.
       simpl.
       eauto.
    -- simpl in *.
       match goal with
       | [ H : Datatypes.S _ = 0 |- _ ] => inv H
       end.
  - intros; simpl in *.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H
    end.
    match goal with
    | [ X : FunType |- _ ] => destruct X
    end.
    match goal with
    | [ H : InstIndsValid _ (FunT ?A _) ?B |- _ ] =>
      let H' := fresh "H" in
      assert (H' : length A = length B)
    end.
    { match goal with
      | [ |- ?A = ?B ] =>
        let H' := fresh "H" in
        assert (H' : Datatypes.S A = Datatypes.S B);
        [ | inv H'; auto ]
      end.
      match goal with
      | [ H : _ = ?B |- _ = ?B ] => rewrite <-H
      end.
      apply eq_sym.
      eapply InstInd_length; eauto. }
      
    unfold InstInds.
    match goal with
    | [ H : InstInd _ _ = Some _ |- _ ] =>
      simpl in *; rewrite H; clear H
    end.
    match goal with
    | [ H : InstIndsValid _ _ _, H' : length _ = length _ |- _ ] =>
      specialize (IHidxs _ _ _ H H')
    end.
    destructAll.
    unfold InstInds in *.
    eauto.
Qed.

Definition subst_of_index (idx : Index) :=
  match idx with
  | LocI l => ext subst.SLoc l id
  | SizeI s => ext subst.SSize s id
  | QualI q => ext subst.SQual q id
  | PretypeI pt => ext subst.SPretype pt id
  end.

Fixpoint subst_of_indices (idxs : list Index) :=
  match idxs with
  | [] => id
  | idx :: idxs' => (subst_of_index idx) ∘ (subst_of_indices idxs')
  end.

Lemma subst'_of_comp : forall {su su'},
    subst'_of su ∘' subst'_of su' =
    subst'_of (su ∘ su').
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  destruct x.
  all: simpl.
  all:
    match goal with
    | [ |- ?F ?A (?F ?B ?C) = _ ] =>
      replace (F A (F B C)) with
          (subst_ext' A (subst_ext' B C))
        by auto
    end.
  all:
    match goal with
    | [ |- _ = ?F ?A (?F ?B ?C) ] =>
      replace (F A (F B C)) with
          (subst_ext' A (subst_ext' B C))
        by auto
    end.
  all: repeat rewrite subst_ext'_assoc.
  all: rewrite weaks_subst_comm; auto.
Qed.

Definition knd_of_index (idx : Index) :=
  match idx with
  | LocI _ => subst.SLoc
  | QualI _ => subst.SQual
  | SizeI _ => subst.SSize
  | PretypeI _ => subst.SPretype
  end.

Definition obj_of_index (idx : Index)
  : subst.Kind (knd_of_index idx) :=
  match idx with
  | LocI l => l
  | QualI q => q
  | SizeI sz => sz
  | PretypeI pt => pt
  end.

Lemma idx_debruijn_subst_ext_conds : forall idx,
    debruijn_subst_ext_conds
      (subst'_of (subst_of_index idx))
      debruijn.zero
      (knd_of_index idx)
      (obj_of_index idx).
Proof.
  destruct idx; simpl.
  all: apply simpl_debruijn_subst_ext_conds.
Qed.

Definition multisubst_func :=
  forall knd : subst.Ind, list (subst.Kind knd).
Definition empty_msf : multisubst_func := fun _ => [].

Definition add_pr_to_msf (knd : subst.Ind) (obj : subst.Kind knd) (f : multisubst_func)
  : multisubst_func :=
  fun knd' =>
    match knd', knd, obj with
    | subst.SLoc, subst.SLoc, _ => obj :: f subst.SLoc
    | subst.SLoc, _, _ => f subst.SLoc
    | subst.SQual, subst.SQual, _ => obj :: f subst.SQual
    | subst.SQual, _, _ => f subst.SQual
    | subst.SSize, subst.SSize, _ => obj :: f subst.SSize
    | subst.SSize, _, _ => f subst.SSize
    | subst.SPretype, subst.SPretype, _ => obj :: f subst.SPretype
    | subst.SPretype, _, _ => f subst.SPretype
    end.

Definition add_index_to_msf (idx : Index) :=
  add_pr_to_msf (knd_of_index idx) (obj_of_index idx).

Definition msf_of_indices (idxs : list Index) :=
  fold_left (fun f idx => add_index_to_msf idx f) idxs empty_msf.

Definition debruijn_multisubst_ext_conds
           (f : Subst' subst.Kind)
           (ks : subst.Ind -> nat)
           (msf : multisubst_func) :=
  (forall knd v' ks',
      v' < ks knd ->
      f knd v' ks' =
      subst.VarKind knd (ks' knd + v')) /\
  (forall knd v' ks' obj,
      ks knd <= v' ->
      nth_error (msf knd) (v' - ks knd) = Some obj ->
      f knd v' ks' =
      subst.subst'_rwasm
        knd
        (debruijn.weaks' (debruijn.plus ks ks'))
        obj) /\
  (forall knd v' ks',
      ks knd <= v' ->
      nth_error (msf knd) (v' - ks knd) = None ->
      f knd v' ks' =
      subst.VarKind knd (ks' knd + v' - (length (msf knd)))).

Lemma subst_to_multisubst : forall {f ks knd obj},
    debruijn_subst_ext_conds f ks knd obj ->
    debruijn_multisubst_ext_conds
      f ks
      (add_pr_to_msf knd obj empty_msf).
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  split; [ | split ].
  - intros.
    destruct knd; destruct knd0; simpl in *.
    all:
      match goal with
      | [ H : context[_ <> ?X], H' : _ < _ ?X |- _ ] => idtac
      | [ H : context[_ <> ?X] |- _ ] => rewrite H
      end.
    all: simpl; auto; solve_ineqs.
    all:
      match goal with
      | [ H : context[_ <> _ _] |- _ ] => rewrite H
      end.
    all: try apply Nat.lt_neq; auto.
    all: unfold shift_down_after.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with true; auto
      end.
    all: apply eq_sym.
    all: rewrite Nat.ltb_lt; auto.
  - intros.
    destruct knd; destruct knd0; simpl in *.
    all: unfold empty_msf in *.
    all:
      try match goal with
          | [ H : nth_error [_] ?IDX = Some _ |- _ ] =>
            remember IDX as idx;
            revert H; generalize (eq_sym Heqidx);
            case idx; intros; simpl in *
          end.
    all:
      try match goal with
          | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
            remember IDX as idx'; destruct idx'; inversion H
          end.
    all:
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst
      end.
    all: rewrite Nat.sub_0_le in *.
    all:
      match goal with
      | [ H : ?A <= ?B, H' : ?B <= ?A |- _ ] =>
        specialize (Nat.le_antisymm _ _ H H'); intros; subst
      end.
    all:
      match goal with
      | [ H : context[?A ?B ?C _] |- ?A ?B ?C _ = _ ] =>
        rewrite H; auto
      end.
  - intros.
    destruct knd; destruct knd0; simpl in *.
    all:
      match goal with
      | [ H : context[_ <> ?X] |- _ ?X _ _ = _ ] => idtac
      | [ H : context[_ <> _], H' : context[_ <> _ _] |- _ ] =>
        rewrite H
      end.
    all: simpl; solve_ineqs.
    all: try rewrite Nat.sub_0_r; auto.

    all: rewrite nth_error_None in *.
    all: unfold empty_msf in *; simpl in *.
    all:
      match goal with
      | [ H : context[_ <> _ _] |- _ ] => rewrite H
      end.
    all: try intro; subst.
    all: try rewrite Nat.sub_diag in *.
    all:
      try match goal with
          | [ H : 1 <= 0 |- _ ] => inversion H
          end.

    all: unfold shift_down_after.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false; auto
      end.
    all: apply eq_sym.
    all: rewrite Nat.ltb_ge; auto.
Qed.

Lemma id_multisubst :
  debruijn_multisubst_ext_conds (subst'_of id) zero empty_msf.
Proof.
  split; [ | split ].
  all: intros; simpl.
  all: destruct knd; simpl.
  all: unfold get_var'.
  all: unfold weaks'.
  all: unfold var.
  all: simpl.
  all: unfold zero.
  all: rewrite Nat.add_0_r.
  all: try rewrite Nat.sub_0_r.
  all: auto.
  all: unfold empty_msf in *.
  all:
    try match goal with
        | [ H : nth_error [] ?IDX = _ |- _ ] =>
          destruct IDX; simpl in *; inversion H
        end.
Qed.

Definition merge_msfs
           (msf1 : multisubst_func)
           (msf2 : multisubst_func) : multisubst_func :=
  fun knd => msf1 knd ++ msf2 knd.

Definition value_closed
           (knd : subst.Ind)
           (obj : subst.Kind knd) :=
  forall f,
    subst.subst'_rwasm knd f obj = obj.

Definition msf_closed (msf : multisubst_func) :=
  forall knd i obj,
    nth_error (msf knd) i = Some obj ->
    value_closed knd obj.

Lemma multisubst_comp : forall {f1 f2 ks msf1 msf2},
    debruijn_multisubst_ext_conds f1 ks msf1 ->
    debruijn_multisubst_ext_conds f2 ks msf2 ->
    msf_closed msf2 ->
    debruijn_multisubst_ext_conds
      (f1 ∘' f2) ks (merge_msfs msf2 msf1).
Proof.
  intros.
  unfold debruijn_multisubst_ext_conds in *.
  destructAll.
  split; [ | split ]; intros; simpl.
  - match goal with
    | [ H : context[_ < _ _ -> ?F _ _ _ = _]
        |- context[?F _ _ _] ] =>
      rewrite H; auto
    end.
    destruct knd; simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false; [ | apply eq_sym ]
      end.
    all: try rewrite Nat.ltb_ge.
    all: try apply le_plus_l.
    all: rewrite plus_zero.
    all: rewrite minus_plus.
    all:
      match goal with
      | [ H : context[_ < _ _ -> ?F _ _ _ = _]
          |- context[?F _ _ _] ] =>
        rewrite H; auto
      end.
  - unfold merge_msfs in *.
    match goal with
    | [ H : nth_error (?L ++ _) ?IDX = Some _ |- _ ] =>
      specialize (Nat.lt_ge_cases IDX (length L));
      let H' := fresh "H" in intro H'; case H'; intros
    end.
    -- match goal with
       | [ H : nth_error (?L ++ _) ?IDX = Some _,
           H' : ?IDX < length ?L |- _ ] =>
         rewrite (nth_error_app1 _ _ H') in H
       end.
       match goal with
       | [ H : context[_ <= _ ->
                       nth_error _ _ = Some _ ->
                       ?F _ _ _ = _]
           |- _ _ (?F _ _ _) = _ ] =>
         erewrite H; eauto
       end.
       match goal with
       | [ H : msf_closed _,
           H' : nth_error _ _ = Some _ |- _ ] =>
         repeat erewrite (H _ _ _ H'); auto
       end.
    -- match goal with
       | [ H : context[_ <= _ ->
                       nth_error _ _ = None ->
                       ?F _ _ _ = _]
           |- _ _ (?F _ _ _) = _ ] =>
         erewrite H; eauto
       end.
       2:{
         rewrite nth_error_None; auto.
       }

       destruct knd; simpl.
       all: unfold get_var'.
       all: unfold under_ks'.
       all:
         match goal with
         | [ |- context[if ?B then _ else _] ] =>
           replace B with false
         end.
       all:
         try match goal with
             | [ |- false = _ ] =>
               apply eq_sym; rewrite Nat.ltb_ge;
               rewrite <-Nat.add_sub_assoc; [ apply le_plus_l | ]
             end.
       all: try eapply le_trans; eauto.
       all: try apply Nat.le_sub_l.

       all:
         match goal with
         | [ H : length ?L <= ?IDX,
             H' : nth_error (?L ++ _) _ = Some _ |- _ ] =>
           rewrite (nth_error_app2 _ _ H) in H'
         end.
       all: rewrite <-Nat.sub_add_distr.
       all:
         match goal with
         | [ |- context[_ - (?A + ?B)] ] =>
           rewrite (Nat.add_comm A B)
         end.
       all: rewrite <-minus_plus_simpl_l_reverse.
       all:
         match goal with
         | [ H : nth_error _ (?A - ?B - ?C) = Some _ |- _ ] =>
           rewrite <-Nat.sub_add_distr in H;
           rewrite (Nat.add_comm B C) in H;
           rewrite Nat.sub_add_distr in H
         end.
       all:
         match goal with
         | [ H : context[_ <= _ ->
                         nth_error _ _ = Some _ ->
                         ?F _ _ _ = _]
             |- ?F _ _ _ = _ ] =>
           erewrite H; eauto
         end.
       all: simpl.
       all: try rewrite plus_zero; auto.

       all:
         match goal with
         | [ H : ?A <= ?B, H' : ?C <= ?B - ?A |- _ ] =>
           apply (plus_le_compat_r _ _ A) in H';
           rewrite Nat.sub_add in H'; auto;
           apply (Nat.sub_le_mono_r _ _ C) in H';
           rewrite minus_plus in H'; auto
         end.
  - rewrite nth_error_None in *.
    unfold merge_msfs in *.
    rewrite app_length in *.
    match goal with
    | [ H : context[_ <= _ ->
                    nth_error _ _ = None ->
                    ?F _ _ _ = _]
        |- _ _ (?F _ _ _) = _ ] =>
      erewrite H; eauto
    end.
    2:{
      rewrite nth_error_None.
      eapply le_trans; [ | eauto ].
      apply le_plus_l.
    }
    destruct knd; simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false
      end.
    all:
      try match goal with
          | [ |- false = _ ] =>
            apply eq_sym; rewrite Nat.ltb_ge;
            rewrite <-Nat.add_sub_assoc; [ apply le_plus_l | ]
          end.
    all:
      try match goal with
          | [ H : _ + _ <= _ - _ |- _ ] =>
            eapply le_trans; [ | eapply le_trans; [ exact H | ] ]
          end.
    all: try apply Nat.le_sub_l.
    all: try apply le_plus_l.

    all: rewrite <-Nat.sub_add_distr.
    all:
      match goal with
      | [ |- context[_ - (?A + ?B)] ] =>
        rewrite (Nat.add_comm A B)
      end.
    all: rewrite <-minus_plus_simpl_l_reverse.
    all:
      match goal with
      | [ H : context[_ <= _ ->
                      nth_error _ _ = None ->
                      ?F _ _ _ = _]
          |- ?F _ _ _ = _ ] =>
        erewrite H; eauto
      end.
    all: try rewrite nth_error_None.
    all:
      try match goal with
          | [ |- _ <= _ - ?A - _ ] =>
            rewrite (Nat.add_le_mono_r _ _ A)
          end.
    all: try rewrite <-Nat.sub_add_distr.
    all:
      try match goal with
          | [ |- context[_ - (?A + ?B)] ] =>
            rewrite (Nat.add_comm A B)
          end.
    all: try rewrite Nat.sub_add_distr.
    all: try rewrite Nat.sub_add; auto.
    all:
      try match goal with
          | [ |- (?A + ?B) <= _ ] =>
            rewrite (Nat.add_comm A B); auto
          end.
    all:
      try match goal with
          | [ H : ?A + _ <= ?B |- ?A <= ?B ] =>
            eapply le_trans; [ | exact H ]; apply le_plus_l
          end.

     all:
       try match goal with
           | [ H : ?A <= ?B, H' : ?C <= ?B - ?A |- _ <= _ ] =>
             apply (plus_le_compat_r _ _ A) in H';
             rewrite Nat.sub_add in H'; auto;
             apply (Nat.sub_le_mono_r _ _ C) in H';
             rewrite minus_plus in H'; auto;
             rewrite Nat.sub_add_distr in H';
             eapply le_trans; [ exact H' | ]
           end.       
     all: try apply Nat.le_sub_l.

     all: simpl.
     all: unfold plus.
     all: unfold zero.
     all: rewrite Nat.add_0_r.
     all: rewrite Nat.add_sub_assoc.
     all:
       try match goal with
           | [ H : _ + _ <= _ - _ |- _ ] =>
             eapply le_trans; [ | eapply le_trans; [ exact H | ] ]
           end.
     all: try apply le_plus_l.
     all: try apply Nat.le_sub_l.
     all: rewrite <-Nat.sub_add_distr.
     all:
       match goal with
       | [ |- context[_ - (?A + ?B)] ] =>
         rewrite (Nat.add_comm A B)
       end.
     all: rewrite Nat.sub_add_distr; auto.
Qed.

Lemma empty_msf_closed : msf_closed empty_msf.
Proof.
  unfold msf_closed; intros.
  unfold empty_msf in *.
  match goal with
  | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
    destruct IDX; inversion H
  end.
Qed.

Lemma LocValid_zero_imp_value_closed : forall {l},
    LocValid 0 l ->
    value_closed subst.SLoc l.
Proof.
  intros.
  match goal with
  | [ H : LocValid _ _ |- _ ] => inversion H; subst; simpl in *
  end.
  2:{
    match goal with | [ H : _ < 0 |- _ ] => inversion H end.
  }
  intro; auto.
Qed.  

Lemma QualValid_empty_imp_value_closed : forall {q},
    QualValid [] q ->
    value_closed subst.SQual q.
Proof.
  intros.
  match goal with
  | [ H : QualValid _ _ |- _ ] => inversion H; subst; simpl in *
  end.
  2:{
    match goal with
    | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
      destruct IDX; inversion H
    end.
  }
  intro; auto.
Qed.

Lemma SizeValid_empty_imp_value_closed : forall {sz},
    SizeValid [] sz ->
    value_closed subst.SSize sz.
Proof.
  induction sz; intros;
    match goal with
    | [ H : SizeValid [] _ |- _ ] => inversion H; subst
    end;
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] => inversion H; subst
    end.
  - match goal with
    | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
      destruct IDX; inversion H
    end.
  - unfold value_closed.
    intro.
    simpl.
    match goal with
    | [ H : _ -> _, H' : _ -> _ |- _ ] =>
      rewrite H; auto; rewrite H'; auto
    end.
  - intro; auto.
Qed.

Lemma debruijn_under_under_kindvars : forall {kvs f ks},
    debruijn_under_conds f ks ->
    debruijn_under_conds
      (subst.under_kindvars' kvs f)
      (fold_right
         (fun kv ks' =>
            (debruijn.plus
               (debruijn.sing
                  (subst.kind_of_kindvar kv)
                  1)
               ks'))
         ks
         kvs).
Proof.
  induction kvs; simpl; auto.
  intros.
  specialize (IHkvs _ _ H).
  destruct a; simpl.
  all: unfold subst.under_kindvar'; simpl.
  all: apply debruijn_under_under_knd; auto.
Qed.

Lemma debruijn_under_change_ks : forall {f ks ks'},
    debruijn_under_conds f ks ->
    ks = ks' ->
    debruijn_under_conds f ks'.
Proof.
  intros; subst; auto.
Qed.

Definition ks_of_fctx (F : Function_Ctx) :=
  fun knd =>
    match knd with
    | subst.SLoc => location F
    | subst.SQual => length (qual F)
    | subst.SSize => length (size F)
    | subst.SPretype => length (type F)
    end.

Lemma qual_under_conds_no_effect : forall {F q f},
    debruijn_under_conds f (ks_of_fctx F) ->
    QualValid (qual F) q ->
    subst.subst'_qual f q = q.
Proof.
  unfold debruijn_under_conds.
  intros.
  destruct q; simpl in *; auto.
  unfold get_var'.
  erewrite H.
  - unfold zero; simpl; auto.
  - unfold ks_of_fctx.
    match goal with
    | [ H : QualValid _ _ |- _ ] => inversion H; subst
    end;
      match goal with
      | [ H : @Logic.eq Qual _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    rewrite <-nth_error_Some.
    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] => rewrite H
    end.
    solve_ineqs.
Qed.

Lemma quals_under_conds_no_effect : forall {qs F f},
    debruijn_under_conds f (ks_of_fctx F) ->
    Forall (QualValid (qual F)) qs ->
    subst.subst'_quals f qs = qs.
Proof.
  induction qs; intros; simpl in *; auto.
  match goal with
  | [ H : Forall _ _ |- _ ] => inversion H; subst
  end.
  erewrite qual_under_conds_no_effect; eauto.
  erewrite IHqs; eauto.
Qed.

Lemma loc_under_conds_no_effect : forall {F l f},
    debruijn_under_conds f (ks_of_fctx F) ->
    LocValid (location F) l ->
    subst.subst'_loc f l = l.
Proof.
  unfold debruijn_under_conds.
  intros.
  match goal with
  | [ H : LocValid _ _ |- _ ] =>
    inversion H; subst; simpl in *; auto
  end.
  unfold get_var'.
  match goal with
  | [ H : forall _ _ _, _ -> _ |- _ ] => rewrite H
  end.
  - unfold zero.
    simpl; auto.
  - unfold ks_of_fctx; auto.
Qed.

Lemma size_under_conds_no_effect : forall {sz F f},
    debruijn_under_conds f (ks_of_fctx F) ->
    SizeValid (size F) sz ->
    subst.subst'_size f sz = sz.
Proof.
  induction sz; intros; simpl in *; auto;
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inversion H; subst
    end;
    match goal with
    | [ H : @Logic.eq Size _ _ |- _ ] => inversion H; subst
    end.
  - unfold get_var'.
    match goal with
    | [ H : debruijn_under_conds _ _ |- _ ] => rewrite H; auto
    end.
    unfold ks_of_fctx.
    rewrite <-nth_error_Some.
    match goal with
    | [ H : ?A = _ |- ?A <> _ ] => rewrite H; solve_ineqs
    end.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma sizes_under_conds_no_effect : forall {szs F f},
    debruijn_under_conds f (ks_of_fctx F) ->
    Forall (SizeValid (size F)) szs ->
    subst.subst'_sizes f szs = szs.
Proof.
  induction szs; intros; simpl in *; auto.
  match goal with
  | [ H : Forall _ _ |- _ ] => inversion H; subst
  end.
  erewrite size_under_conds_no_effect; eauto.
  erewrite IHszs; eauto.
Qed.

Lemma kv_under_conds_no_effect : forall {kv F f},
    debruijn_under_conds f (ks_of_fctx F) ->
    KindVarValid F kv ->
    subst.subst'_kindvar f kv = kv.
Proof.
  intros.
  unfold KindVarValid in *.
  destruct kv; simpl in *; auto; destructAll.
  - do 2 ltac:(erewrite quals_under_conds_no_effect; eauto).
  - do 2 ltac:(erewrite sizes_under_conds_no_effect; eauto).
  - erewrite size_under_conds_no_effect; eauto.
    erewrite qual_under_conds_no_effect; eauto.
Qed.

Ltac prove_ks_eq F :=
  unfold plus;
  unfold ks_of_fctx;
  apply FunctionalExtensionality.functional_extensionality;
  let knd := fresh "knd" in intro knd; destruct knd;
  destruct F; subst; simpl in *;
  unfold sing; simpl;
  try rewrite Nat.add_0_l; auto;
  try rewrite map_length; auto;
  try rewrite Nat.add_comm; auto.

Lemma kvs_under_conds_no_effect : forall {kvs F f},
    debruijn_under_conds f (ks_of_fctx F) ->
    KindVarsValid F kvs ->
    subst.subst'_kindvars f kvs = kvs.
Proof.
  induction kvs; simpl in *; auto.
  intros.
  match goal with
  | [ H : KindVarsValid _ _ |- _ ] => inversion H; subst
  end.
  erewrite kv_under_conds_no_effect; eauto.
  erewrite IHkvs; eauto.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all: unfold subst.under_kindvar'.
  all: simpl.
  all: eapply debruijn_under_change_ks.
  all: try eapply debruijn_under_under_knd; eauto.
  all: prove_ks_eq F.
Qed.

Lemma fold_right_ks_of_kvs : forall ks kvs,
    fold_right
      (fun kv ks' =>
         (debruijn.plus
            (debruijn.sing
               (subst.kind_of_kindvar kv)
               1)
            ks'))
      ks
      kvs
    =
    plus (ks_of_kvs kvs) ks.
Proof.
  induction kvs; simpl in *; auto.
  rewrite IHkvs.
  apply plus_assoc.
Qed.

Lemma ks_add_constraints : forall {kvs F},
    ks_of_fctx (add_constraints F kvs) =
    plus (ks_of_kvs kvs) (ks_of_fctx F).
Proof.
  induction kvs; intros; simpl in *; auto.
  rewrite IHkvs.
  match goal with
  | [ |- _ = plus (plus ?A ?B) _ ] =>
    rewrite (plus_comm A B)
  end.
  rewrite <-plus_assoc.
  match goal with
  | [ |- plus _ ?A = plus _ ?B ] =>
    replace B with A; auto
  end.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all: prove_ks_eq F.
Qed.  

Lemma TypesValid_under_conds_no_effect :
  (forall F t,
      TypeValid F t ->
      forall f,
        debruijn_under_conds f (ks_of_fctx F) ->
        subst.subst'_type f t = t) /\
  (forall F ht,
      HeapTypeValid F ht ->
      forall f,
        debruijn_under_conds f (ks_of_fctx F) ->
        subst.subst'_heaptype f ht = ht) /\
  (forall F atyp,
      ArrowTypeValid F atyp ->
      forall f,
        debruijn_under_conds f (ks_of_fctx F) ->
        subst.subst'_arrowtype f atyp = atyp) /\
  (forall F ft,
      FunTypeValid F ft ->
      forall f,
        debruijn_under_conds f (ks_of_fctx F) ->
        subst.subst'_funtype f ft = ft).
Proof.
  eapply TypesValid_ind'.
  all: intros; simpl in *.

  Ltac rw_under_qual :=
    erewrite qual_under_conds_no_effect; eauto.
  Ltac rw_under_loc :=
    erewrite loc_under_conds_no_effect; eauto.
  Ltac rw_under_size :=
    erewrite size_under_conds_no_effect; eauto.
  Ltac use_IH :=
    match goal with
    | [ H : context[_ = _] |- _ ] => rewrite H; auto
    end.
  Ltac use_Forall_IH :=
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H;
      specialize (H _ H'); rewrite H; auto
    end.

  - rw_under_qual.
  - rw_under_qual.
    unfold get_var'.
    match goal with
    | [ H : debruijn_under_conds _ _ |- _ ] =>
      erewrite H
    end.
    -- simpl.
       unfold zero; auto.
    -- unfold ks_of_fctx.
       rewrite <-nth_error_Some.
       match goal with
       | [ H : nth_error _ _ = Some _ |- _ ] =>
         rewrite H; solve_ineqs
       end.
  - rw_under_qual.
    match goal with
    | [ |- QualT _ (_ _ ?Q) = _ ] =>
      erewrite (qual_under_conds_no_effect (q:=Q)); eauto
    end.
    match goal with
    | [ H : forall _, _ -> _ = _ |- _ ] =>
      rewrite H; auto
    end.
    eapply debruijn_under_change_ks.
    -- eapply debruijn_under_under_knd; eauto.
    -- prove_ks_eq C.
  - rw_under_qual.
  - rw_under_qual.
    match goal with
    | [ |- context[map ?F ?TS] ] =>
      replace (map F TS) with TS; auto
    end.
    match goal with
    | [ |- ?A = _ ] => rewrite <-(map_id A) at 1
    end.
    apply map_ext_in.
    intros.
    use_Forall_IH.
  - rw_under_qual.
    use_IH.
  - rw_under_loc.
    rw_under_qual.
  - rw_under_loc.
    rw_under_qual.
    use_IH.
  - rw_under_loc.
    rw_under_qual.
    use_IH.
  - use_IH; [ rw_under_qual | ].
    eapply debruijn_under_change_ks.
    -- eapply debruijn_under_under_knd; eauto.
    -- prove_ks_eq C.
  - rw_under_loc.
    rw_under_qual.
  - match goal with
    | [ |- _ ?A = _ ?B ] =>
      replace B with A at 2; auto
    end.
    rewrite <-map_id.
    apply map_ext_in.
    intros.
    use_Forall_IH.
  - match goal with
    | [ |- _ ?A = _ ?B ] =>
      replace B with A at 2; auto
    end.
    rewrite <-map_id.
    apply map_ext_in.
    intros.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    match goal with
    | [ H : Forall _ _, H' : List.In _ _ |- _ ] =>
      rewrite Forall_forall in H; specialize (H _ H')
    end.
    destructAll.
    simpl in *.
    use_IH.
    rw_under_size.
  - use_IH.
  - rw_under_qual.
    rw_under_size.
    use_IH.
    eapply debruijn_under_change_ks.
    -- eapply debruijn_under_under_knd; eauto.
    -- prove_ks_eq C.
  - match goal with
    | [ |- Arrow ?A ?B = Arrow ?C ?D ] =>
      replace C with A at 2; [ replace D with B at 2; auto | ]
    end.
    all: rewrite <-map_id.
    all: apply map_ext_in.
    all: intros.
    all: use_Forall_IH.
  - erewrite kvs_under_conds_no_effect; eauto.
    use_IH.
    eapply debruijn_under_change_ks.
    -- eapply debruijn_under_under_kindvars; eauto.
    -- rewrite fold_right_ks_of_kvs.
       rewrite ks_add_constraints; auto.
Qed.  

Lemma TypeValid_empty_imp_value_closed : forall {F pt q},
    TypeValid F (QualT pt q) ->
    Function_Ctx_empty F ->
    value_closed subst.SPretype pt.
Proof.
  unfold value_closed.
  intros.
  specialize TypesValid_under_conds_no_effect.
  let H := fresh "H" in
  intro H; destruct H as [H];
    match goal with
    | [ H' : TypeValid _ _ |- _ _ ?F _ = _ ] =>
      specialize (H _ _ H' F)
    end.
  match goal with
  | [ H : ?A -> _ |- _ ] =>
    let H' := fresh "H" in
    assert (H' : A); [ | specialize (H H') ]
  end.
  { eapply debruijn_under_change_ks.
    - apply trivial_debruijn_under_conds.
    - unfold Function_Ctx_empty in *.
      destructAll.
      unfold zero.
      prove_ks_eq F; subst; auto. }
  simpl in *.
  match goal with
  | [ H : QualT _ _ = QualT _ _ |- _ ] =>
    inversion H
  end.
  match goal with
  | [ H : ?A = _ |- context[?A] ] => repeat rewrite H; auto
  end.
Qed.  

Lemma InstIndValid_value_closed : forall {idx kvs atyp F},
    Function_Ctx_empty F ->
    InstIndValid F (FunT kvs atyp) idx ->
    value_closed (knd_of_index idx) (obj_of_index idx).
Proof.
  unfold Function_Ctx_empty.
  intros.
  destructAll.
  destruct F; subst; simpl in *; subst; simpl in *.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] =>
    inversion H; subst; simpl in *
  end.
  - apply LocValid_zero_imp_value_closed; auto.
  - eapply TypeValid_empty_imp_value_closed; eauto.
    unfold Function_Ctx_empty; auto.
  - apply QualValid_empty_imp_value_closed; auto.
  - apply SizeValid_empty_imp_value_closed; auto.
Qed.

Lemma add_pr_to_msf_closed : forall {knd obj msf},
    msf_closed msf ->
    value_closed knd obj ->
    msf_closed (add_pr_to_msf knd obj msf).
Proof.
  unfold msf_closed.
  intros.
  destruct knd; destruct knd0; simpl in *.
  all:
    try match goal with
        | [ H : nth_error (_ :: _) ?IDX = Some _ |- _ ] =>
          destruct IDX; simpl in *;
            [ inversion H; subst; auto | ]
        end.
  all:
    match goal with
    | [ H : forall _ _ _, _ |- _ ] => eapply H; eauto
    end.
Qed.

Lemma msf_of_indices_snoc : forall idxs idx,
    msf_of_indices (idxs ++ [idx]) =
    add_index_to_msf idx (msf_of_indices idxs).
Proof.
  intros; unfold msf_of_indices; rewrite fold_left_snoc; auto.
Qed.

Lemma InstIndsValid_nth_error : forall {idx' idxs idx kvs atyp F},
    nth_error idxs idx' = Some idx ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    exists kvs' atyp',
      InstIndValid F (FunT kvs' atyp') idx.
Proof.
  induction idx'; intros; simpl in *; destruct idxs; simpl in *;
    match goal with
    | [ H : _ = Some _ |- _ ] =>
      inversion H; subst; simpl in *
    end;
    match goal with
    | [ X : ArrowType |- _ ] => destruct X
    end;
    match goal with
    | [ H : InstIndsValid _ _ (_ :: _) |- _ ] =>
      specialize (InstIndsValid_cons_inv H)
    end;
    intros; destructAll; eauto.
Qed.

Lemma InstIndsValid_In : forall {idxs idx kvs atyp F},
    List.In idx idxs ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    exists kvs' atyp',
      InstIndValid F (FunT kvs' atyp') idx.
Proof.
  intros.
  match goal with
  | [ H : List.In _ _ |- _ ] =>
    apply In_nth_error in H; destructAll
  end.
  eapply InstIndsValid_nth_error; eauto.
Qed.

Lemma InstIndsValid_msf_closed : forall {idxs kvs atyp F},
    Function_Ctx_empty F ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    msf_closed (msf_of_indices idxs).
Proof.
  apply
    (rev_ind
       (fun idxs =>
          forall kvs atyp F,
            Function_Ctx_empty F ->
            InstIndsValid F (FunT kvs atyp) idxs ->
            msf_closed (msf_of_indices idxs))).
  all: intros; simpl in *.
  - unfold msf_of_indices; simpl.
    apply empty_msf_closed.
  - match goal with
    | [ X : ArrowType |- _ ] => destruct X
    end.
    rewrite msf_of_indices_snoc.
    match goal with
    | [ H : InstIndsValid _ (FunT ?KVS _) _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : exists kvs' kv', KVS = kvs' ++ [kv'])
    end.
    { apply snoc_exists.
      eapply Nat.lt_le_trans;
        [ | eapply InstIndsValid_length_ineq; eauto ].
      rewrite snoc_length.
      apply Nat.lt_0_succ. }
    destructAll.
    match goal with
    | [ H : InstIndsValid _ _ (?L ++ [?IDX]) |- _ ] =>
      let H' := fresh "H" in
      assert (H' : List.In IDX (L ++ [IDX])) by apply in_snoc;
      specialize (InstIndsValid_In H' H)
    end.
    intros; destructAll.
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] =>
      apply InstIndsValid_remove_snoc in H
    end.
    match goal with
    | [ H : forall _ _ _, _,
        H' : Function_Ctx_empty _,
        H'' : InstIndsValid _ _ _ |- _ ] =>
      specialize (H _ _ _ H' H'')
    end.
    unfold add_index_to_msf.
    apply add_pr_to_msf_closed; auto.
    eapply InstIndValid_value_closed; eauto.
Qed.

Lemma add_pr_to_msf_merge_msfs_comm : forall {knd obj msf1 msf2},
    add_pr_to_msf
      knd obj
      (merge_msfs msf1 msf2)
    =
    merge_msfs
      (add_pr_to_msf knd obj msf1)
      msf2.
Proof.
  intros.
  apply FunctionalExtensionality.functional_extensionality_dep.
  destruct knd; simpl.
  all: intro knd'; destruct knd'; simpl.
  all: unfold merge_msfs; simpl; auto.
Qed.

Lemma msf_of_indices_cons : forall {idxs idx},
    msf_of_indices (idx :: idxs)
    =
    merge_msfs
      (msf_of_indices idxs)
      (add_index_to_msf idx empty_msf).
Proof.
  apply
    (rev_ind
       (fun idxs =>
          forall idx,
            msf_of_indices (idx :: idxs)
            =
            merge_msfs
              (msf_of_indices idxs)
              (add_index_to_msf idx empty_msf))).
  - intros; simpl in *.
    unfold msf_of_indices.
    simpl.
    apply FunctionalExtensionality.functional_extensionality_dep.
    intros.
    unfold merge_msfs.
    unfold empty_msf; simpl; auto.
  - intros.
    rewrite app_comm_cons.
    repeat rewrite msf_of_indices_snoc.
    match goal with
    | [ H : forall _, _ = _ |- _ ] => rewrite H
    end.
    unfold add_index_to_msf.
    apply add_pr_to_msf_merge_msfs_comm.
Qed.

Lemma subst_of_indices_multisubst : forall {idxs kvs atyp F},
    Function_Ctx_empty F ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    debruijn_multisubst_ext_conds
      (subst'_of (subst_of_indices idxs))
      debruijn.zero
      (msf_of_indices idxs).
Proof.
  induction idxs; intros; simpl; [ apply id_multisubst | ].
  rewrite <-subst'_of_comp.
  match goal with
  | [ X : ArrowType |- _ ] => destruct X
  end.
  match goal with
  | [ H : InstIndsValid _ _ (_ :: _) |- _ ] =>
    apply InstIndsValid_cons_inv in H
  end.
  destructAll.

  assert (H' : forall su ks msf msf', debruijn_multisubst_ext_conds su ks msf -> msf = msf' -> debruijn_multisubst_ext_conds su ks msf').
  { intros; subst; auto. }
  eapply H'.
  - eapply multisubst_comp.
    -- eapply subst_to_multisubst.
       apply idx_debruijn_subst_ext_conds.
    -- eauto.
    -- eapply InstIndsValid_msf_closed; eauto.
  - apply eq_sym.
    apply msf_of_indices_cons.
Qed.

Lemma debruijn_multisubst_ext_under_knd : forall {f ks msf knd},
    debruijn_multisubst_ext_conds f ks msf ->
    debruijn_multisubst_ext_conds
      (debruijn.under' knd f)
      (debruijn.plus (debruijn.sing knd 1) ks)
      msf.
Proof.
  intros.
  unfold debruijn_multisubst_ext_conds in *.
  destructAll.
  split; [ | split ]; intros; simpl.
  - unfold under'.
    unfold under_ks'.
    unfold var'.
    unfold var.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as b;
      generalize (eq_sym Heqb); case b; intros; auto
    end.
    match goal with
    | [ H : context[_ < _ -> _] |- _ ] => rewrite H
    end.
    2:{
      unfold plus in *.
      match goal with
      | [ |- _ - ?A < _ ] =>
        rewrite (Nat.add_lt_mono_r _ _ A)
      end.
      rewrite Nat.sub_add; [ | rewrite <-Nat.ltb_ge; auto ].
      rewrite Nat.add_comm; auto.
    }
    unfold plus.
    rewrite Nat.add_comm.
    rewrite <-Nat.add_sub_swap; [ | rewrite <-Nat.ltb_ge; auto ].
    rewrite <-Nat.add_sub_assoc; [ | apply le_plus_l ].
    match goal with
    | [ |- context[?A + ?B - _] ] =>
      rewrite (Nat.add_comm A B)
    end.
    rewrite Nat.add_sub.
    rewrite Nat.add_comm; auto.
  - unfold under'.
    unfold under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false
    end.
    2:{
      apply eq_sym.
      rewrite Nat.ltb_ge.
      eapply le_trans; [ | eauto ].
      unfold plus.
      apply le_plus_l.
    }
    unfold plus in *.
    rewrite Nat.sub_add_distr in *.
    match goal with
    | [ H : context[nth_error _ _ = Some _ -> _],
        H' : nth_error _ ?IDX = Some _ |- _ ] =>
      erewrite (H _ _ _ _ _ H')
    end.
    Unshelve.
    2:{
      match goal with
      | [ |- _ <= _ - ?A ] =>
        rewrite (Nat.add_le_mono_r _ _ A)
      end.
      rewrite Nat.sub_add; [ rewrite Nat.add_comm; auto | ].
      eapply le_trans; [ | eauto ].
      apply le_plus_l.
    }
    match goal with
    | [ |- _ _ (_ ?F) _ = _ _ (_ ?F2) _ ] =>
      replace F with F2; auto
    end.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    lia.
  - unfold under'.
    unfold under_ks'.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false
    end.
    2:{
      apply eq_sym.
      rewrite Nat.ltb_ge.
      eapply le_trans; [ | eauto ].
      unfold plus.
      apply le_plus_l.
    }
    unfold plus in *.
    rewrite Nat.sub_add_distr in *.
    match goal with
    | [ H : context[nth_error _ _ = None -> _],
        H' : nth_error _ ?IDX = None |- _ ] =>
      erewrite (H _ _ _ _ H')
    end.
    Unshelve.
    2:{
      match goal with
      | [ |- _ <= _ - ?A ] =>
        rewrite (Nat.add_le_mono_r _ _ A)
      end.
      rewrite Nat.sub_add; [ rewrite Nat.add_comm; auto | ].
      eapply le_trans; [ | eauto ].
      apply le_plus_l.
    }
    match goal with
    | [ |- _ _ (?A - _) = _ _ (?B - _) ] =>
      replace A with B; auto
    end.
    lia.
Qed.

Lemma debruijn_multisubst_ext_under_kindvars : forall {kvs f ks msf},
    debruijn_multisubst_ext_conds f ks msf ->
    debruijn_multisubst_ext_conds
      (subst.under_kindvars' kvs f)
      (fold_right
         (fun kv ks' =>
            (debruijn.plus
               (debruijn.sing
                  (subst.kind_of_kindvar kv)
                  1)
               ks'))
         ks
         kvs)
      msf.
Proof.
  induction kvs; simpl; auto.
  intros.
  specialize (IHkvs _ _ _ H).
  destruct a; simpl.
  all: unfold subst.under_kindvar'; simpl.
  all: apply debruijn_multisubst_ext_under_knd; auto.
Qed.

Definition ks_of_msf (msf : multisubst_func) :=
  fun knd => length (msf knd).

Lemma multisubst_comp_swapped : forall {ks msf1 msf2 f1 f2},
    msf_closed msf2 ->
    debruijn_multisubst_ext_conds f1 ks msf1 ->
    debruijn_multisubst_ext_conds
      f2 (plus (ks_of_msf msf1) ks) msf2 ->
    debruijn_multisubst_ext_conds
      (f1 ∘' f2) ks (merge_msfs msf1 msf2).
Proof.
  intros.
  unfold debruijn_multisubst_ext_conds in *.
  destructAll.
  split; [ | split ]; intros; simpl in *.
  - match goal with
    | [ H : context[_ < _ -> ?F _ _ _ = _]
        |- _ _ (?F _ _ _) = _ ] =>
      rewrite H
    end.
    2:{
      unfold plus.
      eapply lt_le_trans; eauto.
      apply le_plus_r.
    }
    destruct knd; simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false
      end.
    all:
      try match goal with
          | [ |- false = _ ] =>
            apply eq_sym; rewrite Nat.ltb_ge; apply le_plus_l
          end.

    all: rewrite minus_plus.
    all:
      match goal with
      | [ H : context[_ < _ -> ?F _ _ _ = _]
          |- ?F _ _ _ = _ ] =>
        rewrite H; auto
      end.
    all: simpl.
    all: unfold plus; unfold zero; simpl.
    all: rewrite Nat.add_0_r; auto.
  - unfold merge_msfs in *.
    match goal with
    | [ H : nth_error (?L ++ _) ?IDX = Some _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : IDX < length L \/ length L <= IDX) by apply Nat.lt_ge_cases;
      case H';
      let H'' := fresh "H" in
      intro H''
    end.
    -- match goal with
       | [ H : nth_error (?L ++ _) ?IDX = Some _,
           H' : ?IDX < _ |- _ ] =>
         rewrite (nth_error_app1 _ _ H') in H
       end.
       match goal with
       | [ H : context[_ < _ -> ?F _ _ _ = _]
           |- _ _ (?F _ _ _) = _ ] =>
         rewrite H
       end.
       2:{
         unfold plus.
         match goal with
         | [ |- ?A < _ + ?B ] =>
           rewrite <-(Nat.sub_add B A); auto
         end.
         rewrite <-Nat.add_lt_mono_r.
         unfold ks_of_msf; auto.
       }
       destruct knd; simpl.
       all: unfold get_var'.
       all: unfold under_ks'.
       all:
         match goal with
         | [ |- context[if ?B then _ else _] ] =>
           replace B with false
         end.
       all:
         try match goal with
             | [ |- false = _ ] =>
               apply eq_sym; rewrite Nat.ltb_ge; apply le_plus_l
             end.

       all: rewrite Nat.add_comm.
       all: rewrite Nat.add_sub.
       all:
         match goal with
         | [ H : context[nth_error (?F _) _ = Some _ -> _],
             H' : nth_error (?F _) _ = Some _ |- _ ] =>
           erewrite H; eauto
         end.
       all: simpl.
       all: rewrite plus_zero; auto.
    -- match goal with
       | [ H : nth_error (?L ++ _) ?IDX = Some _,
           H' : _ <= ?IDX |- _ ] =>
         rewrite (nth_error_app2 _ _ H') in H
       end.
       match goal with
       | [ H : context[nth_error (?F _) _ = Some _ -> _],
           H' : nth_error (?F _) _ = Some _ |- _ ] =>
         erewrite H; eauto
       end.
       2:{
         unfold plus.
         match goal with
         | [ |- _ + ?B <= ?A ] =>
           rewrite <-(Nat.sub_add B A); auto
         end.
         rewrite <-Nat.add_le_mono_r.
         unfold ks_of_msf; auto.
       }
       2:{
         unfold plus.
         rewrite Nat.add_comm.
         rewrite Nat.sub_add_distr.
         eauto.
       }

       match goal with
       | [ H : msf_closed _,
           H' : nth_error _ _ = Some _ |- _ ] =>
         repeat erewrite (H _ _ _ H'); auto
       end.
  - unfold merge_msfs in *.
    rewrite nth_error_None in *.
    rewrite app_length in *.
    match goal with
    | [ H : context[nth_error _ _ = None -> ?F _ _ _ = _]
        |- _ _ (?F _ _ _) = _ ] =>
      erewrite H; eauto
    end.
    2:{
      unfold plus.
      match goal with
      | [ |- _ + ?B <= ?A ] =>
        rewrite <-(Nat.sub_add B A); auto
      end.
      rewrite <-Nat.add_le_mono_r.
      unfold ks_of_msf.
      eapply le_trans; [ | eauto ].
      apply le_plus_l.
    }
    2:{
      rewrite nth_error_None.
      unfold plus.
      rewrite Nat.add_comm.
      rewrite Nat.sub_add_distr.
      unfold ks_of_msf.
      match goal with
      | [ |- ?A <= _ - _ - ?B ] =>
        rewrite <-(Nat.add_sub A B)
      end.
      apply Nat.sub_le_mono_r.
      rewrite Nat.add_comm; auto.
    }

    destruct knd; simpl.
    all: unfold get_var'.
    all: unfold under_ks'.
    all:
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        replace B with false
      end.
    all:
      try match goal with
          | [ |- false = _ ] =>
            apply eq_sym; rewrite Nat.ltb_ge;
            rewrite <-Nat.add_sub_assoc; [ apply le_plus_l | ]
          end.
    all:
      try match goal with
          | [ H : _ + _ <= _ - _ |- _ <= _ ] =>
            eapply le_trans; [ eapply le_trans; [ | exact H ] | ]
          end.
    all: try apply le_plus_r.
    all: try apply Nat.le_sub_l.

    all: rewrite <-Nat.sub_add_distr.
    all:
      match goal with
      | [ |- _ _ (_ - (?A + ?B)) _ = _ ] =>
        rewrite (Nat.add_comm A B)
      end.
    all: rewrite <-minus_plus_simpl_l_reverse.
    all:
      match goal with
      | [ H : context[nth_error _ _ = None -> ?F _ _ _ = _]
          |- ?F _ _ _ = _ ] =>
        erewrite H; eauto
      end.
    all:
      try match goal with
          | [ |- ?A <= _ - ?B ] =>
            rewrite <-(Nat.add_sub A B)
          end.
    all: try apply Nat.sub_le_mono_r.
    all:
      try match goal with
          | [ |- ?A + _ <= ?B ] =>
            rewrite <-(Nat.add_sub B A)
          end.
    all:
      try match goal with
          | [ |- _ <= ?A + ?B - _ ] =>
            rewrite (Nat.add_comm A B);
            rewrite <-Nat.add_sub_assoc; auto
          end.
    all: try rewrite <-Nat.add_le_mono_l.
    all: try ltac:(eapply le_trans; [ | eauto ]).
    all: try apply le_plus_r.

    all: try rewrite nth_error_None.
    all:
      try match goal with
          | [ |- _ <= _ ] =>
            rewrite <-Nat.sub_add_distr;
            rewrite Nat.add_comm;
            rewrite Nat.sub_add_distr
          end.
    all:
      try match goal with
          | [ |- ?A <= _ - _ - ?B ] =>
            rewrite <-(Nat.add_sub A B)
          end.
    all: try apply Nat.sub_le_mono_r; auto.

    all: simpl.
    all:
      match goal with
      | [ |- _ ?A = _ ?B ] =>
        replace B with A; auto
      end.
    all: unfold plus.
    all: unfold zero.
    all: rewrite Nat.add_0_r.
    all: rewrite Nat.add_sub_assoc.
    all:
      try match goal with
          | [ H : _ + _ <= _ - _ |- _ ] =>
            eapply le_trans; [ eapply le_trans; [ | exact H ] | ]
          end.
    all: try apply le_plus_r.
    all: try apply Nat.le_sub_l.
    all: rewrite <-Nat.sub_add_distr.
    all:
      match goal with
      | [ |- _ - (?A + ?B) = _ ] =>
        rewrite (Nat.add_comm A B); auto
      end.
Qed.

Lemma debruijn_multisubst_ext_conds_determinate : forall {f1 f2 ks msf},
    debruijn_multisubst_ext_conds f1 ks msf ->
    debruijn_multisubst_ext_conds f2 ks msf ->
    f1 = f2.
Proof.
  intros.
  unfold debruijn_multisubst_ext_conds in *.
  destructAll.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  match goal with
  | [ H' : context[_ < ?KS _] |- _ ?KND ?V _ = _ ] =>
    let H := fresh "H" in
    assert (H : V < KS KND \/ KS KND <= V) by apply Nat.lt_ge_cases;
    case H; intros
  end.
  - match goal with
    | [ H : context[_ < _ -> _], H' : context[_ < _ -> _] |- _ ] =>
      rewrite H; auto; rewrite H'; auto
    end.
  - match goal with
    | [ H : context[nth_error (?MSF _) (_ - ?KS _)]
        |- _ ?KND ?V _ = _ ] =>
      remember (nth_error (MSF KND) (V - KS KND)) as obj;
      generalize (eq_sym Heqobj); case obj; intros
    end.
    -- match goal with
       | [ H : context[nth_error _ _ = Some _ -> _],
           H' : context[nth_error _ _ = Some _ -> _] |- _ ] =>
         erewrite H; eauto; erewrite H'; eauto
       end.
    -- match goal with
       | [ H : context[nth_error _ _ = None -> _],
           H' : context[nth_error _ _ = None -> _] |- _ ] =>
         erewrite H; eauto; erewrite H'; eauto
       end.
Qed.

Lemma ks_of_msf_merge_msfs : forall {ks1 ks2},
    ks_of_msf (merge_msfs ks1 ks2)
    =
    plus (ks_of_msf ks1) (ks_of_msf ks2).
Proof.
  intros.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  unfold merge_msfs.
  unfold ks_of_msf.
  rewrite app_length.
  unfold plus; auto.
Qed.

Lemma subst_kindvars_does_not_change_ks : forall {kvs su},
    ks_of_kvs (subst.subst'_kindvars su kvs) =
    ks_of_kvs kvs.
Proof.
  induction kvs; simpl in *; auto.
  intros.
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end.
  all: simpl.
  all: rewrite IHkvs; auto.
Qed.

Lemma InstInds_ks_of_kvs : forall {idxs kvs atyp kvs' atyp'},
    InstInds (FunT kvs atyp) idxs = Some (FunT kvs' atyp') ->
    ks_of_kvs kvs
    =
    plus (ks_of_msf (msf_of_indices idxs)) (ks_of_kvs kvs').
Proof.
  induction idxs; intros; simpl in *.
  - unfold msf_of_indices.
    simpl.
    unfold ks_of_msf.
    simpl.
    rewrite plus_id.
    unfold InstInds in *.
    simpl in *.
    match goal with
    | [ H : Some _ = Some _ |- _ ] =>
      inversion H; subst; auto
    end.
  - rewrite msf_of_indices_cons.
    rewrite ks_of_msf_merge_msfs.
    repeat match goal with
           | [ X : ArrowType |- _ ] => destruct X
           end.
    match goal with
    | [ H : InstInds _ (_ :: _) = Some _ |- _ ] =>
      apply InstInds_cons_inv in H
    end.
    destructAll.
    match goal with
    | [ H : InstInd (FunT ?KVS _) _ = Some _ |- _ ] =>
      destruct KVS; [ simpl in *; inversion H | ]
    end.
    match goal with
    | [ H : InstInd (FunT (?KV :: _) _) ?IDX = Some _ |- _ ] =>
      destruct KV; destruct IDX; simpl in *;
      inversion H; subst; simpl in *; clear H
    end.
    all:
      match goal with
      | [ H : forall _ _ _ _, _,
          H' : InstInds _ _ = Some _ |- _ ] =>
        specialize (H _ _ _ _ H');
        rewrite subst_kindvars_does_not_change_ks in H;
        rewrite H
      end.
    all: rewrite plus_assoc.
    all:
      match goal with
      | [ |- plus (plus ?A ?B) _ = _ ] =>
        rewrite (plus_comm A B)
      end.
    all:
      match goal with
      | [ |- plus (plus _ ?A) _ = plus (plus _ ?B) _ ] =>
        replace B with A; auto
      end.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: let knd := fresh "knd" in intro knd; destruct knd.
    all: auto.
Qed.    

Lemma subst_of_indices_commute_gen : forall {idxs kvs kvs' idx atyp atyp' F kvs'' atyp''},
    Function_Ctx_empty F ->
    InstIndsValid F (FunT kvs atyp) idxs ->
    InstInds (FunT kvs atyp) idxs = Some (FunT kvs' atyp') ->
    InstIndValid F (FunT kvs'' atyp'') idx ->
    subst.under_kindvars'
      kvs'
      (subst'_of (subst_of_indices idxs))
      ∘'
      subst.under_kindvars'
      kvs
      (subst'_of (subst_of_index idx))
    =
    subst.under_kindvars'
      kvs'
      (subst'_of (subst_of_index idx ∘ subst_of_indices idxs)).
Proof.
  intros.
  eapply debruijn_multisubst_ext_conds_determinate.
  - eapply multisubst_comp_swapped.
    -- eapply add_pr_to_msf_closed.
       --- apply empty_msf_closed.
       --- eapply InstIndValid_value_closed; eauto.
    -- eapply debruijn_multisubst_ext_under_kindvars.
       eapply subst_of_indices_multisubst; eauto.
    -- erewrite <-InstInds_ks_of_kvs; eauto.
       apply debruijn_multisubst_ext_under_kindvars.
       apply subst_to_multisubst.
       apply idx_debruijn_subst_ext_conds.
  - apply debruijn_multisubst_ext_under_kindvars.
    rewrite <-subst'_of_comp.
    apply multisubst_comp.
    -- apply subst_to_multisubst.
       apply idx_debruijn_subst_ext_conds.
    -- eapply subst_of_indices_multisubst; eauto.
    -- eapply InstIndsValid_msf_closed; eauto.
Qed.

Lemma subst_ext_subst_of_index : forall {idx} {A : Type} {H : @BindExt Ind Kind VarKind BindVar_rwasm BindRWasm A} {q : A},
    subst.subst_index idx q =
    subst_ext' (subst'_of (subst_of_index idx)) q.
Proof.
  intros.
  destruct idx.
  all: simpl.
  all: unfold subst_ext; auto.
Qed.

Lemma subst_ext_subst_of_indices : forall {idxs} {A : Type} {H : @BindExt Ind Kind VarKind BindVar_rwasm BindRWasm A} {q : A},
    subst.subst_indices idxs q =
    subst_ext' (subst'_of (subst_of_indices idxs)) q.
Proof.
  induction idxs; simpl in *.
  - intros.
    rewrite id_eq_var'.
    rewrite subst_ext'_var_e; auto.
  - intros.
    match goal with
    | [ X : Index |- _ ] => destruct X
    end.
    all: simpl.
    all: rewrite IHidxs.
    all:
      match goal with
      | [ |- ?F ?A ?B = _ ] =>
        replace (F A B) with (subst_ext' (subst'_of A) B)
      end.
    all: unfold subst_ext; auto.
    all: rewrite subst_ext'_assoc.
    all: simpl.
    all: rewrite subst'_of_comp; auto.
Qed.

Definition shift_down_after_eq
           (v : nat)
           (kspec : nat)
           (kspec' : nat) :=
  if v <=? kspec
  then kspec' + v
  else kspec' + v - 1.

Definition InstFunctionCtxInd_under_ks
           (F : Function_Ctx)
           (ks : Ind -> nat)
           (idx : Index) :=
  match idx with
  | LocI loc =>
    subst_ext'
      (under_ks'
         ks (subst'_of (ext SLoc loc id)))
      (update_location_ctx
         (shift_down_after_eq (location F) (ks SLoc) 0)
         F)
  | SizeI sz =>
    subst_ext'
      (under_ks'
         ks (subst'_of (ext SSize sz id)))
      (update_size_ctx
         (remove_nth (size F) (ks SSize)) F)
  | QualI q =>
    subst_ext'
      (under_ks'
         ks (subst'_of (ext SQual q id)))
      (update_qual_ctx
         (remove_nth (qual F) (ks SQual)) F)
  | PretypeI pt =>
    subst_ext'
      (under_ks'
         ks (subst'_of (ext SPretype pt id)))
      (update_type_ctx
         (remove_nth (type F) (ks SPretype)) F)
  end.

Lemma InstFunctionCtxInd_under_empty_ks : forall {F F' idx},
    InstFunctionCtxInd F idx = Some F' ->
    InstFunctionCtxInd_under_ks F zero idx = F'.
Proof.
  intros.
  destruct idx; simpl in *.
  
  Ltac handle_list_subgoal obj Heqobj :=
    unfold zero;
    match goal with
    | [ |- context[remove_nth ?A _] ] =>
      remember A as obj; generalize (eq_sym Heqobj);
      case obj; intros; subst
    end;
    match goal with
    | [ H : ?A = _, H' : context[?A] |- _ ] =>
      rewrite H in H'
    end;
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end;
    simpl; 
    rewrite under_ks'_zero; auto.
  
  - unfold shift_down_after_eq.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false
    end.
    2:{
      unfold zero.
      simpl.
      apply eq_sym.
      rewrite Nat.leb_gt.
      destruct (location F); try lia.
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
    }
    remember (location F) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros; subst.
    all:
      match goal with
      | [ H : ?A = _, H' : context[?A] |- _ ] =>
        rewrite H in H'
      end.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite under_ks'_zero.
    auto.
  - handle_list_subgoal obj Heqobj.
  - handle_list_subgoal obj Heqobj.
  - handle_list_subgoal obj Heqobj.
Qed.

Definition kind_of_index idx :=
  match idx with
  | LocI _ => SLoc
  | QualI _ => SQual
  | SizeI _ => SSize
  | PretypeI _ => SPretype
  end.

Definition ks_of_idxs idxs :=
  fold_right
    (fun idx acc => plus (sing (kind_of_index idx) 1) acc)
    zero
    idxs.

Lemma shift_down_after_eq_S : forall {n1 n2},
    shift_down_after_eq (Datatypes.S n1) (Datatypes.S n2) 0 =
    Datatypes.S (shift_down_after_eq n1 n2 0).
Proof.
  intros.
  unfold shift_down_after_eq.
  simpl.
  match goal with
  | [ |- _ = Datatypes.S (if ?B then _ else _) ] =>
    remember B as b; generalize (eq_sym Heqb);
    case b; intros; subst; simpl; auto
  end.
  rewrite Nat.leb_gt in *.
  lia.
Qed.

Lemma label_comp : forall {label su su'},
    map
      (fun '(ts, lctx) =>
         (subst'_types su ts,
          subst'_local_ctx su lctx))
      (map
         (fun '(ts, lctx) =>
            (subst'_types su' ts,
             subst'_local_ctx su' lctx)) label) =
    map
      (fun '(ts, lctx) =>
         (subst'_types (su ∘' su') ts,
          subst'_local_ctx (su ∘' su') lctx))
      label.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.label
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_label_ctx label empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma ret_comp : forall {ret su su'},
    option_map
      (subst'_types su)
      (option_map
         (subst'_types su')
         ret)
    =
    option_map (subst'_types (su ∘' su')) ret.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.ret
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_ret_ctx ret empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma qual_comp : forall {qual su su'},
    map
      (fun '(qs1, qs2) =>
         (subst'_quals su qs1,
          subst'_quals su qs2))
      (map
         (fun '(qs1, qs2) =>
            (subst'_quals su' qs1,
             subst'_quals su' qs2))
         qual) =
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (su ∘' su') qs1,
          subst'_quals (su ∘' su') qs2))
      qual.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.qual
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_qual_ctx qual empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma size_comp : forall {size su su'},
    map
      (fun '(ss1, ss2) =>
         (subst'_sizes su ss1,
          subst'_sizes su ss2))
      (map
         (fun '(ss1, ss2) =>
            (subst'_sizes su' ss1,
             subst'_sizes su' ss2))
         size)
    =
    map
      (fun '(ss1, ss2) =>
         (subst'_sizes (su ∘' su') ss1,
          subst'_sizes (su ∘' su') ss2))
      size.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.size
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_size_ctx size empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma type_comp : forall {type : list (Size * Qual * HeapableConstant)} {su su'},
    map
      (fun '(s, q, hc) =>
         (subst'_size su s,
          subst'_qual su q, hc))
      (map
         (fun '(s, q, hc) =>
            (subst'_size su' s,
             subst'_qual su' q, hc))
         type)
    =
    map
      (fun '(s, q, hc) =>
         (subst'_size (su ∘' su') s,
          subst'_qual (su ∘' su') q, hc))
      type.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.type
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_type_ctx type empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma linear_comp : forall {linear su su'},
    pmap (subst'_qual su)
         (pmap (subst'_qual su') linear)
    =
    pmap (subst'_qual (su ∘' su')) linear.
Proof.
  intros.
  match goal with
  | [ |- ?A = _ ] =>
    replace A with
        (typing.linear
           (subst_ext'
              su
              (subst_ext'
                 su'
                 (update_linear_ctx linear empty_Function_Ctx))))
  end.
  2:{ simpl; auto. }
  rewrite subst_ext'_assoc.
  simpl; auto.
Qed.

Lemma sing_knd_eq : forall knd c,
    sing knd c knd = c.
Proof.
  destruct knd; simpl in *; auto.
Qed.

Lemma sing_knd_neq : forall {knd knd'} c,
    knd <> knd' ->
    sing knd c knd' = 0.
Proof.
  destruct knd; destruct knd'; simpl in *; auto; intros; solve_impossibles.
Qed.

Lemma ltb_zero : forall x,
    x <? 0 = false.
Proof.
  intros.
  rewrite Nat.ltb_ge.
  lia.
Qed.

Lemma ltb_plus : forall x y,
    x + y <? x = false.
Proof.
  intros.
  rewrite Nat.ltb_ge.
  lia.
Qed.

Lemma ltb_zero_one_plus : forall c,
    0 <? 1 + c = true.
Proof.
  intros.
  rewrite Nat.ltb_lt.
  lia.
Qed.

Lemma ltb_refl : forall c,
    c <? c = false.
Proof.
  intros.
  rewrite Nat.ltb_ge.
  lia.
Qed.

Lemma subst'_rwasm_VarKind : forall knd su c,
    subst'_rwasm knd su (VarKind knd c) = su knd c zero.
Proof.
  destruct knd; simpl; unfold get_var'; auto.
Qed.

Ltac handle_ltb :=
  let obj := fresh "obj" in
  let Heqobj := fresh "Heqobj" in
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
    remember B as obj; generalize (eq_sym Heqobj);
    case obj; intros;
    match goal with
    | [ H : B = _, H' : _ = B |- _ ] =>
      rewrite H in H'
    end;
    repeat rewrite Nat.ltb_lt in *;
    repeat rewrite Nat.ltb_ge in *
  end.

Ltac solve_shift_down_after_lem :=
  intros;
  unfold shift_down_after;
  handle_ltb;
  repeat rewrite Nat.ltb_lt in *;
  repeat rewrite Nat.ltb_ge in *;
  lia.

Lemma shift_down_after_ltb_kspec' : forall v kspec kspec',
    v <> kspec ->
    shift_down_after v kspec kspec' <? kspec' = false.
Proof.
  solve_shift_down_after_lem.
Qed.

Lemma shift_down_after_minus_kspec' : forall v kspec kspec',
    shift_down_after v kspec kspec' - kspec' =
    shift_down_after v kspec 0.
Proof.
  solve_shift_down_after_lem.
Qed.

Lemma shift_down_after_to_plus_kspec' : forall v kspec kspec',
    v <> kspec ->
    shift_down_after v kspec kspec' =
    shift_down_after v kspec 0 + kspec'.
Proof.
  solve_shift_down_after_lem.
Qed.

Lemma shift_down_after_stays_lt : forall {v thresh kspec},
    v <> thresh ->
    v <> kspec ->
    thresh < kspec ->
    shift_down_after v kspec 0 <> thresh.
Proof.
  solve_shift_down_after_lem.
Qed.

Lemma shift_down_after_after_lt : forall {v thresh kspec},
    v <> 1 + thresh ->
    v <> kspec ->
    kspec < 1 + thresh ->
    shift_down_after v kspec 0 <> thresh.
Proof.
  solve_shift_down_after_lem.
Qed.

Lemma shift_down_after_comm : forall {v c1 c2 c3},
    v <> c2 ->
    v <> 1 + c1 ->
    c2 < 1 + c1 ->
    shift_down_after
      (shift_down_after v (1 + c1) 0)
      c2
      c3
    =
    shift_down_after
      (shift_down_after v c2 0)
      c1
      c3.
Proof.
  intros.
  unfold shift_down_after.
  repeat handle_ltb; subst; lia.
Qed.

Lemma debruijn_subst_comm : forall {f1 f2 f3 f4 ks knd knd' obj obj'},
    value_closed knd obj ->
    value_closed knd' obj' ->
    debruijn_subst_ext_conds f1 zero knd obj ->
    debruijn_subst_ext_conds f2 (plus (sing knd 1) ks) knd' obj' ->
    debruijn_subst_ext_conds f3 ks knd' obj' ->
    debruijn_subst_ext_conds f4 zero knd obj ->
    f1 ∘' f2 = f3 ∘' f4.
Proof.
  intros.
  unfold Subst'.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  unfold debruijn_subst_ext_conds in *.
  simpl.
  destructAll.
  Ltac apply_knd_case :=
    match goal with
    | [ H : context[_ <> ?A -> ?F _ _ _ = _] |- context[?F ?K _ _] ] =>
      let H' := fresh "H" in
      assert (H' : K = A \/ K <> A) by apply eq_dec_ind;
      case H'; intros; subst;
      [ match goal with
        | [ H : forall _, F _ ?N _ = _ |- context[F _ ?N2 _] ] =>
          let H'' := fresh "H" in
          assert (H'' : N2 = N \/ N2 <> N) by apply eq_dec_nat;
          case H''; intros;
          [ match goal with
            | [ H''' : N2 = N |- _ ] =>
              rewrite <-H''' in H; rewrite H
            end |
            match goal with
            | [ H : context[_ <> N -> F _ _ _ = _] |- _ ] =>
              rewrite H; auto
            end ]
        end
        | rewrite H; auto ]
    end.
  
  repeat apply_knd_case.
  all: unfold plus in *; unfold zero in *; simpl in *.
  
  Ltac rw_value_closed :=
    match goal with
    | [ H : value_closed _ ?O
        |- context[subst'_rwasm _ _ ?O] ] =>
      rewrite H
    end.
  Ltac rw_under_ks_hit_subst :=
    unfold under_ks';
    rewrite ltb_plus;
    rewrite minus_plus;
    rewrite plus_zero;
    match goal with
    | [ H : context[?F ?A ?B _] |- context[?F ?A ?B _] ] =>
      rewrite H
    end;
    rw_value_closed; auto.
  
  - rewrite sing_knd_eq in *; lia.
  - rewrite sing_knd_eq in *.
    repeat rw_value_closed.
    unfold shift_down_after.
    rewrite ltb_zero.
    simpl.
    rewrite <-Nat.add_sub_assoc by lia.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite subst'_rwasm_VarKind.
    rw_under_ks_hit_subst.
  - repeat rw_value_closed.
    rewrite sing_knd_neq; auto.
    simpl.
    rewrite subst'_rwasm_VarKind.
    rw_under_ks_hit_subst.
  - repeat rw_value_closed.
    rewrite subst'_rwasm_VarKind.
    rewrite sing_knd_eq in *.
    subst.
    unfold shift_down_after.
    rewrite ltb_zero_one_plus.
    rewrite Nat.add_0_r; auto.
    unfold under_ks'.
    rewrite ltb_refl.
    rewrite Nat.sub_diag.
    rewrite plus_zero.
    match goal with
    | [ H : context[?F ?A ?B _] |- context[?F ?A ?B _] ] =>
      rewrite H
    end.
    rw_value_closed; auto.
  - repeat rewrite subst'_rwasm_VarKind.
    rewrite sing_knd_eq in *.
    unfold under_ks'.
    repeat rewrite shift_down_after_ltb_kspec'; auto.
    rewrite plus_zero.
    repeat rewrite shift_down_after_minus_kspec'.
    match goal with
    | [ H : forall _ _, _ <> _ -> ?F _ _ _ = _ |- ?F _ _ _ = _ ] =>
      rewrite H; [ | apply shift_down_after_stays_lt; lia ]
    end.
    match goal with
    | [ H : forall _ _, _ <> _ -> ?F _ _ _ = _ |- _ = ?F _ _ _ ] =>
      rewrite H; [ | apply shift_down_after_after_lt; lia ]
    end.
    rewrite shift_down_after_comm by lia; auto.
  - rewrite sing_knd_neq in *; auto.
    simpl in *.
    repeat rewrite subst'_rwasm_VarKind.
    unfold under_ks'.
    rewrite shift_down_after_ltb_kspec'; auto.
    rewrite ltb_plus.
    rewrite minus_plus.
    rewrite shift_down_after_minus_kspec'.
    rewrite plus_zero.
    match goal with
    | [ H : context[_ <> _ -> ?F _ _ _ = _] |- ?F _ _ _ = _ ] =>
      rewrite H; auto
    end.
    match goal with
    | [ H : context[_ <> _ _ -> ?F _ _ _ = _] |- _ = ?F _ _ _ ] =>
      rewrite H; auto
    end.
    rewrite Nat.add_comm.
    rewrite <-shift_down_after_to_plus_kspec' by lia.
    auto.
  - repeat rw_value_closed.
    rewrite subst'_rwasm_VarKind.
    subst.
    rewrite Nat.add_0_r.
    unfold under_ks'.
    rewrite ltb_refl.
    rewrite Nat.sub_diag.
    match goal with
    | [ H : context[?F ?A ?B _] |- context[?F ?A ?B _] ] =>
      rewrite H
    end.
    rw_value_closed; auto.
  - repeat rewrite subst'_rwasm_VarKind.
    unfold under_ks'.
    rewrite ltb_plus.
    rewrite shift_down_after_ltb_kspec'; auto.
    rewrite shift_down_after_minus_kspec'.
    match goal with
    | [ H : context[_ <> _ -> ?F _ _ _ = _] |- _ = ?F _ _ _ ] =>
      rewrite H; auto
    end.
    rewrite minus_plus.
    rewrite plus_zero.
    match goal with
    | [ H : forall _ _, _ <> _ -> ?F _ _ _ = _ |- ?F _ _ _ = _ ] =>
      rewrite H; auto
    end.
    rewrite shift_down_after_to_plus_kspec' by lia.
    rewrite Nat.add_comm; auto.
  - repeat rewrite subst'_rwasm_VarKind.
    unfold under_ks'.
    rewrite ltb_plus.
    repeat match goal with
           | [ H : context[_ <> _ -> ?F _ _ _ = _] |- context[?F _ _ _] ] =>
             rewrite H; auto
           end.
Qed.

Lemma debruijn_subst_under_ks : forall {ks su ks' knd obj},
    debruijn_subst_ext_conds su ks knd obj ->
    debruijn_subst_ext_conds
      (under_ks' ks' su)
      (plus ks' ks)
      knd
      obj.
Proof.
  intros.
  unfold debruijn_subst_ext_conds in *.
  destructAll.
  split; [ | split ].
  - intros.
    unfold under_ks'.
    unfold plus.
    rewrite ltb_plus.
    rewrite minus_plus.
    match goal with
    | [ H : context[?F ?A ?B _] |- context[?F ?A ?B _] ] =>
      rewrite H
    end.
    match goal with
    | [ |- _ _ (weaks' ?F) _ = _ _ (weaks' ?F2) _ ] =>
      replace F2 with F; auto
    end.
    unfold plus.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    lia.
  - unfold plus.
    intros.
    unfold under_ks'.
    unfold shift_down_after.
    unfold var'.
    unfold var.
    match goal with
    | [ |- (if ?B then _ else _) = _ ] =>
      remember B as obj'; generalize (eq_sym Heqobj');
      case obj'; intros; subst
    end.
    -- match goal with
       | [ |- context[if ?B then _ else _] ] =>
         replace B with true; auto
       end.
       apply eq_sym.
       rewrite Nat.ltb_lt in *.
       lia.
    -- rewrite Nat.ltb_ge in *.
       match goal with
       | [ H : context[_ <> _ _ -> _] |- _ ] => rewrite H; [ | lia ]
       end.
       unfold shift_down_after.
       unfold plus.
       match goal with
       | [ |- ?A ?B ?C = ?A ?B ?D ] =>
         replace D with C; auto
       end.
       match goal with
       | [ |- (if ?B then _ else _) = _ ] =>
         remember B as obj2; generalize (eq_sym Heqobj2);
         case obj2; intros; subst
       end.
       --- match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with true; [ lia | ]
           end.
           apply eq_sym.
           rewrite Nat.ltb_lt in *.
           lia.
       --- match goal with
           | [ |- context[if ?B then _ else _] ] =>
             replace B with false; [ lia | ]
           end.
           apply eq_sym.
           rewrite Nat.ltb_ge in *.
           lia.
  - intros.
    unfold under_ks'.
    match goal with
    | [ |- (if ?B then _ else _) = _ ] =>
      remember B as obj'; generalize (eq_sym Heqobj');
      case obj'; intros; subst
    end.
    -- unfold var'.
       unfold var.
       auto.
    -- rewrite Nat.ltb_ge in *.
       match goal with
       | [ H : context[_ <> _ -> ?F _ _ _] |- context[?F _ _ _] ] =>
         rewrite H; auto
       end.
       unfold plus.
       match goal with
       | [ |- ?A ?B ?C = ?A ?B ?D ] =>
         replace D with C; auto
       end.
       lia.
Qed.

Lemma debruijn_subst_comm_simpl : forall {ks knd knd' obj obj'},
    value_closed knd obj ->
    value_closed knd' obj' ->
    ((subst'_of
        (ext knd obj id))
       ∘'
       under_ks'
       (plus (sing knd 1) ks)
       (subst'_of (ext knd' obj' id)))
    =
    ((under_ks'
        ks
        (subst'_of (ext knd' obj' id)))
       ∘'
       (subst'_of
          (ext knd obj id))).
Proof.
  intros.
  erewrite debruijn_subst_comm.
  - eauto.
  - shelve.
  - shelve.
  - apply simpl_debruijn_subst_ext_conds.
  - match goal with
    | [ |- debruijn_subst_ext_conds ?F ?A ?B ?C ] =>
      replace (debruijn_subst_ext_conds F A B C)
        with (debruijn_subst_ext_conds F (plus A zero) B C)
    end.
    2:{ rewrite plus_zero; auto. }
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  - match goal with
    | [ |- debruijn_subst_ext_conds ?F ?A ?B ?C ] =>
      replace (debruijn_subst_ext_conds F A B C)
        with (debruijn_subst_ext_conds F (plus A zero) B C)
    end.
    2:{ rewrite plus_zero; auto. }
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  - apply simpl_debruijn_subst_ext_conds.

  Unshelve.
  all: auto.
Qed.

Definition index_closed (idx : Index) :=
  match idx with
  | LocI l => value_closed SLoc l
  | SizeI sz => value_closed SSize sz
  | QualI q => value_closed SQual q
  | PretypeI pt => value_closed SPretype pt
  end.

Lemma some_inv : forall {A} {a b : A},
    a = b ->
    Some a = Some b.
Proof.
  intros; subst; auto.
Qed.

Lemma InstFunctionCtxInd_comm : forall {idx F F' idx' ks},
    index_closed idx ->
    index_closed idx' ->
    InstFunctionCtxInd F idx = Some F' ->
    InstFunctionCtxInd
      (InstFunctionCtxInd_under_ks
         F
         (plus (sing (kind_of_index idx) 1) ks) idx') idx =
    Some (InstFunctionCtxInd_under_ks F' ks idx').
Proof.
  intros.
  destruct F; destruct idx; simpl in *.
  1: destruct location.
  3: destruct size.
  5: destruct qual.
  7: destruct type.
  all:
    match goal with
    | [ H : _ = Some _ |- _ ] => inv H
    end.

  Ltac apply_comm_tactics :=
    unfold subst'_function_ctx; simpl;
    repeat rewrite label_comp;
    repeat rewrite ret_comp;
    repeat rewrite qual_comp;
    repeat rewrite size_comp;
    repeat rewrite type_comp;
    repeat rewrite linear_comp;
    rewrite debruijn_subst_comm_simpl; auto.

  all: destruct idx'; simpl in *.
  all: try now ltac:(rewrite remove_nth_map; apply_comm_tactics).
  1:{
    match goal with
    | [ |- context[plus ?A ?B ?C] ] =>
      replace (plus A B C) with (Datatypes.S (B C)) by auto
    end.
    rewrite shift_down_after_eq_S; simpl.
    apply_comm_tactics.
  }
  all:
    match goal with
    | [ |- context[plus ?A ?B ?C] ] =>
      replace (plus A B C) with (B C) by auto
    end.
  all: apply_comm_tactics.
Qed.

Lemma InstFunctionCtxInds_comm : forall {idxs ks idx F F'},
    InstFunctionCtxInds F idxs = Some F' ->
    Forall index_closed idxs ->
    index_closed idx ->
    InstFunctionCtxInds (InstFunctionCtxInd_under_ks F (plus (ks_of_idxs idxs) ks) idx) idxs =
    Some (InstFunctionCtxInd_under_ks F' ks idx).
Proof.
  induction idxs.
  - intros; simpl in *.
    rewrite plus_id.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H; auto
    end.
  - intros.
    simpl in *.
    match goal with
    | [ |- context[plus (plus ?A ?B) _] ] =>
      rewrite (plus_comm A B)
    end.
    rewrite <-plus_assoc.
    match goal with
    | [ H : context[InstFunctionCtxInds ?F ?IDXS] |- _ ] =>
      remember (InstFunctionCtxInds F IDXS) as obj;
      generalize (eq_sym Heqobj); case obj; intros; subst
    end.
    all:
      match goal with
      | [ H : ?A = _, H' : context[?A] |- _ ] =>
        rewrite H in H'
      end.
    2:{
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
    }
    match goal with
    | [ H : Forall _ (_ :: _) |- _ ] => inv H
    end.
    erewrite IHidxs; eauto.
    eapply InstFunctionCtxInd_comm; eauto.
Qed.

Lemma under_kindvars'_to_under_ks' : forall {kvs su},
    under_kindvars' kvs su =
    under_ks' (ks_of_kvs kvs) su.
Proof.
  induction kvs; intros; simpl; auto.
  - rewrite under_ks'_zero; auto.
  - unfold under_kindvar'.
    unfold under'.
    rewrite IHkvs.
    unfold under_ks'.
    unfold Subst'.
    apply FunctionalExtensionality.functional_extensionality_dep.
    intros.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    unfold plus.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      remember B as obj; generalize (eq_sym Heqobj); case obj; intros
    end.
    -- match goal with
       | [ |- context[if ?B then _ else _] ] =>
         remember B as obj2; generalize (eq_sym Heqobj2); case obj2; intros; auto
       end.
       rewrite Nat.ltb_lt in *.
       rewrite Nat.ltb_ge in *.
       lia.
    -- match goal with
       | [ |- context[if ?B then _ else _] ] =>
         remember B as obj2; generalize (eq_sym Heqobj2); case obj2; intros
       end.
       --- match goal with
	       | [ |- context[if ?B then _ else _] ] =>
             replace B with true
           end.
           2:{
             apply eq_sym.
             rewrite Nat.ltb_lt in *.
             rewrite Nat.ltb_ge in *.
             lia.
           }
           unfold var'.
           match goal with
           | [ |- _ _ ?A = _ _ ?B ] => replace B with A; auto
           end.
           rewrite Nat.ltb_lt in *.
           rewrite Nat.ltb_ge in *.
           lia.
       --- match goal with
	       | [ |- context[if ?B then _ else _] ] =>
             replace B with false
           end.
           2:{
             apply eq_sym.
             rewrite Nat.ltb_ge in *.
             lia.
           }
           rewrite OrdersEx.Nat_as_DT.sub_add_distr.
           match goal with
           | [ |- _ _ _ ?A = _ _ _ ?B ] =>
             replace B with A; auto
           end.
           apply FunctionalExtensionality.functional_extensionality.
           intros.
           lia.
Qed.

Inductive InstIndValid_at : Function_Ctx -> (Ind -> nat) -> Index -> Prop :=
| InstIndValidLoc_at_None : forall F ks l,
    location F < ks SLoc ->
    InstIndValid_at F ks (LocI l)
| InstIndValidLoc_at_Some : forall F ks l,
    location F >= ks SLoc ->
    InstIndValid (InstFunctionCtxInd_under_ks F ks (LocI l))
                 (FunT [LOC] (Arrow [] []))
                 (LocI (subst'_loc (weaks' ks) l)) ->
    InstIndValid_at F ks (LocI l)
| InstIndValidQual_at_None : forall F ks q,
    nth_error (qual F) (ks SQual) = None ->
    InstIndValid_at F ks (QualI q)
| InstIndValidQual_at_Some : forall F ks q qs0 qs1,
    nth_error (qual F) (ks SQual) = Some (qs0, qs1) ->
    InstIndValid (InstFunctionCtxInd_under_ks F ks (QualI q))
                 (FunT [QUAL (subst'_quals (under_ks' ks (subst'_of (ext SQual q id))) qs0)
                             (subst'_quals (under_ks' ks (subst'_of (ext SQual q id))) qs1)]
                       (Arrow [] []))
                 (QualI (subst'_qual (weaks' ks) q)) ->
    InstIndValid_at F ks (QualI q)
| InstIndValidSize_at_None : forall F ks sz,
    nth_error (size F) (ks SSize) = None ->
    InstIndValid_at F ks (SizeI sz)
| InstIndValidSize_at_Some : forall F ks sz szs0 szs1,
    nth_error (size F) (ks SSize) = Some (szs0, szs1) ->
    InstIndValid (InstFunctionCtxInd_under_ks F ks (SizeI sz))
                 (FunT [SIZE
                          (subst'_sizes (under_ks' ks (subst'_of (ext SSize sz id))) szs0)
                          (subst'_sizes (under_ks' ks (subst'_of (ext SSize sz id))) szs1)]
                       (Arrow [] []))
                 (SizeI (subst'_size (weaks' ks) sz)) ->
    InstIndValid_at F ks (SizeI sz)
| InstIndValidPretype_at_None : forall F ks pt,
    nth_error (type F) (ks SPretype) = None ->
    InstIndValid_at F ks (PretypeI pt)
| InstIndValidPretype_at_Some : forall F ks pt sz q hc,
    nth_error (type F) (ks SPretype) = Some (sz, q, hc) ->
    InstIndValid (InstFunctionCtxInd_under_ks F ks (PretypeI pt))
                 (FunT [TYPE sz q hc] (Arrow [] []))
                 (PretypeI (subst'_pretype (weaks' ks) pt)) ->
    InstIndValid_at F ks (PretypeI pt).

Lemma ks_of_kvs_to_ks_of_idxs : forall {idxs atyp kvs F},
    InstIndsValid F (FunT kvs atyp) idxs ->
    length kvs = length idxs ->
    ks_of_kvs kvs = ks_of_idxs idxs.
Proof.
  induction idxs; intros; simpl in *;
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; simpl in *; auto
    end.
  - destruct kvs; simpl in *; auto.
    match goal with
    | [ H : Datatypes.S _ = 0 |- _ ] => inv H
    end.
  - destruct kvs; simpl in *.
    1:{
      match goal with
      | [ H : 0 = Datatypes.S _ |- _ ] => inv H
      end.
    }
    match goal with
    | [ X : KindVar |- _ ] => destruct X
    end.
    all:
      match goal with
      | [ X : Index |- _ ] => destruct X
      end.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inv H
      end.
    all: simpl.
    all:
      match goal with
      | [ H : InstIndsValid _ (FunT ?KVS _) _
          |- context[ks_of_kvs ?KVS2] ] =>
        replace (ks_of_kvs KVS2) with (ks_of_kvs KVS);
          [ | rewrite ks_of_kvs_subst_kindvars; auto ]
      end.
    all:
      match goal with
      | [ H : forall _, _ |- _ ] => erewrite H; eauto
      end.
    all: rewrite length_subst_kindvars.
    all:
      match goal with
      | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] => inv H; auto
      end.
Qed.

Lemma pure_under_ks_of_kvs : forall {kvs knd obj},
    debruijn_subst_ext_conds
      (under_ks' (ks_of_kvs kvs) (subst'_of (ext knd obj id)))
      (ks_of_kvs kvs)
      knd obj.
Proof.
  intros.
  rewrite <-under_kindvars'_to_under_ks'.
  apply pure_under_kindvars.
Qed.

Ltac prepare_collect_app_simpl_subgoal :=
  intros;
  rewrite app_nil_r;
  apply eq_sym;
  rewrite <-map_id;
  apply map_ext;
  intros;
  destruct_prs;
  simpl.    

Ltac solve_collect_app_IH_subgoal lem :=
  intros;
  rewrite app_assoc;
  repeat rewrite lem;
  match goal with
  | [ H : forall _, _ |- _ ] => rewrite H
  end;
  match goal with
  | [ X : KindVar |- _ ] => destruct X
  end;
  simpl;
  rewrite ks_of_kvs_app; simpl;
  try match goal with
      | [ |- ?A :: ?B = ?A :: ?C ] => replace C with B; auto
      end;
  try rewrite map_app;
  match goal with
  | [ |- ?A ++ ?B = ?A ++ ?C ] => replace C with B; auto
  end;
  try solve_map_map.

Lemma collect_qctx_app : forall {kvs' kvs},
    collect_qctx (kvs ++ kvs') =
    collect_qctx
      kvs'
      ++
      map
      (fun '(qs0, qs1) =>
         (subst'_quals (weaks' (ks_of_kvs kvs')) qs0,
          subst'_quals (weaks' (ks_of_kvs kvs')) qs1))
      (collect_qctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs' =>
          forall kvs,
            collect_qctx (kvs ++ kvs') =
            collect_qctx
              kvs'
              ++
              map
              (fun '(qs0, qs1) =>
                 (subst'_quals (weaks' (ks_of_kvs kvs')) qs0,
                  subst'_quals (weaks' (ks_of_kvs kvs')) qs1))
              (collect_qctx kvs))).
  - prepare_collect_app_simpl_subgoal.
    repeat rewrite weaks_zero_no_effect_on_quals.
    auto.
  - solve_collect_app_IH_subgoal collect_qctx_snoc.
Qed.

Ltac solve_rev_map_map :=
  apply map_ext;
  intros;
  destruct_prs;
  repeat rewrite <-compose_weak_weaks_qual;
  repeat rewrite <-compose_weak_weaks_size;
  repeat rewrite <-compose_weak_weaks_quals;
  repeat rewrite <-compose_weak_weaks_sizes;
  repeat rewrite <-compose_weak_weaks_types;
  repeat rewrite <-compose_weak_weaks_local_ctx;
  auto.

Lemma collect_szctx_app : forall {kvs' kvs},
    collect_szctx (kvs ++ kvs') =
    collect_szctx
      kvs'
      ++
      map
      (fun '(szs0, szs1) =>
         (subst'_sizes (weaks' (ks_of_kvs kvs')) szs0,
          subst'_sizes (weaks' (ks_of_kvs kvs')) szs1))
      (collect_szctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs' =>
          forall kvs,
            collect_szctx (kvs ++ kvs') =
            collect_szctx
              kvs'
              ++
              map
              (fun '(szs0, szs1) =>
                 (subst'_sizes (weaks' (ks_of_kvs kvs')) szs0,
                  subst'_sizes (weaks' (ks_of_kvs kvs')) szs1))
              (collect_szctx kvs))).
  - prepare_collect_app_simpl_subgoal.
    repeat rewrite weaks_zero_no_effect_on_sizes.
    auto.
  - solve_collect_app_IH_subgoal collect_szctx_snoc.
    all: solve_rev_map_map.

    Ltac handle_subst_weak :=
      match goal with
      | [ |- context[subst'_sizes (subst'_of (weak ?KND))] ] =>
        erewrite (weak_non_size_no_effect_on_sizes
                    (knd:=KND)
                    (f:=(subst'_of (weak KND))))
      end;
      solve_ineqs;
      try apply single_weak_debruijn_weak_conds.

    all: repeat handle_subst_weak; auto.
Qed.

Lemma collect_tctx_app : forall {kvs' kvs},
    collect_tctx (kvs ++ kvs') =
    collect_tctx
      kvs'
      ++
      map
      (fun '(sz, q, hc) =>
         (subst'_size (weaks' (ks_of_kvs kvs')) sz,
          subst'_qual (weaks' (ks_of_kvs kvs')) q,
          hc))
      (collect_tctx kvs).
Proof.
  apply
    (rev_ind
       (fun kvs' =>
          forall kvs,
            collect_tctx (kvs ++ kvs') =
            collect_tctx
              kvs'
              ++
              map
              (fun '(sz, q, hc) =>
                 (subst'_size (weaks' (ks_of_kvs kvs')) sz,
                  subst'_qual (weaks' (ks_of_kvs kvs')) q,
                  hc))
              (collect_tctx kvs))).
  - prepare_collect_app_simpl_subgoal.
    rewrite weaks_zero_no_effect_on_size.
    rewrite weaks_zero_no_effect_on_qual.
    auto.
  - solve_collect_app_IH_subgoal collect_tctx_snoc.
    2:{
      repeat rewrite <-compose_weak_weaks_size.
      match goal with
      | [ |- context[subst'_size (subst'_of (weak ?KND))] ] =>
        erewrite (weak_non_size_no_effect_on_size
                    (knd:=KND)
                    (f:=(subst'_of (weak KND))));
          solve_ineqs; auto
      end.
      apply single_weak_debruijn_weak_conds.
    }
    
    all: solve_rev_map_map.
    all:
      match goal with
      | [ |- context[subst'_size (subst'_of (weak ?KND))] ] =>
        erewrite (weak_non_size_no_effect_on_size
                    (knd:=KND)
                    (f:=(subst'_of (weak KND))));
          solve_ineqs; auto
      end;
      try apply single_weak_debruijn_weak_conds.
    all:
      match goal with
      | [ |- context[subst'_qual (subst'_of (weak ?KND))] ] =>
        erewrite (weak_non_qual_no_effect_on_qual
                    (knd:=KND)
                    (f:=(subst'_of (weak KND))));
          solve_ineqs; auto
      end;
      try apply single_weak_debruijn_weak_conds.
Qed.

Lemma simple_fields_eq_subst : forall {kvs F F' atyp kvs' atyp' idx},
    Function_Ctx_empty F' ->
    simple_fields_eq F (add_constraints F' kvs) ->
    InstIndValid F' (FunT kvs atyp) idx ->
    InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp') ->
    simple_fields_eq
      (InstFunctionCtxInd_under_ks F (ks_of_kvs kvs') idx)
      (add_constraints F' kvs').
Proof.
  Ltac handle_size :=
    erewrite size_debruijn_subst_ext;
    [ | | rewrite <-under_kindvars'_to_under_ks';
          apply pure_under_kindvars ];
    try now solve_ineqs.
  Ltac handle_qual :=
    erewrite qual_debruijn_subst_ext;
    [ | | rewrite <-under_kindvars'_to_under_ks';
          apply pure_under_kindvars ];
    try now solve_ineqs.
  Ltac handle_sizes :=
    erewrite sizes_debruijn_subst_ext;
    [ | | rewrite <-under_kindvars'_to_under_ks';
          apply pure_under_kindvars ];
    try now solve_ineqs.
  Ltac handle_quals :=
    erewrite quals_debruijn_subst_ext;
    [ | | rewrite <-under_kindvars'_to_under_ks';
          apply pure_under_kindvars ];
    try now solve_ineqs.
  Ltac handle_map_goal :=
    rewrite <-map_id;
    apply map_ext;
    intros;
    destruct_prs;
    repeat handle_qual;
    repeat handle_size;
    repeat handle_quals;
    repeat handle_sizes.
  Ltac prepare_subgoal :=
    rewrite cons_append;
    rewrite collect_qctx_app;
    rewrite collect_szctx_app;
    rewrite collect_tctx_app;
    simpl;
    repeat rewrite app_nil_r;
    split; [ | split; [ | split ] ];
    try handle_map_goal.
  Ltac handle_special_goal lem :=
    match goal with
    | [ |- context[remove_nth (?L ++ ?L2) ?IDX] ] =>
      replace (remove_nth (L ++ L2) IDX) with L
    end;
    [ | 
      rewrite <-lem;
      rewrite remove_nth_prefix;
      rewrite app_nil_r; auto ];
    try handle_map_goal.
  
  intros.
  unfold simple_fields_eq in *.
  rewrite add_constraints_to_ks_of_kvs in *.
  unfold Function_Ctx_empty in *.
  destructAll.
  destruct F; destruct F'; subst; simpl in *; subst; simpl in *.
  repeat rewrite app_nil_r.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H
  end.
  all:
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
  all: repeat rewrite ks_of_kvs_subst_kindvars.
  all: simpl.
  - erewrite kindvars_debruijn_subst_ext.
    4:{ apply simpl_debruijn_subst_ext_conds. }
    all: solve_ineqs.
    prepare_subgoal.
    
    unfold plus; simpl.
    unfold shift_down_after_eq.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
      replace B with false
    end.
    2:{
      apply eq_sym.
      rewrite Nat.leb_gt.
      lia.
    }
    lia.
  - erewrite kindvars_debruijn_subst_ext.
    4:{ apply simpl_debruijn_subst_ext_conds. }
    all: solve_ineqs.
    prepare_subgoal.
    -- handle_special_goal length_collect_tctx.
    -- unfold plus; auto.
  - erewrite collect_qctx_subst_qual.
    2:{ apply pure_under_ks_of_kvs. }
    erewrite collect_szctx_subst_qual.
    erewrite collect_tctx_subst_qual.
    2:{ apply pure_under_ks_of_kvs. }
    prepare_subgoal.
    -- handle_special_goal length_collect_qctx.
       auto.
    -- apply map_ext.
       intros.
       destruct_prs.
       handle_size.
    -- unfold plus; auto.
  - erewrite collect_qctx_subst_size.
    erewrite collect_szctx_subst_size.
    2:{ apply pure_under_ks_of_kvs. }
    erewrite collect_tctx_subst_size.
    2:{ apply pure_under_ks_of_kvs. }
    prepare_subgoal.
    -- handle_special_goal length_collect_szctx.
       auto.
    -- apply map_ext.
       intros.
       destruct_prs.
       handle_qual.
    -- unfold plus; auto.
Qed.

Lemma KindVarsValid_InstInd : forall {kvs kvs' F' atyp' atyp idx},
    KindVarsValid F' kvs ->
    InstIndValid F' (FunT kvs atyp) idx ->
    InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp') ->
    KindVarsValid F' kvs'.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H
  end.
  all: simpl in *.
  all:
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
  all: simpl in *.
  
  - erewrite kindvars_debruijn_subst_ext.
    4:{ apply simpl_debruijn_subst_ext_conds. }
    all: solve_ineqs.
    all: eapply KindVarsValid_Function_Ctx; eauto.
    all: destruct F'; subst; simpl in *; auto.
    -- handle_map_goal.
       repeat handle_weak_quals.
       auto.
    -- handle_map_goal.
       repeat handle_weak_sizes.
       auto.
  - erewrite kindvars_debruijn_subst_ext.
    4:{ apply simpl_debruijn_subst_ext_conds. }
    all: solve_ineqs.
    all: eapply KindVarsValid_Function_Ctx; eauto.
    all: destruct F'; subst; simpl in *; auto.
    -- handle_map_goal.
       repeat handle_weak_quals.
       auto.
    -- handle_map_goal.
       repeat handle_weak_sizes.
       auto.
  - match goal with
    | [ |- KindVarsValid ?F (subst'_kindvars ?SU _) ] =>
      replace F with
          (add_constraints F (subst'_kindvars SU []))
    end.
    2:{ simpl; auto. }
    eapply KindVarsValid_subst_qual; auto; simpl; eauto.
    apply simpl_debruijn_subst_ext_conds.
  - match goal with
    | [ |- KindVarsValid ?F (subst'_kindvars ?SU _) ] =>
      replace F with
          (add_constraints F (subst'_kindvars SU []))
    end.
    2:{ simpl; auto. }
    eapply KindVarsValid_subst_size; auto; simpl; eauto.
    apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma QualValid_empty_imp_subst_quals_no_effect : forall {qs},
    Forall (QualValid []) qs ->
    forall su,
      subst'_quals su qs = qs.
Proof.
  induction qs; intros; simpl in *; auto.
  match goal with
  | [ H : Forall _ (_ :: _) |- _ ] => inv H
  end.
  rewrite QualValid_empty_imp_value_closed; auto.
  rewrite IHqs; auto.
Qed.

Lemma SizeValid_empty_imp_subst_sizes_no_effect : forall {szs},
    Forall (SizeValid []) szs ->
    forall su,
      subst'_sizes su szs = szs.
Proof.
  induction szs; intros; simpl in *; auto.
  match goal with
  | [ H : Forall _ (_ :: _) |- _ ] => inv H
  end.
  rewrite SizeValid_empty_imp_value_closed; auto.
  rewrite IHszs; auto.
Qed.

Lemma InstIndValid_to_InstIndValid_at : forall {kvs F F' atyp idx kvs' atyp'},
    InstIndValid F' (FunT kvs atyp) idx ->
    InstInd (FunT kvs atyp) idx = Some (FunT kvs' atyp') ->
    Function_Ctx_empty F' ->
    KindVarsValid F' kvs ->
    simple_fields_eq F (add_constraints F' kvs) ->
    InstIndValid_at F (ks_of_kvs kvs') idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H
  end.
  all: simpl in *.
  all:
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
  all: rewrite ks_of_kvs_subst_kindvars.
  all: rewrite add_constraints_to_ks_of_kvs in *.
  all: unfold simple_fields_eq in *.
  all: destructAll.
  all: simpl in *.
  all: unfold Function_Ctx_empty in *; destructAll.
  all: destruct F; destruct F'; subst; simpl in *; subst; simpl in *.
  all:
    match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
  all:
    match goal with
    | [ H : KindVarValid _ _ |- _ ] => inv H; simpl in *
    end.
  - apply InstIndValidLoc_at_Some; simpl; [ lia | ].
    econstructor.
    match goal with
    | [ H : LocValid 0 _ |- _ ] => inv H
    end.
    -- econstructor; simpl; eauto.
    -- match goal with
       | [ H : _ < 0 |- _ ] => inv H
       end.       
  - eapply InstIndValidPretype_at_Some; simpl.
    -- rewrite <-length_collect_tctx.
       rewrite nth_error_prefix.
       eauto.
    -- rewrite <-length_collect_tctx.
       rewrite remove_nth_prefix.
       repeat rewrite app_nil_r.
       econstructor.
       --- eapply sizeOfPretype_empty_ctx; eauto.
           erewrite TypeValid_empty_imp_value_closed; eauto.
           constructor; auto.
       --- eapply SizeValid_empty_ctx; eauto.
       --- repeat rewrite SizeValid_empty_imp_value_closed; auto.
           eapply SizeValid_empty_ctx; eauto.
       --- repeat rewrite SizeValid_empty_imp_value_closed; auto.
           apply SizeLeq_empty_ctx; eauto.
       --- repeat rewrite QualValid_empty_imp_value_closed; auto.
           eapply TypeValid_sub; eauto.
           ---- erewrite TypeValid_empty_imp_value_closed; eauto.
                constructor; auto.
           ---- constructor; simpl; try constructor; auto.
                lia.
       --- intros.
           match goal with
           | [ H : ?A, H' : ?A -> _ |- _ ] =>
             specialize (H' H)
           end.
           unfold heapable in *.
           simpl in *.
           eapply NoCapsPretype_empty_ctx; eauto.
           erewrite TypeValid_empty_imp_value_closed; eauto.
           constructor; auto.
  - eapply InstIndValidQual_at_Some; simpl.
    -- rewrite <-length_collect_qctx.
       rewrite nth_error_prefix.
       eauto.
    -- constructor.
       --- eapply QualValid_empty_ctx; eauto.
           erewrite QualValid_empty_imp_value_closed; eauto.
       --- repeat rewrite QualValid_empty_imp_subst_quals_no_effect; auto.
           prepare_Forall.
           destructAll.
           split.
           ---- eapply QualValid_empty_ctx; eauto.
           ---- eapply QualLeq_empty_ctx; eauto.
                erewrite QualValid_empty_imp_value_closed; eauto.
       --- repeat rewrite QualValid_empty_imp_subst_quals_no_effect; auto.
           prepare_Forall.
           destructAll.
           split.
           ---- eapply QualValid_empty_ctx; eauto.
           ---- eapply QualLeq_empty_ctx; eauto.
                erewrite QualValid_empty_imp_value_closed; eauto.
  - eapply InstIndValidSize_at_Some; simpl.
    -- rewrite <-length_collect_szctx.
       rewrite nth_error_prefix.
       eauto.
    -- constructor.
       --- eapply SizeValid_empty_ctx; eauto.
           erewrite SizeValid_empty_imp_value_closed; eauto.
       --- repeat rewrite SizeValid_empty_imp_subst_sizes_no_effect; auto.
           prepare_Forall.
           destructAll.
           split.
           ---- eapply SizeValid_empty_imp_all_SizeValid; eauto.
           ---- eapply SizeLeq_empty_ctx; eauto.
                erewrite SizeValid_empty_imp_value_closed; eauto.
       --- repeat rewrite SizeValid_empty_imp_subst_sizes_no_effect; auto.
           prepare_Forall.
           destructAll.
           split.
           ---- eapply SizeValid_empty_imp_all_SizeValid; eauto.
           ---- eapply SizeLeq_empty_ctx; eauto.
                erewrite SizeValid_empty_imp_value_closed; eauto.
Qed.

Lemma InstIndValid_index_closed : forall {F ft idx},
    InstIndValid F ft idx ->
    Function_Ctx_empty F ->
    index_closed idx.
Proof.
  intros.
  destruct F; simpl in *.
  unfold Function_Ctx_empty in *; destructAll; simpl in *; subst.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H; simpl in *
  end.
  - apply LocValid_zero_imp_value_closed; auto.
  - eapply TypeValid_empty_imp_value_closed; eauto.
    unfold Function_Ctx_empty; auto.
  - apply QualValid_empty_imp_value_closed; auto.
  - apply SizeValid_empty_imp_value_closed; auto.
Qed.

Lemma InstIndValids_index_closed : forall {idxs F ft},
    InstIndsValid F ft idxs ->
    Function_Ctx_empty F ->
    Forall index_closed idxs.
Proof.
  induction idxs; intros; simpl in *; constructor.
  all:
    match goal with
    | [ H : InstIndsValid _ _ _ |- _ ] => inv H; eauto
    end.
  eapply InstIndValid_index_closed; eauto.
Qed.
