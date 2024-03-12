From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive FSets.FMapFacts
     micromega.Lia Sets.Ensembles Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.tactics RWasm.list_util
        RWasm.map_util RWasm.EnsembleUtil.

Module F := FMapFacts.Properties map_util.M.
Import F.

Definition update_unr (U : HeapTyping ) (S : StoreTyping) : StoreTyping :=
{| InstTyp := InstTyp S; LinTyp := LinTyp S; UnrTyp := U |}.

Ltac solve_inst_or_unr_typ_eq :=
  repeat match goal with
         | [ H : SplitStoreTypings [_; _] _ |- _ ] =>
           inversion H; subst; simpl in *; clear H
         | [ H : Forall _ [_; _] |- _ ] =>
           inversion H; subst; simpl in *; clear H
         | [ H : SplitStoreTypings (_ :: _) _ |- _ ] =>
           inversion H; subst; simpl in *; clear H
         | [ H : Forall _ (_ :: _) |- _ ] =>
           inversion H; subst; simpl in *; clear H
         | [ H : SplitStoreTypings [_] _ |- _ ] =>
           inversion H; subst; simpl in *; clear H
         | [ H : Forall _ [_] |- _ ] =>
           inversion H; subst; simpl in *; clear H
         end;
  destructAll;
  repeat match goal with
         | [ H : ?A = _ |- ?A = _ ] =>
           rewrite H in *; clear H
         | [ H : ?A = _ |- _ = ?A ] =>
           rewrite H in *; clear H
         | [ H : _ = ?A |- ?A = _ ] =>
           rewrite (eq_sym H) in *; clear H
         | [ H : _ = ?A |- _ = ?A ] =>
           rewrite (eq_sym H) in *; clear H
         end;
  eauto.

Section Splitting.
  
  Definition HasEmptyLinTyping (S : StoreTyping) :=
    let (it, lin, unrt) := S in
    M.is_empty lin = true. 
    
  Lemma SplitHeapTypings_EmptyHeapTyping_l Hemp H :
    M.is_empty Hemp = true ->
    SplitHeapTypings [Hemp; H] H.
  Proof.
    split. simpl. 
    rewrite Dom_ht_is_empty. now sets.
    eassumption.
    
    intros l ht Hh. constructor 3.
    unfold get_heaptype in *.
    eapply gis_empty; eassumption.
    
    constructor. eassumption.
    constructor.
  Qed.
  

  Lemma SplitHeapTypings_EmptyHeapTyping_r H Hemp :
    M.is_empty Hemp = true ->
    SplitHeapTypings [H; Hemp] H.
  Proof.
    split. simpl.
    rewrite (Dom_ht_is_empty Hemp H0). now sets.
    
    
    intros l ht Hh.

    constructor. eassumption.
    
    constructor 3.
    unfold get_heaptype. rewrite gis_empty. reflexivity. eassumption.
    
    constructor.
  Qed.
  
  Lemma SplitStoreTypings_EmptyHeapTyping S :
    HasEmptyLinTyping S -> 
    SplitStoreTypings [S; S] S.
  Proof.
    destruct S; unfold SplitStoreTypings; simpl; intros Hemp. split.
    - constructor. simpl. eauto. constructor. simpl. eauto.
      constructor.
    - eapply SplitHeapTypings_EmptyHeapTyping_l. eassumption.
  Qed.

  Lemma SplitStoreTypings_EmptyHeapTyping_l S :
    SplitStoreTypings [empty_LinTyp S; S] S.
  Proof.
    destruct S; unfold SplitStoreTypings; simpl. split.
    - constructor. simpl. eauto. constructor. simpl. eauto.
      constructor.
    - eapply SplitHeapTypings_EmptyHeapTyping_l. reflexivity. 
  Qed.
 
  Lemma SplitStoreTypings_EmptyHeapTyping_r S :
    SplitStoreTypings [S; empty_LinTyp S] S.
  Proof.
    destruct S; unfold SplitStoreTypings; simpl. split.
    - constructor. simpl. eauto. constructor. simpl. eauto.
      constructor.
    - eapply SplitHeapTypings_EmptyHeapTyping_r. reflexivity.
  Qed.

  
  Lemma ExactlyInOne_comm b l ht H1 H2 :
    ExactlyInOne b l ht [H1; H2] ->
    ExactlyInOne b l ht [H2; H1].
  Proof.
    intros Hyp. inv Hyp.
    - inv H8. constructor 3; eauto.
      constructor; eauto.
    - inv H8.
      constructor; eauto.
      constructor 3; eauto.
      inv H10.
      constructor 3; eauto.
      constructor 3; eauto.
      constructor.
  Qed. 

  Lemma SplitHeapTypings_comm S1 S2 S :
    SplitHeapTypings [S1; S2] S ->
    SplitHeapTypings [S2; S1] S.
  Proof.
    intros H. inv H.
    constructor; eauto.
    simpl in *. rewrite <- H0. now sets.
    intros. eapply ExactlyInOne_comm; eauto.
  Qed.

  
  Lemma SplitStoreTypings_comm S1 S2 S :
    SplitStoreTypings [S1; S2] S ->
    SplitStoreTypings [S2; S1] S.
  Proof.
    destruct S1; destruct S2; destruct S.
    intros H. inv H. simpl in *. inv H0. inv H3. inv H4. simpl in *.
    inv H2.
    constructor.
    constructor. now eauto. constructor. now eauto.
    now constructor.
    simpl. eapply SplitHeapTypings_comm. eassumption.
  Qed. 

  Definition StoreTyping_eq (S1 S2 : StoreTyping) :=
    InstTyp S1 = InstTyp S2 /\
    eq_map (LinTyp S1) (LinTyp S2) /\   
    UnrTyp S1 = UnrTyp S2.

  Lemma SplitHeapTypings_eq Ss S S' :
    SplitHeapTypings Ss S ->
    SplitHeapTypings Ss S' ->
    eq_map S S'.
  Proof.
    intros Hyp Hyp'. inv Hyp. inv Hyp'.
    rewrite H1 in H.
    
    intros l.

    destruct (get_heaptype l S) eqn:Heq;
    destruct (get_heaptype l S') eqn:Heq'; eauto.

    2:{ assert (Hc : exists h, get_heaptype l S' = Some h).
        { eapply H. eexists; eauto. }
        inv Hc. congruence. } 


    2:{ assert (Hc : exists h, get_heaptype l S = Some h).
        { eapply H. eexists; eauto. }
        inv Hc. congruence. } 

    eapply H0 in Heq.
    eapply H2 in Heq'.
    revert Heq Heq'. clear; intros Heq Heq'.

    induction Ss. now inv Heq.

    inv Heq.

    - inv Heq'; congruence.

    - inv Heq'. congruence.
      eauto.
  Qed.

  Lemma SplitStoreTypings_eq S1 Ss S S' :
    SplitStoreTypings (S1 :: Ss) S ->
    SplitStoreTypings (S1 :: Ss) S' ->
    StoreTyping_eq S S'.
  Proof.
    intros H1 H2. inv H1. inv H2. simpl in *.
    split; [| split ].
    
    2:{ eapply SplitHeapTypings_eq; eauto. }

    inv H. inv H5. inv H1. inv H7. congruence. 
    inv H. inv H5. inv H1. inv H7. congruence. 
  Qed.


  Lemma Union_list_app A (l1 l2 : list (Ensemble A)) :
    Union_list (l1 ++ l2) <--> Union_list l1 :|: Union_list l2. 
  Proof.
    induction l1. simpl. now sets.
    simpl. rewrite IHl1. sets.
  Qed.


  Lemma ExactlyInOne_app_l l ht S1 S2 :
    ExactlyInOne false l ht S1 ->
    ExactlyInOne true l ht S2 ->    
    ExactlyInOne false l ht (S1 ++ S2).
  Proof.
    intros H1 H2. induction H1. eassumption.
    - constructor; eauto.
    - constructor; eauto.
  Qed.

  Lemma ExactlyInOne_app_r l ht S1 S2 :
    ExactlyInOne true l ht S1 ->
    ExactlyInOne false l ht S2 ->    
    ExactlyInOne false l ht (S1 ++ S2).
  Proof.
    intros H1 H2. induction S1; inv H1. eassumption.
    simpl. constructor 3; eauto.
  Qed.

  Lemma ExactlyInOne_true l ht S :
    ~ l \in Union_list (map Dom_ht S) ->
    ExactlyInOne true l ht S.
  Proof.
    intros H. induction S.
    - now constructor.
    - constructor.

      + destruct (get_heaptype l a) eqn:Hget; eauto.
        
        exfalso. eapply H. simpl. left. eexists; eauto.

      + eapply IHS. intros Hc. eapply H.
        simpl; right; eauto.
  Qed.

  Definition union {A} : map_util.M.t A -> map_util.M.t A -> map_util.M.t A :=
    M._map2 (fun o1 o2 =>
             match o1, o2 with
             | Some x1, _ => Some x1
             | _, Some y1 => Some y1
             | _, _ => None
             end).
  
  Lemma Dom_ht_union (HT1 HT2 : HeapTyping) :
    Dom_ht (union HT1 HT2) <--> Dom_ht HT1 :|: Dom_ht HT2.
  Proof.
    constructor; unfold Dom_ht; intros x Hx; unfold In, Dom_map in *.
    - destruct Hx as [y Hy]; unfold union in Hy; rewrite M.gmap2 in Hy by auto.
      destruct (M.find (N.succ_pos x) HT1) eqn:Heq1, (M.find (N.succ_pos x) HT2) eqn:Heq2; try easy.
      + left; inv Hy. unfold In.  eauto.
      + left; inv Hy; unfold In; eauto.
      + right; inv Hy; unfold In; eauto.
    - unfold union; rewrite M.gmap2 by auto.
      destruct (M.find (N.succ_pos x) HT1) eqn:Heq1; [now eauto|].
      inv Hx; [unfold In in *; firstorder congruence|]. unfold In in *.
      destruct H as [y Hy]. exists y. now rewrite Hy.
  Qed.
  
  Definition minus {A} : map_util.M.t A -> map_util.M.t A -> map_util.M.t A :=
    M._map2 (fun o1 o2 =>
               match o1, o2 with
               | _, Some _ => None
               | o, None => o
               end).
  
  Lemma Dom_ht_minus (HT1 HT2 : HeapTyping) :
    Dom_ht (minus HT1 HT2) <--> Dom_ht HT1 \\ Dom_ht HT2.
  Proof.
    constructor; unfold Dom_ht; intros x Hx; unfold In, Dom_map in *.
    - constructor; unfold In.
      + destruct Hx as [y Hy]. unfold minus in Hy; rewrite M.gmap2 in Hy by auto.
        destruct (M.find (N.succ_pos x) HT2); [easy|]. eauto.
      + intros [y Hy]; destruct Hx as [y' Hy'].
        unfold minus in Hy'; rewrite M.gmap2 in Hy' by auto.
        destruct (M.find (N.succ_pos x) HT2); easy.
    - inv Hx. unfold In in *. destruct H as [y Hy]. rename H0 into Hnotin_HT2.
      unfold minus; rewrite M.gmap2 by auto.
      exists y; rewrite Hy.
      destruct (M.find (N.succ_pos x) HT2) eqn:Heqn; [exfalso; apply Hnotin_HT2; eauto|auto].
  Qed.

  (*
  
  Definition ht_disjoint (H1 H2 : HeapTyping) :=
    forall x, match M.find x H1, M.find x H2 with
         | Some _, Some _ => False
         | _, _ => True
         end.

  Fixpoint All {A} P (xs : list A) := match xs with [] => True | x :: xs => P x /\ All P xs end.
  
  Fixpoint pairwise_disjoint (Hs : list HeapTyping) :=
    match Hs with
    | [] => True
    | H :: Hs => All (ht_disjoint H) Hs /\ pairwise_disjoint Hs
    end.
  
  Lemma SplitHeapTypings_disjoint Hs H :
    SplitHeapTypings Hs H ->
    pairwise_disjoint Hs.
  Proof.
    revert H; induction Hs as [|H' Hs IHHs]; [easy|].
    inversion 1.
    cbn; split.
    Abort.
*)

  Definition get_ExactlyInOne H Hs :=
    forall l ht, get_heaptype l H = Some ht -> ExactlyInOne false l ht Hs.

  Lemma ExactlyInOne_true_converse l ht S :
    ExactlyInOne true l ht S ->
    ~ l \in Union_list (map Dom_ht S).
  Proof.
    induction S; [cbn; now inversion 1|].
    cbn; inversion 1; subst.
    intros Hin. inv Hin.
    - destruct H0 as [? ?]; unfold get_heaptype in *; congruence.
    - apply IHS; auto.
  Qed.

  Lemma ExactlyInOne_true_iff l ht S :
    ExactlyInOne true l ht S <->
    ~ l \in Union_list (map Dom_ht S).
  Proof. split; (apply ExactlyInOne_true_converse + apply ExactlyInOne_true). Qed.

  Lemma In_or_Iff_Union : forall {A} (a : A) S1 S2,
    Ensembles.In _ (S1 :|: S2) a <-> Ensembles.In _ S1 a \/ Ensembles.In _ S2 a.
  Proof. split; intros; destruct H; auto; [now left|now right]. Qed.

  Lemma ExactlyInOne_true_app l ht S1 S2 :
    ExactlyInOne true l ht (S1 ++ S2) <->
    ExactlyInOne true l ht S1 /\ ExactlyInOne true l ht S2.
  Proof.
    rewrite !ExactlyInOne_true_iff, !map_app, !Union_list_app, !In_or_Iff_Union.
    tauto.
  Qed.

  Lemma ExactlyInOne_app_inv l ht H1 H2 :
     ExactlyInOne false l ht (H1 ++ H2) ->
     (ExactlyInOne false l ht H1 /\ ExactlyInOne true l ht H2) \/
     (ExactlyInOne true l ht H1 /\ ExactlyInOne false l ht H2).
  Proof.
    induction H1.
    - cbn; right; split; [now constructor|now auto].
    - intros H; inv H.
      + apply ExactlyInOne_true_app in H8; destruct H8; left; split; [constructor; auto|auto].
      + apply IHlist in H9.
        destruct H9; [left|right];
          (split; [apply NotInHead + apply FoundNil + apply InHead|]; auto; tauto).
  Qed.
  
  Lemma ExactlyInOne_app_comm:
    forall (b : bool) (l : Ptr) (ht : HeapType) (H1 H2 : list HeapTyping),
      ExactlyInOne b l ht (H1 ++ H2) -> ExactlyInOne b l ht (H2 ++ H1).
  Proof.
    induction H1; [cbn; intros; rewrite app_nil_r; auto|].
    cbn. intros H2 H; inv H.
    - apply ExactlyInOne_true_app in H9.
      destruct H9 as [HH1 HH2].
      apply ExactlyInOne_app_r; auto.
      constructor; auto.
    - destruct b.
      + apply ExactlyInOne_true_app in H9.
        apply ExactlyInOne_true_app; firstorder try tauto.
        constructor; auto.
      + apply ExactlyInOne_app_inv in H9.
        destruct H9.
        * apply ExactlyInOne_app_r; [tauto|].
          apply NotInHead; tauto.
        * apply ExactlyInOne_app_l; [tauto|].
          apply NotInHead; tauto.
  Qed.

  Lemma get_ExactlyInOne_disjoint H Hl Hx Hr :
    Dom_ht H <--> Union_list (map Dom_ht Hl) :|: Dom_ht Hx :|: Union_list (map Dom_ht Hr) ->
    get_ExactlyInOne H (Hl ++ [Hx] ++ Hr) ->
    Ensembles.Disjoint _ (Dom_ht Hx) (Union_list (map Dom_ht Hl) :|: Union_list (map Dom_ht Hr)).
  Proof.
    revert H; induction Hl.
    - cbn. intros H; rewrite !Union_Empty_set_neut_l.
      intros Heq Hone.
      constructor; intros _ [x HHx HHr]; unfold In in *.
      assert (x_in_H : Dom_ht H x) by (apply Heq; now left).
      destruct HHx as [ht Hht], x_in_H as [ht' Hht'].
      specialize (Hone _ _ Hht').
      inv Hone; [|unfold get_heaptype in *; congruence].
      apply ExactlyInOne_true_converse in H6.
      contradiction.
    - cbn; intros H. intros Heq Hone.
      constructor; intros _ [x HHx HHalr]; unfold In in *.
      assert (x_in_H : x \in Dom_ht H).
      { apply Heq; eauto with Ensembles_DB. }
      destruct x_in_H as [ht Hht].
      specialize (Hone _ _ Hht).
      inv HHalr.
      + inv H0.
        * destruct H1 as [ht' Hht'].
          inv Hone; [|unfold get_heaptype in *; congruence].
          rewrite ExactlyInOne_true_iff, map_app, Union_list_app in H6.
          cbn in H6. rewrite !In_or_Iff_Union in H6. tauto.
        * apply ExactlyInOne_app_comm with (H1 := a :: Hl) (H2 := Hx :: Hr) in Hone.
          destruct HHx as [ht' Hht'].
          inv Hone; [|unfold get_heaptype in *; congruence].
          rewrite ExactlyInOne_true_iff, map_app, Union_list_app in H7.
          cbn in H7. rewrite !In_or_Iff_Union in H7. tauto.
      + apply ExactlyInOne_app_comm with (H1 := a :: Hl) (H2 := Hx :: Hr) in Hone.
        destruct HHx as [ht' Hht'].
        inv Hone; [|unfold get_heaptype in *; congruence].
        rewrite ExactlyInOne_true_iff, map_app, Union_list_app in H7.
        cbn in H7. rewrite !In_or_Iff_Union in H7. tauto.
  Qed.
  
  Lemma SplitHeapTypings_cons : forall HThd HTtl HT,
    SplitHeapTypings (HThd :: HTtl) HT ->
    SplitHeapTypings HTtl (minus HT HThd).
  Proof.
    intros* [Hdom Hget]. split.
    - cbn in Hdom; rewrite Dom_ht_minus.
      rewrite <- Hdom.
      rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set.
      rewrite Union_Empty_set_neut_l.
      assert (Hget_one : get_ExactlyInOne HT (HThd :: HTtl)) by exact Hget.
      apply get_ExactlyInOne_disjoint with (Hl := []) (Hx := HThd) (Hr := HTtl) in Hget.
      2:{ cbn. rewrite Union_Empty_set_neut_l. symmetry; apply Hdom. }
      cbn in Hget; rewrite Union_Empty_set_neut_l in Hget.
      rewrite Setminus_Disjoint; eauto with Ensembles_DB.
    - intros l Ht; unfold minus, get_heaptype; rewrite M.gmap2 by auto.
      destruct (M.find _ HThd) eqn:Hhd; [now inversion 1|].
      intros HHT; specialize (Hget _ _ HHT).
      inv Hget; unfold get_heaptype in *; congruence.
  Qed.

  Lemma SplitStoreTypings_cons : forall x Ss S,
      SplitStoreTypings (x :: Ss) S ->
      exists S',
        SplitStoreTypings Ss S'.
  Proof.
    intros x Ss S H; inv H. inv H0.
    exists {|InstTyp := InstTyp S; UnrTyp := UnrTyp S; LinTyp := minus (LinTyp S) (LinTyp x)|}.
    constructor; auto. intros Hs; cbn.
    apply SplitHeapTypings_cons; auto.
  Qed.

  Lemma SplitHeapTypings_nil_Empty : SplitHeapTypings [] (M.empty _).
  Proof.
    constructor.
    - cbn; split; intros x; unfold In; try inversion 1; rewrite M.gempty in *; easy.
    - intros*; unfold get_heaptype; rewrite M.gempty; inversion 1.
  Qed.

  Lemma succ_pos_pred_N p :
    N.succ_pos (Pos.pred_N p) = p.
  Proof.
    induction p; cbn; try firstorder congruence; try intuition congruence.
    now rewrite POrderedType.Positive_as_OT.succ_pred_double.
  Qed.

  Lemma SplitHeapTypings_nil S : SplitHeapTypings [] S -> M.is_empty S = true.
  Proof.
    inversion 1.
    apply M.is_empty_1.
    apply M.Empty_alt.
    intros x; destruct (M.find x S) eqn:Hx; auto.
    destruct H0 as [_ S_sub_empty].
    replace x with (N.succ_pos (Pos.pred_N x)) in Hx by apply succ_pos_pred_N.
    unfold Dom_ht, M.key, Dom_map, In in S_sub_empty.
    assert (x_in_dom_S : exists y, M.find (N.succ_pos (Pos.pred_N x)) S = Some y) by eauto.
    specialize (S_sub_empty (Pos.pred_N x) x_in_dom_S).
    cbn in S_sub_empty. inv S_sub_empty.
  Qed.

  Lemma SplitHeapTypings_cons_Empty Hemp Ss S :
    SplitHeapTypings Ss S ->
    M.is_empty Hemp = true ->
    SplitHeapTypings (Hemp :: Ss) S.
  Proof.
    intros H; inv H; constructor.
    - cbn. rewrite Dom_ht_is_empty by auto. rewrite Union_Empty_set_neut_l; auto.
    - intros l ht Hget; apply NotInHead; [unfold get_heaptype; now rewrite gis_empty|auto].
  Qed.

  Definition SplitHeapTypingsOnce (S1 S2 S : HeapTyping) : Prop :=
    Dom_ht S <--> Dom_ht S1 :|: Dom_ht S2 /\
    Ensembles.Disjoint _ (Dom_ht S1) (Dom_ht S2) /\
    M.Equal S (union S1 S2).

  Fixpoint SplitHeapTypings' Ss (S : HeapTyping) :=
    match Ss with
    | [] => M.is_empty S = true
    | Shd :: Ss =>
      Dom_ht Shd \subset Dom_ht S /\
      (forall l, l \in Dom_ht Shd -> get_heaptype l Shd = get_heaptype l S) /\
      SplitHeapTypings' Ss (minus S Shd)
    end.

  Lemma Decidable_Dom_ht (S : HeapTyping) :
    Decidable (Dom_ht S).
  Proof.
    constructor; intros x.
    destruct (M.find (N.succ_pos x) S) eqn:Hx; [left; now exists h|right; intros [y Hy]; congruence].
  Qed.
  Hint Resolve Decidable_Dom_ht : Ensembles_DB.
  
  Lemma SplitHeapTypings'_dom Ss S :
    SplitHeapTypings' Ss S ->
    Dom_ht S <--> Union_list (map Dom_ht Ss).
  Proof.
    revert S; induction Ss; [cbn; intros S H; rewrite Dom_ht_is_empty by auto; reflexivity|].
    cbn; intros S [Hinc [Hsub HSs]]; apply IHSs in HSs.
    rewrite Dom_ht_minus in HSs.
    destruct HSs as [HSsl HSsr]; split.
    - apply Included_Union_Setminus_Included; auto with Ensembles_DB.
    - apply Union_Included; auto with Ensembles_DB.
      eapply Included_trans; [apply HSsr|]; auto with Ensembles_DB.
  Qed.

  Lemma SplitHeapTypings_spec Ss S :
    SplitHeapTypings Ss S <-> SplitHeapTypings' Ss S.
  Proof.
    revert S; induction Ss.
    - cbn; intros; split.
      + intros; now apply SplitHeapTypings_nil.
      + intros. constructor; [cbn; rewrite !Dom_ht_is_empty by auto; reflexivity|].
        intros; unfold get_heaptype in *; rewrite gis_empty in *; auto; easy.
    - cbn. intros S; split.
      + intros H; inv H; cbn in *.
        split; [eapply Included_trans; try apply H0; eauto with Ensembles_DB|].
        split.
        * intros l Hl.
          assert (l_in_S : l \in Dom_ht S). { apply H0; now left. }
          destruct l_in_S as [ht Hht].
          specialize (H1 l ht Hht); inv H1; unfold get_heaptype in *; [congruence|].
          destruct Hl as [ht' Hht']; unfold get_heaptype in *; congruence.
        * apply IHSs; constructor; auto.
          -- rewrite Dom_ht_minus.
             apply (get_ExactlyInOne_disjoint S [] a Ss) in H1; [|cbn; normalize_sets; symmetry; auto].
             cbn in H1; rewrite Union_Empty_set_neut_l in H1.
             split; [|apply Setminus_Included_Included_Union; rewrite Union_commut; auto].
             apply Included_Setminus; auto with Ensembles_DB.
             eapply Included_trans; [|apply H0]; auto with Ensembles_DB.
          -- intros l ht Hht.
             unfold get_heaptype, minus in Hht; rewrite M.gmap2 in Hht by auto.
             destruct (M.find (N.succ_pos l) a) eqn:Ha; [easy|].
             specialize (H1 _ _ Hht); inv H1; unfold get_heaptype in *; congruence.
      + intros [Hsub [Heq Hminus]].
        constructor; auto.
        * pose proof Hminus as Hdom.
          apply SplitHeapTypings'_dom in Hdom.
          cbn; rewrite <- Hdom, Dom_ht_minus.
          rewrite <- Union_Setminus_Same_set; auto with Ensembles_DB.
        * rewrite <- IHSs in Hminus. inv Hminus. rename H into Hdom, H0 into Hget.
          intros l ht Hht. unfold get_heaptype, minus in Hget.
          specialize (Hget l ht); rewrite M.gmap2 in Hget by auto.
          destruct (M.find (N.succ_pos l) a) eqn:Ha.
          -- apply InHead.
             ++ rewrite Heq; auto. unfold Dom_ht, Dom_map, In; eauto.
             ++ apply ExactlyInOne_true_iff; intros Hin.
                assert (l_notin_a : ~ l \in Dom_ht a).
                { rewrite Dom_ht_minus in Hdom. apply Hdom in Hin. now inv Hin. }
                apply l_notin_a; exists h; auto.
          -- apply NotInHead; [unfold get_heaptype in *; easy|].
             apply Hget; unfold get_heaptype in *; easy.
  Qed.

  Lemma Equal_Same_Dom (S1 S2 : HeapTyping) :
    M.Equal S1 S2 ->
    Dom_ht S1 <--> Dom_ht S2.
  Proof.
    intros Heq; split; intros x [y Hy]; exists y; (rewrite <- Heq + rewrite Heq); auto.
  Qed.

  Lemma minus_resp_Equal {A} (S1 S2 S : map_util.M.t A) :
    M.Equal S1 S2 ->
    M.Equal (minus S1 S) (minus S2 S).
  Proof.
    intros Heq x; unfold minus; rewrite !M.gmap2 by auto.
    destruct (M.find x S); auto.
  Qed.
  
  Lemma SplitHeapTypings'_resp_Equal Ss S1 S2 :
    M.Equal S1 S2 ->
    SplitHeapTypings' Ss S1 ->
    SplitHeapTypings' Ss S2.
  Proof.
    revert S1 S2; induction Ss.
    - cbn; intros S1 S2 Heq Hemp; apply M.is_empty_1, M.Empty_alt.
      apply M.is_empty_2 in Hemp; rewrite M.Empty_alt in Hemp.
      intros; rewrite <- Heq. auto.
    - intros S1 S2 Heq [Hdom [Heql Hsplit]]; split; [|split].
      + rewrite <- (Equal_Same_Dom S1 S2) by auto. auto.
      + intros; unfold get_heaptype in *; rewrite <- Heq; auto.
      + eapply IHSs; eauto.
        now apply minus_resp_Equal.
  Qed.
  
  Lemma minus_minus_minus_union {A} (M N P : map_util.M.t A) :
    M.Equal (minus (minus M N) P) (minus M (union N P)).
  Proof.
    intros x; unfold minus, union; rewrite !M.gmap2 by auto.
    destruct (M.find x N), (M.find x P), (M.find x M); auto.
  Qed.

  Lemma SplitHeapTypings_app' Ss Ss' S :
    SplitHeapTypings' (Ss ++ Ss') S ->
    exists S',
      SplitHeapTypings' Ss S' /\
      SplitHeapTypings' (S' :: Ss') S.
  Proof.
    revert S; induction Ss.
    - exists (M.empty _); split; [easy|].
      cbn; split; [rewrite Dom_ht_empty; auto with Ensembles_DB|split].
      + intros l; rewrite Dom_ht_empty; inversion 1.
      + eapply SplitHeapTypings'_resp_Equal; [|apply H].
        intros x; unfold minus; now rewrite M.gmap2, M.gempty by auto.
    - intros S [Hdom [Heq Hsplit]].
      specialize (IHSs _ Hsplit); destruct IHSs as [S' [HS' HSS']].
      exists (union a S'); cbn.
      split.
      + split; [rewrite Dom_ht_union; auto with Ensembles_DB|split].
        * intros l Hl.
          unfold get_heaptype, union; rewrite M.gmap2 by auto.
          destruct (M.find (N.succ_pos l) a) as [ht|] eqn:Hwat; auto.
          destruct Hl; congruence.
        * eapply SplitHeapTypings'_resp_Equal; [|eauto].
          intros x; unfold minus, union; rewrite !M.gmap2 by auto.
          destruct (M.find x a) eqn:Hfind; [|now destruct (M.find x S')].
          apply SplitHeapTypings'_dom  in HSS'.
          cbn in HSS'; rewrite Dom_ht_minus in HSS'.
          destruct (M.find x S') as [wat|] eqn:Hwat; auto.
          assert (x_in_S' : Pos.pred_N x \in Dom_ht S' :|: Union_list (map Dom_ht Ss')).
          { left; unfold Dom_ht, Dom_map, In. rewrite succ_pos_pred_N. eauto. }
          apply HSS' in x_in_S'; inv x_in_S'.
          contradiction H0; unfold Dom_ht, Dom_map, In.
          rewrite succ_pos_pred_N. eauto.
      + split; [|split]; destruct HSS' as [Hdom' [Heq' Hsplit']].
        * rewrite Dom_ht_union; apply Union_Included; auto.
          rewrite Dom_ht_minus in Hdom'; eapply Included_trans; [apply Hdom'|]; auto with Ensembles_DB.
        * intros l; rewrite Dom_ht_union; intros Hin.
          destruct (Decidable_Dom_ht a); destruct (Dec l) as [Hina|Hnotina].
          -- destruct Hina as [y Hy].
             replace (get_heaptype l (union a S')) with (get_heaptype l a).
             2:{ unfold union, get_heaptype; rewrite M.gmap2 by auto; now rewrite Hy. }
             apply Heq; now exists y.
          -- replace (get_heaptype l (union a S')) with (get_heaptype l S').
             2:{ unfold union, get_heaptype; rewrite M.gmap2 by auto.
                 destruct (M.find (N.succ_pos l) a) as [wat|] eqn:Hfind;
                   [contradiction Hnotina; now exists wat|].
                 now destruct (M.find (N.succ_pos l) S'). }
             replace (get_heaptype l S) with (get_heaptype l (minus S a)).
             2:{ unfold minus, get_heaptype; rewrite M.gmap2 by auto.
                 destruct (M.find (N.succ_pos l) a) as [wat|] eqn:Hfind;
                   [contradiction Hnotina; now exists wat|easy]. }
             apply Heq'; now inv Hin.
        * eapply SplitHeapTypings'_resp_Equal; [apply minus_minus_minus_union|apply Hsplit'].
  Qed.
  
  Lemma SplitHeapTypings_app Ss Ss' S :
    SplitHeapTypings (Ss ++ Ss') S ->
    exists S',
      SplitHeapTypings Ss S' /\
      SplitHeapTypings (S' :: Ss') S.
  Proof.
    rewrite !SplitHeapTypings_spec.
    intros H; apply SplitHeapTypings_app' in H.
    destruct H as [S' [HS' HS'S]].
    rewrite <- SplitHeapTypings_spec in *; eauto.
  Qed.
  
  Lemma SplitStoreTyping_app Ss Ss' S :
    SplitStoreTypings (Ss ++ Ss') S ->
    exists S',
      SplitStoreTypings Ss S' /\
      SplitStoreTypings (S' :: Ss') S. 
  Proof.
    intros Hs. inv Hs. eapply Forall_app in H. inv H.
    simpl in *. rewrite map_app in H0.
    eapply SplitHeapTypings_app in H0. destructAll.
    destruct S. 
    exists {| InstTyp := InstTyp; LinTyp := x; UnrTyp := UnrTyp |}.
    split.

    constructor. simpl. eassumption.
    eassumption.

    constructor; simpl. constructor; eauto.
    eassumption.
  Qed.

  (* Lemma Dom_ht_Node_None (a1 a2 : HeapTyping) : *)
  (*   Dom_ht (M.Node a1 None a2) <--> Dom_ht a1 :|: Dom_ht a2. *)
  (* Proof. *)
  (*   split; intros x Hin; inv Hin. *)
  (*   - destruct x; simpl in H. congruence.  *)
  (*     destruct p; simpl in H; eauto. *)
  (*     left; eexists; eauto.  *)
  (*     simpl in H.  *)
      
        
  Lemma SplitHeapTyping_empty Ss S :
    SplitHeapTypings Ss S ->
    M.is_empty S = true -> 
    Forall (fun s => M.is_empty s = true) Ss.
  Proof.
    intros H1 H2. inv H1. clear H0.
    rewrite Dom_ht_is_empty in H; eauto. clear H2.
    induction Ss.
    - now constructor.
    - simpl in H.
      assert (He1 := Union_Same_set_Empty_set_r _ _ H).
      assert (He2 := Union_Same_set_Empty_set_l _ _ H).

      constructor; [| now eauto ].
      clear H IHSs He1.

      eapply M.is_empty_1.
      intros x v Hget. 

      assert (Heq : (N.succ_pos (N.pos x - 1)) = x).
      { destruct x; simpl; try reflexivity.
        eapply POrderedType.Positive_as_OT.succ_pred_double. }
      
      assert (Hin : (N.pos x - 1)%N \in Empty_set _).
      { eapply He2. eexists. rewrite Heq. eassumption. }

      inv Hin. 
  Qed.


  Lemma SplitStoreTypings_Empty SS S :
    SplitStoreTypings SS S ->
    M.is_empty (LinTyp S) = true ->
    Forall (fun S => M.is_empty (LinTyp S) = true) SS.
  Proof.
    intros Hs He. inv Hs. simpl in *.
    
    eapply SplitHeapTyping_empty in H0; eauto.

    revert H0. clear. intros Hall. induction SS. simpl in *.
    - now constructor.
    - inv Hall; eauto.
  Qed. 

  
  Lemma SplitStoreTypings_Empty2 S1 S2 S : 
    SplitStoreTypings [S1; S2] S ->
    M.is_empty (LinTyp S) = true ->
    M.is_empty (LinTyp S1) = true /\ M.is_empty (LinTyp S2) = true.
  Proof.
    intros Hem His.
    eapply SplitStoreTypings_Empty in Hem; eauto. inv Hem.
    inv H2. eauto.
  Qed.

  Lemma SplitStoreTypings_Empty_eq S1 S2 S :
    SplitStoreTypings [S1; S2] S ->
    M.is_empty (LinTyp S1) = true ->
    StoreTyping_eq S2 S. 
  Proof.
    intros H1 Heq. inv H1. inv H. simpl in *.
    inv H3. inv H4. inv H5. split; eauto.
    split; eauto.

    assert (Heq1 := SplitHeapTypings_EmptyHeapTyping_l (LinTyp S1) (LinTyp S2) Heq). 

    eapply SplitHeapTypings_eq. eassumption. eassumption.
  Qed. 
    
 
  Lemma SplitHeapTypings_Singl H :
    SplitHeapTypings [H] H.
  Proof.
    constructor; simpl; eauto.
    now sets.
    intros. 
    constructor; eauto. constructor.
  Qed.
  
  Lemma SplitStoreTypings_Singl H :
    SplitStoreTypings [H] H.
  Proof.
    constructor; simpl; eauto.
    eapply SplitHeapTypings_Singl.
  Qed.
  
  Lemma SplitHeapTypings_Emp H :
    M.is_empty H = true ->
    SplitHeapTypings [] H.
  Proof.
    constructor; simpl; eauto.
    rewrite Dom_ht_is_empty; eauto. now sets. 
    intros.
    eapply M.is_empty_2 in H0. unfold M.Empty, M.MapsTo in H0.
    exfalso.
    eapply H0; eauto. 
  Qed.
  
  Lemma SplitStoreTypings_Emp H :
    M.is_empty (LinTyp H) = true ->        
    SplitStoreTypings [] H.
  Proof.
    constructor; simpl; eauto.
    eapply SplitHeapTypings_Emp; eauto.
  Qed.
        
  Lemma SplitHeapTypings_merge Ss1 Ss2 S1 S2 S :
    SplitHeapTypings Ss1 S1 ->
    SplitHeapTypings Ss2 S2 ->                        
    SplitHeapTypings [S1; S2] S ->
    SplitHeapTypings (Ss1 ++ Ss2) S. 
  Proof.
    intros H1 H2 H3. inv H1; inv H2; inv H3; simpl in *.
    constructor.
    rewrite map_app, Union_list_app. rewrite H, H1, <- H2. now sets.
    intros l1 ht Hget.
    eapply H5 in Hget.

    inv Hget.

    - inv H11. inv H14. eapply H0 in H8.
      
      eapply ExactlyInOne_app_l. eassumption.
      eapply ExactlyInOne_true.
      intros Hc. eapply H1 in Hc.
      inv Hc. unfold get_heaptype in *. congruence.

    - inv H12. inv H13. eapply H4 in H8. 

      assert (Hc : ~ In N (Union_list (map Dom_ht Ss1)) l1).
      intros Hc. eapply H in Hc. destruct Hc.
      unfold get_heaptype in *. congruence.

      eapply ExactlyInOne_true in Hc.

      eapply ExactlyInOne_app_r. eassumption. eassumption.

      inv H14. 
  Qed.

  Definition merge {A} (m1 m2 : map_util.M.t A) :=
    M.fold (fun x v m => M.add x v m) m1 m2. 

    
  Lemma merge_spec {A} (m1 m2 : map_util.M.t A) l v:
    M.find l (merge m1 m2) = Some v <-> (M.find l m1 = Some v \/ (M.find l m2 = Some v /\ M.find l m1 = None)).
  Proof.
    unfold merge.
    rewrite M.fold_1. simpl.
    assert (Hcorr := M.elements_correct m1).
    assert (Hcom := M.elements_complete m1).
    assert (Hnd := M.elements_3w m1). 
                     
    revert Hcorr Hcom Hnd. generalize (M.elements m1).
    intros l1; revert m1 m2; induction l1; intros m1 m2 Hcorr Hcom Hnd; simpl in *.
    - split; eauto; firstorder.
      right. split; eauto.
      destruct (M.find l m1) eqn:Hget; eauto.
      exfalso; eauto.
    - destruct a as [l' v']. simpl in *. rewrite IHl1 with (m1 := M.remove l' m1) ; eauto.

      + split.
        * intros H1. destruct (M.E.eq_dec l l'); subst.
          -- inv H1. rewrite M.grs in H. congruence.
             inv H. rewrite M.gss in H0. inv H0. 
             left. eapply Hcom. eauto.
          -- inv H1. rewrite M.gro in H; eauto.
             inv H. rewrite M.gso in H0; eauto.
             rewrite M.gro in H1; eauto.

        * inv Hnd. intros Hyp. destruct (M.E.eq_dec l l'); subst.
          -- inv Hyp.
             ++ eapply Hcorr in H. inv H. inv H0.
                right. split. rewrite M.gss. reflexivity. rewrite M.grs. reflexivity.

                exfalso. eapply H1. eapply SetoidList.InA_alt.
                eexists. split; eauto. reflexivity.

             ++  inv H. exfalso.
                 assert (Hc : M.find l' m1 = Some v').
                 eapply Hcom. now eauto. congruence.

          -- inv Hyp.
             ++ left. rewrite M.gro. eassumption. eassumption.

             ++ inv H. right. rewrite M.gso; eauto; rewrite M.gro; eauto.


      + intros.
        destruct (M.E.eq_dec i l'); subst.
        rewrite M.grs in H; congruence.
        rewrite M.gro in H; eauto.
        eapply Hcorr in H. inv H; eauto. inv H0; exfalso; eauto.

        
      + intros i1 v1 Hin1. 
        inv Hnd.
        destruct (M.E.eq_dec i1 l'); subst.
        * exfalso. eapply H1. eapply SetoidList.InA_alt.
          eexists. split; eauto. reflexivity.
        * rewrite M.gro; eauto.

      + inv Hnd; eauto.
  Qed. 

  Lemma merge_spec_None {A} (m1 m2 : map_util.M.t A) l :
    M.find l m1 = None ->
    M.find l m2 = None ->
    M.find l (merge m1 m2) = None.
  Proof.
    intros Hf1 Hf2.

    destruct (M.find l (merge m1 m2)) eqn:Heqb; eauto.

    eapply merge_spec in Heqb. inv Heqb; try congruence.
    inv H. congruence.
  Qed.

    
  Lemma Dom_map_merge {A} (m1 m2 : map_util.M.t A) :
    Dom_map (merge m1 m2) <--> Dom_map m1 :|: Dom_map m2.
  Proof.
    split; intros l Hin; inv Hin.
    - eapply merge_spec in H. inv H.

      + left. eexists; eauto.
      + inv H0. right; eexists; eauto. 

    - inv H. eexists. eapply merge_spec. eauto.

    - destruct (M.find l m1) eqn:Hg.

      + eexists. eapply merge_spec. left; eauto.

      + inv H. eexists; eauto. eapply merge_spec. eauto.
  Qed. 
      
  Lemma Dom_ht_merge {A} (m1 m2 : map_util.M.t A) :
    Dom_ht (merge m1 m2) <--> Dom_ht m1 :|: Dom_ht m2.
  Proof.
    unfold Dom_ht. split; intros l Hin; unfold In in *; simpl in *.
    - eapply Dom_map_merge in Hin. inv Hin; eauto.
      left. eassumption. right; eassumption.
    - eapply Dom_map_merge. inv Hin; eauto.
      left; eauto. right; eauto.
  Qed.
  

  Lemma SplitStoreTypings_merge Ss1 Ss2 S1 S2 S :
    SplitStoreTypings Ss1 S1 ->
    SplitStoreTypings Ss2 S2 ->                        
    SplitStoreTypings [S1; S2] S ->
    SplitStoreTypings (Ss1 ++ Ss2) S. 
  Proof.
    intros H1 H2 H3. inv H1. inv H2. simpl in *. inv H3. simpl in *.
    inv H2. inv H7. inv H8. inv H9. inv H10. 
    constructor.
    + eapply Forall_app. split.
      rewrite H2, H3. eassumption.
      rewrite H6, H7. eassumption.
    + simpl. rewrite map_app.
      eapply SplitHeapTypings_merge; eassumption. 
  Qed.

  Lemma SplitHeapTypings_assoc H1 H2 H3 H4 H :
    SplitHeapTypings [H1; H2] H3 ->
    SplitHeapTypings [H3; H4] H ->

    SplitHeapTypings [H2; H4] (merge H2 H4) /\
    SplitHeapTypings [H1; (merge H2 H4)] H.
  Proof.
    intros Hs1 Hs2. inv Hs1. inv Hs2. 

    split.

    - constructor. simpl.
      rewrite Dom_ht_merge. sets.
      
      intros l ht Hget. eapply merge_spec in Hget. inv Hget.

      + econstructor. eassumption.
        econstructor; [| econstructor ].
        
        
        assert (Hc' : exists v, get_heaptype l H3 = Some v).
        { eapply H0. simpl. right. left. eexists; eauto.  }
        
        destructAll. assert (Hg := H9). eapply H5 in H9. inv H9.

        inv H16. unfold get_heaptype in H17. congruence.
        
        inv H17; unfold get_heaptype in *.
        2:{ inv H18. }

        assert (Hc' : exists v, get_heaptype l H = Some v).
        { eapply H6. simpl. left. eexists; eauto.  }
        destructAll.

        eapply H7 in H9. inv H9.
        inv H19. eassumption.

        unfold get_heaptype in *. congruence.

      + inv H8. constructor 3. eassumption. constructor. eassumption. constructor. 

    - constructor. simpl.
      rewrite Dom_ht_merge. normalize_sets.
      rewrite <- H6. simpl. normalize_sets.
      rewrite <- H0. simpl. normalize_sets. now sets.

      intros l ht Hget. specialize (H5 l ht). specialize (H7 l ht Hget).

      inv H7.

      + eapply H5 in H11. inv H14. inv H16. inv H11.
        * inv H14. inv H17. constructor. eassumption.
          constructor.
          eapply merge_spec_None; eauto.

          constructor.
          
        * inv H16. inv H13.

          -- constructor 3. eassumption.
             constructor. unfold get_heaptype.
             eapply merge_spec. now left. constructor.

          -- inv H17.

      + inv H15.

        * inv H13. 
          constructor 3.

          edestruct (get_heaptype l H1) eqn:Hc; eauto. exfalso.
          assert (Hc' : exists v, get_heaptype l H3 = Some v).
          eapply H0. simpl. left. eexists; eauto.
          destructAll. congruence.

          constructor. unfold get_heaptype.
          eapply merge_spec. right. split; eauto.

          destruct (M.find (N.succ_pos l) H2) eqn:Hc; eauto.

          exfalso. 
          assert (Hc' : exists v, get_heaptype l H3 = Some v).
          eapply H0. simpl. right. left. eexists; eauto.
          destructAll. congruence.

          constructor.

        * inv H16.
  Qed.

  
  Lemma SplitStoreTypings_assoc S1 S2 S3 S4 S :
    SplitStoreTypings [S1; S2] S3 ->
    SplitStoreTypings [S3; S4] S ->

    exists S',
      SplitStoreTypings [S2; S4] S' /\
      SplitStoreTypings [S1; S'] S.
  Proof.
    intros H1 H2.
    destruct H1; destruct H2.
    destruct S1; destruct S2; destruct S3; destruct S4; destruct S.
    simpl in *. inv H. inv H1. inv H5. inv H6. inv H4. simpl in *. 
    inv H3. inv H7. inv H3. inv H4. inv H5.

    edestruct SplitHeapTypings_assoc. eapply H0. eapply H2.
    
    eexists {| InstTyp := InstTyp2; LinTyp := (merge LinTyp0 LinTyp2); UnrTyp := UnrTyp2 |}.
    split.

    - constructor. constructor; eauto. simpl. eassumption.
    - constructor. constructor; eauto. simpl. eassumption.
  Qed.


  Lemma SplitHeapTypings_Empty' SS S :
    SplitHeapTypings SS S ->
    Forall (fun S => M.is_empty S = true) SS ->
    M.is_empty S = true.        
  Proof.
    revert S; induction SS.
    - intros S H; apply SplitHeapTypings_nil in H.
      intros []; auto.
    - intros S H. apply SplitHeapTypings_cons in H.
      intros Hforall; inv Hforall; apply IHSS in H; auto.
      apply M.is_empty_1; rewrite M.Empty_alt.
      apply M.is_empty_2 in H; apply M.is_empty_2 in H2.
      rewrite M.Empty_alt in *.
      unfold minus in *.
      intros x; specialize (H x); specialize (H2 x).
      rewrite M.gmap2 in * by auto. rewrite H2 in *. auto.
  Qed.

  
  Lemma SplitStoreTypings_Empty' SS S :
    SplitStoreTypings SS S ->
    Forall (fun S => M.is_empty (LinTyp S) = true) SS ->
    M.is_empty (LinTyp S) = true.        
  Proof.
    intros Hs Hall. inv Hs. simpl in *.
    eapply SplitHeapTypings_Empty'; eauto.
    revert Hall. clear. intros Hall. induction SS. simpl in *.
    - now constructor.
    - inv Hall; eauto. simpl. constructor; eauto.
  Qed.

  Lemma is_empty_LinTyp S : M.is_empty (LinTyp (empty_LinTyp S)) = true.
  Proof.
    destruct S. reflexivity.
  Qed.

    Lemma SplitHeapTypings_map_eq SS S1 S2 :
    SplitHeapTypings SS S1 ->
    eq_map S1 S2 ->
    SplitHeapTypings SS S2.
  Proof.
    intros Hs1 Heq.
    inv Hs1. constructor.

    - rewrite H.

      split; intros x [v Hin].

      unfold eq_map, get_heaptype in *. erewrite Heq in Hin.
      eexists. eassumption.
      
      unfold eq_map, get_heaptype in *. erewrite <- Heq in Hin.
      eexists. eassumption.


    - intros.
      eapply H0. rewrite Heq.
      eassumption.
  Qed. 

    
  Lemma SplitStoreTyping_eq SS S1 S2 :
    SplitStoreTypings SS S1 ->
    StoreTyping_eq S1 S2 ->
    SplitStoreTypings SS S2.
  Proof.
    intros H1 H2.
    destruct H1. simpl in *. destruct H2. destructAll.
    constructor.
    rewrite <- H1, <- H3. eassumption.
    simpl.

    eapply SplitHeapTypings_map_eq; eassumption.
  Qed.


  Global Instance StoreTyping_Equiv : Equivalence StoreTyping_eq.
  Proof.
    econstructor.
    - intros []. split; eauto. split; eauto.
      simpl. unfold eq_map. reflexivity.
    - intros [] [] H. inv H. destructAll.
      simpl in *. subst. split; eauto.
      split.
      intros x. now simpl; eauto.
      reflexivity.
    - intros [] [] [] H1 H2. inv H1; inv H2. destructAll.
      simpl in *; subst.
      split; eauto.
      split.
      intros x. simpl; eauto. rewrite H0; eauto.
      reflexivity.
  Qed.   

    Lemma ExactlyInOne_permut b l ht S1 S2:
    ExactlyInOne b l ht S1 ->
    Permutation.Permutation S1 S2 ->
    ExactlyInOne b l ht S2.
  Proof.
    intros Hex Hperm. revert b l ht Hex; induction Hperm; intros b ptr ht Hex.
    - eassumption.
    - inv Hex.
      + constructor; eauto.
      + constructor; eauto.
    - inv Hex.
      + inv H6.
        eapply NotInHead. eassumption.
        econstructor. eassumption. eassumption.
      + inv H6.
        * econstructor; eauto.
          econstructor; eauto.
        * econstructor; eauto.
          econstructor; eauto.
    - eauto.
  Qed. 
        
  Lemma SplitHeapTypings_permut S1 S2 S :
    Permutation.Permutation S1 S2 ->
    SplitHeapTypings S1 S ->
    SplitHeapTypings S2 S.
  Proof.
    intros H Hs. inv Hs.
    constructor.
    - rewrite <- H0.
      eapply Union_list_permut.
      eauto.
      eapply Permutation.Permutation_map.
      symmetry. eassumption. 
    - intros.
      eapply ExactlyInOne_permut; eauto.
  Qed.

  Lemma SplitStoreTypings_permut S1 S2 S :
    Permutation.Permutation S1 S2 ->
    SplitStoreTypings S1 S ->
    SplitStoreTypings S2 S.
  Proof.
    intros H Hs. inv Hs. simpl in *.
    constructor. 
    - eapply Permutation.Permutation_Forall; eauto.
    - simpl.
      eapply SplitHeapTypings_permut; [| eassumption ].
      eapply Permutation.Permutation_map.
      eassumption.
  Qed.

  Lemma SplitStoreTypings_comm' S1 S2 S :
    SplitStoreTypings (S1 ++ S2) S ->
    SplitStoreTypings (S2 ++ S1) S.
  Proof.
    eapply SplitStoreTypings_permut; eauto.
    eapply Permutation.Permutation_app_comm.
  Qed. 

  Lemma SplitHeapTypings_merge' S1 S2 S3 S :
    SplitHeapTypings S1 S2 ->
    SplitHeapTypings (S2 :: S3) S ->
    SplitHeapTypings (S1 ++ S3) S. 
  Proof.
    intros H1 H2.
    inv H1. inv H2. simpl in *.
    split.
    - rewrite map_app. rewrite Union_list_app. rewrite H.
      eassumption.
    - intros.
      eapply H3 in H2. inv H2.
      + eapply ExactlyInOne_app_l. now eauto. eassumption. 
      + eapply ExactlyInOne_app_r; eauto.
        eapply ExactlyInOne_true.
        intros Hin. eapply H in Hin.
        destruct Hin. unfold get_heaptype in H10. congruence.
  Qed.

  Lemma SplitStoreTypings_merge' S1 S2 S3 S :
    SplitStoreTypings S1 S2 ->
    SplitStoreTypings (S2 :: S3) S ->
    SplitStoreTypings (S1 ++ S3) S. 
  Proof.
    intros H1 H2.
    inv H1. inv H2. simpl in *.
    split.
    - eapply Forall_app. inv H1.
      destructAll. rewrite <- H1, <- H2 in *. 
      split; eauto.
    - simpl.
      rewrite map_app. eapply SplitHeapTypings_merge'; eauto.
  Qed.


  Lemma SplitHeapTypings_empty_app S1 S2 S :
    SplitStoreTypings (S1 ++ S2) S ->
    Forall (fun S => M.is_empty (LinTyp S) = true) S1 ->
    SplitStoreTypings S2 S.
  Proof.
    intros H1 Hall.

    edestruct SplitStoreTyping_app.
    eassumption. destructAll. 
    

    edestruct SplitStoreTyping_app.
    eapply SplitStoreTypings_comm'.
    replace (x :: S2) with ([x] ++ S2) in H0 by reflexivity. now eapply H0.
    destruct H2.

    eapply SplitStoreTypings_comm in H3. 
    eapply SplitStoreTypings_Empty_eq in H3.

    eapply SplitStoreTyping_eq; [| eassumption ]. eassumption.

    eapply SplitStoreTypings_Empty'.

    eassumption. eassumption.
  Qed.

  Lemma Dom_ht_is_empty_list A (S1 : list (map_util.M.t A)) :
    Forall (fun S => M.is_empty S = true) S1 ->
    Union_list (map Dom_ht S1) <--> (Ensembles.Empty_set _).
  Proof.
    intros Hall.
    induction Hall.
    - reflexivity.
    - simpl.
      rewrite IHHall. rewrite Dom_ht_is_empty.
      sets. eassumption.
  Qed.
  
  
  Lemma SplitHeapTypings_empty_app' S1 S2 S :
    SplitHeapTypings S2 S ->
    Forall (fun S => M.is_empty S = true) S1 ->
    SplitHeapTypings (S1 ++ S2) S.
  Proof.   
    intros H1 Hall.
    inv H1.
    constructor.
    - rewrite map_app, Union_list_app.
      rewrite H.
      rewrite Dom_ht_is_empty_list. now sets.
      eassumption.
    - intros. eapply ExactlyInOne_app_r; eauto.

      eapply ExactlyInOne_true.
      rewrite Dom_ht_is_empty_list. intros Hc. now inv Hc.
      eassumption.
  Qed.
  

  Lemma SplitStoreTypings_repeat S j :
    HasEmptyLinTyping S ->
    SplitStoreTypings (repeat S j) S.
  Proof.
    induction j; intros H.
    - eapply SplitStoreTypings_Emp.
      unfold HasEmptyLinTyping in *. destruct S; assumption.
    - assert (He := H). eapply IHj in H.
      simpl.

      replace (S :: repeat S j) with ([S] ++ repeat S j) by reflexivity.

      { split.

        eapply Forall_app. split; eauto.

        { clear. induction j. now constructor.
          simpl. constructor; eauto. }
        
        simpl.
        replace (LinTyp S :: map LinTyp (repeat S j)) with
            ([LinTyp S] ++ map LinTyp (repeat S j)) by reflexivity.

        eapply SplitHeapTypings_empty_app'.

        inv H. eassumption.

        constructor. destruct S. eassumption.

        now constructor. }
  Qed.
  
  Lemma eq_dec_positive:
    forall (p1 p2: positive), (p1 = p2) \/ (p1 <> p2).
  Proof.
    intro. induction p1; intros; destruct p2.
    - specialize (IHp1 p2). destruct IHp1.
      left. f_equal. auto. right. intro. apply H. inversion H0. auto.
    - right. intro. inversion H.
    - right. intro. inversion H.
    - right. intro. inversion H.
    - specialize (IHp1 p2). destruct IHp1.
      left. f_equal. auto.
      right. intro. apply H. injection H0. auto.
    - right. intro. inversion H.
    - right. intro. inversion H.
    - right. intro. inversion H.
    - left. auto.
  Qed.

  Lemma in_map_inv : forall {A B} {f : A -> B} {el} {l},
      List.In el (map f l) ->
      exists el', el = f el' /\ List.In el' l.
  Proof.
    intros. generalize dependent el.
    induction l; intros; inversion H; subst; simpl in *; eauto.
    specialize (IHl _ H0). destruct IHl. destruct H1. eauto.
  Qed.

  Lemma in_permut : forall {A} {el : A} {l},
    List.In el l ->
    exists l', Permutation.Permutation l (el :: l').
  Proof.
    intros. generalize dependent el.
    induction l; intros; inversion H; subst; auto.
    eexists; econstructor; auto.
    specialize (IHl _ H0). destruct IHl.
    exists (a :: x).
    destruct l. inversion H; subst; inversion H0.
    apply Permutation.Permutation_sym.
    eapply Permutation.perm_trans. eapply Permutation.perm_swap.
    apply Permutation.perm_skip.
    apply Permutation.Permutation_sym. auto.
  Qed.

  Lemma set_nth_trivial : forall {A l idx el},
      length l <= idx ->
      @set_nth A l idx el = l.
  Proof.
    intros A l.
    induction l; intros; destruct idx; inversion H; subst; simpl in *; eauto;
      f_equal; rewrite IHl; auto; lia. 
  Qed.

  Lemma In_set_nth : forall {A l idx el el'},
    @List.In A el' (set_nth l idx el) ->
    (el' = el \/ List.In el' l).
  Proof.
    intros A l. induction l; intros; destruct idx; inversion H; subst; simpl in *;
      eauto.
    specialize (IHl _ _ _ H0). destruct IHl. auto. auto.
  Qed.

  Lemma nth_error_set_nth : forall {A l idx} el,
      idx < length l ->
      @nth_error A (set_nth l idx el) idx = Some el.
  Proof.
    intros A l. induction l; intros; destruct idx; inversion H; subst;
      simpl in *; eauto; rewrite Nat.sub_0_r in *; eapply IHl; lia.
  Qed.

  Fixpoint remove_nth {A} (l : list A) (n : nat) : list A :=
    match l with
    | [] => []
    | x :: l' => match n with
                 | 0 => l'
                 | Datatypes.S n' => x :: (remove_nth l' n')
                 end
    end.

  Lemma remove_nth_set_nth : forall {A} l idx el,
      @remove_nth A (set_nth l idx el) idx = remove_nth l idx.
  Proof.
    intros A l. induction l; intros; destruct idx; simpl; auto.
    f_equal. rewrite Nat.sub_0_r. eauto.
  Qed.

  Lemma remove_nth_map : forall {A B} {l : list A} {f : A -> B} {idx},
      remove_nth (map f l) idx = map f (remove_nth l idx).
    Proof.
      intros A B l.
      induction l; intros; destruct idx; simpl; eauto.
      f_equal; eauto.
    Qed.

  Lemma remove_nth_app1 : forall {A} {l1 : list A} {l2 idx},
      idx < length l1 ->
      remove_nth (l1 ++ l2) idx = (remove_nth l1 idx) ++ l2.
  Proof.
    intros A l1.
    induction l1; intros; destruct idx; simpl in *; inversion H; subst; eauto;
      f_equal; eapply IHl1; lia.
  Qed.

  Lemma In_remove_nth_weak : forall {A} {idx el} {l : list A},
      List.In el (remove_nth l idx) ->
      List.In el l.
  Proof.
    induction idx.
    - intros.
      destruct l; simpl in *; auto.
    - intros.
      destruct l; simpl in *; auto.
      match goal with
      | [ H : _ \/ _ |- _ ] => case H; intros; subst
      end.
      -- left; auto.
      -- right; eauto.
  Qed.

  Lemma NoDup_remove_nth : forall {A} {l : list A} idx,
      NoDup l ->
      NoDup (remove_nth l idx).
  Proof.
    intros A l idx.
    revert A l.
    induction idx.
    - intros.
      destruct l; simpl; auto.
      match goal with
      | [ H : NoDup _ |- _ ] => inversion H; auto
      end.
    - intros.
      destruct l; simpl; auto.
      match goal with
      | [ H : NoDup _ |- _ ] => inversion H; subst; simpl in *
      end.
      constructor; eauto.
      intro.
      match goal with
      | [ H : List.In _ (remove_nth _ _) |- _ ] =>
        apply In_remove_nth_weak in H
      end.
      eauto.
  Qed.

  Lemma In_NoDup_remove_nth : forall {A} {idx} {l : list A} {el el'},
      NoDup l ->
      nth_error l idx = Some el ->
      List.In el' (remove_nth l idx) <-> (List.In el' l /\ el' <> el).
  Proof.
    induction idx.
    - intros.
      destruct l; simpl in *.
      1:{
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        end.
      }
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : NoDup (_ :: _) |- _ ] => inversion H; subst
      end.
      split; intros.
      -- split; [ right; auto | ].
         intro; subst.
         eauto.
      -- destructAll.
         match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; subst; auto
         end.
         exfalso; eauto.
    - intros.
      destruct l; simpl in *.
      1:{
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        end.
      }
      match goal with
      | [ H : NoDup (_ :: _) |- _ ] => inversion H; subst
      end.
      erewrite IHidx; eauto.
      split; intros.
      -- match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; subst
         end.
         --- split; [ left; auto | ].
             intro; subst.
             match goal with
             | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply nth_error_In in H
             end.
             eauto.
         --- destructAll.
             split; auto.
      -- destructAll.
         match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; subst
         end.
         --- left; auto.
         --- right; auto.
  Qed.

  Lemma Permutation_remove_nth : forall {A} {idx el} {l : list A},
      nth_error l idx = Some el ->
      Permutation.Permutation l (el :: remove_nth l idx).
  Proof.
    induction idx; intros.
    - destruct l; simpl in *.
      1:{
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        end.
      }
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst
      end.
      auto.
    - destruct l; simpl in *.
      1:{
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        end.
      }
      eapply Permutation.Permutation_trans.
      -- apply Permutation.perm_skip.
         eapply IHidx; eauto.
      -- apply Permutation.perm_swap.
  Qed.

  Lemma SplitStoreTypings_cons' x Ss S :
    SplitStoreTypings (x :: Ss) S ->
    exists S',
      InstTyp S' = InstTyp S /\
      UnrTyp S' = UnrTyp S /\
      SplitStoreTypings Ss S'.
  Proof.
    intros Hsplit. 
    edestruct SplitStoreTypings_cons as [S' H]. eassumption.
    destruct S'. destruct x. 
    inv Hsplit. simpl in *. inv H0. destructAll.

    simpl in *. 
    eexists {| InstTyp := InstTyp0; LinTyp := LinTyp; UnrTyp := UnrTyp0 |}.
    simpl. split. congruence. split. congruence.

    destruct Ss.
    - constructor. now constructor.        
      inv H. simpl in *. eassumption.

    - inv H. simpl in *.
      inv H5. destructAll.
      constructor. simpl. rewrite H, H0 in *. 
      constructor. now eauto. eassumption.
      simpl. eassumption.
  Qed.

  Lemma SplitHeapTypings_Permutation : forall H1 H2 H,
      Permutation.Permutation H1 H2 ->
      SplitHeapTypings H1 H ->
      SplitHeapTypings H2 H.
  Proof.
    unfold SplitHeapTypings.
    intros. destruct H3. induction H0; split; auto.
    - eapply Same_set_trans.
      eapply Union_list_permut.
      eapply Permutation.Permutation_map. apply Permutation.perm_skip.
      apply Permutation.Permutation_sym. eauto.
      auto.
    - intros. 
      eapply ExactlyInOne_permut. apply H4; auto.
      apply Permutation.perm_skip. auto.
    - eapply Same_set_trans.
      eapply Union_list_permut.
      eapply Permutation.Permutation_map. apply Permutation.perm_swap.
      auto.
    - intros. eapply ExactlyInOne_permut. apply H4; auto.
      apply Permutation.perm_swap.
    - eapply Same_set_trans.
      eapply Union_list_permut.
      eapply Permutation.Permutation_map. eapply Permutation.perm_trans.
      apply Permutation.Permutation_sym. eauto. apply Permutation.Permutation_sym. eauto.
      auto.
    - intros. eapply ExactlyInOne_permut. eauto.
      eapply Permutation.perm_trans; eauto.
  Qed.          

  Lemma get_heaptype_Some_Dom_ht: forall {A} l S,
        (exists ht, get_heaptype l S = Some ht) <->
        Ensembles.In N (@Dom_ht A S) l.
  Proof.
    unfold get_heaptype. unfold Dom_ht.
    unfold Ensembles.In. unfold Dom_map.
    intros. split; intros; auto.
  Qed.

  Lemma get_heaptype_Some_imp_Dom_ht: forall {A} l S ht,
      get_heaptype l S = Some ht -> Ensembles.In N (@Dom_ht A S) l.
  Proof.
    intros.
    rewrite <-  get_heaptype_Some_Dom_ht.
    eexists; eauto.
  Qed.

  Theorem get_heaptype_In_Union_list: forall {A} Ss S1 l1 t1,
      get_heaptype l1 S1 = Some t1 ->
      List.In S1 Ss ->
      Ensembles.In N (Union_list (map (@Dom_ht A) Ss)) l1.
  Proof.
    intros A Ss. induction Ss; intros; inversion H0.
    - subst. simpl. 
      apply Ensembles.Union_introl.
      eapply get_heaptype_Some_imp_Dom_ht. eauto.
    - simpl.
      apply Ensembles.Union_intror.
      eapply IHSs; eauto.
  Qed.

  Theorem ExactlyInOne_true_get_heaptype: forall Ss S l1 x ht,
      ExactlyInOne true l1 ht Ss ->
      List.In S Ss ->
      get_heaptype l1 S = Some x ->
      False.
  Proof.
    intros Ss. induction Ss; intros; inversion H0; subst.
    - inversion H; subst. rewrite H1 in H8. inversion H8.
    - inversion H; subst. eapply IHSs; eauto.
  Qed.

  Theorem ExactlyInOne_get_heaptype: forall Ss S l1 ht x,
      ExactlyInOne false l1 x Ss ->
      get_heaptype l1 S = Some ht ->
      List.In S Ss ->
      x = ht.
  Proof.
    intros Ss. induction Ss; intros; inversion H1; subst; auto.
    - inversion H; subst. rewrite H5 in H0. injection H0. auto. rewrite H8 in H0.
      inversion H0.
    - inversion H; subst.
      + exfalso. eapply ExactlyInOne_true_get_heaptype.
        exact H9. exact H2. eauto.
      + eapply IHSs; eauto.
  Qed.

  Lemma SplitHeapTypings_get_heaptype_LinTyp : forall {Ss S1 S2 l1 t1},
      get_heaptype l1 S1 = Some t1 ->
      List.In S1 Ss ->
      SplitHeapTypings Ss S2 ->
      get_heaptype l1 S2 = Some t1.
  Proof.
    intros. inversion H1. clear H1.
    assert (h: Ensembles.In N (Dom_ht S2) l1).
    { rewrite <- H2. eapply get_heaptype_In_Union_list; eauto. }
    rewrite <- get_heaptype_Some_Dom_ht in h. destruct h.
    specialize (H3 l1 x H1).
    rewrite H1. f_equal.
    eapply ExactlyInOne_get_heaptype; eauto.
  Qed.  

  Lemma SplitStoreTypings_get_heaptype_LinTyp : forall {Ss S1 S2 l1 t1},
      get_heaptype l1 (LinTyp S1) = Some t1 ->
      List.In S1 Ss ->
      SplitStoreTypings Ss S2 ->
      get_heaptype l1 (LinTyp S2) = Some t1.
  Proof.
    intros.
    eapply SplitHeapTypings_get_heaptype_LinTyp; [ eauto | | ].
    - apply in_map; eauto.
    - unfold SplitStoreTypings in *.
      destructAll; auto.
  Qed.

  Lemma SplitStoreTypings_get_heaptype_LinTyp_gen : forall {loc lt ht Ss S},
      get_heaptype loc lt = Some ht ->
      List.In lt (map LinTyp Ss) ->
      SplitStoreTypings Ss S ->
      get_heaptype loc (LinTyp S) = Some ht.
  Proof.
    intros.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] =>
      apply in_map_inv in H; destructAll
    end.
    eapply SplitStoreTypings_get_heaptype_LinTyp; eauto.
  Qed.

  Definition merge_heaps {A} h1 h2 :=
    M.fold (@M.add A) h1 h2.

  Definition disjoint_heaps {A} h1 h2 :=
    forall l,
      ((exists ht : A, get_heaptype l h1 = Some ht) -> get_heaptype l h2 = None) /\
      ((exists ht : A, get_heaptype l h2 = Some ht) -> get_heaptype l h1 = None).

  Definition disjoint_from_list {A} h l :=
    Forall (fun h' => @disjoint_heaps A h h') l.

  Definition remove_heap
             {A} (h1 : typing.M.t A) (h2 : typing.M.t A) :=
    M.fold (fun k _ acc => M.remove k acc) h1 h2.

  Lemma disjoint_heaps_or : forall {A h1 h2},
      (forall l, (exists ht, get_heaptype l h1 = Some ht) -> get_heaptype l h2 = None) \/
      (forall l, (exists ht, get_heaptype l h2 = Some ht) -> get_heaptype l h1 = None) ->
      @disjoint_heaps A h1 h2.
  Proof.
    intros.
    constructor.
    all:
      match goal with
      | [ H : _ \/ _ |- _ ] =>
        case H
      end.
    all: intros; eauto.
    all: destructAll.
    all:
      match goal with
      | [ |- ?A = None ] =>
        remember A as opt;
        generalize (eq_sym Heqopt);
        case opt; [ | auto ]
      end.
    all: intros.
    all:
      match goal with
      | [ H : forall _, _ -> get_heaptype _ ?H = None,
          H' : get_heaptype ?L ?H = Some _ |- _ ] =>
        let H'' := fresh "H" in
        assert (H'' : get_heaptype L H = None);
        [ | rewrite H'' in H'; inversion H' ]
      end.
    all: eauto.
  Qed.
  
  Lemma disjoint_heaps_comm : forall {A h1 h2},
      @disjoint_heaps A h1 h2 <->
      @disjoint_heaps A h2 h1.
  Proof.
    intros; constructor.
    all: intros.
    all: apply disjoint_heaps_or.
    all: unfold disjoint_heaps in *.
    all: left.
    all: intros; destructAll.
    all:
      match goal with
      | [ H : forall _, _ |- get_heaptype ?L _ = _ ] =>
        specialize (H L); destructAll
      end.
    all:
      match goal with
      | [ H : ?A -> ?B |- ?B ] => apply H
      end.
    all: eexists; eauto.
  Qed.

  Lemma find_add : forall {A h l ht l' ht'},
      @map_util.M.find A l h = Some ht ->
      ((l = l' /\
        map_util.M.find l (M.add l' ht' h) = Some ht') \/
       (l <> l' /\
        map_util.M.find l (M.add l' ht' h) = Some ht)).
  Proof.
    intros.
    match goal with
    | [ |- context[map_util.M.find ?L (M.add ?LP _ _)] ] =>
      let H' := fresh "H" in
      assert (H' : L = LP \/ L <> LP) by apply eq_dec_positive;
      case H'; intros; subst
    end.
    - left; split; auto.
      rewrite M.gss; auto.
    - right; split; auto.
      rewrite M.gso; auto.
  Qed.

  Lemma find_add_inv : forall {A h l ht l' ht'},
      @map_util.M.find A l (M.add l' ht' h) = Some ht ->
      ((l = l' /\ ht = ht') \/
       (l <> l' /\
        map_util.M.find l h = Some ht)).
  Proof.
    intros.
    match goal with
    | [ H : context[map_util.M.find ?L (M.add ?LP _ _)] |- _ ] =>
      let H' := fresh "H" in
      assert (H' : L = LP \/ L <> LP) by apply eq_dec_positive;
      case H'; intros; subst;
      [ left | right ]; split; auto
    end.
    - rewrite M.gss in *.
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; auto
      end.
    - rewrite M.gso in *; auto.
  Qed.

  Lemma Dom_ht_merge_heaps : forall {A} h1 h2,
      Dom_ht h1 :|: Dom_ht h2 <-->
      Dom_ht (@merge_heaps A h1 h2).
  Proof.
    intros.
    unfold merge_heaps.
    apply fold_rec_bis.
    - intros.
      eapply Same_set_trans; [ | eauto ].
      apply Same_set_Union_compat_l.
      unfold Dom_ht.
      unfold Dom_map.
      unfold Ensembles.Same_set.
      unfold Ensembles.Included.
      unfold Ensembles.In.
      split.
      all: intros; destructAll.
      all:
        match goal with
        | [ H : map_util.M.Equal _ _,
            H' : map_util.M.find _ _ = Some _ |- _ ] =>
          unfold map_util.M.Equal in H;
          rewrite H in H' || rewrite <-H in H'
        end.
      all: eexists; eauto.
    - intros.
      eapply Same_set_trans; [ | apply Union_Empty_set_neut_l ].
      eapply Same_set_Union_compat_l.
      unfold Dom_ht.
      unfold Dom_map.
      unfold Ensembles.Same_set.
      unfold Ensembles.Included.
      unfold Ensembles.In.
      split.
      -- intros; destructAll.
         rewrite M.gempty in *.
         match goal with
         | [ H : None = Some _ |- _ ] => inversion H
         end.
      -- intros.
         match goal with
         | [ H : Ensembles.Empty_set _ _ |- _ ] =>
           inversion H
         end.
    - intros.
      unfold Dom_ht in *.
      unfold Dom_map in *.
      unfold Ensembles.Same_set in *.
      unfold Ensembles.Included in *.
      unfold Ensembles.In in *.
      split; intros.
      -- match goal with
         | [ H : (_ :|: _) _ |- _ ] =>
           inversion H; subst; unfold Ensembles.In in *;
           simpl in *; destructAll
         end.
         --- match goal with
             | [ H : map_util.M.find _ (map_util.M.add _ _ _) = Some _ |- _ ] =>
               apply find_add_inv in H;
               case H; intros; destructAll; subst
             end.
             ---- rewrite M.gss; eexists; eauto.
             ---- rewrite M.gso; auto.
                  match goal with
                  | [ H : forall _, _ -> exists ht, map_util.M.find (N.succ_pos _) ?MP = Some ht
                      |- context[M.find _ ?MP] ] =>
                    apply H
                  end.
                  left.
                  unfold Ensembles.In.
                  eexists; eauto.
         --- match goal with
             | [ H : forall _, (?S1 :|: ?S2) _ -> _,
                 H' : map_util.M.find (N.succ_pos ?L) _ = Some _ |- _ ] =>
               let H'' := fresh "H" in
               assert (H'' : (S1 :|: S2) L);
               [ | specialize (H _ H'') ]
             end.
             { right.
               unfold Ensembles.In.
               eexists; eauto. }
             destructAll.
             match goal with
             | [ H : map_util.M.find _ ?A = Some _
                 |- context[M.add ?L ?HT ?A] ] =>
               apply (find_add (l':=L) (ht':=HT)) in H;
               case H; intros; destructAll; eexists; eauto
             end.
      -- destructAll.
         match goal with
         | [ H : map_util.M.find _ (map_util.M.add _ _ _) = Some _ |- _ ] =>
           apply find_add_inv in H;
           case H; intros; destructAll; subst
         end.
         --- left.
             unfold Ensembles.In.
             rewrite M.gss.
             eexists; eauto.
         --- match goal with
             | [ H : forall _, (exists ht, map_util.M.find _ ?MP = Some _) -> _,
                 H' : map_util.M.find _ ?MP = Some _ |- _ ] =>
               specialize (H _ (ex_intro _ _ H'));
               inversion H; subst;
               unfold Ensembles.In in *; destructAll; simpl in *;
               [ | right; eexists; eauto ]
             end.
             left.
             unfold Ensembles.In.
             match goal with
             | [ H : map_util.M.find _ ?MP = Some _
                 |- context[map_util.M.add ?L ?HT ?MP] ] =>
               apply (find_add (l':=L) (ht':=HT)) in H;
               case H; intros; destructAll; eexists; eauto
             end.
  Qed.  

  Lemma find_merge_heaps : forall {A l h1 h2 ht},
      M.find l (@merge_heaps A h1 h2) = Some ht ->
      M.find l h1 = Some ht \/
      M.find l h2 = Some ht.
  Proof.
    intros A l h1 h2 ht.
    unfold merge_heaps.
    apply fold_rec_bis.
    - intros.
      match goal with
      | [ H : ?A -> ?B, H' : ?A |- _ ] =>
        specialize (H H'); case H; intros
      end.
      -- left.
         match goal with
         | [ H : map_util.M.Equal _ _ |- _ ] =>
           unfold map_util.M.Equal in H; rewrite <-H
         end.
         auto.
      -- right; auto.
    - intros; right; auto.
    - intros.
      match goal with
      | [ H : M.find _ (M.add _ _ _) = Some _ |- _ ] =>
        apply find_add_inv in H;
        case H; intros; destructAll; subst
      end.
      -- left; rewrite M.gss; auto.
      -- rewrite M.gso; auto.
  Qed.   

  Ltac apply_find_merge_heaps :=
    match goal with
    | [ H : M.find _ (merge_heaps _ _) = Some _ |- _ ] =>
      apply find_merge_heaps in H
    | [ H : get_heaptype _ (merge_heaps _ _) = Some _ |- _ ] =>
      apply find_merge_heaps in H
    end.
  Ltac apply_find_merge_heaps_case :=
    match goal with
    | [ H : M.find _ (merge_heaps _ _) = Some _ |- _ ] =>
      apply find_merge_heaps in H; case H
    | [ H : get_heaptype _ (merge_heaps _ _) = Some _ |- _ ] =>
      apply find_merge_heaps in H; case H
    end.

  Lemma find_remove_heap : forall {A l h1 h2 ht},
      M.find l (@remove_heap A h1 h2) = Some ht <->
      M.find l h1 = None /\
      M.find l h2 = Some ht.
  Proof.
    intros.
    unfold remove_heap.
    apply fold_rec_bis; intros.
    - match goal with
      | [ H : map_util.M.Equal _ _ |- _ ] =>
        unfold map_util.M.Equal in H; rewrite <-H
      end.
      auto.
    - rewrite M.gempty.
      constructor; intros; destructAll; auto.
    - match goal with
      | [ |- context[M.find ?L1 (M.remove ?L2 _) = Some _] ] =>
        let H0 := fresh "H" in
        assert (H0 : L1 = L2 \/ L1 <> L2) by apply eq_dec_positive;
        case H0; intros; subst
      end.
      all: constructor; intros; destructAll.
      -- rewrite M.grs in *.
         match goal with
         | [ H : None = Some _ |- _ ] => inversion H
         end.
      -- rewrite M.gss in *.
         match goal with
         | [ H : Some _ = None |- _ ] => inversion H
         end.
      -- rewrite M.gso; auto.
         rewrite M.gro in *; auto.
         match goal with
         | [ H : _ <-> _ |- _ ] => destruct H
         end.
         match goal with
         | [ H : ?A -> ?B, H' : ?A |- _ ] => exact (H H')
         end.
      -- rewrite M.gro; auto.
         rewrite M.gso in *; auto.
         match goal with
         | [ H : _ <-> _ |- _ ] => destruct H
         end.
         match goal with
         | [ H : ?A /\ ?B -> ?C, H' : ?A, H'' : ?B |- _ ] =>
           exact (H (conj H' H''))
         end.
  Qed.

  Lemma ExactlyInOne_true_imp_not_in_Union_list : forall {Ss l ht},
      ExactlyInOne true l ht Ss ->
      ~ Union_list (map Dom_ht Ss) l.
  Proof.
    induction Ss.
    - intros; simpl in *.
      intro.
      match goal with
      | [ H : Ensembles.Empty_set _ _ |- _ ] => inversion H
      end.
    - intros; simpl in *.
      intro.
      match goal with
      | [ H : ExactlyInOne _ _ _ (_ :: _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : (_ :|: _) _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      -- unfold Dom_ht in *.
         unfold Dom_map in *.
         unfold Ensembles.In in *.
         destructAll.
         unfold get_heaptype in *.
         match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- unfold Ensembles.In in *.
         match goal with
         | [ H : context[~ _] |- _ ] => eapply H; eauto
         end.
  Qed.
  
  Lemma ExactlyInOne_true_imp_get_heaptype_None_In : forall {Ss S l ht},
      List.In S Ss ->
      ExactlyInOne true l ht Ss ->
      get_heaptype l S = None.
  Proof.
    induction Ss; intros;
      match goal with
      | [ H : List.In _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end;
      match goal with
      | [ H : ExactlyInOne _ _ _ _ |- _ ] =>
        inversion H; subst; simpl in *; auto
      end.
    match goal with
    | [ H : context[_ -> get_heaptype _ _ = None] |- _ ] =>
      eapply H; eauto
    end.
  Qed.
    
  Lemma SplitHeapTypings_disjoint_from_list : forall {Ss S1 S},
      SplitHeapTypings (S1 :: Ss) S ->
      disjoint_from_list S1 Ss.
  Proof.
    intros.
    unfold disjoint_from_list.
    rewrite Forall_forall.
    intros.
    apply disjoint_heaps_or.
    left; intros; destructAll.
    match goal with
    | [ H : SplitHeapTypings _ ?S,
        H' : get_heaptype ?L _ = Some ?HT |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : get_heaptype L S = Some HT)
    end.
    { eapply SplitHeapTypings_get_heaptype_LinTyp; eauto.
      constructor; auto. }
    unfold SplitHeapTypings in *.
    destructAll.
    match goal with
    | [ H : forall _ _, get_heaptype _ ?S = Some _ -> _,
        H' : get_heaptype _ ?S = Some _ |- _ ] =>
      specialize (H _ _ H'); inversion H; subst; simpl in *
    end.
    - eapply ExactlyInOne_true_imp_get_heaptype_None_In; eauto.
    - match goal with
      | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
        rewrite H in H'; inversion H'
      end.
  Qed.

  Lemma SplitHeapTypings_disjoint_heaps : forall {S1 S2},
      disjoint_heaps S1 S2 ->
      exists S,
        SplitHeapTypings [S1; S2] S.
  Proof.
    intros.
    exists (merge_heaps S1 S2).
    simpl.
    constructor.
    - simpl.
      eapply Same_set_trans; [ | apply Dom_ht_merge_heaps ].
      split; apply Same_set_Union_compat_r;
        [ | apply Same_set_sym ].
      all: apply Union_Empty_set_neut_r.
    - intros.
      apply_find_merge_heaps_case; intros.
      1: constructor; auto; constructor; [ | constructor ].
      2: constructor 3; [ | constructor; [ auto | constructor ] ].
      all: unfold disjoint_heaps in *.
      all:
        match goal with
        | [ H : forall _, _,
            H' : M.find (N.succ_pos ?L) _ = Some _ |- _ ] =>
          specialize (H L)
        end.
      all: destructAll; eauto.
  Qed.

  Lemma SplitHeapTypings_remove_heap : forall {S1 Ss S},
      SplitHeapTypings (S1 :: Ss) S ->
      exists S', SplitHeapTypings Ss S'.
  Proof.
    intros.
    exists (remove_heap S1 S).
    unfold SplitHeapTypings in *; destructAll.
    constructor.
    - unfold Ensembles.Same_set in *.
      unfold Ensembles.Included in *.
      unfold Ensembles.In in *.
      simpl in *; destructAll.
      split; intros.
      -- unfold Dom_ht.
         unfold Dom_map.
         unfold Ensembles.In.
         match goal with
         | [ H : forall _, (?S1 :|: ?S2) _ -> _,
             H' : ?S2 ?L |- _ ] =>
           let H0 := fresh "H" in
           assert (H0 : (S1 :|: S2) L);
           [ right; auto | specialize (H _ H0) ]
         end.
         match goal with
         | [ H : Dom_ht _ _ |- _ ] =>
           unfold Dom_ht in H;
           unfold Dom_map in H;
           unfold Ensembles.In in H
         end.
         destructAll.
         match goal with
         | [ H : map_util.M.find _ ?S = Some ?HT,
             H' : forall _ _, get_heaptype _ _ = Some _ -> _ |- _ ] =>
           exists HT; specialize (H' _ _ H)
         end.
         rewrite find_remove_heap.
         split; auto.
         match goal with
         | [ H : ExactlyInOne _ _ _ (_ :: _) |- _ ] =>
           inversion H; subst; simpl in *; auto
         end.
         exfalso.
         eapply ExactlyInOne_true_imp_not_in_Union_list; eauto.
      -- match goal with
         | [ H : Dom_ht _ _ |- _ ] =>
           unfold Dom_ht in H;
           unfold Dom_map in H;
           unfold Ensembles.In in H;
           let x := fresh "x" in
           destruct H as [x H];
           rewrite find_remove_heap in H
         end.
         destructAll.
         match goal with
         | [ H : forall _, Dom_ht ?S _ -> _,
             H' : M.find (N.succ_pos ?L) ?S = Some _ |- _ ] =>
           let H0 := fresh "H" in
           assert (H0 : Dom_ht S L);
           [ | specialize (H _ H0) ]
         end.
         { unfold Dom_ht.
           unfold Dom_map.
           unfold Ensembles.In.
           eexists; eauto. }
         match goal with
         | [ H : (_ :|: _) _ |- _ ] =>
           inversion H; subst; simpl in *
         end.
         --- unfold Dom_ht in *.
             unfold Dom_map in *.
             unfold Ensembles.In in *.
             destructAll.
             match goal with
             | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
               rewrite H in H'; inversion H'
             end.
         --- auto.
    - intros.
      unfold get_heaptype in *.
      match goal with
      | [ H : map_util.M.find _ (remove_heap _ _) = Some _ |- _ ] =>
        rewrite find_remove_heap in H
      end.
      destructAll.
      match goal with
      | [ H : forall _ _, map_util.M.find _ ?S = Some _ -> _,
          H' : M.find _ ?S = Some _ |- _ ] =>
        specialize (H _ _ H'); inversion H; subst; simpl in *
      end.
      -- unfold get_heaptype in *.
         match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- auto.
  Qed.

  Lemma SplitStoreTypings_disjoint_heaps : forall {S1 S2},
      InstTyp S1 = InstTyp S2 ->
      UnrTyp S1 = UnrTyp S2 ->
      disjoint_heaps (LinTyp S1) (LinTyp S2) ->
      exists S,
        SplitStoreTypings [S1; S2] S.
  Proof.
    intros.
    match goal with
    | [ H : disjoint_heaps _ _ |- _ ] =>
      specialize (SplitHeapTypings_disjoint_heaps H)
    end.
    intros; destructAll.
    match goal with
    | [ H : SplitHeapTypings _ ?S |- _ ] =>
      exists {| InstTyp := InstTyp S1; LinTyp := S; UnrTyp := UnrTyp S1 |}
    end.
    constructor; simpl; auto.
  Qed.

  Lemma get_heaptype_None_imp_ExactlyInOne_true : forall {A Ss S l ht},
      Union_list (map Dom_ht Ss) \subset Dom_ht S ->
      @get_heaptype A l S = None ->
      ExactlyInOne true l ht Ss.
  Proof.
    induction Ss; [ constructor | ].
    intros.
    simpl in *.
    match goal with
    | [ H : _ :|: _ \subset _ |- _ ] =>
      specialize (Union_Included_l _ _ _ H);
      specialize (Union_Included_r _ _ _ H)
    end.
    intros.
    match goal with
    | [ H : forall _ _ _, Union_list _ \subset _ -> _,
        H' : Union_list _ \subset Dom_ht ?S,
        H'' : get_heaptype _ _ = None
        |- ExactlyInOne _ ?L ?HT _ ] =>
      specialize (H S L HT H' H'')
    end.
    constructor; auto.
    unfold Dom_ht in *.
    unfold Dom_map in *.
    unfold Ensembles.Included in *.
    unfold Ensembles.In in *.
    match goal with
    | [ |- ?A = None ] =>
      remember A as opt; generalize (eq_sym Heqopt); case opt; auto
    end.
    intros.
    unfold get_heaptype in *.
    match goal with
    | [ H : forall _, (exists y, map_util.M.find _ ?A = Some _) -> _,
        H' : map_util.M.find (N.succ_pos ?L) ?A = Some ?HT |- _ ] =>
      specialize (H _ (ex_intro (fun ht => map_util.M.find (N.succ_pos L) A = Some ht) HT H'))
    end.
    destructAll.
    match goal with
    | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
      rewrite H in H'; inversion H'
    end.
  Qed.

  Lemma ExactlyInOne_true_imp_get_heaptype_None : forall {A Ss S l ht},
      (Dom_ht S :&: Ensembles.Singleton N l) \subset Union_list (map Dom_ht Ss) ->
      ExactlyInOne true l ht Ss ->
      @get_heaptype A l S = None.
  Proof.
    induction Ss; intros; simpl in *;
      unfold Dom_ht in *;
      unfold Dom_map in *;
      unfold Ensembles.Included in *;
      unfold Ensembles.In in *;
      match goal with
      | [ |- ?A = None ] =>
        remember A as opt; generalize (eq_sym Heqopt); case opt; auto
      end;
      intros;
      unfold get_heaptype in *;
      match goal with
      | [ H : forall _, (?S1 :&: ?S2) _ -> _,
          H' : map_util.M.find (N.succ_pos ?L) _ = Some _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : (S1 :&: S2) L);
        [ constructor; unfold Ensembles.In;
          [ eexists; eauto | constructor ] | specialize (H _ H0) ]
      end.
    - match goal with
      | [ H : Ensembles.Empty_set _ _ |- _ ] => inversion H
      end.
    - match goal with
      | [ H : ExactlyInOne _ _ _ (_ :: _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : (_ :|: _) _ |- _ ] =>
        inversion H; subst; simpl in *;
        unfold Ensembles.In in *; destructAll
      end.
      -- unfold get_heaptype in *.
         match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- match goal with
         | [ H : ExactlyInOne true _ _ (_ :: _),
             H' : ExactlyInOne true ?L ?HT ?SS,
             H'' : map_util.M.find (N.succ_pos _) ?S = Some _,
             H''' : forall _ _ _, _ -> _ -> _ |- _ ] =>
           generalize (H''' S L HT)
         end.
         match goal with
         | [ |- (?A -> _) -> _ ] =>
           let H0 := fresh "H" in
           let H1 := fresh "H" in
           assert (H0 : A);
           [ | intro H1; specialize (H1 H0) ]
         end.
         { intros.
           match goal with
           | [ H : (_ :&: _) _ |- _ ] =>
             inversion H; subst; simpl in *
           end.
           unfold Ensembles.In in *.
           match goal with
           | [ H : Ensembles.Singleton _ _ _ |- _ ] =>
             inversion H; subst; simpl in *
           end.
           auto. }
         match goal with
         | [ H : ?A, H' : ?A -> ?B |- _ ] =>
           specialize (H' H)
         end.
         match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
  Qed.   

  Lemma ExactlyInOne_false_imp_get_heaptype_Some : forall {A Ss S l ht},
      Union_list (map Dom_ht Ss) \subset Dom_ht S ->
      ExactlyInOne false l ht Ss ->
      exists ht', @get_heaptype A l S = Some ht'.
  Proof.
    induction Ss; intros;
      match goal with
      | [ H : ExactlyInOne false _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end;
      match goal with
      | [ H : _ :|: _ \subset _ |- _ ] =>
        specialize (Union_Included_l _ _ _ H);
        specialize (Union_Included_r _ _ _ H)
      end;
      intros.
    - unfold Dom_ht in *.
      unfold Dom_map in *.
      unfold Ensembles.Included in *.
      unfold Ensembles.In in *.
      unfold get_heaptype in *.
      match goal with
      | [ H : context[_ -> exists ht, map_util.M.find _ ?S = Some _]
          |- exists ht, map_util.M.find _ ?S = Some _ ] =>
        apply H
      end.
      eexists; eauto.
    - match goal with
      | [ H : context[_ -> exists ht, get_heaptype _ _ = Some _]
          |- exists ht, get_heaptype _ _ = Some _ ] =>
        eapply H; eauto
      end.
  Qed.   

  Lemma ExactlyInOne_false_app : forall {Ss1 Ss2 l ht},
      ExactlyInOne false l ht (Ss1 ++ Ss2) <->
      ((ExactlyInOne true l ht Ss1 /\ ExactlyInOne false l ht Ss2) \/
       (ExactlyInOne false l ht Ss1 /\ ExactlyInOne true l ht Ss2)).
  Proof.
    induction Ss1.
    - intros.
      simpl.
      constructor; intros.
      -- left; split; auto.
         constructor.
      -- match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; destructAll
         end.
         --- auto.
         --- match goal with
             | [ H : ExactlyInOne false _ _ [] |- _ ] => inversion H
             end.
    - intros; simpl.
      constructor; intros.
      -- match goal with
         | [ H : ExactlyInOne false _ _ _ |- _ ] =>
           inversion H; subst; simpl in *
         end.
         --- right.
             split.
             ---- constructor; auto.
                  eapply proj1; eapply ExactlyInOne_true_app; eauto.
             ---- eapply proj2; eapply ExactlyInOne_true_app; eauto.
         --- match goal with
             | [ H : forall _ _ _, ExactlyInOne _ _ _ _ <-> _,
                 H' : ExactlyInOne _ ?L ?HT (_ ++ ?SS2) |- _ ] =>
               specialize (H SS2 L HT);
               let H0 := fresh "H" in
               destruct H as [H H0]; specialize (H H');
               case H; intros; destructAll
             end.
             ---- left; split.
                  ----- constructor; auto.
                  ----- auto.
             ---- right; split.
                  ----- apply NotInHead; auto.
                  ----- auto.
      -- match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; destructAll
         end.
         --- match goal with
             | [ H : ExactlyInOne _ _ _ (_ :: _) |- _ ] =>
               inversion H; subst; simpl in *
             end.
             match goal with
             | [ H : forall _ _ _, ExactlyInOne _ _ _ (?SS1 ++ _) <-> _,
                 H' : ExactlyInOne true ?L ?HT ?SS1,
                 H'' : ExactlyInOne false ?L ?HT ?SS2 |- _ ] =>
               specialize (H SS2 L HT);
               let H0 := fresh "H" in
               destruct H as [H H0];
               specialize (H0 (or_introl (conj H' H'')))
             end.
             apply NotInHead; auto.
         --- match goal with
             | [ H : ExactlyInOne _ _ _ (_ :: _) |- _ ] =>
               inversion H; subst; simpl in *
             end.
             ---- constructor; auto.
                  rewrite ExactlyInOne_true_app; auto.
             ---- match goal with
                  | [ H : forall _ _ _, ExactlyInOne _ _ _ (?SS1 ++ _) <-> _,
                      H' : ExactlyInOne false ?L ?HT ?SS1,
                      H'' : ExactlyInOne true ?L ?HT ?SS2 |- _ ] =>
                    specialize (H SS2 L HT);
                    let H0 := fresh "H" in
                    destruct H as [H H0];
                    specialize (H0 (or_intror (conj H' H'')))
                  end.
                  apply NotInHead; auto.
  Qed.   

  Lemma ExactlyInOne_false_uniq : forall {Ss l ht1 ht2},
      ExactlyInOne false l ht1 Ss ->
      ExactlyInOne false l ht2 Ss ->
      ht1 = ht2.
  Proof.
    induction Ss; intros;
      repeat match goal with
             | [ H : ExactlyInOne false _ _ [] |- _ ] =>
               inversion H
             | [ H : ExactlyInOne false _ _ (_ :: _) |- _ ] =>
               inversion H; subst; simpl in *; clear H
             end;
      try match goal with
          | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
            rewrite H in H'; inversion H'
          end.    
    - match goal with
      | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
        rewrite H in H'; inversion H'; subst; auto
      end.
    - match goal with
      | [ H : context[_ -> _ = _] |- _ ] => eapply H; eauto
      end.
  Qed.
    
  Lemma ExactlyInOne_inv : forall {Ss l ht},
      ExactlyInOne false l ht Ss ->
      (exists S1,
          List.In S1 Ss /\
          get_heaptype l S1 = Some ht).
  Proof.
    intro Ss.
    elim Ss; intros;
      match goal with
      | [ H : ExactlyInOne _ _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    - eexists; split; eauto.
    - match goal with
      | [ H : forall _ _, ExactlyInOne _ _ _ _ -> _,
          H' : ExactlyInOne _ _ _ _ |- _ ] =>
        specialize (H _ _ H')
      end.
      destructAll.
      eexists; split; eauto.
  Qed.
    
  Lemma SplitHeapTypings_inv : forall {Ss S l ht},
      get_heaptype l S = Some ht ->
      SplitHeapTypings Ss S ->
      (exists S1,
          List.In S1 Ss /\
          get_heaptype l S1 = Some ht).
  Proof.
    intros.
    unfold SplitHeapTypings in *.
    destructAll.
    match goal with
    | [ H : get_heaptype _ _ = Some _,
        H' : forall _ _, get_heaptype _ _ = Some _ -> _ |- _ ] =>
      specialize (H' _ _ H)
    end.
    apply ExactlyInOne_inv; auto.
  Qed.
    
  Lemma SplitStoreTypings_inv : forall {Ss S l ht},
      get_heaptype l (LinTyp S) = Some ht ->
      SplitStoreTypings Ss S ->
      (exists S1,
          List.In S1 Ss /\
          get_heaptype l (LinTyp S1) = Some ht).
  Proof.
    intros.
    unfold SplitStoreTypings in *.
    destructAll.
    match goal with
    | [ H : get_heaptype _ _ = Some _,
        H' : SplitHeapTypings _ _ |- _ ] =>
      specialize (SplitHeapTypings_inv H H')
    end.
    intros; destructAll.
    match goal with
    | [ H : List.In _ (map _ _) |- _ ] =>
      apply in_map_inv in H; destructAll
    end.
    eexists; split; eauto.
  Qed.

  Lemma SplitHeapTypings_disjoint_from_list_imp_disjoint_heaps : forall {S1 Ss S2},
      SplitHeapTypings Ss S1 ->
      disjoint_from_list S2 Ss ->
      disjoint_heaps S1 S2.
  Proof.
    intros.
    apply disjoint_heaps_or.
    left.
    intros; destructAll.
    match goal with
    | [ H : SplitHeapTypings _ ?S,
        H' : get_heaptype _ ?S = Some _ |- _ ] =>
      specialize (SplitHeapTypings_inv H' H)
    end.
    intros; destructAll.
    unfold disjoint_from_list in *.
    rewrite Forall_forall in *.
    match goal with
    | [ H : forall _, List.In _ ?L -> _, H' : List.In _ ?L |- _ ] =>
      specialize (H _ H')
    end.
    unfold disjoint_heaps in *.
    match goal with
    | [ H : context[get_heaptype _ ?S = None]
        |- get_heaptype ?L ?S = None ] =>
      specialize (H L);
      let H' := fresh "H" in
      destruct H as [H H']; apply H'
    end.
    eexists; eauto.
  Qed.

  Lemma Dom_ht_subset_disjoint_heaps : forall {A} {S S1 S2},
      Dom_ht S \subset Dom_ht S1 ->
      @disjoint_heaps A S1 S2 ->
      disjoint_heaps S S2.
  Proof.
    intros.
    apply disjoint_heaps_or.
    left.
    intros; destructAll.
    match goal with
    | [ H : disjoint_heaps _ _ |- get_heaptype ?L _ = None ] =>
      unfold disjoint_heaps in H; specialize (H L)
    end.
    destructAll.
    match goal with
    | [ H : ?A -> ?B |- ?B ] => apply H
    end.
    unfold Dom_ht in *.
    unfold Dom_map in *.
    unfold Ensembles.Included in *.
    unfold Ensembles.In in *.
    unfold get_heaptype in *.
    eauto.
  Qed.

  Lemma Dom_ht_subset_disjoint_from_list : forall {A} {S S1 Ss},
      Dom_ht S \subset Dom_ht S1 ->
      @disjoint_from_list A S1 Ss ->
      disjoint_from_list S Ss.
  Proof.
    intros.
    unfold disjoint_from_list in *.
    rewrite Forall_forall in *.
    intros.
    match goal with
    | [ H : forall _, List.In _ ?L -> _, H' : List.In _ ?L |- _ ] =>
      specialize (H _ H')
    end.
    eapply Dom_ht_subset_disjoint_heaps; eauto.
  Qed.  

  Lemma SplitHeapTypings_disjoint_heaps_imp_disjoint_from_list : forall {S1 Ss S2},
      SplitHeapTypings Ss S1 ->
      disjoint_heaps S2 S1 ->
      disjoint_from_list S2 Ss.
  Proof.
    intros.
    unfold disjoint_from_list.
    rewrite Forall_forall.
    intros.
    match goal with
    | [ H : List.In _ ?L |- _ ] =>
      specialize (in_permut H)
    end.
    intros.
    destructAll.
    match goal with
    | [ H : Permutation.Permutation ?L1 ?L2,
        H' : SplitHeapTypings ?L1 ?S |- _ ] =>
      specialize (SplitHeapTypings_permut _ _ _ H H')
    end.
    let H' := fresh "H" in intro H'; destruct H'.
    simpl in *.
    rewrite disjoint_heaps_comm.
    eapply Dom_ht_subset_disjoint_heaps; eauto.
    - eapply Union_Included_l; eauto.
    - rewrite disjoint_heaps_comm; auto.
  Qed.

  Lemma SplitStoreTypings_apply_update_unr : forall {Ss S UT},
      SplitStoreTypings Ss S ->
      SplitStoreTypings (map (update_unr UT) Ss) (update_unr UT S).
  Proof.
    intros.
    split.
    - unfold SplitStoreTypings in *; destructAll.
      rewrite Forall_forall.
      intros.
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] =>
        apply in_map_inv in H
      end.
      destructAll.
      simpl; split; auto.
      rewrite Forall_forall in *.
      match goal with
      | [ H : forall _, List.In _ ?SS -> _, H' : List.In _ ?SS |- _ ] =>
        specialize (H _ H')
      end.
      destructAll; auto.
    - simpl.
      rewrite map_map.
      unfold update_unr.
      simpl.
      unfold SplitStoreTypings in *.
      destructAll; auto.
  Qed.

  Lemma SplitStoreTypings_undo_update_unr : forall {Ss UT S UT'},
      SplitStoreTypings (map (update_unr UT) Ss) S ->
      Forall (fun S' => UnrTyp S' = UT') Ss ->
      exists S',
        SplitStoreTypings Ss S'.
  Proof.
    intros.
    exists {| InstTyp := InstTyp S; LinTyp := LinTyp S; UnrTyp := UT' |}.
    constructor.
    - simpl.
      unfold SplitStoreTypings in *; destructAll.
      rewrite Forall_forall in *.
      intros.
      match goal with
      | [ H : forall _, List.In _ ?SS -> _, H' : List.In _ ?SS |- _ ] =>
        specialize (H _ H'); split; auto; clear H
      end.
      match goal with
      | [ H : forall _, List.In _ (map ?F _) -> _, H' : List.In _ _ |- _ ] =>
        specialize (in_map F _ _ H');
        let H0 := fresh "H" in intro H0; specialize (H _ H0)
      end.
      destructAll.
      unfold update_unr in *.
      simpl in *.
      auto.
    - simpl.
      unfold SplitStoreTypings in *.
      destructAll.
      rewrite map_map in *.
      unfold update_unr in *.
      simpl in *; auto.
  Qed.

  Lemma SplitHeapTypings_same_two_lists : forall {Ss1 Ss2 S S'},
      SplitHeapTypings Ss1 S ->
      SplitHeapTypings Ss2 S ->
      SplitHeapTypings Ss1 S' ->
      SplitHeapTypings Ss2 S'.
  Proof.
    intros.
    split.
    - unfold SplitHeapTypings in *; destructAll.
      eapply Same_set_trans; eauto.
      eapply Same_set_trans; [ | eauto ].
      apply Same_set_sym; auto.
    - intros.
      match goal with
      | [ H : SplitHeapTypings _ ?SP,
          H' : get_heaptype _ ?SP = Some _ |- _ ] =>
        specialize (SplitHeapTypings_inv H' H)
      end.
      intros; destructAll.
      
      match goal with
      | [ H : get_heaptype ?L ?S1 = Some ?HT,
          H' : List.In ?S1 ?SS,
          H'' : SplitHeapTypings ?SS ?S2,
          H''' : SplitHeapTypings ?SS ?S2P,
          H'''' : get_heaptype ?L ?S2P = Some ?HT |- _ ] =>
        specialize (SplitHeapTypings_get_heaptype_LinTyp H H' H'')
      end.
      intros.
      unfold SplitHeapTypings in *; destructAll; eauto.
  Qed.

  Lemma SplitStoreTypings_update_unr_two_lists : forall {Ss1 Ss2 UT S S'},
      SplitStoreTypings Ss1 S ->
      SplitStoreTypings Ss2 S ->
      SplitStoreTypings (map (update_unr UT) Ss1) S' ->
      length Ss1 > 0 ->
      SplitStoreTypings (map (update_unr UT) Ss2) S'.
  Proof.
    intros.
    assert (H' : InstTyp S' = InstTyp S /\ UnrTyp S' = UT).
    { match goal with
      | [ H : length ?SS > 0,
          H' : context[?SS], H'' : context[?SS] |- _ ] =>
        revert H; revert H'; revert H''; case SS; simpl; auto
      end.
      - intro; intro; intro H''; inversion H''.
      - intros.
        unfold SplitStoreTypings in *; destructAll.
        match goal with
        | [ H : Forall _ (_ _ _ :: _ _ _) |- _ ] =>
          inversion H; subst; simpl in *
        end.
        destructAll; split; auto.
        match goal with
        | [ H : Forall _ (_ :: _) |- _ ] =>
          inversion H; subst; simpl in *
        end.
        destructAll.
        eapply eq_trans; eauto. }
    destructAll.
    
    constructor.
    - unfold SplitStoreTypings in *; destructAll.
      rewrite Forall_forall in *.
      intros.
      match goal with
      | [ H : List.In _ (map _ _) |- _ ] =>
        apply in_map_inv in H
      end.
      destructAll; simpl.
      split; auto.
      match goal with
      | [ H : forall _, List.In _ ?SS -> _, H' : List.In _ ?SS |- _ ] =>
        specialize (H _ H')
      end.
      destructAll; eapply eq_trans; eauto.
    - rewrite map_map; simpl.
      unfold SplitStoreTypings in *; destructAll.
      eapply (SplitHeapTypings_same_two_lists (Ss1:=map LinTyp Ss1) (S:=LinTyp S)); eauto.
      rewrite map_map in *.
      unfold update_unr in *; simpl in *.
      auto.
  Qed.

  Lemma SplitHeapTypings_trans_even_more_gen : forall {Ss Ss' Ss'' S1 S2},
    SplitHeapTypings Ss S1 ->
    SplitHeapTypings Ss' S1 ->
    SplitHeapTypings (Ss ++ Ss'') S2 ->
    SplitHeapTypings (Ss' ++ Ss'') S2.
  Proof.
    intros.
    unfold SplitHeapTypings in *.
    destructAll.
    split.
    - simpl in *.
      rewrite map_app in *.
      rewrite Union_list_app in *.
      eapply Same_set_trans; [ | eauto ].
      eapply Same_set_Union_compat_l.
      eapply Same_set_trans; [ eauto | ].
      apply Same_set_sym; auto.
    - intros.
      match goal with
      | [ H : forall _ _, get_heaptype _ ?LT = Some _ -> _,
          H' : get_heaptype _ ?LT = Some _ |- _ ] =>
        specialize (H _ _ H')
      end.
      rewrite map_app in *.
      match goal with
      | [ H : ExactlyInOne false _ _ (_ ++ _) |- _ ] =>
        rewrite ExactlyInOne_false_app in H;
        case H; intros; destructAll
      end.
      -- rewrite ExactlyInOne_false_app; left.
         split; auto.
         eapply get_heaptype_None_imp_ExactlyInOne_true; eauto.
         eapply ExactlyInOne_true_imp_get_heaptype_None; eauto.
         eapply Included_trans; [ eapply Included_Intersection_l | ].
         auto.
      -- rewrite ExactlyInOne_false_app; right.
         split; auto.
         match goal with
         | [ H : context[_ -> ExactlyInOne false _ _ ?SS]
             |- ExactlyInOne false _ _ ?SS ] =>
           apply H
         end.
         match goal with
         | [ |- ?A = Some _ ] =>
           remember A as opt; generalize (eq_sym Heqopt);
           case opt; intros
         end.
         --- repeat match goal with
                    | [ H : forall _ _, get_heaptype _ ?S = Some _ -> _,
                        H' : get_heaptype _ ?S = Some _ |- _ ] =>
                      specialize (H _ _ H')
                    end.
             match goal with
             | [ H : ExactlyInOne false ?L _ ?SS,
                 H' : ExactlyInOne false ?L _ ?SS |- _ ] =>
               specialize (ExactlyInOne_false_uniq H H')
             end.
             intros; subst; auto.
         --- match goal with
             | [ H : ?A = None |- _ ] =>
               let H0 := fresh "H" in
               assert (H0 : exists ht, A = Some ht);
               [ | destructAll;
                   match goal with
                   | [ H' : ?A = None, H'' : ?A = Some _ |- _ ] =>
                     rewrite H' in H''; inversion H''
                   end ]
             end.
             eapply ExactlyInOne_false_imp_get_heaptype_Some; [ | eauto ].
             auto.
  Qed.

  Lemma SplitStoreTypings_trans_even_more_gen : forall {Ss Ss' Ss'' S1 S2},
    SplitStoreTypings Ss S1 ->
    SplitStoreTypings Ss' S1 ->
    SplitStoreTypings (Ss ++ Ss'') S2 ->
    InstTyp S1 = InstTyp S2 ->
    UnrTyp S1 = UnrTyp S2 ->
    SplitStoreTypings (Ss' ++ Ss'') S2.
  Proof.
    intros.
    unfold SplitStoreTypings in *.
    destructAll.
    constructor.
    - rewrite Forall_forall in *.
      intros.
      match goal with
      | [ H : List.In _ (_ ++ _) |- _ ] =>
        apply in_app_or in H; case H; intros
      end.
      -- match goal with
         | [ H : forall _, List.In _ ?L -> _,
             H' : List.In _ ?L |- _ ] =>
           specialize (H _ H')
         end.
         destructAll.
         split.
         all: eapply eq_trans; [ eapply eq_sym; eauto | ]; auto.
      -- match goal with
         | [ H : context[InstTyp ?S = _ /\ _]
             |- InstTyp ?S = _ /\ _ ] =>
           apply H
         end.
         apply in_or_app; right; auto.
    - rewrite map_app in *.
      eapply SplitHeapTypings_trans_even_more_gen; [ | | eauto ]; eauto.
  Qed.

  Lemma SplitStoreTypings_trans_gen : forall {Ss Ss' S1 S2},
    SplitStoreTypings Ss S1 ->
    SplitStoreTypings (S1 :: Ss') S2 ->
    SplitStoreTypings (Ss ++ Ss') S2.
  Proof.
    intros.
    eapply SplitStoreTypings_trans_even_more_gen;
      [ | eauto | | | ].
    - apply SplitStoreTypings_Singl.
    - match goal with
      | [ H : context[?A :: ?B] |- _ ] =>
        replace (A :: B) with ([A] ++ B) in H; eauto
      end.
    - solve_inst_or_unr_typ_eq.
    - solve_inst_or_unr_typ_eq.
  Qed.

  Lemma SplitStoreTypings_trans_gen_inv : forall {Ss Ss' S1 S2},
    SplitStoreTypings Ss S1 ->
    SplitStoreTypings (Ss ++ Ss') S2 ->
    InstTyp S1 = InstTyp S2 ->
    UnrTyp S1 = UnrTyp S2 ->
    SplitStoreTypings (S1 :: Ss') S2.
  Proof.
    intros.
    match goal with
    | [ |- context[?A :: ?B] ] =>
      replace (A :: B) with ([A] ++ B) by auto
    end.
    eapply SplitStoreTypings_trans_even_more_gen;
      [ | apply SplitStoreTypings_Singl | eauto | | ].
    all: auto.
  Qed.

  Lemma SplitHeapTypings_split : forall {Ss1 Ss2 S},
      SplitHeapTypings (Ss1 ++ Ss2) S ->
      exists S', SplitHeapTypings Ss1 S'.
  Proof.
    induction Ss1.
    - intros.
      exists (M.empty _).
      constructor.
      -- simpl.
         constructor;
           unfold Ensembles.Included; unfold Ensembles.In; intros.
         --- match goal with
             | [ H : Ensembles.Empty_set _ _ |- _ ] =>
               inversion H; subst; simpl in *
             end.
         --- unfold Dom_ht in *.
             unfold Dom_map in *.
             unfold Ensembles.In in *.
             rewrite M.gempty in *.
             destructAll.
             match goal with
             | [ H : None = Some _ |- _ ] => inversion H
             end.
      -- unfold get_heaptype.
         intros.
         rewrite M.gempty in *.
         match goal with
         | [ H : None = Some _ |- _ ] => inversion H
         end.
    - intros; simpl in *.
      match goal with
      | [ H : SplitHeapTypings (_ :: _) _ |- _ ] =>
        specialize (SplitHeapTypings_remove_heap H);
        specialize (SplitHeapTypings_disjoint_from_list H)
      end.
      intros; destructAll.
      match goal with
      | [ H : forall _ _, SplitHeapTypings (?SS1 ++ _) _ -> _,
          H' : SplitHeapTypings (?SS1 ++ _) _ |- _ ] =>
        specialize (H _ _ H')
      end.
      destructAll.
      match goal with
      | [ H : disjoint_from_list ?S (?SS1 ++ ?SS2) |- _ ] =>
        let H' := fresh "H" in
        assert (H' : disjoint_from_list S SS1)
      end.
      { unfold disjoint_from_list in *.
        match goal with
        | [ H : Forall _ (_ ++ _) |- _ ] =>
          apply Forall_app in H
        end.
        destructAll; auto. }
      match goal with
      | [ H : SplitHeapTypings ?SS ?S1,
          H' : disjoint_from_list ?S2 ?SS |- _ ] =>
        specialize (SplitHeapTypings_disjoint_heaps (SplitHeapTypings_disjoint_from_list_imp_disjoint_heaps H H'))
      end.
      intros; destructAll.
      match goal with
      | [ H : SplitHeapTypings [_; _] ?S |- _ ] => exists S
      end.
      match goal with
      | [ |- context[?A :: ?B] ] =>
        replace (A :: B) with ([A] ++ B) by auto
      end.
      eapply SplitHeapTypings_permut;
        [ apply Permutation.Permutation_app_comm | ].
      eapply SplitHeapTypings_trans_even_more_gen;
        [ apply SplitHeapTypings_Singl | eauto | ].
      simpl; auto.
  Qed.
  
  Lemma SplitStoreTypings_split_weak : forall {Ss1 Ss2 S},
      SplitStoreTypings (Ss1 ++ Ss2) S ->
      exists S',
        SplitStoreTypings Ss1 S' /\
        InstTyp S' = InstTyp S /\
        UnrTyp S' = UnrTyp S.
  Proof.
    intros.
    unfold SplitStoreTypings in *.
    destructAll.
    rewrite map_app in *.
    match goal with
    | [ H : SplitHeapTypings (_ ++ _) _ |- _ ] =>
      specialize (SplitHeapTypings_split H)
    end.
    intros; destructAll.
    match goal with
    | [ H : SplitHeapTypings ?L ?S,
        H' : SplitHeapTypings _ (LinTyp ?SORIG)
        |- context[SplitHeapTypings ?L _] ] =>
      exists {| InstTyp := InstTyp SORIG; LinTyp := S; UnrTyp := UnrTyp SORIG |}
    end.
    simpl.
    split; split; auto.
    match goal with
    | [ H : Forall _ (_ ++ _) |- _ ] =>
      apply Forall_app in H
    end.
    destructAll; auto.
  Qed.

  Lemma SplitStoreTypings_split : forall {Ss1 Ss2 S},
      SplitStoreTypings (Ss1 ++ Ss2) S ->
      exists S',
        SplitStoreTypings Ss1 S' /\
        SplitStoreTypings (S' :: Ss2) S.
  Proof.
    intros.
    specialize (SplitStoreTypings_split_weak H).
    intro H'; destruct H' as [S'].
    destructAll.
    exists S'; split; auto.
    match goal with
    | [ |- context[?A :: ?B] ] =>
      replace (A :: B) with ([A] ++ B) by auto
    end.
    eapply SplitStoreTypings_trans_gen_inv; eauto.
  Qed.

  Lemma SplitStoreTypings_move_one : forall {S1 S2 S S0 Ss},
      SplitStoreTypings [S1; S2] S ->
      SplitStoreTypings (S0 :: Ss) S1 ->
      exists S1' S2',
        SplitStoreTypings Ss S1' /\
        SplitStoreTypings [S0; S1'] S1 /\
        SplitStoreTypings [S0; S2] S2' /\
        SplitStoreTypings [S1'; S2'] S.
  Proof.
    intros.
    match goal with
    | [ H : SplitStoreTypings (?S1 :: ?SS) ?S |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings (SS ++ [S1]) S);
      [ | clear H; specialize (SplitStoreTypings_split H0) ]
    end.
    { eapply SplitStoreTypings_permut; [ apply Permutation.Permutation_app_comm | ].
      auto. }
    let H' := fresh "H" in
    intro H'; destruct H' as [S1']; exists S1'.
    match goal with
    | [ H : SplitStoreTypings [?S1; ?S2] ?S,
        H' : SplitStoreTypings ?SS ?S1 |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings (SS ++ [S2]) S)
    end.
    { eapply SplitStoreTypings_trans_gen; eauto. }
    rewrite <-app_assoc in *.
    match goal with
    | [ H : SplitStoreTypings (?S1 ++ ?S2 ++ ?S3) ?S |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings ((S2 ++ S3) ++ S1) S);
      [ | specialize (SplitStoreTypings_split H0) ]
    end.
    { eapply SplitStoreTypings_permut; [ | eauto ].
      apply Permutation.Permutation_app_comm. }
    let H' := fresh "H" in
    intro H'; destruct H' as [S2']; exists S2'.
    simpl in *; destructAll.
    split; auto.
    split;
    [ eapply SplitStoreTypings_permut; [ | eauto ]; constructor | ].
    split; auto.
    eapply SplitStoreTypings_trans_gen_inv.
    - eauto.
    - eapply SplitStoreTypings_permut;
        [ apply Permutation.Permutation_app_comm | ].
      simpl; auto.
    - solve_inst_or_unr_typ_eq.
    - solve_inst_or_unr_typ_eq.
  Qed.

  Ltac natural_permut_SplitStoreTypings :=
    repeat match goal with
           | [ H : List.In ?S ?SS,
               H' : SplitStoreTypings ?SS ?SW |- _ ] =>
             specialize (in_permut H);
             let l := fresh "l" in
             let H0 := fresh "H" in
             intro H0; destruct H0 as [l];
             let H1 := fresh "H" in
             assert (H1 : SplitStoreTypings (S :: l) SW);
             [ eapply SplitStoreTypings_permut;
               [ exact H0 | exact H' ]
             | clear H' ]
           end.
        
  Lemma SplitStoreTypings_extract_nested : forall {Sinner Ss S Ss' S'},
      List.In Sinner Ss ->
      SplitStoreTypings Ss S ->
      List.In S Ss' ->
      SplitStoreTypings Ss' S' ->
      exists S'',
        SplitStoreTypings [Sinner; S''] S'.
  Proof.
    intros.
    natural_permut_SplitStoreTypings.
    repeat match goal with
           | [ H : SplitStoreTypings (?A :: ?B) ?S |- _ ] =>
             replace (A :: B) with ([A] ++ B) in H by auto;
             let H0 := fresh "H" in
             assert (H0 : SplitStoreTypings (B ++ [A]) S);
             [ eapply SplitStoreTypings_permut;
               [ apply Permutation.Permutation_app_comm | exact H ]
             | clear H; specialize (SplitStoreTypings_split H0) ]
           end.
    intros; destructAll.
    match goal with
    | [ H : SplitStoreTypings (?L ++ [?S]) ?SP
        |- context[SplitStoreTypings _ ?SP] ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings ([S] ++ L) SP);
      [ eapply SplitStoreTypings_permut;
        [ apply Permutation.Permutation_app_comm | exact H ] | ];
      destruct H0
    end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings (_ :: _) _ |- _ ] =>
      specialize (SplitHeapTypings_disjoint_from_list H)
    end.
    intros.
    repeat match goal with
           | [ H : SplitStoreTypings _ _ |- _ ] =>
             destruct H
           end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings [?S1; _] ?S,
        H' : disjoint_from_list ?S ?SS |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : disjoint_from_list S1 SS);
      [ destruct H | ]
    end.
    { eapply Dom_ht_subset_disjoint_from_list; [ | eauto ].
      simpl in *.
      eapply Union_Included_l; eauto. }
    match goal with
    | [ H : SplitHeapTypings ?SS ?S1,
        H' : disjoint_from_list ?S2 ?SS |- _ ] =>
      specialize (SplitHeapTypings_disjoint_heaps (SplitHeapTypings_disjoint_from_list_imp_disjoint_heaps H H'))
    end.
    match goal with
    | [ |- context[SplitStoreTypings _ ?S] ] =>
      let H' := fresh "H" in
      let S'' := fresh "S" in
      intro H'; destruct H' as [S''];
      exists {| InstTyp := InstTyp S; LinTyp := S''; UnrTyp := UnrTyp S |}
    end.
    constructor.
    - constructor; [ | constructor; auto ].
      match goal with
      | [ H : Forall _ [_; ?S] |- InstTyp _ = InstTyp ?S /\ _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : Forall _ [?S] |- InstTyp _ = InstTyp ?S /\ _ ] =>
        inversion H; subst; simpl in *
      end.
      destructAll.
      match goal with
      | [ H : ?A = ?B, H' : ?C = ?D |- _ = ?B /\ _ = ?D ] =>
        rewrite <-H; rewrite <-H'
      end.
      match goal with
      | [ H : Forall _ (?S :: _) |- _ = InstTyp ?S /\ _ ] =>
        inversion H; subst; simpl in *
      end.
      auto.
    - simpl in *.
      eapply SplitHeapTypings_permut;
        [ apply Permutation.perm_swap | ].
      match goal with
      | [ |- SplitHeapTypings [?A; ?B] _ ] =>
        replace [A; B] with ([A] ++ [B]) by auto
      end.
      eapply SplitHeapTypings_trans_even_more_gen;
        [ | apply SplitHeapTypings_Singl | ]; eauto.
      simpl.
      match goal with
      | [ |- SplitHeapTypings [?A; ?B; ?C] _ ] =>
        replace [A; B; C] with ([A] ++ [B; C]) by auto
      end.
      eapply SplitHeapTypings_permut;
        [ apply Permutation.Permutation_app_comm | ].
      eapply SplitHeapTypings_trans_even_more_gen;
        [ apply SplitHeapTypings_Singl | eauto | ].
      eapply SplitHeapTypings_permut;
        [ apply Permutation.perm_swap | ].
      auto.
  Qed.

  Lemma SplitStoreTypings_change_vals : forall {S0 S0' Ss S1},
      SplitStoreTypings (S0 :: Ss) S1 ->
      InstTyp S0 = InstTyp S0' ->
      UnrTyp S0 = UnrTyp S0' ->
      (Dom_ht (LinTyp S0)) <--> (Dom_ht (LinTyp S0')) ->
      exists S1',
        SplitStoreTypings (S0' :: Ss) S1' /\
        InstTyp S1 = InstTyp S1' /\
        UnrTyp S1 = UnrTyp S1' /\
        (Dom_ht (LinTyp S1)) <--> (Dom_ht (LinTyp S1')).
  Proof.
    intros.
    match goal with
    | [ H : SplitStoreTypings _ _ |- _ ] => destruct H
    end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings (_ :: _) _ |- _ ] =>
      specialize (SplitHeapTypings_remove_heap H);
      specialize (SplitHeapTypings_disjoint_from_list H)
    end.
    intros; destructAll.
    match goal with
    | [ H : Dom_ht ?S1 <--> Dom_ht ?S2,
        H' : disjoint_from_list ?S1 ?SS |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : disjoint_from_list S2 SS)
    end.
    { eapply Dom_ht_subset_disjoint_from_list; eauto. }
    match goal with
    | [ H : SplitHeapTypings ?SS ?S,
        H' : disjoint_from_list ?SP ?SS |- _ ] =>
      specialize (SplitHeapTypings_disjoint_heaps (SplitHeapTypings_disjoint_from_list_imp_disjoint_heaps H H'))
    end.
    match goal with
    | [ |- context[InstTyp ?S = _] ] =>
      let H' := fresh "H" in
      let S' := fresh "S" in
      intro H'; destruct H' as [S'];
      exists {| InstTyp := InstTyp S; LinTyp := S'; UnrTyp := UnrTyp S |}
    end.
    simpl in *.
    split; [ | split; auto; split; auto ].
    - constructor.
      -- simpl.
         match goal with
         | [ H : Forall _ (_ :: _) |- _ ] =>
           inversion H; subst; simpl in *
         end.
         constructor; auto.
         destructAll.
         split; eapply eq_trans; eauto.
      -- simpl.
         match goal with
         | [ |- context[?A :: ?B] ] =>
           replace (A :: B) with ([A] ++ B) by auto
         end.
         eapply SplitHeapTypings_permut;
           [ apply Permutation.Permutation_app_comm | ].
         eapply SplitHeapTypings_trans_even_more_gen;
           [ apply SplitHeapTypings_Singl | eauto | ].
         simpl; auto.
    - match goal with
      | [ H : SplitHeapTypings (_ :: _) _ |- _ ] => destruct H
      end.
      eapply Same_set_trans; [ | eauto ].
      match goal with
      | [ H : SplitHeapTypings _ ?S |- Dom_ht ?S <--> _ ] =>
        destruct H
      end.
      apply Same_set_sym; eapply Same_set_trans; [ | eauto ].
      simpl.
      eapply Same_set_trans.
      1:{
        split; eapply Same_set_Union_compat_r;
        [ | apply Same_set_sym ].
        all: apply Union_Empty_set_neut_r.
      }
      eapply Same_set_trans; [ eapply Union_commut | ].
      match goal with
      | [ H : SplitHeapTypings _ ?S |- _ :|: Dom_ht ?S <--> _ ] =>
        destruct H
      end.
      eapply Same_set_trans.
      1:{
        split; eapply Same_set_Union_compat_r;
        [ apply Same_set_sym | ].
        all: eauto.
      }
      eapply Same_set_Union_compat_l.
      apply Same_set_sym; auto.
  Qed.

  Lemma SplitStoreTypings_safe_set_nth : forall {Ss S Ss1 S1 S2 S' idx},
    SplitStoreTypings Ss S ->
    List.In S Ss1 ->
    SplitStoreTypings Ss1 S1 ->
    SplitStoreTypings [S2; S1] S' ->
    exists S',
      SplitStoreTypings (set_nth Ss idx S2) S'.
  Proof.
    intros.
    natural_permut_SplitStoreTypings.
    match goal with
    | [ H : SplitStoreTypings [_; _] _ |- _ ] => destruct H
    end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings [_; _] _ |- _ ] =>
      specialize (SplitHeapTypings_disjoint_from_list H)
    end.
    intros.
    unfold disjoint_from_list in *.
    match goal with
    | [ H : Forall _ [_] |- _ ] => inversion H; subst; simpl in *
    end.
    match goal with
    | [ H : SplitStoreTypings (_ :: _) _ |- _ ] => destruct H
    end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings _ ?S1,
        H' : disjoint_heaps ?S2 ?S1 |- _ ] =>
      specialize (SplitHeapTypings_disjoint_heaps_imp_disjoint_from_list H H')
    end.
    unfold disjoint_from_list.
    let H' := fresh "H" in
    intro H'; inversion H'; subst; simpl in *.

    match goal with
    | [ |- context[set_nth ?L ?IDX _] ] =>
      remember (nth_error L IDX) as opt;
      generalize (eq_sym Heqopt); case opt; intros
    end.
    2:{
      rewrite nth_error_None in *.
      rewrite set_nth_trivial; auto.
      eexists; eauto.
    }

    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] =>
      specialize (Permutation_remove_nth H)
    end.
    intros.
    match goal with
    | [ H : Permutation.Permutation ?L1 ?L2,
        H' : SplitStoreTypings ?L1 ?S |- _ ] =>
      specialize (SplitStoreTypings_permut _ _ _ H H')
    end.
    intros.

    match goal with
    | [ H : SplitStoreTypings ?SS ?S,
        H' : disjoint_heaps (LinTyp ?S2) (LinTyp ?S)
        |- context[set_nth ?SS _ _] ] =>
      specialize (SplitHeapTypings_disjoint_heaps H');
      intros; destructAll;
      match goal with
      | [ H'' : SplitHeapTypings [LinTyp S2; LinTyp S] ?SP |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : SplitHeapTypings [LinTyp S; LinTyp S2] SP);
        [ eapply SplitHeapTypings_permut;
          [ apply Permutation.perm_swap | ]; auto | ]
      end
    end.

    match goal with
    | [ H : SplitHeapTypings [LinTyp ?S; ?S2] ?SP,
        H' : SplitStoreTypings (?S3 :: remove_nth ?SS ?IDX) ?S |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitHeapTypings (map LinTyp (S3 :: remove_nth SS IDX) ++ [S2]) SP);
      [ eapply SplitHeapTypings_trans_even_more_gen;
        [ 
        | destruct H'; eauto
        | replace [LinTyp S; S2] with ([LinTyp S] ++ [S2]) in H by auto;
          exact H ];
        apply SplitHeapTypings_Singl | ]
    end.
    simpl in *.
    match goal with
    | [ H : SplitHeapTypings (LinTyp _ :: _ ++ _) _ |- _ ] =>
      specialize (SplitHeapTypings_remove_heap H)
    end.

    match goal with
    | [ H : SplitStoreTypings ?SS ?S |- context[set_nth ?SS _ _] ] =>
      let H' := fresh "H" in
      let S' := fresh "S" in
      intro H'; destruct H' as [S'];
      exists {| InstTyp := InstTyp S; LinTyp := S'; UnrTyp := UnrTyp S |}
    end.

    constructor; simpl in *.
    - rewrite Forall_forall; intros.

      match goal with
      | [ H : List.In _ (set_nth _ _ _) |- _ ] =>
        apply In_set_nth in H; case H; intros; subst
      end.
      -- match goal with
         | [ H : Forall _ (?S :: _) |- InstTyp ?S = _ /\ _ ] =>
           inversion H; subst; simpl in *
         end.
         destructAll.
         match goal with
         | [ H : _ = ?A |- ?A = _ /\ _ ] => rewrite <-H
         end.
         match goal with
         | [ H : _ = ?A |- _ /\ ?A = _ ] => rewrite <-H
         end.
         match goal with
         | [ H : Forall _ [?S; _] |- _ = InstTyp ?S /\ _ ] =>
           inversion H; subst; simpl in *
         end.
         destructAll.
         match goal with
         | [ H : _ = ?A |- _ = ?A /\ _ ] => rewrite <-H
         end.
         match goal with
         | [ H : _ = ?A |- _ /\ _ = ?A ] => rewrite <-H
         end.
         match goal with
         | [ H : Forall _ [?S] |- InstTyp ?S = _ /\ _ ] =>
           inversion H; subst; simpl in *
         end.
         destructAll.
         split; apply eq_sym; auto.
      -- match goal with
         | [ H : SplitStoreTypings ?SS ?S,
             H' : List.In ?SP ?SS
             |- InstTyp ?S = InstTyp ?SP /\ _ ] =>
           destruct H as [H];
           rewrite Forall_forall in H; specialize (H _ H')
         end.
         auto.
    - match goal with
      | [ H : nth_error _ _ = Some _
          |- context[set_nth ?SS ?IDX ?EL] ] =>
        specialize (nth_error_Some_length _ _ _ H);
        let H' := fresh "H" in intro H';
        specialize (nth_error_set_nth EL H')
      end.
      intros.
      eapply SplitHeapTypings_permut.
      { apply Permutation.Permutation_map.
        apply Permutation.Permutation_sym.
        eapply Permutation_remove_nth; eauto. }
      simpl.
      match goal with
      | [ |- context[?A :: ?B] ] =>
        replace (A :: B) with ([A] ++ B) by auto
      end.
      eapply SplitHeapTypings_permut;
        [ apply Permutation.Permutation_app_comm | ].
      rewrite remove_nth_set_nth; auto.
  Qed.

  Lemma SplitStoreTypings_trans : forall {Ss S1 S2},
      SplitStoreTypings Ss S1 ->
      SplitStoreTypings [S1] S2 ->
      SplitStoreTypings Ss S2.
  Proof.
    intros.
    match goal with
    | [ |- SplitStoreTypings ?S _ ] =>
      replace S with (S ++ []) by apply app_nil_r
    end.
    eapply SplitStoreTypings_trans_gen; eauto.
  Qed.

  Lemma SplitStoreTypings_add_one : forall {Ss S S1 S'},
      SplitStoreTypings Ss S ->
      SplitStoreTypings [S1; S] S' ->
      SplitStoreTypings (S1 :: Ss) S'.
  Proof.
    intros.
    match goal with
    | [ |- context[?A :: ?B] ] =>
      replace (A :: B) with ([A] ++ B) by auto
    end.
    eapply SplitStoreTypings_permut;
      [ apply Permutation.Permutation_app_comm | ].
    eapply SplitStoreTypings_trans_gen; eauto.
    eapply SplitStoreTypings_permut; [ | eauto ].
    constructor.
  Qed.
          
  Lemma SplitStoreTypings_add_loc : forall {S loc ht},
      get_heaptype loc (LinTyp S) = None ->
      exists S',
        SplitStoreTypings [{| InstTyp := InstTyp S; LinTyp := M.add (N.succ_pos loc) ht (M.empty HeapType); UnrTyp := UnrTyp S |}; S] S'.
  Proof.
    intros.
    apply SplitStoreTypings_disjoint_heaps; simpl; auto.
    apply disjoint_heaps_or.
    constructor.
    intros; destructAll.
    unfold get_heaptype in *.
    match goal with
    | [ H : map_util.M.find ?L1 (M.add ?L2 _ _) = Some _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : L1 = L2 \/ L1 <> L2) by apply eq_dec_positive;
      case H';
      let H'' := fresh "H" in intro H''; try rewrite H''; auto
    end.
    rewrite M.gso in *; auto.
    rewrite M.gempty in *; auto.
    match goal with
    | [ H : None = Some _ |- _ ] => inversion H
    end.
  Qed.

  Lemma map_find_empty: forall {T} n (m: M.tree T),
      M.is_empty m = true -> map_util.M.find n m = None.
  Proof.
    intros.
    generalize dependent n.
    induction m; intros; destruct n; auto; simpl; destruct o; try discriminate H; simpl in H;
      apply andb_prop in H as [H1 H2]; eauto.
  Qed.

  Lemma get_heaptype_empty: forall {T}  n (m: M.tree T),
      M.is_empty m = true -> get_heaptype n m = None.
  Proof.
    unfold get_heaptype.
    intros.
    eapply map_find_empty. auto.
  Qed.
        
  Lemma SplitStoreTypings_remove_cons S1 S2 S3 S4 Ss S5:
    SplitStoreTypings [S1; S2] S3 ->
    SplitStoreTypings (S4 :: Ss) S1 ->
    SplitStoreTypings Ss S5 ->
    InstTyp S1 = InstTyp S5 ->
    UnrTyp S1 = UnrTyp S5 ->
    exists S6,
      SplitStoreTypings [S5; S2] S6.
  Proof.
    intros.
    apply SplitStoreTypings_disjoint_heaps.
    1-2:
      match goal with
      | [ H : ?F ?A = ?F ?B |- ?F ?B = _ ] =>
        rewrite <-H; solve_inst_or_unr_typ_eq
      end.
    apply disjoint_heaps_or.
    constructor 2.
    intros; destructAll.
    match goal with
    | [ H : SplitStoreTypings [_; _] _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    match goal with
    | [ H : SplitHeapTypings [_; _] _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    match goal with
    | [ H : forall _ _, get_heaptype _ _ = Some _ -> _,
        H' : get_heaptype ?L (LinTyp ?S) = Some ?HT,
        H'' : SplitStoreTypings [?SP; ?S] ?SW |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : List.In S [SP; S]);
      [ constructor 2; constructor; auto | ];
      specialize (SplitStoreTypings_get_heaptype_LinTyp H' H0 H'');
      let H1 := fresh "H" in intro H1;
      specialize (H _ _ H1);
      inversion H; subst; simpl in *
    end.
    - match goal with
      | [ H : ExactlyInOne true _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
        rewrite H in H'; inversion H'
      end.
    - match goal with
      | [ |- ?A = None ] =>
        remember A as opt;
        generalize (eq_sym Heqopt);
        case opt; [ | auto ]
      end.
      intros.

      match goal with
      | [ H : get_heaptype _ (LinTyp ?S) = Some _,
          H' : SplitStoreTypings ?SS ?S,
          H'' : InstTyp _ = InstTyp ?S,
          H''' : SplitStoreTypings (?SP :: ?SS) _ |- _ ] =>
        specialize (SplitStoreTypings_inv H H');
        let H0 := fresh "H" in
        let x := fresh "x" in
        intro H0; destruct H0 as [x]; destructAll;
        match goal with
        | [ H1 : List.In x _,
            H3 : get_heaptype _ (LinTyp x) = Some _ |- _ ] =>
          let H2 := fresh "H" in
          assert (H2 : List.In x (SP :: SS)); [ constructor 2; auto | ];
          specialize (SplitStoreTypings_get_heaptype_LinTyp H3 H2 H''')
        end
      end.
      intros.
      match goal with
      | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
        rewrite H in H'; inversion H'
      end.
  Qed.

  Lemma SplitHeapTypings_add_empty_heap : forall {Ss S S'},
      SplitHeapTypings Ss S ->
      M.is_empty S' = true ->
      SplitHeapTypings (S' :: Ss) S.
  Proof.
    intros.
    unfold SplitHeapTypings in *; destructAll.
    constructor.
    - simpl.
      eapply Same_set_trans;
        [ eapply Same_set_Union_compat_l;
          apply Dom_ht_is_empty; auto | ].
      eapply Same_set_trans; [ eapply Union_Empty_set_neut_l | ].
      auto.
    - intros.
      match goal with
      | [ H : forall _ _, get_heaptype _ _ = Some _ -> _,
          H' : get_heaptype _ _ = Some _ |- _ ] =>
        specialize (H _ _ H')
      end.
      apply NotInHead; auto.
      apply get_heaptype_empty; auto.
  Qed.
  
  Lemma SplitStoreTypings_add_empty_StoreTyping : forall {Ss S S'},
      SplitStoreTypings Ss S ->
      InstTyp S = InstTyp S' ->
      UnrTyp S = UnrTyp S' ->
      M.is_empty (LinTyp S') = true ->
      SplitStoreTypings (S' :: Ss) S.
  Proof.
    intros.
    unfold SplitStoreTypings in *; destructAll.
    constructor; [ constructor; auto | ].
    simpl.
    eapply SplitHeapTypings_add_empty_heap; eauto.
  Qed.

  Lemma SplitStoreTypings_add_empty_LinTyp : forall {Ss S},
      SplitStoreTypings Ss S ->
      SplitStoreTypings (empty_LinTyp S :: Ss) S.
  Proof.
    intros.
    eapply SplitStoreTypings_add_empty_StoreTyping; eauto.
    all: unfold empty_LinTyp; destruct S; simpl in *; auto.
  Qed.

  Lemma SplitHeapTypings_remove_empty_heap : forall {Ss S1 S},
      SplitHeapTypings (S1 :: Ss) S ->
      M.is_empty S1 = true ->
      SplitHeapTypings Ss S.
  Proof.
    intros.
    unfold SplitHeapTypings in *; destructAll.
    constructor.
    - eapply Same_set_trans;
        [ eapply Same_set_sym; eapply Union_Empty_set_neut_l | ].
      eapply Same_set_trans;
        [ eapply Same_set_Union_compat_l;
          eapply Same_set_sym;
          eapply Dom_ht_is_empty; eauto | ].
      simpl in *; auto.
    - intros.
      match goal with
      | [ H : forall _ _, get_heaptype _ _ = Some _ -> _,
          H' : get_heaptype _ _ = Some _ |- _ ] =>
        specialize (H _ _ H');
        inversion H; subst; simpl in *; auto
      end.
      match goal with
      | [ H : get_heaptype ?L ?S = Some ?HT,
          H' : M.is_empty ?S = true |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : get_heaptype L S = None);
        [ apply get_heaptype_empty; auto | ];
        rewrite H0 in H; inversion H
      end.
  Qed.

  Lemma SplitStoreTypings_remove_empty_cons : forall {Ss S1 S},
      SplitStoreTypings (S1 :: Ss) S ->
      M.is_empty (LinTyp S1) = true ->
      SplitStoreTypings Ss S.
  Proof.
    intros.
    unfold SplitStoreTypings in *; destructAll.
    match goal with
    | [ H : Forall _ (_ :: _) |- _ ] =>
      inversion H; subst; simpl in *
    end.
    constructor; auto.
    eapply SplitHeapTypings_remove_empty_heap; eauto.
  Qed.

  Lemma SplitStoreTypings_remove_empty : forall {Ss S1 S idx},
      SplitStoreTypings Ss S ->
      nth_error Ss idx = Some S1 ->
      M.is_empty (LinTyp S1) = true ->
      SplitStoreTypings (remove_nth Ss idx) S.
  Proof.
    intros.
    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] =>
      specialize (Permutation_remove_nth H)
    end.
    intros.
    match goal with
    | [ H : Permutation.Permutation ?L1 ?L2,
        H' : SplitStoreTypings ?L1 ?S |- _ ] =>
      specialize (SplitStoreTypings_permut _ _ _ H H')
    end.
    intros.
    eapply SplitStoreTypings_remove_empty_cons; eauto.
  Qed.

  Lemma SplitHeapTypings_remove_one_cons_weak : forall {S S1 S2 S3},
      SplitHeapTypings [S2; S1] S ->
      SplitHeapTypings [S3; S1] S ->
      eq_map S2 S3.
  Proof.
    intros.
    unfold eq_map; intros.
    match goal with
    | [ |- ?A = _ ] =>
      remember A as opt; generalize (eq_sym Heqopt); case opt; intros
    end.
    - match goal with
      | [ H : SplitHeapTypings [?S; _] ?SP,
          H' : get_heaptype ?V ?S = Some ?HT |- _ ] =>
        let H'' := fresh "H" in
        assert (H'' : get_heaptype V SP = Some HT);
        [ eapply SplitHeapTypings_get_heaptype_LinTyp;
          [ eauto | | exact H ]; constructor; auto | ]
      end.
      match goal with
      | [ H : SplitHeapTypings [?S; _] ?SP,
          H''' : get_heaptype ?V ?S = Some ?HT,
          H' : get_heaptype ?V ?SP = Some ?HT |- _ ] =>
        let H'' := fresh "H" in
        destruct H as [H'' H];
        specialize (H _ _ H');
        inversion H; subst; simpl in *
      end.
      -- match goal with
         | [ H : ExactlyInOne true _ _ _ |- _ ] =>
           inversion H; subst; simpl in *
         end.
         match goal with
         | [ H : SplitHeapTypings _ ?S,
             H' : get_heaptype _ ?S = Some _ |- _ ] =>
           let H'' := fresh "H" in
           destruct H as [H'' H];
           specialize (H _ _ H');
           inversion H; subst; simpl in *;
           [ apply eq_sym; auto | ]
         end.
         match goal with
         | [ H : ExactlyInOne false _ _ [_] |- _ ] =>
           inversion H; subst; simpl in *
         end.
         --- match goal with
             | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
               rewrite H in H'; inversion H'
             end.
         --- match goal with
             | [ H : ExactlyInOne false _ _ [] |- _ ] =>
               inversion H
             end.
      -- match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
    - match goal with
      | [ H : get_heaptype ?L ?S = None,
          H' : SplitHeapTypings [?S; _] ?SP |- _ ] =>
        remember (get_heaptype L SP) as opt2;
        generalize (eq_sym Heqopt2);
        case opt2; intros
      end.
      -- match goal with
         | [ H : SplitHeapTypings [?SP; _] ?S,
             H' : get_heaptype _ ?S = Some _,
             H'' : get_heaptype _ ?SP = None |- _ ] =>
           specialize (SplitHeapTypings_inv H' H)
         end.
         intros; destructAll.
         match goal with
         | [ H : List.In _ [_; _] |- _ ] =>
           inversion H; subst; simpl in *
         end.
         --- match goal with
             | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
               rewrite H in H'; inversion H'
             end.
         --- match goal with
             | [ H : _ \/ False |- _ ] =>
               case H; intros; [ | exfalso; auto ]; subst
             end.
             match goal with
             | [ H : SplitHeapTypings [?S; _] ?SW,
                 H' : get_heaptype _ ?SW = Some _
                 |- _ = get_heaptype _ ?S ] =>
               let H'' := fresh "H" in
               destruct H as [H'' H];
               specialize (H _ _ H')
             end.
             match goal with
             | [ H : ExactlyInOne _ _ _ _ |- _ ] =>
               inversion H; subst; simpl in *;
               [ | apply eq_sym; auto ]
             end.
             match goal with
             | [ H : ExactlyInOne _ _ _ _ |- _ ] =>
               inversion H; subst; simpl in *
             end.
             match goal with
             | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
               rewrite H in H'; inversion H'
             end.
      -- match goal with
         | [ |- None = ?A ] =>
           remember A as opt3;
           generalize (eq_sym Heqopt3);
           case opt3; intros; auto
         end.
         match goal with
         | [ H : SplitHeapTypings [?S; _] ?SP,
             H' : get_heaptype ?V ?S = Some ?HT |- _ ] =>
           let H'' := fresh "H" in
           assert (H'' : get_heaptype V SP = Some HT);
           [ | rewrite <-H''; apply eq_sym; auto ]
         end.
         eapply SplitHeapTypings_get_heaptype_LinTyp; eauto.
         constructor; auto.
  Qed.

  Lemma SplitStoreTypings_remove_one_cons_weak : forall {S S1 S2 S3},
      SplitStoreTypings [S2; S1] S ->
      SplitStoreTypings [S3; S1] S ->
      StoreTyping_eq S2 S3.
  Proof.
    intros.
    unfold StoreTyping_eq.
    split; [ solve_inst_or_unr_typ_eq | ].
    split; [ | solve_inst_or_unr_typ_eq ].
    unfold SplitStoreTypings in *.
    destructAll.
    simpl in *.
    eapply SplitHeapTypings_remove_one_cons_weak; eauto.
  Qed.  

  Lemma SplitStoreTypings_remove_one_cons : forall {Ss S1 S2 S},
      SplitStoreTypings [S1; S2] S ->
      SplitStoreTypings (S1 :: Ss) S ->
      SplitStoreTypings Ss S2.
  Proof.
    intros.
    match goal with
    | [ H : SplitStoreTypings [?A; ?B] ?S |- _ ] =>
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings [B; A] S);
      [ eapply SplitStoreTypings_permut; [ | exact H ]; constructor | ];
      clear H
    end.
    match goal with
    | [ H : SplitStoreTypings (?A :: ?B) ?S,
        H'' : SplitStoreTypings [_; _] _ |- _ ] =>
      replace (A :: B) with ([A] ++ B) in H by auto;
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings (B ++ [A]) S);
      [ eapply SplitStoreTypings_permut; [ | exact H ];
        apply Permutation.Permutation_app_comm | ];
      clear H;
      specialize (SplitStoreTypings_split H')
    end.
    intros; destructAll.
    eapply SplitStoreTyping_eq; eauto.
    eapply SplitStoreTypings_remove_one_cons_weak; eauto.
  Qed.

  Lemma SplitStoreTypings_remove_one : forall Ss S1 S2 S idx,
      SplitStoreTypings Ss S ->
      SplitStoreTypings [S1; S2] S ->
      nth_error Ss idx = Some S1 ->
      SplitStoreTypings (set_nth Ss idx (empty_LinTyp S2)) S2.
  Proof.
    intros.
    match goal with
    | [ |- context[set_nth ?SS ?IDX ?EL] ] =>
      let H := fresh "H" in
      assert (H : nth_error (set_nth SS IDX EL) IDX = Some EL)
    end.
    { apply nth_error_set_nth.
      eapply nth_error_Some_length; eauto. }
    eapply SplitStoreTypings_permut;
      [ eapply Permutation.Permutation_sym; eapply Permutation_remove_nth; eauto | ].
    rewrite remove_nth_set_nth.
    apply SplitStoreTypings_add_empty_LinTyp.
    match goal with
    | [ H : nth_error _ _ = Some _,
        H' : nth_error (set_nth _ _ _) _ = Some _ |- _ ] =>
      specialize (Permutation_remove_nth H); intros
    end.
    match goal with
    | [ H : Permutation.Permutation ?L1 ?L2,
        H' : SplitStoreTypings ?L1 ?S |- _ ] =>
      specialize (SplitStoreTypings_permut _ _ _ H H')
    end.
    intros.
    eapply SplitStoreTypings_remove_one_cons; eauto.
  Qed.

  Ltac replace_set_nth_with_remove_nth_hyp :=
    match goal with
    | [ H : SplitStoreTypings (set_nth ?SS ?IDX ?EL) ?S |- _ ] =>
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings (EL :: (remove_nth SS IDX)) S);
      [ | clear H ]
    end;
    [ eapply SplitStoreTypings_permut; [ | eauto ];
      match goal with
      | [ |- context[set_nth _ _ ?EL] ] =>
        rewrite <-(remove_nth_set_nth _ _ EL)
      end;
      apply Permutation_remove_nth;
      apply nth_error_set_nth;
      eapply nth_error_Some_length; eauto | ].

  Ltac replace_set_nth_with_remove_nth_goal :=
    match goal with
    | [ |- SplitStoreTypings (set_nth ?SS ?IDX ?EL) ?S ] =>
      let H := fresh "H" in
      assert (H : SplitStoreTypings (EL :: (remove_nth SS IDX)) S)
    end;
    [ |
      eapply SplitStoreTypings_permut; [ | eauto ];
      apply Permutation.Permutation_sym;
      match goal with
      | [ |- context[set_nth _ _ ?EL] ] =>
        rewrite <-(remove_nth_set_nth _ _ EL)
      end;
      apply Permutation_remove_nth;
      apply nth_error_set_nth;
      eapply nth_error_Some_length; eauto ].

  Ltac add_remove_nth_to_hyp :=
    match goal with
    | [ H : SplitStoreTypings ?SS ?S,
        H' : nth_error ?SS ?IDX = Some ?SP |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings (SP :: (remove_nth SS IDX)) S);
      [ | clear H ]
    end;
    [ eapply SplitStoreTypings_permut; [ | eauto ];
      apply Permutation_remove_nth; auto | ].
                   
  Lemma SplitStoreTypings_StructSet_add_one : forall {Ss Ss' S1 S2 S3 S S' S'' idx idx2},
      SplitStoreTypings Ss S ->
      nth_error Ss idx = Some S' ->
      SplitStoreTypings Ss' S' ->
      nth_error Ss' idx2 = Some S'' ->
      M.is_empty (LinTyp S'') = true ->
      SplitStoreTypings [S1; S] S2 ->
      SplitStoreTypings (set_nth Ss' idx2 S1) S3 ->
      SplitStoreTypings (set_nth Ss idx S3) S2.
  Proof.
    intros.
    match goal with
    | [ H : SplitStoreTypings ?SS ?S,
        H' : nth_error ?SS _ = Some ?SP,
        H'' : M.is_empty (LinTyp ?SP) = true |- _ ] =>
      specialize (SplitStoreTypings_remove_empty H H' H'');
      clear H
    end.
    intros.
    replace_set_nth_with_remove_nth_hyp.
    add_remove_nth_to_hyp.
    replace_set_nth_with_remove_nth_goal.
    eapply SplitStoreTypings_trans_gen_inv; eauto.
    2-3: solve_inst_or_unr_typ_eq.
    simpl.
    match goal with
    | [ |- context[?A :: ?B] ] =>
      replace (A :: B) with ([A] ++ B) by auto
    end.
    eapply SplitStoreTypings_permut;
      [ apply Permutation.Permutation_app_comm | ].
    match goal with
    | [ H : SplitStoreTypings [?A; ?B] ?S |- _ ] =>
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings [B; A] S);
      [ eapply SplitStoreTypings_permut; [ | eauto ];
        constructor | ];
      clear H
    end.
    eapply SplitStoreTypings_trans_gen; eauto.
    eapply SplitStoreTypings_trans_gen; eauto.       
  Qed.

  Lemma SplitStoreTypings_StructSwap_remove_add_one : forall {Ss S idx S' Ss' idx2 S'' Srest S1 S2 S3},
      SplitStoreTypings Ss S ->
      nth_error Ss idx = Some S' ->
      SplitStoreTypings Ss' S' ->
      nth_error Ss' idx2 = Some S'' ->
      SplitStoreTypings [S''; Srest] S ->
      SplitStoreTypings [S1; Srest] S2 ->
      SplitStoreTypings (set_nth Ss' idx2 S1) S3 ->
      SplitStoreTypings (set_nth Ss idx S3) S2.
  Proof.
    intros.
    replace_set_nth_with_remove_nth_hyp.
    replace_set_nth_with_remove_nth_goal.
    add_remove_nth_to_hyp.
    
    match goal with
    | [ H : SplitStoreTypings _ ?S,
        H' : SplitStoreTypings [_; _] ?S |- _ ] =>
      revert H'
    end.
    add_remove_nth_to_hyp.
    intros.

    eapply SplitStoreTypings_trans_gen_inv; eauto.
    2-3: solve_inst_or_unr_typ_eq.
    simpl.
    match goal with
    | [ |- context[?A :: ?B] ] =>
      replace (A :: B) with ([A] ++ B) by auto
    end.
    eapply SplitStoreTypings_permut;
      [ apply Permutation.Permutation_app_comm | ].
    match goal with
    | [ H : SplitStoreTypings [?A; ?B] ?S
        |- SplitStoreTypings _ ?S ] =>
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings [B; A] S);
      [ eapply SplitStoreTypings_permut; [ | eauto ];
        constructor | ];
      clear H
    end.
    eapply SplitStoreTypings_trans_gen; eauto.
    eapply SplitStoreTypings_remove_one_cons; eauto.
    rewrite app_comm_cons.
    eapply SplitStoreTypings_trans_gen; eauto.
  Qed.

  Lemma SplitStoreTypings_split_and_replace_empty : forall {S_ignore Swhole Shead Shead1 Shead2 Stail j Stailj},
      SplitStoreTypings (Shead :: S_ignore ++ Stail) Swhole ->
      SplitStoreTypings [Shead1; Shead2] Shead ->
      nth_error Stail j = Some Stailj ->
      M.is_empty (LinTyp Stailj) = true ->
      SplitStoreTypings (Shead2 :: S_ignore ++ (set_nth Stail j Shead1)) Swhole.
  Proof.
    intros.
    match goal with
    | [ |- SplitStoreTypings (?S1 :: ?S2 ++ (set_nth ?SS ?IDX ?EL)) ?S ] =>
      let H := fresh "H" in
      assert (H : SplitStoreTypings (S1 :: S2 ++ (EL :: remove_nth SS IDX)) S)
    end.
    2:{
      eapply SplitStoreTypings_permut; [ | eauto ].
      constructor.
      eapply Permutation.Permutation_app; auto.
      match goal with
      | [ |- context[set_nth _ _ ?EL] ] =>
        rewrite <-(remove_nth_set_nth _ _ EL)
      end.
      apply Permutation.Permutation_sym.
      apply Permutation_remove_nth.
      apply nth_error_set_nth.
      eapply nth_error_Some_length; eauto.
    }
    match goal with
    | [ |- SplitStoreTypings (?S1 :: ?SS1 ++ ?S2 :: ?SS2) ?S ] =>
      let H := fresh "H" in
      assert (H : SplitStoreTypings ([S2; S1] ++ (SS1 ++ SS2)) S)
    end.
    2:{
      eapply SplitStoreTypings_permut; [ | eauto ].
      eapply Permutation.Permutation_trans;
        [ apply Permutation.perm_swap | ].
      constructor.
      match goal with
      | [ |- Permutation.Permutation (?A :: ?B) _ ] =>
        replace (A :: B) with ([A] ++ B) by auto
      end.
      eapply Permutation.Permutation_trans;
        [ apply Permutation.Permutation_app_comm | ].
      rewrite <-app_assoc.
      apply Permutation.Permutation_app; auto.
      apply Permutation.Permutation_app_comm.
    }
    eapply SplitStoreTypings_trans_gen; eauto.
    match goal with
    | [ H : nth_error ?SS2 ?IDX = Some ?SP
        |- SplitStoreTypings
             (?S :: ?SS1 ++ (remove_nth ?SS2 ?IDX)) ?SW ] =>
      let H' := fresh "H" in
      assert (H' : SplitStoreTypings
                     (SP :: S :: SS1 ++ (remove_nth SS2 IDX)) SW)
    end.
    { eapply SplitStoreTypings_permut; [ | eauto ].
      eapply Permutation.Permutation_trans;
        [ | apply Permutation.perm_swap ].
      constructor.
      match goal with
      | [ |- Permutation.Permutation _ (?A :: ?B) ] =>
        replace (A :: B) with ([A] ++ B) by auto
      end.
      eapply Permutation.Permutation_trans;
        [ | apply Permutation.Permutation_app_comm ].
      rewrite <-app_assoc.
      apply Permutation.Permutation_app; auto.
      eapply Permutation.Permutation_trans;
        [ | apply Permutation.Permutation_app_comm ].
      simpl.
      apply Permutation_remove_nth; auto. }
    eapply SplitStoreTypings_remove_empty_cons; eauto.
  Qed.

  Theorem eq_map_Dom_ht: forall {T} m1 m2,
    eq_map m1 m2 -> @Dom_ht T m1 <--> Dom_ht m2.
  Proof.
    unfold eq_map. unfold get_heaptype. unfold Dom_ht. unfold Ensembles.In.
    unfold Dom_map.
    intros.
    split; unfold Ensembles.Included; intros;
      unfold Ensembles.In in *; intros; destruct H0; specialize (H x); exists x0;
      rewrite <- H0; auto.
  Qed.

  
End Splitting. 

