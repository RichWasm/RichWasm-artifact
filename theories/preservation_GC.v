From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.map_util
        RWasm.typing_util RWasm.tactics RWasm.list_util RWasm.EnsembleUtil
        RWasm.splitting RWasm.surface RWasm.memory RWasm.subst RWasm.debruijn
        RWasm.misc_util RWasm.preservation.

Module PreservationGC (M : Memory) (T : MemTyping M).

  Module Red := Reduction M T.

  Import M T Red Utils.


  (* TODO move -- duplicate *)
  Definition HasTypeLocal S vs L :=
    let (loctaus, locis) := split L in
    Forall2
      (fun (v : Value) (tau : Typ) => HasTypeValue S empty_Function_Ctx v tau)
      vs loctaus ->
    Forall2
      (fun (tau : Typ) (i : Size) =>
         exists j : Size,
           sizeOfType (type empty_Function_Ctx) tau = Some j /\
           SizeLeq [] j i =
           Some true) loctaus locis.


  Definition mem (m : Mem) (l : M.Loc) (h : t) :=
    match get l m h with
    | Some _ => true
    | None => false
    end.


  Definition remove_heaptype {A : Type} (l : N) (ht : map_util.M.t A) :=
    M.remove (N.succ_pos l) ht.


  Definition restrict_StoreTyping (S : StoreTyping) (H : t) (H' : t) :=
    let (i, lin, unr) := S in
    let lin' := List.fold_left
                  (fun lin' '(l, v, len) => if mem Linear l H'
                                            then lin'
                                            else remove_heaptype l lin') (to_list Linear H) lin in

    let unr' := List.fold_left
                  (fun unr' '(l, v, len) => if mem Unrestricted l H'
                                            then unr'
                                            else remove_heaptype l unr') (to_list Unrestricted H) unr in
    Build_StoreTyping i lin' unr'.


  Lemma reachable_roots m t S :
    S \subset L.reach m t S.
  Proof.
    intros l Hin. exists 0. split; eauto.
    constructor.
  Qed.

  Lemma restrict_StoreTyping_InstTyp S h1 h2 :
    InstTyp (restrict_StoreTyping S h1 h2) = InstTyp S.
  Proof.
    unfold restrict_StoreTyping. destruct S; simpl. reflexivity.
  Qed.


  Lemma restrict_StoreTyping_submap S h1 h2 :
    sub_map (LinTyp (restrict_StoreTyping S h1 h2)) (LinTyp S).
  Proof.
    intros l ht. destruct S; simpl.
    revert LinTyp.
    generalize (to_list Linear h1).

    intros locs; induction locs; intros Lin Hget; simpl in *.
    - eassumption.
    - destruct a as [[? ?] ?]. simpl in *.
      eapply IHlocs in Hget.
      destruct (mem Linear l0 h2). eassumption.

      eapply typing.M.find_1.
      eapply typing.M.find_2 in Hget.

      eapply M.remove_3 in Hget. eassumption.
  Qed.

  Lemma restrict_StoreTyping_submap_Unr S h1 h2 :
    sub_map (UnrTyp (restrict_StoreTyping S h1 h2)) (UnrTyp S).
  Proof.
    intros l ht. destruct S; simpl.
    revert UnrTyp.
    generalize (to_list Unrestricted h1).

    intros locs; induction locs; intros Lin Hget; simpl in *.
    - eassumption.
    - destruct a as [[? ?] ?]. simpl in *.
      eapply IHlocs in Hget.
      destruct (mem Unrestricted l0 h2). eassumption.

      eapply typing.M.find_1.
      eapply typing.M.find_2 in Hget.

      eapply M.remove_3 in Hget. eassumption.
  Qed.

  Lemma exists_succ_pos : forall p, exists n, p = N.succ_pos n.
  Proof.
    intros p.
    destruct p.
    + exists (2 * (N.pos p))%N. reflexivity.
    + exists (2 * N.pos p - 1)%N. simpl. lia.
    + exists 0%N. reflexivity.
  Qed.


  Lemma empty_submap A (m1 m2 : map_util.M.t A) :
    sub_map m1 m2 ->
    M.is_empty m2 = true ->
    M.is_empty m1 = true.
  Proof.
    intros Hm1 Heq.
    eapply PositiveMap.is_empty_2 in Heq.
    eapply PositiveMap.is_empty_1.
    intros x a Hin.
    destruct (exists_succ_pos x). subst.
    eapply Hm1 in Hin. eapply Heq. eassumption.
  Qed.

  Import MemUtils.

  (* TODO move *)
  Lemma free_dom l m h h' :
    free l m h = Some h' ->
    dom m h <--> l |: dom m h'.
  Proof.
    intros Hf. split; intros l' Hin'; inv Hin'.
    - destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      now sets.
      eapply get_free_o in Hf; eauto.
      right. eexists. rewrite Hf. eassumption.
    - inv H.
      destruct (get l' m h) eqn:Heq; eauto.
      eexists. eassumption.
      eapply free_spec2 in Heq. congruence.
    - inv H.
      destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      eapply get_free_s in Hf; eauto. congruence.
      eapply get_free_o in Hf; eauto. eexists.
      rewrite <- Hf. eassumption.
  Qed.

  Lemma FromList_dom h m :
    FromList (map (fun x => fst (fst x)) (to_list m h)) <--> dom m h.
  Proof.
    split; intros l Hin.

    - eapply in_map_iff in Hin.  destructAll. destruct x as [[? ?] ?].

      eapply In_nth_error in H0. destructAll.
      simpl.
      eapply in_to_list_implies_get in H. eexists. eassumption.

    - edestruct Hin.

      eapply in_map_iff.  destruct x. exists (l, v, l0).
      simpl. split; eauto.
      eapply get_implies_in_to_list in H. destructAll.
      eapply nth_error_In. eassumption.
  Qed.

  Definition suffix_of {A} (l : list A) l2 :=
    exists l1, l = l1 ++ l2.

  Lemma in_suff_implies_not_NoDup : forall {A} {l'} {l : list A} {el l''},
      l = l' ++ el :: l'' ->
      In el l'' ->
      ~ NoDup l.
  Proof.
    induction l'; intros; simpl in *; subst.
    - intro H'; inversion H'; subst; eauto.
    - intro H'; inversion H'; subst; eauto.
      eapply IHl'; eauto.
  Qed.

  Lemma to_list_NoDup_loc_provable : forall {m h l},
      suffix_of (to_list m h) l ->
      NoDup (map (fun x : M.Loc * M.Val * Len => fst (fst x)) l).
  Proof.
    induction l.
    - intros; constructor.
    - intros; simpl; constructor.
      -- destruct_prs; simpl in *.
         intro.
         unfold suffix_of in *.
         destructAll.
         match goal with
         | [ H : In _ (map _ _) |- _ ] =>
           apply in_map_inv in H
         end.
         destructAll.
         destruct_prs.
         simpl in *.
         match goal with
         | [ H : ?L = _ ++ ?TPL :: _ |- _ ] =>
           let H' := fresh "H" in
           assert (H' : In TPL L); [ rewrite H | ]
         end.
         { apply in_or_app.
           right.
           constructor; auto. }
         match goal with
         | [ H : ?L = _ ++ _ :: ?L2, H' : In ?TPL ?L2 |- _ ] =>
           let H' := fresh "H" in
           assert (H' : In TPL L); [ rewrite H | ]
         end.
         { apply in_or_app.
           right.
           constructor 2; auto. }
         repeat match goal with
                | [ H : In _ (to_list _ _) |- _ ] =>
                  apply In_nth_error in H; destructAll
                end.
         repeat match goal with
                | [ H : nth_error (to_list _ _) _ = Some _ |- _ ] =>
                  apply in_to_list_implies_get in H
                end.
         match goal with
         | [ H : ?A = _, H' : ?A = _ |- _ ] =>
           rewrite H in H'; inversion H'; subst
         end.
         match goal with
         | [ H: _ = _ ++ _ :: _, H' : In _ _ |- _ ] =>
           specialize (in_suff_implies_not_NoDup H H')
         end.
         let H := fresh "H" in intro H; apply H.
         apply to_list_NoDup.
      -- apply IHl.
         unfold suffix_of in *.
         destructAll.
         match goal with
         | [ H : _ = ?A ++ ?B :: ?C |- _ ] =>
           exists (A ++ [B])
         end.
         rewrite <-app_assoc; simpl; auto.
  Qed.         

  Lemma to_list_NoDup_loc : forall m h, NoDup (map (fun x : M.Loc * M.Val * Len => fst (fst x)) (to_list m h)).
  Proof.
    intros.
    eapply to_list_NoDup_loc_provable; eauto.
    exists []; simpl; eauto.
  Qed.

  Lemma mem_in_dom l m h :
    mem m l h = true -> l \in dom m h.
  Proof.
    unfold mem. intros Hmem.
    destruct (get l m) eqn:Hget; try congruence. eexists. eassumption.
  Qed.

  Lemma Union_Setminus_Disjoint_eq A (S S' : Ensembles.Ensemble A) :
    Ensembles.Disjoint _ S S' ->
    S <--> ((S :|: S') \\ S').
  Proof.
    intros Hd.
    rewrite Setminus_Union_distr.
    rewrite (Setminus_Included_Empty_set S'); now sets.
  Qed.

  Lemma succ_pos_inj p1 p2 :
    N.succ_pos p1 = N.succ_pos p2 -> p1 = p2.
  Proof.
    intros Heq. destruct p1; destruct p2; simpl in *; eauto; lia.
  Qed.

  Lemma remove_heaptype_dom_ht_Some A l m ht :
    get_heaptype l m = Some ht ->
    l |: Dom_ht (remove_heaptype l m) <--> @Dom_ht A m.
  Proof.
    intros Hget. split; intros l' Hin.
    - destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      + now eexists; eauto.
      + inv Hin. inv H. congruence. inv H. unfold remove_heaptype in H0.
        rewrite M.gro in H0. eexists. eassumption.
        intros Hc. eapply n.
        eapply succ_pos_inj  in Hc. congruence.
    - destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      + sets.
      + right. inv Hin. eexists. unfold remove_heaptype.
        rewrite M.gro. eassumption.
        intros Hc. eapply n.
        eapply succ_pos_inj  in Hc. congruence.
  Qed.

  Lemma remove_heaptype_dom_ht_None A l m :
    get_heaptype l m = None ->
    Dom_ht (remove_heaptype l m) <--> @Dom_ht A m.
  Proof.
    intros Hget. split; intros l' Hin.
    - destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      + inv Hin. unfold remove_heaptype, get_heaptype in *.
        rewrite M.grs in H. congruence.
      + inv Hin. unfold remove_heaptype, get_heaptype in *.
        rewrite M.gro in H. eexists. eassumption.
        intros Hc. eapply n.
        eapply succ_pos_inj  in Hc. congruence.
    - destruct (OrderedTypeEx.N_as_OT.eq_dec l l'); subst.
      + inv Hin. unfold get_heaptype in *. congruence.
      + inv Hin. eexists. unfold remove_heaptype.
        rewrite M.gro. eassumption.
        intros Hc. eapply n.
        eapply succ_pos_inj  in Hc. congruence.
  Qed.

  Lemma remove_heaptype_not_In A l m :
    ~ l \in Dom_ht (@remove_heaptype A l m).
  Proof.
    intros Hin. inv Hin.
    unfold remove_heaptype in *.
    rewrite M.grs in H. congruence.
  Qed.

  Lemma get_heaptype_None_not_In A l m :
    @get_heaptype A l m = None ->
    ~ l \in Dom_ht m.
  Proof.
    intros Hget Hin. inv Hin.
    unfold get_heaptype in *.
    congruence.
  Qed.

  Lemma mem_non_in_dom l m h :
    mem m l h = false -> ~ l \in dom m h.
  Proof.
    unfold mem. intros Hmem Hnin.
    destruct (get l m) eqn:Hget; try congruence. inv Hnin. congruence.
  Qed.

  Lemma Dom_ht_restrict S h1 h2:
    Dom_ht (LinTyp (restrict_StoreTyping S h1 h2)) <--> Dom_ht (LinTyp S) \\ (dom_lin h1 \\ dom_lin h2).
  Proof.
    destruct S; simpl.
    revert LinTyp.

    assert (Heq : FromList (map (fun x => fst (fst x)) (to_list Linear h1)) <--> dom_lin h1).
    { eapply FromList_dom. }

    assert (Hnd : NoDup (map (fun x => fst (fst x)) (to_list Linear h1))).
    { eapply to_list_NoDup_loc. }

    revert Heq Hnd.

    generalize (to_list Linear h1).

    intros locs; revert h1; induction locs; intros h1 Heq Hnd Lin; simpl in *.

    - normalize_sets. rewrite <- Heq. normalize_sets. now sets.

    - normalize_sets. destruct a as [[? ?] ?]. simpl in *.

      assert (Hin : l \in dom_lin h1).
      { eapply Heq; sets. }
      destruct Hin. destruct x.
      eapply free_spec1 in H. destructAll.

      assert (Heq' :  FromList (map (fun x0 : M.Loc * M.Val * Len => fst (fst x0)) locs) <--> dom_lin x).
      { inv Hnd.
        unfold dom_lin in Heq. rewrite free_dom in Heq; [| eassumption ].
        rewrite Union_Setminus_Disjoint_eq with (S := FromList (map (fun x0 : M.Loc * M.Val * Len => fst (fst x0)) locs)) (S' := [set l]).
        rewrite Union_Setminus_Disjoint_eq with (S := dom_lin x) (S' := [set l]).

        now sets.

        eapply Disjoint_Singleton_r.
        intros Hin. destruct Hin. eapply get_free_s in H. congruence.

        eapply Disjoint_Singleton_r.
        intros Hin. eapply in_map_iff in Hin. destructAll.
        eapply H2. eapply in_map_iff. eexists. split; eauto. }

      destruct (mem Linear l h2) eqn:Hmem.

      + rewrite IHlocs with (h1 := x).

        * rewrite (free_dom _ _ _ _ H).

          rewrite Setminus_Union_distr.
          rewrite (Setminus_Included_Empty_set [set l]). now sets.
          eapply Singleton_Included.
          eapply mem_in_dom. eassumption.

        * eassumption.

        * inv Hnd. eassumption.

      + rewrite IHlocs with (h1 := x).

        * destruct (get_heaptype l Lin) eqn:Hget.

          -- rewrite <- (remove_heaptype_dom_ht_Some _ _ _ _ Hget).
             rewrite (free_dom _ _ _ _ H).
             rewrite Setminus_Union_distr.

             rewrite (Setminus_Included_Empty_set [set l]).

             normalize_sets.

             rewrite (Setminus_Union_distr [set l]).
             rewrite <- Setminus_Union.
             rewrite <- (Included_Setminus_Disjoint _ ([set l] \\ dom_lin h2)).
             now sets.

             eapply Setminus_Disjoint_preserv_r.
             eapply Disjoint_Singleton_r.
             eapply remove_heaptype_not_In.

             rewrite Setminus_Union_distr. eapply Included_Union_preserv_l.

             rewrite <- Included_Setminus_Disjoint. now sets.
             eapply Disjoint_Singleton_l.
             eapply mem_non_in_dom; eauto.

          -- rewrite remove_heaptype_dom_ht_None; eauto.
             rewrite (free_dom _ _ _ _ H).
             rewrite Setminus_Union_distr. rewrite <- Setminus_Union.

             rewrite <- (Included_Setminus_Disjoint _ ([set l] \\ dom_lin h2)).
             now sets.

             eapply Setminus_Disjoint_preserv_r.
             eapply Disjoint_Singleton_r.

             eapply get_heaptype_None_not_In. eassumption.
        * eassumption.
        * inv Hnd. eassumption.
  Qed.


  Lemma sub_map_None A l (S1 S2 : map_util.M.t A) :
    sub_map S1 S2 ->
    get_heaptype l S2 = None ->
    get_heaptype l S1 = None.
  Proof.
    intros H1 Hg.
    destruct (get_heaptype l S1) eqn:Hget; eauto.
    eapply H1 in Hget. congruence.
  Qed.


  Lemma Union_list_exists_l {A : Type} (x : A)
        (ls : list (Ensembles.Ensemble A)) S :
    In S ls -> Ensembles.In A S x ->
    Ensembles.In A (Union_list ls) x.
  Proof.
    intros Hin Hset. induction ls. inv Hin.
    inv Hin; simpl. now left.
    right; eauto.
  Qed.


  Lemma restrict_StoreTyping_Union_list Ss S h1 h2 :
    Union_list (map Dom_ht (map LinTyp Ss)) <--> Dom_ht (LinTyp S) ->
    Union_list (map Dom_ht (map LinTyp (map (fun S0 : StoreTyping => restrict_StoreTyping S0 h1 h2) Ss)))  <-->
    Dom_ht (LinTyp (restrict_StoreTyping S h1 h2)).
  Proof.
    intros H1; split; intros x Hin.
    - eapply Union_lists_exists in Hin. destructAll.
      eapply in_map_iff in H. destructAll.
      eapply in_map_iff in H2. destructAll.
      eapply in_map_iff in H2. destructAll.
      eapply Dom_ht_restrict.
      eapply Dom_ht_restrict in H0.
      inv H0.
      constructor; eauto. eapply H1.
      eapply In_Union_list; [| eassumption ].
      eapply in_map. eapply in_map. eassumption.
    - eapply Dom_ht_restrict in Hin. inv Hin.
      eapply H1 in H.
      eapply Union_lists_exists in H. destructAll.
      eapply in_map_iff in H. destructAll.
      eapply in_map_iff in H3. destructAll.
      eapply Union_list_exists_l.
      2:{ eapply Dom_ht_restrict. constructor; eauto. }
      eapply in_map. eapply in_map.

      eapply in_map with (f := (fun S0 : StoreTyping =>
                                  restrict_StoreTyping S0 h1 h2)).
      eassumption.
  Qed.

  Lemma Dom_ht_restrict_Urn S h1 h2:
    Dom_ht (UnrTyp (restrict_StoreTyping S h1 h2)) <--> Dom_ht (UnrTyp S) \\ (dom_unr h1 \\ dom_unr h2).
  Proof.
    destruct S; simpl.
    revert UnrTyp.

    assert (Heq : FromList (map (fun x => fst (fst x)) (to_list Unrestricted h1)) <--> dom_unr h1).
    { eapply FromList_dom. }

    assert (Hnd : NoDup (map (fun x => fst (fst x)) (to_list Unrestricted h1))).
    { eapply to_list_NoDup_loc. }

    revert Heq Hnd.

    generalize (to_list Unrestricted h1).

    intros locs; revert h1; induction locs; intros h1 Heq Hnd Unr; simpl in *.

    - normalize_sets. rewrite <- Heq. normalize_sets. now sets.

    - normalize_sets. destruct a as [[? ?] ?]. simpl in *.

      assert (Hin : l \in dom_unr h1).
      { eapply Heq; sets. }
      destruct Hin. destruct x.
      eapply free_spec1 in H. destructAll.

      assert (Heq' :  FromList (map (fun x0 : M.Loc * M.Val * Len => fst (fst x0)) locs) <--> dom_unr x).
      { inv Hnd.
        unfold dom_unr in Heq. rewrite free_dom in Heq; [| eassumption ].
        rewrite Union_Setminus_Disjoint_eq with (S := FromList (map (fun x0 : M.Loc * M.Val * Len => fst (fst x0)) locs)) (S' := [set l]).
        rewrite Union_Setminus_Disjoint_eq with (S := dom_unr x) (S' := [set l]).

        now sets.

        eapply Disjoint_Singleton_r.
        intros Hin. destruct Hin. eapply get_free_s in H. congruence.

        eapply Disjoint_Singleton_r.
        intros Hin. eapply in_map_iff in Hin. destructAll.
        eapply H2. eapply in_map_iff. eexists. split; eauto. }

      destruct (mem Unrestricted l h2) eqn:Hmem.

      + rewrite IHlocs with (h1 := x).

        * rewrite (free_dom _ _ _ _ H).

          rewrite Setminus_Union_distr.
          rewrite (Setminus_Included_Empty_set [set l]). now sets.
          eapply Singleton_Included.
          eapply mem_in_dom. eassumption.

        * eassumption.

        * inv Hnd. eassumption.

      + rewrite IHlocs with (h1 := x).

        * destruct (get_heaptype l Unr) eqn:Hget.

          -- rewrite <- (remove_heaptype_dom_ht_Some _ _ _ _ Hget).
             rewrite (free_dom _ _ _ _ H).
             rewrite Setminus_Union_distr.

             rewrite (Setminus_Included_Empty_set [set l]).

             normalize_sets.

             rewrite (Setminus_Union_distr [set l]).
             rewrite <- Setminus_Union.
             rewrite <- (Included_Setminus_Disjoint _ ([set l] \\ dom_unr h2)).
             now sets.

             eapply Setminus_Disjoint_preserv_r.
             eapply Disjoint_Singleton_r.
             eapply remove_heaptype_not_In.

             rewrite Setminus_Union_distr. eapply Included_Union_preserv_l.

             rewrite <- Included_Setminus_Disjoint. now sets.
             eapply Disjoint_Singleton_l.
             eapply mem_non_in_dom; eauto.

          -- rewrite remove_heaptype_dom_ht_None; eauto.
             rewrite (free_dom _ _ _ _ H).
             rewrite Setminus_Union_distr. rewrite <- Setminus_Union.

             rewrite <- (Included_Setminus_Disjoint _ ([set l] \\ dom_unr h2)).
             now sets.

             eapply Setminus_Disjoint_preserv_r.
             eapply Disjoint_Singleton_r.

             eapply get_heaptype_None_not_In. eassumption.
        * eassumption.
        * inv Hnd. eassumption.
  Qed.


  Lemma Dom_ht_restrict_lists Ss h1 h2:
    Union_list
      (map Dom_ht
           (map LinTyp
                (map (fun S0 : StoreTyping => restrict_StoreTyping S0 h1 h2) Ss))) \subset
      Union_list (map Dom_ht (map LinTyp Ss)).
  Proof.
    intros l Hc. eapply Union_lists_exists in Hc. destructAll.
    eapply in_map_iff in H. destructAll.
    eapply in_map_iff in H1. destructAll.
    eapply in_map_iff in H1. destructAll.
    eapply Dom_ht_restrict in H0. inv H0.
    eapply Union_list_exists_l; [| eassumption ].
    eapply in_map_iff. eexists. split. reflexivity.
    eapply in_map_iff. eexists; split; [| eassumption ].
    reflexivity.
  Qed.

  Lemma SplitStoreTypings_restrict_StoreTyping_list Ss S h1 h2:
    SplitStoreTypings Ss S ->
    SplitStoreTypings (map (fun S => restrict_StoreTyping S h1 h2) Ss)
                      (restrict_StoreTyping S h1 h2).
  Proof.
    intros Hs. destruct Hs. simpl in *.
    assert (Heq : Union_list (map Dom_ht (map LinTyp (map (fun S0 : StoreTyping => restrict_StoreTyping S0 h1 h2) Ss)))  <-->
                             Dom_ht (LinTyp (restrict_StoreTyping S h1 h2))).
    { eapply restrict_StoreTyping_Union_list. inv H0. eassumption. }

    constructor; simpl.
    - clear H0 Heq. induction H. now constructor.
      simpl in *. constructor; eauto.
      inv H. destruct S; destruct x; simpl in *. subst. eauto.

    - clear H. inv H0.
      split.

      + eassumption.

      + intros l ht Hget.
        assert (Hin : get_heaptype l (LinTyp S) = Some ht).
        { eapply restrict_StoreTyping_submap. eassumption. }
        eapply H1 in Hin.

        assert (Hdom : l \in Dom_ht (LinTyp (restrict_StoreTyping S h1 h2))).
        { eexists. eassumption. }

        eapply Heq in Hdom.

        clear Heq H H1 Hget.

        revert Hin. generalize false. induction Ss; intros b Hin.

        * eassumption.
        * inv Hin.
          -- simpl in *.

             destruct (get_heaptype l (LinTyp (restrict_StoreTyping a h1 h2))) eqn:Hget.

             ++ constructor.

                ** rewrite Hget. eapply restrict_StoreTyping_submap in Hget. congruence.

                ** eapply ExactlyInOne_true.
                   intros Hc. eapply ExactlyInOne_true_converse in H6.
                   eapply H6. eapply Dom_ht_restrict_lists.
                   eassumption.

             ++ inv Hdom.

                ** inv H. unfold get_heaptype in *. congruence.

                ** eapply ExactlyInOne_true_converse in H6.
                   exfalso. eapply H6. eapply Dom_ht_restrict_lists. eassumption.

          -- simpl in *.

             destruct (get_heaptype l (LinTyp (restrict_StoreTyping a h1 h2))) eqn:Hget.

             ++ eapply restrict_StoreTyping_submap in Hget. congruence.

             ++ inv Hdom. inv H. unfold get_heaptype in *; congruence.

                constructor. eassumption.

                eapply IHSs; eauto.
  Qed.

  Lemma SplitStoreTypings_restrict_StoreTyping S1 S2 S h1 h2:
    SplitStoreTypings [S1; S2] S ->
    SplitStoreTypings [restrict_StoreTyping S1 h1 h2; restrict_StoreTyping S2 h1 h2]
                      (restrict_StoreTyping S h1 h2).
  Proof.
    intros. eapply SplitStoreTypings_restrict_StoreTyping_list with (Ss := [S1; S2]).
    eassumption.
  Qed.


  Lemma reach_in_dom m S h l :
    l \in L.reach m h S ->
    l \in S \/ exists l' v len, get l' m h = Some (v, len) /\ l \in L.locs_HeapValue m v /\ l' \in L.reach m h S.
  Proof.
    intros Hin. inv Hin. destructAll.
    clear H. destruct x; simpl in *.
    - now left.
    - inv H0. destructAll. right.
      do 3 eexists. split; [| split ]; eauto.
      eexists. split. now constructor.
      eassumption.
  Qed.

  Lemma HasTypeValue_in_Dom_ht S F v t l :
    HasTypeValue S F v t ->
    l \in (L.locs_Value Linear v) ->
    l \in Dom_ht (LinTyp S).
  Proof.
    intros Hv. revert l.
    eapply HasTypeValue_ind'
      with (P := fun S F v t =>
                   forall (l : M.Loc) (Hin : Ensembles.In M.Loc (L.locs_Value Linear v) l), Ensembles.In N (Dom_ht (LinTyp S)) l); simpl; intros;
      try (now inv Hin); try (now eauto).

    - eapply SplitHeapTypings'_dom.
      + inv H. eapply SplitHeapTypings_spec. eassumption.

      + clear H. induction H0; eauto.

        simpl in *. inv Hin.

        * left. eauto.

        * right. eapply IHForall3. inv H1. inv H8. inv H7.
          constructor; eauto.
          eassumption.

    - inv Hin. eexists.
      unfold eq_map, get_heaptype in *.
      rewrite H. rewrite M.gss. reflexivity.
  Qed.

  Lemma HasHeapType_in_Dom_ht S hv ht l :
    HasHeapType S empty_Function_Ctx hv ht ->
    l \in (L.locs_HeapValue Linear hv) ->
    l \in Dom_ht (LinTyp S).
  Proof.
    intros Htyp Hin. destruct Htyp; simpl in *.
    - eapply HasTypeValue_in_Dom_ht; eauto.
    - eapply SplitHeapTypings'_dom.
      + inv H. eapply SplitHeapTypings_spec. eassumption.
      + clear H H1 H2. induction H0; simpl in *; eauto.

        inv Hin; eauto.
        * left. eapply HasTypeValue_in_Dom_ht; eauto.
        * right. eapply IHForall3; eauto.
    - eapply SplitHeapTypings'_dom.
      + inv H1. eapply SplitHeapTypings_spec. eassumption.
      + clear H1 H2. induction H3; simpl in *; eauto.

        inv Hin; eauto.
        * left. eapply HasTypeValue_in_Dom_ht; eauto.
        * right. eapply IHForall2; eauto.
    - eapply HasTypeValue_in_Dom_ht; eauto.
  Qed.


  Lemma HasTypeValue_in_locs_Value S F v t :
    HasTypeValue S F v t ->
    NoCapsTyp (heapable F) t = true ->
    Dom_ht (LinTyp S) \subset L.locs_Value Linear v.
  Proof.
    intros Hv.
    eapply HasTypeValue_ind'
      with (P := fun S F v t =>
                   NoCapsTyp (heapable F) t = true ->
                   Dom_ht (LinTyp S) \subset L.locs_Value Linear v); simpl in *; intros;

      try now (rewrite Dom_ht_is_empty; eauto; now sets); try congruence.


    - inv H. simpl in *. inv H4. clear H5.

      rewrite <- H. revert H0 H2. clear. intros Hall.
      induction Hall; intros Hcaps.

      + simpl in *. now sets.

      + simpl in *. repeat do_bools. eapply Union_Included.

        eapply Included_trans. eapply H. eassumption.
        now sets.

        now sets.

    - intros l' Hdom. inv Hdom.
      unfold eq_map, get_heaptype in *. rewrite H in H3.
      destruct (M.E.eq_dec (N.succ_pos l) (N.succ_pos l')).

      + eapply succ_pos_inj in e. subst. reflexivity.

      + rewrite M.gso in H3; eauto.
        rewrite M.gempty in H3. congruence.

    - eapply H0. eapply NoCapsPretype_subst; eassumption.

    - eapply H1. eapply NoCaps_subst_SLoc. eassumption. 

    - eassumption.
  Qed.

  
  Lemma HasHeapType_in_locs_HeapValue S hv ht :
    HasHeapType S empty_Function_Ctx hv ht ->
    NoCapsHeapType [] ht = true ->
    Dom_ht (LinTyp S) \subset L.locs_HeapValue Linear hv.
  Proof.
    intros Htyp Hin. inv Htyp; simpl in *.
    - eapply HasTypeValue_in_locs_Value; eauto.
      eapply forallb_forall. eassumption.
      eapply nth_error_In. eassumption.
    - rewrite <- H1 in Hin. simpl in *. inv H. simpl in *.
      inv H4. rewrite <- H.
      revert H0 Hin. clear. intros Hall Hc. induction Hall.
      + simpl. now sets.
      + simpl in *. repeat do_bools. eapply Included_Union_compat.
        eapply HasTypeValue_in_locs_Value. eassumption. eassumption.

        eapply IHHall. eassumption.

    - inv H1. simpl in *. inv H4. rewrite <- H1.
      revert H3 Hin. clear. intros Hall Hc. induction Hall.
      + simpl. now sets.
      + simpl in *. repeat do_bools. eapply Included_Union_compat.
        eapply HasTypeValue_in_locs_Value. eassumption. eassumption.

        eapply IHHall.

    - eapply HasTypeValue_in_locs_Value. eassumption.
      eapply NoCaps_subst; eassumption. 
  Qed.

  Lemma SplitHeapTypings_Disjoint S1 S2 S :
    SplitHeapTypings [S1; S2] S ->
    Ensembles.Disjoint _ (Dom_ht S1) (Dom_ht S2).
  Proof.
    intros Hs. inv Hs. constructor. intros l Hin. inv Hin.
    simpl in *.
    assert (Hin: l \in Dom_ht S).
    { eapply H; now left; eauto. }

    inv H1; inv H2.
    inv Hin. eapply H0 in H2. inv H2; unfold get_heaptype in *; [ | congruence ].

    inv H10.  unfold get_heaptype in *; congruence.
  Qed.

  Lemma SplitHeapTypings_Disjoint_lists S1 S2 S :
    SplitHeapTypings (S1 ++ S2) S ->
    Ensembles.Disjoint _ (Union_list (map Dom_ht S1)) (Union_list (map Dom_ht S2)).
  Proof.
    intros Hs. inv Hs. constructor. intros l Hin. inv Hin.

    assert (Hin: l \in Dom_ht S).
    { eapply H. rewrite map_app. eapply Union_list_app. now left. }

    inv Hin. eapply H0 in H3.

    eapply ExactlyInOne_app_inv in H3. inv H3; destructAll.

    - eapply ExactlyInOne_true_converse in H4. contradiction.

    - eapply ExactlyInOne_true_converse in H3. contradiction.

  Qed.


  Lemma HasTypeValue_GC F S Sheap Sprog Sother S' v t :
    forall roots h1 h2,
      HasTypeValue S F v t ->
      HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
      SplitStoreTypings (S :: Sother) Sprog ->
      SplitStoreTypings [Sprog; Sheap] S' ->
      L.collect_unr roots h1 h2 ->
      L.locs_Value Unrestricted v \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->
      HasTypeValue (restrict_StoreTyping S h1 h2) F v t.
  Proof.
    intros roots h1 h2 Ht. revert roots h1 h2 Sheap Sprog Sother S'.
    eapply HasTypeValue_ind' with
      (P := fun S F v t => forall roots h1 h2 Sheap Sprog Sother S'
                                  (Hmem : HasTypeMeminst Sheap Sprog h1)
                                  (Hsplit : SplitStoreTypings (S :: Sother) Sprog)
                                  (Hsplit' : SplitStoreTypings [Sprog;Sheap] S')
                                  (Hcol : L.collect_unr roots h1 h2)
                                  (Hlocsu : L.locs_Value Unrestricted v \subset (L.reach_unr h1 (roots :|: L.outset h1))),
                HasTypeValue (restrict_StoreTyping S h1 h2) F v t); intros; eauto;
    try (now econstructor; eauto; first [ eapply empty_submap; [ | eassumption ];
                                          eapply restrict_StoreTyping_submap ]).
    - econstructor; eauto.
      eapply SplitStoreTypings_restrict_StoreTyping_list. eassumption.

      revert H0 S0 Sheap Sprog Sother H Hmem Hsplit Hsplit' Hcol Hlocsu. clear. intros H0; induction H0;
        intros S0 Sheap Sprog Sother H' Hmem Hsplit Hsplit' Hcol Hlocsu.

      now constructor.


      constructor; eauto.

      + simpl in *. eapply H; try eassumption.

        now eapply SplitStoreTypings_merge' with (S1 := x :: l) (S3 := Sother); eauto.
        now sets.

      + simpl in *. assert (Hc := H'). eapply SplitStoreTypings_cons in Hc. destructAll.
        eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
        eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
        rewrite <- app_assoc in Hsplit.
        eapply SplitStoreTyping_app in Hsplit. destructAll.

        eapply IHForall3; [ eassumption | eassumption | eassumption | eassumption | eassumption | ].
        now sets.

    - econstructor; eauto.
      + eapply empty_submap; [ | eassumption ];
          eapply restrict_StoreTyping_submap.
      + assert (Hin : l \in Dom_ht (UnrTyp (restrict_StoreTyping S0 h1 h2))).
        { eapply Dom_ht_restrict_Urn. constructor.
          eexists. eassumption.
          intros Hc. inv Hc. simpl in *. inv Hcol. destructAll.
          inv H3. destruct x. eapply Singleton_Included_r in Hlocsu. eapply (H7 l v0 l0) in Hlocsu. inv Hlocsu.
          eapply H4; eexists; eauto. }

        inv Hin. assert (Hget := H3).
        eapply restrict_StoreTyping_submap_Unr in H3. subst_exp. eassumption.

    - econstructor.
      + destruct (get l Linear h2) eqn:Hget.
        * (* easy case *)
          intro l'. destruct (N.eq_dec l l'); subst.
          -- assert (Hin : l' \in  Dom_ht (LinTyp (restrict_StoreTyping S0 h1 h2))).
             { eapply Dom_ht_restrict. constructor. eexists.
               unfold eq_map, get_heaptype in *. rewrite H. rewrite M.gss. reflexivity.
               intros Hc. inv Hc. eapply H3. eexists. eassumption. }

             destruct Hin.
             unfold eq_map, get_heaptype in *. rewrite H2. rewrite M.gss.
             eapply restrict_StoreTyping_submap in H2.
             unfold eq_map, get_heaptype in *. rewrite H, M.gss in H2. congruence.
          -- unfold eq_map, get_heaptype in *.
             destruct (M.find (N.succ_pos l') (LinTyp (restrict_StoreTyping S0 h1 h2))) eqn:Hget'; eauto.
             eapply restrict_StoreTyping_submap in Hget'. unfold eq_map, get_heaptype in *.
             rewrite H in Hget'. now eauto.

             unfold eq_map, get_heaptype in *. rewrite M.gso, M.gempty. reflexivity.
             now eauto using succ_pos_inj.

        * inv Hcol. destructAll.
          assert (Hin : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) l).
          { inv Hmem. eapply H5. split; eauto. eapply H6.
            right. destruct Hsplit. simpl in *. inv H12. apply H13.
            simpl. left. eexists. unfold eq_map, get_heaptype in H. rewrite H, M.gss. reflexivity. }

          eapply reach_in_dom in Hin. inv Hin.

          -- exfalso. inv H6. inv H7. destructAll. revert H6 H7 Hmem Hsplit Hsplit' H. clear; intros Hget Hin Hmem Hsplit Hsplit' Heq.
             inv Hmem.
             eapply get_implies_in_to_list in Hget. destructAll. eapply nth_error_In in H4.
             eapply Forall2_exists_r in H3; eauto.
             destructAll.

             eapply HasHeapType_in_Dom_ht in H7; [| eassumption ].


             assert (Hdom: Ensembles.In N (Dom_ht (LinTyp Sheap)) l).
             { eapply SplitHeapTypings'_dom.
               eapply SplitHeapTypings_spec. inv H1. eassumption.
               rewrite !map_app. eapply Union_list_app. right.
               eapply Union_list_exists_l; [| eassumption ].

               do 2 eapply in_map. eassumption. }

             assert (Hget: l \in Dom_ht (LinTyp S0)).
             { eexists. unfold eq_map, get_heaptype in *. rewrite Heq.
               rewrite M.gss. reflexivity. }

             assert (Hget': l \in Dom_ht (LinTyp Sprog)).
             { inv Hsplit. inv H10. eapply H11. left. eassumption. }

             eapply SplitHeapTypings_Disjoint. inv Hsplit'. simpl in *. eassumption.
             split; eauto.

          -- exfalso. destructAll. revert H6 H7 Hmem Hsplit Hsplit' H. clear; intros Hget Hin Hmem Hsplit Hsplit' Heq.
             inv Hmem.
             eapply get_implies_in_to_list in Hget. destructAll. eapply nth_error_In in H4.
             eapply Forall2_exists_r in H4; eauto. destructAll.

             eapply HasHeapType_in_Dom_ht in H7; [| eassumption ].

             assert (Hdom: Ensembles.In N (Dom_ht (LinTyp Sheap)) l).
             { eapply SplitHeapTypings'_dom.
               eapply SplitHeapTypings_spec. inv H1. eassumption.
               rewrite !map_app. eapply Union_list_app. left.
               eapply Union_list_exists_l; [| eassumption ].

               do 2 eapply in_map. eassumption. }

             assert (Hget: l \in Dom_ht (LinTyp S0)).
             { eexists. unfold eq_map, get_heaptype in *. rewrite Heq.
               rewrite M.gss. reflexivity. }

             assert (Hget': l \in Dom_ht (LinTyp Sprog)).
             { inv Hsplit. inv H10. eapply H11. left. eassumption. }

             eapply SplitHeapTypings_Disjoint. inv Hsplit'. simpl in *. eassumption.
             split; eauto.

      + eassumption.
      + eassumption.

    - econstructor.
      + destruct (get l Linear h2) eqn:Hget.
        * (* easy case *)
          intro l'. destruct (N.eq_dec l l'); subst.
          -- assert (Hin : l' \in  Dom_ht (LinTyp (restrict_StoreTyping S0 h1 h2))).
             { eapply Dom_ht_restrict. constructor. eexists.
               unfold eq_map, get_heaptype in *. rewrite H. rewrite M.gss. reflexivity.
               intros Hc. inv Hc. eapply H3. eexists. eassumption. }

             destruct Hin.
             unfold eq_map, get_heaptype in *. rewrite H2. rewrite M.gss.
             eapply restrict_StoreTyping_submap in H2.
             unfold eq_map, get_heaptype in *. rewrite H, M.gss in H2. congruence.
          -- unfold eq_map, get_heaptype in *.
             destruct (M.find (N.succ_pos l') (LinTyp (restrict_StoreTyping S0 h1 h2))) eqn:Hget'; eauto.
             eapply restrict_StoreTyping_submap in Hget'. unfold eq_map, get_heaptype in *.
             rewrite H in Hget'. now eauto.

             unfold eq_map, get_heaptype in *. rewrite M.gso, M.gempty. reflexivity.
             now eauto using succ_pos_inj.

        * inv Hcol. destructAll.
          assert (Hin : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) l).
          { inv Hmem. eapply H5. split; eauto. eapply H6.
            right. destruct Hsplit. simpl in *. inv H12. apply H13.
            simpl. left. eexists. unfold eq_map, get_heaptype in H. rewrite H, M.gss. reflexivity. }

          eapply reach_in_dom in Hin. inv Hin.

          -- exfalso. inv H6. inv H7. destructAll. revert H6 H7 Hmem Hsplit Hsplit' H. clear; intros Hget Hin Hmem Hsplit Hsplit' Heq.
             inv Hmem.
             eapply get_implies_in_to_list in Hget. destructAll. eapply nth_error_In in H4.
             eapply Forall2_exists_r in H3; eauto.
             destructAll.

             eapply HasHeapType_in_Dom_ht in H7; [| eassumption ].


             assert (Hdom: Ensembles.In N (Dom_ht (LinTyp Sheap)) l).
             { eapply SplitHeapTypings'_dom.
               eapply SplitHeapTypings_spec. inv H1. eassumption.
               rewrite !map_app. eapply Union_list_app. right.
               eapply Union_list_exists_l; [| eassumption ].

               do 2 eapply in_map. eassumption. }

             assert (Hget: l \in Dom_ht (LinTyp S0)).
             { eexists. unfold eq_map, get_heaptype in *. rewrite Heq.
               rewrite M.gss. reflexivity. }

             assert (Hget': l \in Dom_ht (LinTyp Sprog)).
             { inv Hsplit. inv H10. eapply H11. left. eassumption. }

             eapply SplitHeapTypings_Disjoint. inv Hsplit'. simpl in *. eassumption.
             split; eauto.

          -- exfalso. destructAll. revert H6 H7 Hmem Hsplit Hsplit' H. clear; intros Hget Hin Hmem Hsplit Hsplit' Heq.
             inv Hmem.
             eapply get_implies_in_to_list in Hget. destructAll. eapply nth_error_In in H4.
             eapply Forall2_exists_r in H4; eauto. destructAll.

             eapply HasHeapType_in_Dom_ht in H7; [| eassumption ].

             assert (Hdom: Ensembles.In N (Dom_ht (LinTyp Sheap)) l).
             { eapply SplitHeapTypings'_dom.
               eapply SplitHeapTypings_spec. inv H1. eassumption.
               rewrite !map_app. eapply Union_list_app. left.
               eapply Union_list_exists_l; [| eassumption ].

               do 2 eapply in_map. eassumption. }

             assert (Hget: l \in Dom_ht (LinTyp S0)).
             { eexists. unfold eq_map, get_heaptype in *. rewrite Heq.
               rewrite M.gss. reflexivity. }

             assert (Hget': l \in Dom_ht (LinTyp Sprog)).
             { inv Hsplit. inv H10. eapply H11. left. eassumption. }

             eapply SplitHeapTypings_Disjoint. inv Hsplit'. simpl in *. eassumption.
             split; eauto.

      + eassumption.
      + eassumption.

    - econstructor; eauto.
      + eapply empty_submap; [ | eassumption ];
          eapply restrict_StoreTyping_submap.
      + destruct S0; eassumption.

  Qed.

  Lemma Permutation_In A (x : A) l :
    In x l -> exists l', Permutation.Permutation l (x :: l').
  Proof.
    intros Hin. induction l; inv Hin.

    - exists l. eauto.

    - eapply IHl in H. destructAll. exists (a :: x0).
      eapply Permutation.Permutation_trans.
      eapply Permutation.perm_skip. eassumption.
      eapply Permutation.perm_swap.
  Qed.



  Lemma Forall2_exists_r_two A B (P : A -> B -> Prop) l1 l2 x1 x2 :
    Forall2 P l1 l2 ->
    In x1 l2 -> In x2 l2 ->
    x1 <> x2 ->
    exists y1 y2 l1', Permutation.Permutation l1 (y1 :: y2 :: l1') /\ P y1 x1 /\ P y2 x2.
  Proof.
    intros Hall Hin1 Hin2 Hneq. induction Hall. now inv Hin1.

    inv Hin1.

    - inv Hin2. now congruence.
      eapply Forall2_exists_r in H0; [ | eassumption ].
      destructAll.

      eapply Permutation_In in H0. destructAll.
      do 3 eexists.
      split; [| split ]; [| eassumption | eassumption ].

      eapply Permutation.perm_skip. eassumption.

    - inv Hin2.

      + eapply Forall2_exists_r in H0; [ | eassumption ].
        destructAll.

        eapply Permutation_In in H0. destructAll.
        do 3 eexists.
        split; [| split ]; [| eassumption | eassumption ].

        eapply Permutation.Permutation_trans.
        eapply Permutation.perm_skip. eassumption.

        eapply Permutation.perm_swap.

      + specialize (IHHall H0 H1). destructAll.
        do 3 eexists. split; [| split ]; [| eassumption | eassumption ].

        eapply Permutation.Permutation_trans.
        eapply Permutation.perm_skip. eassumption.

        eapply Permutation.Permutation_trans.
        eapply Permutation.perm_swap.
        eapply Permutation.perm_skip.
        eapply Permutation.perm_swap.
  Qed.


  Transparent subst.subst'_type.

  Lemma HasTypeValue_GC_heap F S Sheap Sprog Sother S' v t :
    forall roots h1 h2,
      HasTypeValue S F v t ->
      HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
      SplitStoreTypings (S :: Sother) Sheap ->
      (exists m l' hv _len, get l' m h2 = Some (hv, _len) /\ L.locs_Value Linear v \subset L.locs_HeapValue Linear hv) ->
      NoCapsTyp (heapable F) t = true ->
      SplitStoreTypings [Sprog; Sheap] S' ->
      L.collect_unr roots h1 h2 ->
      L.locs_Value Unrestricted v \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->
      HasTypeValue (restrict_StoreTyping S h1 h2) F v t.
  Proof.
    intros roots h1 h2 Ht. revert roots h1 h2 Sheap Sprog Sother S'.
    eapply HasTypeValue_ind' with
      (P := fun S F v t => forall roots h1 h2 Sheap Sprog Sother S'
                                  (Hmem : HasTypeMeminst Sheap Sprog h1)
                                  (Hsplit : SplitStoreTypings (S :: Sother) Sheap)
                                  (Hex : exists m l' hv _len, get l' m h2 = Some (hv, _len) /\ L.locs_Value Linear v \subset L.locs_HeapValue Linear hv)
                                  (Hcap: NoCapsTyp (heapable F) t = true)
                                  (Hsplit' : SplitStoreTypings [Sprog;Sheap] S')
                                  (Hcol : L.collect_unr roots h1 h2)
                                  (Hlocsu : L.locs_Value Unrestricted v \subset (L.reach_unr h1 (roots :|: L.outset h1))),
                HasTypeValue (restrict_StoreTyping S h1 h2) F v t); intros; eauto;
    try (now econstructor; eauto; first [ eapply empty_submap; [ | eassumption ];
                                          eapply restrict_StoreTyping_submap ]);
    try (simpl in *; congruence).
    - econstructor; eauto.
      eapply SplitStoreTypings_restrict_StoreTyping_list. eassumption.

      revert H0 S0 Sheap Sprog Sother H Hmem Hsplit Hex Hcap Hsplit' Hcol Hlocsu. clear. intros H0; induction H0;
        intros S0 Sheap Sprog Sother H' Hmem Hsplit Hex Hcap Hsplit' Hcol Hlocsu.

      now constructor.


      constructor; eauto.

      + simpl in *. eapply H; try eassumption.

        * now eapply SplitStoreTypings_merge' with (S1 := x :: l) (S3 := Sother); eauto.

        * destructAll. do 4 eexists. split; eauto. eapply Included_trans; [| eapply H2 ]. now sets.

        * do_bools. eassumption.

        * now sets.

      + simpl in *. assert (Hc := H'). eapply SplitStoreTypings_cons in Hc. destructAll.
        eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
        eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
        rewrite <- app_assoc in Hsplit.
        eapply SplitStoreTyping_app in Hsplit. destructAll.

        eapply IHForall3; [ eassumption | eassumption | eassumption | | | eassumption | eassumption | ].
        * destructAll. do 4 eexists. split; eauto. eapply Included_trans; [| eassumption ]. now sets.

        * do_bools. eassumption.

        * now sets.

    - econstructor; eauto.
      + eapply empty_submap; [ | eassumption ];
          eapply restrict_StoreTyping_submap.
      + assert (Hin : l \in Dom_ht (UnrTyp (restrict_StoreTyping S0 h1 h2))).
        { eapply Dom_ht_restrict_Urn. constructor.
          eexists. eassumption.
          intros Hc. inv Hc. simpl in *. inv Hcol. destructAll.
          inv H3. destruct x3. eapply (H7 l v0 l0) in Hlocsu; [| reflexivity ]. destructAll.
          eapply H4; eexists; eauto. }

        inv Hin. assert (Hget := H3).
        eapply restrict_StoreTyping_submap_Unr in H3. subst_exp. eassumption.

    - econstructor.
      + destruct (get l Linear h2) eqn:Hget.
        * (* easy case *)
          intro l'. destruct (N.eq_dec l l'); subst.
          -- assert (Hin : l' \in  Dom_ht (LinTyp (restrict_StoreTyping S0 h1 h2))).
             { eapply Dom_ht_restrict. constructor. eexists.
               unfold eq_map, get_heaptype in *. rewrite H. rewrite M.gss. reflexivity.
               intros Hc. inv Hc. eapply H3. eexists. eassumption. }

             destruct Hin.
             unfold eq_map, get_heaptype in *. rewrite H2. rewrite M.gss.
             eapply restrict_StoreTyping_submap in H2.
             unfold eq_map, get_heaptype in *. rewrite H, M.gss in H2. congruence.
          -- unfold eq_map, get_heaptype in *.
             destruct (M.find (N.succ_pos l') (LinTyp (restrict_StoreTyping S0 h1 h2))) eqn:Hget'; eauto.
             eapply restrict_StoreTyping_submap in Hget'. unfold eq_map, get_heaptype in *.
             rewrite H in Hget'. now eauto.

             unfold eq_map, get_heaptype in *. rewrite M.gso, M.gempty. reflexivity.
             now eauto using succ_pos_inj.

        * exfalso. inv Hcol. destructAll.
          assert (Hin : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) l).
          { inv Hmem. eapply H5. split; eauto. eapply H8.
            left. destruct Hsplit. simpl in *. inv H14. apply H15.
            simpl. left. eexists. unfold eq_map, get_heaptype in H. rewrite H, M.gss. reflexivity. }

          simpl in *. eapply Singleton_Included_r in H7.

          eapply reach_in_dom in Hin. inv Hin.

          -- inv H8. inv H9. destructAll.

             destruct x.

             { eapply H10. now do 3 eexists; eauto. }

             eapply H2 in H6.

             eapply get_implies_in_to_list in H6.
             eapply get_implies_in_to_list in H8. destructAll.
             eapply nth_error_In in H6.
             eapply nth_error_In in H8.

             destruct Hmem.

             eapply Forall2_exists_r in H14; eauto.
             destructAll.

             eapply Forall2_exists_r in H15; eauto.
             destructAll.


             eapply SplitHeapTypings_Disjoint_lists.

             inv H13; simpl in *. rewrite map_app in H27. eassumption.

             split.

             ** eapply Union_list_exists_l. eapply in_map. eapply in_map. eassumption.

                eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

             ** eapply Union_list_exists_l. eapply in_map. eapply in_map. eassumption.

                eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

          -- inv H8. inv H9. destructAll.

             assert (Hsome := H6). eapply H2 in H6.

             eapply get_implies_in_to_list in H6.
             eapply get_implies_in_to_list in H8. destructAll.
             eapply nth_error_In in H6.
             eapply nth_error_In in H8.

             destruct Hmem.

             destruct x.

             ++ eapply Forall2_exists_r in H14; eauto.
                destructAll.

                eapply Forall2_exists_r in H15; eauto.
                destructAll.


                eapply SplitHeapTypings_Disjoint_lists.

                inv H13; simpl in *. rewrite map_app in H27. eassumption.

                split.

                ** eapply Union_list_exists_l. eapply in_map. eapply in_map. eassumption.

                   eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

                ** eapply Union_list_exists_l. eapply in_map. eapply in_map. eassumption.

                   eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

             ++ eapply Forall2_exists_r_two in H14; [| eapply H6 | eapply H8 | ].
                2:{ intros Hneq. inv Hneq.

                    assert (Hnone : get x3 Linear h2 = None) by (eapply H5; eauto).

                    congruence. }


                destructAll.

                eapply SplitStoreTyping_app in H13. destruct H13 as [S'' [Hlin _ ]].
                eapply SplitStoreTypings_permut in Hlin; eauto.

                eapply SplitStoreTyping_app with (Ss := [x; x8]) in Hlin. destruct Hlin as [S''' [Hlin _ ]].

                eapply SplitHeapTypings_Disjoint.

                inv Hlin; simpl in *. eassumption.

                split.

                ** eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

                ** eapply HasHeapType_in_Dom_ht. eassumption. eassumption.


      + eassumption.

      + eassumption.

    - econstructor; eauto.
      eapply H0; eauto. unfold r in *.
      eapply NoCapsPretype_subst; eassumption.

    - econstructor; eauto.
      eapply H1; eauto. eapply NoCaps_subst_SLoc; eauto.

    - econstructor; eauto.
      eapply empty_submap; [ | eassumption ].
      now eapply restrict_StoreTyping_submap.
      destruct S0. simpl in *. eassumption.
  Qed.


  Lemma HasHeapType_GC F S Sheap Sprog Sother S' hv ht :
    forall roots h1 h2,
      HasHeapType S F hv ht ->

      HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
      SplitStoreTypings (S :: Sother) Sprog ->
      SplitStoreTypings [Sprog; Sheap] S' ->
      L.locs_HeapValue Unrestricted hv \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

      L.collect_unr roots h1 h2 ->
      HasHeapType (restrict_StoreTyping S h1 h2) F hv ht.
  Proof.
    intros roots h1 h2 Ht.
    revert roots h1 h2 Sheap Sprog Sother S'.
    eapply HasHeapType_ind with
      (P := fun S F hv ht => forall roots h1 h2 Sheap Sprog Sother S'
                                    (Hmem: HasTypeMeminst Sheap Sprog h1)
                                    (Hsplit : SplitStoreTypings (S :: Sother) Sprog)
                                    (Hsplit' : SplitStoreTypings [Sprog; Sheap] S')
                                    (Hsub : L.locs_HeapValue Unrestricted hv \subset (L.reach_unr h1 (roots :|: L.outset h1)))

                                    (Hcol :  L.collect_unr roots h1 h2),
                HasHeapType (restrict_StoreTyping S h1 h2) F hv ht); intros; eauto;
      try (now econstructor; eauto; first [ eapply empty_submap; [ | eassumption ];
                                            eapply restrict_StoreTyping_submap ]).
    - econstructor; eauto.
      eapply HasTypeValue_GC; eauto.

    - econstructor; [ | | eassumption | ].
      + eapply SplitStoreTypings_restrict_StoreTyping_list.
        eassumption.
      + destructAll.
        revert H0 S0 Sheap Sprog Sother S' H Hmem Hsplit Hsplit' Hsub Hcol.
        clear; intros H1; induction H1;
          intros S0 Sheap Sprog Sother S' Hss Hmem Hsplit Hsplit' Hsub Hcol.
        now constructor.
        constructor; eauto.
        * eapply HasTypeValue_GC; eauto.

          eapply SplitStoreTypings_merge' with (S1 := x :: l). eassumption. eassumption.

          simpl in *. now sets.


        * simpl in *. assert (Hc := Hss). eapply SplitStoreTypings_cons in Hc. destructAll.
          eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
          eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
          rewrite <- app_assoc in Hsplit.
          eapply SplitStoreTyping_app in Hsplit. destructAll.

          eapply IHForall3; try eassumption.

          simpl in *. now sets.
      + eauto.

    - econstructor; auto.
      + eapply SplitStoreTypings_restrict_StoreTyping_list.
        eassumption.
      + revert H3 S0 Sheap Sprog Sother S' H1 Hmem Hsplit Hsplit' Hsub Hcol.
        clear; intros H3; induction H3;
          intros S0 Sheap Sprog Sother S' Hss Hmem Hsplit Hsplit' Hsub Hcol.
        now constructor.
        constructor; eauto.
        * eapply HasTypeValue_GC; eauto.

          eapply SplitStoreTypings_merge' with (S1 := x :: l). eassumption. eassumption.

          simpl in *. now sets.

        * simpl in *. assert (Hc := Hss). eapply SplitStoreTypings_cons in Hc. destructAll.
          eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
          eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
          rewrite <- app_assoc in Hsplit.
          eapply SplitStoreTyping_app in Hsplit. destructAll.

          eapply IHForall2; try eassumption.

          simpl in *. now sets.

    -  econstructor; auto.
       + eassumption.
       + eassumption.
       + eassumption.
       + eapply HasTypeValue_GC; eauto.
  Qed.


  Lemma HasHeapType_GC_heap F S Sheap Sprog Sother S' hv ht :
    forall roots h1 h2,
      HasHeapType S F hv ht ->

      HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
      SplitStoreTypings (S :: Sother) Sheap ->
      (exists m l' _len, get l' m h2 = Some (hv, _len)) ->
      NoCapsHeapType (heapable F) ht = true ->

      SplitStoreTypings [Sprog; Sheap] S' ->
      L.locs_HeapValue Unrestricted hv \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

      L.collect_unr roots h1 h2 ->
      HasHeapType (restrict_StoreTyping S h1 h2) F hv ht.
  Proof.
    intros roots h1 h2 Ht.
    revert roots h1 h2 Sheap Sprog Sother S'.
    eapply HasHeapType_ind with
      (P := fun S F hv ht => forall roots h1 h2 Sheap Sprog Sother S'
                                    (Hmem: HasTypeMeminst Sheap Sprog h1)
                                    (Hsplit : SplitStoreTypings (S :: Sother) Sheap)
                                    (Hex : exists m l' _len, get l' m h2 = Some (hv, _len))
                                    (Hcaps: NoCapsHeapType (heapable F) ht = true)
                                    (Hsplit' : SplitStoreTypings [Sprog; Sheap] S')
                                    (Hsub : L.locs_HeapValue Unrestricted hv \subset (L.reach_unr h1 (roots :|: L.outset h1)))

                                    (Hcol :  L.collect_unr roots h1 h2),
                HasHeapType (restrict_StoreTyping S h1 h2) F hv ht); intros; eauto;
      try (now econstructor; eauto; first [ eapply empty_submap; [ | eassumption ];
                                            eapply restrict_StoreTyping_submap ]).
    - econstructor; eauto.
      eapply HasTypeValue_GC_heap; eauto.

      + destructAll. do 4 eexists. split. eassumption. reflexivity.
      + simpl in *. eapply forallb_forall in Hcaps. eassumption.
        eapply nth_error_In. eassumption.

    - econstructor; [ | | eassumption | ].
      + eapply SplitStoreTypings_restrict_StoreTyping_list.
        eassumption.
      +

        assert (Hex' : exists (m : Mem) (l'0 : M.Loc) (hv : M.Val) (_len : Len), get l'0 m h2 = Some (hv, _len) /\ Union_list (map (L.locs_Value Linear) vs) \subset L.locs_HeapValue Linear hv).

        { destructAll. do 4 eexists. split. eassumption. simpl. now sets. }

        simpl in *. rewrite <- H1 in Hcaps. simpl in *.

        revert H0 S0 Sheap Sprog Sother S' H Hmem Hsplit Hsplit' Hsub Hcol Hex' Hcaps.
        clear; intros H1; induction H1;
          intros S0 Sheap Sprog Sother S' Hss Hmem Hsplit Hsplit' Hsub Hcol Hex' Hcaps.
        now constructor.

        constructor; eauto.
        * eapply HasTypeValue_GC_heap; eauto.

          -- eapply SplitStoreTypings_merge' with (S1 := x :: l). eassumption. eassumption.
          -- destructAll. do 4 eexists. split. eassumption. simpl in *. now sets.
          -- simpl in *. repeat do_bools. eassumption.
          -- simpl in *. now sets.

        * simpl in *. assert (Hc := Hss). eapply SplitStoreTypings_cons in Hc. destructAll.
          eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
          eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
          rewrite <- app_assoc in Hsplit.
          eapply SplitStoreTyping_app in Hsplit. destructAll.

          eapply IHForall3; try eassumption.

          -- simpl in *. now sets.
          -- destructAll. do 4 eexists. split. eassumption. simpl. now sets.
          -- simpl in *. repeat do_bools. eassumption.

      + eauto.

    - econstructor; auto.
      + eapply SplitStoreTypings_restrict_StoreTyping_list.
        eassumption.
      +

        assert (Hex' : exists (m : Mem) (l'0 : M.Loc) (hv : M.Val) (_len : Len), get l'0 m h2 = Some (hv, _len) /\ Union_list (map (L.locs_Value Linear) vs) \subset L.locs_HeapValue Linear hv).

        { destructAll. do 4 eexists. split. eassumption. simpl. now sets. }


        revert H3 S0 Sheap Sprog Sother S' H1 Hmem Hsplit Hsplit' Hsub Hcol Hex' Hcaps.
        clear; intros H1; induction H1;
          intros S0 Sheap Sprog Sother S' Hss Hmem Hsplit Hsplit' Hsub Hcol Hex' Hcaps.
        now constructor.
        constructor; eauto.
        * eapply HasTypeValue_GC_heap; eauto.

          -- eapply SplitStoreTypings_merge' with (S1 := x :: l). eassumption. eassumption.
          -- destructAll. do 4 eexists. split. eassumption. simpl in *. now sets.
          -- simpl in *. now sets.

        * simpl in *. assert (Hc := Hss). eapply SplitStoreTypings_cons in Hc. destructAll.
          eapply SplitStoreTypings_merge' in Hsplit; [| eassumption ].
          eapply SplitStoreTypings_comm' with (S1 := [x]) (S2 := l ++ Sother) in Hsplit.
          rewrite <- app_assoc in Hsplit.
          eapply SplitStoreTyping_app in Hsplit. destructAll.

          eapply IHForall2; try eassumption.
          -- simpl in *. now sets.
          -- destructAll. do 4 eexists. split. eassumption. simpl. now sets.

    -  econstructor; auto.
       + eassumption.
       + eassumption.
       + eassumption.
       + eapply HasTypeValue_GC_heap; eauto.
         * destructAll. do 4 eexists. split. eassumption. reflexivity.
         * simpl in *. eapply NoCaps_subst. eassumption. eassumption. 
  Qed.
  

  Lemma HasTypeLocals_GC F Ss Sheap Sprog Sother S'  vs taus :
    forall roots h1 h2,
      HasTypeLocals F Ss vs taus ->

      HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
      SplitStoreTypings (Ss ++ Sother) Sprog ->
      SplitStoreTypings [Sprog; Sheap] S' ->
      Union_list (map (L.locs_Value Unrestricted) vs) \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

      L.collect_unr roots h1 h2 ->
      HasTypeLocals F (map (fun S => restrict_StoreTyping S h1 h2) Ss) vs taus.
  Proof.
    intros r h1 h2 Hloc Hmem Hs Hs' Hin Hc. inv Hloc.
    constructor. revert Sheap Sprog Sother S' Hmem Hs Hs' Hin Hc.
    induction H; intros Sheap Sprog Sother S' Hmem Hs Hs' Hin Hc.
    - now constructor.
    - simpl in *. constructor; eauto.
      destruct z. simpl in *.
      eapply HasTypeValue_GC; eauto.

      now sets.

      eapply IHForall3; try eassumption.

      eapply SplitStoreTypings_comm' with (S1 := [x]) in Hs.
      rewrite <- app_assoc in Hs. eassumption.

      now sets.
  Qed.

  Lemma list_append_same_empty A (x y : list A) :
    x = y ++ x -> y = [].
  Proof.
    intros H. replace x with ([] ++ x) in H at 1 by reflexivity.
    eapply app_inv_tail in H. congruence.
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
    | [ |- HasTypeInstruction _ _ _ _ [StructFree] _ _ ] =>
      eapply StructFreeTyp; eauto
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
    | [ |- HasTypeInstruction _ _ _ _ [Label _ _ _ _ _] _ _ ] =>
      eapply LabelTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Malloc _ _ _] _ _ ] =>
      eapply MallocTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Free] _ _ ] =>
        eapply FreeTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Unreachable] _ _ ] =>
        eapply UnreachableType; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Nop] _ _ ] =>
        eapply NopTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Drop] _ _ ] =>
        eapply DropTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Select] _ _ ] =>
        eapply SelectTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Block  _ _ _] _ _ ] =>
        eapply BlockTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Br _] _ _ ] =>
        eapply BrTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Br_if _] _ _ ] =>
        eapply Br_ifTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Br_table _ _] _ _ ] =>
        eapply Br_tableTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Ret] _ _ ] =>
        eapply RetTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Inst _] _ _ ] =>
        eapply InstITyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Group _ _] _ _ ] =>
        eapply GroupType; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Ungroup] _ _ ] =>
        eapply UngroupTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [CapSplit] _ _ ] =>
        eapply CapSplitTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [CapJoin] _ _ ] =>
        eapply CapJoinTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [RefDemote] _ _ ] =>
        eapply RefDemoteTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [RefSplit] _ _ ] =>
        eapply RefSplitTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [RefJoin] _ _ ] =>
        eapply RefJoinTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Qualify _] _ _ ] =>
        eapply QualifyTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Trap] _ _ ] =>
        eapply TrapTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [CallAdm _ _] _ _ ] =>
        eapply CallAdmTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Label _ _ _ _ _] _ _ ] =>
        eapply LabelTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Local _ _ _ _ _] _ _ ] =>
        eapply LocalTyp; eauto
    | [ |- HasTypeInstruction _ _ _ _ [Malloc _ _ _] _ _ ] =>
        eapply MallocTyp; eauto
    end.

    Lemma restrict_StoreTyping_empty_comm S h1 h2 :
      StoreTyping_eq
        (restrict_StoreTyping (empty_LinTyp S) h1 h2) (empty_LinTyp (restrict_StoreTyping S h1 h2)).
    Proof.
      destruct S. unfold StoreTyping_eq. simpl. split; eauto. split; eauto.
      unfold remove_heaptype. generalize (to_list Linear h1). intros l.
      assert (Heq : eq_map (M.empty HeapType) (M.empty HeapType)) by eapply eq_map_refl.
      revert Heq. generalize (M.empty HeapType) at 1 3. induction l; intros m Heq.
      - eassumption.
      - destruct a as [[? ?] ?].
        simpl. eapply IHl.
        destruct (mem Linear l0 h2).
        eassumption.
        eapply eq_map_trans. eapply proper_remove. eassumption.
        eapply remove_empty.
    Qed.


    Definition HasTypeInstruction_GC_def Sp M F L es arrt L' :=
      forall roots h1 h2 Sheap Sprog Sother S'

        (Hmem : HasTypeMeminst Sheap Sprog h1) (* initial mem is typed in some store typings *)
        (Hsplit : SplitStoreTypings (Sp :: Sother) Sprog)
        (Hsplit' : SplitStoreTypings [Sprog; Sheap] S')
        (Hin : Union_list (map (L.locs_Instruction Unrestricted) es) \subset (L.reach_unr h1 (roots :|: L.outset h1)))

        (Hcol : L.collect_unr roots h1 h2),

        HasTypeInstruction (restrict_StoreTyping Sp h1 h2) M F L es arrt L'.

    Definition HasTypeClosure_GC_def (S : StoreTyping) (C : Closure) (ft : FunType) : Prop :=
      forall roots h1 h2 Sheap Sprog Sother S',

        HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
        SplitStoreTypings (S :: Sother) Sprog ->
        SplitStoreTypings [Sprog; Sheap] S' ->
        L.locs_Closure Unrestricted C  \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

        L.collect_unr roots h1 h2 ->
        HasTypeClosure (restrict_StoreTyping S h1 h2) C ft.


    Definition HasTypeFunc_GC_def (S : StoreTyping) (M : Module_Ctx) (f : Func) (exs : list ex) (ft : FunType):  Prop :=
      forall roots h1 h2 Sheap Sprog Sother S',

        HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
        SplitStoreTypings (S :: Sother) Sprog ->
        SplitStoreTypings [Sprog; Sheap] S' ->
        L.locs_Func Unrestricted f \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

        L.collect_unr roots h1 h2 ->
        HasTypeFunc (restrict_StoreTyping S h1 h2) M f exs ft.

    Definition HasTypeConf_GC_def S maybe_ret i locvs locsz es taus :=
      forall roots h1 h2 Sheap Sprog Sother S',

        HasTypeMeminst Sheap Sprog h1 -> (* initial mem is typed in some store typings *)
        SplitStoreTypings (S :: Sother) Sprog ->
        SplitStoreTypings [Sprog; Sheap] S' ->
        Union_list (map (L.locs_Instruction Unrestricted) es) :|: Union_list (map (L.locs_Value Unrestricted) locvs) \subset (L.reach_unr h1 (roots :|: L.outset h1)) ->

        L.collect_unr roots h1 h2 ->
        HasTypeConf (restrict_StoreTyping S h1 h2) maybe_ret i locvs locsz es taus.


    Lemma HasTypeInstruction_GC Sp M F L es arrt L'
          (Htyp : HasTypeInstruction Sp M F L es arrt L') :
      HasTypeInstruction_GC_def Sp M F L es arrt L'.
  Proof.
    (* The difficult part is proving that the linear locations that were removed
       were not referenced by es *)
    (* For unrestrivted locs that were collcted is easy beacause the are unreachable.

      Must make some assumption about locs of es.
     *)
    (* All cases are trivial -- since no instruction uses a heap type -- except for Value + Malloc  *)

    eapply (HasTypeInstruction_mind'  HasTypeInstruction_GC_def HasTypeClosure_GC_def
                                     HasTypeFunc_GC_def HasTypeConf_GC_def);
      intros; try (intro; intros);
      try now (HasTypeEauto;
               first [ eapply empty_submap; [ | eassumption ];
                       eapply restrict_StoreTyping_submap ]).


    - (* value *)
      HasTypeEauto.
      eapply HasTypeValue_GC; try eassumption. now sets.

    - (* block *)
      HasTypeEauto.
      eapply H0; try eassumption. now sets.

    - (* loop *)
      HasTypeEauto.
      eapply H0; try eassumption. now sets.

    - (* ite *)
      HasTypeEauto.

      eapply H0; try eassumption. simpl in *.
      eapply Included_trans; [| eassumption ].
      eapply Included_Union_preserv_l. now sets.

      eapply H2; try eassumption. simpl in *. now sets.

    - (* mempack *)
      HasTypeEauto.
      eapply H0; try eassumption. now sets.

    - unfold F1, F2 in *. eapply VariantCaseTypUnr; eauto.
      eapply empty_submap; [ | eassumption ];
        eapply restrict_StoreTyping_submap.

      revert H2 H3 Hmem Hsplit Hsplit' Hin Hcol. clear.
      intros H1; induction H1; intros Hgc Hmem Hsplit Hsplit' Hin Hcol.

      now constructor.

      inv Hgc. constructor; eauto.

      + eapply H4; try eassumption.
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_preserv_l.
        unfold L.locs_Instruction. simpl. now sets.

      + eapply IHForall2; try eassumption.

        eapply Included_trans; [| eassumption ].
        unfold L.locs_Instruction. simpl.
        rewrite <- Union_assoc. now sets.

    - unfold F2, F1 in *. eapply VariantCaseTypLin; eauto.
      eapply empty_submap; [ | eassumption ];
        eapply restrict_StoreTyping_submap.

      revert H0 H1 Hmem Hsplit Hsplit' Hin Hcol. clear.
      intros H1; induction H1; intros Hgc Hmem Hsplit Hsplit' Hin Hcol.

      now constructor.

      inv Hgc. constructor; eauto.

      + eapply H4; try eassumption.
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_preserv_l.
        unfold L.locs_Instruction. simpl. now sets.

      + eapply IHForall2; try eassumption.

        eapply Included_trans; [| eassumption ].
        unfold L.locs_Instruction. simpl.
        rewrite <- Union_assoc. now sets.

    - HasTypeEauto.
      eapply H0; try eassumption. now sets.

      eapply empty_submap; [ | eassumption ].
      eapply restrict_StoreTyping_submap.

    - HasTypeEauto.
      eapply H0; try eassumption. now sets.

      eapply empty_submap; [ | eassumption ].
      eapply restrict_StoreTyping_submap.

    - HasTypeEauto.
      eapply H0; try eassumption.

      eapply Included_trans; [| eassumption ].
      simpl. eapply Included_Union_preserv_l. now sets.

    - eapply LabelTyp.
      eassumption.
      eapply H1; try eassumption.
      eapply Included_trans; [| eassumption ].
      simpl. eapply Included_Union_preserv_l. now sets.

      eapply HasTypeInstruction_StoreTyping_eq. eapply H3; try eassumption.

      eapply SplitStoreTypings_merge' with (S1 := [empty_LinTyp S; S]).
      eapply SplitStoreTypings_EmptyHeapTyping_l. eassumption.

      eapply Included_trans; [| eassumption ].
      simpl. eapply Included_Union_preserv_l. now sets.

      eapply restrict_StoreTyping_empty_comm.

      auto.

    - HasTypeEauto.
      eapply H2; try eassumption.

      eapply Included_trans; [| eassumption ].
      simpl. eapply Included_Union_preserv_l. now sets.


    - (* Malloc *)
      eapply MallocTyp; eauto.
      eapply HasHeapType_GC; eauto.
      eapply Included_trans; [| eassumption ].
      eapply Included_Union_preserv_l. unfold L.locs_Instruction. now sets.

    - (* Empty *)
      eapply EmptyTyp; auto.
      eapply empty_submap; [ | eassumption ].
      eapply restrict_StoreTyping_submap.

    - (* Cons *)
      eapply ConsTyp.
      eapply SplitStoreTypings_restrict_StoreTyping. eassumption.

      eapply H1; try eassumption.
      eapply SplitStoreTypings_merge' with (S1 := [S1;S2]). eassumption. eassumption.
      rewrite map_app, Union_list_app in *. now sets.

      eapply H3; try eassumption.

      eapply SplitStoreTypings_comm' with (S1 := [S1]) in H.
      eapply SplitStoreTypings_merge' with (S1 := [S2;S1]). eassumption. eassumption.
      rewrite map_app, Union_list_app in *. now sets.

    - (* Frame *)
      eapply FrameTyp. eassumption. eassumption. eassumption.
      eapply H3; eassumption. eassumption.
      auto.
      auto.

    - (* ChangeBegLocal *)
      eapply ChangeBegLocalTyp; [ | | eauto ].
      auto.
      auto.

    - (* ChangeEndLocal *)
      eapply ChangeEndLocalTyp; [ | | eauto ].
      auto.
      auto.
      
    - (* Closure *)
      econstructor; try eassumption. all: eauto.
      unfold restrict_StoreTyping.
      destruct S; simpl in *.
      auto.

    - (* Func *)
      econstructor; try eassumption. all: eauto.

    - (* Config *)
      econstructor. eassumption.

      destruct S; simpl in *; eassumption.

      eapply SplitStoreTypings_restrict_StoreTyping_list with (Ss := S_stack :: Ss).
      eassumption.

      eapply HasTypeLocals_GC; try eassumption.
      eapply SplitStoreTypings_merge' in H8; [| eassumption ].
      simpl in H8. eapply SplitStoreTypings_comm' with (S1 := [S_stack]) in H8.
      rewrite <- app_assoc in H8. eassumption.
      now sets.
      eassumption.

      eapply H5; try eassumption.
      eapply SplitStoreTypings_merge' with (S1 := S_stack :: Ss); eassumption.
      now sets.

      eassumption.

    - eassumption.
  Qed.

  Lemma setminus_eq A (s1 s2 : Ensembles.Ensemble A) :
    s2 \subset s1 ->
    s2 <--> s1 \\ (s1 \\ s2).
  Proof.
    split.
    - intros x H1. constructor; eauto.
      intros Hc. inv Hc. eauto.
    - intros x H1. inv H1.
      assert (Hem := LEM (Ensembles.In A s2 x)). inv Hem; eauto.
      exfalso. eapply H2. constructor; eauto.
  Qed.

  Lemma collect_urn_lin_subset roots h1 h2  :
    L.collect_unr roots h1 h2 ->
    dom_lin h2 \subset dom_lin h1.
  Proof.
    intros Hc. inv Hc. destructAll.
    intros l Hin. inv Hin.
    eapply H0 in H3. eexists; eauto.
  Qed.

  Lemma collect_urn_unr_subset roots h1 h2  :
    L.collect_unr roots h1 h2 ->
    dom_unr h2 \subset dom_unr h1.
  Proof.
    intros Hc. inv Hc. destructAll.
    intros l Hin. inv Hin.
    eapply H0 in H3. eexists; eauto.
  Qed.

  Definition not_empty_LinTyp (S : StoreTyping) : bool :=
    negb (M.is_empty (LinTyp S)).

  Lemma get_heaptype_restrict l S h1 h2 ht:
    l \in dom_lin h2 ->
    get_heaptype l (LinTyp S) = Some ht  ->
    get_heaptype l (LinTyp (restrict_StoreTyping S h1 h2)) = Some ht.
  Proof.
    intros Hin Hget.
    destruct (get_heaptype l (LinTyp (restrict_StoreTyping S h1 h2))) eqn:Hget'.

    - eapply restrict_StoreTyping_submap in Hget'. congruence.

    - edestruct (Dom_ht_restrict S h1 h2) as [_ Hsub].

      edestruct Hsub.

      constructor. eexists. eassumption.
      intros Hc. inv Hc. contradiction.

      unfold get_heaptype in *. congruence.
  Qed.

  Lemma get_heaptype_restrict_unr l S h1 h2 ht:
    l \in dom_unr h2 ->
    get_heaptype l (UnrTyp S) = Some ht  ->
    get_heaptype l (UnrTyp (restrict_StoreTyping S h1 h2)) = Some ht.
  Proof.
    intros Hin Hget.
    destruct (get_heaptype l (UnrTyp (restrict_StoreTyping S h1 h2))) eqn:Hget'.

    - eapply restrict_StoreTyping_submap_Unr in Hget'. congruence.

    - edestruct (Dom_ht_restrict_Urn S h1 h2) as [_ Hsub].

      edestruct Hsub.

      constructor. eexists. eassumption.
      intros Hc. inv Hc. contradiction.

      unfold get_heaptype in *. congruence.
  Qed.

  Lemma NoDup_app A l1 l2 (x : A)  :
    NoDup (l1 ++ l2) ->
    In x l1 ->
    ~ In x l2.
  Proof.
    intros Hnd Hin. induction l1.
    - now inv Hin.
    - inv Hin.
      + intros Hin'. simpl in *. eapply NoDup_cons_iff in Hnd.
        destructAll. eapply H. eapply in_or_app. now right.
      + eapply IHl1; eauto. now inv Hnd.
  Qed.

  Lemma Permutation_disjoint h1 h2 m l l':
    Permutation.Permutation (to_list m h2) l ->
    Permutation.Permutation (to_list m h1) (l' ++ l) ->
    sub_heap m h2 h1 ->
    (forall l v len, In (l, v, len)  l' -> get l m h1 = Some (v, len) /\ get l m h2 = None).
  Proof.
    intros Hp1 Hp2 Hsub l1 v len Hin.

    assert (Hget1 : get l1 m h1 = Some (v, len)).
    { assert (Hget' := in_or_app l' l _ ltac:(left; exact Hin)).
      eapply Permutation.Permutation_in in Hget'.
      2:{ eapply Permutation.Permutation_sym. eassumption. }
      eapply In_nth_error in Hget'. destructAll.
      eapply in_to_list_implies_get. eassumption. }

    split; eauto.

    destruct (get l1 m h2) eqn:Hget; [| reflexivity ].
    exfalso.

    destruct p.

    specialize (Hsub _ _ _ Hget). rewrite Hget1 in Hsub. inv Hsub.

    assert (Hin' := Hp2).
    eapply Permutation.Permutation_in in Hin'.

    2:{ eapply get_implies_in_to_list in Hget1.
        destructAll. eapply nth_error_In in H. eassumption. }

    assert (Hnd := NoDup_app _ l' l _ ltac:(eapply Permutation.Permutation_NoDup ; [ eassumption | eapply to_list_NoDup]) Hin).

    eapply Permutation.Permutation_in in Hp1.

    2:{ eapply get_implies_in_to_list in Hget. destructAll. eapply nth_error_In. eassumption. }

    eauto.
  Qed.


  Lemma is_empty_Lin_dom (S : HeapTyping) :
    Dom_ht S \subset Ensembles.Empty_set _ ->
    M.is_empty S = true.
  Proof.
    intros Hdom.
    eapply PositiveMap.is_empty_1.
    unfold PositiveMap.Empty in *.
    intros l v Hin. unfold PositiveMap.MapsTo in *.

    specialize (Hdom (Pos.pred_N l)).
    destruct Hdom.

    eexists. rewrite succ_pos_pred_N. eassumption.
  Qed.

  Lemma HasTypeMeminst_GC Sp Sh S' h1 h2 roots :
    HasTypeMeminst Sh Sp h1 ->
    SplitStoreTypings [Sp; Sh] S' ->
    L.collect_unr roots h1 h2 ->
    HasTypeMeminst (restrict_StoreTyping Sh h1 h2)
                   (restrict_StoreTyping Sp h1 h2) h2.
  Proof.
    intros Hmem Hsplit Hcoll. assert (Hmem' := Hmem).
    inv Hmem.

    assert (Hsubl := to_list_sub_heap h2 h1 Linear ltac:(now destruct Hcoll; eauto)).
    assert (Hsubu := to_list_sub_heap h2 h1 Unrestricted ltac:(now destruct Hcoll; eauto)).

    destructAll.

    assert (Hallall := H3).

    eapply Forall2_flip in H2. eapply Permutation.Permutation_Forall2 in H2; [| eassumption ].
    eapply Forall2_flip in H3. eapply Permutation.Permutation_Forall2 in H3; [| eassumption ].
    destructAll.


    eapply Forall2_flip in H9.
    eapply Forall2_flip in H6.

    eapply Forall2_app_inv_r in H9. eapply Forall2_app_inv_r in H6. destructAll.

    eapply Forall2_flip in H12. eapply Permutation.Permutation_Forall2 in H12; [| eapply Permutation.Permutation_sym; eassumption ].
    eapply Forall2_flip in H10. eapply Permutation.Permutation_Forall2 in H10; [| eapply Permutation.Permutation_sym; eassumption ].

    destructAll.

    eapply Forall2_flip in H11.
    eapply Forall2_flip in H13.


    eapply MeminstT with (S_lin := map (fun S => restrict_StoreTyping S h1 h2) x3) (S_unr := map (fun S => restrict_StoreTyping S h1 h2) x0).


    - rewrite !Dom_ht_restrict. rewrite <- Setminus_Union_distr.
      rewrite <- H.
      eapply setminus_eq.
      eapply collect_urn_lin_subset. eassumption.
    - rewrite !Dom_ht_restrict_Urn. rewrite <- Setminus_Union_distr, <- H0.
      eapply setminus_eq.
      eapply collect_urn_unr_subset. eassumption.
    -  assert (Hs := H1).
       eapply SplitStoreTypings_permut in H1.

      2:{ eapply Permutation.Permutation_trans.

          - eapply Permutation.Permutation_app_head.
            eapply Permutation.Permutation_trans. eassumption.
            eapply Permutation.Permutation_app_head. eassumption.

          - eapply Permutation.Permutation_app_tail.
            eapply Permutation.Permutation_trans. eassumption.
            eapply Permutation.Permutation_app_head. eassumption. }



      eapply SplitStoreTypings_permut with (S2 := (x7 ++ x5) ++ x3 ++ x0) in H1.
      2:{ rewrite <- !app_assoc. eapply Permutation.Permutation_app_head.
          rewrite !app_assoc. eapply Permutation.Permutation_app_tail.
          eapply Permutation.Permutation_app_comm. }


      apply SplitStoreTypings_restrict_StoreTyping_list with (h1 := h1) (h2 := h2) in H1.

      rewrite map_app in H1. eapply SplitHeapTypings_empty_app in H1.
      + rewrite map_app in H1. eassumption.
      + rewrite map_app. eapply Forall_app. split.
        * inv Hcoll. destructAll.
          assert (Hdis := Permutation_disjoint _ _ _ _ _ H7 H8 H15).

          revert Hdis H9 H17. clear. intros Hdis Hall Hlin.
          induction Hall.

          -- now constructor.

          -- destruct y as [[? ?] ?]. destructAll.

             constructor.

             2:{ eapply IHHall; eauto.
                 intros. eapply Hdis. now right. }


             eapply is_empty_Lin_dom.

             intros loc Hin1.
             eapply Dom_ht_restrict in Hin1. inv Hin1.
             exfalso.

             assert (Hlocs : loc \in L.locs_HeapValue Linear v).
             { eapply HasHeapType_in_locs_HeapValue; eauto. }


             assert (Hr1 : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) l0).
             { eapply Hlin.
               split. eexists. eapply Hdis. now left. eapply Hdis. now left. }

             assert (Hr2 : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) loc).
             { destruct Hr1. destructAll. exists (1 + x1). split. now constructor.
               do 3 eexists. split. eassumption. split. eapply Hdis. now left.
               eassumption. }

             eapply Hlin in Hr2. eapply H5.
             destructAll. constructor. eexists; eauto.
             intros Hc. inv Hc. congruence.

        * inv Hcoll. destructAll. eapply Forall2_flip in Hallall.

          eapply Forall2_flip in Hallall.

          assert (Hsplit'' : exists S'', SplitStoreTypings S_unr S'').
          { eapply SplitStoreTypings_comm' in Hs.
            eapply SplitStoreTyping_app in Hs. destructAll. eauto. }

          assert (Hdis := Permutation_disjoint _ _ _ _ _ H4 H5 H14).

          revert Hdis H6 H17 Hsplit'' Hallall H14. clear. intros Hdis Hall Hlin Hsplit Hallall Hsub.
          induction Hall.

          -- now constructor.

          -- destruct y as [[? ?] ?]. destructAll.

             constructor.

             2:{ eapply IHHall; eauto.
                 - intros. eapply Hdis. now right. }

             eapply is_empty_Lin_dom.

             intros loc Hin1.
             eapply Dom_ht_restrict in Hin1. inv Hin1.
             exfalso.

             assert (Hlocs : loc \in L.locs_HeapValue Linear v).
             { eapply HasHeapType_in_locs_HeapValue; eauto. }


             assert (Hr2 : Ensembles.In M.Loc (L.reach_lin h1 (L.lin_locs_in_unr h1 \\ L.lin_locs_in_unr h2)) loc).
             { eapply reachable_roots. constructor.

               exists l0, v, l1. split. eapply Hdis. now left. eassumption.

               intros Hc. destruct Hc. destructAll.


               eapply Forall2_exists_r_two in Hallall.
               2:{ edestruct get_implies_in_to_list. eapply Hsub. eapply H7.
                   eapply nth_error_In. eapply H9. }

               2:{ edestruct get_implies_in_to_list. eapply Hdis. now left.
                   eapply nth_error_In. eapply H9. }

               2:{ intros Hc. inv Hc. specialize (Hdis l0 v l1 ltac:(now left)). destructAll. congruence. }

               destructAll.

               eapply SplitStoreTypings_permut in H0; [ | eassumption ].
               eapply SplitStoreTyping_app with (Ss := [x5; x6]) in H0. destruct H0 as [S''' [Hs _ ]].

                eapply SplitHeapTypings_Disjoint.

                inv Hs; simpl in *. eassumption.

                split.

                ** eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

                ** eapply HasHeapType_in_Dom_ht. eassumption. eassumption.

             }

             eapply Hlin in Hr2. eapply H6. destructAll.

             constructor. eexists. eassumption.
             intros Hc. inv Hc. congruence.

    - assert (Hin : forall l v len , In (l, v, len) (to_list Linear h2) -> get l Linear h2 = Some (v, len)).
      { intros. eapply In_nth_error in H14. destructAll. eapply in_to_list_implies_get; eauto. }


      assert (Hsplit' : exists So, SplitStoreTypings (x3 ++ So) Sh).
      { eapply SplitStoreTypings_permut in H1.
        2:{ eapply Permutation.Permutation_app_tail.
            eapply Permutation.Permutation_trans. eassumption.
            eapply Permutation.Permutation_app_head. eassumption. }

        rewrite <- app_assoc in H1. eapply SplitStoreTypings_comm' in H1.
        rewrite <- app_assoc in H1. eauto. }


      revert Hin H13 Hsplit' Hmem' Hsplit Hcoll. generalize (to_list Linear h2). clear.
      intros l1  Hin Hall Hsplit' Hmem Hsplit Hcoll. induction Hall.

      + now constructor.

      + constructor.

        2:{ eapply IHHall.
            - intros. eapply Hin. now right; eauto.
            - destructAll. eexists ([x] ++ x0).
              eapply SplitStoreTypings_permut.
              rewrite app_assoc.
              eapply Permutation.Permutation_app_tail.
              eapply Permutation.Permutation_app_comm. eassumption. }

        destruct y as [[l1 hv] len]. destructAll.

        eexists x1. split; [| split; [| split; [| split ]]]; eauto.

        * inv H1.
          -- left. eapply get_heaptype_restrict; eauto.
             eexists. eapply Hin. now left.
          -- right. eapply get_heaptype_restrict; eauto.
             eexists. eapply Hin. now left.

        * eapply HasHeapType_GC_heap; [ eassumption | eassumption | | | | eassumption | | eassumption ].

          eassumption.

          do 3 eexists. eapply Hin. now left.

          eassumption.

          inv Hcoll. destructAll. intros l2 Hin2. eapply reachable_roots.
          right. do 3 eexists.
          split. eapply H6. eapply Hin. now left.
          eassumption.

    - assert (Hin : forall l v len , In (l, v, len) (to_list Unrestricted h2) -> get l Unrestricted h2 = Some (v, len)).
      { intros. eapply In_nth_error in H14. destructAll. eapply in_to_list_implies_get; eauto. }


      assert (Hsplit' : exists So, SplitStoreTypings (x0 ++ So) Sh).
      { eapply SplitStoreTypings_permut in H1.
        2:{ eapply Permutation.Permutation_app_head.
            eapply Permutation.Permutation_trans. eassumption.
            eapply Permutation.Permutation_app_head. eassumption. }

        rewrite app_assoc in H1. eapply SplitStoreTypings_comm' in H1.
        eauto. }

      revert Hin H11 Hsplit' Hmem' Hsplit Hcoll. generalize (to_list Unrestricted h2). clear.
      intros l1  Hin Hall Hsplit' Hmem Hsplit Hcoll. induction Hall.

      + now constructor.

      + constructor.

        2:{ eapply IHHall.
            - intros. eapply Hin. now right; eauto.
            - destructAll. eexists ([x] ++ x0).
              eapply SplitStoreTypings_permut.
              rewrite app_assoc.
              eapply Permutation.Permutation_app_tail.
              eapply Permutation.Permutation_app_comm. eassumption. }

        destruct y as [[l1 hv] len]. destructAll.

        eexists x1. split; [| split; [| split; [| split ]]]; eauto.

        * eapply get_heaptype_restrict_unr; eauto.
          eexists. eapply Hin. now left.

        * eapply HasHeapType_GC_heap; [ eassumption | eassumption | | | | eassumption | | eassumption ].

          eassumption.

          do 3 eexists. eapply Hin. now left.

          eassumption.

          inv Hcoll. destructAll. intros l2 Hin2.

          specialize (Hin l1 hv len ltac:(now left)).

          assert (Hr : Ensembles.In M.Loc (L.reach_unr h1 (roots :|: L.outset h1)) l1).
          { eapply H7. split; eauto. }

          destruct Hr. destructAll. eexists (1 + x2). split. now  constructor.
          simpl. do 3 eexists. split; eauto.
  Qed.


  Lemma Preservation_reduce_GC Sp Sh S_stack Ss M F L L' arrt addr s vs es s' i C:
    HasTypeStore s Sh Sp ->
    SplitStoreTypings (S_stack :: Ss) Sp ->
    HasTypeLocals empty_Function_Ctx Ss vs L ->
    HasTypeInstruction S_stack M F L es arrt L' ->
    nth_error (InstTyp Sp) i = Some C ->

    GC_step s vs es addr s' vs es ->

    exists Sh' Sp' S_stack' Ss',
      HasTypeLocals empty_Function_Ctx Ss' vs L /\
        HasTypeInstruction S_stack' M F L es arrt L' /\
        nth_error (InstTyp Sp') i = Some C /\
        SplitStoreTypings (S_stack' :: Ss') Sp' /\
        HasTypeStore s' Sh' Sp'.
  Proof.
    intros HS Hsplit Hloc Hins Hnth Hstep. inv Hstep. clear H5 H6.
    unfold s'0 in *. inv HS.

    exists (restrict_StoreTyping Sh h1 h2).
    exists (restrict_StoreTyping Sp h1 h2).
    exists (restrict_StoreTyping S_stack h1 h2).
    eexists (map (fun s => restrict_StoreTyping s h1 h2) Ss).

    split; [| split; [| split; [| split]]].

    - eapply HasTypeLocals_GC; try eassumption.

      eapply SplitStoreTypings_comm' with (S1 := [S_stack]). eassumption.

      eapply Included_trans; [| eapply reachable_roots ].
      unfold roots. eapply Included_Union_preserv_l.
      eapply Included_Union_preserv_l.
      now sets.

    - eapply HasTypeInstruction_GC; try eassumption.

      eapply Included_trans; [| eapply reachable_roots ].
      unfold roots. eapply Included_Union_preserv_l.
      eapply Included_Union_preserv_l.
      now sets.

    - rewrite !restrict_StoreTyping_InstTyp. eassumption.

    - eapply SplitStoreTypings_restrict_StoreTyping_list with (Ss := S_stack :: Ss). eassumption.

    - eapply StoreT with (S := restrict_StoreTyping S h1 h2).

      + eapply SplitStoreTypings_restrict_StoreTyping.
        eassumption.

      + simpl.
        rewrite !restrict_StoreTyping_InstTyp. eassumption.

      +  simpl. unfold h1 in *.
         eapply HasTypeMeminst_GC; eauto.

  Qed.

End PreservationGC.
