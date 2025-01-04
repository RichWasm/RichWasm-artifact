
From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive Sets.Ensembles micromega.Lia .
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


Require Import RWasm.tactics RWasm.term RWasm.EnsembleUtil RWasm.locations RWasm.memory RWasm.reduction RWasm.typing RWasm.list_util
        RWasm.typing_util RWasm.splitting RWasm.misc_util.

Lemma LCEffEqual_length : forall {C L1 L2},
    LCEffEqual C L1 L2 ->
    length L1 = length L2.
Proof.
  unfold LCEffEqual.
  intros.
  eapply Forall2_length; eauto.
Qed.

Module Progress (M : Memory) (T : MemTyping M).
  Definition size_t := size.

  Module Red := Reduction M T.
  Import M T Red T.L.
  Import Utils.

  Ltac invert H := inversion H; subst.

  Definition typing_valid S_rest S_heap s :=
    forall l ht,
      (map_util.get_heaptype l (LinTyp S_rest) = Some ht ->
       exists hv n S_h' Ss,
         SplitStoreTypings [S_h'; Ss] S_heap /\
         get l Linear (meminst s) = Some (hv, n) /\
         HasHeapType S_h' empty_Function_Ctx hv ht /\
         RoomForStrongUpdates n ht) /\
      (map_util.get_heaptype l (UnrTyp S_rest) = Some ht ->
       exists hv n S_h' Ss,
         SplitStoreTypings [S_h'; Ss] S_heap /\
         get l Unrestricted (meminst s) = Some (hv, n) /\
         HasHeapType S_h' empty_Function_Ctx hv ht /\
         RoomForStrongUpdates n ht).

  Lemma nth_error_nil : forall (A : Type) n, nth_error ([] : list A) n = None.
  Proof. induction n; eauto. Qed.

  Lemma nth_error_unzip : forall (A B : Type) (L : list (A * B))  locsz i1 sz0 typ,
  (let (_, szs) := split L in szs = locsz) ->
  nth_error L i1 = Some (typ, sz0) ->
  nth_error locsz i1 = Some sz0.
  Proof.
    intros.
    revert sz0 i1 typ locsz H0 H.
    induction L; intros.
    - destruct i1; simpl in H0; discriminate.
    - destruct i1.
      + simpl.
        destruct a.
        simpl in *.
        invert H0.
        destruct (split L).
        rewrite<- H.
        congruence.
      + simpl.
        destruct a.
        simpl in *.
        destruct (split L).
        invert H.
        eapply IHL; eauto.
  Qed.

  (* A whole bunch of stuff copied from typing_util: *)

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
    ~ l \in Union_list (map map_util.Dom_ht S) ->
    ExactlyInOne true l ht S.
  Proof.
    intros H. induction S.
    - now constructor.
    - constructor.

      + destruct (map_util.get_heaptype l a) eqn:Hget; eauto.
        
        exfalso. eapply H. simpl. left. eexists; eauto.

      + eapply IHS. intros Hc. eapply H.
        simpl; right; eauto.
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
      inv Hc. unfold map_util.get_heaptype in *. congruence.

    - inv H12. inv H13. eapply H4 in H8. 

      assert (Hc : ~ In N (Union_list (map map_util.Dom_ht Ss1)) l1).
      intros Hc. eapply H in Hc. destruct Hc.
      unfold map_util.get_heaptype in *. congruence.

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
    map_util.Dom_map (merge m1 m2) <--> map_util.Dom_map m1 :|: map_util.Dom_map m2.
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
    map_util.Dom_ht (merge m1 m2) <--> map_util.Dom_ht m1 :|: map_util.Dom_ht m2.
  Proof.
    unfold map_util.Dom_ht. split; intros l Hin; unfold In in *; simpl in *.
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


  Lemma Forall3_monotonic {A B C} (R R' : A -> B -> C -> Prop)
        (l1 : list A) (l2 : list B) (l3 : list C):
    (forall x1 x2 x3, R x1 x2 x3 -> R' x1 x2 x3) ->
    Forall3 R l1 l2 l3 ->
    Forall3 R' l1 l2 l3.
  Proof.
    intros H Hall. induction Hall. now constructor.
    constructor; eauto.
  Qed.

  Lemma Forall3_monotonic_strong (A B C: Type) (R R' : A -> B -> C -> Prop)
        (l1 : list A) (l2 : list B) (l3 : list C):
    (forall x1 x2 x3, List.In x1 l1 -> List.In x2 l2 -> List.In x3 l3 ->
                      R x1 x2 x3 -> R' x1 x2 x3) ->
    Forall3 R l1 l2 l3 -> Forall3 R' l1 l2 l3.
  Proof.
    intros H Hall. induction Hall. now constructor.
    constructor; eauto.
    eapply H. now left. now left. now left. eassumption.
    eapply IHHall.
    intros. 
    eapply H. now right. now right. now right. eassumption.
  Qed.

  Lemma Forall3_app {A B C} (R : A -> B -> C -> Prop) l1 l2 l3 l1' l2' l3' :
    Forall3 R l1' l2' l3' ->
    Forall3 R l1 l2 l3 ->
    Forall3 R (l1' ++ l1) (l2' ++ l2) (l3' ++ l3).
  Proof.
    intros Hall Hall'. induction Hall. eassumption.
    simpl. constructor; eauto.
  Qed.


  Lemma forall_e_v :
    forall es,
    Forall (fun e : Instruction => exists v : Value, e = Val v) es -> exists vs : list Value, map Val vs = es.
  Proof.
    intros.
    elim H.
    + exists []. eauto.
    + intros.
      destruct H2.
      destruct H2.
      destruct H0.
      rewrite H0.
      exists (x1 :: x0).
      eapply map_cons.
  Qed.

  Lemma map_empty : forall (A B : Type) (F : A -> B), map F [] = []. Proof. eauto. Qed.

  Lemma value_instr : forall i v, i = Val v -> value i. Proof. intros. unfold value. rewrite H. simpl. eauto. Qed.

  Lemma values_val_map : forall vs, values (map Val vs).
  Proof.
    intros.
    unfold values.
    elim vs.
    + rewrite map_empty; eauto.
    + intros.
      rewrite map_cons.
      assert (H_a := value_instr (Val a) a (eq_refl (Val a))).
      assert (H_cons_constr := Forall_cons).
      assert (H_cons := H_cons_constr Instruction value (Val a) (map Val l) H_a H).
      eauto.
  Qed.

  Lemma forall2_front : forall (A B : Type) (f : A -> B -> Prop) vs taus, Forall2 f vs taus -> length taus <> 0 -> exists v vs' tau taus', vs = v :: vs' /\ taus = tau :: taus' /\ Forall2 f vs' taus' /\ f v tau.
  Proof.
    intros.
    revert H0.
    elim H.
    + easy.
    + intros.
      exists x. exists l. exists y. exists l'.
      eauto.
  Qed.


  Lemma length_non_empty : forall (A : Type) (l : list A) a b, l = a :: b -> length l <> 0.
  Proof.
    intros.
    rewrite H.
    unfold length.
    easy.
  Qed.

  Lemma forall3_back : forall (A B C : Type) (f : A -> B -> C -> Prop) Ss vs taus last,
      Forall3 f Ss vs (taus ++ [last]) ->
      exists Ss' S' vs' v',
        Ss' ++ [S'] = Ss
        /\ vs' ++ [v'] = vs
        /\ Forall3 f Ss' vs' taus
        /\ Forall3 f [S'] [v'] [last].
  Proof.
    intros.
    revert vs taus last H.
    induction Ss; intros.
    + invert H.
      destruct taus; invert H0.
    + invert H.
      destruct taus; simpl in H2.
      - simpl in H.
        destruct (Forall3_length _ _ _ _ H) as [H21 H22].
        rewrite H22 in H21.
        simpl in H21.
        simpl in H22.
        exists []. exists a. exists []. exists y.
        simpl.
        split.
        * destruct Ss; eauto.
          invert H21.
        * split.
          ++destruct l'; eauto.
            invert H22.
          ++split.
            --eapply Forall3_nil.
            --invert H2.
              eapply Forall3_cons; eauto.
              eapply Forall3_nil.
      - simpl in H2.
        invert H2.
        eapply IHSs in H5.
        destruct H5 as [Ss' [S' [vs' [v' [H10 [H11 [H12 H13]]]]]]].
        exists (a :: Ss'). exists S'. exists (y :: vs'). exists v'.
        split.
        * simpl.
          rewrite H10.
          reflexivity.
        * split.
          ++rewrite<- H11.
            reflexivity.
          ++split; eauto.
            eapply Forall3_cons; eauto.
  Qed.

  Hint Constructors HasTypeInstruction.
  Hint Constructors HasTypeValue.


  (* Begin First section of overly specific lemmas ZZZ *)

  Lemma value_typings_linear : forall Ss F vs taus qf,
      Forall3 (fun S v tau => HasTypeValue S F v tau) Ss vs taus ->
      Forall3 (fun S v tau => HasTypeValue S (update_linear_ctx (list_util.set_hd qf (linear F)) F) v tau) Ss vs taus.
  Proof.
    intros.
    eapply Forall3_monotonic.
    2 : { exact H. }
    intros.
    simpl in H0.
    eapply HasTypeValue_Function_Ctx; try exact H0; induction F; simpl; easy.
  Qed.

  Lemma local_typings_linear : forall (A : Type) Ss F vs (taus : list (Typ * A)) qf,
      Forall3 (fun S v '(tau, _) => HasTypeValue S F v tau) Ss vs taus ->
      Forall3 (fun S v '(tau, _) => HasTypeValue S (update_linear_ctx (list_util.set_hd qf (linear F)) F) v tau) Ss vs taus.
  Proof.
    intros.
    eapply Forall3_monotonic.
    2 : { exact H. }
    intros.
    destruct x3.
    eapply HasTypeValue_Function_Ctx; try exact H0; induction F; simpl; easy.
  Qed.

  Lemma value_typings_ret_agnostic : forall Ss vs0 tauvs taus0,
      Forall3 (fun (S : StoreTyping) (v : Value) (tau : Typ) => HasTypeValue S empty_Function_Ctx v tau) Ss vs0 tauvs ->
      Forall3 (fun (S : StoreTyping) (v : Value) (tau : Typ) => HasTypeValue S (update_ret_ctx (Some taus0) empty_Function_Ctx) v tau) Ss vs0 tauvs.
  Proof.
    intros.
    eapply Forall3_monotonic.
    2 : {exact H . }
    intros.
    simpl in H0.
    eapply HasTypeValue_Function_Ctx; try exact H0; simpl; easy.
  Qed.


Lemma local_typings_linear_label_agnostic : forall (A : Type) S_locals F locs (taus : list (Typ * A)) L tau1,
      Forall3 (fun (S : StoreTyping) (v : Value) '(t, _) => HasTypeValue S F v t) S_locals locs taus ->
      Forall3 (fun (S : StoreTyping) (v : Value) '(t, _) => HasTypeValue S (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) (update_label_ctx ((tau1, L) :: label F) F)) v t) S_locals locs taus.
  Proof.
  intros.
    eapply Forall3_monotonic.
    2 : {exact H . }
    intros.
    destruct x3.
    eapply HasTypeValue_Function_Ctx; try exact H0; induction F; simpl; easy.
  Qed.

(* End section of over specificity ZZZ *)

  Lemma Forall3_app_split : forall (A B C : Type) (P : A -> B -> C -> Prop) a b c1 c2, Forall3 P a b (c1 ++ c2) -> exists a1 a2 b1 b2, a1 ++ a2 = a /\ b1 ++ b2 = b /\ Forall3 P a1 b1 c1 /\ Forall3 P a2 b2 c2.
  Proof.
    intros.
    revert a b c2 H.
    induction c1; intros.
    + simpl in H.
      exists []. exists a. exists []. exists b.
      do 3 (split; eauto).
      eapply Forall3_nil.
    + rewrite<- app_comm_cons in H.
      invert H.
      eapply IHc1 in H5.
      destruct H5 as [a1 [a2 [b1 [b2 [H10 [H22 [H12 H13]]]]]]].
      exists (x :: a1). exists a2. exists (y :: b1). exists b2.
      do 2 (split; try (rewrite<- app_comm_cons; f_equal; assumption)).
      split; eauto.
      eapply Forall3_cons; eauto.
  Qed.

  Lemma Forall_nth_error : forall (A : Type) (P : A -> Prop) L n a,
      nth_error L n = Some a -> Forall P L -> P a.
  Proof.
    intros.
    revert n H.
    induction L; intros.
    + unfold nth_error in H.
      destruct n; simpl in H; discriminate.
    + invert H0.
      destruct n.
      - simpl in H.
        invert H.
        assumption.
      - simpl in H.
        exact (IHL H4 _ H).
  Qed.

  Lemma Forall2_switch : forall (A B : Type) (P : A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 -> Forall2 (fun b a => P a b) l2 l1.
  Proof.
    intros.
    revert l2 H.
    induction l1; intros.
    - invert H.
      eauto.
    - invert H.
      eapply IHl1 in H4.
      eapply Forall2_cons; eauto.
  Qed.

  Lemma Forall2_nth_error : forall (A B : Type) (P : A -> B -> Prop) l L b n,
      nth_error L n = Some b -> Forall2 P l L -> exists a, nth_error l n = Some a /\ P a b.
  Proof.
    intros.
    revert n H l H0.
    induction L; intros.
    + unfold nth_error in H.
      destruct n; simpl in H; discriminate.
    + invert H0.
      destruct n.
      - simpl in H.
        invert H.
        invert H0.
        exists x.
        split; eauto.
      - simpl in H.
        exact (IHL _ H _ H5).
  Qed.

  Lemma Forall3_nth_error : forall (A B C : Type) (P : A -> B -> C -> Prop) L1 L2 L3 c n,
      nth_error L3 n = Some c -> Forall3 P L1 L2 L3 -> exists a b, nth_error L1 n = Some a /\ nth_error L2 n = Some b /\ P a b c.
  Proof.
    intros.
    revert n H L1 L2 H0.
    induction L3; intros.
    + unfold nth_error in H.
      destruct n; simpl in H; discriminate.
    + invert H0. destruct n.
    - simpl in H.
        invert H.
        invert H0.
        exists x. exists y.
        split; eauto.
      - simpl in H.
        exact (IHL3 _ H _ _ H6).
  Qed.

  Lemma split_cons : forall (A B : Type) (a : A) (b : B) L la lb,
          split ((a, b) :: L) = (la, lb) ->
          exists la' lb',
                 a :: la' = la /\
                 b :: lb' = lb /\
                 split L = (la', lb').
  Proof.
    intros.
    destruct la; destruct lb; try (simpl in H; destruct (split L); invert H).
    eauto.
  Qed.

  Lemma split_combine_eq : forall (A B : Type) L (l1 : list A) (l2 : list B) , split L = (l1, l2) -> combine l1 l2 = L.
  Proof.
    intros.
    revert l1 l2 H.
    induction L; intros.
    + invert H.
      eauto.
    + destruct a.
      eapply split_cons in H.
      destruct H as [la' [lb' [H10 [H11 H12]]]].
      eapply IHL in H12.
      rewrite<- H10.
      rewrite<- H11.
      simpl.
      apply f_equal.
      assumption.
  Qed.

  (* Begin second round of over-specific lemmas YYY *)
  Lemma qual_linear_label : forall F tau1 L q,
      qual F = [] ->
      qual (update_linear_ctx (list_util.Cons_p q (linear F)) (update_label_ctx ((tau1, L) :: label F) F)) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma qual_linear : forall F q,
      qual F = [] ->
      qual (update_linear_ctx (list_util.set_hd q (linear F)) F) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma size_linear_label : forall F tau1 L q,
      size_t F = [] ->
      size_t (update_linear_ctx (list_util.Cons_p q (linear F)) (update_label_ctx ((tau1, L) :: label F) F)) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma size_linear : forall F q,
      size_t F = [] ->
      size_t (update_linear_ctx (list_util.set_hd q (linear F)) F) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma type_linear_label : forall F tau1 L q,
      type F = [] ->
      type (update_linear_ctx (list_util.Cons_p q (linear F)) (update_label_ctx ((tau1, L) :: label F) F)) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma label_linear_label : forall F x q,
      label F = x ->
      label (update_linear_ctx (Cons_p q (linear F)) F) = x.
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.

  Lemma label_update_label : forall L F,
      label (update_label_ctx L F) = L.
  Proof.
    intros.
    induction F.
    simpl.
    easy.
  Qed.

  Lemma type_linear : forall F q,
      type F = [] ->
      type (update_linear_ctx (list_util.set_hd q (linear F)) F) = [].
  Proof.
    intros.
    induction F.
    simpl.
    simpl in H.
    assumption.
  Qed.
  (* End second round YYY *)

  Lemma split_combine_cons : forall (A B : Type) (a : A) (b : B) L1 L2,
          (split ((a, b) :: combine L1 L2)) = (a :: L1, b :: L2) ->
          (split (combine L1 L2)) = (L1, L2).
  Proof.
    intros.
    invert H.
    destruct (split (combine L1 L2)).
    invert H1.
    easy.
  Qed.

  Lemma forall3_combine : forall (A B C D : Type) (R : A -> B -> C -> Prop) L1 L2 L3 (L4 : list D),
                          Forall3 (fun a b c => R a b c) L1 L2 L3 ->
                          split (combine L3 L4) = (L3, L4) ->
                          Forall3 (fun a b '(c, _) => R a b c) L1 L2 (combine L3 L4).
  Proof.
    intros.
    revert L1 L2 L4 H H0.
    induction L3; intros.
    + invert H0.
      simpl.
      invert H.
      eapply Forall3_nil.
    + invert H.
      simpl in H0.
      destruct L4.
      invert H0.
      eapply split_combine_cons in H0.
      assert (H10 := IHL3 l l' L4 H6 H0).
      eapply Forall3_cons.
      exact H5.
      exact H10.
  Qed.


  Lemma subset_commutes_1 : forall (H : HeapTyping) Hs1 Hs2,
  Union_list (map map_util.Dom_ht (Hs1 ++ H :: Hs2)) \subset Union_list (map map_util.Dom_ht (H :: Hs1 ++ Hs2)).
    intros.
    unfold "\subset".
    unfold map_util.Dom_ht.
    unfold map_util.Dom_map.
    unfold In.
    simpl.
    intros.
    induction Hs1.
    + simpl.
      simpl in H0.
      assumption.
    + simpl in H0.
      destruct H0.
      - right.
        left.
        assumption.
      - eapply IHHs1 in H0.
        destruct H0; try (left; assumption).
        right.
        right.
        assumption.
  Qed.

  Lemma subset_commutes_2 : forall (H : HeapTyping) Hs1 Hs2,
  Union_list (map map_util.Dom_ht (H :: Hs1 ++ Hs2)) \subset Union_list (map map_util.Dom_ht (Hs1 ++ H :: Hs2)).
  Proof.
    intros.
    unfold "\subset".
    unfold map_util.Dom_ht.
    unfold map_util.Dom_map.
    unfold In.
    simpl.
    intros.
    destruct H0.
    + unfold In in H0.
      induction Hs1.
      - simpl.
        left.
        assumption.
      - simpl.
        right.
        assumption.
    + unfold In in H0.
      induction Hs1.
      - simpl.
        right.
        simpl in H0.
        assumption.
      - simpl.
        simpl in H0.
        destruct H0; try (left; assumption).
        eapply IHHs1 in H0.
        right.
        assumption.
  Qed.

  Lemma Not_ExactlyInOne_commutes : forall H Hs1 Hs2 ht l,
  ExactlyInOne true l ht (H :: Hs1 ++ Hs2) ->
  ExactlyInOne true  l ht (Hs1 ++ H :: Hs2).
  Proof.
    intros.
    induction Hs1; eauto.
    invert H0.
    invert H8.
    assert (H20 := NotInHead _ _ _ _ _ H7 H10).
    eapply IHHs1 in H20.
    eapply NotInHead; eauto.
  Qed.

  Lemma ExactlyInOne_commutes : forall H Hs1 Hs2 ht l,
  ExactlyInOne false l ht (H :: Hs1 ++ Hs2) ->
  ExactlyInOne false l ht (Hs1 ++ H :: Hs2).
  Proof.
    intros.
    invert H0.
    + induction Hs1.
      - simpl.
        simpl in H7.
        eapply InHead; eauto.
      - invert H7.
        assert (H20 := InHead _ _ _ _ H4 H10).
        eapply IHHs1 in H20; try assumption.
        eapply NotInHead; eauto.
    + clear H0.
      revert H8.
      induction Hs1; intros.
      - simpl.
        simpl in H8.
        eapply NotInHead; eauto.
      - invert H8.
        * assert (H20 := NotInHead _ _ _ _ _ H7 H6).
          eapply Not_ExactlyInOne_commutes in H20.
          eapply InHead; eauto.
        * eapply IHHs1 in H9.
          eapply NotInHead; eauto.
  Qed.

  Lemma SplitHeapTypings_commutative : forall H1 H2 Hs1 Hs2,
    SplitHeapTypings (H1 :: Hs1 ++ Hs2) (LinTyp H2) ->
    SplitHeapTypings (Hs1 ++ H1 :: Hs2) (LinTyp H2).
  Proof.
    intros.
    invert H.
    clear H.
    split.
    + clear H3.
      unfold "<-->".
      unfold "<-->" in H0.
      destruct H0.
      split.
      - clear H0.
        assert (H0 := subset_commutes_1 H1 Hs1 Hs2).
        exact (Included_trans _ _ _ H0 H).
      - clear H.
        assert (H := subset_commutes_2 H1 Hs1 Hs2).
        exact (Included_trans _ _ _ H0 H).
    + intros.
      eapply H3 in H.
      eapply ExactlyInOne_commutes in H.
      assumption.
  Qed.

  Lemma SplitStoreTypings_commutative : forall S1 S2 Ss1 Ss2,
      SplitStoreTypings ((S1 :: Ss1) ++ Ss2) S2 ->
      SplitStoreTypings (Ss1 ++ (S1 :: Ss2)) S2.
  Proof.
    intros.
    invert H.
    split.
    + rewrite Forall_app.
      invert H0.
      eapply Forall_app in H5.
      destruct H5.
      split; eauto.
    + clear H0 H.
      simpl in H1.
      rewrite map_app in H1.
      rewrite map_app.
      simpl.
      eapply SplitHeapTypings_commutative.
      assumption.
  Qed.

  Lemma map_empty_util : forall var,
      map_util.M.find var (M.empty (list Qual * list Qual)) = None.
  Proof.
    intros.
    destruct var; eauto.
  Qed.

  Lemma inst_inds_length : forall vars taus0 taus1 taus2 taus3 is,
      InstInds (FunT vars (Arrow taus0 taus1)) is = Some (FunT [] (Arrow taus2 taus3)) ->
      length taus0 = length taus2.
  Proof.
    intros.
    revert vars taus0 taus1 taus2 taus3 H.
    induction is; intros.
    + unfold InstInds in H.
      simpl in H.
      invert H.
      reflexivity.
    + unfold InstInds in H.
      simpl in H.
      destruct vars; try (clear IHis; induction is; eauto; simpl in H; discriminate).
      destruct k; try
      ( destruct a; try (clear IHis; induction is; eauto; simpl in H; discriminate);
        unfold InstInds in IHis;
        eapply IHis in H;
        rewrite map_length in H;
        eauto).
  Qed.

  Lemma Dom_ht_from_heap_typing : forall (A : Type) l (x : map_util.M.t A) ht,
    map_util.get_heaptype l x = Some ht -> (map_util.Dom_ht x) l.
  Proof.
    intros.
    unfold map_util.Dom_ht.
    unfold In.
    unfold map_util.Dom_map.
    unfold map_util.get_heaptype in H.
    exists ht.
    eassumption.
  Qed.

  Lemma Dom_ht_superset : forall Ss i S' l,
    nth_error Ss i = Some S' ->
    map_util.Dom_ht (LinTyp S') l ->
    Union_list (map map_util.Dom_ht (map LinTyp Ss)) l.
  Proof.
    intros.
    revert i H.
    induction Ss.
    + intro i. case i; simpl; discriminate.
    + intro i.
      case i; intros.
      - simpl in H.
        invert H.
        simpl.
        left.
        assumption.
      - simpl in H.
        eapply IHSs in H.
        simpl.
        right.
        assumption.
  Qed.

  Lemma SplitStore_get_heaptype_sub_map : forall S S' Ss l ht i,
      SplitStoreTypings Ss S ->
      nth_error Ss i = Some S' ->
      map_util.get_heaptype l (LinTyp S') = Some ht ->
      map_util.get_heaptype l (LinTyp S) = Some ht.
  Proof.
    intros.
    invert H.
    simpl in H3.
    invert H3.
    destruct H4.
    unfold "\subset" in H4.
    unfold In in H4.
    assert (H10 := H4 l).
    assert (H20 := Dom_ht_from_heap_typing _ _ _ _ H1).
    assert (H30 := Dom_ht_superset _ _ _ _ H0 H20).
    assert (H40 := H10 H30).
    unfold map_util.Dom_ht in H40.
    unfold In in H40.
    unfold map_util.Dom_map in H40.
    destruct H40 as [x H40].
    fold (map_util.get_heaptype l (LinTyp S)) in H40.
    assert (H50 := H5 l x H40).
    clear H H2 H3 H4 H6 H5 H10 H20 H30.
    revert i H0.
    induction Ss.
    + simpl in H50.
      invert H50.
    + intros.
      destruct i.
      - simpl in H0.
        invert H0.
        invert H50.
        * rewrite<- H4 in H40.
          rewrite H1 in H40.
          assumption.
        * rewrite H7 in H1.
          discriminate.
      - simpl in H0.
        invert H50.
        * exfalso.
          clear H40 H50 IHSs H4 a S.
          revert i H0.
          induction Ss; intros.
          ++destruct i; discriminate.
          ++invert H7.
            assert (H10 := IHSs H9).
            destruct i.
            --simpl in H0.
              invert H0.
              rewrite H8 in H1.
              discriminate.
            --simpl in H0.
              exact (H10 _ H0).
        * exact (IHSs H8 i H0).
  Qed.


  Lemma nth_error_fst : forall (A : Type) (a : A) b,
      nth_error [a; b] 0 = Some a.
  Proof.
    eauto.
  Qed.

  Lemma nth_error_snd : forall (A : Type) (a : A) b,
      nth_error [a; b] 1 = Some b.
  Proof.
    eauto.
  Qed.


  (* This lemma is the crux of unrestricted memory usage *)
  Lemma mem_typing_specific_unrestricted : forall S_unr s l0 v l S0 ht,
      Forall2 (fun (S : StoreTyping) (hvl : N * HeapValue * Len) =>
                 exists ht : HeapType,
                 map_util.get_heaptype (fst (fst hvl)) (UnrTyp S) = Some ht /\
                 HasHeapType S empty_Function_Ctx (snd (fst hvl)) ht /\
                 RoomForStrongUpdates (snd hvl) ht /\
                 HeapTypeValid empty_Function_Ctx ht) S_unr (to_list Unrestricted (meminst s)) ->
      get l0 Unrestricted (meminst s) = Some (v, l) ->
      map_util.get_heaptype l0 (UnrTyp S0) = Some ht ->
      Forall (fun S' : StoreTyping => InstTyp S0 = InstTyp S' /\ UnrTyp S0 = UnrTyp S') S_unr ->
      exists S',
        RoomForStrongUpdates l ht /\
        HasHeapType S' empty_Function_Ctx v ht.
  Proof.
    intros.
    eapply get_implies_in_to_list in H0.
    destruct H0 as [i H0].
    destruct (Forall2_nth_error _ _ _ _ _ _ _ H0 H) as [S [H3 [ht2 [H4 [H5 [H6 H7]]]]]].
    destruct (Forall_nth_error _ _ _ _ _ H3 H2).
    simpl in H4.
    simpl in H5.
    simpl in H6.
    rewrite H9 in H1.
    rewrite H1 in H4.
    invert H4.
    exists S.
    split; assumption.
  Qed.

  Lemma mem_typing_specific_linear : forall S_whole S_heap S_prog s l0 v l ht S_lin S_unr,
      Forall2
        (fun (S : StoreTyping) (hvl : N * HeapValue * Len) =>
           exists ht : HeapType,
             (map_util.get_heaptype (fst (fst hvl)) (LinTyp S_heap) = Some ht \/
              map_util.get_heaptype (fst (fst hvl)) (LinTyp S_prog) = Some ht) /\
             HasHeapType S empty_Function_Ctx (snd (fst hvl)) ht /\
             RoomForStrongUpdates (snd hvl) ht /\
             HeapTypeValid empty_Function_Ctx ht) S_lin (to_list Linear (meminst s)) ->
      get l0 Linear (meminst s) = Some (v, l) ->
      map_util.get_heaptype l0 (LinTyp S_prog) = Some ht ->
      SplitStoreTypings [S_prog; S_heap] S_whole ->
      SplitStoreTypings (S_lin ++ S_unr) S_heap ->
      exists S',
        RoomForStrongUpdates l ht /\
        HasHeapType S' empty_Function_Ctx v ht.
  Proof.
    intros.
    eapply get_implies_in_to_list in H0.
    destruct H0 as [i H0].
    destruct (Forall2_nth_error _ _ _ _ _ _ _ H0 H) as [S [H4 [ht2 [H5 [H6 [H7 H8]]]]]].
    simpl in H5.
    simpl in H6.
    simpl in H7.
    assert (H10 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H2 (nth_error_fst _ S_prog S_heap) H1).
    destruct H5.
    + assert (H11 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H2 (nth_error_snd _ S_prog S_heap) H5).
      rewrite H10 in H11.
      invert H11.
      exists S.
      split; assumption.
    + assert (H11 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H2 (nth_error_fst _ S_prog S_heap) H5).
      rewrite H10 in H11.
      invert H11.
      exists S.
      split; assumption.
  Qed.


  Lemma f_equal_app : forall (A B : Type) (f g : A -> B) (x : A),
      f = g -> f x = g x.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma update_empty_fun_ctx_none : (update_ret_ctx None empty_Function_Ctx) = empty_Function_Ctx.
  Proof.
    unfold update_ret_ctx.
    unfold empty_Function_Ctx.
    eauto.
  Qed.


  Lemma union_implication : forall (A : Type) (f1 : Ensemble A) (f2 : Ensemble A) l v, ((f1 :|: f2) l -> v) -> (f2 l -> v).
  Proof.
    intros.
    eapply X.
    right.
    assumption.
  Qed.

  Lemma nth_error_cons : forall (A : Type) (a : A) L, nth_error (a :: L) 0 = Some a.
  Proof.
    eauto.
  Qed.


  Lemma Union_list_cons_subset : forall x,
    Union_list (map map_util.Dom_ht (map_util.M.empty HeapType :: x)) \subset
    Union_list (map map_util.Dom_ht (x)).
  Proof.
    unfold "\subset".
    unfold map_util.Dom_ht.
    unfold map_util.Dom_map.
    unfold In.
    simpl.
    intros.
    destruct H; eauto.
    unfold In in H.
    destruct H.
    assert (H1 := map_util.M.gempty HeapType (N.succ_pos x0)).
    rewrite H1 in H.
    discriminate.
  Qed.

  Lemma Union_list_subset_cons : forall x,
    Union_list (map map_util.Dom_ht (x)) \subset
    Union_list (map map_util.Dom_ht (map_util.M.empty HeapType :: x)).
  Proof.
    unfold "\subset".
    unfold map_util.Dom_ht.
    unfold map_util.Dom_map.
    unfold In.
    simpl.
    intros.
    induction x; eauto.
    - simpl in H.
      invert H.
    - simpl in H.
      destruct H.
      + simpl.
        right. left.
        exact H.
      + eapply IHx in H.
        simpl.
        destruct H.
        * left.
          eassumption.
        * right. right. eassumption.
  Qed.

  Lemma store_typing_split_n : forall (S : StoreTyping) (n : nat),
      n > 0 ->
      exists Ss,
        length Ss = n /\
        SplitStoreTypings Ss S.
  Proof.
    intros.
    induction n; try invert H.
    - exists [S].
      split; eauto.
      split; try (eapply Forall_cons; eauto).
      simpl.
      split; intros.
      + unfold "<-->".
        unfold "\subset".
        unfold map_util.Dom_ht.
        unfold map_util.Dom_map.
        unfold In.
        simpl.
        split; intros.
        * do 2 destruct H0; eauto.
        * left.
          unfold In.
          eassumption.
      + eapply InHead; eauto; try eapply FoundNil.
    - assert (n > 0) by lia.
      eapply IHn in H0.
      do 2 destruct H0.
      exists ((Build_StoreTyping (InstTyp S) (map_util.M.empty HeapType) (UnrTyp S)) :: x).
      simpl.
      split; eauto.
      invert H2.
      split; eauto.
      simpl.
      simpl in H4.
      invert H4.
      split; eauto.
      + destruct H0.
        split.
        * exact (Included_trans _ _ _ (Union_list_cons_subset (map LinTyp x)) H0).
        * exact (Included_trans _ _ _ H6 (Union_list_subset_cons (map LinTyp x))).
      + intros.
        eapply H5 in H6.
        eapply NotInHead; eauto.
        eapply map_util.M.gempty.
  Qed.

  Lemma value_map_is_values : forall es vs,
      es = map Val vs ->
      values es.
  Proof.
    intros.
    unfold values.
    unfold value.
    revert es H.
    induction vs; intros; simpl in H; try (invert H; eauto).
    eapply Forall_cons; eauto.
    simpl.
    easy.
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
    rewrite map_util.Dom_ht_is_empty; eauto. now sets.
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

  Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.


  Lemma locals_value_agnostic : forall S C F L1 L2 x tau1 tau2,
      HasTypeInstruction S C F L1 (map Val x) (Arrow tau1 tau2) L2 ->
      LCEffEqual (size F) L1 L2.
  Proof.
    intros.
    assert (H0 := value_map_is_values (map Val x) x (eq_refl _)).
    destruct (Values_HasTypeInstruction _ _ _ _ _ _ _ _ H0 H) as [t [Ss [H1 [H2 [H3 H4]]]]]; eauto.
    destructAll; auto.
  Qed.

  Lemma size_typecheck_eq : forall S1 S2 v1 v2 tau,
    HasTypeValue S1 empty_Function_Ctx v1 tau ->
    HasTypeValue S2 empty_Function_Ctx v2 tau ->
    size_val v2 = size_val v1.
  Proof.
    intros.
    edestruct (HasTypeValue_sizeOfType_concrete) as [sz [n [H1 H2]]].
    eapply H. reflexivity.
    assert (H3 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H H1 (eq_refl _) H2).
    assert (H4 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H0 H1 (eq_refl _) H2).
    lia.
  Qed.


  Lemma Singleton_map_get : forall S l ht,
      map_util.eq_map (LinTyp S)
                      (map_util.M.add (N.succ_pos l) ht (map_util.M.empty HeapType))
      -> map_util.get_heaptype l (LinTyp S) = Some ht.
  Proof.
    intros.
    unfold map_util.eq_map in H.
    rewrite (H l).
    unfold map_util.get_heaptype.
    induction l; eauto.
    simpl.
    clear H.
    induction p; eauto.
    simpl.
    induction p; eauto.
  Qed.


  (* Print Assumptions struct_typing_implies_size. *)

  Lemma fold_size_constant : forall l1 l2 c1 c2,
      Forall2 (fun (v : Value) (sz : Size) => exists n : nat, size_to_nat sz = Some n /\ (size_val v <= n)) l1 l2 ->
      (c1 <= c2)%N ->
      (fold_left (fun (n : N) (v0 : Value) => N.of_nat (size_val v0) + n) l1 c1 <=
       fold_left (fun (acc : N) (sz0 : Size) => match size_to_nat sz0 with
                                                | Some n => acc + N.of_nat n
                                                | None => acc
                                                end) l2 c2)%N.
  Proof.
    induction l1; intros; try (invert H; simpl; assumption).
    invert H.
    destruct H3 as [n [H10 H11]].
    simpl.
    rewrite H10.
    assert (N.of_nat (size_val a) + c1 <= c2 + N.of_nat n)%N by lia.
    exact (IHl1 _ _ _ H5 H1).
  Qed.

  Lemma nth_error_preceding : forall (A : Type) ss n (s : A),
      nth_error ss (Datatypes.S n) = Some s ->
      exists s', nth_error ss n = Some s'.
  Proof.
    intros.
    assert (nth_error ss (Datatypes.S n) <> None).
    { intro.
      congruence.
    }
    eapply nth_error_Some in H0.
    assert (n < length ss) by lia.
    eapply nth_error_Some in H1.
    destruct (nth_error ss n); eauto.
    congruence.
  Qed.

  Lemma Forall3_flip : forall (A B C : Type) (l1 : list A) (l2 : list B) (l3 : list C) R,
      Forall3 (fun x1 x2 x3 => R x1 x2 x3) l1 l2 l3 -> Forall3 (fun x1 x3 x2 => R x1 x2 x3) l1 l3 l2.
  Proof.
    induction l1; intros; invert H; try (exact (Forall3_nil (fun x1 x3 x2 => R x1 x2 x3))).
    assert (IH := IHl1 _ _ _ H5).
    eapply Forall3_cons; eauto.
  Qed.


(* Lemmas to be proven *)

  (* TODO Move to splitting.v *)
  Definition UnionStoreTyping (S1 S2 : StoreTyping) :=
    {| InstTyp := InstTyp S1; LinTyp := union (LinTyp S1) (LinTyp S2); UnrTyp := UnrTyp S1 |}.

  Definition EmptyStoreTyping := {| InstTyp := []; LinTyp := M.empty _; UnrTyp := M.empty _ |}.
  
  Definition union_all := fold_right UnionStoreTyping EmptyStoreTyping.

  Definition SplitStoreTypings' Ss (S : StoreTyping) :=
    Forall (fun S' => InstTyp S = InstTyp S' /\ UnrTyp S = UnrTyp S') Ss /\
    SplitHeapTypings' (map LinTyp Ss) (LinTyp S).

  Lemma SplitStoreTypings_spec Ss S :
    SplitStoreTypings Ss S <-> SplitStoreTypings' Ss S.
  Proof.
    unfold SplitStoreTypings, SplitStoreTypings'; split; intuition eauto;
      (rewrite SplitHeapTypings_spec + rewrite <- SplitHeapTypings_spec); auto.
  Qed.
  
  Lemma minus_union_cancel {A} (M N : map_util.M.t A) :
    Disjoint _ (map_util.Dom_ht M) (map_util.Dom_ht N) ->
    map_util.M.Equal (minus (union M N) M) N.
  Proof.
    intros Hdis; intros x; unfold minus, union; rewrite !M.gmap2 by auto.
    destruct (M.find x M) as [x'|] eqn:Hx'.
    - destruct Hdis as [Hdis]. specialize (Hdis (Pos.pred_N x)).
      destruct (M.find x N) as [x''|] eqn:Hx''; auto.
      contradiction Hdis; split; [exists x'; now rewrite succ_pos_pred_N|].
      exists x''. now rewrite succ_pos_pred_N.
    - destruct (M.find x N); auto.
  Qed.

  Lemma Equal_sym {A} (M N : map_util.M.t A) : M.Equal M N -> M.Equal N M.
  Proof. intros H x; specialize (H x); congruence. Qed.

  Lemma Dom_ht_union_all Ss :
    map_util.Dom_ht (LinTyp (union_all Ss)) <--> Union_list (map map_util.Dom_ht (map LinTyp Ss)).
  Proof.
    induction Ss; cbn; [now rewrite map_util.Dom_ht_empty|].
    now rewrite <- IHSs, Dom_ht_union.
  Qed.

  Lemma SplitStoreTypings_cons_Disjoint S Ss (S_whole : StoreTyping) :
    SplitStoreTypings (S :: Ss) S_whole ->
    Disjoint _ (map_util.Dom_ht (LinTyp S)) (map_util.Dom_ht (LinTyp (union_all Ss))).
  Proof.
    intros. inv H. cbn in *. inv H1. cbn in *.
    let t := type of H2 in change t
      with (get_ExactlyInOne (LinTyp S_whole) ([] ++ [LinTyp S] ++ map LinTyp Ss)) in H2.
    apply get_ExactlyInOne_disjoint in H2; cbn in *; 
      rewrite Union_Empty_set_neut_l in *; [|apply Same_set_sym; auto].
    rewrite Dom_ht_union_all; auto.
  Qed.
    
  Lemma SplitStoreTypings_union_all Ss S :
    SplitStoreTypings Ss S ->
    SplitStoreTypings Ss (union_all Ss).
  Proof.
    rewrite !SplitStoreTypings_spec; revert S; induction Ss as [|S' Ss IHSs]; intros S.
    - cbn; intros; constructor; auto; cbn; constructor; auto; cbn.
    - intros H; pose proof H as H'; rewrite <- SplitStoreTypings_spec in H'.
      pose proof H as H''.
      apply SplitStoreTypings_cons_Disjoint in H'.
      unfold SplitStoreTypings' in H|-*; cbn. intuition eauto.
      + inv H0. constructor; auto. eapply Forall_impl; try eassumption.
        cbn; intuition congruence.
      + rewrite splitting.Dom_ht_union. eauto with Ensembles_DB.
      + match goal with H : In _ (map_util.Dom_ht _) _ |- _ => destruct H as [res Hres] end.
        unfold map_util.get_heaptype.
        unfold union. rewrite M.gmap2 by auto.
        now rewrite Hres in *.
      + eapply SplitHeapTypings'_resp_Equal; [apply Equal_sym; apply minus_union_cancel; auto|].
        inv H1. inv H2.
        specialize (IHSs {|InstTyp := InstTyp S;
                           LinTyp := (minus (LinTyp S) (LinTyp S')); UnrTyp := UnrTyp S|}).
        apply IHSs; unfold SplitStoreTypings'; intuition eauto.
        inv H0. eapply Forall_impl; try eassumption. cbn; intuition congruence.
  Qed.

  (* END TODO move to splitting.v *)

  Lemma SplitStoreTypings_cons_InstUnr S Ss S_whole :
    SplitStoreTypings (S :: Ss) S_whole ->
    InstTyp S = InstTyp S_whole /\ UnrTyp S = UnrTyp S_whole.
  Proof. intros H; inv H; inv H0; constructor; cbn in *; intuition. Qed.

  Definition map_leq {A} (m1 m2 : map_util.M.t A) :=
    forall l, l \in map_util.Dom_ht m1 -> map_util.get_heaptype l m1 = map_util.get_heaptype l m2.
  
  Lemma typing_valid_Dom_sub S_sub S S_heap s :
    map_leq (LinTyp S_sub) (LinTyp S) ->
    map_leq (UnrTyp S_sub) (UnrTyp S) ->
    typing_valid S S_heap s ->
    typing_valid S_sub S_heap s.
  Proof.
    unfold typing_valid; intros Hsub_lin Hsub_unr Hvalid l ht.
    specialize (Hvalid l ht); split; destruct Hvalid as [Hvalid_lin Hvalid_unr]; intros Hget.
    - specialize (Hsub_lin l (ex_intro _ ht Hget)); rewrite Hsub_lin in Hget; auto.
    - specialize (Hsub_unr l (ex_intro _ ht Hget)); rewrite Hsub_unr in Hget; auto.
  Qed.

  Lemma typing_valid_Doms S Ss S_whole :
    SplitStoreTypings (S :: Ss) S_whole ->
    map_leq (LinTyp S) (LinTyp S_whole) /\ map_leq (UnrTyp S) (UnrTyp S_whole).
  Proof.
    intros H; pose proof H as H'.
    inv H; cbn in *; inv H0; split; [|intros l; intuition congruence].
    rewrite SplitStoreTypings_spec in H'; unfold SplitStoreTypings' in H'; cbn in H'.
    unfold map_leq; intuition eauto.
  Qed.

  Lemma SplitStoreTypings_cons_InstTyp S Ss S_whole :
    SplitStoreTypings (S :: Ss) S_whole ->
    InstTyp S = InstTyp S_whole.
  Proof.
    intros H; inv H. inv H0. destruct S, S_whole; cbn; f_equal; cbn in *; intuition congruence.
  Qed.
  
  Lemma drop_values_stores : forall S1 S2 S S_locals S_rest S_whole S_heap s i C,
    SplitStoreTypings (((S1 ++ S2) ++ [S]) ++ S_locals) S_rest ->
    nth_error (InstTyp S_rest) i = Some C ->
    typing_valid S_rest S_heap s ->
    Forall2 (fun i C => HasTypeInstance (InstTyp S_rest) i C) (inst s) (InstTyp S_rest) ->
    Forall (fun S' : StoreTyping => InstTyp S_whole = InstTyp S' /\ UnrTyp S_whole = UnrTyp S')
      [S_rest; S_heap] ->
    exists S',
           SplitStoreTypings ((S2 ++ [S]) ++ S_locals) S' /\
           nth_error (InstTyp S') i = Some C /\
           typing_valid S' S_heap s /\
           Forall2 (fun i C => HasTypeInstance (InstTyp S') i C) (inst s) (InstTyp S') /\
           Forall (fun S'' : StoreTyping => InstTyp S_whole = InstTyp S'' /\ UnrTyp S_whole = UnrTyp S'')
             [S'; S_heap].
  Proof.
    intros* Hsplit_rest Hget Hvalid Hunr Hsplit_whole.
    rewrite <- (app_assoc S1 S2 [S]) in Hsplit_rest.
    rewrite <- (app_assoc S1 (S2 ++ [S])) in Hsplit_rest.
    apply SplitStoreTypings_comm' in Hsplit_rest.
    apply SplitStoreTyping_app in Hsplit_rest.
    destruct Hsplit_rest as [S' [HS' Hsplit_rest]]; exists S'; split; auto.
    split; [apply SplitStoreTypings_cons_InstUnr in Hsplit_rest; intuition congruence|].
    split; [apply typing_valid_Doms in Hsplit_rest; eapply typing_valid_Dom_sub; intuition eauto|].
    assert (HInstTyp : InstTyp S' = InstTyp S_rest)
      by (inv Hsplit_rest; inv H; cbn in *; intuition congruence).
    assert (HUnrTyp : UnrTyp S' = UnrTyp S_rest)
      by (inv Hsplit_rest; inv H; cbn in *; intuition congruence).
    rewrite HInstTyp.
    split; [eapply Forall2_monotonic; [|eassumption]; cbn; intros; eauto|].
    inv Hsplit_whole; inv H2; constructor; intuition eauto; try congruence.
  Qed.

  Lemma drop_function_frame_store : forall S_values S_locals S S_rest S_heap S_whole s,
      SplitStoreTypings ((S_values ++ [S]) ++ S_locals) S_rest ->
      Forall (fun S' : StoreTyping => InstTyp S_whole = InstTyp S' /\ UnrTyp S_whole = UnrTyp S')
         [S_rest; S_heap] ->
      typing_valid S_rest S_heap s ->
      Forall (fun S' : StoreTyping => InstTyp S_whole = InstTyp S' /\ UnrTyp S_whole = UnrTyp S')
         [S; S_heap] /\
      typing_valid S S_heap s.
  Proof.
    intros* Hsplit_rest Hsplit_whole Hvalid.
    rewrite <- app_assoc in Hsplit_rest.
    apply SplitStoreTypings_comm' in Hsplit_rest.
    pose proof Hsplit_rest as HInstUnr.
    apply SplitStoreTypings_cons_InstUnr in HInstUnr; split.
    - inv Hsplit_whole; inv H2; constructor; [|constructor]; intuition eauto; try congruence.
    - eapply typing_valid_Doms in Hsplit_rest.
      eapply typing_valid_Dom_sub; try eassumption; intuition eauto.
  Qed.

  Lemma sequence_store : forall S1 S2 S S_values S_locals S_rest S_heap S_whole i C s,
      SplitStoreTypings [S1; S2] S ->
      SplitStoreTypings ((S_values ++ [S]) ++ S_locals) S_rest ->
      Forall (fun S' : StoreTyping => InstTyp S_whole = InstTyp S' /\ UnrTyp S_whole = UnrTyp S')
         [S_rest; S_heap] ->
      nth_error (InstTyp S_rest) i = Some C ->
      typing_valid S_rest S_heap s ->
      Forall2 (fun i C => HasTypeInstance (InstTyp S_rest) i C) (inst s) (InstTyp S_rest) ->
      exists S',
             SplitStoreTypings ((S_values ++ [S1]) ++ S_locals) S' /\
             Forall (fun S'' : StoreTyping => InstTyp S' = InstTyp S'' /\ UnrTyp S' = UnrTyp S'')
               [S'; S_heap] /\
             nth_error (InstTyp S') i = Some C /\
             typing_valid S' S_heap s /\
             Forall2 (fun i C => HasTypeInstance (InstTyp S') i C) (inst s) (InstTyp S').
  Proof.
    intros* Hsplit_S Hsplit_rest Hsplit_whole Hnth Hvalid Hforall.
    rewrite <- app_assoc in Hsplit_rest.
    apply SplitStoreTypings_comm' in Hsplit_rest.
    eapply SplitStoreTypings_merge' in Hsplit_rest; eauto.
    change (_ S_locals S_values) with (S_locals ++ S_values) in *.
    change (_ ++ _ ++ _) with ([S1] ++ [S2] ++ S_locals ++ S_values) in Hsplit_rest.
    apply SplitStoreTypings_permut with (S2 := ((S_values ++ [S1]) ++ S_locals) ++ [S2]) in Hsplit_rest.
    2:{ rewrite app_assoc. eapply Permutation.perm_trans; [apply Permutation.Permutation_app_tail;
                                                           apply Permutation.Permutation_app_comm|].
        rewrite <- app_assoc.
        eapply Permutation.perm_trans; [apply Permutation.Permutation_app_comm|].
        apply Permutation.Permutation_app_tail.
        eapply Permutation.perm_trans; [apply Permutation.Permutation_app_head;
                                        apply Permutation.Permutation_app_comm|].
        rewrite app_assoc; apply Permutation.Permutation_app_tail.
        apply Permutation.Permutation_app_comm. }
    apply SplitStoreTyping_app in Hsplit_rest; destruct Hsplit_rest as [S' [HS' Hsplit_rest]].
    exists S'; split; [easy|].
    assert (HInstUnr : InstTyp S' = InstTyp S_rest /\ UnrTyp S' = UnrTyp S_rest)
      by now apply SplitStoreTypings_cons_InstUnr in Hsplit_rest.
    split; [|split; [intuition congruence|split]].
    - inv Hsplit_whole; inv H2; constructor; auto; constructor; intuition; try congruence.
    - apply typing_valid_Doms in Hsplit_rest; eapply typing_valid_Dom_sub; intuition eauto.
    - rewrite (proj1 HInstUnr). eapply Forall2_monotonic; try eassumption; cbn.
      eauto.
  Qed.
  
  (* BEGIN MISC LEMMAS
     TODO John: misc lemmas that should be moved to proper places *)
  Definition sizes_as_Nat szs :=
    fold_left
       (fun (acc : nat) (sz : Size) =>
          match size_to_nat sz with
          | Some n => acc + n
          | None => acc
          end) szs 0.

  Lemma term_size_Struct vs : term.size (Struct vs) = list_sum (map size_val vs).
  Proof.
    cbn.
    rewrite fold_left_map with (f := Nat.add) (g := size_val) in * by lia.
    rewrite fold_symmetric in * by lia.
    induction vs; cbn in *; auto.
  Qed.

  Lemma sizes_as_Nat_app xs ys : sizes_as_Nat (xs ++ ys) = (sizes_as_Nat xs + sizes_as_Nat ys).
  Proof.
    unfold sizes_as_Nat.
    rewrite !fold_left_map with
        (f := Nat.add)
        (g := fun sz => match size_to_nat sz with None => 0 | Some n => n end)
      by (intros; destruct (size_to_nat x); lia).
    rewrite !fold_symmetric by lia.
    induction xs; cbn; auto. intuition lia.
  Qed.

  Lemma set_nth_spec {A} (xs : list A) n y :
    (n < length xs) ->
    set_nth xs n y = firstn n xs ++ [y] ++ skipn (1 + n) xs.
  Proof.
    revert n; induction xs as [|x' xs IHxs].
    - destruct n; inversion 1.
    - destruct n; cbn; auto.
      replace (n - 0) with n by lia.
      intros; rewrite IHxs; auto. lia.
  Qed.
  (* END MISC LEMMAS *)

  Lemma fields_well_sized_totals_well_sized vs is :
    Forall2 (fun v sz => exists n, size_to_nat sz = Some n /\ size_val v <= n) vs is ->
    (list_sum (map size_val vs) <= sizes_as_Nat is).
  Proof.
    unfold sizes_as_Nat.
    rewrite !fold_left_map with
        (f := Nat.add)
        (g := fun sz => match size_to_nat sz with None => 0 | Some n => n end)
      by (intros; destruct (size_to_nat _); lia).
    rewrite !fold_symmetric by lia.
    induction 1; [now cbn|].
    destruct H as [n [Hn Hleq]].
    cbn in *. rewrite Hn. unfold list_sum in IHForall2. lia.
  Qed.

  Lemma size_update : forall vs i l v_old v_new,
    nth_error vs i = Some v_old ->
    (size_val v_new <= size_val v_old) ->
    (fold_left (fun n v => size_val v + n) vs 0 <= l) ->
    (fold_left (fun n v => size_val v + n) (set_nth vs i v_new) 0 <= l).
  Proof.
    intros* Hnth Hleq.
    rewrite !fold_left_map with (f := Nat.add) (g := size_val), !fold_symmetric by lia.
    intros; enough (
                fold_right Nat.add 0 (map size_val (set_nth vs i v_new)) <=
                fold_right Nat.add 0 (map size_val vs))
      by lia.
    clear H; revert dependent i; induction vs; [destruct i; inversion 1; auto|].
    destruct i.
    - intros H; inv H; cbn; lia.
    - intros H; inv H; cbn. specialize (IHvs i ltac:(auto)).
      replace (i - 0) with i by lia. lia.
  Qed.

  (* Michael: This lemma shows that a store that is used to check a list of values can be split into a series
              of stores to check each value. *)
  Lemma specialize_instruction_value_typing : forall S_values S1 S2 S S_locals S_rest vs1 vs2 taus1 taus2 C F L,
  Forall3 (fun (S' : StoreTyping) (v : Value) (t : Typ) => HasTypeValue S' F v t) S_values vs1 taus1 ->
  HasTypeInstruction S1 C F L (map Val vs2) (Arrow taus1 taus2) L ->
  SplitStoreTypings ((S_values ++ [S]) ++ S_locals) S_rest ->
  SplitStoreTypings [S1; S2] S ->
  exists Ss',
    Forall3 (fun (S' : StoreTyping) (v : Value) (t : Typ) => HasTypeValue S' F v t) (S_values ++ Ss') (vs1 ++ vs2) taus2 /\
    SplitStoreTypings (((S_values ++ Ss') ++ [S2]) ++ S_locals) S_rest.
  Proof.
    intros* Hforall Hvs2 Hsplit_rest Hsplit_S.
    assert (values (map Val vs2)) by apply values_Val.
    pose proof Hvs2 as Hvs2'.
    unshelve eapply Values_HasTypeInstruction in Hvs2; auto.
    rewrite to_values_Val in Hvs2.
    destruct Hvs2 as [vts [Ss [Hvts [HSs [Htyping H']]]]].
    destructAll.
    exists Ss.
    split; [ apply Forall3_app; auto|].
    rewrite <- app_assoc in Hsplit_rest.
    apply SplitStoreTypings_comm' in Hsplit_rest.
    eapply SplitStoreTypings_merge' in Hsplit_rest; try eassumption.
    change (_ S_locals S_values) with (S_locals ++ S_values) in Hsplit_rest.
    eapply SplitStoreTypings_merge' in Hsplit_rest; try eassumption.
    rewrite <- (app_assoc _ [S2] S_locals), <- app_assoc.
    apply SplitStoreTypings_comm'.
    rewrite <- !app_assoc; apply Hsplit_rest.
  Qed.

  (* Michael: This lemma is surprisingly complicated. The idea is that we need to know that the
              update of an element does not make the overall struct too large. *)
  Lemma struct_update_size : forall n vs szs sz sz_slot n_sz_slot v l S taus tauszs,
      (sizes_as_Nat szs <= l) ->
      (term.size (Struct vs) <= sizes_as_Nat szs) ->
      HasHeapType S empty_Function_Ctx (Struct vs) (StructType tauszs) ->
      split tauszs = (taus, szs) ->
      size_val v = sz ->
      nth_error szs n = Some sz_slot ->
      size_to_nat sz_slot = Some n_sz_slot ->
      sz <= n_sz_slot ->
      (term.size (Struct (set_nth vs n v)) <= l).
  Proof.
    intros. rewrite term_size_Struct in *.
    enough (list_sum  (map size_val (set_nth vs n v)) <= sizes_as_Nat szs) by lia. clear H l.
    assert (n < length szs) by (eapply nth_error_Some_length; eauto).
    pose proof H1 as HHeapType.
    eapply struct_typing_implies_size in HHeapType; eauto.
    inv H1.
    assert (length szs = length vs).
    { apply Forall3_length in H10.
      assert (taus0 = fst (split tauszs)) by (destruct (split tauszs); cbn; congruence).
      assert (length taus0 = length tauszs) by (subst; eapply split_length_l).
      assert (szs = snd (split tauszs)) by (destruct (split tauszs); cbn; congruence).
      assert (length szs = length tauszs) by (subst; eapply split_length_r).
      lia. }
    assert (n < length vs) by lia.
    rewrite set_nth_spec, !map_app, !list_sum_app by auto.
    rewrite (split_list_at_n vs n v) in H0 by lia.
    rewrite !map_app, !list_sum_app in * by auto.
    change (list_sum (map size_val [?x])) with (size_val x + 0) in *.
    rewrite (split_list_at_n vs n v) in H10 by lia.
    apply Forall3_app_inv_2 in H10.
    destruct H10 as [Ss1 [SS3 [taus1 [taus3' [HForall1 [HForall23 [-> ->]]]]]]].
    assert (Hlen_taus1 : length taus1 = n).
    { apply Forall3_length in HForall1.
      rewrite <- firstn_length_le with (l := vs); lia. }
    apply Forall3_app_inv_2 in HForall23.
    destruct HForall23 as [Ssv [Ss3 [tausv [taus3 [HForallv [HForall3 [-> ->]]]]]]].
    inv HForallv. inv H15.
    assert (is = szs) by (destruct (split tauszs); cbn in *; congruence); subst is.
    destruct H14 as [H100 H14].
    apply Forall2_app_inv_l in H14.
    destruct H14 as [is1 [is23 [Htaus_is1 [Htaus_is23 ->]]]].
    apply Forall2_app_inv_l in Htaus_is23.
    destruct Htaus_is23 as [isv [is3 [Htaus_isv [Htaus_is3 ->]]]].
    inv Htaus_isv. inv H14.
    destruct H10 as [sztau [Hsztau Hleq]].
    specialize (SizeOfType_empty_valid Hsztau).
    intro Hsztau_valid.
    assert (Hy_valid : SizeValid [] y).
    { rewrite Forall_forall in H100.
      eapply H100.
      apply in_or_app.
      right.
      apply in_or_app.
      left.
      constructor; auto. }
    specialize (size_valid_empty_implies_to_nat _ Hsztau_valid).
    intro H200.
    destruct H200 as [nsztau Hnsztau].
    specialize (size_valid_empty_implies_to_nat _ Hy_valid).
    intro H200.
    destruct H200 as [ny Hy].
    destruct Hleq as [Hvalid Hleq].
    apply (SizeLeq_Const _ _ _ _ Hnsztau Hy) in Hleq.
    eapply SizeOfValue_Typecheck_Actual in H11; eauto.
    assert (Hlen_is1 : length is1 = length taus1) by now apply Forall2_length in Htaus_is1.
    assert (sz_slot = y) by (cbn in H4; rewrite <- Hlen_is1, nth_error_app in H4; congruence).
    subst y.
    assert (ny = n_sz_slot) by congruence. subst ny.
    rewrite H11 in *; clear H11. rewrite H2 in *; clear H2.
    apply Forall2_app_inv_r in HHeapType.
    destruct HHeapType as [vs1 [vs23 [HHeapType1 [HHeapType23 ->]]]].
    apply Forall2_app_inv_r in HHeapType23.
    destruct HHeapType23 as [vsv [vs3 [HHeapTypev [HHeapType3 ->]]]].
    inv HHeapTypev. inv H11. destruct H10 as [nsz_slot [Hnsz_slot Hleq_x0]].
    assert (nsz_slot = n_sz_slot) by congruence; subst nsz_slot.
    rewrite !sizes_as_Nat_app.
    assert (sizes_as_Nat [sz_slot] = n_sz_slot) by (cbn; now rewrite Hy).
    enough (
      list_sum (map size_val (firstn (length taus1) (vs1 ++ [x0] ++ vs3))) <= sizes_as_Nat is1 /\
      list_sum (map size_val (skipn (1 + length taus1) (vs1 ++ [x0] ++ vs3))) <= sizes_as_Nat is3) by lia.
    assert (length vs1 = length taus1) by (apply Forall2_length in HHeapType1; lia).
    rewrite firstn_prefix in * by auto.
    assert (Hskip : skipn (1 + length taus1) (vs1 ++ [x0] ++ vs3) = vs3).
    { rewrite skipn_app.
      rewrite skipn_all by lia.
      replace (1 + length taus1 - length vs1) with 1 by lia.
      rewrite skipn_app.
      now cbn. }
    rewrite Hskip in *.
    apply fields_well_sized_totals_well_sized in HHeapType1.
    apply fields_well_sized_totals_well_sized in HHeapType3.
    lia.
  Qed.

  Lemma ctx_app_singleton n ctx e i :
    ctx_app n ctx [e] = [i] ->
    (forall m a es1 es2, i <> Label m a es1 es2) ->
    n = 0 /\ (match ctx with LZero l1 l2 => l1 = [] /\ l2 = [] | _ => True end).
  Proof.
    destruct ctx.
    - cbn; intros H; pose proof H as Hlen.
      apply f_equal with (f := @length _) in Hlen.
      rewrite !app_length in Hlen; cbn in Hlen.
      destruct l, l0 eqn:Hes; cbn in Hlen; try lia.
      intuition lia.
    - cbn; intros H. pose proof H as Hlen.
      apply f_equal with (f := @length _) in Hlen.
      rewrite !app_length in Hlen; cbn in Hlen.
      destruct l, l1; cbn in Hlen; try lia.
      destruct i; (try intuition congruence); cbn in H; inv H.
  Qed.

  Lemma ctx_app_singleton_nil n ctx e :
    ctx_app n ctx [e] <> [].
  Proof.
    destruct ctx; cbn; intros H; pose proof H as Hlen;
    apply f_equal with (f := @length _) in Hlen;
    rewrite !app_length in Hlen; cbn in Hlen;
    destruct l, l0 eqn:Hes; cbn in Hlen; try lia.
  Qed.

  Lemma ctx_app_singleton_label k ctx i tf es1 es2 :
    ctx_app k ctx [Ret] = [Label i tf es1 es2] ->
    match ctx with
    | LZero _ _ => False
    | LSucc_label k' vs i' tf' es1' c es2' =>
      vs = [] /\ es2' = [] /\ i = i' /\ tf = tf' /\ es1 = es1' /\ es2 = ctx_app k' c [Ret]
    end.
  Proof.
    destruct ctx.
    - cbn; intros H; pose proof H as Hlen; apply f_equal with (f := @length _) in Hlen.
      rewrite app_length in Hlen; cbn in Hlen; destruct l, l0; cbn in Hlen; try lia; inv H.
    - cbn; intros H; pose proof H as Hlen; apply f_equal with (f := @length _) in Hlen.
      rewrite app_length in Hlen; cbn in Hlen; destruct l, l1; cbn in Hlen; try lia.
      inv H; easy.
  Qed.

  Lemma ctx_app_cons k ctx e_hole e es :
    ctx_app k ctx [e_hole] = e :: es ->
    match e with
    | term.Val v => e = e_hole \/ exists ctx', ctx_app k ctx' [e_hole] = es
    | _ =>
      match ctx with
      | LZero l r => l = [] /\ e_hole = e
      | LSucc_label k vs i tf es1 c es2 => vs = [] /\ e = Label i tf es1 (ctx_app k c [e_hole]) /\ es = es2
      end
    end.
  Proof.
    destruct ctx.
    - destruct e; try (destruct l; cbn; auto; intuition congruence).
      cbn. destruct l; cbn; [intuition congruence|].
      right; exists (LZero l l0); cbn in *; congruence.
    - destruct e; try (destruct l; cbn; auto; congruence).
      + cbn. destruct l; cbn; [intuition congruence|].
        right; exists (LSucc_label k l n a l0 ctx l1); cbn in *; congruence.
      + cbn; destruct l; cbn; [intuition congruence|].
        intuition congruence.
  Qed.
  
  Definition ctx_cons n v (ctx : context n) :=
    match ctx with
    | LZero l r => LZero (v :: l) r
    | LSucc_label k vs i tf es1 c es2 => LSucc_label k (v :: vs) i tf es1 c es2
    end.

  Lemma ctx_cons_spec n v (ctx : context n) es :
    ctx_app n (ctx_cons n v ctx) es = Val v :: ctx_app n ctx es.
  Proof. destruct ctx; reflexivity. Qed.
  
  Lemma ctx_app_singleton_app n (ctx : context n) es1 es2 e :
    match e with Label _ _ _ _ => False | _ => True end ->
    es1 ++ es2 = ctx_app n ctx [e] ->
    (exists n ctx, es1 = ctx_app n ctx [e]) \/ (exists n ctx, es2 = ctx_app n ctx [e]).
  Proof.
    revert n ctx; induction es1.
    - right; eauto.
    - intros* He H; symmetry in H; apply ctx_app_cons in H.
      destruct a; try solve
       [destruct ctx; intuition eauto; subst; try congruence;
        try match goal with
        | |- (exists n ctx, ?e :: ?es = ctx |[ [?e] ]|) \/ _ =>
          left; exists 0, (LZero [] es); reflexivity
        end].
      + destruct H; [subst; left; exists 0, (LZero [] es1); reflexivity|].
        destruct H as [ctx' Hctx']. symmetry in Hctx'. apply IHes1 in Hctx'; auto.
        destruct Hctx' as [Hctx'|Hctx']; destruct Hctx' as [n' [ctx'' Hctx'']]; [left|right; eauto].
        exists n', (ctx_cons n' v ctx''); rewrite ctx_cons_spec; now f_equal.
      + destruct ctx.
        * destruct H; subst. left. exists 0, (LZero [] es1). reflexivity.
        * intuition eauto; subst; inv H; destruct e; try solve [inversion He];
          match goal with
          | |- (exists n ctx, Label ?n' ?a ?l1 (?ctx' |[ [?e] ]|) :: ?es = ctx |[ [?e] ]|) \/ _ =>
            left; exists (1 + k), (LSucc_label k [] n' a l1 ctx es); reflexivity
          end.
  Qed.
  
  Lemma ret_in_hole_F_nonempty S C F L tf L' n ctx :
    HasTypeInstruction S C F L (ctx_app n ctx [Ret]) tf L' ->
    ret F <> None.
  Proof.
    remember (ctx |[ [Ret] ]|) as ctxret.
    intros H; revert n ctx Heqctxret.
    induction H; subst; intros.
    (* Most cases easy because have equation like ctx |[ [Ret] ]| = [some instruction that isn't Ret] *)
    all: try match goal with
    | H : [_] = ?ctx |[ _ ]| |- _ =>
      let H' := fresh in
      pose proof H as H';
      symmetry in H'; apply ctx_app_singleton in H'; [|congruence];
      destruct ctx; [|lia]; destruct H' as [? [? ?]]; subst; cbn in H; inversion H
    end.
    - (* found Ret! F not none by assumption *) intros wat; congruence.
    - (* ctx could be nonempty, in which case we have es2 = ctx' |[ [Ret] ]| for some ctx'
         and have that F is nonempty by IH on subterm es2 *)
      match goal with
      | H : [Label _ _ _ _] = ctx |[ _ ]| |- _ => 
        symmetry in H; apply ctx_app_singleton_label in H; destruct ctx; [easy|];
        decompose [Logic.and] H; subst
      end.
      destruct F; cbn in *; eapply IHHasTypeInstruction1; eauto.
    - exfalso; eapply ctx_app_singleton_nil; eauto.
    - (* ret is in es0 or in e. need IH at smaller list of instructions *)
      apply ctx_app_singleton_app in Heqctxret; try exact I.
      destruct Heqctxret as [Hctx|Hctx]; destruct Hctx as [n' [ctx' Hctx']]; firstorder.
    - (* frame rule *) subst F'; destruct F; cbn in *; eauto.
    - eauto.
    - eauto.
  Qed.
  
  Lemma not_ret_in_hole_empty_ctx : forall S C L L' tf es,
      HasTypeInstruction S C empty_Function_Ctx L es tf L' ->
      (forall n ctx, ~ (ctx_app n ctx [Ret] = es)).
  Proof.
    intros* Hty n ctx <-. apply ret_in_hole_F_nonempty in Hty. now apply Hty.
  Qed.

  Lemma not_ret_in_hole_empty_ctx_conf : forall S i vs szs es taus,
      HasTypeConf S None i vs szs es taus ->
      (forall n ctx, ~ (ctx_app n ctx [Ret] = es)).
  Proof.
    intros.
    invert H.
    simpl in F.
    unfold F in H5.
    eapply not_ret_in_hole_empty_ctx in H5.
    exact H5.
  Qed.

  Lemma br_in_hole_implies_depth_instr S C F L es t L' n ctx k :
    HasTypeInstruction S C F L es t L' ->
    es = ctx_app n ctx [Br k] ->
    qual F = [] ->
    k < n + length (label F).
  Proof.
    revert S C F L es t L' k; induction ctx as [vs es'|k' vs i tf es1 ctx IHctx es2];
    intros S C F L es t L' k.
    - cbn; intros Hty ->; destruct t as [taus1' taus2'].
      apply composition_typing in Hty.
      destruct Hty as [frame [taus1 [taus3' [taus2'' [Lvs [qf stuff]]]]]].
      destruct stuff as [Svs [Srest [-> [-> [Hframe [Hleq [Hqual1 [Hqual2 [Hvs [Hbres HS]]]]]]]]]].
      change (?x :: ?xs) with ([x] ++ xs) in Hbres.
      apply composition_typing in Hbres.
      destruct Hbres as [frame' [taus2 [taus3 [taus23 [Lbr [qbr stuff]]]]]].
      destruct stuff as [Sbr [Srest' [-> [-> [Hframe' [Hleq' [Hqual1' [Hqual2' [Hbr [Hes HSrest]]]]]]]]]].
      intros.
      apply Br_HasTypeInstruction in Hbr.
      2:{
        destruct F; cbn in *; auto.
      }
      destructAll.
      intros.
      destruct F; cbn in *.
      eapply nth_error_Some_length; eauto.
    - cbn; intros Hty ->; destruct t as [taus1' taus2'].
      intros.
      apply composition_typing in Hty.
      destruct Hty as [frame [taus1 [taus3' [taus2'' [Lvs [qf stuff]]]]]].
      destruct stuff as [Svs [Srest [-> [-> [Hframe [Hleq [Hqual1 [Hqual2 [Hvs [Hlabeles HS]]]]]]]]]].
      change (?x :: ?xs) with ([x] ++ xs) in Hlabeles.
      apply composition_typing in Hlabeles.
      destruct Hlabeles as [frame' [taus2 [taus3 [taus23 [Lbr [qbr stuff]]]]]].
      destruct stuff as [Sbr [Srest' [-> [-> [Hframe' [Hleq' [Hqual1' [Hqual2' [Hlabel [Hes HSrest]]]]]]]]]].
      apply Label_HasTypeInstruction in Hlabel.
      destructAll; lazy zeta in *; destructAll.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (ctx |[ [Br k] ]|) _ _ |- _ =>
        eapply IHctx in H; [|reflexivity|]
      end.
      -- destruct F; cbn in *. lia.
      -- destruct F; cbn in *; auto.
  Qed.
  
  Lemma br_in_hole_implies_depth_conf : forall S taus1 i vs szs es taus2,
      HasTypeConf S taus1 i vs szs es taus2 ->
      (forall n ctx k, (ctx_app n ctx [Br k] = es) -> k < n).
  Proof.
    intros* H; inv H; intros n ctx k Hctx.
    match goal with
    | H : HasTypeInstruction _ _ _ _ _ _ _ |- _ => 
      eapply br_in_hole_implies_depth_instr in H; eauto; cbn in *; lia
    end.
  Qed.
  
  Lemma ret_hole_excluded_middle : forall es,
      (exists n ctx, ctx_app n ctx [Ret] = es) \/ ~ (exists n ctx, ctx_app n ctx [Ret] = es).
  Proof. intros; apply LEM. Qed.

  Lemma br_hole_excluded_middle : forall es,
      (exists n ctx, ctx_app n ctx [Br n] = es) \/ ~ (exists n ctx, ctx_app n ctx [Br n] = es).
  Proof. intros; apply LEM. Qed.
  
  (* TODO move *)
  Lemma Forall3_skipn n {A B C} (R : A -> B -> C -> Prop) xs ys zs :
    Forall3 R xs ys zs ->
    Forall3 R (skipn n xs) (skipn n ys) (skipn n zs).
  Proof.
    intros H; revert n; induction H; [destruct n; constructor|].
    destruct n; cbn in *; [constructor; auto|]; auto.
  Qed.

  Lemma return_reduce_extract_vs : forall n ctx es S C F L L' taus1 taus2,
    ctx_app n ctx [Ret] = es ->
    HasTypeInstruction S C F L es (Arrow [] taus1) L' ->
    ret F = Some taus2 ->
    qual F = [] ->
    exists vs ctx',
      ctx_app n ctx' (map Val vs ++ [Ret]) = es /\ length vs = length taus2.
  Proof.
    (* proof should be similar to br_reduce_extract_vs below *)
    induction ctx as [vs es'|k' vs i tf es1 ctx IHctx es2].
    - cbn; intros* <- Hty Hnth.
      apply composition_typing in Hty. lazy zeta in *; destructAll.
      match goal with
      | H : [] = ?xs ++ ?ys |- _ =>
        destruct xs, ys; [clear H|cbn in H; congruence..]
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (_ :: _) _ _ |- _ =>
        change (?x :: ?xs) with ([x] ++ xs) in H;
        apply composition_typing in H;
        lazy zeta in *; destructAll
      end.
      intros.
      match goal with
      | H : HasTypeInstruction _ _ _ _ [Ret] _ _ |- _ =>
        apply Ret_HasTypeInstruction in H; destructAll
      end.
      2:{
        destruct F; cbn in *; auto.
      }
      match goal with
      | H1 : ret _ = Some ?v1, H2 : ret F = Some ?v2 |- _ =>
        let Heq := fresh in
        assert (Heq : v1 = v2) by (clear - H1 H2; destruct F; cbn in *; congruence);
        inv Heq
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (map term.Val _) _ _ |- _ =>
        unshelve eapply Values_HasTypeInstruction in H;
        [apply values_val_map|]; rewrite to_values_Val in *;
        destructAll; cbn in *; subst
      end.
      match goal with
      | H : Forall3 _ ?S vs (?ts1 ++ ?ts2 ++ ?ts3 ++ taus2) |- _ =>
        exists (skipn (length (ts1 ++ ts2 ++ ts3)) vs), (LZero (firstn (length (ts1 ++ ts2 ++ ts3)) vs) es');
        apply (Forall3_skipn (length (ts1 ++ ts2 ++ ts3))) in H;
        apply Forall3_length in H;
        rewrite !app_assoc, skipn_app in H;
        rewrite Nat.sub_diag in H; cbn in H;
        rewrite !app_length, !skipn_length, !app_length in *
      end.
      split; [|lia].
      cbn; rewrite !app_assoc, <- map_app, firstn_skipn, <- app_assoc; split; auto.
    - intros* Hes Hty Hnth. intros. cbn in *; subst es.
      apply composition_typing in Hty; lazy zeta in *; destructAll.
      match goal with
      | H : [] = ?xs ++ ?ys |- _ =>
        destruct xs, ys; [clear H|cbn in H; congruence..]
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (_ :: _) _ _ |- _ =>
        change (?x :: ?xs) with ([x] ++ xs) in H;
        apply composition_typing in H;
        lazy zeta in *; destructAll
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ [Label _ _ _ _] _ _ |- _ =>
        apply Label_HasTypeInstruction in H; lazy zeta in *; destructAll
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (ctx |[ [Ret] ]|) _ _ |- _ =>
        eapply IHctx in H; (try reflexivity); [|destruct F; cbn in *; now eauto|];
        [destruct H as [ihvs [ihctx [<- Hihvs]]] | ]
      end.
      -- exists ihvs; unshelve eexists; [apply LSucc_label|split]; try reflexivity; auto.
      -- destruct F; cbn in *; auto.
  Qed.
  
  Lemma br_reduce_extract_vs : forall n ctx es S C F L L' taus1 taus2 L'' k,
    ctx_app n ctx [Br (n + k)] = es ->
    HasTypeInstruction S C F L es (Arrow [] taus1) L' ->
    nth_error (label F) k = Some (taus2, L'') ->
    qual F = [] ->
    exists vs ctx',
      ctx_app n ctx' (map Val vs ++ [Br (n + k)]) = es /\ length vs = length taus2.
  Proof.
    induction ctx as [vs es'|k' vs i tf es1 ctx IHctx es2].
    - cbn; intros* <- Hty Hnth. intros.
      apply composition_typing in Hty. lazy zeta in *; destructAll.
      match goal with
      | H : [] = ?xs ++ ?ys |- _ =>
        destruct xs, ys; [clear H|cbn in H; congruence..]
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (_ :: _) _ _ |- _ =>
        change (?x :: ?xs) with ([x] ++ xs) in H;
        apply composition_typing in H;
        lazy zeta in *; destructAll
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ [Br k] _ _ |- _ =>
        apply Br_HasTypeInstruction in H; destructAll
      end.
      2:{
        destruct F; cbn in *; auto.
      }
      match goal with
      | H1 : nth_error _ k = Some ?v1, H2 : nth_error (label ?F) k = Some ?v2 |- _ =>
        let Heq := fresh in
        assert (Heq : v1 = v2) by (clear - H1 H2; destruct F; cbn in *; congruence);
        inv Heq
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (map term.Val _) _ _ |- _ =>
        unshelve eapply Values_HasTypeInstruction in H;
        [apply values_val_map|]; rewrite to_values_Val in *;
        destructAll; cbn in *; subst
      end.
      match goal with
      | H : Forall3 _ ?S vs (?ts1 ++ ?ts2 ++ ?ts3 ++ taus2) |- _ =>
        exists (skipn (length (ts1 ++ ts2 ++ ts3)) vs), (LZero (firstn (length (ts1 ++ ts2 ++ ts3)) vs) es');
        apply (Forall3_skipn (length (ts1 ++ ts2 ++ ts3))) in H;
        apply Forall3_length in H;
        rewrite app_assoc, skipn_app in H; cbn in H;
        rewrite !app_length, !skipn_length, !app_length in *
      end.
      split; [|lia].
      cbn; rewrite !app_assoc, <- map_app, firstn_skipn, <- app_assoc; split; auto.
    - intros* Hes Hty Hnth. intros. cbn in *; subst es.
      replace (Datatypes.S (k' + k)) with (k' + (Datatypes.S k)) in * by lia.
      apply composition_typing in Hty; lazy zeta in *; destructAll.
      match goal with
      | H : [] = ?xs ++ ?ys |- _ =>
        destruct xs, ys; [clear H|cbn in H; congruence..]
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (_ :: _) _ _ |- _ =>
        change (?x :: ?xs) with ([x] ++ xs) in H;
        apply composition_typing in H;
        lazy zeta in *; destructAll
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ [Label _ _ _ _] _ _ |- _ =>
        apply Label_HasTypeInstruction in H; lazy zeta in *; destructAll
      end.
      match goal with
      | H : HasTypeInstruction _ _ _ _ (ctx |[ [Br _] ]|) _ _ |- _ =>
        eapply IHctx in H; (try reflexivity); [|destruct F; cbn in *; now eauto|];
        [destruct H as [ihvs [ihctx [<- Hihvs]]] | ]
      end.
      -- exists ihvs; unshelve eexists; [apply LSucc_label|split]; try reflexivity; auto.
      -- destruct F; cbn in *; auto.
  Qed.
  
  Lemma HasTypeStore_weakening : forall s Sh S_rest S_whole,
      SplitStoreTypings [S_rest; Sh] S_whole ->
      HasTypeStore s Sh S_rest ->
      typing_valid S_rest Sh s.
  Proof.
    intros*; intros Hsplit H; inv H. inv H2.
    unfold typing_valid.
    intros l ht; split; intros Hget.
    - assert (l_in_s : l \in MemUtils.dom_lin (meminst s)).
      { apply H; right; exists ht; apply Hget. }
      destruct l_in_s as [[hv n] Hhvn].
      assert (lhvn_in_s : exists i, nth_error (to_list Linear (meminst s)) i = Some (l, hv, n)).
      { eapply get_implies_in_to_list; eauto. }
      destruct lhvn_in_s as [i Hi].
      eapply Forall2_nth_error in Hi; eauto.
      cbn in Hi. destruct Hi as [S'' [HS [ht' [Hnc [Hht' [Hty [Hroom Hvalid]]]]]]].
      apply nth_error_split in HS; destruct HS as [S_lin1 [S_lin2 [HS_lin12 Hlen_lin1]]].
      subst S_lin; rewrite <- app_assoc in H4; apply SplitStoreTypings_comm' in H4.
      rewrite <- !app_assoc in H4; cbn in H4.
      change (?x :: ?xs) with ([x] ++ xs) in H4.
      apply SplitStoreTypings_comm' in H4.
      apply SplitStoreTyping_app in H4; destruct H4 as [S' [HS' HSh]].
      apply SplitStoreTypings_comm in HSh.
      exists hv, n, S'', S'.
      destruct Hht'; [|intuition congruence].
      clear - Hsplit Hget H2.
      apply SplitStoreTypings_cons_Disjoint in Hsplit.
      destruct Hsplit as [Hsplit]; contradiction (Hsplit l).
      constructor; [now exists ht|exists ht'].
      cbn; unfold union; rewrite M.gmap2 by auto; unfold map_util.get_heaptype in *; now rewrite H2.
    - assert (l_in_s : l \in MemUtils.dom_unr (meminst s)).
      { apply H3; right; exists ht; apply Hget. }
      destruct l_in_s as [[hv n] Hhvn].
      assert (lhvn_in_s : exists i, nth_error (to_list Unrestricted (meminst s)) i = Some (l, hv, n)).
      { eapply get_implies_in_to_list; eauto. }
      destruct lhvn_in_s as [i Hi].
      eapply Forall2_nth_error in Hi; eauto.
      cbn in Hi. destruct Hi as [S'' [HS [ht' [Hht' [Hty [Hroom Hvalid]]]]]].
      apply nth_error_split in HS; destruct HS as [S_unr1 [S_unr2 [HS_unr12 Hlen_unr1]]].
      subst S_unr. rewrite app_assoc in H4; apply SplitStoreTypings_comm' in H4.
      cbn in H4. change (?x :: ?xs) with ([x] ++ xs) in H4.
      apply SplitStoreTypings_comm' in H4.
      apply SplitStoreTyping_app in H4; destruct H4 as [S' [HS' HSh]].
      apply SplitStoreTypings_comm in HSh.
      exists hv, n, S'', S'.
      pose proof HSh as HInstUnrS.
      apply SplitStoreTypings_cons_InstUnr in HInstUnrS.
      pose proof Hsplit as HInstUnrSh.
      pose proof Hsplit as HInstUnrS_rest.
      apply SplitStoreTypings_cons_InstUnr in HInstUnrS_rest.
      apply SplitStoreTypings_comm in HInstUnrSh.
      apply SplitStoreTypings_cons_InstUnr in HInstUnrSh.
      assert (UnrTyp S_rest = UnrTyp S'') by intuition congruence.
      intuition congruence.
  Qed.

  Lemma no_ret_in_hole_label_extend : forall (tau1 : list Typ) taus2 es1 es2,
    (forall (n : nat) (ctx : context n),
        ctx |[ [Ret] ]| <> [Label (length tau1) (Arrow [] taus2) es1 es2]) ->
    (forall (n : nat) (ctx : context n), ctx |[ [Ret] ]| <> es2).
  Proof.
    intros* Hlabel n ctx Hes2.
    unshelve eapply Hlabel; [|eapply (LSucc_label n [])|]; cbn; rewrite ?Hes2; try reflexivity.
  Qed.

  Lemma br_in_hole_extend : forall n (ctx : context n) k (tau1 : list Typ) taus2 es1 es2,
      (forall (n : nat) (ctx : context n) (k : nat),
          ctx |[ [Br k] ]| = [Label (length tau1) (Arrow [] taus2) es1 es2] -> k < n) ->
      ~ (exists (n : nat) (ctx : context n), ctx |[ [Br n] ]| = es2) ->
      ctx |[ [Br k] ]| = es2 -> k < n.
  Proof.
    intros* Hlabel Hes2; intros <-.
    specialize (Hlabel _ (LSucc_label n [] (length tau1) (Arrow [] taus2) es1 ctx []) k eq_refl).
    enough (k <> n) by lia.
    intros H; subst; contradiction Hes2; eauto.
  Qed.

  Definition ctx_snoc n e (ctx : context n) :=
    match ctx with
    | LZero l r => LZero l (r ++ [e])
    | LSucc_label k vs i tf es1 c es2 => LSucc_label k vs i tf es1 c (es2 ++ [e])
    end.

  Lemma ctx_snoc_spec n e (ctx : context n) es :
    ctx_app n (ctx_snoc n e ctx) es = ctx_app n ctx es ++ [e].
  Proof. destruct ctx; cbn; rewrite <- !app_assoc; reflexivity. Qed.
  
  Lemma sequence_ret_not_in_hole_l : forall es e,
      (forall (n : nat) (ctx : context n), ctx |[ [Ret] ]| <> es ++ [e]) ->
      (forall (n : nat) (ctx : context n), ctx |[ [Ret] ]| <> es).
  Proof.
    intros* Hret n ctx Hctx.
    apply (Hret n (ctx_snoc n e ctx)). rewrite ctx_snoc_spec; congruence.
  Qed.

  Lemma sequence_br_not_in_hole_l : forall es e,
      (forall (n : nat) (ctx : context n) (k : nat), ctx |[ [Br k] ]| = es ++ [e] -> k < n) ->
      (forall (n : nat) (ctx : context n) (k : nat), ctx |[ [Br k] ]| = es -> k < n).
  Proof.
    intros* Hctx n ctx k Heq.
    apply (Hctx n (ctx_snoc n e ctx)).
    rewrite ctx_snoc_spec; congruence.
  Qed.

  Fixpoint ctx_add_prefix n vs (ctx : context n) :=
    match vs with
    | [] => ctx
    | v :: vs => ctx_cons n v (ctx_add_prefix n vs ctx)
    end.

  Lemma ctx_add_prefix_spec n vs (ctx : context n) es :
    ctx_app n (ctx_add_prefix n vs ctx) es = map Val vs ++ ctx_app n ctx es.
  Proof. induction vs; [reflexivity|cbn; rewrite ctx_cons_spec; congruence]. Qed.
  
  Lemma sequence_ret_not_in_hole_r : forall vs e,
      (forall (n : nat) (ctx : context n), ctx |[ [Ret] ]| <> (map Val vs) ++ [e]) ->
      (forall (n : nat) (ctx : context n), ctx |[ [Ret] ]| <> [e]).
  Proof.
    intros* Hctx n ctx Heq.
    apply (Hctx n (ctx_add_prefix n vs ctx)).
    rewrite ctx_add_prefix_spec; congruence.
  Qed.

  Lemma sequence_br_not_in_hole_r : forall vs e,
      (forall (n : nat) (ctx : context n) (k : nat), ctx |[ [Br k] ]| = (map Val vs) ++ [e] -> k < n) ->
      (forall (n : nat) (ctx : context n) (k : nat), ctx |[ [Br k] ]| = [e] -> k < n).
  Proof.
    intros* Hctx n ctx k Heq.
    apply (Hctx n (ctx_add_prefix n vs ctx) k).
    rewrite ctx_add_prefix_spec; congruence.
  Qed.

  Lemma HasTypeInstance_SplitStoreTypings : forall S_1 S_2 S S' s,
    SplitStoreTypings ((S_1 ++ [S']) ++ S_2) S ->
    Forall2 (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp S) i C)
          (inst s) (InstTyp S') ->
    Forall2 (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp S') i C)
          (inst s) (InstTyp S').
  Proof.
    intros* Hsplit Hforall.
    rewrite <- app_assoc in Hsplit.
    apply SplitStoreTypings_comm' in Hsplit.
    apply SplitStoreTypings_cons_InstTyp in Hsplit.
    eapply Forall2_monotonic; try apply Hforall; cbn; intuition congruence.
  Qed.

  Lemma size_consts_are_sizes : forall sz_ns, (forall i sz, nth_error (map SizeConst sz_ns) i = Some sz -> sigT (fun n => size_to_nat sz = Some n /\ nth_error sz_ns i = Some n)).
  Proof.
    induction sz_ns; simpl; intros.
    - rewrite (nth_error_nil _ i) in H; discriminate.
    - revert H; case i; intros.
      + simpl in H.
        simpl.
        invert H.
        exists a.
        eauto.
      + simpl in H.
        exact (IHsz_ns n sz H).
  Qed.

  Lemma size_consts_hide : forall sz_ns, exists szs, (map SizeConst sz_ns) = szs.
  Proof. eauto. Qed.

  Lemma nat_n_swap : forall n n', n <= N.to_nat n' -> (N.of_nat n <= n')%N.
  Proof. lia. Qed.

  Lemma n_nat_swap : forall n n', (N.of_nat n <= n')%N -> n <= N.to_nat n'.
  Proof. lia. Qed.


  Lemma fold_is_size_as_nat : forall szs n,
              (fold_left (fun (acc : N) (sz : Size) => match size_to_nat sz with | Some n => acc + N.of_nat n | None => acc end) szs 0 <= n)%N ->
              sizes_as_Nat szs <= N.to_nat n.
  Proof.
    intros.
    (*assert ((N.of_nat 0) = (N.of_nat (0 + 0))) by lia. 
    rewrite H0 in H.
    clear H0. *)
    revert H.
    assert ((N.of_nat 0) = 0%N) by lia.
    rewrite<- H.
    clear H.
    unfold sizes_as_Nat.
    generalize 0.
    revert n.
    induction szs; intros.
    - simpl. simpl in H.
      lia.
    - simpl in H.
      simpl.
      destruct (size_to_nat a); try (eapply IHszs in H; now eauto).
      assert ((N.of_nat n0 + N.of_nat n1)%N = (N.of_nat (n0 + n1))) by lia.
      rewrite H0 in H.
      eapply IHszs in H.
      eassumption.
  Qed.

  Lemma InstInds_None_None is :
    fold_left (fun ft0 i => match ft0 with Some ft1 => InstInd ft1 i | None => None end) is None = None.
    induction is; eauto.
  Qed.

  Lemma inst_size_is_closed_gen : forall {idxs kvs atyp atyp' sz},
      SizeValid (size (add_constraints empty_Function_Ctx kvs)) sz ->
      InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp') ->
      InstIndsValid empty_Function_Ctx (FunT kvs atyp) idxs ->
      SizeValid [] (subst.subst_indices idxs sz).
  Proof.
    apply
      (rev_ind
         (fun idxs =>
            forall kvs atyp atyp' sz,
              SizeValid (size (add_constraints empty_Function_Ctx kvs)) sz ->
              InstInds (FunT kvs atyp) idxs = Some (FunT [] atyp') ->
              InstIndsValid empty_Function_Ctx (FunT kvs atyp) idxs ->
              SizeValid [] (subst.subst_indices idxs sz))).
    all: intros; simpl in *.
    - unfold InstInds in *.
      simpl in *.
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; simpl in *; auto
      end.
    - match goal with
      | [ H : InstInds _ (_ ++ [_]) = Some _ |- _ ] =>
        specialize (InstInds_snoc_inv_to_empty H)
      end.
      intros; destructAll.
      match goal with
      | [ H : context[add_constraints empty_Function_Ctx _] |- _ ] =>
        rewrite add_constraints_to_ks_of_kvs in H; simpl in H;
        rewrite collect_szctx_snoc in H; rewrite app_nil_r in H
      end.
      rewrite subst_indices_snoc_size.
      match goal with
      | [ H : context[InstInd (FunT [_] _)] |- _ ] =>
        specialize (H (Arrow [] []))
      end.
      destructAll.
      match goal with
      | [ H : forall _ _ _ _, _,
          H' : context[collect_szctx ?KVS] |- _ ] =>
        specialize (H KVS)
      end.
      match goal with
      | [ H : InstInd (FunT [?KV] _) ?IDX = Some _ |- _ ] =>
        destruct KV; destruct IDX; simpl in *
      end.
      all:
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        | [ H : Some _ = Some _ |- _ ] => inversion H; subst
        end.
      1-2,4: erewrite size_debruijn_subst_ext.
      all: try apply simpl_debruijn_subst_ext_conds; solve_ineqs.
      all:
        match goal with
        | [ H : forall _, exists _, _ |- _ ] =>
          specialize (H (Arrow [] [])); destructAll
        end.
      all:
        match goal with
        | [ H : forall _ _ _, _ |- _ ] =>
          eapply H
        end.
      all: try rewrite add_constraints_to_ks_of_kvs; simpl.
      all: try rewrite app_nil_r.
      all: eauto.

      all: try eapply InstIndsValid_remove_snoc.
      all: try eapply InstIndsValid_Function_Ctx_stronger; eauto.
      
      eapply SizeValid_subst_ind; eauto.
      -- eapply SizeValid_length; eauto.
         simpl.
         rewrite map_length; auto.
      -- apply in_snoc.

    Unshelve.
    repeat constructor.
  Qed.

  Lemma SizeValid_empty_imp_closed : forall {sz},
      SizeValid [] sz -> size_closed sz.
  Proof.
    induction sz; intro H; inversion H; subst;
      match goal with
      | [ H : @Logic.eq Size _ _ |- _ ] =>
        inversion H; subst; simpl in *; eauto
      end.
    match goal with
    | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
      destruct IDX; simpl in *; inversion H
    end.
  Qed.
  
  Lemma inst_sizes_is_closed is taus0 taus1 taus2 taus3 sz0 cnstr :
    let chi0 := FunT cnstr (Arrow taus0 taus3) in
    let F_cnstr := add_constraints empty_Function_Ctx cnstr in
    let F1 := update_ret_ctx (Some taus3) F_cnstr in
    Forall (fun sz : Size => SizeValid (size F1) sz) sz0 ->
    InstInds chi0 is = Some (FunT [] (Arrow taus1 taus2)) ->
    InstIndsValid empty_Function_Ctx chi0 is ->
    sizes_closed (subst_in_size is sz0).
  Proof.
    rewrite subst_in_size_eq_map; simpl.
    intros.
    unfold sizes_closed.
    rewrite Forall_forall.
    intros.
    apply SizeValid_empty_imp_closed.
    rewrite in_map_iff in *.
    destructAll.
    match goal with
    | [ H : Forall _ ?L, H' : List.In _ ?L |- _ ] =>
      rewrite Forall_forall in H;
      specialize (H _ H'); rewrite update_ret_ctx_size in H
    end.
    eapply inst_size_is_closed_gen; eauto.
  Qed.

  Lemma LCEffEqual_Forall3_arg3 : forall {A B C L1 L2 P} {l1 : list A} {l2 : list B},
      LCEffEqual C L1 L2 ->
      Forall3 P l1 l2 L1 ->
      (forall x y t sz1 sz2,
          P x y (t, sz1) ->
          SizeLeq C sz1 sz2 = Some true ->
          SizeLeq C sz2 sz1 = Some true ->
          P x y (t, sz2)) ->
      Forall3 P l1 l2 L2.
  Proof.
    intros.
    rewrite Forall3_forall.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] => rewrite Forall3_forall in H
    end.
    destructAll.
    split.
    2:{
      split; auto.
      eapply eq_trans; eauto.
      eapply LCEffEqual_length; eauto.
    }
    intros.
    destruct_prs.
    use_LCEffEqual_nth_error_right.
    match goal with
    | [ H : forall _ _ _ _,
          nth_error ?L1 _ = Some _ ->
          nth_error ?L2 _ = Some _ ->
          nth_error ?L3 _ = Some _ -> _,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _,
        H''' : nth_error ?L3 _ = Some _ |- _ ] =>
      specialize (H _ _ _ _ H' H'' H''')
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
  Qed.

  Lemma SizeLeq_right_closed_imp_left_closed_sigT : forall sz1 sz2 c2,
      size_to_nat sz2 = Some c2 ->
      SizeLeq [] sz1 sz2 = Some true ->
      {c1 &
       size_to_nat sz1 = Some c1}.
  Proof.
    intros.
    remember (size_to_nat sz1) as obj.
    generalize (eq_sym Heqobj); case obj; intros.
    - eexists; eauto.
    - specialize (SizeLeq_right_closed_imp_left_closed _ _ _ H H0).
      intros.
      rewrite H1 in H2.
      exfalso.
      destructAll.
      inversion H2.
  Qed.

  Lemma LCEffEqual_nth_error_left_sigT : forall {C L L' idx tau sz},
      LCEffEqual C L L' ->
      nth_error L idx = Some (tau, sz) ->
      {sz' &
        nth_error L' idx = Some (tau, sz') /\
        SizeLeq C sz sz' = Some true /\
        SizeLeq C sz' sz = Some true}.
  Proof.
    intros.
    remember (nth_error L' idx) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    - destruct_prs.
      unfold LCEffEqual in *.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      intros; simpl in *.
      destructAll.
      eexists; eauto.
    - specialize (LCEffEqual_nth_error_left H H0).
      intros.
      rewrite H1 in H2.
      exfalso.
      destructAll.
      inversion H2.
  Qed.

  Lemma LCEffEqual_nth_error_right_sigT : forall {C L L' idx tau sz},
      LCEffEqual C  L L' ->
      nth_error L' idx = Some (tau, sz) ->
      {sz' &
        nth_error L idx = Some (tau, sz') /\
        SizeLeq C sz sz' = Some true /\
        SizeLeq C sz' sz = Some true}.
  Proof.
    intros.
    remember (nth_error L idx) as obj.
    generalize (eq_sym Heqobj).
    case obj; intros.
    - destruct_prs.
      unfold LCEffEqual in *.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      intros; simpl in *.
      destructAll.
      eexists; eauto.
    - specialize (LCEffEqual_nth_error_right H H0).
      intros.
      rewrite H1 in H2.
      exfalso.
      destructAll.
      inversion H2.
  Qed.

  Definition Progress_HasTypeInstruction_mind S_stack M F L es tf L' (H : HasTypeInstruction S_stack M F L es tf L') :=
    forall i vs locs s locszs taus1 taus2 S_values S_locals S_heap S_rest S_whole,
      tf = (Arrow taus1 taus2) ->
      SplitStoreTypings ((S_values ++ [S_stack]) ++ S_locals) S_rest ->
      Forall3 (fun S' v t => HasTypeValue S' F v t) S_values vs taus1 ->
      Forall3 (fun S' v '(t, _) => HasTypeValue S' F v t) S_locals locs L ->
      nth_error (InstTyp S_rest) i = Some M ->
      (typing_valid S_rest S_heap s /\
       Forall2
         (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp S_rest) i C)
         (inst s) (InstTyp S_rest)) ->
      (qual F) = [] ->
      (typing.size F) = [] ->
      (type F) = [] ->
      Forall (fun S' : StoreTyping => InstTyp S_whole = InstTyp S' /\ UnrTyp S_whole = UnrTyp S') [S_rest; S_heap] ->
      (forall n ctx, ~ (ctx_app n ctx [Ret] = es)) ->
      (forall n ctx k, (ctx_app n ctx [Br k] = es) -> k < n) ->
      (forall i sz typ, nth_error L i = Some (typ, sz) -> sigT (fun n => size_to_nat sz = Some n /\ nth_error locszs i = Some n)) ->
      location F = 0 ->
      Forall (fun e : Instruction => exists v : Value, e = Val v) es \/
      es = [Trap] \/
      (exists (s' : Store) (locs' vs' : list Value) (es' : list Instruction),
          Reduce s locs locszs (map Val vs ++ es) i s' locs' (map Val vs' ++ es')).
  Definition Progress_HasTypeClosure_mind S C F (H : HasTypeClosure S C F) := True.
  Definition Progress_HasTypeFunc_mind S M f ex chi (H : HasTypeFunc S M f ex chi) := True.
  Definition Progress_HasTypeConf_mind S_rest ret i vlocs szs es taus (H : HasTypeConf S_rest ret i vlocs szs es taus) :=
    ret = None \/ ret = Some taus ->
    forall (s : Store) sz_ns S_heap S,
      (forall i sz, nth_error szs i = Some sz -> sigT (fun n => size_to_nat sz = Some n /\ nth_error sz_ns i = Some n)) ->
      Forall (fun S' : StoreTyping => InstTyp S = InstTyp S' /\ UnrTyp S = UnrTyp S') [S_rest; S_heap] ->
      (typing_valid S_rest S_heap s /\
       Forall2
         (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp S_rest) i C)
         (inst s) (InstTyp S_rest)) ->
      (forall n ctx, ~ (ctx_app n ctx [Ret] = es)) ->
      (forall n ctx k, (ctx_app n ctx [Br k] = es) -> k < n) ->
      Forall (fun e : Instruction => exists v : Value, e = Val v) es \/
      es = [Trap] \/
      (exists (s' : Store) (locs' : list Value) (es' : list Instruction),
          Reduce s vlocs sz_ns es i s' locs' es').

  Theorem Progress :
    forall S i s locs sz_ns es taus,
      HasTypeConfig S i s locs sz_ns es taus ->
      Forall (fun e => exists v, e = Val v) es \/
      es = [Trap] \/
      exists s' locs' es', Reduce s locs sz_ns es i s' locs' es'.
    Proof.
      intros.
      invert H. clear H.
      assert (Heq : @None (list Typ) = None) by reflexivity.
      assert (H4 := not_ret_in_hole_empty_ctx_conf _ _ _ _ _ _ H2).
      assert (H5 := br_in_hole_implies_depth_conf _ _ _ _ _ _ _ H2).
      revert H5.
      revert H4.
      invert H1.
      rewrite<- (SplitStoreTypings_cons_InstTyp _ _ _ H) in H3.
      assert (H5 := HasTypeStore_weakening _ _ _ _ H0 H1).
      assert (H6 : typing_valid Sprog Sh s /\ Forall2 (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp Sprog) i C) (inst s) (InstTyp Sprog)) by eauto.
      invert H.
      clear H8 H5 H4 H H1 H0 S H3.
      assert (HConst := size_consts_are_sizes sz_ns).
      destruct (size_consts_hide sz_ns) as [sz Hremember].
      rewrite Hremember in H2, HConst.
      clear Hremember.
      revert H2 Heq s sz_ns Sh S0 HConst H7 H6.
      generalize (@None (list Typ)) at 1 2.
      intros ret Htyp Hret.
      assert (Hor : ret = None \/ ret = Some taus); eauto.
      revert Hor.
      clear Hret.
      eapply HasTypeConf_mind with
          (P := Progress_HasTypeInstruction_mind)
          (P0 := Progress_HasTypeClosure_mind)
          (P1 := Progress_HasTypeFunc_mind)
          (P2 := Progress_HasTypeConf_mind).
      - (* value *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        left.
        apply Forall_cons; eauto.
        (* Prove that a context is available *)
        Unshelve. exact Htyp.
      - (* unreachable *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        right. right.
        exists s. exists locs0. exists vs. exists [Trap].
        assert (Hcongr := CtxCongr s s locs0 locs0 locszs i0 [Unreachable] [Trap] 0 (LZero vs []) (StepSimple s locs0 locszs i0 [Unreachable] [Trap] (red_unreachable i0))).
        eauto.
      - (* nop *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        right. right.
        invert H.
        invert H1.
        exists s. exists locs0. exists []. exists [].
        rewrite map_empty.
        do 2 rewrite app_nil_l.
        eapply StepSimple.
        eapply red_nop.
      - (* drop *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists []. exists [].
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_drop.
      - (* select *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H21.
        exists s. exists locs0.
        invert H20.
        case i1.
        + exists [y0]. exists [].
          rewrite app_nil_r.
          eapply StepSimple.
          eapply red_select_O.
        + intros.
          exists [y]. exists [].
          rewrite app_nil_r.
          eapply StepSimple.
          eapply red_select_not_O.
          eauto.
      - (* block *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H0.
        exists s. exists locs0. exists []. exists ([Label (length taus3) (Arrow [] taus3) [] (map Val vs ++ es0)]).
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_block; eauto.
        eapply values_val_map.
        symmetry.
        rewrite (map_length Val vs).
        eapply (list_util.Forall3_length _ _ _ _ H2).
      - (* loop *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H0.
        exists s. exists locs0. exists []. exists ([Label (length taus0) (Arrow [] taus3) [Loop (Arrow taus0 taus3) es0] (map Val vs ++ es0)]).
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_loop; eauto.
        eapply values_val_map.
        symmetry.
        rewrite (map_length Val vs).
        eapply (list_util.Forall3_length _ _ _ _ H2).
      - (* ite *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H1.
        destruct (forall3_back _ _ _ _ _ _ _ _ H3) as [Ss' [S' [vs'[v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        invert H17.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        case i1.
        + exists s. exists locs0. exists vs'. exists [Block (Arrow taus1 taus3) tl es2].
          assert (Hsimple := red_ite_O i0 U (Arrow taus1 taus3) tl es1 es2).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
        + intros.
          exists s. exists locs0. exists vs'. exists [Block (Arrow taus1 taus3) tl es1].
          assert (Hsimple := red_ite_not_O i0 U (Arrow taus1 taus3) tl es1 es2 (Datatypes.S n) (O_S n)).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
    - (* br *)
      unfold Progress_HasTypeInstruction_mind.
      intros.
      clear H12.
      right. right.
      assert (forall (ctx : context 0), ~(ctx |[ [Br i0] ]| = [Br i0])).
      { intros ctx contra.
        apply H10 in contra.
        lia.
      }
      exfalso.
      assert (H13 := H10 0 (LZero [] []) i0).
      simpl in H13.
      assert ([Br i0] = [Br i0]) by reflexivity.
      eapply H13 in H14.
      lia.
      - (* br_if *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        destruct (forall3_back _ _ _ _ _ _ _ _ H1) as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        invert H15.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        case i2; intros; exists s; exists locs0; exists vs'.
        + exists [].
          rewrite app_nil_r.
          assert (Hsimple := red_br_if_O i1 U i0).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
        + exists [Br i0].
          assert (Hsimple := red_br_if_not_O i1 U i0 (Datatypes.S n) (O_S n)).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
      - (* br_table *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        rewrite app_assoc in H1.
        destruct (forall3_back _ _ _ _ _ _ _ _ H1) as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        invert H15.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        case (Nat.le_gt_cases (length is) i1).
        + intros.
          exists s. exists locs0. exists vs'. exists [Br k].
          assert (Hsimple := red_br_table_geq i0 U is i1 k H12).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
        + intros.
          destruct (nth_error_some_exists _ _ _ H12).
          exists s. exists locs0. exists vs'. exists [Br x].
          assert (Hsimple := red_br_table_lt i0 U _ _ k _ H12 H13).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          eassumption.
    - (* ret *)
      unfold Progress_HasTypeInstruction_mind.
      intros.
      clear H12.
      exfalso.
      assert (H12 := H9 0 (LZero [] [])).
      simpl in H12.
      easy.
      - (* get_local *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        rewrite map_empty.
        rewrite app_nil_l.
        destruct (Forall3_nth_error _ _ _ _ S_locals locs0 L _ _ e0 H2).
        destruct H12 as [v [H20 [H21 H22]]].
        invert q0.
        * case const; exists s.
          exists locs0. exists []. exists [Val v].
          eapply StepFull.
          eapply red_get_local_unr.
          exact H21.
          exists (set_nth locs0 i0 Tt). exists []. exists [Val v].
          eapply StepFull.
          eapply red_get_local_lin.
          exact H21.
          congruence.
        * symmetry in H5. destruct H5.
          rewrite nth_error_nil in H13.
          discriminate.
      - (* set_local *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        destruct (Forall3_nth_error _ _ _ _ _ locs0 L _ _  e0 H2) as [S' [v [H20 [H21 H22]]]].
        match goal with
        | [ X : Store |- _ ] => exists X
        end.
        exists (set_nth locs0 i0 y). exists []. exists [].
        eapply StepFull.
        destruct (H11 _ _ _ e0) as [n [H30 H31]].
        eapply red_set_local; eauto.
        rewrite H6 in e3.
        symmetry in e2.
        rewrite H7 in e2.
        specialize (SizeOfType_empty_valid e2).
        intro H40.
        apply size_valid_empty_implies_to_nat in H40.
        destruct H40 as [n1 H40].
        eapply (SizeLeq_Const _ _ _ _ H40 H30) in e3.
        rewrite <-H7 in e2.
        assert (H50 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H16 e2 H6 H40).
        rewrite H50.
        exact e3.
      - (* tee_local *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        match goal with
        | [ X : Store |- _ ] => exists X
        end.
        exists locs0. exists [y; y]. exists  [Set_local i0].
        eapply StepSimple.
        eapply red_tee_local.
      - (* get_global *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        rewrite map_empty.
        rewrite app_nil_l.
        invert H4.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ H3 H13) as [M [H20 H21]].
        invert H21.
        unfold C0 in e0.
        simpl in e0.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ e0 H16).
        destruct H17.
        destruct x.
        exists s. exists locs0. exists [v]. exists [].
        eapply StepFull.
        eapply red_get_global; eauto.
      - (* set_global *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H4.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ H3 H13) as [M [H20 H21]].
        invert H21.
        unfold C0 in e0.
        simpl in e0.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ e0 H18).
        destruct H19.
        destruct x0.
        eexists. exists locs0. exists []. exists [].
        rewrite map_empty.
        rewrite app_nil_r.
        eapply StepFull.
        eapply red_set_global; eauto.
      - (* coderef *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        exists s. exists locs0. exists vs. exists [Val (Coderef i1 i0 [])].
        invert H.
        invert H1.
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_coderef.
      - (* inst *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H16.
        exists s. exists locs0. exists [Coderef modi tabi (is0 ++ is)]. exists [].
        rewrite app_nil_r.
        eapply StepSimple.
        eapply red_coderef_inst.
      - (* call_indirect *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        clear H8 H7 H6 H5 H3 H2 H.
        destruct (forall3_back _ _ _ _ _ _ _ _ H1) as [Ss' [S' [vs' [v' [H21 [H22 [H23 H24]]]]]]].
        invert H24.
        clear H9 H24 H23 H1.
        invert H5.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        destruct H4.
        invert H0.
        do 2 rewrite<- app_assoc in H4.
        simpl in H4.
        eapply Forall_app in H4.
        destruct H4 as [H20 H21].
        invert H21.
        destruct H13 as [H22 H23].
        rewrite H22 in H1.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ H3 H1) as [M [H30 H31]].
        invert H31.
        unfold C0 in H9.
        simpl in H9.
        assert (ts = tab {| term.func := cls; glob := gs; tab := ts |}) by eauto.
        rewrite H17 in H9.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ H6 H9) as [X [H40 H41]].
        exists s. exists locs0. exists vs'. exists [CallAdm X is].
        assert (Hfull := red_call_indirect i0 s locs0 locszs _ _ _ _ is H30 H40).
        assert (Hred := StepFull _ _ _ _ _ _ _ _ Hfull).
        assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
        do 2 rewrite <- ctx_zero_unfold in Hcongr.
        do 2 rewrite app_nil_r in Hcongr.
        eassumption.
      - (* call *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        destruct H4.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ H3 H12) as [M [H20 H21]].
        destruct H21.
        unfold C in e0.
        simpl in e0.
        destruct (Forall2_nth_error _ _ _ _ _ _ _ e0 H13) as [cl [H30 H31]].
        exists s. exists locs0. exists vs. exists [CallAdm cl is].
        assert (Hfull := red_call _ _ locs0 locszs _ _ _ is H20 H30).
        assert (Hred := StepFull _ _ _ _ _ _ _ _ Hfull).
        assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs []) Hred).
        do 2 rewrite <- ctx_zero_unfold in Hcongr.
        do 2 rewrite app_nil_r in Hcongr.
        eassumption.
      - (* rec.fold *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists [Fold y]. exists [].
        rewrite app_nil_r.
        eapply StepSimple.
        eapply red_rec_fold.
      - (* rec.unfold *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H16.
        exists s. exists locs0. exists [v]. exists [].
        rewrite app_nil_r.
        eapply StepSimple.
        eapply red_rec_unfold.
      - (* group *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        right. right.
        invert H.
        destruct (list_util.Forall3_length _ _ _ _ H1) as [H20 H21].
        rewrite<- H21.
        exists s. exists locs0. exists []. exists [Val (term.Prod (to_values (map Val vs) (values_val_map vs)))].
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_group.
        eapply map_length.
      - (* ungroup *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H16.
        simpl.
        exists s. exists locs0. exists vs. exists [].
        rewrite app_nil_r.
        eapply StepSimple.
        eapply red_ungroup.
      - (* cap split *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists [Cap; Own]. exists [].
        rewrite app_nil_r.
        invert H16; eapply StepSimple; eapply red_split.
      - (* cap join *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H18.
        exists s. exists locs0. exists [Cap]. exists [].
        rewrite app_nil_r.
        invert H16; eapply StepSimple; eapply red_join.
      - (* ref demote *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0.
        invert H16.
        + match goal with
          | [ H : context[Ref (LocP ?L Unrestricted)] |- _ ] =>
            exists [Ref (LocP L Unrestricted)]
          end.
          exists [].
          rewrite app_nil_r.
          eapply StepSimple. eapply red_demote.
        + match goal with
          | [ H : context[Ref (LocP ?L Linear)] |- _ ] =>
            exists [Ref (LocP L Linear)]
          end.
          exists [].
          rewrite app_nil_r.
          eapply StepSimple. eapply red_demote.
      - (* mempack *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists [Mempack l y]. exists [].
        rewrite app_nil_r.
        eapply StepSimple.
        eapply red_mempack.
      - (* memunpack *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H0.
        destruct (forall3_back _ _ _ _ _ _ _ _ H2) as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        invert H16.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        exists s. exists locs0. exists vs'.
        match goal with
        | [ H : context[debruijn.ext _ ?L debruijn.id] |- _ ] =>
          exists [Block (Arrow taus1 taus3) tl (Val v :: map (debruijn.subst_ext (@debruijn.ext _ _ subst.Kind subst.SLoc L debruijn.id)) es0)];
          assert (Hsimple := red_memunpack i0 L v tl (Arrow taus1 taus3) es0)
        end.
        assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
        assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
        do 2 rewrite<- ctx_zero_unfold in Hcongr.
        do 2 rewrite app_nil_r in Hcongr.
        eassumption.
      - (* struct malloc *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        assert (H20 := list_util.Forall2_length _ _ _ f).
        destruct (list_util.Forall3_length _ _ _ _ H1) as [H21 H22].
        symmetry in H20.
        exists s. exists locs0. exists []. exists [Malloc (fold_left (fun sz1 sz2 => (SizePlus sz1 sz2)) szs (SizeConst 0)) (Struct (to_values (map Val vs) (values_val_map vs))) q].
        rewrite app_nil_l.
        rewrite<- (map_length Val) in H22.
        eapply StepSimple.
        eapply (red_struct_malloc i0 (length taus1) _ (values_val_map vs) _ ); eauto.
        unfold sizes_closed.
        rewrite H6 in f0.
        eapply (Forall_impl _ _ f0).
        Unshelve.
        intros.
        induction a.
        + invert H12; try discriminate.
          rewrite nth_error_nil in H14.
          discriminate.
        + intros.
          invert H12; try discriminate.
          invert H13.
          simpl.
          eauto.
        + simpl. eauto.
      - (* struct free *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists [y]. exists [Free].
        assert (Hred := red_struct_free i0 s locs0 locszs).
        assert (Hfull := StepFull _ _ _ _ _ _ _ _ Hred).
        eapply (CtxCongr _ _ _ _ _ _ _ _ 0 (LZero [y] []) Hfull).
      - (* struct get *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        clear H H1 H2 H5 H6 H7 H17 Htyp i es taus Sprog ret.
        invert H16; simpl; simpl in H0.
        + clear H15.
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end.
          invert H0.
          invert H2.
          destruct H12.
          rewrite H7 in H21.
          destruct (H21 H14) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          rewrite (combine_split _ _ e0) in H22.
          invert H22.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ e1 H19) as [S' [v [H40 [H41 H42]]]].
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Ref (LocP L Unrestricted); v]
          end.
          exists [].
          simpl.
          eapply StepFull.
          eapply red_struct_get; eauto.
        + assert (H100 := nth_error_cons _ x (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H12).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end. 
          destruct (H20 H102) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          rewrite (combine_split _ _ e0) in H7.
          invert H7.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ e1 H6) as [S' [v [H40 [H41 H42]]]].
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Ref (LocP L Linear); v]
          end.
          exists [].
          simpl.
          eapply StepFull.
          eapply red_struct_get; eauto.
      - (* struct set *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        assert (H200 := H5).
        assert (H201 := H6).
        assert (H202 := H7).
        clear H H1 H2 H5 H6 H7 H17 H19 Htyp i es taus Sprog ret.
        invert H16; simpl; simpl in H0.
        + clear H15.
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end.
          invert H0.
          invert H2.
          destruct H12.
          rewrite H7 in H21.
          destruct (H21 H14) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          assert (H400 := SizeOfStruct_Typecheck_Actual _ _ _ _ _ _ H32 (combine_split _ _ e0) (eq_refl _)).
          rewrite (combine_split _ _ e0) in H23.
          invert H23.
          destruct H27 as [H26a H26b].
          destruct (Forall2_nth_error _ _ _ _ _ _ _ e3 H26b) as [tau_old' [H83 H84]].
          clear H84.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ H83 H22) as [S''' [v [H80 [H81 H82]]]].
          rewrite H201 in e5.
          eapply Forall2_switch in H26b.
          assert (H120 := Forall2_nth_error _ _ _ _ _ _ _ H83 H26b).
          simpl in H120.
          destruct H120 as [sz_slot [H120 [sz_v [H121 H122]]]].
          rewrite e3 in H120.
          invert H120.
          invert H33; try easy.
          simpl in H26.
          eapply combine_split in e0.
          rewrite e0 in H24.
          invert H24.
          rewrite H202 in e4.
          specialize (SizeOfType_empty_valid e4).
          intro H401.
          apply size_valid_empty_implies_to_nat in H401.
          destruct H401 as [n_tau_sz H401].
          assert (H402 : SizeValid [] sz_slot).
          { rewrite Forall_forall in H26a.
            apply H26a.
            eapply nth_error_In; eauto. }
          apply size_valid_empty_implies_to_nat in H402.
          destruct H402 as [n_sz_slot H402].
          eapply (SizeLeq_Const _ _ _ _ H401 H402) in e5.
          rewrite <-H202 in e4.
          assert (H404 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H18 e4 H201 H401).
          specialize (H400 eq_refl).
          assert (H405 := struct_update_size _ _ _ _ _ _ _ _ _ _ _ (fold_is_size_as_nat szs0 n' H26) H400 H32 e0 H404 e3 H402 e5).
          destruct (set_spec1 _ _ _ _ _ _ H31 (nat_n_swap _ _ H405)) as [m H410].
          match goal with
          | [ X : Store |- _ ] =>
              exists (Build_Store (inst X) m (out_set X))
          end.
          exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Ref (LocP L Unrestricted)]
          end.
          exists [].
          simpl.
          eapply StepFull.
          eapply red_struct_set; eauto.
          unfold update_mem; rewrite H410; eauto.
          simpl; reflexivity.
        + assert (H100 := nth_error_cons _ x (x0 :: S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H12).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end.
          destruct (H20 H102) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          rewrite (combine_split _ _ e0) in H7.
          invert H7.
          assert (H400 := SizeOfStruct_Typecheck_Actual _ _ _ _ _ _ H32 (combine_split _ _ e0) (eq_refl _)).
          destruct H22 as [H19a H19b].
          destruct (Forall2_nth_error _ _ _ _ _ _ _ e3 H19b) as [tau_old' [H83 H84]].
          clear H84.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ H83 H6) as [S''' [v [H80 [H81 H82]]]].
          rewrite H201 in e5.
          eapply Forall2_switch in H19b.
          assert (H120 := Forall2_nth_error _ _ _ _ _ _ _ H83 H19b).
          simpl in H120.
          destruct H120 as [sz_slot [H120 [sz_v [H121 H122]]]].
          rewrite e3 in H120.
          invert H120.
          invert H33; try easy.
          eapply combine_split in e0.
          rewrite e0 in H13.
          invert H13.
          rewrite H202 in e4.
          specialize (SizeOfType_empty_valid e4).
          intro H401.
          apply size_valid_empty_implies_to_nat in H401.
          destruct H401 as [n_tau_sz H401].
          assert (H402 : SizeValid [] sz_slot).
          { rewrite Forall_forall in H19a.
            apply H19a.
            eapply nth_error_In; eauto. }
          apply size_valid_empty_implies_to_nat in H402.
          destruct H402 as [n_sz_slot H402].
          eapply (SizeLeq_Const _ _ _ _ H401 H402) in e5.
          rewrite <-H202 in e4.
          assert (H404 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H18 e4 H201 H401).
          specialize (H400 eq_refl).
          assert (H405 := struct_update_size _ _ _ _ _ _ _ _ _ _ _ (fold_is_size_as_nat _ _ H19) H400 H32 e0 H404 e3 H402 e5).
          destruct (set_spec1 _ _ _ _ _ _ H31 (nat_n_swap _ _ H405)) as [m H410].
          match goal with
          | [ X : Store |- context[LocP ?L _] ] =>
            exists (update_out_set L (Build_Store (inst X) m (out_set X)) (Struct vs) (Struct (set_nth vs n y0)))
          end.
          exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Ref (LocP L Linear)]
          end.
          exists [].
          simpl.
          eapply StepFull.
          eapply red_struct_set; eauto.
          unfold update_mem; rewrite H410; eauto.
          simpl; reflexivity.
      - (* struct swap *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        assert (H200 := H5).
        assert (H201 := H6).
        assert (H202 := H7).
        clear H H1 H2 H5 H6 H7 H17 H19 Htyp i es taus Sprog ret.
        invert H16; simpl; simpl in H0.
        + clear H15.
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end.
          invert H0.
          invert H2.
          destruct H12.
          rewrite H7 in H21.
          destruct (H21 H14) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          assert (H400 := SizeOfStruct_Typecheck_Actual _ _ _ _ _ _ H32 (combine_split _ _ e0) (eq_refl _)).
          rewrite (combine_split _ _ e0) in H23.
          invert H23.
          destruct H27 as [H26a H26b].
          destruct (Forall2_nth_error _ _ _ _ _ _ _ e2 H26b) as [tau_old' [H83 H84]].
          clear H84.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ H83 H22) as [S''' [v [H80 [H81 H82]]]].
          rewrite H201 in e4.
          eapply Forall2_switch in H26b.
          assert (H120 := Forall2_nth_error _ _ _ _ _ _ _ H83 H26b).
          simpl in H120.
          destruct H120 as [sz_slot [H120 [sz_v [H121 H122]]]].
          rewrite e2 in H120.
          invert H120.
          invert H33; try easy.
          simpl in H26.
          eapply combine_split in e0.
          rewrite e0 in H24.
          invert H24.
          rewrite H202 in e3.
          specialize (SizeOfType_empty_valid e3).
          intro H401.
          apply size_valid_empty_implies_to_nat in H401.
          destruct H401 as [n_tau_sz H401].
          assert (H402 : SizeValid [] sz_slot).
          { rewrite Forall_forall in H26a.
            apply H26a.
            eapply nth_error_In; eauto. }
          apply size_valid_empty_implies_to_nat in H402.
          destruct H402 as [n_sz_slot H402].
          eapply (SizeLeq_Const _ _ _ _ H401 H402) in e4.
          rewrite <-H202 in e3.
          assert (H404 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H18 e3 H201 H401).
          specialize (H400 eq_refl).
          assert (H405 := struct_update_size _ _ _ _ _ _ _ _ _ _ _ (fold_is_size_as_nat _ _ H26) H400 H32 e0 H404 e2 H402 e4).
          destruct (set_spec1 _ _ _ _ _ _ H31 (nat_n_swap _ _ H405)) as [m H410].
          match goal with
          | [ X : Store |- _ ] =>
              exists (Build_Store (inst X) m (out_set X))
          end.
          exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Ref (LocP L Unrestricted); v]
          end.
          exists [].
          simpl.
          eapply StepFull.
          eapply red_struct_swap; eauto.
          unfold update_mem; rewrite H410; eauto.
          simpl; reflexivity.
        + assert (H100 := nth_error_cons _ x (x0 :: S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H12).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (StructType (combine taus0 szs))) as [H20 H21]
          end.
          destruct (H20 H102) as [hv [n' [S_h' [Ss [H30 [H31 [H32 H33]]]]]]].
          invert H32.
          rewrite (combine_split _ _ e0) in H7.
          invert H7.
          assert (H400 := SizeOfStruct_Typecheck_Actual _ _ _ _ _ _ H32 (combine_split _ _ e0) (eq_refl _)).
          destruct H22 as [H19a H19b].
          destruct (Forall2_nth_error _ _ _ _ _ _ _ e2 H19b) as [tau_old' [H83 H84]].
          clear H84.
          destruct (Forall3_nth_error _ _ _ _ _ _ _ _ _ H83 H6) as [S''' [v [H80 [H81 H82]]]].
          rewrite H201 in e4.
          eapply Forall2_switch in H19b.
          assert (H120 := Forall2_nth_error _ _ _ _ _ _ _ H83 H19b).
          simpl in H120.
          destruct H120 as [sz_slot [H120 [sz_v [H121 H122]]]].
          rewrite e2 in H120.
          invert H120.
          invert H33; try easy.
          eapply combine_split in e0.
          rewrite e0 in H13.
          invert H13.
          rewrite H202 in e3.
          specialize (SizeOfType_empty_valid e3).
          intro H401.
          apply size_valid_empty_implies_to_nat in H401.
          destruct H401 as [n_tau_sz H401].
          assert (H402 : SizeValid [] sz_slot).
          { rewrite Forall_forall in H19a.
            apply H19a.
            eapply nth_error_In; eauto. }
          apply size_valid_empty_implies_to_nat in H402.
          destruct H402 as [n_sz_slot H402].
          eapply (SizeLeq_Const _ _ _ _ H401 H402) in e4.
          rewrite <-H202 in e3.
          assert (H404 := SizeOfValue_Typecheck_Actual _ _ _ _ _ _ H18 e3 H201 H401).
          specialize (H400 eq_refl).
          assert (H405 := struct_update_size _ _ _ _ _ _ _ _ _ _ _ (fold_is_size_as_nat _ _ H19) H400 H32 e0 H404 e2 H402 e4).
          destruct (set_spec1 _ _ _ _ _ _ H31 (nat_n_swap _ _ H405)) as [m H410].
          match goal with
          | [ X : Store |- context[LocP ?L _] ] =>
            exists (update_out_set L (Build_Store (inst X) m (out_set X)) (Struct vs) (Struct (set_nth vs n y0))); exists locs0; exists [Ref (LocP L Linear); v]; exists []
          end.
          simpl.
          eapply StepFull.
          eapply red_struct_swap; eauto.
          unfold update_mem; rewrite H410; eauto.
          simpl; reflexivity.
      -(* variant malloc *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        simpl.
        exists s. exists locs0. exists []. exists [Malloc (SizePlus (SizeConst 32) (size_of_value y)) (Variant n y) q].
        rewrite map_empty.
        rewrite app_nil_l.
        eapply StepSimple.
        eapply red_variant_malloc.
      - (* variant case unrestricted *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        eapply forall3_back in H1.
        destruct H1 as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        invert H14.
        + invert H4.
          unfold typing_valid in H1.
          match goal with
          | [ |- context[LocP ?L _] ]=>
            destruct (H1 L (VariantType tausv)) as [H30 H31]
          end.
          invert H0.
          do 2 rewrite<- app_assoc in H13.
          simpl in H13.
          eapply Forall_app in H13.
          destruct H13.
          invert H16.
          destruct H26.
          rewrite<- H19 in H21.
          destruct (H31 H21) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          destruct (Forall2_nth_error _ _ _ _ _ _ _ H29 f) as [es' [H90 H91]].
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists ((Ref (LocP L Unrestricted)) :: vs')
          end.
          exists [Block (Arrow taus1 taus2) tl (Val v :: es')].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (Hsimple := red_variant_case_am i0 s Unrestricted locs0 locszs L (Arrow taus1 taus2) tl es0 es' i1 v n')
          end.
          unfold get_mem in Hsimple.
          assert (length (map Val vs') = length taus1).
          clear - H22.
          rewrite map_length.
          eapply Forall3_length.
          exact H22.
          assert (Hsimple' := Hsimple (VariantType tausv) (map Val vs') (values_val_map vs') taus1 taus2 H41 H90 (eq_refl _) H26).
          assert (Hred := StepFull _ _ _ _ _ _ _ _ Hsimple').
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero [] []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2 : {rewrite H5 in H33. rewrite nth_error_nil in H33. discriminate. }
          rewrite H5 in e2.
          eapply QualLeq_Bottom_Const in e2.
          inversion e2; subst.
          simpl in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          exact Hcongr.
        + do 2 rewrite<- app_assoc in H0.
          simpl in H0.
          assert (H100 := nth_error_app _ S' Ss' (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H19).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H1.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H1 L (VariantType tausv)) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          destruct (Forall2_nth_error _ _ _ _ _ _ _ H16 f) as [es' [H60 H61]].
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists ((Ref (LocP L Linear)) :: vs'); exists [Block (Arrow taus1 taus2) tl (Val v :: es')];
            assert (Hsimple := red_variant_case_am i0 s Linear locs0 locszs L (Arrow taus1 taus2) tl es0 es' i1 v n')
          end.
          unfold get_mem in Hsimple.
          assert (length (map Val vs') = length taus1).
          clear - H22.
          rewrite map_length.
          eapply Forall3_length.
          exact H22.
          assert (Hsimple' := Hsimple (VariantType tausv) (map Val vs') (values_val_map vs') taus1 taus2 H41 H60 (eq_refl _) H13).
          assert (Hred := StepFull _ _ _ _ _ _ _ _ Hsimple').
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero [] []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2 : {rewrite H5 in H20. rewrite nth_error_nil in H20. discriminate. }
          rewrite H5 in e2.
          eapply QualLeq_Bottom_Const in e2.
          inversion e2; subst.
          simpl in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          exact Hcongr.
      - (* variant case linear *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        eapply forall3_back in H1.
        destruct H1 as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        invert H14.
        + invert q1.
          2 : {rewrite H5 in H12. rewrite nth_error_nil in H12. discriminate. }
          eapply QualLeq_Bottom_Const in H24.
          inversion H24; subst.
          rewrite H5 in e1.
          eapply QualLeq_Const_False in e1.
          easy.
        + do 2 rewrite<- app_assoc in H0.
          simpl in H0.
          assert (H100 := nth_error_app _ S' Ss' (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H19).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H1.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H1 L (VariantType tausv)) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          destruct (Forall2_nth_error _ _ _ _ _ _ _ H16 f) as [es' [H60 H61]].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (Hloc : exists st', update_mem s L Linear (Array 0 []) = Some st')
          end.
          { unfold update_mem.
            match goal with
            | [ |- context[set ?A ?B ?C ?D] ] =>
              assert (Hsubgoal : exists E, set A B C D = Some E)
            end.
            { eapply set_spec1; eauto.
              simpl.
              eapply OrdersEx.N_as_OT.le_0_l. }
            destruct Hsubgoal as [E Hsubgoal].
            rewrite Hsubgoal.
            eexists; eauto. }
          destruct Hloc as [st'].
          exists st'. exists locs0. exists vs'.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Val v; Val (Ref (LocP L Linear)); Free; Block (Arrow (taus1 ++ [tau]) taus3) tl es'];
            assert (Hsimple := red_variant_case_mm i0 s st' locs0 locszs L (Arrow taus1 taus3) tl es0 es' i1 v n')
          end.
          unfold get_mem in Hsimple.
          eapply Hsimple in H41.
          3: { exact H60. }
          assert (Hred := StepFull _ _ _ _ _ _ _ _ H41).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2: {rewrite H5 in q0. inversion q0; subst.
              - inversion H17.
              - rewrite nth_error_nil in H25.
                inversion H25. }
          rewrite H5 in e0.
          eapply QualLeq_Top_Const in e0.
          inversion e0; subst.
          exact Hcongr.
          exact H13.
          exact H16.
          exact eq_refl.
          exact eq_refl.
      - (* array malloc *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H18.
        simpl.
        exists s. exists locs0. exists []. exists [Malloc (SizePlus (SizeConst 32) (fold_left (fun sz1 sz2 => (SizePlus sz1 sz2))(repeat (size_of_value y) i1) (SizeConst 0))) (Array i1 (repeat y i1)) q].
        eapply StepSimple.
        eapply red_array_malloc.
      - (* array get *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H18.
        clear H H1 H2 H5 H6 H7 H17 H19 Htyp i es taus Sprog ret.
        invert H16; simpl; simpl in H0.
        + clear H17.
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (ArrayType (QualT p Unrestricted))) as [H30 H31]
          end.
          invert H0.
          invert H2.
          destruct H12.
          rewrite H7 in H31.
          destruct (H31 H15) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          case (Nat.lt_ge_cases i1 (length vs)).
          * intros.
            destruct (nth_error_some_exists _ i1 vs H12).
            match goal with
            | [ |- context[LocP ?L _] ] =>
              exists s; exists locs0; exists [Ref (LocP L Unrestricted); x1]; exists []
            end.
            simpl.
            eapply StepFull.
            eapply red_array_get; eauto.
          * intros.
            destruct (nth_error_None vs i1).
            assert (H45 := H26 H12).
            exists s. exists locs0. exists []. exists [Trap].
            simpl.
            eapply StepFull.
            eapply red_array_get_trap; eauto.
        + assert (H100 := nth_error_cons _ x (x0 :: S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H12).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (ArrayType (QualT p Unrestricted))) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          case (Nat.lt_ge_cases i1 (length vs)).
          * intros.
            destruct (nth_error_some_exists _ i1 vs H2).
            exists s. exists locs0.
            match goal with
            | [ |- context[LocP ?L _] ] =>
              exists [Ref (LocP L Linear); x1]
            end.
            exists [].
            simpl.
            eapply StepFull.
            eapply red_array_get; eauto.
          * intros.
            destruct (nth_error_None vs i1).
            assert (H60 := H19 H2).
            exists s. exists locs0. exists []. exists [Trap].
            simpl.
            eapply StepFull.
            eapply red_array_get_trap; eauto.
      - (* array set *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        assert (H204 := H12).
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H21.
        invert H18.
        assert (H200 := H5).
        assert (H201 := H6).
        assert (H202 := H7).
        clear H H1 H2 H5 H6 H7 H17 H19 H21 Htyp i es taus Sprog ret.
        invert H16; simpl; simpl in H0.
        + clear H17.
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (ArrayType (QualT p Unrestricted))) as [H30 H31]
          end.
          invert H0.
          invert H2.
          destruct H12.
          rewrite H7 in H31.
          destruct (H31 H15) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          case (Nat.lt_ge_cases i1 (length vs)).
          * intros.
            destruct (nth_error_some_exists _ i1 vs H12).
            assert (H160 := get_spec1 _ _ _ _ _ H41).
            simpl in H160.
            assert (size_val y1 <= size_val x2).
            destruct (Forall2_nth_error _ _ _ _ _ _ _ H21 H33) as [S''' [H170 H171]].
            assert (qual F = qual empty_Function_Ctx) by eauto.
            assert (Hstrong_1 : size F = size empty_Function_Ctx) by eauto.
            assert (Hstrong_2 : type F = type empty_Function_Ctx) by eauto.
            assert (Hstrong_3 : location F = location empty_Function_Ctx) by eauto.
            assert (H180 := HasTypeValue_Function_Ctx _ _ _ _ _ H27 Hstrong_1 Hstrong_2 Hstrong_3 H20).
            assert (H90 := size_typecheck_eq _ _ _ _ _ H171 H180).
            lia.
            assert (H170 := size_update _ _ _ _ _ H21 H27 (n_nat_swap _ _ H160)).
            assert (term.size (Array (length vs) (set_nth vs i1 y1)) <= N.to_nat n') by eauto.
            assert (H180 := set_spec1 _ _ _ _ _ _ H41 (nat_n_swap _ _ H28)).
            destruct H180 as [mem' H180].
            exists (Build_Store (inst s) mem' (out_set s)). exists locs0.
            match goal with
            | [ |- context[LocP ?L _] ] =>
              exists [Ref (LocP L Unrestricted)]
            end.
            exists [].
            eapply StepFull.
            eapply red_array_set; eauto.
            unfold update_mem; rewrite H180; eauto.
            unfold qualconstr_eq_dec; reflexivity.
          * intros.
            exists s. exists locs0. exists []. exists [Trap].
            simpl.
            eapply StepFull.
            eapply red_array_set_trap; eauto.
        + assert (H100 := nth_error_cons _ x (x0 :: x1 :: S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H12).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H L (ArrayType (QualT p Unrestricted))) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          case (Nat.lt_ge_cases i1 (length vs)).
          * intros.
            destruct (nth_error_some_exists _ i1 vs H2).
            assert (H60 := get_spec1 _ _ _ _ _ H41).
            simpl in H60.
            assert (size_val y1 <= size_val x2).
            destruct (Forall2_nth_error _ _ _ _ _ _ _ H5 H26) as [S'' [H70 H71]].
            assert (qual F = qual empty_Function_Ctx) by eauto.
            assert (Hstrong_1 : size F = size empty_Function_Ctx) by eauto.
            assert (Hstrong_2 : type F = type empty_Function_Ctx) by eauto.
            assert (Hstrong_3 : location F = location empty_Function_Ctx) by eauto.
            assert (H80 := HasTypeValue_Function_Ctx _ _ _ _ _ H19 Hstrong_1 Hstrong_2 Hstrong_3 H20).
            assert (H90 := size_typecheck_eq _ _ _ _ _ H71 H80).
            lia.
            assert (H70 := size_update _ _ _ _ _ H5 H19 (n_nat_swap _ _ H60)).
            assert (term.size (Array (length vs) (set_nth vs i1 y1)) <= N.to_nat n') by eauto.
            assert (H80 := set_spec1 _ _ _ _ _ _ H41 (nat_n_swap _ _ H21)).
            destruct H80 as [mem' H80].
            match goal with
            | [ |- context[LocP ?L _] ] =>
              exists (update_out_set L (Build_Store (inst s) mem' (out_set s)) (Array (length vs) vs) (Array (length vs) (set_nth vs i1 y1))); exists locs0; exists [Ref (LocP L Linear)]; exists []
            end.
            eapply StepFull.
            eapply red_array_set; eauto.
            unfold update_mem; rewrite H80; eauto.
            unfold qualconstr_eq_dec; reflexivity.
          * intros.
            exists s. exists locs0. exists []. exists [Trap].
            simpl.
            eapply StepFull.
            eapply red_array_set_trap; eauto.
      - (* array free *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        exists s. exists locs0. exists vs. exists [Free].
        assert (Hred := red_array_free i0 s locs0 locszs).
        assert (Hfull := StepFull _ _ _ _ _ _ _ _ Hred).
        assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs []) Hfull).
        do 2 rewrite<- ctx_zero_unfold in Hcongr.
        simpl in Hcongr.
        eassumption.
      - (* Exist Pack *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s1. exists locs0. exists []. exists [Malloc (SizePlus (SizeConst 64) (size_of_value y)) (Pack p y (Ex sz0 q (QualT hp hq))) q].
        eapply StepSimple.
        simpl.
        eapply red_exist_pack.
      - (* Exist Unpack Unrestricted *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H0.
        eapply forall3_back in H2.
        destruct H2 as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        invert H15.
        + invert H5.
          unfold typing_valid in H2.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H2 L (Ex sz0 qα (QualT p_ex q_ex))) as [H30 H31]
          end.
          invert H1.
          do 2 rewrite<- app_assoc in H14.
          simpl in H14.
          eapply Forall_app in H14.
          destruct H14.
          invert H17.
          destruct H27.
          rewrite<- H20 in H24.
          destruct (H31 H24) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists ((Ref (LocP L Unrestricted)) :: vs')
          end.
          exists [Block (Arrow taus1 taus2) tl (Val v :: map (debruijn.subst_ext (Kind:=subst.Kind) (debruijn.ext subst.SPretype pt debruijn.id)) es0)].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (Hsimple := red_unpack_am i0 s locs0 locszs (Arrow taus1 taus2) tl es0 L pt v (Ex sz0 qα (QualT p_ex q_ex)) Unrestricted n')
          end.
          unfold get_mem in Hsimple.
          assert (length (map Val vs') = length taus1).
          clear - H22.
          rewrite map_length.
          eapply Forall3_length.
          exact H22.
          assert (Hsimple' := Hsimple (Ex sz0 qα (QualT p_ex q_ex)) (map Val vs') (values_val_map vs') taus1 taus2 H41 (eq_refl _) H27).
          assert (Hred := StepFull _ _ _ _ _ _ _ _ Hsimple').
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero [] []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2 : {rewrite H6 in H32. rewrite nth_error_nil in H32. discriminate. }
          rewrite H6 in e1.
          eapply QualLeq_Bottom_Const in e1.
          inversion e1; subst.
          simpl in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          exact Hcongr.
        + do 2 rewrite<- app_assoc in H1.
          simpl in H1.
          assert (H100 := nth_error_app _ S' Ss' (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H20).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H1 H100 H101).
          invert H5.
          unfold typing_valid in H2.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H2 L (Ex sz0 qα (QualT p_ex q_ex))) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          exists s. exists locs0.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists ((Ref (LocP L Linear)) :: vs')
          end.
          exists [Block (Arrow taus1 taus2) tl (Val v :: map (debruijn.subst_ext (Kind:=subst.Kind) (debruijn.ext subst.SPretype pt debruijn.id)) es0)].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (Hsimple := red_unpack_am i0 s locs0 locszs (Arrow taus1 taus2) tl es0 L pt v (Ex sz0 qα (QualT p_ex q_ex)))
          end.
          unfold get_mem in Hsimple.
          assert (length (map Val vs') = length taus1).
          clear - H22.
          rewrite map_length.
          eapply Forall3_length.
          exact H22.
          assert (Hsimple' := Hsimple _ _ (Ex sz0 qα (QualT p_ex q_ex)) (map Val vs') (values_val_map vs') taus1 taus2 H41 eq_refl H14).
          assert (Hred := StepFull _ _ _ _ _ _ _ _ Hsimple').
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero [] []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2 : {rewrite H6 in H17. rewrite nth_error_nil in H17. discriminate. }
          rewrite H6 in e1.
          eapply QualLeq_Bottom_Const in e1.
          inversion e1; subst.
          simpl in Hcongr.
          do 2 rewrite app_nil_r in Hcongr.
          exact Hcongr.
      - (* Exist Unpack Linear *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H13.
        right. right.
        invert H0.
        eapply forall3_back in H2.
        destruct H2 as [Ss' [S' [vs' [v' [H20 [H21 [H22 H23]]]]]]].
        invert H23.
        rewrite map_app.
        rewrite<- app_assoc.
        simpl.
        invert H15.
        + invert q1.
          2 : {rewrite H6 in H13. rewrite nth_error_nil in H13. discriminate. }
          eapply QualLeq_Bottom_Const in H25.
          inversion H25; subst.
          rewrite H6 in e0.
          eapply QualLeq_Const_False in e0.
          easy.
        + do 2 rewrite<- app_assoc in H1.
          simpl in H1.
          assert (H100 := nth_error_app _ S' Ss' (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H20).
          assert (H102 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H1 H100 H101).
          invert H5.
          unfold typing_valid in H2.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H2 L (Ex sz0 qα tau)) as [H30 H31]
          end.
          destruct (H30 H102) as [hv [n' [S_h' [Ss [H40 [H41 [H42 H43]]]]]]].
          invert H42.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (Hloc : exists st', update_mem s L Linear (Array 0 []) = Some st')
          end.
          { unfold update_mem.
            match goal with
            | [ |- context[set ?A ?B ?C ?D] ] =>
              assert (Hsubgoal : exists E, set A B C D = Some E)
            end.
            { eapply set_spec1; eauto.
              simpl.
              eapply OrdersEx.N_as_OT.le_0_l. }
            destruct Hsubgoal as [E Hsubgoal].
            rewrite Hsubgoal.
            eexists; eauto. }
          destruct Hloc as [st'].
          exists st'. exists locs0. exists vs'.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Val v; Val (Ref (LocP L Linear)); Free; Block (Arrow (taus1 ++ [debruijn.subst_ext (Kind:=subst.Kind) (debruijn.ext subst.SPretype pt debruijn.id) tau]) taus3) tl (map (debruijn.subst_ext (Kind:=subst.Kind) (debruijn.ext subst.SPretype pt debruijn.id)) es0)];
            assert (Hsimple := red_unpack_mm i0 s st' locs0 locszs (Arrow taus1 taus3) tl es0 L pt v n' (Ex sz0 qα tau))
          end.
          unfold get_mem in Hsimple.
          eapply Hsimple in H41.
          assert (Hred := StepFull _ _ _ _ _ _ _ _ H41).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs' []) Hred).
          do 2 rewrite<- ctx_zero_unfold in Hcongr.
          simpl in Hcongr.
          invert q0.
          2 : {rewrite H6 in H17. rewrite nth_error_nil in H17. discriminate. }
          rewrite H6 in e.
          eapply QualLeq_Top_Const in e.
          inversion e; subst.
          exact Hcongr.
          exact H14.
          exact eq_refl.
          exact eq_refl.
      - (* RefSplit *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H16; exists s; exists locs0.
        * match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Cap; PtrV (LocP L Unrestricted)]
          end.
          exists [].
          eapply StepSimple.
          rewrite app_nil_r.
          simpl.
          eapply red_refsplit.
        * match goal with
          | [ |- context[LocP ?L _] ] =>
            exists [Cap; PtrV (LocP L Linear)]
          end.
          exists [].
          eapply StepSimple.
          rewrite app_nil_r.
          simpl.
          eapply red_refsplit.
      - (* RefJoin *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        invert H19.
        invert H18; invert H16; exists s; exists locs0. 

        match goal with
        | [ |- context[LocP ?L _] ] =>
          exists [Ref (LocP L Linear)]
        end.
        exists [].
        eapply StepSimple.
        rewrite app_nil_r.
        simpl.
        eapply red_refjoin.
      - (* Qualify *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        exists s. exists locs0. exists [y]. exists [].
        eapply StepSimple.
        eapply red_qualify.
       (* Administrative Instructions *)
      - (* Trap *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        eauto.
      - (* Call Adm *)  
        unfold Progress_HasTypeInstruction_mind.
        unfold Progress_HasTypeClosure_mind.
        intros.
        right. right.
        symmetry in H0. 
        invert h.
        invert H15.
        exists s. exists locs0. exists []. eexists.
        simpl. 
        eapply StepSimple.
        eapply (red_call_adm _ _ _ _ _ _ _ _ _ taus4 taus5); eauto.
        + destruct (list_util.Forall3_length _ _ _ _ H2) as [H210 H220].
          rewrite H220.
          unfold chi0 in e.
          match goal with
          | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
            inversion H; subst
          end.
          exact (inst_inds_length _ _ _ _ _ _ e).
        + unfold chi0.
          reflexivity.

          Unshelve.
          all: eapply inst_sizes_is_closed; eauto.
          all:
            try match goal with
                | [ |- InstIndsValid _ _ _ ] =>
                  eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ]; eauto
                end.
          
          rewrite update_ret_ctx_size.
          unfold F_cnstr in *.
          rewrite Forall_forall.
          intros.
          match goal with
          | [ H : List.In _ _ |- _ ] =>
            apply In_nth_error in H
          end.
          destructAll.
          match goal with
          | [ H : Forall2 _ ?L1 ?L2,
              H' : nth_error ?L2 ?IDX = Some _ |- _ ] =>
            let H0 := fresh "H" in
            assert (H0 : exists v, nth_error L1 IDX = Some v)
          end.
          { apply nth_error_some_exists.
            match goal with
            | [ H : length ?X = length ?Y |- _ < length ?X ] =>
              rewrite H
            end.
            eapply nth_error_Some_length; eauto. }
          destructAll.
          match goal with
          | [ H : Forall2 _ ?L1 ?L2,
              H' : nth_error ?L1 _ = Some _,
              H'' : nth_error ?L2 _ = Some _ |- _ ] =>
            specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
          end.
          intros; simpl in *.
          eapply SizeOfType_valid_KindVarsValid; eauto.
          match goal with
          | [ H : FunTypeValid _ ?FT |- _ ] =>
            inversion H; subst; simpl in *; auto
          end.
    - (* label *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        assert (H200 := H14).
        clear H14.
        right. right.
        invert H1.
        invert H3.
        simpl.
        destruct (br_hole_excluded_middle es2).
        + destruct H14 as [n' [ctx' H14]].
          assert (ctx_app n' ctx' [Br (n' + 0)] = es2) by (rewrite<- plus_n_O; eauto).
          eapply br_reduce_extract_vs in H15; eauto.
          2 : {induction F. simpl. easy. }
          2:{
            destruct F; cbn in *; auto.
          }
          destruct H15 as [vs' [ctx'' [H20 H21]]].
          rewrite<- plus_n_O in H20.
          rewrite<- H20.
          exists s. exists locs0. exists []. exists (map Val vs' ++ es1).
          simpl.
          eapply StepSimple.
          eapply red_label_ctx.
          eapply values_val_map.
          rewrite (map_length Val vs').
          exact H21.
        + destruct (H _ _ _ _ locszs _ _ _ _ _ _ _ (eq_refl _) H2 (Forall3_nil _) (local_typings_linear_label_agnostic _ _ _ locs0 L _ _ H4) H5 H6 (qual_linear_label _ _ _ _ H7) (size_linear_label _ _ _ _ H8) (type_linear_label _ _ _ _ H9) H10 (no_ret_in_hole_label_extend _ _ _ _ H11)) as [IH | [IH | IH]].
          * intros.
            eapply br_in_hole_extend; eauto.
          * exact H13.
          * induction F; eexact H200.
          * destruct (forall_e_v _ IH).
            rewrite <- H15.
            exists s. exists locs0. exists []. exists (map Val x).
            simpl.
            eapply StepSimple.
            eapply red_label.
            eapply values_val_map.
          * rewrite IH.
            exists s. exists locs0. exists []. exists [Trap].
            eapply StepSimple.
            eapply red_label_trap.
          * destruct IH as [s' [locs' [vs' [es' H20]]]].
            simpl in H20.
            exists s'. exists locs'. exists []. exists [Label (length tau1) (Arrow [] taus2) es1 (map Val vs' ++ es')].
            simpl.
            assert (Hcongr := CtxCongr s s' locs0 locs' locszs i1 es2 (map Val vs' ++ es') (1 + 0) (LSucc_label 0 [] (length tau1) (Arrow [] taus2) es1 (LZero [] []) []) H20).
            do 2 rewrite<- ctx_k_unfold in Hcongr.
            do 2 rewrite<- ctx_zero_unfold in Hcongr.
            simpl in Hcongr.
            do 2 rewrite app_nil_r in Hcongr.
            eassumption.
      - (* local *)
        unfold Progress_HasTypeConf_mind.
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H13.
        right. right.
        destruct (ret_hole_excluded_middle es0).
        + destruct H13 as [n' [ctx' H13]].
          rewrite<- H13.
          invert h.
          eapply return_reduce_extract_vs in H19; eauto.
          2 : { destruct H14; eauto. }
          destruct H19 as [vs' [ctx'' [H30 H31]]].
          rewrite<- H30.
          exists s. exists locs0. exists vs. exists (map Val vs').
          assert (H13 := values_val_map vs').
          rewrite<- (map_length Val vs') in H31.
          assert (Hsimple := red_local_ctx i0 (length taus0) modi vlocs n' ctx'' (map Val vs') slocs H13 H31).
          assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
          assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ 0 (LZero vs []) Hred).
          simpl in Hcongr.
          rewrite app_nil_r in Hcongr.
          exact Hcongr.
        + destruct H5.
          destruct (drop_function_frame_store _ _ _ _ _ _ _ H1 H9 H5) as [H20 H21].
          symmetry in e0.
          assert (forall n (ctx : context n), ctx |[ [Ret] ]| <> es0).
          { intros n ctx contra.
            apply H13.
            exists n. exists ctx. exact contra.
          }
          assert (Forall2 (fun (i : MInst) (C : Module_Ctx) => HasTypeInstance (InstTyp S_rest) i C) (inst s) (InstTyp S)).
          { invert H1.
            rewrite<- app_assoc in H16.
            simpl in H16.
            eapply Forall_app in H16.
            destruct H16.
            invert H18.
            destruct H23.
            rewrite H19 in H14 at 1.
            exact H14.
          }
          destruct (H ltac:(tauto) s slocs S_heap S_whole (size_consts_are_sizes slocs) H20 (conj H21 (HasTypeInstance_SplitStoreTypings _ _ _ _ _ H1 H16)) H15 (br_in_hole_implies_depth_conf _ _ _ _ _ _ _ h)) as [H30 | [H30 | H30]].
          * destruct (forall_e_v _ H30).
            rewrite<- H17.
            exists s. exists locs0. exists vs. exists (map Val x).
            assert (Hsimple := red_local i0 reti modi vlocs (map Val x) slocs (values_val_map x)).
            assert (Hred := StepSimple s locs0 locszs _ _ _ Hsimple).
            assert (Hcongr := CtxCongr _ _ _ _ _ _ _ _ _ (LZero vs []) Hred).
            do 2 rewrite<- ctx_zero_unfold in Hcongr.
            do 2 rewrite app_nil_r in Hcongr.
            eassumption.
          * rewrite H30.
            exists s. exists locs0. exists vs. exists [Local reti modi vlocs slocs [Trap]].
            assert (Hsimple := red_trap modi (LZero [] [])).
            assert (Hred := StepSimple s vlocs slocs _ _ _ Hsimple).
            assert (Hcongr := LocalCongr _ _ locs0 _ _ locszs slocs reti i0 _ [] _ _ Hred).
            assert (Hcongr2 := CtxCongr _ _ _ _ _ _ _ _ _ (LZero vs []) Hcongr).
            eassumption.
          * destruct H30 as [s' [locs' [es' H30]]].
            exists s'. exists locs0. exists vs. exists [Local reti modi locs' slocs es'].
            assert (Hcongr := LocalCongr _ _ locs0 _ _ locszs slocs reti i0 _ [] _ _ H30).
            assert (Hcongr2 := CtxCongr _ _ _ _ _ _ _ _ _ (LZero vs []) Hcongr).
            do 2 rewrite<- ctx_zero_unfold in Hcongr2.
            do 2 rewrite app_nil_r in Hcongr2.
            eassumption.
      - (* malloc *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H13.
        right. right.
        invert H0.
        invert H2.
        rewrite map_empty.
        rewrite app_nil_l.
        invert q0.
        2 : { rewrite nth_error_nil in H14. discriminate. }
        assert (exists l' s', alloc_mem_range s const sz0 H hv = Some (l', s') \/ alloc_mem_range s const sz0 H hv = None).
        destruct (alloc_mem_range s const sz0 H hv); eauto.
        destruct p.
        exists p. exists s0; eauto.
        destruct H13 as [l' [s' [H20 | H20]]].
        + destruct const.
          * exists s'. exists locs0. exists [Mempack (LocP l' Unrestricted) (Ref (LocP l' Unrestricted))]. exists [].
            eapply StepFull.
            eapply red_malloc; simpl; eauto.
          * exists (add_out_set l' s' hv). exists locs0. exists [Mempack (LocP l' Linear) (Ref (LocP l' Linear))]. exists [].
            eapply StepFull.
            eapply red_malloc; simpl; eauto.
        + exists s. exists locs0. exists []. exists [Trap].
          simpl.
          eapply StepFull.
          eapply red_malloc_trap; eauto.
      - (* free *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        clear H12.
        right. right.
        invert H.
        invert H1.
        invert H17.
        simpl.
        invert H16.
        + invert q0.
          2 : {rewrite H5 in H13. rewrite nth_error_nil in H13. discriminate. }
          rewrite H5 in e0.
          eapply QualLeq_Top_Const in e0.
          inversion e0; subst.
          eapply QualLeq_Const_False in H23.
          easy.
        + simpl in H0.
          assert (H100 := nth_error_cons _ x (S :: S_locals)).
          assert (H101 := Singleton_map_get _ _ _ H20).
          assert (H30 := SplitStore_get_heaptype_sub_map _ _ _ _ _ _ H0 H100 H101).
          invert H4.
          unfold typing_valid in H12.
          match goal with
          | [ |- context[LocP ?L _] ] =>
            destruct (H12 L ht) as [H40 H41]
          end.
          destruct (H40 H30) as [hv [n' [S_h' [Ss [H50 [H51 [H52 H53]]]]]]].
          eapply free_spec1 in H51.
          destruct H51 as [mem' H51].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            assert (exists s', free_mem_range s L Linear = Some s')
          end.
          exists (Build_Store (inst s) mem' (out_set s)).
          unfold free_mem_range.
          rewrite H51.
          eauto.
          destruct H14 as [s' H60].
          match goal with
          | [ |- context[LocP ?L _] ] =>
            exists (remove_out_set L s')
          end.
          exists locs0. exists []. exists [].
          simpl.
          eapply StepFull.
          eapply red_free; eauto.
      - (* empty list *)
        unfold Progress_HasTypeInstruction_mind.
        eauto.
      - (* sequencing *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        assert (H200 := H14).
        clear H14.
        invert H1.
        destruct H6.
        destruct (sequence_store _ _ _ _ _ _ _ _ _ _ _ s H2 H10 H5 H6 H14) as [S1' [H20 [H21 [H22 [H23 H24]]]]].
        destruct (H _ _ _ _ locszs taus1 tau2 _ _ _ _ _ (eq_refl _) H20 H3 H4 H22 (conj H23 H24) H7 H8 H9 H21 (sequence_ret_not_in_hole_l _ _ H11) (sequence_br_not_in_hole_l _ _ H12)).
        + exact H13.
        + exact H200.
        + destruct (forall_e_v _ H15).
          destruct H16.
          specialize (locals_value_agnostic _ _ _ _ _ _ _ _ h).
          intros.
          assert (h' : HasTypeInstruction S1 C F L1 (map Val x) (Arrow taus1 tau2) L1).
          { eapply ChangeEndLocalTyp; eauto.
            - eapply HasTypeInstruction_FirstLocalValid; eauto.
            - apply LCEffEqual_sym; auto. }
          destruct (specialize_instruction_value_typing _ _ _ _ _ _ _ _ _ _ _ _ _ H3 h' H2 s) as [Ss [H30 H31]].
          assert (H4' : Forall3 (fun (S' : StoreTyping) (v : Value) '(t, _) => HasTypeValue S' F v t) S_locals locs0 L2).
          { eapply LCEffEqual_Forall3_arg3; eauto. }
          destruct (H0 i0 _ _ _ locszs _ _ _ _ _ _ _ (eq_refl _) H31 H30 H4' H5 (conj H6 H14) H7 H8 H9 H10 (sequence_ret_not_in_hole_r _ _ H11) (sequence_br_not_in_hole_r _ _ H12)).
          * intros.
            match goal with
            | [ H : LCEffEqual _ ?L ?LP,
                H' : nth_error ?LP _ = Some _ |- _ ] =>
              specialize (LCEffEqual_nth_error_right_sigT H H');
              intros; destructAll
            end.
            match goal with
            | [ H : @sigT _ _ |- _ ] => destruct H
            end.
            destructAll.
            match goal with
            | [ H : forall _ _ _, nth_error ?L _ = _ -> _,
                H' : nth_error ?L _ = _ |- _ ] =>
              specialize (H _ _ _ H'); destruct H
            end.
            destructAll.
            repeat match goal with
                   | [ H : size ?F = [], H' : context[size ?F] |- _ ] =>
                     rewrite H in H'
                   end.
            match goal with
            | [ H : size_to_nat ?SZ2 = Some _,
                H' : SizeLeq [] _ ?SZ2 = Some true |- _ ] =>
              specialize (SizeLeq_right_closed_imp_left_closed_sigT _ _ _ H H')
            end.
            intros.
            match goal with
            | [ H : @sigT _ _ |- _ ] => destruct H
            end.
            econstructor; split; eauto.
            match goal with
            | [ H : ?A = Some ?X |- ?A = Some ?Y ] =>
              replace Y with X; auto
            end.
            apply Nat.le_antisymm.
            all: eapply SizeLeq_Const; eauto.
          * exact H200.
          * left.
            rewrite Forall_app.
            eauto.
          * destruct H17; right; right.
            --rewrite H17.
              assert (Hsimple := StepSimple s0 locs0 locszs i0 ((LZero (vs ++ x) [] |[ [Trap] ]|)) [Trap] (red_trap i0 (LZero (vs ++ x) []))).
              rewrite<- ctx_zero_unfold in Hsimple.
              rewrite app_nil_r in Hsimple.
              rewrite map_app in Hsimple.
              rewrite<- app_assoc in Hsimple.
              exists s0. exists locs0. exists []. exists [Trap].
              rewrite map_empty.
              rewrite app_nil_l.
              eassumption.
            --rewrite map_app in H17.
              rewrite<- app_assoc in H17.
              eassumption.
        + destruct H15 as [H30 | H30]; right; right.
          * rewrite H30.
            exists s0. exists locs0. exists []. exists [Trap].
            simpl.
            assert (Hsimple := StepSimple s0 locs0 locszs i0 ((LZero vs [e] |[ [Trap] ]|)) [Trap] (red_trap i0 (LZero vs [e]))).
            rewrite<- ctx_zero_unfold in Hsimple.
            assumption.
          * destruct H30 as [s' [locs' [vs' [es' H30]]]].
            exists s'. exists locs'. exists vs'. exists (es' ++ [e]).
            assert (Hcongr := (CtxCongr s0 s' locs0 locs' locszs i0 (map Val vs ++ es0) (map Val vs' ++ es') 0 (LZero [] [e]) H30)).
            do 2 rewrite<- ctx_zero_unfold in Hcongr.
            rewrite map_empty in Hcongr.
            do 2 rewrite app_nil_l in Hcongr.
            do 2 rewrite<- app_assoc in Hcongr.
            assumption.
      - (* frame rule *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        assert (H200 := H13).
        clear H13.
        invert H0.
        destruct (Forall3_app_split _ _ _ _ _ _ _ _ H2) as [S1 [S2 [vs1 [vs2 [H20 [H21 [H22 H23]]]]]]].
        destruct H20.
        destruct H21.
        destruct H5.
        destruct (drop_values_stores _ _ _ _ _ _ _ _ _ _ H1 H4 H5 H13 H9) as [S_rest' [H31 [H32 [H33 [H34 H35]]]]].
        assert (H30 := H _ _ _ _ locszs _ _ _ _ _ _ _ (eq_refl _) H31 (value_typings_linear _ _ _ _ _ H23) (local_typings_linear _ _ _ _ _ _ H3) H32 (conj H33 H34) (qual_linear _ _ H6) (size_linear _ _ H7) (type_linear _ _ H8) H35 H10 H11).
        destruct H30; eauto; try (destruct F; eauto).
        destruct H14; eauto.
        right. right.
        destruct H14 as [s' [locs' [vs' [es' H40]]]].
        exists s'. exists locs'. exists (vs1 ++ vs'). exists es'.
        assert (Hcongr := CtxCongr s s' locs0 locs' locszs i0 (map Val vs2 ++ es0) (map Val vs' ++ es') 0 (LZero vs1 []) H40).
        do 2 rewrite<- ctx_zero_unfold in Hcongr.
        do 2 rewrite app_nil_r in Hcongr.
        do 2 rewrite map_app.
        do 2 rewrite<- app_assoc.
        assumption.
      - (* ChangeBegLocalTyp *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        eapply H; eauto.
        -- eapply LCEffEqual_Forall3_arg3; eauto.
           apply LCEffEqual_sym; eauto.
        -- intros.
           match goal with
           | [ H : LCEffEqual _ ?L ?LP,
               H' : nth_error ?L _ = Some _ |- _ ] =>
             specialize (LCEffEqual_nth_error_left_sigT H H');
             intros; destructAll
           end.
           match goal with
           | [ H : @sigT _ _ |- _ ] => destruct H
           end.
           destructAll.
           match goal with
           | [ H : forall _ _ _,
                 nth_error ?L _ = Some _ -> _,
               H' : nth_error ?L _ = Some _ |- _ ] =>
             specialize (H _ _ _ H')
           end.
           match goal with
           | [ H : @sigT _ _ |- _ ] => destruct H
           end.
           destructAll.
           eexists; split; [ | eauto ].
           match goal with
           | [ H : size_to_nat ?SZ2 = Some _,
               H' : SizeLeq ?X _ ?SZ2 = Some true,
               H'' : ?X = [] |- _ ] =>
             rewrite H'' in H';
             specialize (SizeLeq_right_closed_imp_left_closed_sigT _ _ _ H H');
             let H0 := fresh "H" in
             intro H0; inversion H0; subst
           end.
           match goal with
           | [ H : ?A = Some ?X |- ?A = Some ?Y ] =>
             replace Y with X; auto
           end.
           apply Nat.le_antisymm.
           all: eapply SizeLeq_Const; eauto.
           destruct F; subst; simpl in *; subst; auto.
      - (* ChangeEndLocalTyp *)
        unfold Progress_HasTypeInstruction_mind.
        intros.
        eapply H; eauto.
      - (* Closure *) eauto.
      - (* Function *) unfold Progress_HasTypeFunc_mind. eauto.
      - (* Conf *)
       unfold Progress_HasTypeInstruction_mind.
       unfold Progress_HasTypeConf_mind.
       intros.
       destruct H0.
        + invert H0.
          rewrite update_empty_fun_ctx_none in H, h0.
          simpl in H.
          invert h.
          assert (H8 : forall i sz typ, nth_error L i = Some (typ, sz) ->
                       {n : nat & size_to_nat sz = Some n /\ nth_error sz_ns i = Some n}).
          { intros.
            assert (H9 := nth_error_unzip _ _ _ _ _ _ _ y H7).
            exact (H1 i1 sz0 H9).
          }
          assert (H7 := H i0 [] locvs s0 sz_ns [] taus0 [] Ss S_heap S S0 (eq_refl _) s (Forall3_nil _) H0 e H3 (eq_refl _) (eq_refl _) (eq_refl _) H2 H4 H5 H8 (eq_refl _)).
          destruct H7; eauto.
          destruct H7; eauto.
          do 4 destruct H7.
          right. right.
          exists x. exists x0. exists (map Val x1 ++ x2).
          eassumption.
        + symmetry in H0.
          destruct H0.
          invert h.
          assert (H8 : forall i sz typ, nth_error L i = Some (typ, sz) ->
                       {n : nat & size_to_nat sz = Some n /\ nth_error sz_ns i = Some n}).
          { intros.
            assert (H9 := nth_error_unzip _ _ _ _ _ _ _ y H6).
            exact (H1 i1 sz0 H9).
          }
          assert (Hloc : Forall3 (fun (S' : StoreTyping) (v : Value) '(t, _) => HasTypeValue S' (update_ret_ctx (Some taus0) empty_Function_Ctx) v t) Ss locvs L ).
          { clear - H0.
            revert Ss locvs H0.
            induction L; intros; invert H0; try eapply Forall3_nil.
            eapply Forall3_cons.
            - destruct a; eapply (HasTypeValue_Function_Ctx _ empty_Function_Ctx); eauto.
            - destruct a; eapply IHL; eauto.
          }
          assert (H7 := H i0 [] locvs s0 sz_ns [] taus0 [] Ss S_heap S S0 (eq_refl _) s (Forall3_nil _) Hloc e H3 (eq_refl _) (eq_refl _) (eq_refl _) H2 H4 H5 H8).
          destruct H7; eauto.
          destruct H6; eauto.
          do 4 destruct H6.
          right. right.
          exists x. exists x0. exists (map Val x1 ++ x2).
          eassumption.
          Unshelve.
          exact (N.of_nat 0). exact s.
  Qed.
    
End Progress.
