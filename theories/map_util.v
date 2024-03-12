(* M.t utilities. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List micromega.Lia Sets.Ensembles Relations.Relations
         Classes.Morphisms FSets.FMapPositive.
Require Import RWasm.EnsembleUtil RWasm.functions RWasm.list_util RWasm.tactics.

Module M := PositiveMap. 

Open Scope Ensembles_scope.

Definition key_set {A : Type} (map : M.t A) :=
  [ set x : positive | match M.find x map with
                           | Some x => True
                           | None => False
                         end ]. 
  
(* [Dom_map] and [Range_map] *)

Definition Range_map {A:Type} sig:  Ensemble A:=
  (fun x => exists y, M.find y sig = Some x).

Definition Dom_map {A:Type} sig : Ensemble (M.key):=
  (fun x => exists (y:A), M.find x sig = Some y).

Lemma Dom_map_empty {A}:
  (Dom_map (M.empty A)) <--> (Empty_set _).
Proof.
  split; intro. intro. inv H. rewrite M.gempty in H0. inv H0.
  intro. inv H.
Qed.

Lemma Dom_map_remove {A:Type} sigma v :
  (Dom_map (@M.remove A v sigma)) <--> (Dom_map sigma \\ [set v]).
Proof.
  split; intros; intro; intros.
  - inv H.
    destruct (BinPos.Pos.eqb_spec x v); subst; eauto.
    + rewrite M.grs in H0. congruence.
    + constructor; eauto.
      rewrite M.gro in H0. eexists; eauto. eassumption. 
      intros Hc. inv Hc. eauto.
  - inv H. inv H0. eexists. rewrite M.gro; eauto.
    intros Hc; subst; sets.
Qed.

Lemma Dom_map_set A (sig: M.t A) x y :
    (Dom_map (M.add x y sig)) <--> (x |: Dom_map sig).
Proof.
  intros. split.
  - intro. intro. inv H.
    destruct (BinPos.Pos.eqb_spec x0 x); subst.
    + rewrite M.gss in H0. inv H0. sets.
    + rewrite M.gso in H0; eauto. right. eexists; eauto.
  - intro. intro.
    destruct (BinPos.Pos.eqb_spec x0 x); subst.
    + eexists. rewrite M.gss. reflexivity.
    + inv H; eauto. inv H0.
      * eexists. rewrite M.gss. reflexivity.
      * inv H0. eexists; eauto. rewrite M.gso; eauto. 
Qed.

Instance Decidable_Dom_map {A} (m : M.t A) : Decidable (Dom_map m).
Proof.
  constructor. intros x.
  destruct (M.find x m) eqn:Heq; eauto.
  left. eexists. eassumption.
  right. intros [y Hget]. congruence.
Qed.


(* N maps *)

Definition get_heaptype {A} (l : N) (ht : M.t A) :=
  M.find (N.succ_pos l) ht.

Definition set_heaptype {A} (l : N) (t : A) (ht : M.t A) :=
  M.add (N.succ_pos l) t ht.

Definition eq_map {t : Type} : relation (M.t t) := 
  fun sub sub' => forall v, get_heaptype v sub = get_heaptype v sub'.

Definition sub_map {A} (map1 map2 : M.t A) :=
  forall x v, get_heaptype x map1 = Some v ->
              get_heaptype x map2 = Some v.


Lemma eq_map_refl t : Reflexive (@eq_map t).
Proof.
  intros; intro; intro; reflexivity.
Qed.
  

Theorem eq_map_sym t: Symmetric (@eq_map t).
Proof.
  intro; intro; intros; intro; auto.
Qed.


Theorem eq_map_trans t: Transitive (@eq_map t).
Proof.
  intros sub sub' sub'' H1 H2 v. unfold eq_map in *.
  rewrite <- H2. eauto. 
Qed.


Lemma eq_map_equiv t : Equivalence (@eq_map t).
Proof.
  constructor.
  eapply eq_map_refl.
  eapply eq_map_sym.
  eapply eq_map_trans. 
Qed.

Lemma remove_empty t x :
  eq_map (M.remove x (M.empty t)) (M.empty t).
Proof.
  unfold eq_map, get_heaptype. intros v.
  rewrite M.gempty. 
  destruct (M.E.eq_dec (N.succ_pos v) x); subst. rewrite M.grs. reflexivity.
  rewrite M.gro; eauto. rewrite M.gempty. reflexivity.
Qed.

Lemma remove_none t x (m : M.t t) :
  M.find x m = None ->
  eq_map (M.remove x m) m. 
Proof.
  intros Hf v. unfold get_heaptype.
  destruct (M.E.eq_dec (N.succ_pos v) x); subst. rewrite M.grs. congruence.
  rewrite M.gro; eauto.
Qed.



Lemma proper_remove t x : Proper (eq_map ==> @eq_map t) (M.remove x).
Proof.
  intros m1 m2 Heq y.
  unfold get_heaptype.
  
  destruct (M.E.eq_dec (N.succ_pos y) x); subst. rewrite !M.grs; reflexivity.

  rewrite !M.gro; eauto.
Qed.


Lemma proper_add t x v : Proper (eq_map ==> @eq_map t) (M.add x v).
Proof.
  intros m1 m2 Heq y.
  unfold get_heaptype.
  
  destruct (M.E.eq_dec (N.succ_pos y) x); subst. rewrite !M.gss; reflexivity.

  rewrite !M.gso; eauto.
Qed.



(* 
Lemma Range_map_remove {A:Type} sigma v :
  Range_map (@M.remove A v sigma) \subset Range_map sigma.
Proof.
  intros. intro. intros. inv H.
  exists x0.
  eapply gr_some.
  apply H0.
Qed.

Lemma not_Range_map_eq {A} sig (x:A) :
  ~ Range_map sig x ->
  ~ (exists z, M.get z sig = Some x).
Proof.
  intros. intro. apply H. inv H0. exists x0; auto.
Qed.

Lemma not_Dom_map_eq {A} (sig:M.t A) x :
    ~ Dom_map sig x ->
    M.get x sig = None.
Proof.
  intro. intros.
  destruct (M.get x sig) eqn:gxs.
  exfalso; apply H. exists a; auto.
  auto.
Qed.

Hint Resolve not_Range_map_eq not_Dom_map_eq : core.

Lemma Range_map_set_list {A} xs (vs : list A) :
    Range_map (set_list (combine xs vs) (M.empty _)) \subset FromList vs.
Proof.
  revert vs; induction xs; intros.
  - simpl. intro.
    intro. inv H. rewrite M.gempty in H0. inv H0.
  - simpl. specialize IHxs. destruct vs. simpl.
    intro; intro; inv H. rewrite M.gempty in H0. inv H0.
    simpl.
    rewrite FromList_cons.
    intro. intro.
    inv H. destruct (peq x0 a).
    subst.
    rewrite M.gss in H0.
    left. inv H0.
    constructor.
    right.
    apply IHxs.
    rewrite M.gso in H0 by auto.
    exists x0. auto.
Qed.


(* TODO move *)
Lemma InList_snd:
  forall {A B} (x:A) (l:list (B*A)),
    List.In x (map snd l) <-> exists v, List.In (v, x) l.
Proof.
  induction l; intros.
  - split; intro H; inv H.
    inv H0.
  - split.
    + intro. destruct a.
      simpl in H. inv H.
      exists b; constructor; auto.
      apply IHl in H0. inv H0. exists x0.
      constructor 2. auto.
    + intro. inv H.
      destruct a. simpl.
      inv H0.
      inv H; auto.
      right.
      apply IHl; eauto.
Qed.

Lemma Decidable_Range_map :
  forall sig, @Decidable positive (Range_map sig).
Proof.
  intros. constructor.
  intro.
  assert (Decidable (FromList (map snd (M.elements sig)))).
  apply Decidable_FromList.
  inv H.
  specialize (Dec x).
  inv Dec.
  unfold FromList in H.
  left. rewrite InList_snd in H.
  destruct H.
  apply M.elements_complete in H.
  exists x0; auto.
  right. intro. inv H0.
  apply H.
  apply InList_snd.
  exists x0. apply M.elements_correct. auto.
Qed.

Lemma Range_set_Included {A} (sig : M.t A) a b :
  ~ a \in Dom_map sig ->
          Range_map sig \subset Range_map (M.set a b sig).
Proof.
  intros Hc x [y Hget]. exists y. rewrite M.gso. eassumption.
  intros Hc'; subst. eapply Hc; eexists; eauto.
Qed.

Lemma Range_set_list_Included {A} (sig : M.t A) l1 l2 :
  Disjoint _ (FromList l1) (Dom_map sig) ->
  NoDup l1 ->
  length l1 = length l2 ->
  Range_map sig \subset Range_map (set_list (combine l1 l2) sig).
Proof.
  revert l2; induction l1; intros; simpl. reflexivity.
  destruct l2; simpl. now sets. normalize_sets.
  eapply Included_trans; [| eapply Range_set_Included; sets ]. simpl.
  eapply IHl1. now sets. inv H0; eassumption.
  inv H1. reflexivity. inv H1. inv H0. rewrite (Dom_map_set_list sig l1 l2); eauto.
  intros Hc; inv Hc; eauto. eapply H. constructor; eauto.
Qed.    

Lemma range_map_set_list {A} (ly : list A) sig lx :
  Range_map (set_list (combine lx ly) sig) \subset (Range_map sig :|: FromList ly).
Proof.
  revert lx; induction ly.
  - intros. intro. intro. destruct lx; simpl in H; auto.
  - intros. destruct lx. simpl. auto with Ensembles_DB.
    simpl. intro. intro.
    inv H. destruct (peq x0 e).
    + subst. rewrite M.gss in H0. inv H0. right; constructor; auto.
    + rewrite M.gso in H0 by auto.
      assert ( Range_map (set_list (combine lx ly) sig) x). exists x0; auto.
      apply IHly in H.
      inv H; auto. right. constructor 2; auto.
Qed.

*) 

Definition Dom_ht {A} (ht : M.t A) := [ set l | (N.succ_pos l \in Dom_map ht) ]. 

Lemma Dom_ht_empty A:
  Dom_ht (M.empty A) <--> Empty_set _.
Proof.
  unfold Dom_ht. split; [ | now sets ].
  intros x H1. unfold In in *. simpl in H1.
  eapply Dom_map_empty in H1. inv H1.
Qed.

Lemma Dom_ht_is_empty {A} (H : M.t A) :
  M.is_empty H = true ->
  Dom_ht H <--> Empty_set _.
Proof.
  intros Hemp. unfold Dom_ht. split; [ | now sets ].
  intros x H1. unfold In in *. eapply PositiveMap.is_empty_2 in Hemp.
  inv H1. exfalso. eapply Hemp. eassumption.
Qed.

Lemma gis_empty A (Hemp : M.t A) x : 
  M.is_empty Hemp = true ->
  M.find x Hemp = None.
Proof.
  intros Heq.
  eapply M.Empty_alt.
  eapply PositiveMap.is_empty_2. eassumption.
Qed. 


(* [sub_map] lemmas *) 


Lemma sub_map_set {A} rho x (v : A) :
  ~ x \in Dom_map rho ->
          sub_map rho (M.add x v rho).
Proof.
  unfold sub_map, get_heaptype. intros Hnin z1 v1 Hget1. rewrite M.gso; eauto.
  intros hc. subst. eapply Hnin. eexists; eauto.
Qed.

Lemma sub_map_trans {A} (rho1 rho2 rho3 : M.t A) :
  sub_map rho1 rho2 ->
  sub_map rho2 rho3 ->
  sub_map rho1 rho3.
Proof.
  intros H1 H2 x v Hget. eauto.
Qed.

Lemma sub_map_refl {A} (rho : M.t A) :
  sub_map rho rho.
Proof.
  intro; intros; eauto.
Qed.


Lemma Dom_map_sub_map {A : Type} (rho1 rho2 : M.t A) :
  sub_map rho1 rho2 ->
  Dom_ht rho1 \subset Dom_ht rho2.
Proof.
  intros H1 x [y Hin].
  eapply H1 in Hin.
  eexists; eauto.
Qed.


Lemma Empty_eq_map A (S1 S2 : M.t A) :
  eq_map S1 S2 ->
  M.Empty S1 ->
  M.Empty S2.
Proof.
  intros Heq He. intros x v Hmt1.
  unfold M.MapsTo in *. 
  unfold eq_map, get_heaptype in *.

  
  assert (H : forall p, exists n, p = N.succ_pos n).
  { clear. intros p.
    destruct p.
    + exists (2 * (N.pos p))%N. reflexivity.
    + exists (2 * N.pos p - 1)%N. simpl. lia. 
    + exists 0%N. reflexivity. }
  
  specialize (H x). destruct H as [n H]. specialize (Heq n). subst.
  eapply He. unfold M.MapsTo. 
  rewrite <- Heq in Hmt1. eassumption.
Qed.


Lemma is_empty_eq_map A (S1 S2 : M.t A) :
  eq_map S1 S2 ->
  M.is_empty S1 = M.is_empty S2. 
Proof.
  intros Heq. 
  destruct (M.is_empty S1) eqn:Heq1;
    destruct (M.is_empty S2) eqn:Heq2; eauto.

  + eapply PositiveMap.is_empty_2 in Heq1.
    eapply Empty_eq_map in Heq; eauto.     
    eapply PositiveMap.is_empty_1 in Heq. congruence.

  + eapply PositiveMap.is_empty_2 in Heq2.
    eapply eq_map_sym in Heq.
    eapply Empty_eq_map in Heq; eauto.     
    eapply PositiveMap.is_empty_1 in Heq. congruence.
Qed. 

