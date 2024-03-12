From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive FSets.FMapFacts micromega.Lia Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.map_util
        RWasm.typing_util RWasm.tactics RWasm.list_util RWasm.EnsembleUtil
        RWasm.splitting RWasm.surface RWasm.typing RWasm.hti_subst_indices RWasm.progress RWasm.preservation RWasm.misc_util.

Theorem sub_0_r: forall n, n - 0 = n. Proof. lia. Qed.

Ltac some := right; intro; inversion H.

Lemma eq_dec_N : forall (a b : N), (a = b) \/ (a <> b).
Proof.
  intros. destruct a; destruct b; auto.
  - right. intro. inversion H.
  - right. intro. inversion H.
  - specialize (eq_dec_positive p p0).
    intros. destruct H.
    left. subst. auto.
    right. intro. apply H. inversion H0. auto.
 Qed.
  
Lemma forall2_map : forall {A B} (l1 : list A) (f : A -> B) P,
  Forall2 P (map f l1) l1 <->
  (forall x, In x l1 -> P (f x) x).
Proof.
  split.
  - induction l1; intros; inversion H0; subst.
    inversion H. subst. auto.
    eapply IHl1; eauto. inversion H. subst. auto.
  - apply Forall2_map_l_strong.
Qed.

Lemma Forall3_snoc : forall {A B C} {P : A -> B -> C -> Prop} {l1 l2 l3 el1 el2 el3},
    Forall3 P (l1 ++ [el1]) (l2 ++ [el2]) (l3 ++ [el3]) <->
    Forall3 P l1 l2 l3 /\ P el1 el2 el3.
Proof.
  intros.
  constructor; rewrite Forall3_forall.
  - intros; destructAll.
    repeat match goal with
           | [ H : context[length (_ ++ [_])] |- _ ] =>
             rewrite snoc_length in H
           end.
    repeat match goal with
           | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
             inversion H; subst; simpl in *; clear H
           end.
    rewrite Forall3_forall.
    split; [ split; auto | ].
    -- intros.
       match goal with
       | [ H : forall _ _ _ _, _ |- _ ] => eapply H
       end.
       all: rewrite nth_error_app1.
       all: eauto.
       all: eapply nth_error_Some_length; eauto.
    -- match goal with
       | [ H : forall _ _ _ _, _ |- _ ] => eapply H
       end.
       all: rewrite nth_error_app2.
       all: try rewrite Nat.sub_diag.
       all: simpl; auto.
       all:
         try match goal with
             | [ H : ?A = _ |- context[?A] ] =>
               rewrite H
             end.
       all: try rewrite Nat.sub_diag.
       all: simpl; auto.
       all:
         try match goal with
             | [ H : ?A = _ |- context[?A] ] =>
               rewrite H
             end.
       all: try rewrite Nat.sub_diag.
       all: simpl; auto.
       all: apply Nat.eq_le_incl; auto.
  - intros.
    destructAll.
    rewrite Forall3_forall; split;
      [ | repeat rewrite snoc_length; auto ].
    intros.
    match goal with
    | [ H : nth_error (?L ++ _) ?IDX = Some _ |- _ ] =>
      specialize (Nat.lt_ge_cases IDX (length L))
    end.
    let H := fresh "H" in intro H; case H; intros.
    -- rewrite nth_error_app1 in *.
       all: auto.
       all:
         repeat match goal with
                | [ H : ?A = _ |- context[?A] ] => rewrite H; auto
                end.
       eauto.
    -- rewrite nth_error_app2 in *.
       all: auto.
       all:
         repeat match goal with
                | [ H : ?A = _ |- context[?A] ] => rewrite H; auto
                end.
       all:
         match goal with
         | [ H : ?A = ?B, H' : ?B = ?C,
             H'' : context[_ - ?A],
	         H''' : context[_ - ?B],
             H'''' : context[_ - ?C] |- _ ] =>
           rewrite <-H' in H'''';
           rewrite <-H in H'''';
           rewrite <-H in H'''
         end.
       all:
         match goal with
         | [ H : context[?N1 - ?N2] |- _ ] =>
           remember (N1 - N2) as n; destruct n; simpl in *
         end.
       2:{
         match goal with
         | [ H : nth_error [] ?IDX = Some _ |- _ ] =>
           destruct IDX; simpl in *; inversion H
         end.
       }
       repeat match goal with
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; subst; simpl in *; clear H
              end.
       auto.
Qed.

Lemma forall3_nth_error_args3 : forall {A B C P l1 l2 l3 j v3},
    Forall3 P l1 l2 l3 ->
    @nth_error C l3 j = Some v3 ->
    exists v1 v2,
      @nth_error A l1 j = Some v1 /\
      @nth_error B l2 j = Some v2 /\
      P v1 v2 v3.
Proof.
  intros.
  match goal with
  | [ H : Forall3 _ _ _ _ |- _ ] => rewrite Forall3_forall in H
  end.
  destructAll.
  match goal with
  | [ H : length ?A = length ?B,
      H' : nth_error ?B ?IDX = Some _ |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : exists y, nth_error A IDX = Some y);
    [ apply nth_error_some_exists; rewrite H | ]
  end.
  { eapply nth_error_Some_length; eauto. }
  destructAll.
  match goal with
  | [ H : length ?A = length ?B,
      H' : nth_error ?B ?IDX = Some _,
      H'' : length ?B = length ?C,
      H''' : nth_error ?C ?IDX = Some _ |- _ ] =>
    let H0 := fresh "H" in
    assert (H0 : exists y, nth_error A IDX = Some y);
    [ apply nth_error_some_exists; rewrite H | ]
  end.
  { eapply nth_error_Some_length; eauto. }
  destructAll.
  do 2 eexists; eauto.
Qed.

Lemma forall3_nth_error_args23 : forall {A B C P l1 l2 l3 j v2 v3},
    Forall3 P l1 l2 l3 ->
    @nth_error B l2 j = Some v2 ->
    @nth_error C l3 j = Some v3 ->
    exists v1,
      @nth_error A l1 j = Some v1 /\
      P v1 v2 v3.
Proof.
  intros.
  generalize dependent l1. generalize dependent l2.
  generalize dependent j.
  induction l3; intros.
  - destruct j; discriminate H1.
  - destruct j.
    + inversion H. subst.
      injection H0. injection H1. intros. subst.
      simpl. eexists. split; eauto.
    + inversion H. subst. simpl.
      eapply IHl3; eauto.
Qed.

Lemma forall2_args_1 : forall {A B} (P : A -> B -> Prop) L1 L2 i v1,
    Forall2 P L1 L2 ->
    nth_error L1 i = Some v1 ->
    exists v2,
      nth_error L2 i = Some v2 /\
      P v1 v2.
Proof.
  induction L1; intros; destruct i.
  - discriminate H0.
  - discriminate H0.
  - injection H0 as h. inversion H. subst.
    exists y. split; auto.
  - destruct L2; inversion H; subst.
    simpl. eapply IHL1; auto.
Qed.

Lemma forall2_args_2 : forall {A B} (P : A -> B -> Prop) L1 L2 i v2,
    Forall2 P L1 L2 ->
    nth_error L2 i = Some v2 ->
    exists v1,
      nth_error L1 i = Some v1 /\
      P v1 v2.
Proof.
  intros.
  generalize dependent L1. generalize dependent i. generalize dependent v2.
  induction L2; intros; destruct i.
  - discriminate H0.
  - discriminate H0.
  - injection H0 as h. inversion H. subst.
    exists x. split; auto.
  - destruct L1; inversion H; subst.
    simpl. eapply IHL2; auto.
Qed.

Lemma forall2_map_eq : forall {A B C} {f : A -> C} {g : B -> C} {l1 l2},
    Forall2 (fun v1 v2 => f v1 = g v2) l1 l2 ->
    map f l1 = map g l2.
  Proof.
    intros A B C f g l1.
    induction l1; intros; destruct l2; inversion H; subst; eauto; simpl.
    f_equal; eauto.
  Qed.

Lemma Forall2_common_logic : forall {A B P l1 l2} {f1 : A -> A} {f2 : B -> B},
    Forall2 P l1 l2 ->
    (forall el1 el2,
        In el1 l1 ->
        In el2 l2 ->
        P el1 el2 ->
        P (f1 el1) (f2 el2)) ->
    Forall2 P (map f1 l1) (map f2 l2).
Proof.
  intros.
  apply forall2_nth_error_inv.
  2:{
    rewrite map_length.
    rewrite map_length.
    eapply Forall2_length; eauto.
  }
  intros.
  repeat match goal with
         | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
           apply nth_error_map_inv in H; destructAll
         end.
  match goal with
  | [ H : forall _ _, _ |- _ ] => apply H
  end.
  1-2: eapply nth_error_In; eauto.
  eapply forall2_nth_error; eauto.
Qed.

Lemma Forall_map_eq : forall {A} {l : list A} {f},
    Forall (fun el => f el = el) l ->
    map f l = l.
  Proof.
    intros.
    induction l; intros; inversion H; subst; auto; simpl.
    f_equal; eauto.
  Qed.

Theorem Permutation_comm: forall {T} (l1 l2: list T),
    Permutation.Permutation l1 l2 <-> Permutation.Permutation l2 l1.
  Proof.
    intros.
    split; intros; induction H; eauto.
    - eapply Permutation.perm_swap.
    - eapply Permutation.perm_trans; eauto.
    - eapply Permutation.perm_swap.
    - eapply Permutation.perm_trans; eauto.
  Qed.

Lemma split_map : forall {A B C D f} {f1 : A -> C} {f2 : B -> D} {l l1 l2},
    Forall (fun '(a, b) => f (a, b) = (f1 a, f2 b)) l ->
    split l = (l1, l2) ->
    split (map f l) = (map f1 l1, map f2 l2).
Proof.
  induction l; intros; simpl in *.
  - match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; subst
    end.
    simpl; auto.
  - match goal with
    | [ F : _ * _ -> _, X : _ * _ |- _ ] =>
      remember (F X) as obj;
      generalize (eq_sym Heqobj); case obj; intros;
      destruct X
    end.
    match goal with
    | [ X : list (_ * _) |- _ ] =>
      remember (split X) as obj2; destruct obj2; intros
    end.
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Forall _ (_ :: _) |- _ ] =>
      inversion H; subst; simpl in *
    end.
    match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inversion H'; subst
    end.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
Qed.

Lemma split_nth_error_inv1 : forall {A B} {idx el lp} {l1 : list A} {l2 : list B},
    split lp = (l1, l2) ->
    nth_error l1 idx = Some el ->
    exists el', nth_error lp idx = Some (el, el').
Proof.
  induction idx.
  - intros.
    destruct l1; simpl in *.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst
    end.
    destruct lp; simpl in *.
    1:{
      match goal with
      | [ H : (_, _) = (_, _) |- _ ] => inversion H
      end.
    }
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    match goal with
    | [ H : context[split ?L] |- _ ] =>
      remember (split L) as obj; destruct obj; intros
    end.
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; subst
    end.
    eexists; eauto.
  - intros.
    destruct l1; simpl in *.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    destruct lp; simpl in *.
    1:{
      match goal with
      | [ H : (_, _) = (_, _) |- _ ] => inversion H
      end.
    }
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    match goal with
    | [ H : context[split ?L] |- _ ] =>
      remember (split L) as obj; destruct obj; intros
    end.
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
Qed.

Lemma Dom_ht_one_loc : forall A loc ht ht',
    Dom_ht (map_util.M.add loc ht (map_util.M.empty A))
    <-->
    Dom_ht (map_util.M.add loc ht' (map_util.M.empty A)).
Proof.
  intros.
  unfold Dom_ht.
  unfold Dom_map.
  unfold Ensembles.Same_set.
  unfold Ensembles.Included.
  unfold Ensembles.In.
  constructor; intros; destructAll.
  all:
    match goal with
    | [ H : map_util.M.find ?L1 (map_util.M.add ?L2 _ _) = _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : L1 = L2 \/ L1 <> L2) by apply eq_dec_positive;
      case H'; intros; subst
    end.
  1,3: rewrite M.gss; eexists; eauto.
  all: rewrite M.gso in *; auto.
  all: rewrite M.gempty in *.
  all:
    match goal with
    | [ H : None = Some _ |- _ ] => inversion H
    end.
Qed.

Definition is_linear m :=
  match m with
  | Linear => true
  | _ => false                     
  end.

Module PreservationFull (M : Memory) (T : MemTyping M).
  Import M T Utils.
  Module Red := Reduction M T.
  Module F := FMapFacts.Properties map_util.M.
  Import Red F.

  Definition remove_heaptype (l : Ptr) (ht : HeapTyping) :=
    M.remove (N.succ_pos l) ht.

  Definition remove_loc (S : StoreTyping) (l : Ptr) (m : QualConstant) :=
    let (mi, ht_l, ht_u) := S in 
    match m with
    | Unrestricted =>
      Build_StoreTyping mi ht_l (remove_heaptype l ht_u)
    | Linear =>
      Build_StoreTyping mi (remove_heaptype l ht_l) ht_u
    end.

  Lemma update_unr_empty_lintyp_swap U S :
    update_unr U (empty_LinTyp S) = empty_LinTyp (update_unr U S).
  Proof.
    destruct S; unfold update_unr; simpl; congruence.
  Qed.

  Lemma free_mem_range_inst s l qc s' :
    free_mem_range s l qc = Some s' ->
    inst s = inst s'.
    Proof.
      intro h.
      unfold free_mem_range in h.
      case (free l qc (meminst s)) eqn:Eq.
      - injection h as h1.
        destruct h1. simpl.
        reflexivity.
      - inversion h.
  Qed.

  Lemma subst_subst'_types_app S l1 l2 :
    subst.subst'_types S (l1 ++ l2) =
    subst.subst'_types S l1 ++ subst.subst'_types S l2.
  Proof.
    generalize dependent l2. induction l1; intros; eauto.
    simpl. f_equal.
    eapply IHl1.
  Qed.
  
  Lemma split_set_localtype  idx t sz l l1 l2:
    split l = (l1, l2) ->
    split (set_localtype idx t sz l) =
    ((set_nth l1 idx t), (set_nth l2 idx sz)).
  Proof.
    intros.
    generalize dependent l1.
    generalize dependent l2.
    generalize dependent idx.
    induction l; intros.
    - injection H as h. subst.  auto.
    - destruct a. destruct idx.
      + simpl. simpl in H. destruct (split l).
        injection H as h. subst. f_equal.
      + simpl. simpl in H. destruct (split l).
        injection H as h. subst. simpl. rewrite Nat.sub_0_r.
        destruct (split (nth_upd l idx (t, sz))) eqn:Eq.
        specialize (IHl idx  l3 l0).
        unfold set_localtype in IHl.
        rewrite Eq in IHl.
        injection IHl as h. subst.
        f_equal. auto.
        intros. auto.
        auto.
  Qed.
  
  Lemma set_localtype_nth_error : forall L idx t sz,
      nth_error L idx = Some (t, sz) ->
      set_localtype idx t sz L = L.
  Proof.
    intros.
    generalize L H.
    clear L H.
    elim idx.
    - intros L.
      simpl.
      case L.
      -- unfold set_localtype.
         unfold nth_upd.
         auto.
      -- intros pr l.
         destruct pr.
         unfold set_localtype.
         simpl.
         intros Heq.
         inversion Heq.
         subst.
         auto.
    - intros n IH L.
      simpl.
      case L.
      -- intros Heq.
         inversion Heq.
      -- intros pr l.
         destruct pr.
         intros H.
         unfold set_localtype.
         simpl.
         unfold set_localtype in IH.
         rewrite IH; auto.
  Qed.

  Lemma leq_unrestricted_imp_eq_unrestricted : forall {pt},
      QualLeq [] pt Unrestricted = Some true ->
      pt = Unrestricted.
  Proof.
    intros.
    specialize (QualLeq_Empty_Ctx _ _ H).
    intros; destructAll.
    destruct H0; auto.
    destruct H0; auto.
    inversion H0.
  Qed.

  Lemma eq_map_empty : forall T m1 m2,
      M.is_empty m1 = true ->
      M.is_empty m2 = true ->
      @eq_map T m1 m2.
  Proof.
    intros.
    unfold eq_map. intros.
    rewrite get_heaptype_empty; auto.
    rewrite get_heaptype_empty; auto.
  Qed.

  Lemma nth_error_split : forall {A B} idx l (l1 : list A) (l2 : list B) v1 v2,
      split l = (l1, l2) ->
      nth_error l idx = Some (v1, v2) ->
      nth_error l1 idx = Some v1 /\ nth_error l2 idx = Some v2.
  Proof.
    intros A B idx l. generalize dependent idx.
    induction l; intros.
    - destruct idx; discriminate H0.
    - destruct a. simpl in H. destruct (split l) eqn:Eq.
      injection H as H'. subst.
      destruct idx.
      + injection H0 as h. subst. split; auto.
      + simpl in H0. simpl.
        apply IHl. auto. auto.
  Qed.

  Lemma length_set_nth : forall {A} (l : list A) (j : nat) (v : A),
        length (set_nth l j v) = length l.
    Proof.
      intros A l. induction l; intros; destruct j; simpl; auto.
    Qed.

  Lemma set_nth_app : forall {A} (l1 : list A) l2 idx v,
      idx < length l1 ->
      set_nth l1 idx v ++ l2 = set_nth (l1 ++ l2) idx v.
    Proof.
      intros A l1. induction l1; intros; destruct idx; inversion H; subst;
        simpl in *; eauto; f_equal; rewrite sub_0_r; eauto.
      rewrite IHl1. auto. lia. rewrite IHl1. auto. lia.
    Qed.

  Lemma set_nth_app2 : forall {A} {l1 : list A} {l2 idx el},
      l1 ++ set_nth l2 idx el =
      set_nth (l1 ++ l2) (length l1 + idx) el.
    Proof.
      intros A l1. induction l1; intros; simpl; auto.
      f_equal. simpl. rewrite IHl1. rewrite sub_0_r. auto.
    Qed.

  Lemma forallb_set_nth : forall {A} {l : list A} {f} {idx} {el},
      forallb f l = true ->
      f el = true ->
      forallb f (set_nth l idx el) = true.
    Proof.
      intros A l. induction l; intros; destruct idx; simpl; auto; inversion H; subst.
      apply andb_prop in H2. destruct H2. rewrite H1. rewrite H0. auto.
      apply andb_prop in H2. destruct H2. rewrite H1. rewrite IHl; auto.
    Qed.
  
  Lemma set_nth_combine_first_comp : forall {A B} {l1 : list A} {l2 : list B} {idx el1 el2},
      nth_error l2 idx = Some el2 ->
      combine (set_nth l1 idx el1) l2 =
      set_nth (combine l1 l2) idx (el1, el2).
    Proof.
      intros A B l1.
      induction l1; intros; auto; simpl; destruct idx; destruct l2; simpl; auto; inversion H;
        subst;  f_equal; auto.
      rewrite sub_0_r. eauto.
   Qed.

  Lemma set_nth_In : forall {A} {l : list A} {el} {idx},
      idx < length l ->
      In el (set_nth l idx el).
    Proof.
      intros A l.
      induction l; intros; destruct idx; inversion H; subst; simpl in *; eauto;
        right; auto; rewrite sub_0_r; apply IHl; lia.
    Qed.

  Lemma set_nth_nth_error : forall {A} l idx (o : A),
      nth_error l idx = Some o ->
      l = set_nth l idx o.
  Proof.
    induction l; intros; auto.
    destruct idx.
    - simpl in H. injection H as h. subst. auto.
    - simpl in H. simpl.
      f_equal;auto.
      apply IHl. rewrite Nat.sub_0_r. auto.
  Qed.

  Lemma set_nth_map: forall {T U} l j (f: T -> U) x,
      map f (set_nth l j x) = (set_nth (map f l) j (f x)).
  Proof.
    intros. generalize dependent j.
    induction l; intros; auto.
    destruct j; auto.
    simpl.
    f_equal; auto.
  Qed.
                    
  Lemma Forall_set_nth : forall {A} (P : A -> Prop) l1 idx a,
      Forall P l1 ->
      P a ->
      Forall P (set_nth l1 idx a).
  Proof.
    induction l1; intros; auto.
    destruct idx; inversion H; subst.
    - apply Forall_cons; auto.
    - simpl. rewrite Nat.sub_0_r. apply Forall_cons; auto.
  Qed.

  Lemma Forall2_set_nth : forall {A B} (P : A -> B -> Prop) l1 l2 idx a b,
      Forall2 P l1 l2 ->
      P a b ->
      Forall2 P (set_nth l1 idx a) (set_nth l2 idx b).
  Proof.
    intros.
    generalize dependent l2. generalize dependent idx.
    induction l1; intros; inversion H; subst; simpl; auto.
    destruct idx.
    - simpl. apply Forall2_cons; auto.
    - simpl. apply Forall2_cons; auto.
  Qed.

  Lemma forall2_set_nth : forall {A B} (P : A -> B -> Prop) L1 L2 i v1 v2,
      Forall2 P L1 L2 ->
      nth_error L2 i = Some v2 ->
      P v1 v2 ->
      Forall2 P (set_nth L1 i v1) L2.
  Proof.
    intros.
    generalize dependent i.
    induction H; intros; simpl; auto.
    destruct i; simpl.
    - injection H2 as h. subst.
      apply Forall2_cons; auto.
    - simpl in H2. rewrite Nat.sub_0_r. apply Forall2_cons; auto.
  Qed.

  Lemma Forall3_set_nth : forall {A B C} (P : A -> B -> C -> Prop) l1 l2 l3 idx a b c,
      Forall3 P l1 l2 l3 ->
      P a b c ->
      Forall3 P (set_nth l1 idx a) (set_nth l2 idx b) (set_nth l3 idx c).
  Proof.
    induction l1; intros; inversion H; subst; auto.
    destruct idx; simpl; apply Forall3_cons; auto.
  Qed.

  Lemma ReplaceAtIdx_nth_error : forall {A} idx (lold : list A) tnew lnew told,
      ReplaceAtIdx idx lold tnew = Some (lnew, told) ->
      lnew = set_nth lold idx tnew.
  Proof.
    induction idx; intros.
    - destruct lold. discriminate H.
      injection H as h. subst. auto.
    - destruct lold. discriminate H.
      simpl in H. rewrite Nat.sub_0_r in H.
      destruct (ReplaceAtIdx idx lold tnew) eqn:Eq.
      + simpl. rewrite Nat.sub_0_r. destruct p.
        injection H as h. subst. f_equal. eapply IHidx. eauto.
      + discriminate H.
  Qed.

  Lemma ReplaceAtIdx_old_nth_error : forall {A} {idx : nat} {lold : list A} {tnew : A} {lnew : list A} {told : A},
        ReplaceAtIdx idx lold tnew = Some (lnew, told) ->
        nth_error lold idx = Some told.
    Proof.
      intros A idx lold.
      revert idx. induction lold; intros; simpl in *; destruct idx; inversion H; subst;
        simpl in *; auto.
      rewrite sub_0_r in *.

      destruct (ReplaceAtIdx idx lold tnew) eqn:Eq.
      - destruct p. injection H as h. subst.
        eapply IHlold. eauto.
      - inversion H.
    Qed.
  
  Lemma ReplaceAtIdx_no_change : forall {A l1 l2 i e},
      @ReplaceAtIdx A i l1 e = Some (l2, e) ->
      l1 = l2.
  Proof.
    intros.
    generalize dependent l1. generalize dependent l2.
    induction i; intros; destruct l1; destruct l2; auto; try discriminate H.
    - injection H as h. subst. auto.
    - simpl in H. rewrite Nat.sub_0_r in H.
      destruct (ReplaceAtIdx i l1 e) eqn:Eq.
      destruct p. discriminate H. discriminate H.
    - simpl in H. rewrite Nat.sub_0_r in H.
      destruct (ReplaceAtIdx i l1 e) eqn:Eq.
      + destruct p. injection H as h. subst.
        f_equal. auto.
      + discriminate H.
  Qed.

  Lemma Forall_Permutation_lst : forall {A l1 l2} (P : A -> Prop),
    Permutation.Permutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
  Proof.
    intros. induction H; auto.
    inversion H0; subst.
    - apply Forall_cons; auto.
    - inversion H0; subst. inversion H3; subst.
      apply Forall_cons; auto.
  Qed.

  Lemma forall2_to_func : forall {A B} (eq_dec : forall r1 r2 : A, {r1 = r2} + {r1 <> r2}) (l1 : list A) (l2 : list B) P,
        B ->
        Forall2 P l2 l1 ->
        NoDup l1 ->
        exists f, l2 = map f l1 /\ forall x, In x l1 -> P (f x) x.
  Proof.
    induction l1; intros.
    - inversion H. subst.
      match goal with
      | [ X : B |- _ ] => exists (fun _ => X)
      end.      
      split; eauto.
      intros. inversion H1.
    - inversion H. subst. inversion H0. subst.
      specialize (IHl1 l P X H5 H6).
      destruct IHl1. destruct H1.
      + simpl.
        exists (fun a' => if eq_dec a a' then x else x0 a').
        remember (eq_dec a a) as obj; revert Heqobj; case obj;
          [ | intros; exfalso; eauto ].
        intros.
        split.
        -- match goal with
           | [ |- _ :: ?A = _ :: ?B ] =>
             let H := fresh "H" in
             assert (H : A = B); [ | rewrite H; auto ]
           end.
           match goal with
           | [ H : ?A = _ |- context[?A] ] => rewrite H
           end.
           apply map_ext_in.
           intros.
           case (eq_dec a a0); intros; subst.
           --- exfalso; eauto.
           --- auto.
        -- intros.
           match goal with
           | [ H : _ \/ _ |- _ ] => case H; intros; subst
           end.
           --- generalize (eq_dec x1 x1).
               let H := fresh "H" in intro H; case H; intros; subst.
               ---- auto.
               ---- exfalso; eauto.
           --- generalize (eq_dec a x1).
               let H := fresh "H" in intro H; case H; intros; subst.
               ---- auto.
               ---- eauto.
  Qed.

  Lemma eq_dec_loc : forall r1 r2 : term.Loc,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; case r1; intros; case r2; intros.
    2,3: right; intro H; inversion H; subst; eauto.
    - specialize (OrderedTypeEx.Nat_as_OT.eq_dec v v0).
      intro H; case H; intros; subst.
      -- left; eauto.
      -- right; intro H'; inversion H'; subst; eauto.
    - specialize (OrdersEx.N_as_OT.eq_dec p p0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (qualconstr_eq_dec q q0).
      intro H'; case H'; intros; subst; [ left; eauto | ].
      right; intro H''; inversion H''; subst; eauto.
  Qed.

  Lemma eq_dec_qual : forall r1 r2 : Qual,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; case r1; intros; case r2; intros.
    2,3: right; intro H; inversion H; subst; eauto.
    - specialize (OrderedTypeEx.Nat_as_OT.eq_dec v v0).
      intro H; case H; intros; subst.
      -- left; eauto.
      -- right; intro H'; inversion H'; subst; eauto.
    - specialize (qualconstr_eq_dec q q0).
      intro H; case H; intros; subst.
      -- left; eauto.
      -- right; intro H'; inversion H'; subst; eauto.
  Qed.

  Lemma eq_dec_kv : forall r1 r2 : KindVar,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; case r1; intros; case r2; intros.
    2-5,7-10,12-15: right; intro H; inversion H; subst; eauto.
    - left; eauto.
    - specialize (list_eq_dec eq_dec_qual l l1).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (list_eq_dec eq_dec_qual l0 l2).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - specialize (list_eq_dec eq_dec_size l l1).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (list_eq_dec eq_dec_size l0 l2).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - specialize (eq_dec_size s s0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (eq_dec_qual q q0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      case h; intros; case h0; intros.
      2-3: right; intro H''; inversion H''; subst; eauto.
      all: left; eauto.
  Qed.    

  Lemma list_eq_dec_Forall_type : forall {A} (l1 : list A) l2,
      Forall_type
        (fun r1 => forall r2, {r1 = r2} + {r1 <> r2}) l1 ->
      {l1 = l2} + {l1 <> l2}.
  Proof.
    induction l1.
    - intros; simpl in *.
      destruct l2.
      -- left; eauto.
      -- right; intro H'; inversion H'.
    - intros.
      inversion X; subst; simpl in *.
      destruct l2; [ right; intro H'; inversion H' | ].
      specialize (IHl1 l2 X1).
      case IHl1; intros.
      -- specialize (X0 a0).
         case X0; intros; subst.
         --- left; eauto.
         --- right; intro H''; inversion H''; subst; eauto.
      -- right; intro H''; inversion H''; subst; eauto.
  Qed.

  Lemma eq_dec_Pre_Typ_Fun_Arrow_Heap :
    (forall p1 : Pretype,
        (fun p => (forall p2, {p = p2} + {p <> p2})) p1) *
    (forall q1 : Typ,
        (fun q => (forall q2, {q = q2} + {q <> q2})) q1) *
    (forall f1 : FunType,
        (fun f => (forall f2, {f = f2} + {f <> f2})) f1) *
    (forall h1 : HeapType,
        (fun h => (forall h2, {h = h2} + {h <> h2})) h1) *
    (forall a1 : ArrowType,
        (fun a => (forall a2, {a = a2} + {a <> a2})) a1).
  Proof.
    match goal with
    | [ |- (forall p1, ?P p1) * (forall q1, ?Q q1) * (forall f1, ?F f1) * (forall h1, ?H h1) * (forall a1, ?A a1) ] =>
      specialize (Pre_Typ_Fun_Arrow_Heap_rect P Q F H A); intros
    end.
    repeat match goal with
           | [ H : ?A -> _ |- _ ] =>
             let H' := fresh "H" in
             assert (H' : A);
             [ repeat clear; shelve | ]; specialize (H H'); clear H'
           end.
    repeat match goal with
           | [ H : _ * _ |- _ ] => destruct H
           end.
    repeat split; intros; eauto.

    Unshelve.
    - intros; case q2; intros.
      specialize (H p0).
      case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (eq_dec_qual q q0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - intros; case p2; intros.
      2-11: right; intro H; inversion H; eauto.
      case n; intros; case n0; intros.
      2-3: right; intro H; inversion H; eauto.
      -- case s; intros; case s0; intros.
         2-3: right; intro H; inversion H; eauto.
         all: case i; intros; case i0; intros.
         2-3,6-7: right; intro H; inversion H; eauto.
         all: left; eauto.
      -- case f; intros; case f0; intros.
         2-3: right; intro H; inversion H; eauto.
         all: left; eauto.
    - intros; case p2; intros.
      1,3-11: right; intro H; inversion H; eauto.
      specialize (OrderedTypeEx.Nat_as_OT.eq_dec v v0).
      intro H; case H; intros; subst; [ left; eauto | ].
      right; intro H'; inversion H'; subst; eauto.
    - intros; case p2; intros.
      1-2,4-11: right; intro H; inversion H; eauto.
      left; eauto.
    - intros; case p2; intros.
      1-3,5-11: right; intro H'; inversion H'; eauto.
      specialize (list_eq_dec_Forall_type l l0 H).
      intro H'; case H'; intros; subst; [ left; eauto | ].
      right; intro H''; inversion H''; subst; eauto.
    - intros; case p2; intros.
      1-4,6-11: right; intro H'; inversion H'; eauto.
      specialize (H f0).
      case H; intros; subst; [ left; eauto | ].
      right; intro H'; inversion H'; subst; eauto.
    - intros; case p2; intros.
      1-5,7-11: right; intro H'; inversion H'; eauto.
      specialize (eq_dec_qual q q0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (H t1).
      case H; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      left; eauto.      
    - intros; case p2; intros.
      1-6,8-11: right; intro H'; inversion H'; eauto.
      specialize (eq_dec_loc l l0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - intros; case p2; intros.
      1-7,9-11: right; intro H'; inversion H'; eauto.
      specialize (H t1).
      case H; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - intros; case p2; intros.
      1-8,10-11: right; intro H'; inversion H'; eauto.
      specialize (eq_dec_loc l l0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - intros; case p2; intros.
      1-9,11: right; intro H'; inversion H'; eauto.
      case c; intros; case c0; intros.
      2-3: right; intro H'; inversion H'; eauto.
      all: specialize (eq_dec_loc l l0).
      all:
        intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      all: specialize (H h0).
      all:
        case H; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      all: left; eauto.
    - intros; case p2; intros.
      1-10: right; intro H'; inversion H'; eauto.
      case c; intros; case c0; intros.
      2-3: right; intro H'; inversion H'; eauto.
      all: specialize (eq_dec_loc l l0).
      all:
        intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      all: specialize (H h0).
      all:
        case H; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      all: left; eauto.
    - intros; case f2; intros.
      specialize (list_eq_dec eq_dec_kv l l0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (H a0).
      case H; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - intros; case a2; intros.
      specialize (list_eq_dec_Forall_type l1 l H).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (list_eq_dec_Forall_type l2 l0 H0).
      intro H''; case H''; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      left; eauto.
    - intros; case h2; intros.
      2-4: right; intro H'; inversion H'; subst; eauto.
      specialize (list_eq_dec_Forall_type l l0 H).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - intros; case h2; intros.
      1,3-4: right; intro H'; inversion H'; subst; eauto.
      assert (H : {l = l0} + {l <> l0});
        [ | case H; intros; subst;
            [ left; eauto
            | right; intro H'; inversion H'; eauto ] ].
      revert l0 X.
      induction l.
      -- intros.
         destruct l0; [ left; eauto | ].
         right; intro H'; inversion H'; subst; eauto.
      -- intros; destruct l0;
           [ right; intro H'; inversion H'; subst; eauto | ].
         destruct a; destruct p.
         inversion X; subst; simpl in *.
         specialize (X0 t1).
         case X0; intros; subst;
           [ | right; intro H'; inversion H'; subst; eauto ].
         specialize (eq_dec_size s s0).
         intro H; case H; intros; subst;
           [ | right; intro H'; inversion H'; subst; eauto ].
         specialize (IHl l0 X1).
         case IHl; intros; subst;
           [ | right; intro H'; inversion H'; subst; eauto ].
         left; eauto.
    - intros; case h2; intros.
      1-2,4: right; intro H'; inversion H'; subst; eauto.
      specialize (H t1).
      case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - intros; case h2; intros.
      1-3: right; intro H'; inversion H'; subst; eauto.
      specialize (eq_dec_size s s0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (eq_dec_qual q q0).
      intro H''; case H''; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      specialize (H t1).
      case H; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      left; eauto.
  Qed.

  Lemma eq_dec_pt : forall r1 r2 : Pretype,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    specialize eq_dec_Pre_Typ_Fun_Arrow_Heap.
    intro.
    repeat match goal with
           | [ H : _ * _ |- _ ] => destruct H
           end.
    eauto.
  Qed.

  Lemma eq_dec_ht : forall r1 r2 : HeapType,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    specialize eq_dec_Pre_Typ_Fun_Arrow_Heap.
    intro.
    repeat match goal with
           | [ H : _ * _ |- _ ] => destruct H
           end.
    eauto.
  Qed.

  Lemma eq_dec_idx : forall r1 r2 : Index,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; case r1; intros; case r2; intros.
    2-5,7-10,12-15: right; intro H; inversion H; subst; eauto.
    - specialize (eq_dec_loc l l0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - specialize (eq_dec_size s s0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - specialize (eq_dec_qual q q0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
    - specialize (eq_dec_pt p p0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      left; eauto.
  Qed.
    
  Lemma eq_dec_val : forall r1 r2 : Value,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    apply (Value_rect'
             (fun r1 => forall r2, {r1 = r2} + {r1 <> r2}));
    intros;
    remember r2 as r2'; generalize (eq_sym Heqr2'); case r2'; intros; subst.
    2-11,13-22,24-33,35-44,46-55,57-66,68-77,79-88,90-99:
      let H := fresh "H" in
      right; intro H; inversion H.
    - remember n as n'; generalize (eq_sym Heqn'); case n'; intros; subst;
      remember n1 as n1'; generalize (eq_sym Heqn1'); case n1'; intros; subst.
      2-3: right; intro H; inversion H.
      -- case s; case s0.
         2-3: right; intro H; inversion H.
         all: case i; case i0.
         2-3,6-7: right; intro H; inversion H.
         all: specialize (OrderedTypeEx.Nat_as_OT.eq_dec n0 n2).
         all: intro H; case H; intros; subst.
         2,4,6,8: right; intro H'; inversion H'; subst; eauto.
         all: left; eauto.
      -- case f; case f0.
         2-3: right; intro H; inversion H.
         all: specialize (OrderedTypeEx.Nat_as_OT.eq_dec n0 n2).
         all: intro H; case H; intros; subst.
         2,4: right; intro H'; inversion H'; subst; eauto.
         all: left; eauto.
    - left; eauto.
    - specialize (OrderedTypeEx.Nat_as_OT.eq_dec n n1).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (OrderedTypeEx.Nat_as_OT.eq_dec n0 n2).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (list_eq_dec eq_dec_idx l l0).
      intro H''; case H''; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      left; eauto.
    - specialize (H v0).
      case H; intros; subst; [ left; eauto | ].
      right; intro H'; inversion H'; subst; eauto.
    - specialize (list_eq_dec_Forall_type l l0 H).
      intro H'; case H'; intros; subst.
      -- left; eauto.
      -- right; intro H''; inversion H''; subst; eauto.
    - specialize (eq_dec_loc l l0).
      intro H; case H; intros; subst.
      -- left; eauto.
      -- right; intro H'; inversion H'; subst; eauto.
    - specialize (eq_dec_loc l l0).
      intro H; case H; intros; subst.
      -- left; eauto.
      -- right; intro H'; inversion H'; subst; eauto.
    - left; eauto.
    - left; eauto.
    - specialize (eq_dec_loc l l0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (H v0).
      case H; intros; subst.
      -- left; eauto.
      -- right; intro H''; inversion H''; subst; eauto.
  Qed.
    
  Lemma eq_dec_hv : forall r1 r2 : HeapValue,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; remember r1 as r1'; generalize (eq_sym Heqr1'); case r1'; intros; subst;
    remember r2 as r2'; generalize (eq_sym Heqr2'); case r2'; intros; subst.
    2-5,7-10,12-15: right; intro H; inversion H.
    - specialize (OrderedTypeEx.Nat_as_OT.eq_dec n n0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (eq_dec_val v v0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      left; eauto.
    - specialize (list_eq_dec eq_dec_val l l0).
      intro H; case H.
      -- intros; subst; left; eauto.
      -- intros; right; intro H'; inversion H'; subst; eauto.
    - specialize (OrderedTypeEx.Nat_as_OT.eq_dec n n0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (list_eq_dec eq_dec_val l l0).
      intro H'; case H'; intros; subst.
      -- left; eauto.
      -- intros; right; intro H''; inversion H''; subst; eauto.
    - specialize (eq_dec_pt p p0).
      intro H; case H; intros; subst;
        [ | right; intro H'; inversion H'; subst; eauto ].
      specialize (eq_dec_val v v0).
      intro H'; case H'; intros; subst;
        [ | right; intro H''; inversion H''; subst; eauto ].
      specialize (eq_dec_ht h h0).
      intro H''; case H''; intros; subst;
        [ | right; intro H'''; inversion H'''; subst; eauto ].
      left; eauto.
  Qed.

  Lemma eq_dec_tpl : forall r1 r2 : N * HeapValue * N,
      {r1 = r2} + {r1 <> r2}.
  Proof.
    intro r1; destruct r1 as [[l1 hv1] sz1].
    intro r2; destruct r2 as [[l2 hv2] sz2].
    specialize (OrdersEx.N_as_OT.eq_dec l1 l2).
    intro H; case H; intros; subst;
      [ | right; intro H'; inversion H'; subst; eauto ].
    specialize (eq_dec_hv hv1 hv2).
    intro H'; case H'; intros; subst;
      [ | right; intro H''; inversion H''; subst; eauto ].
    specialize (OrdersEx.N_as_OT.eq_dec sz1 sz2).
    intro H''; case H''; intros; subst;
      [ | right; intro H'''; inversion H'''; subst; eauto ].
    left; eauto.
  Qed.

  Lemma Forall_combine_ReplaceAtIdx : forall {A B} idx lold vold lnew vnew lstatic vstatic (P : (A * B) -> Prop),
      Forall P (combine lold lstatic) ->
      ReplaceAtIdx idx lold vnew = Some (lnew, vold) ->
      nth_error lstatic idx = Some vstatic ->
      P (vnew, vstatic) ->
      Forall P (combine lnew lstatic).
  Proof.
    intros A B idx lold.
    revert idx.
    induction lold; intros.
    - destruct idx; discriminate H0.
    - destruct lstatic; destruct lnew; simpl; auto.
      inversion H; subst.
      destruct idx.
      + injection H0 as h. subst.
        injection H1 as h. subst.
        apply Forall_cons; auto.
      + simpl in H0. rewrite Nat.sub_0_r in H0. simpl in H1.
        destruct (ReplaceAtIdx idx lold vnew) eqn:Eq.
        ++ destruct p. injection H0 as h. subst.
           apply Forall_cons; auto.
           eapply IHlold; eauto.
        ++ discriminate H0.
  Qed.

  Lemma Forall_combine_nth_error : forall {A B} idx l1 l2 v2 (P : (A * B) -> Prop),
        length l1 = length l2 ->
        Forall P (combine l1 l2) ->
        nth_error l2 idx = Some v2 ->
        exists v1, P (v1, v2).
  Proof.
    induction idx.
    - intros l1 l2.
      case l1; case l2; intros.
      all: simpl in *.
      1-3:
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
        | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
        end.
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : Forall _ _ |- _ ] => inversion H; subst; simpl in *
      end.
      eexists; eauto.
    - intros l1 l2.
      case l1; case l2; intros.
      all: simpl in *.
      1-3:
        match goal with
        | [ H : None = Some _ |- _ ] => inversion H
        | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
        | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
        end.
      match goal with
      | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : Forall _ _ |- _ ] => inversion H; subst; simpl in *
      end.
      eauto.
  Qed.

  Theorem Same_set_Union_compat_r:  forall {A : Type} (s1 s1' s2 : Ensembles.Ensemble A),
      s1 <--> s1' -> s2 :|: s1 <--> s2 :|: s1'.
  Proof.
    intros. inversion H. split.
    - apply Union_Included.
      eapply Included_Union_l.
      eapply Included_trans; eauto.
      eapply Included_Union_r.
    - apply Union_Included.
      eapply Included_Union_l.
      eapply Included_trans; eauto.
      eapply Included_Union_r.
  Qed.

  Lemma Permutation_map_gen : forall {A B} {l1 : list A} {l2} {f1 : A -> B} {f2},
    Permutation.Permutation l1 l2 ->
    ((forall x, In x l1 -> f1 x = f2 x) \/
     (forall x, In x l2 -> f1 x = f2 x)) ->
    Permutation.Permutation (map f1 l1) (map f2 l2).
  Proof.
    intros A B l1 l2 f1 f2 H.
    revert l1 l2 H f1 f2.
    apply
      (Permutation.Permutation_ind
         (fun l1 l2 =>
            forall f1 f2,
              ((forall x, In x l1 -> f1 x = f2 x) \/
               (forall x, In x l2 -> f1 x = f2 x)) ->
              Permutation.Permutation (map f1 l1) (map f2 l2))).
    - auto.
    - intros.
      simpl.
      match goal with
      | [ |- _ (?A :: _) (?B :: _) ] =>
        let H := fresh "H" in
        assert (H : A = B); [ | rewrite H ]
      end.
      { match goal with
        | [ H : _ \/ _ |- _ ] =>
          case H; let H' := fresh "H" in intro H'; apply H'
        end.
        all: constructor; auto. }
      constructor.
      match goal with
      | [ H : forall _ _, _ |- _ ] => apply H
      end.
      match goal with
      | [ H : _ \/ _ |- _ ] => case H; [ left | right ]
      end.
      all: intros.
      all:
        match goal with
        | [ H : forall _, _ -> _ _ = _ _ |- _ ] =>
          apply H
        end.
      all: constructor 2; auto.
    - intros.
      simpl.
      match goal with
      | [ |- _ (?A :: ?C :: _) (?B :: ?D :: _) ] =>
        let H := fresh "H" in
        let H' := fresh "H" in
        assert (H : A = D); [ | assert (H' : C = B); [ | rewrite H; rewrite H' ] ]
      end.
      1-2:
        match goal with
        | [ H : _ \/ _ |- _ ] =>
          case H; let H' := fresh "H" in intro H'; apply H'
        end.
      1,4: constructor; auto.
      1-2: constructor 2; constructor; auto.
      eapply Permutation.perm_trans;
        [ apply Permutation.perm_swap | ].
      constructor.
      constructor.
      match goal with
      | [ |- _ ?A ?B ] =>
        let H := fresh "H" in
        assert (H : A = B); [ | rewrite H; auto ]
      end.
      apply map_ext_in.
      intros.
      match goal with
      | [ H : _ \/ _ |- _ ] =>
        case H; let H' := fresh "H" in intro H'; apply H'
      end.
      all: constructor 2; constructor 2; auto.
    - intros.
      eapply (Permutation.perm_trans (l':=(map f2 l'))).
      -- match goal with
         | [ H : context[_ (map  _ ?L1) (map _ ?L2)]
             |- _ (map _ ?L1) (map _ ?L2) ] =>
           apply H
         end.
         match goal with
         | [ H : _ \/ _ |- _ ] => case H; [ left | right ]; auto
         end.
         intros.
         match goal with
         | [ H : Permutation.Permutation ?L1 ?L2,
             H' : In ?EL ?L1 |- _ ] =>
           let H'' := fresh "H" in
           assert (H'' : In EL L2)
         end.
         { eapply Permutation.Permutation_in; eauto. }
         eauto.
      -- apply Permutation.Permutation_map; auto.
  Qed.

  Lemma Permutation_gen_provable :
    forall idx,
    forall [A B : Type] (f f' : A -> B) (g g' : A -> A) (l l' : list A),
      idx = length l ->
      NoDup l ->
      NoDup l' ->
      (forall x, In x l -> In (g x) l' /\ g' (g x) = x /\ f x = f' (g x)) ->
      (forall x, In x l' -> In (g' x) l /\ g (g' x) = x /\ f' x = f (g' x)) ->
      Permutation.Permutation (map f l) (map f' l').
  Proof.
    induction idx.
    - intros.
      destruct l; simpl in *.
      2:{
        match goal with
        | [ H : 0 = Datatypes.S _ |- _ ] => inversion H
        end.
      }
      destruct l'; simpl in *.
      2:{
        match goal with
        | [ H : forall _, _ \/ _ -> _ |- _ ] =>
          specialize (H _ (or_introl eq_refl))
        end.
        destructAll; exfalso; auto.
      }
      auto.
    - intros.
      destruct l; simpl in *.
      1:{
        match goal with
        | [ H : Datatypes.S _ = 0 |- _ ] => inversion H
        end.
      }
      match goal with
      | [ H : forall _, _ \/ _ -> _ |- _ ] =>
        generalize (H _ (or_introl eq_refl))
      end.
      intros; destructAll.
      match goal with
      | [ H : In _ _ |- _ ] =>
        apply In_nth_error in H
      end.
      destructAll.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        specialize (Permutation_remove_nth H)
      end.
      intros.
      eapply Permutation.Permutation_trans.
      2:{
        apply Permutation.Permutation_map.
        apply Permutation.Permutation_sym; eauto.
      }
      simpl.
      match goal with
      | [ H : ?A = ?B |- _ (?A :: _) _ ] =>
        rewrite H
      end.
      constructor.
      match goal with
      | [ H : NoDup (_ :: _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : forall _ _ _ _ _ _ _ _, _ |- _ ] =>
        eapply (H _ _ _ _ g g'); eauto
      end.
      -- apply NoDup_remove_nth; auto.
      -- intros.
         match goal with
         | [ H : forall _, _ \/ _ -> _, H' : In _ _ |- _ ] =>
           specialize (H _ (or_intror H'))
         end.
         destructAll.
         split; auto.
         erewrite In_NoDup_remove_nth; eauto.
         split; auto.
         intro.
         match goal with
         | [ H : ?A = ?B, H' : _ ?A = _ |- _ ] =>
           rewrite H in H'
         end.
         match goal with
         | [ H : ?A ?B = _, H' : ?A ?B = _ |- _ ] =>
           rewrite H in H'
         end.
         match goal with
         | [ H : In ?A ?L, H' : ~ In ?B ?L, H'' : ?A = ?B |- _ ] =>
           rewrite H'' in H
         end.
         eauto.
      -- intro.
         erewrite In_NoDup_remove_nth; eauto.
         intros.
         destructAll.
         match goal with
         | [ H : In _ ?L,
             H' : forall _, In _ ?L -> _ |- _ ] =>
           specialize (H' _ H)
         end.
         destructAll.
         match goal with
         | [ H : _ \/ _ |- _ ] => case H; intros; subst
         end.
         1: exfalso; eauto.
         split; auto.
  Qed.
        
  Lemma Permutation_gen :
    forall [A B : Type] {f f' : A -> B} {g g' : A -> A} {l l' : list A},
      NoDup l ->
      NoDup l' ->
      (forall x, In x l -> In (g x) l' /\ g' (g x) = x /\ f x = f' (g x)) ->
      (forall x, In x l' -> In (g' x) l /\ g (g' x) = x /\ f' x = f (g' x)) ->
      Permutation.Permutation (map f l) (map f' l').
  Proof.
    intros.
    eapply Permutation_gen_provable; eauto.
  Qed.
  
  Lemma Permutation_gen_change_one :
    forall [A B : Type] {f f' : A -> B} {g g' : A -> A} {l l' : list A} {idx : nat} {in_elem : A} {new_elem : B},
      NoDup l ->
      NoDup l' ->
      nth_error l idx = Some in_elem ->
      (forall x, In x l -> In (g x) l' /\ g' (g x) = x /\ (x = in_elem -> new_elem = f' (g x)) /\ (x <> in_elem -> f x = f' (g x))) ->
      (forall x, In x l' -> In (g' x) l /\ g (g' x) = x /\ ((g' x) = in_elem -> f' x = new_elem) /\ ((g' x) <> in_elem -> f' x = f (g' x))) ->
      Permutation.Permutation (set_nth (map f l) idx new_elem) (map f' l').
  Proof.
    intros.
    eapply Permutation.Permutation_trans.
    1:{
      eapply Permutation_remove_nth.
      eapply nth_error_set_nth; eauto.
      rewrite map_length.
      eapply nth_error_Some_length; eauto.
    }
    rewrite remove_nth_set_nth.
    match goal with
    | [ H : nth_error _ _ = Some _ |- _ ] =>
      specialize (nth_error_In _ _ H)
    end.
    intros.
    match goal with
    | [ H : forall _, In _ ?L -> _,
        H' : In _ ?L |- _ ] =>
      generalize (H _ H')
    end.
    intros; destructAll.
    match goal with
    | [ H : ?A = ?A -> _ |- _ ] => specialize (H eq_refl)
    end.
    match goal with
    | [ H : In _ ?L |- _ _ (map _ ?L) ] =>
      apply In_nth_error in H
    end.
    destructAll.
    eapply Permutation.Permutation_trans.
    2:{
      eapply Permutation.Permutation_sym.
      eapply Permutation_remove_nth; eauto.
      eapply map_nth_error; eauto.
    }
    constructor.
    repeat rewrite remove_nth_map.
    apply (Permutation_gen (g:=g) (g':=g')).
    - apply NoDup_remove_nth; auto.
    - apply NoDup_remove_nth; auto.
    - intros.
      match goal with
      | [ H : In _ _ |- _ ] =>
        erewrite In_NoDup_remove_nth in H; eauto
      end.
      destructAll.
      match goal with
      | [ H : forall _, In _ ?L -> _,
          H' : In _ ?L |- _ ] =>
        generalize (H _ H')
      end.
      intros; destructAll.
      match goal with
      | [ H : ?A, H' : ?A -> ?B |- _ ] =>
        specialize (H' H)
      end.
      split; auto.
      erewrite In_NoDup_remove_nth; eauto.
      split; auto.
      intro.
      match goal with
      | [ H : _ ?A = ?B, H' : _ ?C = ?D,
          H'' : ?D <> ?B, H''' : ?C = ?A |- _ ] =>
        rewrite H''' in H'; rewrite H in H'
      end.
      auto.
    - intros.
      match goal with
      | [ H : In _ _ |- _ ] =>
        erewrite In_NoDup_remove_nth in H; eauto
      end.
      destructAll.
      match goal with
      | [ H : forall _, In _ ?L -> _,
          H' : In _ ?L |- _ ] =>
        generalize (H _ H')
      end.
      intros; destructAll.
      match goal with
      | [ H : ?A <> ?B -> _ |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A <> B); [ | specialize (H H') ]
      end.
      { intro; subst; auto. }        
      split; auto.
      erewrite In_NoDup_remove_nth; eauto.
  Qed.

  Lemma SplitStoreTypings_LinInstruction : forall {S s Sh Sp Slin Sunr idx Sval Sstack S_ignore Ss Sref Sempty F loc tau},
    HasTypeStore s Sh Sp ->
    SplitStoreTypings [Sp; Sh] S ->
    SplitStoreTypings (Slin ++ Sunr) Sh ->
    nth_error Slin idx = Some Sval ->
    SplitStoreTypings (Sstack :: S_ignore ++ Ss) Sp ->
    SplitStoreTypings [Sref; Sempty] Sstack ->
    HasTypeValue Sref F (Ref (LocP loc Linear)) tau ->
    map_util.M.is_empty (LinTyp Sempty) = true ->
    exists Sstack' Sp' Sh' S',
      SplitStoreTypings [Sp'; Sh'] S' /\
      SplitStoreTypings [Sval; Sh'] Sh /\
      SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' /\
      SplitStoreTypings
        [Sval;
        {| InstTyp := InstTyp Sh;
           LinTyp := M.add
                       (N.succ_pos loc)
                       (ArrayType (QualT Unit Unrestricted))
                       (M.empty HeapType);
           UnrTyp := UnrTyp Sh |}]
        Sstack'.
  Proof.
    intros.
          
    match goal with
    | [ H : HasTypeStore _ ?SH ?SP,
        H' : SplitStoreTypings (?SLIN ++ ?SUNR) ?SH,
        H'' : nth_error ?SLIN ?IDX = Some ?TAU,
        H''' : SplitStoreTypings [?SP; ?SH] ?S |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings (TAU :: (remove_nth (SLIN ++ SUNR) IDX)) SH);
      [ eapply SplitStoreTypings_permut; [ | exact H' ]
      | let H1 := fresh "H" in
        assert (H1 : SplitStoreTypings [SH; SP] S);
        [ eapply SplitStoreTypings_permut; [ | exact H''' ];
          constructor | ];
        specialize (SplitStoreTypings_move_one H1 H0) ]
    end.
    { apply Permutation_remove_nth.
      rewrite nth_error_app1; auto.
      eapply nth_error_Some_length; eauto. }
    intros; destructAll.

    match goal with
    | [ H : SplitStoreTypings [?S1; ?SP] ?S,
        H' : SplitStoreTypings [?S1; _] ?SH,
        H'' : HasTypeStore _ ?SH ?SP,
        H''' : SplitStoreTypings (?SST :: _ ++ _) ?SP,
        H'''' : SplitStoreTypings [_; _] ?SST |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings [SP; S1] S);
      [ eapply SplitStoreTypings_permut; [ | exact H ];
        constructor | ];
      specialize (SplitStoreTypings_trans_gen H''' H0);
      let H1 := fresh "H" in intro H1;
      rewrite <-app_comm_cons in H1;
      specialize (SplitStoreTypings_trans_gen H'''' H1)
    end.
    simpl; intros.

    match goal with
    | [ H : SplitStoreTypings (?S0 :: ?S1 :: (?SS1 ++ ?SS2) ++ [?S2]) ?SP,
        H' : M.is_empty (LinTyp ?S1) = true |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : nth_error (S0 :: S1 :: (SS1 ++ SS2) ++ [S2]) 1 = Some S1) by ltac:(simpl; auto);
      specialize (SplitStoreTypings_remove_empty H H0 H');
      let H1 := fresh "H" in simpl; intro H1;
      let H2 := fresh "H" in
      assert (H2 : SplitStoreTypings ([S0; S2] ++ SS1 ++ SS2) SP);
      [ eapply SplitStoreTypings_permut; [ | exact H1 ]
      | specialize (SplitStoreTypings_split H2) ]
    end.
    { constructor.
      eapply Permutation.Permutation_trans.
      - apply Permutation.Permutation_app_comm.
      - simpl; constructor.
        apply Permutation.Permutation_refl. }
    intros; destructAll.

    match goal with
    | [ |- context[_ /\ _ /\ _ /\ SplitStoreTypings [_; ?S] _] ] =>
      remember S as Sref'
    end.

    match goal with
    | [ H : SplitStoreTypings [?S1; ?S2] ?SU1,
        H' : SplitStoreTypings (?SU1 :: _ ++ _) ?SU2,
        H'' : SplitStoreTypings [?SO; ?SU2] ?SU3,
        H''' : SplitStoreTypings [?SP; ?SH] ?SU3,
        H'''' : HasTypeStore _ ?SH ?SP |- _ ] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      let H3 := fresh "H" in
      assert (H1 : InstTyp S1 = InstTyp Sref');
      [ | assert (H2 : UnrTyp S1 = UnrTyp Sref');
          [ | assert (H3 : (Dom_ht (LinTyp S1)) <--> (Dom_ht (LinTyp Sref')));
              [ | specialize (SplitStoreTypings_change_vals H H1 H2 H3) ] ] ]
    end.
    1-2: subst; simpl.
    1-2: solve_inst_or_unr_typ_eq.
    { subst; simpl.
      match goal with
      | [ H : HasTypeValue ?S _ _ _ |- context[?S] ] =>
        inversion H; subst; simpl in *
      end.
      eapply Same_set_trans; [ apply eq_map_Dom_ht; eauto | ].
      apply Dom_ht_one_loc. }
    intros; destructAll.

    match goal with
    | [ H : SplitStoreTypings [?S1; ?S2] ?SU1,
        H' : SplitStoreTypings (?SU1 :: _ ++ _) ?SU2,
        H'' : SplitStoreTypings [?SO; ?SU2] ?SU3,
        H''' : SplitStoreTypings [?SP; ?SH] ?SU3,
        H'''' : HasTypeStore _ ?SH ?SP,
        H''''' : InstTyp ?SU1 = InstTyp ?ASU1,
        H'''''' : UnrTyp ?SU1 = UnrTyp ?ASU1,
        H''''''' : Dom_ht (LinTyp ?SU1) <--> Dom_ht (LinTyp ?ASU1) |- _ ] =>
      specialize (SplitStoreTypings_change_vals H' H''''' H'''''' H''''''')
    end.
    intros; destructAll.

    match goal with
    | [ H : SplitStoreTypings [?S1; ?S2] ?SU1,
        H' : SplitStoreTypings (?SU1 :: _ ++ _) ?SU2,
        H'' : SplitStoreTypings [?SO; ?SU2] ?SU3,
        H''' : SplitStoreTypings [?SP; ?SH] ?SU3,
        H'''' : HasTypeStore _ ?SH ?SP,
        H''''' : InstTyp ?SU2 = InstTyp ?ASU2,
        H'''''' : UnrTyp ?SU2 = UnrTyp ?ASU2,
        H''''''' : Dom_ht (LinTyp ?SU2) <--> Dom_ht (LinTyp ?ASU2) |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : SplitStoreTypings [SU2; SO] SU3);
      [ eapply SplitStoreTypings_permut; [ | exact H'' ];
        constructor | ];
      specialize (SplitStoreTypings_change_vals H0 H''''' H'''''' H''''''')
    end.
    intros; destructAll.

    do 4 eexists.
    split;
      [ | split;
          [ | split;
              [ | eapply SplitStoreTypings_permut;
                  [ apply Permutation.perm_swap | ]; eauto ] ] ];
      [ | | eauto ];
      [ | eauto ].
    eauto.
  Qed.

  Lemma Permutation_StoreTypings : forall A mem1 mem2 loc q1 q2 v sz v' (f1 : N * M.Val * Len -> A) (f2 : N * M.Val * Len -> A),
      get loc q1 mem1 = Some (v, sz) ->
      set loc q1 mem1 v' = Some mem2 ->
      (forall '(loc', hv, len),
          f2 (loc', hv, len) =
          (if (match qualconstr_eq_dec q1 q2 with
               | left _ => (loc =? loc')%N
               | right _ => false
               end)
           then f1 (loc', v, sz)
           else f1 (loc', hv, len))) ->
      Permutation.Permutation
        (map f1 (M.to_list q2 mem1))
        (map f2 (M.to_list q2 mem2)).
  Proof.
    intros.
    match goal with
    | [ H : set _ _ _ _ = _ |- _ ] =>
      specialize (get_set_same _ _ _ _ _ H)
    end.

    intros; destructAll.
    match goal with
    | [ H : get ?L ?M mem1 = Some (?HV, ?SZ),
        H' : get ?L ?M mem2 = Some (?HVP, ?SZP) |- _ ] =>
      apply (Permutation_gen (g:=(fun '(loc', hv, len) => if (match qualconstr_eq_dec q1 q2 with | left _ => (loc =? loc')%N | right _ => false end) then (L, HVP, SZP) else (loc', hv, len))) (g':=(fun '(loc', hv, len) => if (match qualconstr_eq_dec q1 q2 with | left _ => (loc =? loc')%N | right _ => false end) then (L, HV, SZ) else (loc', hv, len))))
    end.
    - apply to_list_NoDup.
    - apply to_list_NoDup.
    - intros x' Hin.
      destruct x' as [[curL curHV] curLen].
      remember (qualconstr_eq_dec q1 q2) as qeqb.
      destruct qeqb; simpl.
      -- assert (Hloc_eq : loc = curL \/ loc <> curL).
         { apply eq_dec_N. }
         case Hloc_eq; intros; subst.
         --- repeat rewrite N.eqb_refl.
             match goal with
             | [ |- _ /\ ?B /\ _ ] =>
               let H := fresh "H" in
               assert (H : B);
               [ | inversion H; subst ]
             end.
             { match goal with
               | [ H : In _ _ |- _ ] =>
                 apply In_nth_error in H
               end.
               destructAll.
               match goal with
               | [ H : nth_error _ _ = Some _ |- _ ] =>
                 apply in_to_list_implies_get in H
               end.
               match goal with
               | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                 rewrite H in H';
                 inversion H'; subst; simpl in *
               end.
               auto. }
             split; [ | split; eauto ].
             ---- match goal with
                  | [ H : get _ _ mem2 = Some _ |- _ ] =>
                    apply get_implies_in_to_list in H
                  end.
                  destructAll.
                  eapply nth_error_In; eauto.
             ---- match goal with
                  | [ H : forall _, _ |-
                      _ = f2 ?TPL ] =>
                    specialize (H TPL);
                    simpl in H;
                    unfold M.Loc;
                    rewrite H
                  end.
                  rewrite N.eqb_refl; auto.
         --- assert (Hneq : (loc =? curL)%N = false).
             { rewrite N.eqb_neq; auto. }
             assert (Hneq2 : curL <> loc).
             { intro; eauto. }
             repeat rewrite Hneq.
             split; [ | split; eauto ].
             ---- match goal with
                  | [ H : In _ _ |- _ ] =>
                    apply In_nth_error in H
                  end.
                  destructAll.
                  match goal with
                  | [ H : nth_error _ _ = Some _ |- _ ] =>
                    apply in_to_list_implies_get in H
                  end.
                  match goal with
                  | [ H : set _ _ _ _ = Some _,
                      H' : _ <> _ |- _ ] =>
                    specialize (get_set_other_loc _ _ _ _ _ _ H H')
                  end.
                  intros.
                  match goal with
                  | [ H : get ?A ?B ?C = Some _,
                      H' : get ?A ?B ?C = get ?AP ?BP ?CP |- _ ] =>
                    rewrite H' in H;
                    apply get_implies_in_to_list in H;
                    let x := fresh "x" in
                    destruct H as [x H];
                    apply nth_error_In in H
                  end.
                  auto.
             ---- match goal with
                  | [ H : forall _, _ |-
                      _ = f2 ?TPL ] =>
                    specialize (H TPL);
                    simpl in H;
                    unfold M.Loc;
                    rewrite H
                  end.
                  rewrite Hneq; auto.
      -- split; [ | split; eauto ].
         --- match goal with
             | [ H : In _ _ |- _ ] =>
               apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : set _ _ _ _ = Some _,
                 H' : _ <> _ |- _ ] =>
               specialize (get_set_other_mem _ _ _ curL _ _ _ H H')
             end.
             intros.
             match goal with
             | [ H : get ?A ?B ?C = Some _,
                 H' : get ?A ?B ?C = get ?AP ?BP ?CP |- _ ] =>
               rewrite H' in H;
               apply get_implies_in_to_list in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply nth_error_In in H
             end.
             auto.
         --- match goal with
             | [ H : forall _, _ |-
                 _ = f2 ?TPL ] =>
               specialize (H TPL);
               simpl in H;
               unfold M.Loc;
               rewrite H
             end.
             auto.
    - intros x' Hin.
      destruct x' as [[curL curHV] curLen].
      remember (qualconstr_eq_dec q1 q2) as qeqb.
      destruct qeqb; simpl.
      -- assert (Hloc_eq : loc = curL \/ loc <> curL).
         { apply eq_dec_N. }
         case Hloc_eq; intros; subst.
         --- repeat rewrite N.eqb_refl.
             match goal with
             | [ H : get _ _ ?MEM = Some _
                 |- In _ (M.to_list _ ?MEM) /\ _ ] =>
               specialize (get_implies_in_to_list _ _ _ _ _ H)
             end.
             intros; destructAll.
             split; [ eapply nth_error_In; eauto | ].
             match goal with
             | [ H : In _ _ |- _ ] =>
               apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some ?TPL
                 |- _ = ?TPL /\ _ ] =>
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
               rewrite H in H'; inversion H'; subst; simpl in *
             end.
             split; [ eauto | ].
             match goal with
             | [ H : forall _, _ |- f2 ?TPL = _ ] =>
               specialize (H TPL); simpl in *; rewrite H
             end.
             rewrite N.eqb_refl; auto.
         --- assert (Hneq : (loc =? curL)%N = false).
             { rewrite N.eqb_neq; auto. }
             repeat rewrite Hneq.
             match goal with
             | [ H : In _ _ |- _ ] =>
               apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some (?L, ?HV, ?SZ),
                 H' : set _ _ _ _ = Some _,
                 H'' : ?L2 <> ?L |- _ ] =>
               apply in_to_list_implies_get in H;
               specialize (get_set_other_loc _ _ _ _ _ _ H' H'');
               let H''' := fresh "H" in
               intro H'''; rewrite <-H''' in H;
               apply get_implies_in_to_list in H
             end.
             destructAll.
             split; [ eapply nth_error_In; eauto | ].
             split; [ eauto | ].
             match goal with
             | [ H : forall _, _ |- f2 ?TPL = _ ] =>
               specialize (H TPL); simpl in *; rewrite H
             end.
             rewrite Hneq; auto.
      -- match goal with
         | [ H : In _ _ |- _ ] =>
           apply In_nth_error in H
         end.
         destructAll.
         match goal with
         | [ H : nth_error _ _ = Some (?L, ?HV, ?SZ),
             H' : set _ _ _ _ = Some _,
             H'' : _ <> _ |- _ ] =>
           apply in_to_list_implies_get in H;
           specialize (get_set_other_mem _ _ _ L _ _ _ H' H'');
           let H''' := fresh "H" in
           intro H'''; rewrite <-H''' in H;
           apply get_implies_in_to_list in H
         end.
         destructAll.
         split; [ eapply nth_error_In; eauto | ].
         split; [ eauto | ].
         match goal with
         | [ H : forall _, _ |- f2 ?TPL = _ ] =>
           specialize (H TPL); simpl in *; rewrite H; auto
         end.
  Qed.  

  Lemma SplitStoreTypings_unr_same : forall {Sstack S_ignore Ss Sp},
      SplitStoreTypings (Sstack :: S_ignore ++ Ss) Sp ->
      map (update_unr (UnrTyp Sp)) S_ignore = S_ignore.
  Proof.
    intros Sstack S_ignore. generalize dependent Sstack.
    induction S_ignore; intros; auto.
    inversion H. simpl in H1. inversion H1. inversion H0. clear H0. subst.
    inversion H7. subst. clear H7.
    simpl. f_equal.
    - destruct H5. rewrite H4.
      destruct a; auto.
    - eapply IHS_ignore. split.
      + apply Forall_app in H8. destruct H8.
        apply Forall_cons. exact H6.
        apply Forall_app. split. auto.
        apply Forall_cons. exact H5. exact H4.
      + simpl. inversion H1. split.
        ++ rewrite <- H2. simpl.
           apply Same_set_Union_compat_r.
           rewrite map_app. rewrite map_app.
           rewrite Union_list_app.
           rewrite map_app. rewrite map_app.
           rewrite Union_list_app.
           simpl.
           rewrite (Union_commut).
           rewrite <- Union_assoc.
           rewrite Union_commut.
           rewrite (Union_commut (Dom_ht (LinTyp a))).
           apply Same_set_Union_compat_l.
           rewrite Union_commut. 
           reflexivity.
        ++ intros. specialize (H4 _ _ H7).
           inversion H4; subst.
           -- apply InHead. auto. inversion H15. subst. auto.
              rewrite map_app.
              rewrite ExactlyInOne_true_app.
              rewrite map_app in H18.
              rewrite ExactlyInOne_true_app in H18. destruct H18.
              split; auto.
              apply NotInHead; auto.
           -- apply NotInHead. auto.
              rewrite map_app.
              inversion H16; subst.
              +++ rewrite map_app in H17.
                  rewrite ExactlyInOne_true_app in H17.
                  destruct H17.
                  apply ExactlyInOne_app_r. auto.
                  simpl. apply InHead. auto. auto.
              +++ rewrite map_app in H18.
                  apply ExactlyInOne_app_inv in H18. destruct H18; destruct H9.
                  apply ExactlyInOne_app_l; auto.
                  simpl. apply NotInHead. auto. auto.
                  apply ExactlyInOne_app_r. auto.
                  simpl. apply NotInHead; auto.
  Qed.

  Lemma Union_In_l: forall {T} S1 S2 S x,
      Ensembles.In T S1 x ->
      S1 :|: S2 <--> S ->
      Ensembles.In T S x.
  Proof.
    intros. inversion H0. 
    unfold Ensembles.Included in H1.
    eapply H1.
    apply Ensembles.Union_introl. auto.
  Qed.

  Theorem In_singleton_eq: forall {T U} L x y (f: T -> U),
      In x L -> [y] = map f L -> f x = y.
  Proof.
    intros T U L. induction L; intros; inversion H; subst.
    - injection H0 as h. auto.
    - destruct L. inversion H1. inversion H0.
  Qed.

  Theorem app_single: forall {T} (a b: T),
      [a] ++ [b] = [a;b].
  Proof.
    intros. auto.
  Qed.
    
  Lemma EqualTyps_StructLinInstruction : forall l S1 S2 S S' So Sint Ss1 Ss2 ht ht',
      SplitStoreTypings [S'; So] Sint ->
      SplitStoreTypings (Sint :: Ss1 ++ Ss2) S2 ->
      SplitStoreTypings [S2; S1] S ->
      eq_map
        (LinTyp S')
        (map_util.M.add
           (N.succ_pos l) ht
           (map_util.M.empty HeapType)) ->
      get_heaptype l (LinTyp S1) = Some ht' \/
      get_heaptype l (LinTyp S2) = Some ht' ->
      ht = ht'.
  Proof.
    intros.
                     
    match goal with
    | [ H : get_heaptype ?L _ = Some ?T \/
            get_heaptype ?L ?S2 = Some ?T,
        H' : eq_map _ (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
      assert (Hght : get_heaptype L S2 = Some HT)
    end.
    { match goal with
      | [ H : eq_map (LinTyp ?S1) (map_util.M.add (N.succ_pos ?L) ?HT _),
          H' : SplitStoreTypings [?S1; _] ?S2 |- _ ] =>
        eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S2));
        [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); [ | | eauto ]; [ | constructor; eauto ]
        |
        | eauto ];
        [ | constructor; eauto ]
      end.
      unfold get_heaptype.
      match goal with
      | [ H : eq_map _ _ |- _ ] =>
        unfold eq_map in H;
        unfold get_heaptype in H;
        rewrite H
      end.
      rewrite M.gss; auto. }

    match goal with
    | [ H : get_heaptype ?L _ = Some ?T \/
            get_heaptype ?L _ = Some ?T |- _ ] =>
      case H; intros
    end.
    - match goal with
      | [ H : SplitStoreTypings [?S1; ?S2] _,
          H' : get_heaptype ?L (LinTyp ?S1) = Some _,
          H'' : get_heaptype ?L (LinTyp ?S2) = Some _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : SplitHeapTypings [LinTyp ?S1; LinTyp ?S2] (LinTyp ?S),
          H' : get_heaptype ?L (LinTyp ?S1) = Some ?HT,
          H'' : get_heaptype ?L (LinTyp ?S2) = Some _ |- _ ] =>
        inversion H; subst; simpl in *;
        assert (Hght_upper : get_heaptype L (LinTyp S) = Some HT);
        [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); eauto; constructor; eauto | ]
      end.
      match goal with
      | [ H : forall _ _, get_heaptype _ (LinTyp ?S) = _ -> _,
          H' : get_heaptype _ (LinTyp ?S) = _ |- _ ] =>
        specialize (H _ _ H');
        inversion H; subst; simpl in *
      end.
      -- match goal with
         | [ H : ExactlyInOne true _ _ _ |- _ ] =>
           inversion H; subst; simpl in *
         end.
         match goal with
         | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- match goal with
         | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
           rewrite H in H'; inversion H'
         end.
    - match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] =>
        rewrite H in H'; inversion H'; subst
      end.
      auto.
  Qed.

  Lemma SplitStoreTypings_eq_typs : forall S1 S2 Sl Sorig,
      SplitStoreTypings Sl Sorig ->
      In S1 Sl ->
      In S2 Sl ->
      InstTyp S1 = InstTyp S2 /\ UnrTyp S1 = UnrTyp S2.
  Proof.
    intros.
    inversion H.
    rewrite Forall_forall in H2.
    assert (HS1: InstTyp Sorig = InstTyp S1 /\ UnrTyp Sorig = UnrTyp S1).
    eapply H2; eauto.
    destruct HS1.
    assert (HS2: InstTyp Sorig = InstTyp S2 /\ UnrTyp Sorig = UnrTyp S2).
    eapply H2; eauto.
    destruct HS2.
    split.
    rewrite <- H4.
    rewrite <- H6.
    auto.
    rewrite <- H5.
    rewrite <- H7.
    auto.
  Qed.

  Lemma SplitStoreTypings_eq_typs2 : forall {S l1 S'},
      SplitStoreTypings l1 S' ->
      In S l1 ->
      UnrTyp S = UnrTyp S' /\ InstTyp S = InstTyp S'.
  Proof.
    intros.
    inversion H.
    rewrite Forall_forall in H1.
    specialize (H1 S H0).
    destruct H1.
    split; auto.
  Qed.

  Lemma StructLinear_SplitStoreTypings_eq_typs2 : forall {B C} {Ss0 idx Svnew Snew f} {vs : list B} {taus : list C} {v},
      SplitStoreTypings (set_nth Ss0 idx Svnew) Snew ->
      Forall3 f Ss0 vs taus ->
      nth_error vs idx = Some v ->
      UnrTyp Svnew = UnrTyp Snew /\
      InstTyp Svnew = InstTyp Snew.
  Proof.
    intros.
    eapply SplitStoreTypings_eq_typs2; [ eauto | ].
    apply set_nth_In.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] =>
      specialize (Forall3_length _ _ _ _ H)
    end.
    intros; destructAll.
    match goal with
    | [ H : ?A = _ |- _ < ?A ] =>
      rewrite H
    end.
    eapply nth_error_Some_length; eauto.
  Qed.

  Ltac use_StructLinear_SplitStoreTypings_eq_typs2 :=
    match goal with
    | [ H : SplitStoreTypings (set_nth ?Ss0 ?idx ?Svnew) ?Snew,
        H' : Forall3 _ ?Ss0 ?vs _,
        H'' : nth_error ?vs ?idx = Some _ |- _ ] =>
      specialize (StructLinear_SplitStoreTypings_eq_typs2 H H' H'')
    end.

  Theorem Union_List_set_nth_empty: forall {T U} (m: T -> Ensembles.Ensemble U) (x y: T) l i,
      nth_error l i = Some y ->
      (m y) <--> Ensembles.Empty_set U -> 
      Union_list (map m (set_nth l i x)) <-->
        (m x) :|: (Union_list (map m l)).
  Proof.
    intros.
    generalize dependent i. generalize dependent y.
    induction l; intros; destruct i.
    - inversion H.
    - inversion H.
    - injection H as h. subst.
      simpl.
      rewrite (Union_commut (m y)).
      rewrite H0.
      rewrite Union_Empty_set_neut_r.
      reflexivity.
    - simpl. rewrite Nat.sub_0_r. rewrite IHl; eauto.
      rewrite Union_assoc. rewrite (Union_commut (m a)).
      rewrite <- Union_assoc.
      reflexivity.
  Qed.

  Theorem map_map_compose: forall {U T X} (f1: U -> T) (f2: T -> X) l,
    map f2 (map f1 l) = map (fun x => (f2 (f1 x))) l.
  Proof.
    induction l; auto.
    simpl. f_equal. auto.
  Qed.

  Lemma SplitHeapTypings_get_heaptype_some_cons: forall Shead Shead1 Shead2 l ht,
      SplitHeapTypings [LinTyp Shead1; LinTyp Shead2] (LinTyp Shead) ->
      get_heaptype l (LinTyp Shead) = Some ht ->
      get_heaptype l (LinTyp Shead1) = Some ht \/
      get_heaptype l (LinTyp Shead2) = Some ht.
  Proof.
    intros. inversion H.
    specialize (H2 _ _ H0).
    inversion H2; subst.
    - left. auto.
    - inversion H10; subst. right. auto.
      inversion H12.
  Qed.

  Theorem cons_split_empty_l: forall {T U} (L: list (T*U)) x l,
      ~ ([], l) = split (x::L).
  Proof.
    intros.
    intro.
    simpl in H.
    destruct x. destruct (split L).
    injection H as h. inversion h.
  Qed.

  Theorem cons_split_empty_r: forall {T U} (L: list (T*U)) x l,
      ~ (l, []) = split (x::L).
  Proof.
    intros.
    intro.
    simpl in H.
    destruct x. destruct (split L).
    injection H as h. inversion H.
  Qed.

  Theorem cons_split_head_inj: forall {T U} (L: list (T*U)) a a' b b' l1 l2,
      (a::l1, b::l2) = split ((a',b')::L) -> a = a' /\ b = b' /\ (l1,l2) = split L.
  Proof.
    intros.
    simpl in H. destruct (split L). injection H as h; subst. auto.
  Qed.

  Theorem Forall2_combine: forall {T U} l l1 l2 P,
      (l1, l2) = split l ->
      (Forall P l) <->
      (Forall2 (fun (x: T) (y: U) => P (x,y)) l1 l2).
  Proof.
    intros T U l. induction l; intros; split; intro; auto.
    - injection H as h. subst. auto.
    - destruct l1; destruct l2.
      exfalso. eapply cons_split_empty_l; eauto.
      exfalso. eapply cons_split_empty_l; eauto.
      exfalso. eapply cons_split_empty_r; eauto.
      destruct a.
      apply cons_split_head_inj in H. destruct H. destruct H1. subst.
      inversion H0. subst.
      apply Forall2_cons; auto.
      eapply IHl; eauto.
    - destruct l1; destruct l2.
      exfalso. eapply cons_split_empty_l; eauto.
      exfalso. eapply cons_split_empty_l; eauto.
      exfalso. eapply cons_split_empty_r; eauto.
      destruct a. apply cons_split_head_inj in H.
      destruct H. destruct H1. subst.
      inversion H0; subst.
      apply Forall_cons; eauto.
      eapply IHl; eauto.
  Qed.

  Lemma in_tpl : forall {A B} {l : list (A * B)} {l1 l2 x1 x2},
      In (x1, x2) l ->
      split l = (l1, l2) ->
      exists idx,
        nth_error l1 idx = Some x1 /\
        nth_error l2 idx = Some x2.
  Proof.
    induction l; intros;
      match goal with
      | [ H : In _ _ |- _ ] => inversion H; subst; simpl in *
      end;
      repeat match goal with
             | [ H : context[split ?L] |- _ ] => revert H
             end;
      match goal with
      | [ |- context[split ?L] ] =>
        remember (split L) as tpl;
        generalize (eq_sym Heqtpl); case tpl
      end;
      intros;
      repeat match goal with
             | [ X : _ * _ |- _ ] => destruct X; simpl in *
             end;
      match goal with
      | [ H : (_, _) = (_, _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
    - exists 0; simpl in *; auto.
    - match goal with
      | [ H : In (?X1, ?X2) _,
          H' : context[(?L1, ?L2) = (_, _) -> _] |- _ ] =>
        specialize (H' L1 L2 X1 X2 H eq_refl)
      end.
      destructAll.
      match goal with
      | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
        exists (Datatypes.S IDX)
      end.
      simpl; auto.
  Qed.

  Lemma TypeValid_QualValid : forall {F pt q},
      TypeValid F (QualT pt q) ->
      QualValid (qual F) q.
  Proof.
    intros.
    inversion H; auto.
  Qed.
   
  Lemma HasHeapType_HeapTypeValid S F hv x :
    HasHeapType S F hv x ->
    HeapTypeValid F x.
  Proof.
    intros.
    inversion H; subst; simpl in *.
    - apply VariantValid. auto.
    - constructor.
      destructAll.
      rewrite Forall_forall.
      intros.
      match goal with
      | [ X : _ * _ |- _ ] =>
        destruct X
      end.
      match goal with
      | [ H : In (_, _) _, H' : (_, _) = split _ |- _ ] =>
        specialize (in_tpl H (eq_sym H'))
      end.
      intros; destructAll.
      
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      simpl; intros; destructAll.
      eexists; split; eauto; split; [ | split; eauto ].
      -- match goal with
         | [ H : Forall _ _ |- _ ] =>
           rewrite Forall_forall in H; apply H
         end.
         eapply nth_error_In; eauto.
      -- match goal with
         | [ H : Forall3 _ _ _ ?L3,
             H' : nth_error ?L3 _ = Some _ |- _ ] =>
           specialize (forall3_nth_error_args3 H H')
         end.
         intros; destructAll.
         eapply HasType_Valid; eauto.
    - constructor; auto.
    - constructor; auto.
      eapply TypeValid_QualValid; eauto.
  Qed.

  Lemma HasHeapType_Function_Ctx : forall {S F F' hv ht},
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    HasHeapType S F hv ht ->
    HasHeapType S F' hv ht.
  Proof.
    intros.
    match goal with
    | [ H : HasHeapType _ _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    - econstructor; eauto.
      -- rewrite Forall_forall in *.
         intros.
         match goal with
         | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
           specialize (H' _ H)
         end.
         eapply TypeValid_Function_Ctx; eauto.
      -- eapply HasTypeValue_Function_Ctx; eauto.
    - econstructor; eauto.
      -- rewrite Forall3_forall.
         split; [ | eapply Forall3_length; eauto ].
         intros.
         match goal with
         | [ H : Forall3 _ _ _ _ |- _ ] =>
           rewrite Forall3_forall in H
         end.
         destructAll.
         match goal with
         | [ H : forall _ _ _ _,
               nth_error ?L1 _ = _ ->
               nth_error ?L2 _ = _ ->
               nth_error ?L3 _ = _ -> _,
             H' : nth_error ?L1 _ = _,
             H'' : nth_error ?L2 _ = _,
             H''' : nth_error ?L3 _ = _ |- _ ] =>
           specialize (H _ _ _ _ H' H'' H''')
         end.
         eapply HasTypeValue_Function_Ctx; eauto.
      -- repeat match goal with
                | [ H : _ = ?A |- context[?A] ] => rewrite <-H
                end.
         auto.
    - econstructor; eauto.
      -- eapply TypeValid_Function_Ctx; eauto.
      -- repeat match goal with
                | [ H : _ = ?A |- context[?A] ] => rewrite <-H
                end.
         auto.
      -- apply forall2_nth_error_inv;
           [ | eapply Forall2_length; eauto ].
         intros.
         match goal with
         | [ H : Forall2 _ ?L1 ?L2,
             H' : nth_error ?L1 _ = Some _,
             H'' : nth_error ?L2 _ = Some _ |- _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
         end.
         intros; simpl in *.
         eapply HasTypeValue_Function_Ctx; eauto.
    - econstructor.
      1-4: unfold heapable in *.
      1-4:
        repeat match goal with
               | [ H : _ = ?A |- context[?A] ] => rewrite <-H
               end.
      1-4: eauto.
      -- eapply TypeValid_Function_Ctx; eauto.
      -- eapply TypeValid_Function_Ctx; eauto.
         all: destruct F; subst; simpl in *.
         all: destruct F'; subst; simpl in *.
         all: auto.
      -- simpl.
         eapply HasTypeValue_Function_Ctx; eauto.
  Qed.   
    
  Lemma HasHeapType_empty_function_ctx_rev : forall {S1 F hv ht},
      HasHeapType S1 F hv ht ->
      Function_Ctx_empty F ->
      HasHeapType S1 empty_Function_Ctx hv ht.
  Proof.
    intros.
    eapply HasHeapType_Function_Ctx; [ | | | | eauto ].
    all: unfold Function_Ctx_empty in *.
    all: destructAll.
    all: destruct F; subst; simpl in *; auto.
  Qed.

  Lemma HasHeapType_update_linear_ctx_rev : forall {S F L hv ht},
      HasHeapType S (update_linear_ctx L F) hv ht ->
      HasHeapType S F hv ht.
  Proof.
    intros.
    eapply HasHeapType_Function_Ctx; [ | | | | eauto ].
    all: destruct F; subst; simpl in *; auto.
  Qed.
  
  Lemma HasHeapType_Unrestricted_LinEmpty : forall {S F v ht},
      HasHeapType S F v ht ->
      HeapTypeUnrestricted F ht ->
      qual F = [] ->
      M.is_empty (LinTyp S) = true.
  Proof.
    intros.
    match goal with
    | [ H : HasHeapType _ _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    all:
      match goal with
      | [ H : HeapTypeUnrestricted _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
    - rewrite Forall_forall in *.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply nth_error_In in H
      end.
      match goal with
      | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
        specialize (H' _ H)
      end.
      match goal with
      | [ T : Typ |- _ ] => destruct T
      end.
      eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
    - eapply SplitStoreTypings_Empty'; eauto.
      eapply Forall3_HasTypeValue_Unrestricted_LinEmpty; eauto.
      rewrite Forall_forall.
      intros.
      match goal with
      | [ H : In _ _ |- _ ] => apply In_nth_error in H
      end.
      destructAll.
      match goal with
      | [ H : _ = split _, H' : nth_error _ _ = Some _ |- _ ] =>
        specialize (split_nth_error_inv1 (eq_sym H) H')
      end.
      intros; destructAll.
      match goal with
      | [ H : nth_error ?L _ = Some _,
          H' : Forall _ ?L |- _ ] =>
        rewrite Forall_forall in H';
        apply nth_error_In in H;
        specialize (H' _ H)
      end.
      simpl in *.
      match goal with
      | [ T : Typ |- _ ] => destruct T
      end.
      auto.
    - eapply SplitStoreTypings_Empty'; eauto.
      rewrite Forall_forall.
      intros.
      match goal with
      | [ H : In _ _ |- _ ] => apply In_nth_error in H
      end.
      destructAll.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
        specialize (Forall2_length _ _ _ H); intros;
        let H'' := fresh "H" in
        assert (H'' : exists y, nth_error L2 IDX = Some y)
      end.
      { apply nth_error_some_exists.
        match goal with
        | [ H : _ = ?A |- _ < ?A ] => rewrite <-H
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
      eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
    - match goal with
      | [ H : HasTypeValue _ _ _ (_ _ (subst.subst'_qual _ ?Q))
          |- _ ] =>
        destruct Q; subst; simpl in *
      end.
      all: unfold debruijn.get_var' in *.
      all: simpl in *.
      all: unfold debruijn.get_var' in *.
      all:
        try match goal with
            | [ H : context[debruijn.weaks' debruijn.zero] |- _ ] =>
              rewrite debruijn.weaks'_zero in H
            end.
      all: unfold debruijn.var' in *.
      all: simpl in *.
      all: unfold debruijn.var in *.
      all: simpl in *.
      all: eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
  Qed.

  Theorem eq_map_get_heaptype: forall {T} m1 m2 l,
      eq_map m1 m2 -> @get_heaptype T l m1 = get_heaptype l m2.
  Proof.
    unfold eq_map. unfold get_heaptype.
    intros. apply H.
  Qed.

  Lemma map_to_values : forall {vs} (Hvs : values vs),
      vs = map Val (to_values vs Hvs).
  Proof.
    intros vs; elim vs; intros; [ simpl; auto | ].
    match goal with
    | [ H : values _ |- _ ] =>
      unfold values in H; inversion H; subst
    end.
    match goal with
    | [ H : value ?A |- _ ] =>
      unfold value in H; destruct A;
      try match goal with
          | [ H' : False |- _ ] => inversion H'
          end
    end.
    match goal with
    | [ H : forall _, ?L = _, H' : Forall value ?L |- _ ] =>
      specialize (H H')
    end.
    simpl.
    match goal with
    | [ H : context[to_values ?L ?H1]
        |- context[to_values ?L ?H2] ] =>
      let H' := fresh "H" in
      assert (H' : to_values L H1 = to_values L H2) by apply to_values_eq;
      rewrite (eq_sym H')
    end.
    match goal with
    | [ H : _ = ?A |- context[?A] ] => rewrite (eq_sym H)
    end.
    eauto.
  Qed.

  Lemma HasTypeValue_same_envs : forall S1 S2 F v t,
      HasTypeValue S1 F v t ->
      InstTyp S1 = InstTyp S2 ->
      UnrTyp S1 = UnrTyp S2 ->
      eq_map (LinTyp S1) (LinTyp S2) ->
      HasTypeValue S2 F v t.
  Proof.
    intros.
    generalize dependent S2.
    induction H; intros; try econstructor; eauto; try (erewrite <- is_empty_eq_map; eauto).
    - inversion H.
      split.
      + rewrite <- H2. rewrite <- H3. auto.
      + simpl. simpl in H6.
        inversion H6.
        split.
        ++ rewrite H7. eapply eq_map_Dom_ht. auto.
        ++ intros. apply H8. erewrite eq_map_get_heaptype; eauto.
    - rewrite <- H4. auto.
    - eapply eq_map_sym.
      eapply eq_map_trans.
      apply eq_map_sym. eauto. auto.
    - apply eq_map_sym.
      eapply eq_map_trans.
      apply eq_map_sym. eauto. auto.
    - rewrite  <- H5. auto.
  Qed.

  Lemma HasTypeValue_empty_store_typing S1 S2 F v t :
    HasTypeValue S1 F v t ->
    UnrTyp S1 = map_util.M.empty HeapType ->
    InstTyp S1 = InstTyp S2 ->
    LinTyp S1 = LinTyp S2 ->
    HasTypeValue S2 F v t.
  Proof.
    intros Htyp. 
    revert S2.
    eapply HasTypeValue_ind'
      with (P := fun S1 F v t =>
                   forall S2 (H1 : UnrTyp S1 = map_util.M.empty HeapType)
                          (H2 : InstTyp S1 = InstTyp S2)
                          (H3 : LinTyp S1 = LinTyp S2), 
                     HasTypeValue S2 F v t); intros;
      try (inv Htyp ; constructor; eauto; congruence).
    - eapply ProdTyp with (Ss := map (update_unr (UnrTyp S2)) Ss); eauto.

      + inv H. constructor; simpl in *; eauto.
        assert (Forall_map : forall A B (P : B -> Prop) (f : A -> B) xs, Forall (fun x => P (f x)) xs -> Forall P (map f xs)).
        { induction 1; constructor; auto. }
        eapply Forall_map. simpl.
        eapply Forall_impl; [| eassumption ].
        intros; simpl in *; destructAll. split; congruence.
        rewrite map_map. erewrite map_ext. rewrite <- H4. eassumption.
        intro s. reflexivity.
        
      + assert (Hin :
                 forall x, In x Ss ->
                           UnrTyp x = UnrTyp S /\ InstTyp x = InstTyp S).
        { intros. eapply SplitStoreTypings_eq_typs2. eassumption. eassumption. }
        rewrite H2 in Hin.
        revert H0 Hin. 
        clear. intros Hall Hin. induction Hall.
        now constructor; eauto.
        
        constructor.
        * eapply H; try (destruct x; simpl; reflexivity).
          eapply Hin. now left.
        * eapply IHHall. intros. eapply Hin. now right.
    - constructor; eauto. now congruence.
      rewrite H3 in H0. rewrite get_heaptype_empty in H0.
      congruence. eapply M.is_empty_1.
      eapply M.empty_1.
    - econstructor; eauto; congruence.
    - eassumption.
  Qed.

  Lemma HeapTypeUnrestricted_empty_function_ctx_rev : forall {F ht},
      HeapTypeUnrestricted F ht ->
      Function_Ctx_empty F ->
      HeapTypeUnrestricted empty_Function_Ctx ht.
    Proof.
      intros. induction H; subst; econstructor; inversion H0;
        try rewrite H1 in *; simpl in *; auto.
      rewrite H2 in *. auto. rewrite H2 in *. auto.
   Qed.

  Lemma HeapTypeValid_update_linear_ctx_rev : forall {F L ht},
      HeapTypeValid (update_linear_ctx L F) ht ->
      HeapTypeValid F ht.
    Proof.
      intros.
      generalize dependent F. revert L.
      induction ht using HeapType_ind' with
        (Q := fun t => forall F L, TypeValid (update_linear_ctx L F) t -> TypeValid F t)
        (P := fun p => forall F L q,
                  TypeValid (update_linear_ctx L F) (QualT p q) -> TypeValid F (QualT p q))
        (F := fun f => forall F L,
                  FunTypeValid (update_linear_ctx L F) f -> FunTypeValid F f)
        (A := fun a => forall F L,
                  ArrowTypeValid (update_linear_ctx L F) a -> ArrowTypeValid F a);
        intros;
        match goal with
          | [t: Typ |- _] => destruct t
          | _ => eauto
        end;
        match goal with
          | [h: TypeValid _ _ |- _] => inversion h
          | [h: HeapTypeValid _ _ |- _] => inversion h
          | [h: ArrowTypeValid _ _ |- _] => inversion h
          | [h: FunTypeValid _ _ |- _] => inversion h
        end; subst; econstructor; destruct F; simpl in *; eauto;
        try rewrite Forall_forall in *; intros; eauto.
      - eapply IHht. simpl. eauto.
      - eapply IHht. simpl. eauto.
      - clear H H4 IHht.
        generalize dependent label.
        revert  ret qual size type location linear L.
        induction l; intros.
        apply KindVarsValidNil.
        inversion H3; subst.
        apply KindVarsValidCons; eauto.
        destruct a0; simpl in *; eauto.
      - clear H H3.
        generalize dependent label.
        revert ret qual size type location linear L.
        induction l; intros; simpl in *; eauto.
        destruct a0; simpl in *; unfold subst'_function_ctx in *; simpl in *; eauto.
      - specialize (H3 _ H1). specialize (H _ H1).
        destruct x. simpl in *.
        destruct H3. exists x.
        destruct H2. split; auto.
        destruct H3. split; auto.
        destruct H4. split; auto.
        eapply H. eauto.
      - eapply IHht. simpl. eauto.
  Qed.

  Lemma HasTypeInstruction_values_locals : forall {S M F L t es L'},
      HasTypeInstruction S M F L es t L' ->
      values es ->
      LCEffEqual (size F) L L'.
  Proof.
    intros.
    induction H.
    all: try match goal with
             | [ H : values _ |- _ ] =>
               inversion H; subst; simpl in *;
               match goal with
               | [ H : False |- _ ] => inversion H
               end
             end.
    all: try apply LCEffEqual_refl.
    all: destruct F; subst; simpl in *.
    all: eauto.
    - unfold values in *; rewrite Forall_app in *.
      destructAll.
      eapply LCEffEqual_trans; eauto.
    - eapply LCEffEqual_trans; [ eapply LCEffEqual_sym | ]; eauto.
    - eapply LCEffEqual_trans; eauto.
  Qed.

  Lemma HasTypeValues_imp_HasTypeInstruction_provable : forall {idx Ss S ts vs LT F C L},
      idx = length ts ->
      SplitStoreTypings Ss S ->
      Forall3
        (fun t e S =>
           exists v,
             e = Val v /\
             HasTypeValue
               S
               (update_linear_ctx LT F)
               v t)
        ts vs Ss ->
      LocalCtxValid F L ->
      HasTypeInstruction
        S C F L vs (Arrow [] ts) L.
  Proof.
    induction idx.
    - intros.
      match goal with
      | [ H : 0 = length ?T |- _ ] =>
        destruct T; simpl in *
      end.
      2:{
        match goal with
        | [ H : 0 = Datatypes.S _ |- _ ] =>
          inversion H; subst; simpl in *
        end.
      }
      match goal with
      | [ H : Forall3 _ _ _ _ |- _ ] => inversion H; subst
      end.
      constructor; auto.
      eapply SplitStoreTypings_Empty'; eauto.
    - intros.
      match goal with
      | [ H : Datatypes.S _ = length ?T |- _ ] =>
        destruct T; simpl in *
      end.
      1:{
        match goal with
        | [ H : Datatypes.S _ = 0 |- _ ] =>
          inversion H; subst; simpl in *
        end.
      }
      match goal with
      | [ H : Forall3 _ _ _ _ |- _ ] =>
        specialize (Forall3_length _ _ _ _ H)
      end.
      intros; destructAll.
      simpl in *.
      match goal with
      | [ H : Forall3 _ ?L1 ?L2 ?L3 |- _ ] =>
        let H' := fresh "H" in
        let H'' := fresh "H" in
        assert (H' : exists l1' el1', L1 = l1' ++ [el1']);
        [ | assert (H'' : exists l2' el2', L2 = l2' ++ [el2']);
            [ | assert (H''' : exists l3' el3', L3 = l3' ++ [el3']) ] ]
      end.
      1-3: apply snoc_exists.
      1-3:
        match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] => inversion H; subst
        end.
      1-3: simpl in *.
      1-3: apply gt_Sn_O.
      destructAll.
      match goal with
      | [ H : ?A :: ?B = _ ++ _, H' : context[?A :: ?B] |- _ ] =>
        rewrite H in H'; rewrite H
      end.
      match goal with
      | [ H : Forall3 _ _ _ _ |- _ ] =>
        rewrite Forall3_snoc in H
      end.
      destructAll.
      match goal with
      | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
        specialize (SplitStoreTypings_split H)
      end.
      intros; destructAll.
      eapply ConsTyp; eauto.
      -- match goal with
         | [ H : forall _ _ _ _ _ _ _ _, _ |- _ ] =>
           eapply H; [ | eauto | eauto | eauto ]
         end.
         match goal with
         | [ H : Datatypes.S _ = Datatypes.S _ |- _ ] =>
           inversion H
         end.
         eapply snoc_cons_eq_length; eauto.
      -- match goal with
         | [ |- context[Arrow ?T _] ] =>
           replace T with (T ++ []) at 1 by apply app_nil_r
         end.
         eapply FrameTyp; eauto.
         --- rewrite Forall_forall.
             intros.
             match goal with
             | [ T : Typ |- _ ] => destruct T
             end.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- constructor.
             ---- apply HasTypeValue_update_linear_ctx.
                  eapply HasTypeValue_update_linear_ctx_rev; eauto.
             ---- destruct F; subst; simpl in *; solve_lcvs.
         --- rewrite Forall_forall.
             intros.
             match goal with
             | [ H : In _ _ |- _ ] => apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : Forall3 _ ?L1 ?L2 ?L3,
                 H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
               rewrite Forall3_forall in H; destructAll;
               let H0 := fresh "H" in
               let H1 := fresh "H" in
               assert (H0 : exists x, nth_error L2 IDX = Some x);
               [ | assert (H1 : exists x, nth_error L3 IDX = Some x) ]
             end.
             1-2: apply nth_error_some_exists.
             1-2:
               match goal with
               | [ H : nth_error ?L _ = Some _ |- _ < ?A ] =>
                 replace A with (length L); auto; try congruence
               end.
             1-2: eapply nth_error_Some_length; eauto.

             destructAll.
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
             destructAll.
             eapply HasType_Valid.
             eapply HasTypeValue_update_linear_ctx_rev; eauto.
  Qed.    

  Lemma HasTypeValues_imp_HasTypeInstruction : forall {Ss S ts vs LT F C L},
    SplitStoreTypings Ss S ->
    Forall3
      (fun t e S =>
         exists v,
           e = Val v /\
           HasTypeValue
             S
             (update_linear_ctx LT F)
             v t)
      ts vs Ss ->
    LocalCtxValid F L ->
    HasTypeInstruction
      S C F L vs (Arrow [] ts) L.
  Proof.
    intros.
    eapply HasTypeValues_imp_HasTypeInstruction_provable; eauto.
  Qed.

  Ltac use_HasTypeValues_imp_HasTypeInstruction F :=
    eapply HasTypeValues_imp_HasTypeInstruction;
    [ eauto | | destruct F; subst; simpl in *; solve_lcvs ];
    rewrite Forall3_forall;
    split; [ | eapply Forall3_length; eauto ];
    intros;
    match goal with
    | [ H : Forall3 _ ?L1 ?L2 ?L3,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _,
        H''' : nth_error ?L3 _ = Some _
        |- _ ] =>
      rewrite Forall3_forall in H;
      destruct H as [H];
      specialize (H _ _ _ _ H' H'' H''')
    end;
    destructAll;
    eexists; split; [ eauto | ];
    match goal with
    | [ H : HasTypeValue
              ?A
              (update_linear_ctx ?LT ?F)
              ?C ?D
        |- HasTypeValue
             ?A
             (update_linear_ctx _ ?F2)
             ?C ?D ] =>
      let H' := fresh "H" in
      assert
        (H' : update_linear_ctx LT F =
              update_linear_ctx LT F2);
      [ | rewrite H' in H ]
    end;
    [ destruct F; subst; simpl in *;
      auto | ];
    eauto.
  
  Lemma composition_typing_single_moreinfo S M F L1 es e ts1 ts2 L2 :
    HasTypeInstruction S M F L1 (es ++ [e]) (Arrow ts1 ts2) L2 ->
    exists ts ts1' ts2' ts3 L3 S1 S2 qf,
      ts1 = ts ++ ts1' /\
      ts2 = ts ++ ts2' /\
      Forall (fun '(QualT _ q) => QualLeq (qual F) q qf = Some true) ts /\
      QualLeq (qual F) (get_hd (linear F)) qf = Some true /\
      let F' := update_linear_ctx (set_hd qf (linear F)) F in
      HasTypeInstruction S1 M F' L1 es (Arrow ts1' ts3) L3 /\
      HasTypeInstruction S2 M F' L3 [e] (Arrow ts3 ts2') L2 /\
      SplitStoreTypings [S1; S2] S /\
      Forall (TypeValid F) ts.
  Proof.
    intros.
    specialize (composition_typing_single_strong S M F L1 es e ts1 ts2 L2). intro.
    match goal with
    | [ H : ?A -> _, H' : ?A |- _ ] => specialize (H H')
    end.
    destructAll.
    do 8 eexists; eauto.
  Qed.

  Lemma SplitStoreTypings_EmptyStoreTyping : forall {Ss IT S},
      SplitStoreTypings Ss (EmptyStoreTyping IT) ->
      In S Ss ->
      StoreTyping_eq S (EmptyStoreTyping IT).
  Proof.
    intros.
    constructor; [ | split ].
    - eapply proj2.
      eapply SplitStoreTypings_eq_typs2; eauto.
    - unfold eq_map; intros.
      unfold EmptyStoreTyping; simpl.
      unfold get_heaptype.
      rewrite M.gempty.
      match goal with
      | [ |- ?A = None ] =>
        remember A as opt;
        generalize (eq_sym Heqopt);
        case opt; intros; auto
      end.
      match goal with
      | [ H : map_util.M.find _ _ = Some _,
          H' : In _ _, H'' : SplitStoreTypings _ _ |- _ ] =>
        specialize (SplitStoreTypings_get_heaptype_LinTyp H H' H'')
      end.
      unfold EmptyStoreTyping; simpl.
      unfold get_heaptype.
      rewrite M.gempty.
      apply eq_sym.
    - eapply proj1.
      eapply SplitStoreTypings_eq_typs2; eauto.
  Qed.

  (* Two pretypes are equal without locations if
     both pretypes are equal
     *except* for the locations they contain *)
  Inductive Pretype_eq_without_loc
    : Pretype -> Pretype -> Prop :=
  | NumEq : forall nt,
      Pretype_eq_without_loc (Num nt) (Num nt)
  | TVarEq : forall v,
      Pretype_eq_without_loc (TVar v) (TVar v)
  | UnitEq : Pretype_eq_without_loc Unit Unit
  | ProdTEq : forall ts ts',
      Forall2 Typ_eq_without_loc ts ts' ->
      Pretype_eq_without_loc (ProdT ts) (ProdT ts')
  | CoderefTEq : forall ft ft',
      FunType_eq_without_loc ft ft' ->
      Pretype_eq_without_loc (CoderefT ft) (CoderefT ft')
  | RecEq : forall q t t',
      Typ_eq_without_loc t t' ->
      Pretype_eq_without_loc (Rec q t) (Rec q t')
  | PtrTEq : forall l l',
      Pretype_eq_without_loc (PtrT l) (PtrT l')
  | ExLocEq : forall t t',
      Typ_eq_without_loc t t' ->
      Pretype_eq_without_loc (ExLoc t) (ExLoc t')
  | OwnREq : forall l l',
      Pretype_eq_without_loc (OwnR l) (OwnR l')
  | CapTEq : forall c l l' ht ht',
      HeapType_eq_without_loc ht ht' ->
      Pretype_eq_without_loc (CapT c l ht) (CapT c l' ht')
  | RefTEq : forall c l l' ht ht',
      HeapType_eq_without_loc ht ht' ->
      Pretype_eq_without_loc (RefT c l ht) (RefT c l' ht')
  with Typ_eq_without_loc : Typ -> Typ -> Prop :=
  | QualTEq : forall pt pt' q,
      Pretype_eq_without_loc pt pt' ->
      Typ_eq_without_loc (QualT pt q) (QualT pt' q)
  with HeapType_eq_without_loc
       : HeapType -> HeapType -> Prop :=
  | VariantTypeEq : forall ts ts',
      Forall2 Typ_eq_without_loc ts ts' ->
      HeapType_eq_without_loc (VariantType ts) (VariantType ts')
  | StructTypeEq : forall l ts szs l' ts' szs',
      split l = (ts, szs) ->
      split l' = (ts', szs') ->
      Forall2 Typ_eq_without_loc ts ts' ->
      HeapType_eq_without_loc (StructType l) (StructType l')
  | ArrayTypeEq : forall t t',
      Typ_eq_without_loc t t' ->
      HeapType_eq_without_loc (ArrayType t) (ArrayType t')
  | ExEq : forall sz q t t',
      Typ_eq_without_loc t t' ->
      HeapType_eq_without_loc (Ex sz q t) (Ex sz q t')
  with ArrowType_eq_without_loc
         : ArrowType -> ArrowType -> Prop :=
  | ArrowEq : forall ts1 ts1' ts2 ts2',
      Forall2 Typ_eq_without_loc ts1 ts1' ->
      Forall2 Typ_eq_without_loc ts2 ts2' ->
      ArrowType_eq_without_loc (Arrow ts1 ts2) (Arrow ts1' ts2')
  with FunType_eq_without_loc
       : FunType -> FunType -> Prop :=
  | FunTEq : forall kvs atyp atyp',
      ArrowType_eq_without_loc atyp atyp' ->
      FunType_eq_without_loc (FunT kvs atyp) (FunT kvs atyp').

  Ltac unfold_typ_eq :=
    match goal with
    | [ H : Typ_eq_without_loc _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  Ltac unfold_pretype_eq :=
    match goal with
    | [ H : Pretype_eq_without_loc _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
  Ltac unfold_heaptype_eq :=
    match goal with
    | [ H : HeapType_eq_without_loc _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.

  Lemma RecVarUnderRefPretype_eq_under_loc : forall {pt pt' tctx},
      Pretype_eq_without_loc pt pt' ->
      RecVarUnderRefPretype pt tctx true ->
      RecVarUnderRefPretype pt' tctx true.
  Proof.
    eapply
      (Pretype_ind'
         (fun pt =>
            forall pt' tctx,
              Pretype_eq_without_loc pt pt' ->
              RecVarUnderRefPretype pt tctx true ->
              RecVarUnderRefPretype pt' tctx true)
         (fun t =>
            forall t' tctx,
              Typ_eq_without_loc t t' ->
              RecVarUnderRefTyp t tctx true ->
              RecVarUnderRefTyp t' tctx true)
         (fun _ => True)
         (fun _ => True)
         (fun _ => True)).
    all: try auto.
    all: intros.

    Ltac unfold_recvar_pretype :=
      match goal with
      | [ H : RecVarUnderRefPretype _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.

    - unfold_typ_eq.
      constructor.
      match goal with
      | [ H : RecVarUnderRefTyp _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      eauto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      unfold_recvar_pretype.
      constructor; auto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      constructor.
      rewrite Forall_forall.
      intros.
      rewrite Forall_forall in *.
      match goal with
      | [ H : In _ _ |- _ ] => apply In_nth_error in H
      end.
      destructAll.
      match goal with
      | [ H : Forall2 _ _ _ |- _ ] =>
        specialize (Forall2_length _ _ _ H)
      end.
      intros.
      match goal with
      | [ H : nth_error ?L ?IDX = Some _,
          H' : length ?L2 = length ?L |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : exists y, nth_error L2 IDX = Some y);
        [ apply nth_error_some_exists; rewrite H';
          eapply nth_error_Some_length; exact H | ]
      end.
      destructAll.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      intros.
      match goal with
      | [ H : forall _, _ -> _ |- _ ] => eapply H; eauto
      end.
      -- eapply nth_error_In; eauto.
      -- unfold_recvar_pretype.
         rewrite Forall_forall in *.
         match goal with
         | [ H : forall _, _ -> RecVarUnderRefTyp _ _ _ |- _ ] =>
           eapply H
         end.
         eapply nth_error_In; eauto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      unfold_recvar_pretype.
      constructor; auto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      unfold_recvar_pretype.
      constructor; auto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      constructor; auto.
    - unfold_pretype_eq.
      constructor; auto.
  Qed.

  Lemma sizeOfPretype_eq_under_loc : forall {pt pt' szs},
      Pretype_eq_without_loc pt pt' ->
      sizeOfPretype szs pt = sizeOfPretype szs pt'.
  Proof.
    eapply
      (Pretype_ind'
         (fun pt =>
            forall pt' szs,
              Pretype_eq_without_loc pt pt' ->
              sizeOfPretype szs pt = sizeOfPretype szs pt')
         (fun t =>
            forall t' szs,
              Typ_eq_without_loc t t' ->
              sizeOfType szs t = sizeOfType szs t')
         (fun _ => True)
         (fun _ => True)
         (fun _ => True)).
    all: try auto.
    all: intros.
    all: try ltac:(unfold_pretype_eq; eauto).

    - unfold_typ_eq.
      eauto.
    - unfold_pretype_eq.
      match goal with
      | [ |- _ ?A = _ ?B ] =>
        let H := fresh "H" in
        assert (H : A = B); [ | rewrite H; auto ]
      end.
      eapply forall2_map_eq.
      apply forall2_nth_error_inv;
        [ | eapply Forall2_length; eauto ].
      intros.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
      end.
      intros.
      rewrite Forall_forall in *.
      match goal with
      | [ H : forall _, _ -> _ |- _ ] => eapply H; eauto
      end.
      eapply nth_error_In; eauto.
  Qed.
    
  Ltac apply_Forall2_common_logic :=
    apply Forall2_common_logic; auto;
    intros;
    rewrite Forall_forall in *;
    eauto.

  Lemma Pretype_subst_weak_eq_without_loc_provable : forall {pt pt' f ks ks''},
      debruijn_weaks_conds f ks ks'' ->
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype f pt)
        (subst.subst'_pretype f pt').
  Proof.
    eapply
      (Pretype_ind'
         (fun pt =>
            forall pt' f ks ks'',
              debruijn_weaks_conds f ks ks'' ->
              Pretype_eq_without_loc pt pt' ->
              Pretype_eq_without_loc
                (subst.subst'_pretype f pt)
                (subst.subst'_pretype f pt'))
         (fun t =>
            forall t' f ks ks'',
              debruijn_weaks_conds f ks ks'' ->
              Typ_eq_without_loc t t' ->
              Typ_eq_without_loc
                (subst.subst'_type f t)
                (subst.subst'_type f t'))
         (fun ft =>
            forall ft' f ks ks'',
              debruijn_weaks_conds f ks ks'' ->
              FunType_eq_without_loc ft ft' ->
              FunType_eq_without_loc
                (subst.subst'_funtype f ft)
                (subst.subst'_funtype f ft'))
         (fun ht =>
            forall ht' f ks ks'',
              debruijn_weaks_conds f ks ks'' ->
              HeapType_eq_without_loc ht ht' ->
              HeapType_eq_without_loc
                (subst.subst'_heaptype f ht)
                (subst.subst'_heaptype f ht'))
         (fun atyp =>
            forall atyp' f ks ks'',
              debruijn_weaks_conds f ks ks'' ->
              ArrowType_eq_without_loc atyp atyp' ->
              ArrowType_eq_without_loc
                (subst.subst'_arrowtype f atyp)
                (subst.subst'_arrowtype f atyp'))).
    all: intros.

    - unfold_typ_eq; constructor.
      eauto.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq.
      unfold debruijn.get_var'.
      unfold debruijn_weaks_conds in *.
      destructAll.
      match goal with
      | [ H : context[_ >= ?KS _ -> _]
          |- context[_ ?KND ?V debruijn.zero] ] =>
        let H' := fresh "H" in
        assert (H' : V < KS KND \/ V >= KS KND);
        [ | case H'; intros ]
      end.
      { unfold Peano.ge.
        apply Nat.lt_ge_cases. }
      -- match goal with
         | [ H : context[_ < _ -> _] |- _ ] =>
           rewrite H; auto
         end.
      -- match goal with
         | [ H : context[_ >= _ -> _] |- _ ] =>
           rewrite H; auto
         end.
         simpl; constructor.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq; constructor.
      apply_Forall2_common_logic.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq; constructor.
      match goal with
      | [ H : forall _, _ |- _ ] => eapply H; eauto
      end.
      eapply debruijn_weaks_conds_under_knd; eauto.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq; constructor.
      match goal with
      | [ H : forall _, _ |- _ ] => eapply H; eauto
      end.
      eapply debruijn_weaks_conds_under_knd; eauto.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq; constructor.
      eauto.
    - match goal with
      | [ H : FunType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      constructor.
      match goal with
      | [ H : forall _, _ |- _ ] => eapply H; eauto
      end.
      eapply debruijn_weaks_conds_under_kindvars; eauto.
    - match goal with
      | [ H : ArrowType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      constructor.
      -- apply_Forall2_common_logic.
      -- apply_Forall2_common_logic.
    - unfold_heaptype_eq; constructor.
      apply_Forall2_common_logic.
    - unfold_heaptype_eq.
      econstructor.
      1-2: eapply split_map; eauto.
      1-2: rewrite Forall_forall.
      1-2: let x := fresh "x" in intro x; destruct x.
      1-2: eauto.
      
      apply_Forall2_common_logic.
      match goal with
      | [ H : split ?L = (?L1, _),
          H' : In _ ?L1,
          H'' : context[In _ ?L] |- _ ] =>
        apply In_nth_error in H'
      end.
      destructAll.
      match goal with
      | [ H : split ?L = _,
          H' : nth_error _ _ = Some _,
          H'' : context[In _ ?L] |- _ ] =>
        specialize (split_nth_error_inv1 H H');
        intros; destructAll
      end.
      match goal with
      | [ H : nth_error ?L _ = Some _,
          H' : context[In _ ?L] |- _ ] =>
        apply nth_error_In in H; specialize (H' _ H)
      end.
      simpl in *.
      eauto.
    - unfold_heaptype_eq; constructor.
      eauto.
    - unfold_heaptype_eq; constructor.
      match goal with
      | [ H : forall _, _ |- _ ] => eapply H; eauto
      end.
      eapply debruijn_weaks_conds_under_knd; eauto.
  Qed.

  Lemma Pretype_subst_weak_eq_without_loc : forall {pt pt' ks},
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype
           (debruijn.weaks' ks)
           pt)
        (subst.subst'_pretype
           (debruijn.weaks' ks)
           pt').
  Proof.
    intros.
    eapply Pretype_subst_weak_eq_without_loc_provable; eauto.
    apply simpl_debruijn_weak_conds.
  Qed.

  Ltac prove_StructType_case :=
      apply forall2_nth_error_inv;
      [ | repeat rewrite map_length;
          eapply Forall2_length; eauto ];
      intros;
      repeat match goal with
             | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
               specialize (nth_error_map_inv H);
               intros; destructAll; clear H
             end;
      rewrite Forall_forall in *;
      match goal with
      | [ H : split ?L = _,
          H' : nth_error _ _ = Some _,
          H'' : context[In _ ?L] |- _ ] =>
        specialize (split_nth_error_inv1 H H');
        intros; destructAll
      end;
      match goal with
      | [ H : context[In _ ?L],
          H' : nth_error ?L _ = Some _ |- _ ] =>
        apply nth_error_In in H'; specialize (H _ H');
        simpl in *; eapply H; eauto
      end;
      eapply forall2_nth_error; eauto.
  
  Lemma Pretype_subst_Pretype_eq_without_loc_provable : forall {pt pt' pts pts' f f'},
      Pretype_eq_without_loc pts pts' ->
      related_subst_conds f f' subst.SPretype pts pts' ->
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype f pt)
        (subst.subst'_pretype f' pt').
  Proof.
    eapply
      (Pretype_ind'
         (fun pt =>
            forall pt' pts pts' f f',
              Pretype_eq_without_loc pts pts' ->
              related_subst_conds f f' subst.SPretype pts pts' ->
              Pretype_eq_without_loc pt pt' ->
              Pretype_eq_without_loc
                (subst.subst'_pretype f pt)
                (subst.subst'_pretype f' pt'))
         (fun t =>
            forall t' pts pts' f f',
              Pretype_eq_without_loc pts pts' ->
              related_subst_conds f f' subst.SPretype pts pts' ->
              Typ_eq_without_loc t t' ->
              Typ_eq_without_loc
                (subst.subst'_type f t)
                (subst.subst'_type f' t'))
         (fun ft =>
            forall ft' pts pts' f f',
              Pretype_eq_without_loc pts pts' ->
              related_subst_conds f f' subst.SPretype pts pts' ->
              FunType_eq_without_loc ft ft' ->
              FunType_eq_without_loc
                (subst.subst'_funtype f ft)
                (subst.subst'_funtype f' ft'))
         (fun ht =>
            forall ht' pts pts' f f',
              Pretype_eq_without_loc pts pts' ->
              related_subst_conds f f' subst.SPretype pts pts' ->
              HeapType_eq_without_loc ht ht' ->
              HeapType_eq_without_loc
                (subst.subst'_heaptype f ht)
                (subst.subst'_heaptype f' ht'))
         (fun atyp =>
            forall atyp' pts pts' f f',
              Pretype_eq_without_loc pts pts' ->
              related_subst_conds f f' subst.SPretype pts pts' ->
              ArrowType_eq_without_loc atyp atyp' ->
              ArrowType_eq_without_loc
                (subst.subst'_arrowtype f atyp)
                (subst.subst'_arrowtype f' atyp'))).
    all: intros.
    
    Ltac solve_forall2s :=
      apply forall2_nth_error_inv;
      [
      | repeat rewrite map_length;
        eapply Forall2_length; eauto ];
      intros;
      repeat match goal with
             | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
               specialize (nth_error_map_inv H);
               intros; destructAll; clear H
             end;
      rewrite Forall_forall in *;
      match goal with
      | [ H : forall _, In _ ?L -> _,
          H' : nth_error ?L _ = Some _ |- _ ] =>
        eapply H; [ | | eauto | ]; [ | eauto | ]
      end;
      [ eapply nth_error_In; eauto
      | eapply forall2_nth_error; [ | eauto | ]; eauto ].

    - unfold_typ_eq.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      eauto.
    - unfold_pretype_eq; auto.
    - unfold_pretype_eq.
      unfold debruijn.get_var'.
      unfold related_subst_conds in *.
      destructAll.
      unfold debruijn_subst_ext_conds in *.
      destructAll.
      match goal with
      | [ H : context[_ subst.SPretype (?F subst.SPretype) _],
          H'' : context[_ subst.SPretype (?F subst.SPretype) _]
          |- context[_ subst.SPretype ?V _] ] =>
        let H' := fresh "H" in
        assert (H' : V = F subst.SPretype \/ V <> F subst.SPretype) by apply eq_dec_nat;
        case H'; intros; subst;
        [ rewrite H; rewrite H''; auto | ]
      end.
      2:{
        match goal with
        | [ H : context[_ <> ?SPEC],
            H' : context[_ <> ?SPEC],
            H'' : _ <> ?SPEC |- _ ] =>
          rewrite H; auto; rewrite H'; auto
        end.
        simpl; constructor.
      }
      simpl.
      apply Pretype_subst_weak_eq_without_loc; auto.
    - unfold_pretype_eq; auto.
    - unfold_pretype_eq.
      constructor.
      solve_forall2s.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | | auto ]
      end.
      -- match goal with
         | [ H : Pretype_eq_without_loc ?A ?B,
             H' : related_subst_conds _ _ _ ?A ?B |- _ ] =>
           exact H
         end.
      -- apply related_subst_conds_under_knd; auto.
    - unfold_pretype_eq.
      erewrite loc_related_subst_conds1; eauto; solve_ineqs.
      erewrite loc_related_subst_conds2; eauto; solve_ineqs.
    - unfold_pretype_eq.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | | auto ]
      end.
      -- match goal with
         | [ H : Pretype_eq_without_loc ?A ?B,
             H' : related_subst_conds _ _ _ ?A ?B |- _ ] =>
           exact H
         end.
      -- apply related_subst_conds_under_knd; auto.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq; constructor.
      eauto.
    - match goal with
      | [ H : FunType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      erewrite kindvars_related_subst_conds1; eauto; solve_ineqs.
      erewrite kindvars_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> ArrowType_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | | auto ]
      end.
      -- match goal with
         | [ H : Pretype_eq_without_loc ?A ?B,
             H' : related_subst_conds _ _ _ ?A ?B |- _ ] =>
           exact H
         end.
      -- apply related_subst_conds_under_kindvars; auto.
    - match goal with
      | [ H : ArrowType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      constructor; solve_forall2s.      
    - unfold_heaptype_eq; constructor.
      solve_forall2s.
    - unfold_heaptype_eq. econstructor.

      1-2: eapply split_map; eauto.
      1-2: rewrite Forall_forall.
      1-2: let x := fresh "x" in intro x; destruct x.
      1-2: eauto.

      prove_StructType_case.
    - unfold_heaptype_eq. constructor.
      eauto.
    - unfold_heaptype_eq.
      erewrite size_related_subst_conds1; eauto; solve_ineqs.
      erewrite size_related_subst_conds2; eauto; solve_ineqs.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | | auto ]
      end.
      -- match goal with
         | [ H : Pretype_eq_without_loc ?A ?B,
             H' : related_subst_conds _ _ _ ?A ?B |- _ ] =>
           exact H
         end.
      -- apply related_subst_conds_under_knd; auto.
  Qed.
  
  Lemma Pretype_subst_Pretype_eq_without_loc : forall {pt pt' pts pts'},
      Pretype_eq_without_loc pts pts' ->
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype
           (debruijn.subst'_of
              (debruijn.ext
                 subst.SPretype pts debruijn.id))
           pt)
        (subst.subst'_pretype
           (debruijn.subst'_of
              (debruijn.ext
                 subst.SPretype pts' debruijn.id))
           pt').
  Proof.
    intros.
    eapply Pretype_subst_Pretype_eq_without_loc_provable; auto.
    2:{
      exists debruijn.zero.
      split; apply simpl_debruijn_subst_ext_conds.
    }
    auto.
  Qed.

  Lemma Pretype_subst_loc_eq_without_loc_provable : forall {pt pt' l l' f f'},
      related_subst_conds f f' subst.SLoc l l' ->
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype f pt)
        (subst.subst'_pretype f' pt').
  Proof.
    eapply
      (Pretype_ind'
         (fun pt =>
            forall pt' l l' f f',
              related_subst_conds f f' subst.SLoc l l' ->
              Pretype_eq_without_loc pt pt' ->
              Pretype_eq_without_loc
                (subst.subst'_pretype f pt)
                (subst.subst'_pretype f' pt'))
         (fun t =>
            forall t' l l' f f',
              related_subst_conds f f' subst.SLoc l l' ->
              Typ_eq_without_loc t t' ->
              Typ_eq_without_loc
                (subst.subst'_type f t)
                (subst.subst'_type f' t'))
         (fun ft =>
            forall ft' l l' f f',
              related_subst_conds f f' subst.SLoc l l' ->
              FunType_eq_without_loc ft ft' ->
              FunType_eq_without_loc
                (subst.subst'_funtype f ft)
                (subst.subst'_funtype f' ft'))
         (fun ht =>
            forall ht' l l' f f',
              related_subst_conds f f' subst.SLoc l l' ->
              HeapType_eq_without_loc ht ht' ->
              HeapType_eq_without_loc
                (subst.subst'_heaptype f ht)
                (subst.subst'_heaptype f' ht'))
         (fun atyp =>
            forall atyp' l l' f f',
              related_subst_conds f f' subst.SLoc l l' ->
              ArrowType_eq_without_loc atyp atyp' ->
              ArrowType_eq_without_loc
                (subst.subst'_arrowtype f atyp)
                (subst.subst'_arrowtype f' atyp'))).
    all: intros.

    - unfold_typ_eq.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      eauto.
    - unfold_pretype_eq; auto.
    - unfold_pretype_eq.
      unfold debruijn.get_var'.
      unfold related_subst_conds in *.
      destructAll.
      unfold debruijn_subst_ext_conds in *.
      destructAll.
      match goal with
      | [ H : context[_ <> subst.SLoc],
          H' : context[_ <> subst.SLoc] |- _ ] =>
        rewrite H; solve_ineqs; rewrite H'; solve_ineqs
      end.
      simpl; constructor.
    - unfold_pretype_eq; auto.
    - unfold_pretype_eq.
      constructor.
      apply_Forall2_common_logic.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | auto ]
      end.
      apply related_subst_conds_under_knd; eauto.
    - unfold_pretype_eq.
      constructor.
    - unfold_pretype_eq.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | auto ]
      end.
      apply related_subst_conds_under_knd; eauto.
    - unfold_pretype_eq; constructor.
    - unfold_pretype_eq; constructor.
      eauto.
    - unfold_pretype_eq; constructor.
      eauto.
    - match goal with
      | [ H : FunType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      erewrite kindvars_related_subst_conds1; eauto; solve_ineqs.
      erewrite kindvars_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> ArrowType_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | auto ]
      end.
      apply related_subst_conds_under_kindvars; eauto.
    - match goal with
      | [ H : ArrowType_eq_without_loc _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      constructor; apply_Forall2_common_logic.
    - unfold_heaptype_eq; constructor.
      apply_Forall2_common_logic.
    - unfold_heaptype_eq.
      econstructor.

      1-2: eapply split_map; eauto.
      1-2: rewrite Forall_forall.
      1-2: let x := fresh "x" in intro x; destruct x.
      1-2: eauto.

      prove_StructType_case.
    - unfold_heaptype_eq. constructor.
      eauto.
    - unfold_heaptype_eq.
      erewrite size_related_subst_conds1; eauto; solve_ineqs.
      erewrite size_related_subst_conds2; eauto; solve_ineqs.
      erewrite qual_related_subst_conds1; eauto; solve_ineqs.
      erewrite qual_related_subst_conds2; eauto; solve_ineqs.
      constructor.
      match goal with
      | [ H : context[_ -> Typ_eq_without_loc _ _] |- _ ] =>
        eapply H; [ | auto ]
      end.
      apply related_subst_conds_under_knd; eauto.
  Qed.

  Lemma Pretype_subst_loc_eq_without_loc : forall {pt pt' l l'},
      Pretype_eq_without_loc pt pt' ->
      Pretype_eq_without_loc
        (subst.subst'_pretype
           (debruijn.subst'_of
              (debruijn.ext
                 subst.SLoc l debruijn.id))
           pt)
        (subst.subst'_pretype
           (debruijn.subst'_of
              (debruijn.ext
                 subst.SLoc l' debruijn.id))
           pt').
  Proof.
    intros.
    eapply Pretype_subst_loc_eq_without_loc_provable; auto.
    exists debruijn.zero.
    split; apply simpl_debruijn_subst_ext_conds.
  Qed.

  Ltac destruct_empty_ctx :=
    match goal with
    | [ H : Function_Ctx_empty ?F |- _ ] =>
      destruct F; subst; simpl in *;
      destruct H; destructAll; simpl in *; subst; auto
    end.
  
  Lemma empty_for_one_empty_for_all_provable : forall S F oldv t,
      HasTypeValue S F oldv t ->
      forall IT pt S1 F' newv,
        StoreTyping_eq S (EmptyStoreTyping IT) ->
        F = empty_Function_Ctx ->
        Typ_eq_without_loc t (QualT pt Unrestricted) ->
        Function_Ctx_empty F' ->
        HasTypeValue S1 F' newv (QualT pt Unrestricted) ->
        IT = InstTyp S1 ->
        HasTypeValue (EmptyStoreTyping IT) empty_Function_Ctx newv (QualT pt Unrestricted).
  Proof.
    eapply (HasTypeValue_ind'
              (fun S F oldv t =>
                 forall IT pt S1 F' newv,
                   StoreTyping_eq S (EmptyStoreTyping IT) ->
                   F = empty_Function_Ctx ->
                   Typ_eq_without_loc t (QualT pt Unrestricted) ->
                   Function_Ctx_empty F' ->
                   HasTypeValue S1 F' newv (QualT pt Unrestricted) ->
                   IT = InstTyp S1 ->
                   HasTypeValue (EmptyStoreTyping IT) empty_Function_Ctx newv (QualT pt Unrestricted))).
    all: intros; subst.
    all: unfold_typ_eq.
    all: unfold_pretype_eq.
    all:
      match goal with
      | [ H : HasTypeValue _ _ ?V _
	      |- HasTypeValue _ _ ?V _ ] =>
        inversion H; subst; simpl in *
      end.

    Ltac solve_bad_ref_unr_cases :=
      unfold StoreTyping_eq in *;
      destructAll;
      unfold EmptyStoreTyping in *;
      simpl in *;
      match goal with
      | [ H : get_heaptype _ ?UT = Some _,
          H' : ?UT = map_util.M.empty _ |- _ ] =>
        rewrite H' in H
      end;
      unfold get_heaptype in *;
      rewrite M.gempty in *;
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    
    Ltac solve_bad_ref_lin_cases :=
      unfold StoreTyping_eq in *;
      destructAll;
      unfold EmptyStoreTyping in *;
      simpl in *;
      match goal with
      | [ H : eq_map ?S (map_util.M.add (N.succ_pos ?L) _ _),
          H' : eq_map ?S (map_util.M.empty _) |- _ ] =>
        unfold eq_map in H; unfold eq_map in H';
        specialize (H L); specialize (H' L);
        rewrite H' in H;
        unfold get_heaptype in H;
        rewrite M.gempty in H;
        rewrite M.gss in H;
        inversion H
      end.

    - constructor; auto.
    - constructor; auto.
    - eapply ProdTyp;
        [ eapply SplitStoreTyping_eq; [ | eauto ]; eauto | | ].
      2:{
        eapply TypeValid_Function_Ctx.
        1: eapply HasType_Valid; eauto.
        all: destruct_empty_ctx.
      }
      
      rewrite Forall3_forall.
      split; [ | split ].
      2-3:
        match goal with
        | [ H : Forall3 _ _ _ _, H' : Forall3 _ _ _ _ |- _ ] =>
          specialize (Forall3_length _ _ _ _ H);
          specialize (Forall3_length _ _ _ _ H')
        end.
      2-3: intros; destructAll.
      2-3:
        match goal with
        | [ H : Forall2 _ _ _ |- _ ] =>
          specialize (Forall2_length _ _ _ H)
        end.
      2-3: intros.
      2-3: solve_inst_or_unr_typ_eq.
      
      repeat match goal with
             | [ H : Forall3 _ _ _ _ |- _ ] =>
               rewrite Forall3_forall in H
             end.
      intros; destructAll.
      match goal with
      | [ H : forall _ _ _ _,
            nth_error ?L1 _ = Some _ ->
            nth_error ?L2 _ = Some _ ->
            nth_error ?L3 _ = Some _ -> _,
          H' : nth_error ?L1P ?IDX = Some _,
          H'' : nth_error ?L2 _ = Some _,
          H''' : nth_error ?L3 _ = Some _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : exists y, nth_error L1 IDX = Some y);
        [ | let x0 := fresh "x" in
            destruct H0 as [x0 H0];
            specialize (H _ _ _ _ H0 H'' H''') ]
      end.
      { apply nth_error_some_exists.
        match goal with
        | [ H : ?A = ?B |- _ < ?A ] => rewrite H
        end.
        eapply nth_error_Some_length; eauto. }

      match goal with
      | [ H : TypeValid empty_Function_Ctx _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      rewrite Forall_forall in *.
      
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L2 ?IDX = Some _ |- _ ] =>
        specialize (Forall2_length _ _ _ H); intros;
        let H0 := fresh "H" in
        assert (H0 : exists y, nth_error L1 IDX = Some y)
      end.
      { apply nth_error_some_exists.
        match goal with
        | [ H : ?A = ?B |- _ < ?A ] => rewrite H
        end.
        eapply nth_error_Some_length; eauto. }
      destructAll.
      
      match goal with
      | [ H : context[QualLeq _ _ (QualConst Unrestricted)],
          H' : nth_error ?TAUS _ = Some ?EL,
          H'' : Forall2 _ ?TAUS _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : In EL TAUS);
        [ eapply nth_error_In; eauto | ];
        specialize (H _ H0);
        destruct EL
      end.
      match goal with
      | [ H : QualLeq [] ?Q (QualConst Unrestricted) = Some true
          |- _ ] =>
        specialize (leq_unrestricted_imp_eq_unrestricted H);
        intros; subst
      end.

      match goal with
      | [ H : nth_error _ ?IDX = Some _,
          H' : forall _ _ _ _, _ -> nth_error ?L _ = _ -> _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : exists y, nth_error L IDX = Some y)
      end.
      { apply nth_error_some_exists.
        match goal with
        | [ H : ?A = ?B |- _ < ?B ] => rewrite <-H
        end.
        eapply nth_error_Some_length; eauto. }
      destructAll.

      eapply HasTypeValue_StoreTyping_eq.
      2:{
        specialize StoreTyping_Equiv.
        let H := fresh "H" in intro H; destruct H.
        match goal with
        | [ H : Symmetric StoreTyping_eq |- _ ] => apply H
        end.
        eapply SplitStoreTypings_EmptyStoreTyping;
          [ | eapply nth_error_In; eauto ].
        eapply SplitStoreTyping_eq; eauto.
      }

      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 _ = Some _,
          H'' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H' H'');
        let H0 := fresh "H" in
        intro H0; inversion H0; subst; simpl in *
      end.
      
      match goal with
      | [ H : context[HasTypeValue (EmptyStoreTyping _)] |- _ ] =>
        eapply H; eauto
      end.
      -- eapply SplitStoreTypings_EmptyStoreTyping;
           [ | eapply nth_error_In; eauto ].
         eapply SplitStoreTyping_eq; eauto.
      -- apply eq_sym.
         eapply proj2.
         eapply SplitStoreTypings_eq_typs2; eauto.
         eapply nth_error_In; eauto.
    - constructor; auto.
      constructor; auto; [ econstructor; eauto | ].
      match goal with
      | [ H : TypeValid _ (QualT (PtrT ?L) _) |- context[?L] ] =>
        inversion H; subst; simpl in *
      end.
      destruct_empty_ctx.
    - solve_bad_ref_unr_cases.
    - solve_bad_ref_unr_cases.
    - solve_bad_ref_lin_cases.
    - solve_bad_ref_lin_cases.
    - solve_bad_ref_lin_cases.
    - match goal with
      | [ H : TypeValid _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      exfalso; eapply QualLeq_Const_False.
      destruct F'; subst; simpl in *.
      unfold Function_Ctx_empty in *.
      simpl in *; destructAll; auto.
    - unfold_typ_eq.
      match goal with
      | [ H : TypeValid empty_Function_Ctx _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : QualLeq [] ?Q (QualConst Unrestricted) = Some true
          |- _ ] =>
        specialize (leq_unrestricted_imp_eq_unrestricted H);
        intros; subst
      end.
      constructor; auto.
      -- econstructor; eauto.
         --- eapply RecVarUnderRefPretype_eq_under_loc; eauto.
         --- simpl.
             erewrite <-sizeOfPretype_eq_under_loc; eauto.
         --- simpl.
             match goal with
             | [ H : TypeValid empty_Function_Ctx _,
                 H' : TypeValid ?F _,
                 H'' : HasTypeValue _ ?F _ _ |- _ ] =>
               inversion H'; subst; simpl in *
             end.
             destruct_empty_ctx.
             eapply TypeValid_Function_Ctx; eauto.
             simpl.
             repeat rewrite pretype_weak_no_effect_on_size.
             repeat rewrite pretype_weak_no_effect_on_qual.
             match goal with
             | [ |- [(?A, _, _)] = [(?B, _, _)] ] =>
               let H := fresh "H" in
               assert (H : A = B); [ | rewrite H; auto ]
             end.
             match goal with
             | [ H : ?A = Some ?B, H' : ?C = Some ?D |- ?B = ?D ] =>
               let H0 := fresh "H" in
               assert (H0 : A = C);
               [ | rewrite H0 in H; rewrite H in H';
                   inversion H'; subst; auto ]
             end.
             erewrite <-sizeOfPretype_eq_under_loc; eauto.
      -- match goal with
         | [ H : context[HasTypeValue (EmptyStoreTyping _)] |- _ ] =>
           eapply H; eauto
         end.
         constructor.
         eapply Pretype_subst_Pretype_eq_without_loc; eauto.
    - unfold_typ_eq.
      match goal with
      | [ H : TypeValid empty_Function_Ctx _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : QualLeq [] ?Q (QualConst Unrestricted) = Some true
          |- _ ] =>
        specialize (leq_unrestricted_imp_eq_unrestricted H);
        intros; subst
      end.
      match goal with
      | [ H : TypeValid _ ?T |- context[?T] ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : Function_Ctx_empty ?F |- _ ] =>
        destruct F; subst; simpl in *;
        unfold Function_Ctx_empty in H; destructAll;
        simpl in *; subst; simpl in *
      end.
      constructor; auto.
      -- constructor; auto.
         simpl.
         eapply TypeValid_Function_Ctx; eauto.
      -- simpl.
         match goal with
         | [ H : context[HasTypeValue (EmptyStoreTyping _)] |- _ ] =>
           eapply H; eauto
         end.
         2:{
           unfold Function_Ctx_empty; simpl; auto.
         }
         constructor.
         eapply Pretype_subst_loc_eq_without_loc; eauto.
    - econstructor; eauto.
      eapply TypeValid_Function_Ctx; eauto.
      all:
        match goal with
        | [ H : Function_Ctx_empty ?F |- _ ] =>
          destruct F; subst; simpl in *;
          unfold Function_Ctx_empty in H; destructAll;
          simpl in *; subst; simpl in *; auto
        end.
  Qed.

  Lemma Typ_eq_without_loc_refl : forall {F typ},
      TypeValid F typ ->
      Typ_eq_without_loc typ typ.
  Proof.
    apply
      (TypeValid_ind'
         (fun _ t => Typ_eq_without_loc t t)
         (fun _ ht => HeapType_eq_without_loc ht ht)
         (fun _ atyp => ArrowType_eq_without_loc atyp atyp)
         (fun _ ft => FunType_eq_without_loc ft ft)).

    Ltac forall_to_forall2 :=
      eapply forall2_nth_error_inv; [ | auto ];
      intros;
      rewrite Forall_forall in *;
      match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] =>
        rewrite H in H'; inversion H'; subst
      end;
      match goal with
      | [ H' : nth_error ?L _ = Some _,
          H : forall _, In _ ?L -> Typ_eq_without_loc _ _ |- _ ] =>
        apply H
      end;
      eapply nth_error_In; eauto.

    all: intros; repeat constructor; auto.
    - unfold_typ_eq; auto.
    - forall_to_forall2.
    - unfold_typ_eq; auto.
    - forall_to_forall2.
    - match goal with
      | [ |- context[StructType ?L] ] =>
        remember (split L) as lpr;
        generalize (eq_sym Heqlpr);
        case lpr; intros
      end.
      econstructor; eauto.
      apply forall2_nth_error_inv; auto.
      intros.
      match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] =>
        rewrite H in H'; inversion H'; subst
      end.
      rewrite Forall_forall in *.

      match goal with
      | [ H : split _ = _, H' : nth_error _ _ = Some _ |- _ ] =>
        specialize (split_nth_error_inv1 H H')
      end.
      intros; destructAll.
      match goal with
      | [ H : nth_error ?L _ = Some ?EL,
          H' : context[In _ ?L] |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : In EL L); [ | specialize (H' _ H0) ]
      end.
      { eapply nth_error_In; eauto. }
      destructAll.
      simpl in *; auto.
    - unfold_typ_eq; auto.
    - forall_to_forall2.
    - forall_to_forall2.
  Qed.

  Lemma empty_for_one_empty_for_all : forall S oldv pt S1 F newv,
      HasTypeValue (EmptyStoreTyping (InstTyp S)) empty_Function_Ctx oldv (QualT pt Unrestricted) ->
      Function_Ctx_empty F ->
      HasTypeValue S1 F newv (QualT pt Unrestricted) ->
      InstTyp S = InstTyp S1 ->
      HasTypeValue (EmptyStoreTyping (InstTyp S)) empty_Function_Ctx newv (QualT pt Unrestricted).
  Proof.
    intros.
    eapply empty_for_one_empty_for_all_provable.
    - match goal with
      | [ H : HasTypeValue (EmptyStoreTyping _) _ _ _ |- _ ] =>
        exact H
      end.
    - specialize StoreTyping_Equiv.
      let H := fresh "H" in intro H; destruct H.
      match goal with
      | [ H : Reflexive StoreTyping_eq |- _ ] => apply H
      end.
    - auto.
    - eapply Typ_eq_without_loc_refl.
      eapply HasType_Valid; eauto.
    - eauto.
    - eauto.
    - auto.
  Qed.

  Theorem HasTypeLocals_weaken: forall F x y z l l' l'',
      HasTypeLocals F (x::l) (y::l') (z::l'') ->
      HasTypeLocals F l l' l''.
  Proof.
    intros.
    inversion H; subst. constructor.
    inversion H0; subst. auto.
  Qed.

  Lemma HasTypeLocals_replacement : forall {F Ss vs L j v t sz Ssnew vnew tnew tnewsz},
      HasTypeLocals F Ss vs L ->
      nth_error L j = Some (t, sz) ->
      nth_error vs j = Some v ->
      HasTypeValue Ssnew F vnew tnew ->
      sizeOfType (type F) tnew = Some tnewsz ->
      SizeLeq (size F) tnewsz sz = Some true ->
      HasTypeLocals F (set_nth Ss j Ssnew) (set_nth vs j vnew) (set_localtype j tnew sz L).
  Proof.
    intros.
    match goal with
    | [ H : HasTypeLocals _ _ _ _ |- _ ] => inversion H; subst
    end.
    constructor.
    match goal with
    | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
      generalize dependent IDX
    end.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] => induction H
    end.
    all: intros; subst; auto;
      match goal with
      | [ H : nth_error _ ?IDX = Some _ |- _ ] => destruct IDX
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inversion H; subst
      end.

    - repeat match goal with
             | [ H : Some _ = Some _ |- _ ] =>
               inversion H; subst; clear H
             end.
      simpl. unfold set_localtype. unfold nth_upd.
      apply Forall3_cons; auto.
    - simpl in *.
      rewrite Nat.sub_0_r.
      unfold set_localtype. simpl.
      apply Forall3_cons; auto.
      apply IHForall3; auto.
      eapply HasTypeLocals_weaken; eauto.
  Qed.

  Lemma HasTypeLocals_nth_error : forall {F Ss vs L j v t sz},
      HasTypeLocals F Ss vs L ->
      nth_error L j = Some (t, sz) ->
      nth_error vs j = Some v ->
      exists Ss1,
        nth_error Ss j = Some Ss1 /\
        HasTypeValue Ss1 F v t.
  Proof.
    intros.
    match goal with
    | [ H : HasTypeLocals _ _ _ _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
      generalize dependent IDX
    end.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] => induction H
    end.
    all: subst; intros;
      match goal with
      | [ H : nth_error _ ?IDX = Some _ |- _ ] => destruct IDX
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : _ = Some _ |- _ ] => inversion H; subst; simpl in *
      end.
    all:
      repeat match goal with
             | [ H : Some _ = Some _ |- _ ] =>
               inversion H; subst; simpl in *; clear H
             end.
    - eauto.
    - apply IHForall3; auto. constructor.
      auto.
  Qed.
  
  Theorem InstTyp_EmptyStoreTyping: forall (S: StoreTyping),
      (InstTyp (EmptyStoreTyping (InstTyp S))) = (InstTyp S).
  Proof.
    intros.
    destruct S. auto.
  Qed.

  Lemma HasTypeValue_add_to_unr : forall S F v t,
      HasTypeValue S F v t ->
      forall S',
        sub_map (UnrTyp S) (UnrTyp S') ->
        eq_map (LinTyp S) (LinTyp S') ->
        InstTyp S = InstTyp S' ->
        HasTypeValue S' F v t.
  Proof.
    apply
      (HasTypeValue_ind'
         (fun S F v t =>
            forall S',
              sub_map (UnrTyp S) (UnrTyp S') ->
              eq_map (LinTyp S) (LinTyp S') ->
              InstTyp S = InstTyp S' ->
              HasTypeValue S' F v t)).
    all: intros.

    Ltac solve_trivial_est_subgoal_slow :=
      econstructor; eauto;
      erewrite is_empty_eq_map; eauto;
      apply eq_map_sym; auto.
    Ltac solve_trivial_est_subgoal :=
      constructor; auto;
      erewrite is_empty_eq_map; eauto;
      apply eq_map_sym; auto.
    Ltac solve_trivial_est_subgoal_one_lin :=
      constructor; auto;
      eapply eq_map_trans; [ | eauto ];
      apply eq_map_sym; auto.
    Ltac solve_storetyping_eq_obligation :=
      match goal with
      | [ H : sub_map (UnrTyp ?S) (UnrTyp ?SP) |- _ ] =>
        let H' := fresh "H" in
        assert (H' : StoreTyping_eq (update_unr (UnrTyp SP) S) SP); eauto
      end;
      unfold update_unr;
      constructor; simpl; auto.
    Ltac solve_submap_obligation :=
      match goal with
      | [ H : sub_map ?A ?B |- sub_map ?C ?B ] =>
        let H' := fresh "H" in
        assert (H' : C = A); [ | rewrite H'; auto ]
      end;
      eapply proj1;
      eapply SplitStoreTypings_eq_typs2; eauto;
      eapply nth_error_In; eauto.

    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - (* Prod *)
      econstructor; eauto.
      -- eapply SplitStoreTyping_eq; [ | solve_storetyping_eq_obligation ].
         eapply SplitStoreTypings_apply_update_unr; eauto.
      -- rewrite Forall3_forall.
         split.
         2:{
           rewrite map_length.
           eapply Forall3_length; eauto.
         }
         match goal with
         | [ H : Forall3 _ _ _ _ |- _ ] =>
           rewrite Forall3_forall in H; destructAll
         end.
         intros.
         match goal with
         | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
           apply nth_error_map_inv in H
         end.
         destructAll.
         match goal with
         | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
         end.
         all: unfold update_unr; simpl.
         --- solve_submap_obligation.
         --- constructor.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_one_lin.
    - solve_trivial_est_subgoal_one_lin.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - econstructor; eauto.
      -- erewrite is_empty_eq_map; eauto.
         apply eq_map_sym; auto.
      -- match goal with
         | [ H : ?A = ?B |- context[?B] ] => rewrite <-H; auto
         end.
  Qed.

  Lemma HasTypeValue_update_unr : forall {IT LT UT F v t l ht},
      HasTypeValue {| InstTyp := IT; LinTyp := LT; UnrTyp := UT |} F v t ->
      get_heaptype l UT = None ->
      HasTypeValue {| InstTyp := IT; LinTyp := LT; UnrTyp := M.add (N.succ_pos l) ht UT |} F v t.
  Proof.
    intros.
    eapply HasTypeValue_add_to_unr; eauto.
    - unfold sub_map.
      intros.
      unfold update_unr; simpl in *.
      unfold get_heaptype in *.
      match goal with
      | [ |- map_util.M.find ?L1 (M.add ?L2 _ _) = Some _ ] =>
        let H := fresh "H" in
        assert (H : L1 = L2 \/ L1 <> L2) by apply eq_dec_positive;
        case H; let H' := fresh "H" in intro H'; try rewrite H' in *
      end.
      -- match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- rewrite M.gso; auto.
    - constructor.
  Qed.

  Lemma HasHeapType_add_to_unr : forall S F hv ht,
      HasHeapType S F hv ht ->
      forall S',
        sub_map (UnrTyp S) (UnrTyp S') ->
        eq_map (LinTyp S) (LinTyp S') ->
        InstTyp S = InstTyp S' ->
        HasHeapType S' F hv ht.
  Proof.
    intros.
    match goal with
    | [ H : HasHeapType _ _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    - econstructor; eauto.
      eapply HasTypeValue_add_to_unr; eauto.
    - econstructor; [ | | eauto | ]; auto.
      -- eapply SplitStoreTyping_eq; [ | solve_storetyping_eq_obligation ].
         eapply SplitStoreTypings_apply_update_unr; eauto.
      -- rewrite Forall3_forall.
         split;
           [ | rewrite map_length; eapply Forall3_length; eauto ].
         intros.
         match goal with
         | [ H : Forall3 _ _ _ _ |- _ ] =>
           rewrite Forall3_forall in H
         end.
         destructAll.
         match goal with
         | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
           apply nth_error_map_inv in H
         end.
         destructAll.
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
         eapply HasTypeValue_add_to_unr; eauto.
         all: unfold update_unr; simpl.
         --- solve_submap_obligation.
         --- constructor.
    - econstructor; auto.
      -- eapply SplitStoreTyping_eq; [ | solve_storetyping_eq_obligation ].
         eapply SplitStoreTypings_apply_update_unr; eauto.
      -- apply forall2_nth_error_inv;
           [ | rewrite map_length; eapply Forall2_length; eauto ].
         intros.
         match goal with
         | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
           apply nth_error_map_inv in H
         end.
         destructAll.
         match goal with
         | [ H : Forall2 _ ?L1 ?L2,
             H' : nth_error ?L1 _ = Some _,
             H'' : nth_error ?L2 _ = Some _ |- _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
         end.
         intros; simpl in *.
         eapply HasTypeValue_add_to_unr; eauto.
         all: unfold update_unr; simpl.
         --- solve_submap_obligation.
         --- constructor.
    - econstructor; eauto.
      eapply HasTypeValue_add_to_unr; eauto.
  Qed.
  
  Lemma HasHeapType_update_unr_add_loc : forall {S F hv ht newl newht},
      HasHeapType S F hv ht ->
      get_heaptype newl (UnrTyp S) = None ->
      HasHeapType (update_unr (M.add (N.succ_pos newl) newht (UnrTyp S)) S) F hv ht.
  Proof.
    intros.
    eapply HasHeapType_add_to_unr; eauto.
    - unfold sub_map.
      intros.
      unfold update_unr; simpl.
      unfold get_heaptype in *.
      match goal with
      | [ |- map_util.M.find ?L1 (M.add ?L2 _ _) = Some _ ] =>
        let H := fresh "H" in
        assert (H : L1 = L2 \/ L1 <> L2) by apply eq_dec_positive;
        case H; let H' := fresh "H" in intro H'; try rewrite H' in *
      end.
      -- match goal with
         | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
           rewrite H in H'; inversion H'
         end.
      -- rewrite M.gso; auto.
    - constructor.
  Qed.

  Lemma HasTypeLocals_add_to_unr : forall {F Ss Ss' locvs L},
      HasTypeLocals F Ss locvs L ->
      Forall2
        (fun S S' =>
           sub_map (UnrTyp S) (UnrTyp S') /\
           eq_map (LinTyp S) (LinTyp S') /\
           InstTyp S = InstTyp S')
        Ss Ss' ->
      HasTypeLocals F Ss' locvs L.
  Proof.
    intros.
    match goal with
    | [ H : HasTypeLocals _ _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.
    constructor.
    rewrite Forall3_forall.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] =>
      rewrite Forall3_forall in H
    end.
    destructAll.
    split; [ | split; auto ].
    2:{
      match goal with
      | [ H : _ = ?B |- _ = ?B ] => rewrite <-H
      end.
      apply eq_sym.
      eapply Forall2_length; eauto.
    }
    intros.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L2 ?IDX = Some _ |- _ ] =>
      let H'' := fresh "H" in
      assert (H'' : exists y, nth_error L1 IDX = Some y)
    end.
    { apply nth_error_some_exists.
      match goal with
      | [ H : ?A = _ |- _ < ?A ] => rewrite H
      end.
      eapply nth_error_Some_length; eauto. }
    destructAll.
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
    simpl in *.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.
    intros; simpl in *.
    destructAll.
    eapply HasTypeValue_add_to_unr; eauto.
  Qed.

  Lemma HasType_Instruction_Closure_Func_Conf_add_to_unr :
    (forall S M F L es atyp L',
        HasTypeInstruction S M F L es atyp L' ->
        forall S',
          sub_map (UnrTyp S) (UnrTyp S') ->
          eq_map (LinTyp S) (LinTyp S') ->
          InstTyp S = InstTyp S' ->
          HasTypeInstruction S' M F L es atyp L') /\
    (forall S cl ft,
        HasTypeClosure S cl ft ->
        forall S',
          sub_map (UnrTyp S) (UnrTyp S') ->
          eq_map (LinTyp S) (LinTyp S') ->
          InstTyp S = InstTyp S' ->
          HasTypeClosure S' cl ft) /\
    (forall S M f ex ft,
        HasTypeFunc S M f ex ft ->
        forall S',
          sub_map (UnrTyp S) (UnrTyp S') ->
          eq_map (LinTyp S) (LinTyp S') ->
          InstTyp S = InstTyp S' ->
          HasTypeFunc S' M f ex ft) /\
    (forall S maybe_ret i locvis locsz es taus,
        HasTypeConf S maybe_ret i locvis locsz es taus ->
        forall S',
          sub_map (UnrTyp S) (UnrTyp S') ->
          eq_map (LinTyp S) (LinTyp S') ->
          InstTyp S = InstTyp S' ->
          HasTypeConf S' maybe_ret i locvis locsz es taus).
  Proof.
    apply
      (HasType_Instruction_Closure_Func_Conf_mind
         (fun S M F L es atyp L' =>
            forall S',
              sub_map (UnrTyp S) (UnrTyp S') ->
              eq_map (LinTyp S) (LinTyp S') ->
              InstTyp S = InstTyp S' ->
              HasTypeInstruction S' M F L es atyp L')
         (fun S cl ft =>
            forall S',
              sub_map (UnrTyp S) (UnrTyp S') ->
              eq_map (LinTyp S) (LinTyp S') ->
              InstTyp S = InstTyp S' ->
              HasTypeClosure S' cl ft)
         (fun S M f ex ft =>
            forall S',
              sub_map (UnrTyp S) (UnrTyp S') ->
              eq_map (LinTyp S) (LinTyp S') ->
              InstTyp S = InstTyp S' ->
              HasTypeFunc S' M f ex ft)
         (fun S maybe_ret i locvis locsz es taus =>
            forall S',
              sub_map (UnrTyp S) (UnrTyp S') ->
              eq_map (LinTyp S) (LinTyp S') ->
              InstTyp S = InstTyp S' ->
              HasTypeConf S' maybe_ret i locvis locsz es taus)).
    all: intros.

    Ltac solve_forall2_est_subgoal :=
      apply forall2_nth_error_inv; auto;
        [ | eapply Forall2_length; eauto ];
      intros;
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : Forall2 _ ?L1 ?L2,
          H'' : nth_error ?L1 _ = Some _,
          H''' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_nth_error _ _ _ _ _ _ H H'' H''');
        specialize (forall2_nth_error _ _ _ _ _ _ H' H'' H''')
      end;
      intros; eauto.
    
    - apply ValTyp; auto.
      eapply HasTypeValue_add_to_unr; eauto.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - (* VariantCase Unr *)
      eapply VariantCaseTypUnr; eauto.
      -- erewrite is_empty_eq_map; eauto.
         apply eq_map_sym; auto.
      -- solve_forall2_est_subgoal.
    - (* VariantCase Lin *)
      eapply VariantCaseTypLin; eauto.
      -- erewrite is_empty_eq_map; eauto.
         apply eq_map_sym; auto.
      -- solve_forall2_est_subgoal. 
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal_slow.
    - (* Label *)
      econstructor; eauto.
      match goal with
      | [ H : context[_ -> HasTypeInstruction _ _ _ _ ?ES _ _]
          |- HasTypeInstruction _ _ _ _ ?ES _ _ ] =>
        eapply H
      end.
      all:
        repeat match goal with
               | [ |- context[empty_LinTyp ?S] ] =>
                 destruct S; simpl in *; auto
               end.
      constructor.
    - solve_trivial_est_subgoal_slow.
    - (* Malloc *)
      econstructor; eauto.
      eapply HasHeapType_add_to_unr; eauto.
    - solve_trivial_est_subgoal.
    - solve_trivial_est_subgoal.
    - (* ConsTyp *)
      match goal with
      | [ H : SplitStoreTypings _ _,
          H' : sub_map _ ?UT |- _ ] =>
        specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H);
        let H'' := fresh "H" in
        intro H'';
        simpl in *;
        eapply ConsTyp;
        [ eapply SplitStoreTyping_eq; [ exact H'' | ] | | ]
      end.
      1:{
        unfold update_unr.
        unfold StoreTyping_eq; simpl; auto.
      }
      all:
        match goal with
        | [ H : context[_ -> HasTypeInstruction _ _ _ _ ?ES _ _]
            |- HasTypeInstruction _ _ _ _ ?ES _ _ ] =>
          eapply H
        end.
      all: unfold update_unr; simpl; auto.
      1,3:
        match goal with
        | [ H : sub_map ?A ?C |- sub_map ?B ?C ] =>
          let H' := fresh "H" in
          assert (H' : B = A); [ | rewrite H'; auto ]
        end;
        solve_inst_or_unr_typ_eq.
      all: constructor.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - solve_trivial_est_subgoal_slow.
    - (* HasTypeClosure *)
      econstructor; eauto.
      match goal with
      | [ H : _ = _ |- _ ] => rewrite <-H; auto
      end.
    - solve_trivial_est_subgoal_slow.
    - (* HasTypeConf *)
      match goal with
      | [ H : SplitStoreTypings _ _,
          H' : sub_map _ ?UT |- _ ] =>
        specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H);
        let H'' := fresh "H" in
        intro H'';
        simpl in *;
        econstructor;
        [ | | eapply SplitStoreTyping_eq; [ exact H'' | ] | | | | ]
      end.
      all: eauto.
      -- match goal with
         | [ H : _ = _ |- _ ] => rewrite <-H; eauto
         end.
      -- unfold update_unr.
         unfold StoreTyping_eq; simpl; auto.
      -- eapply HasTypeLocals_add_to_unr; eauto.
         eapply Forall2_map_r_strong.
         intros.
         unfold update_unr; simpl.
         split; [ | split; constructor ].
         match goal with
         | [ H : sub_map ?A ?C |- sub_map ?B ?C ] =>
           let H' := fresh "H" in
           assert (H' : B = A); [ | rewrite H'; auto ]
         end.
         eapply proj1.
         eapply SplitStoreTypings_eq_typs2; eauto.
         constructor 2; auto.
      -- match goal with
         | [ H : context[_ -> HasTypeInstruction _ _ _ _ ?ES _ _]
             |- HasTypeInstruction _ _ _ _ ?ES _ _ ] =>
           eapply H
         end.
         all: unfold update_unr; simpl; auto.
         --- match goal with
             | [ H : sub_map ?A ?C |- sub_map ?B ?C ] =>
               let H' := fresh "H" in
               assert (H' : B = A); [ | rewrite H'; auto ]
             end.
             solve_inst_or_unr_typ_eq.
         --- constructor.
  Qed.

  Lemma HasTypeClosure_EmptyStoreTyping S cl ft :
    HasTypeClosure (EmptyStoreTyping (InstTyp S)) cl ft ->
    M.is_empty (LinTyp S) = true ->
    HasTypeClosure S cl ft.
  Proof.
    intros.
    specialize HasType_Instruction_Closure_Func_Conf_add_to_unr.
    let H := fresh "H" in
    let H' := fresh "H" in
    intro H; destruct H as [H [H']]; eapply H'; eauto.
    -- simpl.
       unfold sub_map.
       unfold get_heaptype.
       intros.
       rewrite M.gempty in *.
       match goal with
       | [ H : None = Some _ |- _ ] => inversion H
       end.
    -- apply eq_map_empty; auto.
  Qed.
  
  Lemma InstIndsValid_empty_Ctx_imp_any_ctx : forall ft is C,
      InstIndsValid empty_Function_Ctx ft is ->
      InstIndsValid C ft is.
  Proof.
    intros. generalize dependent ft. generalize dependent C.
    induction is; intros. constructor.
    inversion H; subst.
    econstructor.
    - match goal with
      | [ H : InstIndValid _ _ _ |- _ ] => inversion H; subst
      end.
      + constructor.
        match goal with
        | [ H : LocValid _ _ |- _ ] => inversion H; subst
        end.
        * econstructor; eauto.
        * simpl in *.
          match goal with
          | [ H : _ < 0 |- _ ] => inversion H
          end.
      + econstructor.
        eapply sizeOfPretype_empty_ctx. eauto.
        eapply SizeLeq_empty_ctx. eauto.
        * apply TypeValid_empty_ctx; auto.
        * intro. eapply NoCapsPretype_empty_ctx. eauto.
      + econstructor.
        all: try ltac:(eapply Forall_Forall; eauto; intros; apply QualLeq_empty_ctx; auto).
        apply QualValid_empty_ctx; auto.
      + econstructor.
        all: try ltac:(eapply Forall_Forall; eauto; intros; apply SizeLeq_empty_ctx; auto).
        apply SizeValid_empty_imp_all_SizeValid; auto.
    - eauto.
    - eapply IHis. eauto.
  Qed.

  Lemma InstIndsValid_update_linear_ctx F ft is :
    InstIndsValid F ft is ->
    InstIndsValid (update_linear_ctx (set_hd (QualConst Linear) (linear F)) F) ft is.
  Proof.
    intros.
    destruct ft.
    eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ].
    all: destruct F; subst; simpl in *; auto.
  Qed.

  Lemma weak_pretype_no_effect_on_quals : forall q : list Qual, subst.subst'_quals (debruijn.subst'_of (debruijn.weak subst.SPretype)) q = q.
  Proof.
    intro q; elim q; eauto.
    intros.
    simpl.
    rewrite H.
    match goal with
    | [ |- ?A :: _ = ?B :: _ ] =>
      assert (H'' : A = B)
    end.
    { destruct a; simpl; eauto. }
    rewrite H''; eauto.
  Qed.

  Lemma local_ctx_weak_subst_injective L L' :
    subst'_local_ctx (debruijn.subst'_of (debruijn.weak subst.SPretype)) L =
    subst'_local_ctx (debruijn.subst'_of (debruijn.weak subst.SPretype)) L' ->
    L = L'.
  Proof.
    intros.
    rewrite <-(local_ctx_debruijn_subst_weak (L:=L) (kndspec:=subst.SPretype) (obj:=Unit)).
    rewrite <-(local_ctx_debruijn_subst_weak (L:=L') (kndspec:=subst.SPretype) (obj:=Unit)).
    rewrite H.
    auto.
  Qed.

  Lemma HasTypeInstruction_debruijn_subst S C F L es taus1 tau taus2 L' sz q pt sz' :
    sizeOfPretype (type F) pt = Some sz' ->
    SizeLeq (size F) sz' sz = Some true ->
    SizeValid (size F) sz ->
    NoCapsPretype (heapable F) pt = true ->
    TypeValid F (QualT pt q) ->
    Function_Ctx_empty F ->
    HasTypeInstruction
      S C
      (subst'_function_ctx
         (debruijn.subst'_of (debruijn.weak subst.SPretype))
         (update_type_ctx ((sz, q, Heapable) :: type F) F))
      (subst'_local_ctx
         (debruijn.subst'_of
            (debruijn.weak subst.SPretype))
         L)
      es
      (Arrow
         ((subst.subst'_types
             (debruijn.subst'_of
                (debruijn.weak subst.SPretype))
             taus1)
            ++
            [tau])
         (subst.subst'_types
            (debruijn.subst'_of
               (debruijn.weak subst.SPretype))
            taus2))
      (subst'_local_ctx
         (debruijn.subst'_of
            (debruijn.weak subst.SPretype))
         L') ->
    HasTypeInstruction
      S C F L
      (map
         (subst.subst'_instruction
            (debruijn.subst'_of
               (debruijn.ext subst.SPretype pt debruijn.id)))
         es)
      (Arrow
         (taus1
            ++
            [subst.subst'_type
               (debruijn.subst'_of
                  (debruijn.ext subst.SPretype pt debruijn.id))
               tau])
         taus2)
      L'.
  Proof.
    intros.
    match goal with
    | [ H : HasTypeInstruction _ _ ?F _ _ _ _
        |- HasTypeInstruction _ _ ?F2 _ _ _ _ ] =>
      assert (Hfequal : InstFunctionCtxInds F [PretypeI pt] = Some F2)
    end.
    { match goal with
      | [ |- InstFunctionCtxInds ?F _ = Some ?F2 ] =>
        replace F with (add_constraints F2 [TYPE sz q Heapable]) by auto
      end.
      eapply InstInds_to_empty_InstFunctionCtxInds.
      unfold InstInds.
      simpl in *.
      eauto. }
    match goal with
    | [ H : HasTypeInstruction _ _ _ ?L _ _ _
        |- HasTypeInstruction _ _ _ ?L2 _ _ _ ] =>
      replace L2 with (subst.subst_indices [PretypeI pt] L)
    end.
    2:{
      simpl in *.
      apply local_ctx_debruijn_subst_weak.
    }
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ _ _ ?L
        |- HasTypeInstruction _ _ _ _ _ _ ?L2 ] =>
      replace L2 with (subst.subst_indices [PretypeI pt] L)
    end.
    2:{
      simpl in *.
      apply local_ctx_debruijn_subst_weak.
    }
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ ?ES _ _
        |- HasTypeInstruction _ _ _ _ ?ES2 _ _ ] =>
      replace ES2 with (map (subst.subst_indices [PretypeI pt]) ES)
    end.
    2:{
      apply map_ext; auto.
    }
    match goal with
    | [ H : HasTypeInstruction _ _ _ _ _ (Arrow ?TAUS _) _
        |- HasTypeInstruction _ _ _ _ _ (Arrow ?TAUS2 _) _ ] =>
      replace TAUS2 with (subst.subst_indices [PretypeI pt] TAUS)
    end.
    1:
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ _ (Arrow _ ?TAUS) _
          |- HasTypeInstruction _ _ _ _ _ (Arrow _ ?TAUS2) _ ] =>
        replace TAUS2 with (subst.subst_indices [PretypeI pt] TAUS)
      end.

    2-3: simpl.
    2-3: unfold subst.subst'_types.
    3: rewrite map_app.
    3: simpl.
    3:
      match goal with
      | [ |- ?A ++ _ = ?B ++ _ ] => replace B with A at 2; auto
      end.
    2-3: unfold subst.subst'_types.
    2-3: simpl.
    2-3: rewrite map_map.
    2-3: rewrite <-map_id.
    2-3: apply map_ext.
    2-3: intros.
    2-3: rewrite type_debruijn_subst_weak; auto.

    eapply HasTypeInstruction_subst_indices; eauto.

    - econstructor; eauto.
      -- econstructor; eauto.
      -- simpl; eauto.
      -- constructor.
    - match goal with
      | [ |- context[_ :: ?X] ] =>
        replace X with (@nil KindVar) by auto
      end.
      constructor; simpl; auto.
    - constructor; constructor; auto.
      eapply TypeValid_QualValid; eauto.

    Unshelve.
    all: repeat constructor.
  Qed.
  
  Lemma set_preserves_doms : forall {l q m v sz m' v'},
      get l q m = Some (v, sz) ->
      set l q m v' = Some m' ->
      MemUtils.dom_lin m <--> MemUtils.dom_lin m' /\
      MemUtils.dom_unr m <--> MemUtils.dom_unr m'.
  Proof.
    intros.
    destruct q.
    all: split; [ unfold MemUtils.dom_lin | unfold MemUtils.dom_unr ].
    all: unfold MemUtils.dom.
    all: split.
    all: unfold Ensembles.Included.
    all: unfold Ensembles.In.
    all: intros; destructAll.
    all: assert (Hlinunr : Linear <> Unrestricted) by solve_ineqs.
    all: assert (Hunrlin : Unrestricted <> Linear) by solve_ineqs.
    all:
      try match goal with
          | [ H : set _ ?M1 _ _ = Some ?NMEM,
              H' : ?M1 <> ?M2
              |- context[get ?L ?M2 ?NMEM] ] =>
            erewrite <-get_set_other_mem; eauto
          end.
    all:
      try match goal with
          | [ H : set _ ?M1 ?OMEM _ = Some _,
              H' : ?M1 <> ?M2
              |- context[get ?L ?M2 ?OMEM] ] =>
            erewrite get_set_other_mem; eauto
          end.
    all:
      match goal with
      | [ H : set ?L1 _ _ _ = Some _,
          H' : get ?L2 _ _ = Some _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : L1 = L2 \/ L1 <> L2) by apply eq_dec_N;
        case H0; intros; subst
      end.
    all: eauto.
    all:
      try match goal with
          | [ H : set ?L _ _ _ = Some ?NMEM
              |- context[get ?L _ ?NMEM] ] =>
            specialize (get_set_same _ _ _ _ _ H);
            intros; destructAll; eauto
          end.
    all:
      try match goal with
          | [ H : set _ _ _ _ = Some ?NMEM
              |- context[get _ _ ?NMEM] ] =>
            erewrite <-get_set_other_loc; eauto
          end.
    all: erewrite get_set_other_loc; eauto.
  Qed.

  Lemma alloc_to_list_Permutation : forall {mem1 q sz hv mem2 loc},
      alloc mem1 q sz hv = Some (mem2, loc, sz) ->
      Permutation.Permutation ((loc, hv, sz) :: (M.to_list q mem1)) (M.to_list q mem2).
  Proof.
    intros.
    match goal with
    | [ H : alloc ?MEM ?M _ _ = Some (_, ?L, _) |- _ ] =>
      assert (Hlemma : forall hv sz,
                 ~ In (L, hv, sz) (M.to_list M MEM))
    end.
    { intros; intro.
      match goal with
      | [ H : In _ _ |- _ ] => apply In_nth_error in H
      end.
      destructAll.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply in_to_list_implies_get in H
      end.
      match goal with
      | [ H : alloc _ _ _ _ = Some (_, ?L, _) |- _ ] =>
        specialize (alloc_fresh _ _ _ _ _ _ H L)
      end.
      match goal with
      | [ |- (?A -> _) -> _ ] =>
        let H := fresh "H" in
        let H' := fresh "H" in
        assert (H : A); [ | intro H'; specialize (H' H) ]
      end.
      { split; [ apply N.le_refl | ].
        apply N.lt_add_pos_r.
        eapply N.lt_lt_0.
        eapply alloc_size.
        apply eq_sym; eauto. }
      match goal with
      | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
        rewrite H in H'; inversion H'
      end. }
      
    apply Permutation.NoDup_Permutation.
    - constructor; [ | apply to_list_NoDup ].
      eauto.
    - apply to_list_NoDup.
    - let x := fresh "x" in
      intro x; destruct x as [[curL curHV] curSz].
      constructor; intros.
      -- match goal with
         | [ H : In _ (_ :: _) |- _ ] =>
           inversion H; subst; simpl in *
         end.
         --- match goal with
             | [ H : (_, _, _) = (_, _, _) |- _ ] =>
               inversion H; subst; simpl in *
             end.
             match goal with
             | [ H : alloc _ _ _ _ = Some _ |- _ ] =>
               apply get_alloc_same in H;
               apply get_implies_in_to_list in H
             end.
             destructAll.
             eapply nth_error_In; eauto.
         --- match goal with
             | [ H : In (?L2, _, _) _,
                 H' : alloc _ _ _ _ = Some (_, ?L, _) |- _ ] =>
               let H'' := fresh "H" in
               assert (H'' : L2 = L \/ L2 <> L) by apply eq_dec_N;
               case H''; intros; subst;
               [ exfalso;
                 match goal with
                 | [ H : forall _ _, ~ _ |- _ ] => eapply H
                 end;
                 eauto | ]
             end.
             match goal with
             | [ H : In _ _ |- _ ] => apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : alloc _ _ _ _ = Some _,
                 H' : _ <> _ |- _ ] =>
               specialize (get_alloc_other_loc _ _ _ _ _ _ _ H H')
             end.
             intros.
             match goal with
             | [ H : get ?L ?M ?MEM = Some _,
                 H' : get _ _ _ = get ?L ?M ?MEM |- _ ] =>
               rewrite H in H';
               apply get_implies_in_to_list in H'
             end.
             destructAll.
             eapply nth_error_In; eauto.
      -- match goal with
         | [ |- In (?L2, _, _) ((?L1, _, _) :: _) ] =>
           let H := fresh "H" in
           assert (H : L2 = L1 \/ L2 <> L1) by apply eq_dec_N;
           case H; intros; subst
         end.
         --- constructor.
             match goal with
             | [ H : In _ _ |- _ ] => apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : alloc _ _ _ _ = Some _ |- _ ] =>
               specialize (get_alloc_same _ _ _ _ _ _ H)
             end.
             intros.
             match goal with
             | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
               rewrite H in H'; inversion H'; subst; simpl in *
             end.
             auto.
         --- constructor 2.
             match goal with
             | [ H : In _ _ |- _ ] =>
               apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : alloc _ _ _ _ = Some _,
                 H' : _ <> _ |- _ ] =>
               specialize (get_alloc_other_loc _ _ _ _ _ _ _ H H')
             end.
             intros.
             match goal with
             | [ H : get ?L ?M ?MEM = Some _,
                 H' : get ?L ?M ?MEM = get _ _ _ |- _ ] =>
               rewrite H' in H;
               apply get_implies_in_to_list in H
             end.
             destructAll.
             eapply nth_error_In; eauto.
  Qed.

  Lemma alloc_to_list_Permutation_diff_qual : forall {mem1 q1 sz hv mem2 loc q2},
      alloc mem1 q1 sz hv = Some (mem2, loc, sz) ->
      q2 <> q1 ->
      Permutation.Permutation (M.to_list q2 mem1) (M.to_list q2 mem2).
  Proof.
    intros.
    apply Permutation.NoDup_Permutation;
    [ apply to_list_NoDup | apply to_list_NoDup | ].
    let x := fresh "x" in
    intro x; destruct x as [[curL curHV] curSz].
    constructor; intros.
    all:
      match goal with
      | [ H : In _ _ |- _ ] => apply In_nth_error in H
      end.
    all: destructAll.
    all:
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        apply in_to_list_implies_get in H
      end.
    all:
      match goal with
      | [ H : get ?L ?M2 _ = Some _,
          H' : alloc _ ?M _ _ = Some _,
          H'' : ?M2 <> ?M |- _ ] =>
        specialize (get_alloc_other_mem _ _ _ L _ _ _ _ H' H'')
      end.
    all: intros.
    all:
      match goal with
      | [ H : ?A = Some _, H' : ?A = ?B |- _ ] =>
        rewrite H' in H
      | [ H : ?A = Some _, H' : ?B = ?A |- _ ] =>
        rewrite (eq_sym H') in H
      end.
    all:
      match goal with
      | [ H : get _ _ _ = Some _ |- _ ] =>
        apply get_implies_in_to_list in H
      end.
    all: destructAll.
    all: eapply nth_error_In; eauto.
  Qed.

  Lemma set_to_list_Permutation : forall {A l m oldmem newmem idx oldv oldsz newv newsz} {f1 : _ -> A} {f2 newel},
      nth_error (M.to_list m oldmem) idx = Some (l, oldv, oldsz) ->
      set l m oldmem newv = Some newmem ->
      get l m newmem = Some (newv, newsz) ->
      (forall '(loc, hv, len),
          In (loc, hv, len) (M.to_list m newmem) ->
          f2 (loc, hv, len) =
          if (loc =? l)%N
          then newel
          else f1 (loc, hv, len)) ->
      Permutation.Permutation
        (set_nth (map f1 (M.to_list m oldmem)) idx newel)
        (map f2 (M.to_list m newmem)).
  Proof.
    intros.
    match goal with
    | [ H : nth_error (M.to_list _ _) _ = Some _ |- _ ] =>
      specialize (in_to_list_implies_get _ _ _ _ _ _ H)
    end.
    intros.
    match goal with
    | [ H : get ?L ?M _ = Some (?HV, ?SZ),
        H' : get ?L ?M _ = Some (?HVP, ?SZP),
        H'' : nth_error (M.to_list ?M _) ?IDX = Some (?L, ?HV, ?SZ) |- _ ] =>
      apply (Permutation_gen_change_one (g:=(fun '(loc, hv, len) => if (loc =? L)%N then (L, HVP, SZP) else (loc, hv, len))) (g':=(fun '(loc, hv, len) => if (loc =? L)%N then (L, HV, SZ) else (loc, hv, len))) (idx:=IDX) (in_elem:=(L, HV, SZ)))
    end.
    - apply to_list_NoDup.
    - apply to_list_NoDup.
    - auto.
    - let x := fresh "x" in
      intro x;
      destruct x as [[curL curHV] curSz].
      assert (Hloc_eq : curL = l \/ curL <> l).
      { apply eq_dec_N. }
      split; [ | split; [ | split ] ].
      -- case Hloc_eq; intros; subst.
         --- rewrite N.eqb_refl.
             match goal with
             | [ H : get _ _ ?T = Some (_, _) |- context[?T] ] =>
               apply get_implies_in_to_list in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply nth_error_In in H
             end.
             auto.
         --- assert (Hneq : (curL =? l)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             rewrite Hneq.
             assert (Hneq2 : l <> curL).
             { intros; eauto. }
             match goal with
             | [ H : set _ _ _ _ = Some _ |- _ ] =>
               specialize (get_set_other_loc _ _ _ _ _ _ H Hneq2)
             end.
             intros.
             match goal with
             | [ H : In ?TPL _ |- In ?TPL _ ] =>
               apply In_nth_error in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : get ?A ?B ?C = _,
                 H' : get ?A ?B ?C = get _ _ _ |- _ ] =>
               rewrite H' in H;
               apply get_implies_in_to_list in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply nth_error_In in H
             end.
             auto.
      -- case Hloc_eq; intros; subst.
         --- repeat rewrite N.eqb_refl.
             match goal with
             | [ H : In ?TPL _ |- _ = ?TPL ] =>
               apply In_nth_error in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply in_to_list_implies_get in H
             end.
             unfold get_mem in *.
             match goal with
             | [ H : get ?A ?B ?C = _,
                 H' : get ?A ?B ?C = _ |- _ ] =>
               rewrite H in H'; inversion H'; subst; simpl in *
             end.
             auto.
         --- assert (Hneq : (curL =? l)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             repeat rewrite Hneq.
             auto.
      -- let H := fresh "H" in intro H; inversion H; subst; simpl in *.
         rewrite N.eqb_refl.
         match goal with
         | [ H : context[f2 _ = _]
             |- context[f2 ?TPL] ] =>
           specialize (H TPL)
         end.
         simpl in *.
         match goal with
         | [ H : In ?A ?B -> f2 _ = _ |- _ ] =>
           let H' := fresh "H" in
           assert (H' : In A B);
             [ | specialize (H H'); rewrite H ]
         end.
         { match goal with
           | [ H : get _ _ ?MEM = Some _ |- context[?MEM] ] =>
             apply get_implies_in_to_list in H
           end.
           destructAll.
           eapply nth_error_In; eauto. }
         rewrite N.eqb_refl; auto.
      -- intros.
         assert (Hneq : curL <> l).
         { intro; subst.
           match goal with
           | [ H : In ?TPL (M.to_list _ _) |- _ ] =>
             apply In_nth_error in H;
             let x := fresh "x" in
             destruct H as [x H];
             apply in_to_list_implies_get in H
           end.
           unfold get_mem in *.
           match goal with
           | [ H : get ?A ?B ?C = _,
               H' : get ?A ?B ?C = _ |- _ ] =>
             rewrite H in H'; inversion H'; subst; simpl in *
           end.
           eauto. }
         assert (Hneq2 : (curL =? l)%N = false).
         { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
         rewrite Hneq2.
         match goal with
         | [ H : context[f2 _ = _]
             |- context[f2 ?TPL] ] =>
           specialize (H TPL)
         end.
         simpl in *.
         match goal with
         | [ H : In ?A ?B -> f2 _ = _ |- _ ] =>
           let H' := fresh "H" in
           assert (H' : In A B);
             [ | specialize (H H');
                 unfold M.Loc in H;
                 rewrite H ]
         end.
         { match goal with
           | [ H : ?L1 <> ?L2 |- _ ] =>
             assert (Hneq3 : L2 <> L1) by ltac:(intro; eauto)
           end.
           match goal with
           | [ H : set _ _ _ _ = Some _ |- _ ] =>
             specialize (get_set_other_loc _ _ _ _ _ _ H Hneq3)
           end.
           intros.
           match goal with
           | [ H : In ?TPL _ |- _ ] =>
             apply In_nth_error in H
           end.
           destructAll.
           match goal with
           | [ H : nth_error _ _ = Some (?L, _, _)
               |- context[?L] ] =>
             apply in_to_list_implies_get in H
           end.
           match goal with
           | [ H : ?A = Some (_, _),
               H' : ?A = get _ _ _ |- _ ] =>
             rewrite H' in H;
             apply get_implies_in_to_list in H
           end.
           destructAll.
           eapply nth_error_In; eauto. }                   
         rewrite Hneq2; auto.
    - let x := fresh "x" in
      intro x;
      destruct x as [[curL curHV] curSz].
      assert (Hloc_eq : curL = l \/ curL <> l).
      { apply eq_dec_N. }
      split; [ | split; [ | split ] ].
      -- case Hloc_eq; intros; subst.
         --- rewrite N.eqb_refl.
             unfold get_mem in *.
             match goal with
             | [ H : get _ _ ?T = Some (_, _) |- context[?T] ] =>
               apply get_implies_in_to_list in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply nth_error_In in H
             end.
             auto.
         --- assert (Hneq : (curL =? l)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             rewrite Hneq.
             assert (Hneq2 : l <> curL).
             { intros; eauto. }
             match goal with
             | [ H : set _ _ _ _ = Some _ |- _ ] =>
               specialize (get_set_other_loc _ _ _ _ _ _ H Hneq2)
             end.
             intros.
             match goal with
             | [ H : In ?TPL _ |- In ?TPL _ ] =>
               apply In_nth_error in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply in_to_list_implies_get in H
             end.
             match goal with
             | [ H : get ?A ?B ?C = _,
                 H' : get _ _ _ = get ?A ?B ?C |- _ ] =>
               rewrite (eq_sym H') in H;
               apply get_implies_in_to_list in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply nth_error_In in H
             end.
             auto.
      -- case Hloc_eq; intros; subst.
         --- repeat rewrite N.eqb_refl.
             match goal with
             | [ H : In ?TPL _ |- _ = ?TPL ] =>
               apply In_nth_error in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply in_to_list_implies_get in H
             end.
             unfold get_mem in *.
             match goal with
             | [ H : get ?A ?B ?C = _,
                 H' : get ?A ?B ?C = _ |- _ ] =>
               rewrite H in H'; inversion H'; subst; simpl in *
             end.
             auto.
         --- assert (Hneq : (curL =? l)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             repeat rewrite Hneq.
             auto.
      -- case Hloc_eq; intros; subst.
         --- match goal with
             | [ H : context[f2 _ = _],
                 H' : In ?TPL _
                 |- context[f2 ?TPL] ] =>
               specialize (H TPL H');
               unfold M.Loc in H;
               rewrite H
             end.
             rewrite N.eqb_refl; auto.
         --- assert (Hneq : (curL =? l)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             rewrite Hneq in *.
             match goal with
             | [ H : (_, _, _) = (_, _, _) |- _ ] =>
               inversion H; subst; simpl in *
             end.
             exfalso.
             eauto.
      -- intros.
         assert (Hneq : curL <> l).
         { intro; subst.
           rewrite N.eqb_refl in *.
           eauto. }
         assert (Hneq2 : (curL =? l)%N = false).
         { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
         rewrite Hneq2.
         match goal with
         | [ H : context[f2 _ = _],
             H' : In ?TPL _
             |- context[f2 ?TPL] ] =>
           specialize (H TPL H');
           unfold M.Loc in H;
           rewrite H
         end.
         rewrite Hneq2; auto.
  Qed.

  Lemma HasHeapType_Struct_replace : forall {Ss0 taus szs vs newtau newv idx newtaus oldtau Svnew Snew F newtausz oldtausz},
      length taus = length szs ->
      ReplaceAtIdx idx taus newtau = Some (newtaus, oldtau) ->
      Forall (fun sz => SizeValid [] sz) szs ->
      Forall2
        (fun tau sz =>
           exists sztau,
             sizeOfType [] tau = Some sztau /\
             SizeLeq [] sztau sz = Some true)
        taus
        szs ->
      Forall3
        (fun S' v t =>
           HasTypeValue
             S' empty_Function_Ctx v t)
        Ss0 vs taus ->
      SplitStoreTypings
        (set_nth Ss0 idx Svnew) Snew ->
      HasTypeValue Svnew F newv newtau ->
      Function_Ctx_empty F ->
      nth_error szs idx = Some oldtausz ->
      sizeOfType (type F) newtau = Some newtausz ->
      SizeLeq (size F) newtausz oldtausz = Some true ->
      HasHeapType
        Snew
        empty_Function_Ctx
        (Struct (set_nth vs idx newv))
        (StructType
           (combine
              newtaus szs)).
  Proof.
    intros.
    econstructor.
    - eauto.
    - eapply Forall3_set_nth; eauto.
      eapply HasTypeValue_empty_function_ctx_rev; eauto.
    - match goal with
      | [ |- (?A, _) = split (combine ?B ?C) ] =>
        assert (Hgoal : (A, C) = (B, C))
      end.
      { match goal with
        | [ H : ReplaceAtIdx _ _ _ = Some _ |- _ ] =>
          specialize (ReplaceAtIdx_nth_error _ _ _ _ _ H)
        end.
        intro.
        subst.
        auto. }

      rewrite combine_split; eauto.
      match goal with
      | [ H : (_, _) = (_, _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
      rewrite length_set_nth; auto.
    - split; [ simpl; auto | ].
      match goal with
      | [ H : nth_error ?L ?IDX = Some ?SZ |- Forall2 _ _ ?L ] =>
        specialize (set_nth_nth_error _ _ _ H)
      end.
      intro H'''''; rewrite H'''''.
      eapply Forall2_set_nth; eauto.
      simpl.
      match goal with
      | [ H : sizeOfType _ ?T = Some ?ST |-
          context[sizeOfType _ ?T = Some _] ] =>
        exists ST
      end.
      match goal with
      | [ H : Function_Ctx_empty ?F |- _ ] =>
        revert H; unfold Function_Ctx_empty;
        destruct F; subst; simpl in *
      end.
      intros; destructAll; subst; auto.
  Qed.

  Lemma StructLinear_WellTyped : forall {F Sh Sp Sh' Sp' Ss0 Svnew Snew mem1 mem2 locc vis oldsz idx v f_lin f_lin' taus szs newtau newtausz oldtau oldtausz newtaus},
      length taus = length szs ->
      set locc Linear mem1 (Struct (set_nth vis idx v)) = Some mem2 ->
      In (locc, Struct vis, oldsz) (M.to_list Linear mem1) ->
      (forall x,
          In x (M.to_list Linear mem1) ->
          let '(loc, hv, len) := x in
          exists ht,
            NoCapsHeapType [] ht = true /\
            (get_heaptype loc (LinTyp Sh) = Some ht \/
             get_heaptype loc (LinTyp Sp) = Some ht) /\
            HasHeapType (f_lin x) empty_Function_Ctx hv ht /\
            RoomForStrongUpdates len ht /\
            HeapTypeValid empty_Function_Ctx ht) ->
      NoCapsHeapType
        [] (StructType (combine taus szs)) = true ->
      RoomForStrongUpdates
        oldsz (StructType (combine taus szs)) ->
      HeapTypeValid
        empty_Function_Ctx
        (StructType (combine taus szs)) ->
      SplitStoreTypings
        Ss0 (f_lin (locc, Struct vis, oldsz)) ->
      Forall
        (fun sz : Size => SizeValid [] sz) szs ->
      Forall2
        (fun tau sz =>
           exists sztau,
             sizeOfType [] tau = Some sztau /\
             SizeLeq [] sztau sz = Some true)
        taus
        szs ->
      Forall3
        (fun S' v t =>
           HasTypeValue S' empty_Function_Ctx v t)
        Ss0
        vis
        taus ->
      SplitStoreTypings
        (set_nth Ss0 idx Svnew) Snew ->
      ReplaceAtIdx idx taus newtau =
      Some (newtaus, oldtau) ->
      Function_Ctx_empty F ->
      HasTypeValue Svnew F v newtau ->
      nth_error szs idx = Some oldtausz ->
      TypeValid F newtau ->
      NoCapsTyp (heapable F) newtau = true ->
      sizeOfType (type F) newtau = Some newtausz ->
      SizeLeq (size F) newtausz oldtausz = Some true ->
      (forall '(loc, hv, len),
          In (loc, hv, len)
             (M.to_list Linear mem2) ->
          f_lin' (loc, hv, len) =
          if (loc =? locc)%N then
            Snew else
            f_lin (loc, hv, len)) ->
      get_heaptype locc (LinTyp Sp') =
      Some (StructType (combine newtaus szs)) ->
      (forall l t,
          (l =? locc)%N = false ->
          get_heaptype l (LinTyp Sh) = Some t \/
          get_heaptype l (LinTyp Sp) = Some t ->
          get_heaptype l (LinTyp Sh') = Some t \/
          get_heaptype l (LinTyp Sp') = Some t) ->
      Forall2
        (fun S '(loc, hv, len) =>
           exists ht,
             NoCapsHeapType [] ht = true /\
             (get_heaptype loc (LinTyp Sh') = Some ht \/
              get_heaptype loc (LinTyp Sp') = Some ht) /\
             HasHeapType S empty_Function_Ctx hv ht /\
             RoomForStrongUpdates len ht /\
             HeapTypeValid empty_Function_Ctx ht)
        (map f_lin' (M.to_list Linear mem2))
        (M.to_list Linear mem2).
  Proof.
    intros.
    rewrite forall2_map.
    intro T; destruct T as [A len']; destruct A as [loc' hv']; subst; simpl in *.
    intros.
    match goal with
    | [ H : set _ _ _ ?HV = Some _,
        H' : context[(_ =? ?B)%N]
        |- _ ] =>
      assert (Hcases : if (loc' =? B)%N then hv' = HV else In (loc', hv', len') (M.to_list Linear mem1));
        [ | remember ((loc' =? B)%N) as b' ]
    end.
    { match goal with
      | [ |- context[(?L =? ?L2)%N] ] =>
        remember (L =? L2)%N as newb;
        revert Heqnewb;
        case newb
      end.
      - let H := fresh "H" in
        intro H; specialize (Ndec.Neqb_complete _ _ (eq_sym H)).
        intros; subst.
        match goal with
        | [ H : In (_, ?HV, _) _ |- context[?HV] ] =>
          apply In_nth_error in H
        end.
        destructAll.
        match goal with
        | [ H : nth_error _ _ = Some (_, ?HV, _) |-
            context[?HV] ] =>
          apply in_to_list_implies_get in H
        end.
        match goal with
        | [ H : set _ _ _ _ = Some _ |- _ ] =>
          specialize (get_set_same _ _ _ _ _ H)
        end.
        intros; destructAll.
        match goal with
        | [ H : ?A = Some (_, _),
            H' : ?A = Some (_, _) |- _ ] =>
          rewrite H in H'; inversion H'; subst
        end.
        auto.
      - match goal with
        | [ |- false = (?L =? ?L2)%N -> _ ] =>
          intros; assert (Hneq_loc : L2 <> L)
        end.
        { rewrite (iff_sym (OrdersEx.N_as_OT.eqb_neq _ _)).
          rewrite N.eqb_sym; eauto. }
        match goal with
        | [ H : set _ _ _ _ = Some _,
            H' : _ <> _ |- _ ] =>
          specialize (get_set_other_loc _ _ _ _ _ _ H H')
        end.
        intros.
        match goal with
        | [ H : In ?TPL _ |- In ?TPL _ ] =>
          apply In_nth_error in H
        end.
        destructAll.
        match goal with
        | [ H : nth_error _ _ = Some ?TPL |- In ?TPL _ ] =>
          apply in_to_list_implies_get in H
        end.
        match goal with
        | [ H : get ?L ?M ?MEM = Some _,
            H' : get _ _ _ = get ?L ?M ?MEM |- _ ] =>
          rewrite H in H';
          apply get_implies_in_to_list in H'
        end.
        destructAll.
        eapply nth_error_In; eauto. }

    revert Heqb' Hcases.
    case b'; intros; subst.
    -- match goal with
       | [ H : true = (?A =? ?B)%N |- _ ] =>
         assert (Heq' : A = B)
       end.
       { rewrite (iff_sym (N.eqb_eq _ _)).
         eauto. }
       subst.
       match goal with
       | [ H : get_heaptype _ _ = Some ?HT |- _ ] =>
         exists HT
       end.
       split.
       { match goal with
         | [ H : ReplaceAtIdx _ _ _ = Some _ |- _ ] =>
           specialize (ReplaceAtIdx_nth_error _ _ _ _ _ H)
         end.
         intros; subst.
         unfold NoCapsHeapType.
         rewrite combine_split; simpl;
           [ | rewrite length_set_nth; eauto ].
         match goal with
         | [ H : context[split (combine _ _)] |- _ ] =>
           rewrite combine_split in H; [ | eauto ]
         end.
         simpl in *.

         apply forallb_set_nth; [ eauto | ].
         match goal with
         | [ H : Function_Ctx_empty ?F |- _ ] =>
           revert H; destruct F; subst; simpl in *
         end.
         unfold Function_Ctx_empty.
         simpl; intros; destructAll.
         unfold heapable in *.
         simpl in *.
         auto. }

       split; [ eauto | ].

       split.
       { eapply HasHeapType_Struct_replace; eauto.
         match goal with
         | [ H : context[In _ ?LST -> f_lin' _ = _],
             H' : In ?TPL ?LST |- _ ] =>
           specialize (H TPL H');
           unfold M.Loc in H;
           unfold M.Val in H;
           unfold Len in H;
           rewrite H
         end.
         rewrite N.eqb_refl.
         eauto. }
       split.
       --- eapply StructTypeFits.
           ---- rewrite combine_split; [ eauto | ].
                match goal with
                | [ H : ReplaceAtIdx _ _ _ = _ |- _ ] =>
                  apply ReplaceAtIdx_nth_error in H
                end.
                subst.
                rewrite length_set_nth; auto.
           ---- match goal with
                | [ H : RoomForStrongUpdates _ _ |- _ ] =>
                  inversion H; subst; simpl in *;
                    [ exfalso; auto | ]
                end.

                match goal with
                | [ H : split (combine _ _) = (_, _) |- _ ] =>
                  rewrite combine_split in H;
                    inversion H; subst; auto
                end.
                unfold get_mem in *.
                match goal with
                | [ H : In _ (M.to_list _ ?MEM),
                    H' : set ?L ?M ?MEM _ = Some _ |- _ ] =>
                  apply In_nth_error in H
                end.
                destructAll.
                match goal with
                | [ H : nth_error (M.to_list _ ?MEM) _ = _,
                    H' : set ?L ?M ?MEM _ = Some _ |- _ ] =>
                  apply in_to_list_implies_get in H
                end.
                match goal with
                | [ H : get ?L ?M ?MEM = Some (_, _),
                    H' : set ?L ?M ?MEM _ = Some _ |- _ ] =>
                  specialize (get_set_same_size _ _ _ _ _ _ _ H H')
                end.
                intros.
                match goal with
                | [ H : In (_, _, ?SZ) _ |- (_ <= ?SZ)%N ] =>
                  apply In_nth_error in H; destructAll
                end.
                match goal with
                | [ H : nth_error _ _ = Some (_, _, ?SZ) |-
                    (_ <= ?SZ)%N ] =>
                  apply in_to_list_implies_get in H
                end.
                match goal with
                | [ H : get ?L ?M ?MEM = _,
                    H' : get ?L ?M ?MEM = _ |- _ ] =>
                  rewrite H in H';
                  inversion H'; subst; simpl in *
                end.
                auto.
       --- match goal with
           | [ H : HeapTypeValid _ _ |- _ ] =>
             inversion H; subst; simpl in *
           end.
           econstructor.

           match goal with
           | [ H : ReplaceAtIdx ?IDX ?LOLD ?TNEW = Some (?LNEW, _), H' : nth_error ?L2 ?IDX = Some ?T2 |- context[combine ?LNEW ?L2] ] =>
             assert (Heq_combine : combine LNEW L2 = set_nth (combine LOLD L2) IDX (TNEW, T2))
           end.
           { match goal with
             | [ H : ReplaceAtIdx _ _ _ = _ |- _ ] =>
               apply ReplaceAtIdx_nth_error in H
             end.
             subst.
             apply set_nth_combine_first_comp; auto. }
           rewrite Heq_combine.
           eapply Forall_set_nth; auto.
           simpl.
           match goal with
           | [ H : Function_Ctx_empty ?F |- _ ] =>
             revert H; unfold Function_Ctx_empty;
             destruct F; subst; simpl in *
           end.
           intros; destructAll; subst.
           eexists; eauto.
           split; [ eauto | ].
           split; [ | split; [ | eauto ] ].
           ---- match goal with
                | [ H : nth_error _ _ = Some ?T |- context[?T] ] =>
                  apply nth_error_In in H
                end.
                match goal with
                | [ H : Forall _ ?SZL,
                    H' : In ?SZ ?SZL |-
                    context[?SZ] ] =>
                  rewrite Forall_forall in H;
                  specialize (H _ H')
                end.
                auto.
           ---- eapply TypeValid_sub; eauto.
                unfold empty_Function_Ctx.
                constructor; simpl; eauto.
                all: constructor.
    -- match goal with
       | [ H : context[NoCapsHeapType _ _], H' : In _ (M.to_list Linear _) |- _ ] =>
         specialize (H _ H')
       end.
       simpl in *; destructAll.
       eexists; split; eauto.
       split; [ eauto | ].
       split; [ | eauto ].
       match goal with
       | [ H : context[In _ ?LST -> f_lin' _ = _],
           H' : In ?TPL ?LST |- _ ] =>
         specialize (H TPL H');
         unfold M.Loc in H;
         unfold M.Val in H;
         unfold Len in H;
         rewrite H
       end.
       match goal with
       | [ H : false = ?A |- context[?A] ] =>
         rewrite (eq_sym H)
       end.
       auto.
  Qed.

  Ltac derive_mappings f_lin f_unr :=
    match goal with
    | [ H : Forall2 _ _ (M.to_list Linear (meminst _)),
        X : StoreTyping |- _ ] =>
      specialize (forall2_to_func eq_dec_tpl _ _ _ X H)
    end;
    let H1 := fresh "H" in
    intro H1;
    destruct H1 as [f_lin];
    [ apply to_list_NoDup | ];
    match goal with
    | [ H : Forall2 _ _ (M.to_list Unrestricted (meminst _)),
        X : StoreTyping |- _ ] =>
      specialize (forall2_to_func eq_dec_tpl _ _ _ X H)
    end;
    let H2 := fresh "H" in
    intro H2;
    destruct H2 as [f_unr];
    [ apply to_list_NoDup | ].
    
  Lemma HasTypeStore_LinInstruction : forall {S Sstack S_ignore Ss Sh Sp S_lin S_unr Sh' Sp' Sstack' S' S1 S2 S3 s s' l1 v sz F loc' t q idx},
      get_mem s l1 Linear = Some (v, sz) ->
      update_mem s l1 Linear (Array 0 []) = Some s' ->
      Forall2
        (fun (i : MInst) (C : Module_Ctx) =>
           HasTypeInstance (InstTyp S) i C)
        (inst s) (InstTyp Sp) ->
      HasTypeValue S1 F (Ref (LocP l1 Linear)) (QualT (RefT W loc' t) q) ->
      map_util.M.is_empty (LinTyp S2) = true ->
      SplitStoreTypings [S1; S2] Sstack ->
      SplitStoreTypings (Sstack :: S_ignore ++ Ss) Sp ->
      SplitStoreTypings [Sp; Sh] S ->
      SplitStoreTypings [Sp'; Sh'] S' ->
      SplitStoreTypings [S3; Sh'] Sh ->
      SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' ->
      SplitStoreTypings [S3; {| InstTyp := InstTyp Sh; LinTyp := M.add (N.succ_pos l1) (ArrayType (QualT Unit Unrestricted)) (M.empty HeapType); UnrTyp := UnrTyp Sh |}] Sstack' ->
      nth_error (M.to_list Linear (meminst s)) idx = Some (l1, v, sz) ->
      MemUtils.dom_lin (meminst s) <--> Dom_ht (LinTyp Sh) :|: Dom_ht (LinTyp Sp) ->
      MemUtils.dom_unr (meminst s) <--> Dom_ht (UnrTyp Sh) :|: Dom_ht (UnrTyp Sp) ->
      SplitStoreTypings (S_lin ++ S_unr) Sh ->
      Forall2
        (fun (S : StoreTyping) '(loc, hv, len) =>
         exists ht : HeapType,
           NoCapsHeapType [] ht = true /\
           (get_heaptype loc (LinTyp Sh) = Some ht \/
            get_heaptype loc (LinTyp Sp) = Some ht) /\
           HasHeapType S empty_Function_Ctx hv ht /\
           RoomForStrongUpdates len ht /\
           HeapTypeValid empty_Function_Ctx ht) S_lin
        (M.to_list Linear (meminst s)) ->
      Forall2
        (fun (S : StoreTyping) '(loc, hv, len) =>
         exists ht : HeapType,
           NoCapsHeapType [] ht = true /\
           get_heaptype loc (UnrTyp S) = Some ht /\
           HasHeapType S empty_Function_Ctx hv ht /\
           RoomForStrongUpdates len ht /\
           HeapTypeValid empty_Function_Ctx ht) S_unr
        (M.to_list Unrestricted (meminst s)) ->
      nth_error S_lin idx = Some S3 ->
      HasTypeStore s' Sh' Sp'.
  Proof.
    intros.
    assert (Hinst : InstTyp Sp = InstTyp Sp') by solve_inst_or_unr_typ_eq.
    assert (Hunr : UnrTyp Sp = UnrTyp Sp') by solve_inst_or_unr_typ_eq.  
    match goal with
    | [ H : update_mem ?S ?L ?Q ?HV = Some ?SP |- _ ] =>
      unfold update_mem in H; simpl in H;
      remember (set L Q (meminst S) HV) as new_mem;
      revert Heqnew_mem; revert H;
      case new_mem;
      [ |
        let H := fresh "H" in
        intro H; inversion H; auto ]
    end.
    intros.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; simpl in *
    end.
    econstructor; eauto; simpl in *.
    - assert (Hinst2 : InstTyp S' = InstTyp S) by solve_inst_or_unr_typ_eq.
      rewrite (eq_sym Hinst).
      rewrite Hinst2.
      auto.
    - match goal with
      | [ |- HasTypeMeminst _ _ ?T ] =>
        assert (Hsubgoal : exists S_lin' S_unr',
                Forall2
                  (fun (S0 : StoreTyping) '(loc, hv, len) =>
                   exists ht : HeapType,
                     NoCapsHeapType [] ht = true /\
                     (get_heaptype loc (LinTyp Sh') = Some ht \/
                      get_heaptype loc (LinTyp Sp') = Some ht) /\
                     HasHeapType S0 empty_Function_Ctx hv ht /\
                     RoomForStrongUpdates len ht /\
                     HeapTypeValid empty_Function_Ctx ht) S_lin'
                  (M.to_list Linear T) /\
                Forall2
                  (fun (S0 : StoreTyping) '(loc, hv, len) =>
                   exists ht : HeapType,
                     NoCapsHeapType [] ht = true /\
                     get_heaptype loc (UnrTyp S0) = Some ht /\
                     HasHeapType S0 empty_Function_Ctx hv ht /\
                     RoomForStrongUpdates len ht /\
                     HeapTypeValid empty_Function_Ctx ht) S_unr'
                  (M.to_list Unrestricted T) /\
                Forall
                  (fun S' : StoreTyping =>
                   InstTyp Sh' = InstTyp S' /\ UnrTyp Sh' = UnrTyp S')
                  (S_lin' ++ S_unr') /\
                SplitHeapTypings (map LinTyp (S_lin' ++ S_unr')) (LinTyp Sh'))
      end.
      { derive_mappings f_lin f_unr.

        match goal with
        | [ H : get_mem _ ?L ?M = Some (?HV, ?SZ) |- context[M.to_list _ ?T] ] =>
          remember (map (fun '(loc, hv, len) => if (BinNatDef.N.eqb loc L) then (empty_LinTyp Sh') else f_lin (loc, hv, len)) (M.to_list Linear T)) as S_lin';
          remember (map f_unr (M.to_list Unrestricted T)) as S_unr'
        end.

        match goal with
        | [ H : S_unr = map f_unr ?T1 /\ _,
            H' : S_unr' = map f_unr ?T2 |- _ ] =>
          assert (Hperm : Permutation.Permutation T1 T2)
        end.
        { apply Permutation.NoDup_Permutation.
          - apply to_list_NoDup.
          - apply to_list_NoDup.
          - intros; constructor; intros.
            -- match goal with
               | [ H : In _ _ |- _ ] => apply In_nth_error in H
               end.
               destructAll.
               match goal with
               | [ H : nth_error (M.to_list _ _) _ = Some ?X |- _ ] =>
                 destruct X as [[curL curHV] curSz];
                 apply in_to_list_implies_get in H
               end.
               assert (Hneq : Linear <> Unrestricted).
               { intro H''''; inversion H''''. }
               match goal with
               | [ H : Some _ = set _ _ _ _ |- _ ] =>
                 specialize (get_set_other_mem _ _ _ curL _ _ _ (eq_sym H) Hneq)
               end.
               intros.
               match goal with
               | [ H : ?A = ?B, H' : ?A = get _ _ ?T |- context[?T] ] =>
                 rewrite H' in H;
                 apply get_implies_in_to_list in H;
                 destruct H as [curIdx H];
                 apply nth_error_In in H
               end.
               auto.
            -- match goal with
               | [ H : In _ _ |- _ ] => apply In_nth_error in H
               end.
               destructAll.
               match goal with
               | [ H : nth_error (M.to_list _ _) _ = Some ?X |- _ ] =>
                 destruct X as [[curL curHV] curSz];
                 apply in_to_list_implies_get in H
               end.
               assert (Hneq : Linear <> Unrestricted).
               { intro H''''; inversion H''''. }
               match goal with
               | [ H : Some _ = set _ _ _ _ |- _ ] =>
                 specialize (get_set_other_mem _ _ _ curL _ _ _ (eq_sym H) Hneq)
               end.
               intros.
               match goal with
               | [ H : ?A = ?B, H' : get _ _ ?T = ?A |- context[?T] ] =>
                 rewrite (eq_sym H') in H;
                 apply get_implies_in_to_list in H;
                 destruct H as [curIdx H];
                 apply nth_error_In in H
               end.
               auto. }

        exists S_lin', S_unr'.
        split; [ | split; [ | split ] ].
        - subst.
          apply Forall2_map_l_strong.
          let x := fresh "x" in intro x; destruct x as [[curL curHV] curLen].
          intros.
          assert (Hloc_eq : curL = l1 \/ curL <> l1).
          { apply eq_dec_N. }
          match goal with
          | [ H : In _ (M.to_list _ _) |- _ ] =>
            apply In_nth_error in H
          end.
          destructAll.
          match goal with
          | [ H : nth_error (M.to_list _ _) _ = _ |- _ ] =>
            apply in_to_list_implies_get in H
          end.
          case Hloc_eq; intros; subst.
          -- rewrite N.eqb_refl.
             match goal with
             | [ H : Some _ = set _ _ _ _ |- _ ] =>
               specialize (get_set_same _ _ _ _ _ (eq_sym H))
             end.
             intros; destructAll.
             match goal with
             | [ H : get ?A ?B ?C = _, H' : get ?A ?B ?C = _ |- _ ] =>
               rewrite H in H'; inversion H'; subst; simpl in *
             end.
             exists (ArrayType (QualT Unit Unrestricted)).
             split; auto.
             split.
             { right.
               eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sstack')); [ | | eauto ].
               - match goal with
                 | [ H : SplitStoreTypings [_; ?A] Sstack' |- _ ] =>
                   eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=A)); [ | | exact H ]
                 end.
                 -- simpl.
                    unfold get_heaptype.
                    rewrite M.gss; auto.
                 -- unfold In; auto.
               - unfold In; auto. }
             split.
             { eapply ArrayHT.
               - assert (Hgoal : SplitStoreTypings [] (empty_LinTyp Sh')); [ | eauto ].
                 constructor; eauto.
                 unfold empty_LinTyp.
                 simpl.
                 destruct Sh'.
                 simpl.
                 constructor.
                 -- unfold Union_list; simpl.
                    unfold Dom_ht.
                    constructor;
                      unfold Ensembles.Included;
                      unfold Ensembles.In;
                      let x := fresh "x" in
                      let H := fresh "H" in
                      intros x H;
                      inversion H.
                    match goal with
                    | [ H : map_util.M.find _ (map_util.M.empty _) = _ |- _ ] =>
                      rewrite M.gempty in H; inversion H
                    end.
                 -- unfold get_heaptype.
                    intro; intro.
                    rewrite M.gempty.
                    let H := fresh "H" in intro H; inversion H.
                 -- constructor.
                    econstructor; eauto.
               - apply QualLeq_Refl.
               - constructor; eauto.
                 simpl.
                 match goal with
                 | [ |- context[empty_LinTyp ?S] ] =>
                   destruct S; unfold empty_LinTyp
                 end.
                 simpl.
                 apply SplitHeapTypings_nil_Empty.
               - simpl; auto.
               - constructor. }
             split; [ constructor; auto | ].
             constructor.
             --- constructor.
                 eapply QualConstValid; eauto.
             --- apply QualLeq_Refl.
          -- assert (Hneq : (curL =? l1)%N = false).
             { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
             rewrite Hneq.
             assert (Hneq2 : l1 <> curL) by eauto.
             match goal with
             | [ H : Some _ = set _ _ _ _ |- _ ] =>
               specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) Hneq2)
             end.
             intros.
             match goal with
             | [ H : get _ _ ?T = ?B, H' : ?C = get _ _ ?T |- _ ] =>
               rewrite (eq_sym H') in H;
               apply get_implies_in_to_list in H;
               destruct H as [curIdx H];
               apply nth_error_In in H;
               match goal with
               | [ H'' : forall _, In _ (M.to_list _ _) -> _ |- _ ] => apply H'' in H; destruct H as [newHt H]
               end
             end.
             destructAll.
             exists newHt.
             split; [ auto | split; [ | eauto ] ].
             match goal with
             | [ H : get_heaptype _ _ = _ \/ get_heaptype _ _ = _ |- _ ] => case H; intros
             end.
             --- match goal with
                 | [ H : SplitStoreTypings [_; _] Sh |- _ ] => inversion H; subst; simpl in *
                 end.
                 match goal with
                 | [ H : get_heaptype _ ?L = Some _,
                     H' : SplitHeapTypings _ ?L |- _ ] =>
                   specialize (SplitHeapTypings_get_heaptype_some_cons _ _ _ _ _ H' H)
                 end.
                 let H := fresh "H" in
                   intro H; case H; [ | eauto ].
                 intros.
                 right.
                 eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sstack')); [ | | eauto ].
                 ---- match goal with
                      | [ H : SplitStoreTypings [?A; _] Sstack' |- _ ] =>
                        eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=A)); [ eauto | | exact H ]
                      end.
                      unfold In; eauto.
                 ---- unfold In; eauto.
             --- match goal with
                 | [ H : get_heaptype _ (LinTyp ?S) = _,
                     H' : SplitStoreTypings _ ?S |- _ ] =>
                   specialize (SplitStoreTypings_inv H H')
                 end.
                 intros; destructAll.
                 match goal with
                 | [ H : In _ (_ :: _) |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 ---- match goal with
                      | [ H : get_heaptype _ (LinTyp ?X) = _,
                          H' : SplitStoreTypings _ ?X |- _ ] =>
                        inversion H'
                      end.
                      simpl in *.
                      match goal with
                      | [ H : get_heaptype _ ?L = _,
                          H' : SplitHeapTypings _ ?L |- _ ] =>
                        specialize (SplitHeapTypings_get_heaptype_some_cons _ _ _ _ _ H' H)
                      end.
                      let H := fresh "H" in
                        intro H; case H.
                      ----- intros.
                            match goal with
                            | [ H : HasTypeValue ?X _ _ _,
                                H' : get_heaptype _ (LinTyp ?X) = _ |- _ ] => inversion H; subst; simpl in *
                            end.
                            unfold eq_map in *.
                            match goal with
                            | [ H : get_heaptype _ ?L = _,
                                H' : forall _, get_heaptype _ ?L = _ |- _ ] =>
                              rewrite H' in H;
                              unfold get_heaptype in H;
                              rewrite M.gso in H;
                              [ rewrite M.gempty in H; inversion H | ]
                            end.
                            intro Hsucc_eq.
                            assert (Hloc_eq2 : curL = l1).
                            { rewrite (eq_sym (N.pos_pred_succ curL)).
                              rewrite (eq_sym (N.pos_pred_succ l1)).
                              rewrite Hsucc_eq.
                              auto. }
                            eauto.
                      ----- unfold get_heaptype at 1.
                            rewrite map_find_empty; [ | auto ].
                            let H := fresh "H" in
                              intro H; inversion H.
                 ---- right.
                      eapply SplitStoreTypings_get_heaptype_LinTyp; [ eauto | | eauto ].
                      right; auto.
        - destructAll; subst.
          apply Forall2_map_l_strong.
          intros.
          match goal with
          | [ H : Permutation.Permutation ?A ?B,
              H' : In _ ?B |- _ ] =>
            apply Permutation.Permutation_sym in H;
            specialize (Permutation.Permutation_in _ H H')
          end.
          intro Hin.
          match goal with
          | [ H : forall _, In _ (M.to_list Unrestricted _) -> _ |- _ ] =>
            specialize (H _ Hin)
          end.
          eauto.
        - rewrite Forall_app.
          repeat rewrite Forall_forall.
          split; intros; subst.
          all:
            match goal with
            | [ H : In _ (map _ _) |- _ ] =>
              rewrite in_map_iff in H
            end.
          all: destructAll.
          -- match goal with
             | [ H : In ?X (M.to_list Linear _) |- _ ] =>
               destruct X as [[curL curHV] curSz];
               apply In_nth_error in H
             end.
             destructAll.
             match goal with
             | [ H : nth_error (M.to_list _ _) _ = _ |- _ ] =>
               apply in_to_list_implies_get in H
             end.
             assert (Hloc_eq : curL = l1 \/ curL <> l1).
             { apply eq_dec_N. }
             case Hloc_eq; intros; subst.
             --- rewrite N.eqb_refl.
                 unfold empty_LinTyp.
                 destruct Sh'.
                 simpl; auto.
             --- assert (Hneq : (curL =? l1)%N = false).
                 { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
                 rewrite Hneq.
                 assert (Hneq2 : l1 <> curL).
                 { let H := fresh "H" in intro H; eauto. }
                 match goal with
                 | [ H : Some _ = set _ _ _ _ |- _ ] =>
                   specialize (get_set_other_loc _ _ _ curL _ _ (eq_sym H) Hneq2)
                 end.
                 intros.
                 match goal with
                 | [ H : get ?A ?B ?C = _,
                     H' : _ = get ?A ?B ?C |- _ ] =>
                   rewrite (eq_sym H') in H;
                   apply get_implies_in_to_list in H
                 end.
                 destructAll.
                 match goal with
                 | [ H : nth_error _ _ = Some _ |- _ ] =>
                   apply nth_error_In in H;
                   specialize (in_map f_lin _ _ H)
                 end.
                 intros.
                 match goal with
                 | [ H : In ?O ?A, H' : SplitStoreTypings (?A ++ ?B) _ |- _ ] =>
                   inversion H'; subst; simpl in *;
                     assert (Hin : In O (A ++ B))
                 end.
                 { apply in_or_app; eauto. }
                 match goal with
                 | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
                   rewrite Forall_forall in H;
                   specialize (H _ H')
                 end.
                 assert (Hinst2 : InstTyp Sh' = InstTyp Sh) by solve_inst_or_unr_typ_eq.
                 assert (Hunr2 : UnrTyp Sh' = UnrTyp Sh) by solve_inst_or_unr_typ_eq.
                 rewrite Hinst2.
                 rewrite Hunr2.
                 auto.
          -- rewrite Permutation_comm in Hperm.
             match goal with
             | [ H : Permutation.Permutation ?A ?B, H' : In _ ?A |- _ ] =>
               specialize (Permutation.Permutation_in _ H H')
             end.
             let H := fresh "H" in intro H; specialize (in_map f_unr _ _ H).
             intros.
             match goal with
             | [ H : In ?O ?B, H' : SplitStoreTypings (?A ++ ?B) _ |- _ ] =>
               inversion H'; subst; simpl in *;
                 assert (Hin : In O (A ++ B))
             end.
             { apply in_or_app; eauto. }
             match goal with
             | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
               rewrite Forall_forall in H;
               specialize (H _ H')
             end.
             assert (Hinst2 : InstTyp Sh' = InstTyp Sh) by solve_inst_or_unr_typ_eq.
             assert (Hunr2 : UnrTyp Sh' = UnrTyp Sh) by solve_inst_or_unr_typ_eq.
             rewrite Hinst2.
             rewrite Hunr2.
             auto.
        - assert (Hperm2 : Permutation.Permutation S_unr' S_unr).
          { destructAll.
            apply Permutation.Permutation_map.
            apply Permutation.Permutation_sym; auto. }
          match goal with
          | [ H : nth_error (M.to_list Linear _) ?IDX = Some ?TPL,
              H' : nth_error _ ?IDX = Some ?V |- _ ] =>
            assert (Hperm3 : Permutation.Permutation S_lin' (set_nth S_lin IDX (empty_LinTyp Sh')))
          end.
          { apply Permutation.Permutation_sym.

            destructAll.
            match goal with
            | [ H : Some _ = set _ _ _ _ |- _ ] =>
              specialize (get_set_same _ _ _ _ _ (eq_sym H))
            end.
            intros; destructAll.
            eapply set_to_list_Permutation; eauto.
            let x := fresh "x" in
            intro x; destruct x as [[curL curHV] curSz].
            intros; auto. }            

          specialize (Permutation.Permutation_sym (Permutation.Permutation_map LinTyp (Permutation.Permutation_app Hperm3 Hperm2))).
          intros.
          eapply SplitHeapTypings_permut; eauto.

          rewrite set_nth_app;
            [ | eapply nth_error_Some_length; eauto ].
          match goal with
          | [ H : SplitStoreTypings (?S1 ++ _) Sh,
              H' : SplitStoreTypings [_; _] Sh,
              H'' : nth_error ?S1 ?IDX = Some _ |- _ ] =>
            specialize (SplitStoreTypings_remove_one _ _ _ _ IDX H H')
          end.
          match goal with
          | [ |- (?A -> _) -> _ ] =>
            let H := fresh "H" in assert (H : A);
            [ | let H' := fresh "H" in
                intro H'; specialize (H' H); inversion H' ]
          end.
          { rewrite nth_error_app1; eauto.
            eapply nth_error_Some_length; eauto. }
          simpl in *; eauto. }
      destruct Hsubgoal as [S_lin' [S_unr' Hsubgoal]].
      destructAll.

      unfold get_mem in *.
      match goal with
      | [ H : get ?L ?Q ?MEM = Some _,
          H' : Some _ = set ?L ?Q ?MEM _ |- _ ] =>
        specialize (set_preserves_doms H (eq_sym H'))
      end.
      intros.
      destructAll.

      apply (MeminstT _ S_lin' S_unr').
      -- eapply Same_set_trans; [ eapply Same_set_sym; eauto | ].
         eapply Same_set_trans.
         1:
           match goal with
           | [ H : MemUtils.dom_lin ?MEM <--> Dom_ht _ :|: Dom_ht _ |- context[?MEM] ] =>
             exact H
           end.
         constructor.
         --- unfold Ensembles.Included.
             unfold Ensembles.In.
             intros.
             match goal with
             | [ H : (_ :|: _) _ |- _ ] =>
               inversion H; subst; simpl in *
             end.
             ---- unfold Ensembles.In in *.
                  unfold Dom_ht in *.
                  unfold Ensembles.In in *.
                  unfold Dom_map in *.
                  destructAll.
                  match goal with
                  | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some ?HT |- _ ] =>
                    let H' := fresh "H" in
                    assert (H' : get_heaptype L (LinTyp S) = Some HT);
                      [ unfold get_heaptype; eauto | ];
                    match goal with
                    | [ H'' : SplitStoreTypings [_; _] S |- _ ] =>
                      specialize (SplitStoreTypings_inv H' H'')
                    end
                  end.
                  intros; destructAll.
                  match goal with
                  | [ H : In _ [_; _] |- _ ] =>
                    inversion H; subst; simpl in *
                  end.
                  ----- right.
                        unfold Ensembles.In.
                        match goal with
                        | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT,
                            H' : SplitStoreTypings [?S; _] ?SPP,
                            H'' : SplitStoreTypings (?SPP :: ?A ++ ?B) ?SP
                            |-
                            exists _, map_util.M.find (N.succ_pos ?L) (LinTyp ?SP) = _ ] =>
                          exists HT;
                          eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=SPP));
                            [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ] | | exact H'' ]
                        end.
                        ------ auto.
                        ------ constructor; auto.
                        ------ constructor; auto.
                  ----- match goal with
                        | [ H : _ \/ False |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        ------ left.
                               unfold Ensembles.In.
                               eexists; eauto.
                        ------ exfalso; auto.
             ---- unfold Ensembles.In in *.
                  unfold Dom_ht in *.
                  unfold Ensembles.In in *.
                  unfold Dom_map in *.
                  destructAll.
                  match goal with
                  | [ H : SplitStoreTypings _ ?S,
                      H' : map_util.M.find _ (LinTyp ?S) = _ |- _ ] =>
                    specialize (SplitStoreTypings_inv H' H)
                  end.
                  intros.
                  destructAll.
                  match goal with
                  | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                    inversion H; subst; simpl in *
                  end.
                  ----- match goal with
                        | [ H : SplitStoreTypings _ ?S,
                            H' : get_heaptype _ (LinTyp ?S) = _ |- _ ] =>
                          specialize (SplitStoreTypings_inv H' H)
                        end.
                        intros; destructAll.
                        match goal with
                        | [ H : In _ [_; _] |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        ------ match goal with
                               | [ H : get_heaptype _ (LinTyp ?S) = Some _,
                                   H' : HasTypeValue ?S _ _ _ |- _ ] =>
                                 inversion H'; subst; simpl in *
                               end.
                               match goal with
                               | [ H : eq_map ?LT _,
                                   H' : get_heaptype _ ?LT = _ |- _ ] =>
                                 unfold eq_map in H;
                                 rewrite H in H'
                               end.
                               match goal with
                               | [ H : get_heaptype ?L (map_util.M.add (N.succ_pos ?L1) _ _) = _ |- _ ] =>
                                 assert (Hloc_eq : L = L1 \/ L <> L1); [ apply eq_dec_N | ]
                               end.
                               case Hloc_eq; intros; subst.
                               ------- right.
                                       unfold Ensembles.In.
                                       exists (ArrayType (QualT Unit Unrestricted)).
                                       match goal with
                                       | [ H' : SplitStoreTypings [_; ?S] ?SPP,
                                           H'' : SplitStoreTypings (?SPP :: ?A ++ ?B) ?SP
                                           |-
                                           map_util.M.find (N.succ_pos ?L) (LinTyp ?SP) = _ ] =>
                                         eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=SPP));
                                           [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ] | | exact H'' ]
                                       end.
                                       -------- simpl.
                                                unfold get_heaptype.
                                                rewrite M.gss; auto.
                                       -------- constructor 2.
                                                constructor; auto.
                                       -------- constructor; auto.
                               ------- unfold get_heaptype in *.
                                       match goal with
                                       | [ H : map_util.M.find _ (map_util.M.add _ _ _) = _ |- _ ] =>
                                         rewrite M.gso in H;
                                         try rewrite map_util.M.gempty in H;
                                         inversion H
                                       end.
                                       intro.
                                       match goal with
                                       | [ H : N.succ_pos ?A = N.succ_pos ?B |- _ ] =>
                                         let H' := fresh "H" in
                                         assert (H' : Pos.pred_N (N.succ_pos A) = Pos.pred_N (N.succ_pos B)); [ rewrite H; auto | ]
                                       end.
                                       repeat rewrite N.pos_pred_succ in *.
                                       eauto.
                        ------ match goal with
                               | [ H : _ \/ False |- _ ] =>
                                 inversion H; subst; simpl in *
                               end.
                               unfold get_heaptype in *.
                               match goal with
                               | [ H : map_util.M.is_empty ?M = true,
                                   H' : map_util.M.find ?L ?M = Some _ |- _ ] =>
                                 rewrite (map_find_empty L M H) in H';
                                 inversion H'
                               end.
                               exfalso; auto.
                  ----- right.
                        unfold Ensembles.In.
                        match goal with
                        | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT,
                            H' : In ?S (_ ++ _),
                            H'' : SplitStoreTypings (_ :: _ ++ _) ?SP |-
                            context[?SP] ] =>
                          exists HT;
                          eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ exact H | | exact H'' ]
                        end.
                        right; auto.
         --- unfold Ensembles.Included.
             unfold Ensembles.In.
             intros.
             match goal with
             | [ H : (_ :|: _) _ |- _ ] =>
               inversion H; subst; simpl in *
             end.
             ---- unfold Ensembles.In in *.
                  unfold Dom_ht in *.
                  unfold Ensembles.In in *.
                  unfold Dom_map in *.
                  destructAll.
                  left.
                  unfold Ensembles.In.
                  match goal with
                  | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some ?HT,
                      H' : SplitStoreTypings [_; _] ?SH
                      |- context[?SH] ] =>
                    exists HT;
                    eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ exact H | | exact H' ]
                  end.
                  constructor 2; constructor; auto.
             ---- unfold Ensembles.In in *.
                  unfold Dom_ht in *.
                  unfold Ensembles.In in *.
                  unfold Dom_map in *.
                  destructAll.
                  match goal with
                  | [ H : SplitStoreTypings _ ?S,
                      H' : map_util.M.find _ (LinTyp ?S) = _ |- _ ] =>
                    specialize (SplitStoreTypings_inv H' H)
                  end.
                  intros.
                  destructAll.
                  match goal with
                  | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                    inversion H; subst; simpl in *
                  end.
                  ----- match goal with
                        | [ H : SplitStoreTypings _ ?S,
                            H' : get_heaptype _ (LinTyp ?S) = _ |- _ ] =>
                          specialize (SplitStoreTypings_inv H' H)
                        end.
                        intros; destructAll.
                        match goal with
                        | [ H : In _ [_; _] |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        ------ left.
                               unfold Ensembles.In.
                               match goal with
                               | [ H : get_heaptype _ (LinTyp ?S) = Some ?HT,
                                   H' : SplitStoreTypings [?S; _] ?SP |- _ ] =>
                                 exists HT;
                                 eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ exact H | | exact H' ]
                               end.
                               constructor; auto.
                        ------ match goal with
                               | [ H : _ \/ False |- _ ] =>
                                 inversion H; subst; simpl in *;
                                 [ | exfalso; auto ]
                               end.
                               unfold get_heaptype in *.
                               match goal with
                               | [ H : map_util.M.find (N.succ_pos ?L) (map_util.M.add (N.succ_pos ?L1) _ _) = _ |- _ ] =>
                                 assert (Hloc_eq : L = L1 \/ L <> L1); [ apply eq_dec_N | ]
                               end.
                               case Hloc_eq; intros; subst.
                               ------- right.
                                       unfold Ensembles.In.
                                       match goal with
                                       | [ H : HasTypeValue _ _ (Ref (LocP _ Linear)) _ |- _ ] =>
                                         inversion H; subst; simpl in *
                                       end.
                                       match goal with
                                       | [ H : eq_map (LinTyp ?S) (map_util.M.add _ ?HT _),
                                           H' : SplitStoreTypings [?S; _] ?S2,
                                           H'' : SplitStoreTypings (?S2 :: _ ++ _) ?SP |- _ ] =>
                                         exists HT;
                                         eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S2));
                                         [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ] | | exact H'' ]
                                       end.
                                       -------- match goal with
                                                | [ H : eq_map _ _ |- _ ] =>
                                                  rewrite H
                                                end.
                                                unfold get_heaptype.
                                                rewrite M.gss; auto.
                                       -------- constructor; auto.
                                       -------- constructor; auto.
                               ------- unfold get_heaptype in *.
                                       match goal with
                                       | [ H : map_util.M.find _ (map_util.M.add _ _ _) = _ |- _ ] =>
                                         rewrite M.gso in H;
                                         try rewrite map_util.M.gempty in H;
                                         inversion H
                                       end.
                                       intro.
                                       match goal with
                                       | [ H : N.succ_pos ?A = N.succ_pos ?B |- _ ] =>
                                         let H' := fresh "H" in
                                         assert (H' : Pos.pred_N (N.succ_pos A) = Pos.pred_N (N.succ_pos B)); [ rewrite H; auto | ]
                                       end.
                                       repeat rewrite N.pos_pred_succ in *.
                                       eauto.
                  ----- right.
                        unfold Ensembles.In.
                        match goal with
                        | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT,
                            H' : In ?S (_ ++ _) |- _ ] =>
                          exists HT;
                          eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ auto | | eauto ]
                        end.
                        constructor 2; auto.
      -- eapply Same_set_trans; [ eapply Same_set_sym; eauto | ].
         match goal with
         | [ H : ?A <--> Dom_ht _ :|: Dom_ht _
             |- ?A <--> _ ] =>
           eapply Same_set_trans; [ exact H | ]
         end.
         assert (Hinst1 : UnrTyp Sp = UnrTyp Sh) by solve_inst_or_unr_typ_eq.
         assert (Hinst2 : UnrTyp Sh' = UnrTyp Sh) by solve_inst_or_unr_typ_eq.
         assert (Hinst3 : UnrTyp Sp' = UnrTyp Sh) by solve_inst_or_unr_typ_eq.
         rewrite Hinst1.
         rewrite Hinst2.
         rewrite Hinst3.
         apply Same_set_refl.
      -- constructor; simpl; eauto.
      -- eauto.
      -- eauto.
  Qed.

  Ltac use_forall2_nth_error :=
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.

  Lemma LCEffEqual_HasTypeLocals : forall {C F Ss vs L L'},
      LCEffEqual C L L' ->
      HasTypeLocals F Ss vs L ->
      HasTypeLocals F Ss vs L'.
  Proof.
    constructor.
    rewrite Forall3_forall.
    match goal with
    | [ H : HasTypeLocals _ _ _ _ |- _ ] =>
      inversion H; subst
    end.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] =>
      rewrite Forall3_forall in H; destructAll
    end.
    split; [ | split; eauto ].
    2:{
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
    simpl in *; auto.
  Qed.

  Lemma Preservation_reduce_full Sh Sp Sstack S_ignore Ss M F L L' arrt addr s vs szs es s' vs' es' :
    Function_Ctx_empty F ->
    HasTypeStore s Sh Sp ->
    nth_error (InstTyp Sp) addr = Some M ->
    SplitStoreTypings (Sstack :: S_ignore ++ Ss) Sp ->
    HasTypeInstruction Sstack M F L es arrt L' ->
    HasTypeLocals F Ss vs L ->
    Reduce_full addr s vs szs es s' vs' es' ->
    exists Sp' Sh' Sstack' Ss' L'',
      HasTypeStore s' Sh' Sp' /\
      SplitStoreTypings (Sstack' :: (map (update_unr (UnrTyp Sp')) S_ignore) ++ Ss') Sp' /\
      HasTypeInstruction Sstack' M F L'' es' arrt L' /\
      HasTypeLocals F Ss' vs' L'' /\
      nth_error (InstTyp Sp') addr = Some M /\
      ((map_util.sub_map (UnrTyp Sp) (UnrTyp Sp')) /\ InstTyp Sp = InstTyp Sp') /\
      LCSizeEqual [] L L''.
  Proof.
    intros Hempty Hst Hmod Hsplit Hi Hl Hred. destruct arrt. inv Hred.
    
    - (* Get_local Unr *)
      show_tlvs Hi.
      apply Get_local_unr_HasTypeInstruction in Hi.
      destructAll.
      match goal with
      | [ H : nth_error ?L ?IDX = Some (?T, ?SZ) |- _ ] =>
        eexists Sp, Sh, Sstack, Ss, (set_localtype IDX T SZ L)
      end.
      split; eauto.

      split; [ | split; [ | split; [ | split; [ | split ] ] ] ]; eauto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow ?L _] ] =>
           replace L with (L ++ []) at 1 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intro qt.
             destruct qt.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- eapply ChangeEndLocalTyp.
             { destruct F; subst; simpl in *; eauto. }
             apply ValTyp.
             2:{
               eapply LocalCtxValid_LCEffEqual.
               2:{ apply LCEffEqual_sym; eauto. }
               destruct F; subst; simpl in *.
               eapply LocalCtxValid_Function_Ctx; eauto.
             }
             match goal with
             | [ H : HasTypeLocals _ _ _ _ |- _ ] =>
               destruct H
             end.

             match goal with
             | [ H : Forall3 _ _ ?L2 ?L3,
                 H' : nth_error ?L2 _ = Some _,
                 H'' : nth_error ?L3 _ = Some _ |- _ ] =>
               specialize (forall3_nth_error_args23 H H' H'')
             end.
             intro Hhtv.
             destruct Hhtv as [Ssj Hhtv].
             destructAll.

             assert (Hssj_unr : M.is_empty (LinTyp Ssj) = true).
             { match goal with
               | [ H : HasTypeValue _ _ _ (QualT _ (QualConst Unrestricted)) |- _ ] =>
                 apply (HasTypeValue_Unrestricted_LinEmpty _ _ _ _ _ H)
               end.
               apply QualLeq_Refl.
               unfold Function_Ctx_empty in *.
               destructAll; auto. }

             assert (Hsstack_in : In Sstack (Sstack :: S_ignore ++ Ss)).
             { simpl.
               constructor 1.
               apply eq_refl. }
             assert (Hssj_in : In Ssj (Sstack :: S_ignore ++ Ss)).
             { simpl.
               constructor 2.
               eapply in_or_app.
               constructor 2.
               eapply nth_error_In; eauto. }

             assert (Heq_inst_unr : InstTyp Sstack = InstTyp Ssj /\ UnrTyp Sstack = UnrTyp Ssj).
             { apply (SplitStoreTypings_eq_typs _ _ _ _ Hsplit Hsstack_in Hssj_in). }
             
             apply HasTypeValue_update_linear_ctx.
             apply (HasTypeValue_same_envs Ssj); [ auto | | | ].
             ---- destructAll; auto.
             ---- destructAll; auto.
             ---- apply eq_map_empty.
                  all: auto.
         --- solve_tvs.
      -- match goal with
         | [ |- context[set_localtype ?IDX ?T ?SZ ?L] ] =>
           let H' := fresh "H" in
           assert (H' : set_localtype IDX T SZ L = L);
           [ | rewrite H'; auto ]
         end.
         apply set_localtype_nth_error.
         auto.
      -- split; eauto.
         eapply sub_map_refl.
      -- eapply set_localtype_LCSizeEqual; eauto.
         all: apply SizeLeq_Refl.
      -- unfold Function_Ctx_empty in *; destructAll; auto.

    - (* Get_local Lin *)
      show_tlvs Hi.
      apply Get_local_lin_HasTypeInstruction in Hi.
      destructAll.

      match goal with
      | [ H : HasTypeLocals _ _ ?VS ?L,
          H' : nth_error ?L _ = Some _,
          H'' : nth_error ?VS _ = Some _ |- _ ] =>
        specialize (HasTypeLocals_nth_error H H' H'')
      end.
      intros Hsst.
      destruct Hsst as [Ss1 Hsst].
      destructAll.

      match goal with
      | [ H : nth_error _ ?IDX = Some ?S,
          H' : HasTypeValue ?S _ _ _,
          H'' : context[set_localtype ?IDX ?T ?SZ ?L] |- _ ] =>
        exists Sp, Sh, Ss1, (set_nth Ss IDX Sstack), (set_localtype IDX T SZ L)
      end.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         match goal with
         | [ H : nth_error _ ?IDX = Some _ |- _ ] =>
           assert (Hpermut :
                     Permutation.Permutation
                       (Sstack :: S_ignore ++ Ss)
                       (Ss1 :: S_ignore ++ set_nth Ss IDX Sstack))
         end.
         { repeat match goal with
                  | [ |- context[?A :: ?B ++ ?C] ] =>
                    replace (A :: B ++ C) with ([A] ++ B ++ C) by
                        ltac:(simpl; congruence)
                  end.

           rewrite Permutation.Permutation_app_comm.
           rewrite<- app_assoc.
           rewrite (Permutation.Permutation_app_comm [Ss1]).
           rewrite<- app_assoc.
           eapply Permutation.Permutation_app_head.
           eapply Permutation.Permutation_trans.
           1:{
             eapply Permutation.Permutation_app_tail.
             eapply Permutation_remove_nth; eauto.
           }
           eapply Permutation.Permutation_trans.
           2:{
             eapply Permutation.Permutation_app_tail.
             eapply Permutation.Permutation_sym.
             eapply Permutation_remove_nth; eauto.
             eapply nth_error_set_nth.
             eapply nth_error_Some_length; eauto.
           }
           rewrite remove_nth_set_nth.
           repeat match goal with
                  | [ |- context[(?A :: ?B) ++ [?C]] ] =>
                    replace (A :: B)
                      with ([A] ++ B) by ltac:(simpl; congruence)
                  end.
           repeat rewrite <-app_assoc.
           rewrite Permutation.Permutation_app_comm.
           eapply Permutation.Permutation_trans;
             [ | eapply Permutation.Permutation_app_comm ].
           repeat rewrite <-app_assoc.
           apply Permutation.Permutation_app_head.
           constructor. }
         apply (SplitStoreTypings_permut _ _ _ Hpermut Hsplit).
      -- match goal with
         | [ |- context[Arrow ?L _] ] =>
           replace L with (L ++ []) at 1 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intros Q.
             destruct Q.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- eapply ChangeBegLocalTyp.
             { apply LCEffEqual_sym.
               destruct F; subst; simpl in *; eauto. }
             apply ValTyp.
             2:{
               destruct F; subst; simpl in *.
               eapply LocalCtxValid_Function_Ctx; eauto.
             }
             apply HasTypeValue_update_linear_ctx.
             auto.
         --- solve_tvs.
      -- match goal with
         | [ H : HasTypeValue _ _ ?V ?T |- _ ] =>
           apply (HasTypeLocals_replacement
                    (t:=T) (v:=V) (tnewsz:=SizeConst 0));
           try eassumption
         end.
         --- apply UnitTyp.
             simpl.
             eauto. econstructor. eapply QualConstValid. eauto.
         --- simpl.
             eauto.
         --- eapply SizeLeq_Bottom.
      -- split; eauto.
         eapply sub_map_refl.
      -- eapply set_localtype_LCSizeEqual; eauto.
         all: apply SizeLeq_Refl.
      -- unfold Function_Ctx_empty in *; destructAll; auto.

    - (* Set_local *)
      match goal with
      | [ H : context[[Val ?V; Set_local ?IDX]] |- _ ] =>
        replace [Val V; Set_local IDX] with
            ([Val V] ++ [Set_local IDX]) in H
          by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Set_local _] _ _ |- _ ] =>
        show_tlvs H; apply Set_local_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.
      match goal with
      | [ H : M.is_empty (LinTyp ?SSTACK) = true,
          H' : SplitStoreTypings [?S1; ?S2] Sstack,
          H'' : context[set_localtype ?IDX ?A ?B ?C] |- _ ] =>
        exists Sp, Sh, SSTACK, (set_nth Ss IDX S1), (set_localtype IDX A B C)
      end.
      split; [ eassumption | ].
      split; [ | split; [ | split; [ | split; [ | split ] ] ] ]; auto.
      -- match goal with
         | [ H : nth_error _ ?IDX = Some (?T, _) |- _ ] =>
           assert (Hlocal :
                     exists Ssj, nth_error Ss IDX = Some Ssj /\
                                 HasTypeValue Ssj F v T)
         end.
         { inversion Hl; subst.
           use_LCEffEqual_nth_error_right.
           match goal with
           | [ H : Forall3 _ _ ?L2 ?L3,
               H' : nth_error ?L2 _ = Some _,
               H'' : nth_error ?L3 _ = Some _ |- _ ] =>
             specialize (forall3_nth_error_args23 H H' H'')
           end.
           eauto. }
         destruct Hlocal as [Ssj [Hlocal1 Hlocal2]].
         match goal with
         | [ H : QualLeq ?Q _ _ = Some true |- _ ] =>
           let H' := fresh "H" in
           assert (H' : Q = []);
           [ | specialize (HasTypeValue_Unrestricted_LinEmpty _ _ _ _ _ Hlocal2 H H') ]
         end.
         { unfold Function_Ctx_empty in *; destructAll; auto. }
         intro Hunr.

         specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.

         apply (SplitStoreTypings_split_and_replace_empty (Shead:=Sstack) (Stailj:=Ssj)); eassumption.
      -- match goal with
         | [ |- context[Arrow ?A ?A] ] =>
           replace A with (A ++ []) by apply app_nil_r
         end.
         apply (FrameTyp _ _ _ _ _ Linear _ _ _ _ (get_hd (linear F))).
         --- reflexivity.
         --- apply Forall_trivial.
             intro typ; destruct typ.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- eapply ChangeEndLocalTyp.
             { destruct F; subst; simpl in *; eauto. }
             apply EmptyTyp; [ eauto | ].
             eapply LocalCtxValid_LCEffEqual; [ | apply LCEffEqual_sym; eauto ].
             destruct F; subst; simpl in *.
             eapply LocalCtxValid_Function_Ctx; eauto.
         --- solve_tvs.
      -- eapply HasTypeLocals_replacement; eauto.
         eapply LCEffEqual_HasTypeLocals; eauto.
      -- split; eauto.
         eapply sub_map_refl.
      -- eapply LCSizeEqual_trans.
         --- eapply LCEffEqual_LCSizeEqual.
             destruct F; subst; simpl in *.
             unfold Function_Ctx_empty in *.
             simpl in *; destructAll; eauto.
         --- eapply set_localtype_LCSizeEqual; eauto.
             all: apply SizeLeq_Refl.

    - (* Get_global *)
      show_tlvs Hi.
      apply Get_global_HasTypeInstruction in Hi.
      destructAll.
      
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ eassumption | split; [| split; [| split; [| split; [| split ]]]]].
      + erewrite SplitStoreTypings_unr_same; eauto.
      + match goal with
        | [ |- context[Arrow ?L _] ] =>
          replace L with (L ++ []) at 1 by apply app_nil_r
        end.
        eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
        * reflexivity.
        * apply Forall_trivial.
          intro A; destruct A.
          apply QualLeq_Top.
        * apply QualLeq_Top.
        * apply ValTyp.
          2:{ destruct F; subst; simpl in *; solve_lcvs. }
          apply HasTypeValue_Function_Ctx with (F := F); try (destruct F; reflexivity).
          
          inv Hst.
          use_forall2_nth_error.
          intro Hhti.
          simpl in *.
          inv Hhti. simpl in *.

          match goal with
          | [ H : Forall2 _ ?L1 _,
              H' : nth_error ?L1 _ = Some (_, _) |- _ ] =>
            assert (Hhtv := forall2_args_1 _ _ _ _ _ H H')
          end.
          destructAll.
          eapply HasTypeValue_empty_function_ctx; [| assumption ].
          
          eapply HasTypeValue_empty_store_typing with
              (S1 := {| InstTyp := InstTyp S;
                        LinTyp := LinTyp Sstack;
                        UnrTyp := M.empty _ |}); simpl; eauto.
          2:{ solve_inst_or_unr_typ_eq. }

          match goal with
          | [ H : ?A = ?B, H' : ?A = ?C |- _ ] =>
           rewrite H in H'; inversion H'; subst
          end.

          eapply HasTypeValue_same_envs. eassumption.
          reflexivity. reflexivity.
          simpl.
          eapply eq_map_empty.
          eapply M.is_empty_1. eapply map_util.M.empty_1. eassumption.
        * solve_tvs.
      + eapply LCEffEqual_HasTypeLocals; eauto.
      + assumption.
      + split; eauto. eapply sub_map_refl.
      + apply LCEffEqual_LCSizeEqual.
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
         
    - (* Set_global *)
      match goal with
      | [ H : context[[Val ?V; Set_global ?IDX]] |- _ ] =>
        replace [Val V; Set_global IDX] with
            ([Val V] ++ [Set_global IDX]) in H
            by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Set_global _] _ _ |- _ ] =>
        show_tlvs H; apply Set_global_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.
      match goal with
      | [ H : SplitStoreTypings [?S1; _] _ |- _ ] =>
        assert (Hempty1 : M.is_empty (LinTyp S1) = true)
      end.
      { eapply HasTypeValue_Unrestricted_LinEmpty; try eassumption.
        unfold Function_Ctx_empty in *; destructAll; auto. }

      assert (Hempty2 : M.is_empty (LinTyp Sstack) = true).
      { eapply SplitStoreTypings_Empty'; [ eassumption | ].
        apply Forall_cons; [ eassumption | ].
        apply Forall_cons; [ eassumption | ].
        apply Forall_nil. }
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- inversion Hst; subst.
         econstructor.
         --- eassumption.
         --- match goal with
             | [ H : HasTypeStore ?S _ _ |- _ ] => destruct S
             end.
             simpl in *.

             eapply forall2_set_nth; try eassumption.

             match goal with
             | [ X : MInst |- _ ] => destruct X
             end.
             simpl in *.

             use_forall2_nth_error.
             intro Horighti.
             inversion Horighti; subst.
             econstructor; try eassumption.

             eapply forall2_set_nth; try eassumption.
             eexists; split.
             ---- match goal with
                  | [ H : QualLeq _ ?Q (QualConst Unrestricted) = Some _ |- _ ] =>
                    assert (Hunr : Q = Unrestricted)
                  end.
                  { eapply leq_unrestricted_imp_eq_unrestricted.
                    destruct F; subst; simpl in *.
                    unfold Function_Ctx_empty in *.
                    destructAll; simpl in *; subst.
                    eassumption. }
                  subst.

                  eapply empty_for_one_empty_for_all; [ | eassumption | eassumption | ].
                  ----- inversion Horighti.
                        subst.
                        simpl in *.

                        use_forall2_nth_error.
                        intro Hhtv.
                        simpl in *.
                        destructAll.
                        match goal with
                        | [ H : GT _ _ = GT _ _ |- _ ] =>
                          inversion H; subst
                        end.
                        eassumption.

                  ----- match goal with
                        | [ H : SplitStoreTypings _ Sstack |- _ ] =>
                          inversion H
                        end.
                        match goal with
                        | [ H : Forall _ [_; _] |- _ ] =>
                          inversion H
                        end.
                        subst.
                        destructAll.
                        match goal with
                        | [ H : ?A = ?B |- ?C = ?B ] =>
                          rewrite (eq_sym H)
                        end.
                        inversion Hsplit.
                        match goal with
                        | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                          inversion H
                        end.
                        subst.
                        destructAll.
                        match goal with
                        | [ H : ?A = ?B |- ?C = ?B ] =>
                          rewrite (eq_sym H)
                        end.
                        match goal with
                        | [ H : SplitStoreTypings [?SP; ?SH] _,
                            H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                          inversion H
                        end.
                        match goal with
                        | [ H : Forall _ [?SP; ?SH],
                            H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                          inversion H
                        end.
                        subst.
                        destructAll.
                        assumption.
             ---- simpl in *.
                  inversion Horighti; subst.

                  use_forall2_nth_error.
                  intro Ht; simpl in *; destructAll.
                  match goal with
                  | [ H : GT _ _ = GT _ _ |- _ ] =>
                    inversion H; eauto
                  end.

         --- destruct s.
             simpl in *.
             eassumption.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow ?A ?A] ] =>
           replace A with (A ++ []) by apply app_nil_r
         end.
         apply (FrameTyp _ _ _ _ _ Linear _ _ _ _ (get_hd (linear F))).
         --- reflexivity.
         --- apply Forall_trivial.
             intro typ; destruct typ.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- apply EmptyTyp; [ eauto | ].
             destruct F; subst; simpl in *; solve_lcvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans.
         all: eapply LCEffEqual_LCSizeEqual; eauto.

    - (* Call_indirect *)
      match goal with
      | [ H : context[[Val ?V; ?C]] |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H
          by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Call_indirect] _ _ |- _ ] =>
        show_tlvs H; apply Call_indirect_HasTypeInstruction in H
      end.
      destructAll.
      rewrite app_assoc in *.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.

      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- repeat rewrite app_assoc.
         eapply (FrameTyp _ _ _ _ _ Linear).
         --- reflexivity.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- match goal with
             | [ H : HasTypeValue _ _ _ _ |- _ ] =>
               inversion H
             end.
             subst.
             eapply CallAdmTyp; [ | eassumption | | | | ].
             ---- match goal with
                  | [ H : SplitStoreTypings _ Sstack |- _ ] =>
                    inversion H
                  end.
                  simpl in *.
                  match goal with
                  | [ H : Forall _ [_; _] |- _ ] =>
                    inversion H
                  end.
                  subst.
                  destructAll.
                  inversion Hsplit.
                  simpl in *.
                  match goal with
                  | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                    inversion H
                  end.
                  subst.
                  destructAll.
                  match goal with
                  | [ H : ?A = ?B, H' : ?C = ?A, H'' : context[nth_error ?B _] |- _ ] =>
                    rewrite (eq_sym H') in H; rewrite (eq_sym H) in H''
                  end.

                  inversion Hst.
                  subst.
                  use_forall2_nth_error.
                  intro Hhti.
                  simpl in *.
                  inversion Hhti.
                  subst.
                  simpl in *.
                  match goal with
                  | [ H : Forall2 _ ?L1 ?L2,
                      H' : nth_error ?L1 _ = Some _,
                      H'' : nth_error ?L2 _ = Some _,
                      H''' : HasTypeInstance _ {| term.func := _; glob := _; tab := ?L1 |} _ |- _ ] =>
                    specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
                  end.
                  intro Htc.
                  simpl in *.

                  match goal with
                  | [ H : SplitStoreTypings [?SP; ?SH] _,
                      H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                    inversion H
                  end.
                  simpl in *.
                  match goal with
                  | [ H : Forall _ [?SP; ?SH],
                      H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                    inversion H
                  end.
                  subst.
                  destructAll.
                  match goal with
                  | [ H : ?A = ?B, H'' : ?B = ?C, H' : context[EmptyStoreTyping ?A] |- _ ] =>
                    rewrite H in H'; rewrite H'' in H'
                  end.
                  apply HasTypeClosure_EmptyStoreTyping;
                    [ assumption | ].
                  eapply SplitStoreTypings_Empty'; eauto.
             ---- apply InstIndsValid_empty_Ctx_imp_any_ctx.
                  assumption.
             ---- destruct F; subst; simpl in *; solve_lcvs.
             ---- destruct F; subst; simpl in *; solve_tvs.
             ---- destruct F; subst; simpl in *; solve_tvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans.
         all: eapply LCEffEqual_LCSizeEqual; eauto.

    - (* Call *)
      show_tlvs Hi.
      apply Call_HasTypeInstruction in Hi.
      destructAll.
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- eapply CallAdmTyp; [ | eassumption | | | | ].
             ---- inversion Hst.
                  subst.

                  use_forall2_nth_error.
                  intro Hhti.
                  simpl in *.
                  inversion Hhti.
                  subst.
                  simpl in *.
                  match goal with
                  | [ H : Forall2 _ ?L1 ?L2,
                      H' : nth_error ?L1 _ = Some _,
                      H'' : nth_error ?L2 _ = Some _,
                      H''' : HasTypeInstance _ {| term.func := ?L1; glob := _; tab := _ |} _ |- _ ] =>
                    specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
                  end.
                  intro Hhtc.
                  simpl in *.
                  apply HasTypeClosure_EmptyStoreTyping; auto.

                  inversion Hsplit.
                  simpl in *.
                  match goal with
                  | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                    inversion H
                  end.
                  subst.
                  destructAll.
                  match goal with
                  | [ H : ?A = ?B |- context[EmptyStoreTyping ?B] ] =>
                    rewrite <-H
                  end.
                  match goal with
                  | [ H : SplitStoreTypings [?SP; ?SH] _,
                      H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                    inversion H
                  end.
                  simpl in *.
                  match goal with
                  | [ H : Forall _ [?SP; ?SH],
                      H' : HasTypeStore _ ?SH ?SP |- _ ] =>
                    inversion H
                  end.
                  subst.
                  destructAll.
                  match goal with
                  | [ H : ?A = ?B |- context[EmptyStoreTyping ?B] ] =>
                    rewrite <-H
                  end.
                  assumption.
            ---- apply InstIndsValid_update_linear_ctx.
                 assumption.
            ---- destruct F; subst; simpl in *; solve_lcvs.
            ---- destruct F; subst; simpl in *; solve_tvs.
            ---- destruct F; subst; simpl in *; solve_tvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         apply LCEffEqual_LCSizeEqual; auto.

    - (* StructFree *)
      show_tlvs Hi.
      apply StructFree_HasTypeInstruction in Hi.
      destructAll.
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow _ ?A] ] =>
           replace A with (A ++ []) at 2 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ Linear).
         --- reflexivity.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- apply FreeTyp.
             ---- eassumption.
             ---- destruct F.
                  simpl in *.
                  eassumption.
             ---- destruct F.
                  simpl in *.
                  assumption.
             ---- eapply StructUnrestricted.
                  destruct F; simpl in *.
                  auto.
             ---- destruct F; subst; simpl in *; solve_lcvs.
             ---- destruct F; subst; simpl in *; solve_tvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         apply LCEffEqual_LCSizeEqual; auto.

    - (* StructGet *)
      match goal with
      | [ H : context[[Val ?V; ?C]] |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H
          by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [StructGet _] _ _ |- _ ] =>
        show_tlvs H; apply StructGet_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.

      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- rewrite app_assoc.
         match goal with
         | [ |- context[Arrow ?A _] ] =>
           replace A with (A ++ []) at 1 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- match goal with
             | [ |- context[[Val ?V1; Val ?V2]] ] =>
               replace [Val V1; Val V2] with ([Val V1] ++ [Val V2]) by ltac:(simpl; congruence)
             end.
             eapply ConsTyp; [ eassumption | | ].
             ---- apply ValTyp.
                  ----- apply HasTypeValue_update_linear_ctx.
                        eassumption.
                  ----- destruct F; subst; simpl in *; solve_lcvs.
             ---- match goal with
                  | [ |- context[Arrow (?A :: ?B) (?A :: ?C)] ] =>
                    replace (A :: B) with ([A] ++ B) by ltac:(simpl; congruence);
                    replace (A :: C) with ([A] ++ C) by ltac:(simpl; congruence)
                  end.
                  eapply FrameTyp; [ reflexivity | | | | ].
                  ----- apply Forall_trivial.
                        intro t.
                        destruct t.
                        apply QualLeq_Top.
                  ----- apply QualLeq_Top.
                  ----- apply ValTyp.
                        apply HasTypeValue_update_linear_ctx.
                        apply HasTypeValue_update_linear_ctx.
                        unfold get_mem in H.
                        match goal with
                        | [ H : HasTypeValue _ _ _ _ |- _ ] =>
                          inversion H; subst
                        end.
                        ------ inversion Hst.
                               subst.
                               match goal with
                               | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : get _ _ _ = Some _ |- _ ] =>
                                 specialize (get_implies_in_to_list _ _ _ _ _ H)
                               end.
                               intro Hne.
                               destructAll.

                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hne2.
                               destructAll.

                               match goal with
                               | [ H : HasHeapType ?S _ (Struct _) _,
                                   H' : HasTypeValue ?S2 _ (Ref (LocP _ _)) _ |- _ ] =>
                                 assert (Hunr_eq : UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
                                   inversion H; subst
                                 end.
                                 match goal with
                                 | [ H : nth_error _ _ = Some ?S
                                     |- UnrTyp ?S = _ ] =>
                                   specialize (@nth_error_In _ _ _ _ H)
                                 end.
                                 intro Hin.
                                 match type of Hin with
                                 | In ?S _ =>
                                   assert (Hin2 : In S (S_lin ++ S_unr))
                                 end.
                                 { apply in_or_app.
                                   constructor 2.
                                   assumption. }
                                 match goal with
                                 | [ H : Forall _ (_ ++ _) |- _ ] =>
                                   rewrite Forall_forall in H;
                                   specialize (H _ Hin2)
                                 end.
                                 destructAll.
                                 assert (Hunr_eq : UnrTyp Sh = UnrTyp Sp) by solve_inst_or_unr_typ_eq.
                                 simpl in *.
                                 match goal with
                                 | [ H : UnrTyp Sh = _,
                                     H' : UnrTyp Sh = UnrTyp Sp |- _ ] =>
                                   rewrite H' in H
                                 end.

                                 match goal with
                                 | [ H : SplitStoreTypings _ Sstack |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : Forall _ [_; _] |- _ ] =>
                                   inversion H
                                 end.
                                 subst.
                                 destructAll.
                                 inversion Hsplit.
                                 match goal with
                                 | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                                   inversion H
                                 end.
                                 subst.
                                 destructAll.
                                 congruence. }

                               match goal with
                               | [ H : ?UT = _,
                                   H' : get_heaptype _ ?UT = Some _ |- _ ] =>
                                 rewrite H in H'
                               end.
                               match goal with
                               | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                                 rewrite H in H'; inversion H'; subst
                               end.
                               match goal with
                               | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                 inversion H; subst; destructAll
                               end.
                               match goal with
                               | [ H : (_, _) = split (combine _ _) |- _ ] =>
                                 rewrite combine_split in H by assumption;
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : Forall3 _ _ ?L2 ?L3,
                                   H' : nth_error ?L2 _ = Some _,
                                   H'' : nth_error ?L3 _ = Some _ |- _ ] =>
                                 specialize (forall3_nth_error_args23 H H' H'')
                               end.
                               intro Hhtv.
                               destructAll.

                               match goal with
                               | [ H : HasTypeValue ?S _ ?V _
                                   |- HasTypeValue ?S2 _ ?V _ ] =>
                                 assert (Htyps_eq : InstTyp S = InstTyp S2 /\ UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ H : nth_error ?SS _ = Some ?S,
                                     H' : SplitStoreTypings ?SS _
                                     |- InstTyp ?S = _ /\ _ ] =>
                                   inversion H'; subst
                                 end.
                                 match goal with
                                 | [ H : nth_error ?SS _ = Some ?S,
                                     H' : Forall _ ?SS
                                     |- InstTyp ?S = _ /\ _ ] =>
                                   rewrite Forall_forall in H';
                                   let H0 := fresh "H" in
                                   assert (H0 : In S SS);
                                   [ eapply nth_error_In;
                                     eassumption | ];
                                   specialize (H' _ H0)
                                 end.

                                 match goal with
                                 | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : SplitStoreTypings (?S1 ++ ?S2) _,
                                     H' : nth_error ?S2 _ = Some ?S,
                                     H'' : Forall _ (?S1 ++ ?S2) |- _ ] =>
                                   specialize (@nth_error_In _ _ _ _ H');
                                   intro Hin;
                                   assert (Hin2 : In S (S1 ++ S2));
                                   [ | rewrite Forall_forall in H'';
                                       specialize (H'' _ Hin2) ]
                                 end.
                                 { apply in_or_app.
                                   constructor 2.
                                   assumption. }

                                 assert (Hunr_eq2 : InstTyp Sh = InstTyp Sp /\ UnrTyp Sh = UnrTyp Sp) by ltac:(split; solve_inst_or_unr_typ_eq).

                                 match goal with
                                 | [ H : SplitStoreTypings _ Sstack |- _ ] =>
                                   inversion H
                                 end.
                                 simpl in *.
                                 match goal with
                                 | [ H : SplitHeapTypings (map _ (_ ++ _)) _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : Forall _ [_; _] |- _ ] =>
                                   inversion H; subst
                                 end.
                                 match goal with
                                 | [ H : Forall _ [_] |- _ ] =>
                                   inversion H; subst
                                 end.
                                 inversion Hsplit; subst.
                                 match goal with
                                 | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                                   inversion H; subst
                                 end.
                                 destructAll.
                                 split; congruence. }
                               destructAll.

                               match goal with
                               | [ |- HasTypeValue _ _ _ (QualT _ ?Q) ] =>
                                 assert (Heq_unr : Q = Unrestricted)
                               end.
                               { eapply leq_unrestricted_imp_eq_unrestricted.
                                 destruct F; subst; simpl in *.
                                 unfold Function_Ctx_empty in *.
                                 destructAll; simpl in *; subst.
                                 eassumption. }
                               subst.

                               eapply HasTypeValue_same_envs.
                               ------- apply HasTypeValue_empty_function_ctx; eassumption.
                               ------- assumption.
                               ------- assumption.
                               ------- apply eq_map_empty; [ | assumption ].
                                       eapply HasTypeValue_Unrestricted_LinEmpty.
                                       -------- eassumption.
                                       -------- apply QualLeq_Refl.
                                       -------- simpl; auto.
                        ------ inversion Hst.
                               subst.
                               match goal with
                               | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : get _ _ _ = Some _ |- _ ] =>
                                 specialize (get_implies_in_to_list _ _ _ _ _ H)
                               end.
                               intro Hne.
                               destructAll.

                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hne2.
                               destructAll.

                               (* Use eq_map to show get_heaptype assertion *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                 assert (Hght : get_heaptype L LT = Some HT)
                               end.
                               { match goal with
                                 | [ H : eq_map _ _ |-
                                     get_heaptype ?L _ = _] =>
                                   rewrite (H L)
                                 end.
                                 unfold get_heaptype.
                                 rewrite typing.M.gss.
                                 eauto. }
                               (* LinTyp x4 is a subset of LinTyp Sstack is a subset of LinTyp Sp *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                 assert (HghtSp : get_heaptype L (LinTyp Sp) = Some HT)
                               end.
                               { match goal with
                                 | [ H : SplitStoreTypings ?SS Sstack |- _ ] =>
                                   specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=Sstack) Hght)
                                 end.
                                 match goal with
                                 | [ |- (?A -> ?B -> _) -> _ ] =>
                                   let H1 := fresh "H" in
                                   let H2 := fresh "H" in
                                   let H3 := fresh "H" in
                                   assert (H1 : A);
                                     [ constructor; eauto
                                     | assert (H2 : B);
                                       [ eauto
                                       | intro H3;
                                         specialize (H3 H1 H2); 
                                         specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=Sstack :: S_ignore ++ Ss) (S2:=Sp) H3) ] ]
                                 end.
                                 match goal with
                                 | [ |- (?A -> ?B -> _) -> _ ] =>
                                   let H1 := fresh "H" in
                                   let H2 := fresh "H" in
                                   let H3 := fresh "H" in
                                   assert (H1 : A);
                                     [ constructor; eauto
                                     | assert (H2 : B);
                                       [ eauto
                                       | intro H3;
                                         specialize (H3 H1 H2) ] ]
                                 end.
                                 eauto. }
                               (* Sp and Sh are disjoint *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                 assert (HnghtSh : forall x, get_heaptype L (LinTyp Sh) = Some x -> False)
                               end.
                               { intros.
                                 match goal with
                                 | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
                                   inversion H
                                 end.
                                 simpl in *.
                                 match goal with
                                 | [ H : SplitHeapTypings [LinTyp Sp; LinTyp Sh] _ |- _ ] =>
                                   inversion H
                                 end.
                                 unfold get_heaptype in *.
                                 match goal with
                                 | [ H : _ <--> _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : _ \subset (Dom_ht (LinTyp S)),
                                     H' : M.find (N.succ_pos ?L) (LinTyp Sh) = _ |- _ ] =>
                                   specialize (H L)
                                 end.
                                 match goal with
                                 | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
                                   let H' := fresh "H" in
                                   assert (H' : A); [ | specialize (H H') ]
                                 end.
                                 { unfold Ensembles.In.
                                   unfold Dom_ht.
                                   simpl.
                                   constructor.
                                   unfold Ensembles.In.
                                   unfold Dom_map.
                                   eexists; eauto. }
                                 unfold Ensembles.In in *.
                                 unfold Dom_ht in *.
                                 unfold Ensembles.In in *.
                                 unfold Dom_map in *.
                                 destructAll.
                                 match goal with
                                 | [ H : forall _ _, M.find (N.succ_pos _) (LinTyp S) = _ -> _,
                                     H' : M.find (N.succ_pos ?L) (LinTyp S) = Some ?T |- _ ] =>
                                   specialize (H L T H'); inversion H; subst; simpl in *
                                 end.
                                 1:
                                   match goal with
                                   | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                                     inversion H; subst; simpl in *
                                   end.
                                 all: unfold get_heaptype in *.
                                 all:
                                   match goal with
                                   | [ H : ?A = Some _, H' : ?A = None |- _ ] => rewrite H in H'; inversion H'
                                   end. }
                               match goal with
                               | [ H : _ \/ _ |- _ ] => case H
                               end.
                               { intro Hbad.
                                 specialize (HnghtSh _ Hbad).
                                 exfalso.
                                 assumption. }
                               intro Hx3.
                               rewrite HghtSp in Hx3.
                               inversion Hx3.
                               subst.

                               match goal with
                               | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : (_, _) = split (combine _ _) |- _ ] =>
                                 rewrite combine_split in H by assumption;
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : Forall3 _ _ ?L2 ?L3,
                                   H' : nth_error ?L2 _ = Some _,
                                   H'' : nth_error ?L3 _ = Some _ |- _ ] =>
                                 specialize (forall3_nth_error_args23 H H' H'')
                               end.
                               intro Hhtv.
                               destructAll.

                               match goal with
                               | [ H : HasTypeValue ?S _ _ _
                                   |- HasTypeValue ?S2 _ _ _ ] =>
                                 assert (Htyps_eq : InstTyp S = InstTyp S2 /\ UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ H : nth_error ?SS _ = Some ?S,
                                     H' : SplitStoreTypings ?SS _
                                     |- InstTyp ?S = _ /\ _ ] =>
                                   inversion H'; subst
                                 end.
                                 match goal with
                                 | [ H : nth_error ?SS _ = Some ?S,
                                     H' : Forall _ ?SS
                                     |- InstTyp ?S = _ /\ _ ] =>
                                   rewrite Forall_forall in H';
                                   let H0 := fresh "H" in
                                   assert (H0 : In S SS);
                                   [ eapply nth_error_In;
                                     eassumption | ];
                                   specialize (H' _ H0)
                                 end.

                                 match goal with
                                 | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : SplitStoreTypings (?S1 ++ ?S2) _,
                                     H' : nth_error ?S1 _ = Some ?S,
                                     H'' : Forall _ (?S1 ++ ?S2) |- _ ] =>
                                   specialize (@nth_error_In _ _ _ _ H');
                                   intro Hin;
                                   assert (Hin2 : In S (S1 ++ S2));
                                   [ | rewrite Forall_forall in H'';
                                       specialize (H'' _ Hin2) ]
                                 end.
                                 { apply in_or_app.
                                   constructor 1.
                                   assumption. }

                                 assert (Hunr_eq2 : InstTyp Sh = InstTyp Sp /\ UnrTyp Sh = UnrTyp Sp) by ltac:(split; solve_inst_or_unr_typ_eq).

                                 match goal with
                                 | [ H : SplitStoreTypings _ Sstack |- _ ] =>
                                   inversion H
                                 end.
                                 simpl in *.
                                 match goal with
                                 | [ H : SplitHeapTypings (map _ (_ ++ _)) _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : Forall _ [_; _] |- _ ] =>
                                   inversion H; subst
                                 end.
                                 match goal with
                                 | [ H : Forall _ [_] |- _ ] =>
                                   inversion H; subst
                                 end.
                                 inversion Hsplit; subst.
                                 match goal with
                                 | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
                                   inversion H; subst
                                 end.
                                 destructAll.
                                 split; congruence. }
                               destructAll.

                               match goal with
                               | [ |- HasTypeValue _ _ _ (QualT _ ?Q) ] =>
                                 assert (Heq_unr : Q = Unrestricted)
                               end.
                               { eapply leq_unrestricted_imp_eq_unrestricted.
                                 destruct F; subst; simpl in *.
                                 unfold Function_Ctx_empty in *.
                                 destructAll; simpl in *; subst.
                                 eassumption. }
                               subst.

                               eapply HasTypeValue_same_envs.
                               -------- apply HasTypeValue_empty_function_ctx; eassumption.
                               -------- assumption.
                               -------- assumption.
                               -------- apply eq_map_empty; [ | assumption ].
                                        eapply HasTypeValue_Unrestricted_LinEmpty.
                                        --------- eassumption.
                                        --------- apply QualLeq_Refl.
                                        --------- simpl; auto.
                        ------ destruct F; subst; simpl in *; solve_lcvs.
                  ----- destruct F; subst; simpl in *; solve_tvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans.
         all: apply LCEffEqual_LCSizeEqual; eauto.

    - (* StructSet *)
      match goal with
      | [ H : context[[?A; ?B; ?C]] |- _ ] =>
        replace [A; B; C] with ([A] ++ [B; C]) in H
        by ltac:(simpl; congruence)
      end.
      specialize (composition_typing _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *.
      destructAll.
      match goal with
      | [ H : context[[Val ?V; ?B]] |- _ ] =>
        replace [Val V; B] with ([Val V] ++ [B]) in H
        by ltac:(simpl; congruence);
        specialize (composition_typing _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hb.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [StructSet _] _ _ |- _ ] =>
        show_tlvs H; apply StructSet_HasTypeInstruction in H
      end.
      simpl in *.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D; ?E] |- _ ] =>
        assert (Htyps : A = C ++ [D] /\ B = E)
      end.
      { eapply app_inj_tail_iff.
        rewrite <-app_assoc; simpl; auto. }
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ ?D ++ [?E] |- _ ] =>
        assert (Htyps2 : A = C ++ D /\ B = E)
      end.
      { eapply app_inj_tail_iff.
        rewrite <-app_assoc; simpl; auto. }
      destructAll.

      match goal with
      | [ H : ReplaceAtIdx _ ?OLDTS ?NEWT = Some (?NEWTS, _),
          H' : update_mem _ ?L ?M _ = Some _,
          H'' : HasTypeValue ?S _ ?V ?NEWT,
          H''' : context[combine ?OLDTS ?SZS] |- _ ] =>
        assert (Hstack :
                  exists Sstack' Sp' Sh' S',
                    SplitStoreTypings [Sp'; Sh'] S' /\
                    SplitStoreTypings [S; Sh] Sh' /\
                    SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' /\
                    if qualconstr_eq_dec M Linear then
                      Sstack' = {|InstTyp:=InstTyp Sstack; UnrTyp:=UnrTyp Sstack; LinTyp:=(M.add (N.succ_pos L) (StructType (combine NEWTS SZS)) (M.empty HeapType))|}
                    else
                      Sstack' = {|InstTyp:=InstTyp Sstack; UnrTyp:=UnrTyp Sstack; LinTyp:=M.empty HeapType|})
      end.
      { match goal with
        | [ H : SplitStoreTypings [?S1; ?S2] ?S,
            H' : SplitStoreTypings [?S0; ?S] ?SP,
            H'' : SplitStoreTypings (?SP :: ?SS1 ++ ?SS2) ?SPP |- _ ] =>
          assert (Hlemma : SplitStoreTypings (S1 :: ([S0; S2] ++ SS1 ++ SS2)) SPP)
        end.
        { eapply SplitStoreTypings_permut.
          { match goal with
            | [ |- context[?S1 :: ([?S0; ?S2] ++ ?SS1 ++ ?SS2)] ] =>
              let H := fresh "H" in
              assert (H : Permutation.Permutation ([S0; S1; S2] ++ SS1 ++ SS2) (S1 :: ([S0; S2] ++ SS1 ++ SS2))); [ | exact H ]
            end.
            apply Permutation.perm_swap. }
          
          eapply SplitStoreTypings_trans_gen; [ | eauto ].
          match goal with
          | [ |- context[[?A; ?B; ?C]] ] =>
              let H := fresh "H" in
              assert (H : [A; B; C] = [A] ++ [B; C]) by ltac:(simpl; auto);
              rewrite H
          end.
          eapply SplitStoreTypings_permut;
          [ eapply Permutation.Permutation_app_comm | ].
          eapply SplitStoreTypings_trans_gen; [ eauto | ].
          eapply SplitStoreTypings_permut; [ | eauto ].
          constructor. }

        match goal with
        | [ H : HasTypeStore _ _ _ |- _ ] =>
          inversion H; subst
        end.
        
        match goal with
        | [ H : HasTypeStore _ ?SH ?SP,
            H' : SplitStoreTypings [?SP; ?SH] ?S |- _ ] =>
          specialize (SplitStoreTypings_move_one H' Hlemma)
        end.
        intros; destructAll.
        
        match goal with
        | [ H : SplitStoreTypings ([?S1; ?S2] ++ ?SS1 ++ ?SS2) ?S,
            H' : map_util.M.is_empty (LinTyp ?S2) = true |- _ ] =>
          let H0 := fresh "H" in
          assert (H0 : nth_error ([S1; S2] ++ SS1 ++ SS2) 1 = Some S2) by ltac:(simpl; auto);
          specialize (SplitStoreTypings_remove_empty H H0 H')
        end.
        intros; simpl in *.

        match goal with
        | [ |- context[if ?B then _ = ?S1 else _ = ?S2] ] =>
          remember (if B then S1 else S2) as Sstack';
          exists Sstack'
        end.

        match goal with
        | [ H : SplitStoreTypings (?S0 :: ?SS1 ++ ?SS2) ?S,
            H' : HasTypeValue ?S0 _ (Ref (LocP _ _)) _ |- _ ] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          let H3 := fresh "H" in
          assert (H1 : InstTyp S0 = InstTyp Sstack');
          [ | assert (H2 : UnrTyp S0 = UnrTyp Sstack');
              [ | assert (H3 : (Dom_ht (LinTyp S0)) <--> (Dom_ht (LinTyp Sstack')));
                  [ | specialize (SplitStoreTypings_change_vals H H1 H2 H3) ] ] ]
        end.
        1-2: solve_inst_or_unr_typ_eq.
        1-2:
          match goal with
          | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
            destruct M; subst; simpl in *; auto
          end.
        { match goal with
          | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
            destruct M; subst; simpl in *
          end.
          - apply eq_map_Dom_ht.
            apply eq_map_empty; [ | simpl; auto ].
            eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
            -- match goal with
               | [ H : HasTypeValue _ _ _ (QualT _ ?Q)
                   |- context[?Q] ] =>
                 inversion H; subst; simpl in *
               end.
               auto.
            -- destruct F; subst; simpl in *.
               unfold Function_Ctx_empty in *.
               simpl in *; destructAll; auto.
          - match goal with
            | [ H : HasTypeValue ?S _ _ _ |- context[?S] ] =>
              inversion H; subst; simpl in *
            end.
            eapply Same_set_trans; [ apply eq_map_Dom_ht; eauto | ].
            apply Dom_ht_one_loc. }

        let H := fresh "H" in
        intro H; destruct H as [Sp'].
        repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               end.

        match goal with
        | [ H0 : SplitStoreTypings (?S0 :: ?SS1 ++ ?SS2) ?S,
            H1 : HasTypeValue ?S0 _ (Ref (LocP _ _)) _,
            H2 : SplitStoreTypings [?S; ?SP] ?SOLD,
            H3 : InstTyp ?S = InstTyp ?SPP,
            H4 : UnrTyp ?S = UnrTyp ?SPP,
            H5 : Dom_ht (LinTyp ?S) <--> Dom_ht (LinTyp ?SPP) |- _ ] =>
          exists SPP; exists SP;
          specialize (SplitStoreTypings_change_vals H2 H3 H4 H5)
        end.
        intros; destructAll.

        eexists; split; [ eauto | ].
        split; [ auto | ].
        split; [ auto | ].
        match goal with
        | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
          destruct M; subst; simpl in *; auto
        end. }

      destruct Hstack as [Sstack' [Sp' [Sh' [S']]]].
      destructAll.

      assert (Hinst : InstTyp Sp = InstTyp Sp') by solve_inst_or_unr_typ_eq.
        
      assert (Hunr : UnrTyp Sp = UnrTyp Sp') by solve_inst_or_unr_typ_eq.
      
      exists Sp', Sh', Sstack', Ss, L'.
      split.
      { econstructor.
        - eassumption.
        - rewrite (eq_sym Hinst).
          match goal with
          | [ H : update_mem ?S _ _ _ = Some ?ST |- _ ] =>
            assert (Hinst_st' : inst S = inst ST);
            [ destruct S; simpl in *;
              unfold update_mem in H; simpl in H;
              match type of H with
              | context[set ?A ?B ?C ?D] => destruct (set A B C D)
              end;
              inversion H; simpl; auto | ]
          end.
          match goal with
          | [ H : update_mem ?S _ _ _ = Some _,
              H' : if qualconstr_eq_dec ?M _ then ?SP = _ else _ = ?SP |- _ ] =>
            assert (Hinst_s' : inst S = inst SP);
            [ destruct M; simpl in *; subst; auto | ]
          end.
          { match goal with
            | [ |- _ = _ (_ _ _ ?A ?B) ] =>
              unfold update_out_set;
              destruct (L.has_urn_ptr_HeapValue B);
              destruct (L.has_urn_ptr_HeapValue A); simpl; auto
            end. }
          rewrite (eq_sym Hinst_s').
          inversion Hst.
          assert (Hinst2 : InstTyp S = InstTyp S') by solve_inst_or_unr_typ_eq.
          rewrite (eq_sym Hinst2).
          auto.
        - destruct m; subst; simpl in *; subst; simpl in *.
          -- inversion Hst; subst; simpl in *.
             match goal with
             | [ H : HasTypeMeminst _ _ _ |- _ ] =>
               inversion H; subst; simpl in *
             end.
             match goal with
             | [ H' : _ \/ _ |- _ ] => case H'
             end.
             1:{
               intros.
               match goal with
               | [ H : HasTypeValue _ _ (Ref (LocP _ Unrestricted)) _ |- _ ] => inversion H; subst; simpl in *
               end.
               match goal with
               | [ H : QualLeq ?Q1 ?A (QualConst Unrestricted) = Some true,
                   H' : QualLeq ?Q2 (QualConst Linear) ?A = Some true |- _ ] =>
                 let H'' := fresh "H" in
                 assert (H'' : Q1 = Q2);
                 [ match goal with
                   | [ |- context[linear ?T] ] => destruct T
                   end;
                   simpl in *; auto
                 | rewrite H'' in H;
                   specialize (QualLeq_Trans _ _ _ _ H' H) ]
               end.
               intros.
               exfalso; eapply QualLeq_Const_False; eauto.
               destruct F; subst; simpl in *.
               unfold Function_Ctx_empty in *.
               simpl in *; destructAll; auto.
             }
             intros; subst.
             assert (Hlin_eq1 : eq_map (LinTyp Sh) (LinTyp Sh')).
             { match goal with
               | [ H : SplitStoreTypings [?A; Sh] Sh' |- _ ] =>
                 assert (Hempty2 : map_util.M.is_empty (LinTyp x13) = true)
               end.
               { eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                 destruct F; subst; simpl in *.
                 unfold Function_Ctx_empty in *.
                 simpl in *; destructAll; auto. }
               eapply proj1; eapply proj2.
               eapply SplitStoreTypings_Empty_eq; eauto. }
             assert (Hlin_eq2 : eq_map (LinTyp Sp) (LinTyp Sp')).
             { assert (Hstack_empty : map_util.M.is_empty (LinTyp Sstack) = true).
               { eapply SplitStoreTypings_Empty'; [ eauto | ].
                 constructor; [ | constructor; auto ].
                 - match goal with
                   | [ H : HasTypeValue ?S _ _ _ |- context[?S] ] =>
                     inversion H; subst; simpl in *
                   end.
                   eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                   destruct F; subst; simpl in *.
                   unfold Function_Ctx_empty in *.
                   simpl in *; destructAll; auto.
                 - eapply SplitStoreTypings_Empty'; [ eauto | ].
                   constructor; [ | constructor; auto ].
                   eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                   destruct F; subst; simpl in *.
                   unfold Function_Ctx_empty in *.
                   simpl in *; destructAll; auto. }
               
               Ltac apply_SplitHeapTypings_empty_app Sc := 
                 match goal with
                 | [ H : SplitStoreTypings (?S1 :: ?Ss) Sc |- _ ] =>
                   specialize (SplitHeapTypings_empty_app [S1] Ss Sc);
                   match goal with
                   [ |- (?A -> ?B -> _) -> _ ] =>
                     let H' := fresh "H" in
                     let H'' := fresh "H" in
                     let H''' := fresh "H" in
                     assert (H' : A);
                     [ rewrite (eq_sym (cons_append _ _)); eauto |
                       assert (H'' : B);
                       [ constructor; eauto |
                         intro H'''; specialize (H''' H' H'') ] ]
                   end
                 end.
               
               apply_SplitHeapTypings_empty_app Sp.
               apply_SplitHeapTypings_empty_app Sp'.
               
               match goal with
               | [ H : SplitStoreTypings (?A ++ ?B) Sp |- _ ] =>
                 remember (A ++ B) as new_stores;
                 repeat match goal with
                        | [ H : context[new_stores] |- _ ] => revert H
                        end;
                 case new_stores; intros; subst; simpl in *
               end.
               - repeat match goal with
                        | [ H : SplitStoreTypings [] _ |- _ ] =>
                          inversion H; clear H
                        end.
                 simpl in *.
                 repeat match goal with
                        | [ H : SplitHeapTypings [] ?S |- _ ] =>
                          specialize (SplitHeapTypings_nil S H);
                          clear H
                        end.
                 intros; apply eq_map_empty; auto.
               - eapply SplitStoreTypings_eq; eauto. }
             
             assert (Hsubgoal : exists S_lin' S_unr',
                                  Forall2
                                    (fun (S0 : StoreTyping) '(loc, hv, len) =>
                                     exists ht : HeapType,
                                       NoCapsHeapType [] ht = true /\
                                       (get_heaptype loc (LinTyp Sh') = Some ht \/
                                        get_heaptype loc (LinTyp Sp') = Some ht) /\
                                       HasHeapType S0 empty_Function_Ctx hv ht /\
                                       RoomForStrongUpdates len ht /\
                                       HeapTypeValid empty_Function_Ctx ht) S_lin'
                                    (M.to_list Linear (meminst s')) /\
                                  Forall2
                                    (fun (S0 : StoreTyping) '(loc, hv, len) =>
                                     exists ht : HeapType,
                                       NoCapsHeapType [] ht = true /\
                                       get_heaptype loc (UnrTyp S0) = Some ht /\
                                       HasHeapType S0 empty_Function_Ctx hv ht /\
                                       RoomForStrongUpdates len ht /\
                                       HeapTypeValid empty_Function_Ctx ht) S_unr'
                                    (M.to_list Unrestricted (meminst s')) /\
                                  Forall
                                    (fun S' : StoreTyping =>
                                     InstTyp Sh = InstTyp S' /\ UnrTyp Sh = UnrTyp S')
                                    (S_lin' ++ S_unr') /\
                                  SplitHeapTypings (map LinTyp (S_lin' ++ S_unr')) (LinTyp Sh)).
             { unfold update_mem in *.
               match goal with
               | [ H : context[set ?A ?B ?C ?D] |- _ ] =>
                 remember (set A B C D) as o;
                   repeat match goal with
                   | [ H : context[o] |- _ ] => revert H
                   end
               end.
               case o; [ | intros H' H''; inversion H'' ].
               intros t H' H''.
               inversion H''; subst; simpl in *.

               derive_mappings f_lin f_unr.
               
               match goal with
               | [ H : get_mem _ ?L Unrestricted = Some (?HV, ?SZ) |- _ ] =>
                 remember (map f_lin (M.to_list Linear t)) as S_lin';
                   remember (map (fun '(loc, hv, len) => if BinNatDef.N.eqb loc L then f_unr (L, HV, SZ) else f_unr (loc, hv, len)) (M.to_list Unrestricted t)) as S_unr'
               end.
               assert (Hperm : Permutation.Permutation (S_lin ++ S_unr) (S_lin' ++ S_unr')).
               { apply Permutation.Permutation_app.
                 - destructAll.
                   eapply Permutation_StoreTypings; eauto.
                   intros; simpl.
                   match goal with
                   | [ X : _ * _ * _ |- _ ] =>
                     destruct X as [[curL curHV] curSz]
                   end.
                   auto.
                 - destructAll.
                   eapply Permutation_StoreTypings; eauto.
                   intros; simpl.
                   match goal with
                   | [ X : _ * _ * _ |- _ ] =>
                     destruct X as [[curL curHV] curSz]
                   end.
                   rewrite N.eqb_sym.
                   match goal with
                   | [ |- context[(?A =? ?B)%N] ] =>
                     remember ((A =? B)%N) as loceqb;
                     revert Heqloceqb;
                     case loceqb; intros; auto;
                     let H := fresh "H" in
                     assert (H : (A = B))
                   end.
                   { apply Ndec.Neqb_complete; eauto. }
                   subst; auto. }
                   
               exists S_lin', S_unr'; destructAll; subst.
               split; [ | split; [ | split ] ].
               - rewrite forall2_map.
                 intros.
                 match goal with
                 | [ H : Forall2 _ _ (M.to_list Linear (meminst ?S)) |- _ ] =>
                   rewrite forall2_map in H;
                   assert (Hsame : forall x, In x (M.to_list Linear t) -> In x (M.to_list Linear (meminst S)))
                 end.
                 { intros.
                   match goal with
                   | [ H : In ?TPL (M.to_list Linear _) |-
                       In ?TPL _ ] =>
                     destruct TPL as [[curL curHV] curSz];
                     apply In_nth_error in H
                   end.
                   destructAll.
                   match goal with
                   | [ H : nth_error _ _ = Some _ |- _ ] =>
                     apply in_to_list_implies_get in H
                   end.
                   assert (Hneq : Unrestricted <> Linear).
                   { let H := fresh "H" in
                     intro H; inversion H. }
                   match goal with
                   | [ H : Some ?MEM2 = set ?LOC Unrestricted ?MEM1 _,
                       H' : get ?LOC2 _ ?MEM2 = _ |- _ ] =>
                     specialize (get_set_other_mem _ _ _ LOC2 _ _ _ (eq_sym H) Hneq)
                   end.
                   intros.
                   match goal with
                   | [ H : get ?A ?B ?C = Some _,
                       H' : get _ _ _ = get ?A ?B ?C |- _ ] =>
                     rewrite (eq_sym H') in H;
                     apply get_implies_in_to_list in H
                   end.
                   destructAll.
                   match goal with
                   | [ H : nth_error _ _ = _ |- _ ] =>
                     apply nth_error_In in H
                   end.
                   auto. }
                   
                 match goal with
                 | [ H : In _ (M.to_list Linear _) |- _ ] =>
                   specialize (Hsame _ H)
                 end.
                 match goal with
                 | [ H : forall _, In _ (M.to_list Linear (meminst _)) -> _ |- _ ] => specialize (H _ Hsame)
                 end.
                 match goal with
                 | [ X : _ * _ * _ |- _ ] =>
                   destruct X as [[curL curHV] curSz]
                 end.
                 destructAll.
                 eexists; split; [ eauto | split; [ | eauto ] ].
                 match goal with
                 | [ H : get_heaptype _ _ = _ \/ get_heaptype _ _ = _ |- _ ] =>
                   case H; intros
                 end.
                 -- left.
                    match goal with
                    | [ H : eq_map _ ?LT |- get_heaptype ?LOC ?LT = _ ] =>
                      unfold eq_map in H;
                      specialize (H LOC);
                      rewrite (eq_sym H); auto
                    end.
                 -- right.
                    match goal with
                    | [ H : eq_map _ ?LT |- get_heaptype ?LOC ?LT = _ ] =>
                      unfold eq_map in H;
                      specialize (H LOC);
                      rewrite (eq_sym H); auto
                    end.
               - rewrite forall2_map.
                 intros.
                 subst.
                 match goal with
                 | [ H : Forall2 _ _ (M.to_list Unrestricted (meminst _)) |- _ ] => rewrite forall2_map in H
                 end.
                 match goal with
                 | [ H : In ?X (M.to_list Unrestricted _) |- _ ] =>
                   destruct X; simpl in *
                 end.
                 match goal with
                 | [ H : In (?P, _) (M.to_list Unrestricted _) |- _ ] =>
                   destruct P; simpl in *
                 end.
                 match goal with
                 | [ |- context[(?A =? ?B)%N] ] =>
                   remember (A =? B)%N as n_eq_l1
                 end.
                 revert Heqn_eq_l1.
                 case n_eq_l1.
                 -- intros; simpl.
                    specialize (Neqb_ok _ _ (eq_sym Heqn_eq_l1)).
                    intros; subst.
                    match goal with
                    | [ H : HasTypeValue _ _ (Ref _)
                                         (QualT (RefT _ _ ?T) _)
                        |- _ ] =>
                      exists T
                    end.
               
                    unfold get_mem in *.
                    match goal with
                    | [ H : get ?L Unrestricted ?MEM = Some (?HV, ?SZ) |- _ ] =>
                      assert (Hinmeminst : In (L, HV, SZ) (M.to_list Unrestricted MEM))
                    end.
                    { match goal with
                      | [ H : get _ _ ?MEM = _ |- context[?MEM] ] =>
                        apply get_implies_in_to_list in H
                      end.
                      destructAll.
                      eapply nth_error_In; eauto. }
                    match goal with
                    | [ H : HasTypeValue _ _ (Ref _)
                                         (QualT (RefT _ _ _) _)
                        |- _ ] =>
                      inversion H; subst; simpl in *
                    end.

                    match goal with
                    | [ H : forall _, In _ (M.to_list Unrestricted (meminst _)) -> _ |- _ ] =>
                      specialize (H _ Hinmeminst)
                    end.
                    simpl in *; destructAll; simpl in *.

                    match goal with
                    | [ H : context[UnrTyp (f_unr (?L, ?HV, ?SZ))],
                        H' : SplitStoreTypings (map _ _ ++ map _ _) ?S
                        |- _ ] =>
                      assert (Heq_typs : UnrTyp (f_unr (L, HV, SZ)) = UnrTyp S); [ | rewrite Heq_typs in H ]
                    end.
                    { eapply proj1.
                      eapply SplitStoreTypings_eq_typs2; eauto.
                      apply in_or_app.
                      right.
                      apply in_map; auto. }

                    match goal with
                    | [ H : get_heaptype ?L (UnrTyp ?S1) = _,
                        H' : get_heaptype ?L (UnrTyp ?S2) = _ |- _ ] =>
                      assert (Heq_typs2 : UnrTyp S1 = UnrTyp S2);
                        [ | rewrite Heq_typs2 in H;
                            rewrite H in H';
                            inversion H'; subst; simpl in * ]
                    end.
                    { solve_inst_or_unr_typ_eq. }
                    match goal with
                    | [ H : context[split (combine _ _)] |- _ ] =>
                      rewrite combine_split in H; [ | auto ];
                        rewrite combine_split; [ | auto ];
                        simpl in *
                    end.
                    split; auto.
                    
                    match goal with
                    | [ H : get_heaptype _ ?A = Some ?T |-
                        context[get_heaptype _ ?B = Some ?T] ] =>
                      assert (Heq_typs3 : B = A);
                        [ | rewrite Heq_typs3 ]
                    end.
                    { solve_inst_or_unr_typ_eq. }
                    split; auto.

                    match goal with
                    | [ H : Some ?T = set ?L Unrestricted _ ?HV,
                        H' : In (?L, ?HV2, ?SZ) (M.to_list Unrestricted ?T) |- _ ] =>
                      assert (Heq_hv : HV2 = HV /\ (N.of_nat (term.size HV) <= SZ)%N)
                    end.
                    { match goal with
                      | [ H : Some _ = set _ _ _ _ |- _ ] =>
                        specialize (get_set_same _ _ _ _ _ (eq_sym H))
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ (M.to_list Unrestricted ?T),
                          H' : get _ _ ?T = Some (?V, _)
                          |- _ = ?V /\ _ ] =>
                        apply In_nth_error in H;
                        let x := fresh "x" in
                        destruct H as [x H];
                        apply in_to_list_implies_get in H
                      end.
                      match goal with
                      | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                        rewrite H in H';
                        inversion H'; subst
                      end.
                      auto. }
                      
                    destructAll; subst; simpl in *.
                    match goal with
                    | [ |- ?A /\ _ ] =>
                      assert (Hsubgoal : A)
                    end.
                    { match goal with
                      | [ H : HasHeapType _ _ (Struct _) _ |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      destructAll.
                      econstructor;
                        [ eauto
                        |
                        | eauto
                        | split;
                          unfold empty_Function_Ctx; simpl; eauto ].

                      match goal with
                      | [ H : (_, _) = split (combine _ _) |- _ ] =>
                        rewrite combine_split in H;
                          inversion H; subst; auto
                      end.
                      
                      match goal with
                      | [ H : ReplaceAtIdx _ _ _ = Some (_, _) |- _ ] =>
                        specialize (ReplaceAtIdx_old_nth_error H)
                      end.
                      intros.
                      match goal with
                      | [ H : Forall3 _ _ ?L2 ?L3,
                          H' : nth_error ?L2 ?IDX = Some _,
                          H'' : nth_error ?L3 ?IDX = Some _ |- _ ] =>
                        specialize (forall3_nth_error_args23 H H' H'')
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : nth_error ?L1 _ = Some _,
                          H' : Forall3 _ ?L1 _ _ |- _ ] =>
                        rewrite (set_nth_nth_error _ _ _ H)
                      end.
                      match goal with
                      | [ H : nth_error ?L3 _ = Some _,
                          H' : Forall3 _ _ _ ?L3 |- _ ] =>
                        rewrite (set_nth_nth_error _ _ _ H)
                      end.
                      apply Forall3_set_nth; eauto.
                      match goal with
                      | [ H : HasTypeValue ?S _ ?V _ |-
                          HasTypeValue _ _ ?V _ ] =>
                        apply (HasTypeValue_same_envs S)
                      end.
                      - eapply HasTypeValue_empty_function_ctx_rev; eauto.
                        match goal with
                        | [ H : Function_Ctx_empty ?F |- _ ] =>
                          unfold Function_Ctx_empty in H;
                            destruct F; destructAll; subst; simpl in *
                        end.
                        constructor; simpl; eauto.
                      - match goal with
                        | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?S,
                            H' : SplitStoreTypings _ (f_unr (?L, ?HV, ?SZ))
                            |- _ ] =>
                          assert (Heq_inst_typs : InstTyp (f_unr (L, HV, SZ)) = InstTyp S);
                          [ | eapply (eq_trans (y := InstTyp S)) ]
                        end.
                        { eapply proj2.
                          eapply SplitStoreTypings_eq_typs2; eauto.
                          apply in_or_app.
                          right.
                          apply in_map; auto. }
                        -- solve_inst_or_unr_typ_eq.
                        -- rewrite (eq_sym Heq_inst_typs).
                           apply eq_sym.
                           eapply proj2.
                           eapply SplitStoreTypings_eq_typs2; eauto.
                           eapply nth_error_In; eauto.
                      - match goal with
                        | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?S |- _ ] =>
                          eapply (eq_trans (y := UnrTyp S))
                        end.
                        -- solve_inst_or_unr_typ_eq.
                        -- match goal with
                           | [ H : UnrTyp _ = UnrTyp ?S |-
                               UnrTyp ?S = _ ] =>
                             rewrite (eq_sym H)
                           end.
                           apply eq_sym.
                           eapply proj1.
                           eapply SplitStoreTypings_eq_typs2; eauto.
                           eapply nth_error_In; eauto.
                      - apply eq_map_empty;
                          eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                        all:
                          match goal with
                          | [ H : Function_Ctx_empty ?F |- _ ] =>
                            unfold Function_Ctx_empty in H;
                            destruct F; destructAll; simpl in *
                          end.
                        all: subst; auto. }

                    split; auto.
                    split; auto.
                    eapply StructTypeFits;
                      [ rewrite combine_split; eauto | ].

                    match goal with
                    | [ H : RoomForStrongUpdates _ _ |- _ ] =>
                      inversion H; subst; simpl in *;
                        [ exfalso; auto | ]
                    end.
                    
                    match goal with
                    | [ H : split (combine _ _) = (_, _) |- _ ] =>
                      rewrite combine_split in H;
                        inversion H; subst; auto
                    end.
                    match goal with
                    | [ H : get ?L ?M ?MEM = Some (_, _),
                        H' : Some _ = set ?L ?M ?MEM _ |- _ ] =>
                      specialize (get_set_same_size _ _ _ _ _ _ _ H (eq_sym H'))
                    end.
                    intros.
                    match goal with
                    | [ H : In (_, _, ?SZ) _ |- (_ <= ?SZ)%N ] =>
                      apply In_nth_error in H; destructAll
                    end.
                    match goal with
                    | [ H : nth_error _ _ = Some (_, _, ?SZ) |-
                        (_ <= ?SZ)%N ] =>
                      apply in_to_list_implies_get in H
                    end.
                    match goal with
                    | [ H : get ?L ?M ?MEM = _,
                        H' : get ?L ?M ?MEM = _ |- _ ] =>
                      rewrite H in H';
                      inversion H'; subst; simpl in *
                    end.
                    auto.
                 -- intros; simpl.
                    match goal with
                    | [ H : Some ?T = set _ _ ?MEM _ |- _ ] =>
                      assert (Hsame : forall n h l, In (n, h, l) (M.to_list Unrestricted T) -> n <> l1 -> In (n, h, l) (M.to_list Unrestricted MEM))
                    end.
                    { intros.
                      match goal with
                      | [ H : ?L <> ?L2 |- In (?L, _, _) _ ] =>
                        assert (Hneq2 : L2 <> L) by ltac:(intro; eauto)
                      end.
                      match goal with
                      | [ H : In (?L, _, _) _ |- In (?L, _, _) _ ] =>
                        apply In_nth_error in H
                      end.
                      destructAll.
                      match goal with
                      | [ H : nth_error _ _ = Some (?L, _, _) |-
                          In (?L, _, _) _ ] =>
                        apply in_to_list_implies_get in H
                      end.
                      match goal with
                      | [ H : Some _ = set ?L _ _ _,
                          H' : ?L <> _ |- _ ] =>
                        specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) H')
                      end.
                      intros.
                      match goal with
                      | [ H : get ?L ?M ?MEM = Some (_, _),
                          H' : get _ _ _ = get ?L ?M ?MEM |- _ ] =>
                        rewrite (eq_sym H') in H;
                        apply get_implies_in_to_list in H
                      end.
                      destructAll.
                      eapply nth_error_In; eauto. }
                    
                    match goal with
                    | [ H : false = (?L1 =? ?L2)%N |- _ ] =>
                      assert (Hneq : L1 <> L2)
                    end.
                    { intro.
                      subst.
                      rewrite OrdersEx.N_as_OT.eqb_refl in Heqn_eq_l1.
                      inversion Heqn_eq_l1. }
                    match goal with
                    | [ H : forall _ _ _, In _ (M.to_list Unrestricted ?T) -> _ -> _,
                        H' : In _ (M.to_list Unrestricted ?T) |- _ ] =>
                      specialize (H _ _ _ H' Hneq);
                        match goal with
                        | [ H'' : forall _, In _ (M.to_list Unrestricted ?MEM) -> _ |- _ ] =>
                          specialize (H'' _ H)
                        end
                    end.
                    auto.
               - eapply Forall_Permutation_lst; eauto.
                 match goal with
                 | [ H : SplitStoreTypings ?L _ |- Forall _ ?L ] =>
                   inversion H; subst; simpl in *
                 end.
                 auto.
               - specialize ((Permutation.Permutation_map LinTyp) _ _ Hperm).
                 intro Hperm'.
                 eapply SplitHeapTypings_Permutation; eauto.
                 match goal with
                 | [ H : SplitStoreTypings ?L _
                     |- SplitHeapTypings (map _ ?L) _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 auto. }
             destruct Hsubgoal as [S_lin' [S_unr']].
             destructAll.
             eapply (MeminstT _ S_lin' S_unr').
             --- assert (Hdom_eq : MemUtils.dom_lin (meminst s) <--> MemUtils.dom_lin (meminst s')).
                 { unfold update_mem in *.
                   match goal with
                   | [ H : context[set ?L ?M ?MEM ?V] |- _ ] =>
                     remember (set L M MEM V) as news;
                     revert Heqnews;
                     revert H;
                     case news
                   end.
                   - intros.
                     match goal with
                     | [ H : Some _ = Some _ |- _ ] =>
                       inversion H; subst; simpl in *
                     end.
                     eapply proj1.
                     eapply set_preserves_doms; eauto.
                   - let H := fresh "H" in
                     intro H; inversion H. }
                 eapply Same_set_trans;
                   [ eapply Same_set_sym; eauto | ].
                 clear Hdom_eq.
                 eapply Same_set_trans; [ eauto | ].
                 eapply Same_set_trans;
                   [ apply Same_set_Union_compat_l;
                     eapply eq_map_Dom_ht; eauto | ].
                 eapply Same_set_Union_compat_r.
                 eapply eq_map_Dom_ht; auto.
             --- assert (Hdom_eq : MemUtils.dom_unr (meminst s) <--> MemUtils.dom_unr (meminst s')).
                 { unfold update_mem in *.
                   match goal with
                   | [ H : context[set ?L ?M ?MEM ?V] |- _ ] =>
                     remember (set L M MEM V) as news;
                     revert Heqnews;
                     revert H;
                     case news
                   end.
                   - intros.
                     match goal with
                     | [ H : Some _ = Some _ |- _ ] =>
                       inversion H; subst; simpl in *
                     end.
                     eapply proj2.
                     eapply set_preserves_doms; eauto.
                   - let H := fresh "H" in
                     intro H; inversion H. }
                 eapply Same_set_trans;
                   [ eapply Same_set_sym; eauto | ].
                 assert (Hunr_eq1 : UnrTyp Sh' = UnrTyp Sh).
                 { solve_inst_or_unr_typ_eq. }
                 rewrite Hunr_eq1.
                 assert (Hunr_eq2 : UnrTyp Sp' = UnrTyp Sp).
                 { solve_inst_or_unr_typ_eq. }
                 rewrite Hunr_eq2.
                 auto.
             --- match goal with
                 | [ H : SplitStoreTypings (S_lin ++ S_unr) _ |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 ---- constructor.
                      ----- assert (Hinst_eq : InstTyp Sh = InstTyp Sh').
                            { solve_inst_or_unr_typ_eq. }
                            assert (Hunr_eq : UnrTyp Sh = UnrTyp Sh').
                            { solve_inst_or_unr_typ_eq. }
                            rewrite (eq_sym Hinst_eq).
                            rewrite (eq_sym Hunr_eq).
                            auto.
                      ----- simpl.
                            eapply SplitHeapTypings_map_eq; eauto.
             --- auto.
             --- auto.
          -- inversion Hst; subst; simpl in *.
             match goal with
             | [ H : HasTypeMeminst _ _ _ |- _ ] =>
               inversion H; subst; simpl in *
             end.


             assert (Hlemma : forall l t,
                        (l =? l1)%N = false ->
                        get_heaptype l (LinTyp Sh) = Some t \/
                        get_heaptype l (LinTyp Sp) = Some t ->
                        get_heaptype l (LinTyp Sh') = Some t \/
                        get_heaptype l (LinTyp Sp') = Some t).
             { intro; intro; intro.
               let H := fresh "H" in intro H; case H; intros.
               - left.
                 eapply SplitStoreTypings_get_heaptype_LinTyp; [ eauto | | eauto ].
                 constructor 2; constructor; auto.
               - match goal with
                 | [ H : get_heaptype ?L (LinTyp ?S) = _,
                     H' : SplitStoreTypings _ ?S |-
                     context[?L] ] =>
                   specialize (SplitStoreTypings_inv H H');
                   clear H
                 end.
                 intros; destructAll.
                 match goal with
                 | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 ---- match goal with
                      | [ H : get_heaptype ?L (LinTyp ?S) = _,
                          H' : SplitStoreTypings _ ?S |-
                          context[?L] ] =>
                        specialize (SplitStoreTypings_inv H H');
                        clear H
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ [_; _] |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      ----- right.
                            match goal with
                            | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP
                                |- get_heaptype _ (LinTyp ?SP) = _ ] =>
                              eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                            end.
                            simpl.
                            match goal with
                            | [ H : HasTypeValue _ _ (Ref _) _ |- _ ] =>
                              inversion H; subst; simpl in *
                            end.
                            unfold eq_map in *.
                            match goal with
                            | [ H : forall _, get_heaptype _ ?LT = _,
                                H' : get_heaptype _ ?LT = _ |- _ ] =>
                              rewrite H in H'
                            end.
                            unfold get_heaptype in *.
                            match goal with
                            | [ H : map_util.M.find (N.succ_pos ?L1) (map_util.M.add (N.succ_pos ?L2) _ _) = _ |- _ ] =>
                              assert (Hloc_dec : L1 = L2 \/ L1 <> L2) by apply eq_dec_N
                            end.
                            case Hloc_dec; intros; subst.
                            ------ rewrite N.eqb_refl in *.
                                   match goal with
                                   | [ H : true = false |- _ ] => inversion H
                                   end.
                            ------ rewrite M.gso in *.
                                   2-3: intro.
                                   2-3:
                                     match goal with
                                     | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                       assert (Hloc_eq : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2));
                                       [ rewrite H; auto | ]
                                     end.
                                   2-3:
                                     repeat rewrite N.pos_pred_succ in *;
                                     subst;
                                     eauto.
                                   rewrite M.gempty in *.
                                   auto.
                      ----- match goal with
                            | [ H : _ \/ False |- _ ] =>
                              case H; [ | intros; exfalso; auto ]
                            end.
                            intros; subst.
                            match goal with
                            | [ H : get_heaptype ?L (LinTyp ?S) = _,
                                H' : SplitStoreTypings _ ?S |-
                                context[?L] ] =>
                              specialize (SplitStoreTypings_inv H H');
                              clear H
                            end.
                            intros; destructAll.
                            match goal with
                            | [ H : In _ [_; _] |- _ ] =>
                              inversion H; subst; simpl in *
                            end.
                            ------ left.
                                   match goal with
                                   | [ H : SplitStoreTypings [?S; _] ?SP
                                       |- get_heaptype _ (LinTyp ?SP) = _ ] =>
                                     eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                                   end.
                                   auto.
                            ------ match goal with
                                   | [ H : _ \/ False |- _ ] =>
                                     case H;
                                     [ | intros;
                                         exfalso; auto ]
                                   end.
                                   intros; subst.
                                   match goal with
                                   | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                       H' : get_heaptype _ (LinTyp ?S) = _ |- _ ] =>
                                     rewrite get_heaptype_empty in H'; [ inversion H' | exact H ]
                                   end.
                 ---- right.
                      match goal with
                      | [ H : In ?S (?S1 ++ ?S2),
                          H' : SplitStoreTypings (_ :: ?S1 ++ ?S2) _ |- _ ] =>
                        eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ]; auto
                      end.
                      constructor 2; auto. }

             assert (Hrealgoal : HasTypeMeminst Sh' Sp' (meminst st')).
             { match goal with
               | [ |- HasTypeMeminst _ _ (meminst ?S) ] =>
               assert (Hsubgoal : exists S_lin' S_unr',
                                    Forall2
                                      (fun (S0 : StoreTyping) '(loc, hv, len) =>
                                       exists ht : HeapType,
                                         NoCapsHeapType [] ht = true /\
                                         (get_heaptype loc (LinTyp Sh') = Some ht \/
                                          get_heaptype loc (LinTyp Sp') = Some ht) /\
                                         HasHeapType S0 empty_Function_Ctx hv ht /\
                                         RoomForStrongUpdates len ht /\
                                         HeapTypeValid empty_Function_Ctx ht) S_lin'
                                      (M.to_list Linear (meminst S)) /\
                                    Forall2
                                      (fun (S0 : StoreTyping) '(loc, hv, len) =>
                                       exists ht : HeapType,
                                         NoCapsHeapType [] ht = true /\
                                         get_heaptype loc (UnrTyp S0) = Some ht /\
                                         HasHeapType S0 empty_Function_Ctx hv ht /\
                                         RoomForStrongUpdates len ht /\
                                         HeapTypeValid empty_Function_Ctx ht) S_unr'
                                      (M.to_list Unrestricted (meminst S)) /\
                                    Forall
                                      (fun S' : StoreTyping =>
                                       InstTyp Sh' = InstTyp S' /\ UnrTyp Sh' = UnrTyp S')
                                      (S_lin' ++ S_unr') /\
                                    SplitHeapTypings (map LinTyp (S_lin' ++ S_unr')) (LinTyp Sh'))
               end.
               { unfold update_mem in *.
                 match goal with
                 | [ H : context[set ?A ?B ?C ?D] |- _ ] =>
                   remember (set A B C D) as o;
                     repeat match goal with
                     | [ H : context[o] |- _ ] => revert H
                     end
                 end.
                 case o; [ | intros H' H''; inversion H'' ].
                 intros t H' H''.
                 inversion H''; subst; simpl in *.

                 derive_mappings f_lin f_unr.

                 repeat match goal with
                        | [ H : _ /\ _ |- _ ] => destruct H
                        end.
                 
                 match goal with
                 | [ H : get_mem ?S ?L Linear = Some (?HV, ?SZ) |- _ ] =>
                   assert (Hin : In (L, HV, SZ) (M.to_list Linear (meminst S)));
                   [ unfold get_mem in H;
                     apply get_implies_in_to_list in H | ]
                 end.
                 { destructAll.
                   eapply nth_error_In; eauto. }

                 match goal with
                 | [ H : forall _, In _ (M.to_list Linear _) -> _ |- _ ] =>
                   let H' := fresh "H" in
                   specialize (H _ Hin) as H'
                 end.
                 simpl in *; destructAll.

                 match goal with
                 | [ H : get_heaptype ?L _ = Some ?T \/
                         get_heaptype ?L _ = Some ?T,
                     H' : HasTypeValue
                            _ _ (Ref (LocP ?L _))
                            (QualT
                               (RefT _ _ (StructType ?TPL)) _) |- _ ] =>
                   assert (Htyp_eq : T = StructType TPL)
                 end.
                 { match goal with
                   | [ H : HasTypeValue _ _ (Ref _) _ |- _ ] =>
                     inversion H; subst; simpl in *
                   end.
                   apply eq_sym.
                   eapply EqualTyps_StructLinInstruction.
                   5: eauto.
                   3: eauto.
                   2: eauto.
                   all: eauto. }

                 match goal with
                 | [ H : HasHeapType _ _ (Struct _) _ |- _ ] =>
                   inversion H; subst; simpl in *
                 end.

                 match goal with
                 | [ H : HasTypeValue ?SV _ ?V _, H' : Some _ = set _ _ _ (Struct (set_nth ?VIS ?IDX ?V)), H'' : Forall3 _ ?SS ?VIS _ |- _ ] =>
                   assert (Hcombine : exists S', SplitStoreTypings ((set_nth SS IDX SV)) S')
                 end.
                 { eapply SplitStoreTypings_safe_set_nth;
                   [ | | | eauto ]; [ eauto | | eauto ].
                   apply in_or_app; left.
                   apply in_map.
                   auto. }
                   
                 destruct Hcombine as [Snew].
                 
                 match goal with
                 | [ H : get_mem _ ?L Linear = Some (?HV, ?SZ) |- _ ] =>
                   remember (map (fun '(loc, hv, len) => if BinNatDef.N.eqb loc L then Snew else f_lin (loc, hv, len)) (M.to_list Linear t)) as S_lin';
                   remember (map f_unr (M.to_list Unrestricted t)) as S_unr'
                 end.

                 match goal with
                 | [ H : Forall2 _ _ (M.to_list Unrestricted (meminst ?S)) |- _ ] =>
                   rewrite forall2_map in H;
                   assert (Hperm : Permutation.Permutation (M.to_list Unrestricted t) (M.to_list Unrestricted (meminst S)));
                   [ | assert (Hsame : forall x, In x (M.to_list Unrestricted t) -> In x (M.to_list Unrestricted (meminst S))) ]
                 end.
                 { apply Permutation.NoDup_Permutation.
                   - apply to_list_NoDup.
                   - apply to_list_NoDup.
                   - let x := fresh "x" in
                     intro x; destruct x as [[curL curHV] curSz].
                     constructor.
                     -- let H := fresh "H" in
                        intro H; apply In_nth_error in H.
                        destructAll.
                        assert (Hneq : Linear <> Unrestricted).
                        { let H := fresh "H" in intro H; inversion H. }
                        match goal with
                        | [ H : nth_error _ _ = Some (?L, _, _),
                            H' : Some _ = set _ _ _ _ |- _ ] =>
                          apply in_to_list_implies_get in H;
                          specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H') Hneq);
                          rewrite H
                        end.
                        let H := fresh "H" in
                        intro H; apply get_implies_in_to_list in H.
                        destructAll.
                        eapply nth_error_In; eauto.
                     -- let H := fresh "H" in
                        intro H; apply In_nth_error in H.
                        destructAll.
                        assert (Hneq : Linear <> Unrestricted).
                        { let H := fresh "H" in intro H; inversion H. }
                        match goal with
                        | [ H : nth_error _ _ = Some (?L, _, _),
                            H' : Some _ = set _ _ _ _ |- _ ] =>
                          apply in_to_list_implies_get in H;
                          specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H') Hneq);
                          rewrite H
                        end.
                        let H := fresh "H" in
                        intro H;
                        apply eq_sym in H;
                        apply get_implies_in_to_list in H.
                        destructAll.
                        eapply nth_error_In; eauto. }
                 { intros.
                   eapply Permutation.Permutation_in; eauto. }

                 exists S_lin', S_unr'; subst.
                 split; [ | split; [ | split ] ].
                 - match goal with
                   | [ H : StructType _ = StructType _ |- _ ] =>
                     inversion H; subst; simpl in *
                   end.
                   match goal with
                   | [ H : _ = split (combine _ _) |- _ ] =>
                     rewrite combine_split in H; auto; inversion H; subst
                   end.
                   destructAll.
                   eapply StructLinear_WellTyped.
                   1,3-13,15-20,23: eauto.
                   -- apply eq_sym; eauto.
                   -- destruct F; subst; simpl in *.
                      unfold Function_Ctx_empty in *.
                      simpl in *.
                      destructAll.
                      auto.
                   -- let x := fresh "x" in
                      intro x; destruct x as [[curL curHV] curSz].
                      auto.
                   -- match goal with
                      | [ H' : SplitStoreTypings (?S :: ?S1 ++ ?S2) ?SP |- context[?SP] ] =>
                        eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ]; [ | constructor; auto ]
                      end.
                      simpl.
                      unfold get_heaptype.
                      rewrite M.gss; auto.
                 - rewrite forall2_map.
                   intros.
                   match goal with
                   | [ H : In _ (M.to_list Unrestricted _) |- _ ] =>
                     specialize (Hsame _ H)
                   end.
                   match goal with
                   | [ H : forall _, In _ (M.to_list Unrestricted (meminst _)) -> _ |- _ ] => specialize (H _ Hsame)
                   end.
                   auto.
                 - rewrite Forall_forall.
                   intros.
                   match goal with
                   | [ H : In _ (_ ++ _) |- _ ] =>
                     apply in_app_or in H; case H; intros
                   end.
                   -- match goal with
                      | [ H : In _ (map _ _) |- _ ] =>
                        apply in_map_inv in H; destructAll; subst
                      end.
                      match goal with
                      | [ X : _ * _ * _ |- _ ] =>
                        destruct X as [[curL curHV] curSz]
                      end.
                      match goal with
                      | [ |- context[(?L1 =? ?L2)%N] ] =>
                        remember (L1 =? L2)%N as locb;
                        revert Heqlocb;
                        case locb; intros
                      end.
                      --- match goal with
                          | [ H : true = (_ =? _)%N |- _ ] =>
                            specialize (Ndec.Neqb_complete _ _ (eq_sym H))
                          end.
                          intros; subst.
                          use_StructLinear_SplitStoreTypings_eq_typs2.
                          intros; destructAll; split.
                          ---- eapply eq_trans; [ | eauto ].
                               solve_inst_or_unr_typ_eq.
                          ---- eapply eq_trans; [ | eauto ].
                               solve_inst_or_unr_typ_eq.
                      --- match goal with
                          | [ H : false = (?L1 =? ?L2)%N |- _ ] =>
                            assert (Hloc_neq : L1 <> L2);
                            [ | assert (Hloc_neq2 : L2 <> L1) ]
                          end.
                          { rewrite (iff_sym (N.eqb_neq _ _)); eauto. }
                          { intro; eauto. }
                          match goal with
                          | [ H : In (_, _, _) _ |- _ ] =>
                            apply In_nth_error in H
                          end.
                          destructAll.
                          match goal with
                          | [ H : nth_error _ _ = Some _ |- _ ] =>
                            apply in_to_list_implies_get in H
                          end.
                          match goal with
                          | [ H : Some _ = set _ _ _ _ |- _ ] =>
                            specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) Hloc_neq2)
                          end.
                          intros.
                          match goal with
                          | [ H : get ?L ?M ?MEM = Some _,
                              H' : get _ _ _ = get ?L ?M ?MEM |- _ ] =>
                            rewrite (eq_sym H') in H;
                            apply get_implies_in_to_list in H
                          end.
                          destructAll.
                          match goal with
                          | [ H : nth_error (M.to_list Linear _) _ = _ |- _ ] =>
                            apply nth_error_In in H
                          end.
                          match goal with
                          | [ H : In ?TPL ?L |- context[?F ?TPL] ] =>
                            let H' := fresh "H" in
                            assert (H' : In (F TPL) (map F L))
                          end.
                          { apply in_map; auto. }
                          match goal with
                          | [ H : In ?TPL ?L,
                              H' : SplitStoreTypings (?L ++ ?L2) _ |- _ ] =>
                            let H'' := fresh "H" in
                            assert (H'' : In TPL (L ++ L2))
                          end.
                          { apply in_or_app.
                            left; auto. }
                          
                          match goal with
                          | [ H : In ?TPL (?L ++ ?L2),
                              H' : SplitStoreTypings (?L ++ ?L2) _ |- _ ] =>
                            specialize (SplitStoreTypings_eq_typs2 H' H)
                          end.
                          intros; destructAll; split.
                          ---- apply eq_sym.
                               eapply eq_trans; [ eauto | ].
                               solve_inst_or_unr_typ_eq.
                          ---- apply eq_sym.
                               eapply eq_trans; [ eauto | ].
                               solve_inst_or_unr_typ_eq.
                   -- match goal with
                      | [ H : In _ (map _ _) |- _ ] =>
                        apply in_map_inv in H; destructAll; subst
                      end.
                      match goal with
                      | [ X : _ * _ * _ |- _ ] =>
                        destruct X as [[curL curHV] curSz]
                      end.
                      match goal with
                      | [ H : forall _, In _ ?L -> In _ _,
                          H' : In _ ?L |- _ ] =>
                        specialize (H _ H')
                      end.
                      match goal with
                      | [ H : In ?TPL ?L,
                          H' : SplitStoreTypings (_ ++ map ?F ?L) _
                          |- context[?F ?TPL] ] =>
                        let H' := fresh "H" in
                        assert (H' : In (F TPL) (map F L))
                      end.
                      { apply in_map; auto. }
                      match goal with
                      | [ H : In ?TPL ?L2,
                          H' : SplitStoreTypings (?L ++ ?L2) _ |- _ ] =>
                          let H'' := fresh "H" in
                          assert (H'' : In TPL (L ++ L2))
                      end.
                      { apply in_or_app.
                        right; auto. }
                      match goal with
                      | [ H : In ?TPL (?L ++ ?L2),
                          H' : SplitStoreTypings (?L ++ ?L2) _ |- _ ] =>
                        specialize (SplitStoreTypings_eq_typs2 H' H)
                      end.
                      intros; destructAll; split.
                      --- apply eq_sym.
                          eapply eq_trans; [ eauto | ].
                          solve_inst_or_unr_typ_eq.
                      --- apply eq_sym.
                          eapply eq_trans; [ eauto | ].
                          solve_inst_or_unr_typ_eq.
                 - match goal with
                   | [ H : StructType _ = StructType _ |- _ ] =>
                     inversion H; subst; simpl in *
                   end.
                   match goal with
                   | [ H : (_, _) = split (combine _ _) |- _ ] =>
                     rewrite combine_split in H; auto;
                     inversion H; subst; simpl in *
                   end.

                   match goal with
                   | [ H : Permutation.Permutation ?L1 ?L2
                       |- context[map ?F ?L1] ] =>
                     assert (Hperm2 : Permutation.Permutation (map F L1) (map F L2))
                   end.
                   { apply Permutation.Permutation_map; auto. }
                   unfold get_mem in *.
                   match goal with
                   | [ H : get ?L ?M ?MEM = Some _ |- _ ] =>
                     specialize (get_implies_in_to_list _ _ _ _ _ H)
                   end.
                   intros; destructAll.
                   match goal with
                   | [ H : nth_error (M.to_list Linear ?MEM1) ?IDX = Some _,
                       H' : Forall2 _ (map ?F1 (M.to_list Linear ?MEM1)) (M.to_list Linear ?MEM1),
                       H'' : SplitStoreTypings (set_nth _ _ _ ) ?SN |-
                       context[map ?F2 (M.to_list Linear ?MEM2)] ] =>
                     assert (Hperm3 :
                               Permutation.Permutation
                                 (set_nth
                                    (map F1 (M.to_list Linear MEM1))
                                    IDX
                                    SN)
                                 (map F2 (M.to_list Linear MEM2)))
                   end.
                   
                   { match goal with
                     | [ H : Some _ = set _ _ _ _ |- _ ] =>
                       specialize (get_set_same _ _ _ _ _ (eq_sym H))
                     end.
                     intros; destructAll.
                     eapply set_to_list_Permutation; eauto.
                     let x := fresh "x" in
                     intro x; destruct x as [[curL curHV] curSz].
                     intros; auto. }

                   specialize (Permutation.Permutation_map LinTyp (Permutation.Permutation_app Hperm3 (Permutation.Permutation_sym Hperm2))).
                   let H := fresh "H" in
                   intro H;
                   eapply SplitHeapTypings_permut; [ exact H | ].
                   rewrite set_nth_app;
                     [ | eapply nth_error_Some_length;
                         eapply nth_error_map; eauto ].

                   match goal with
                   | [ |- SplitHeapTypings (map LinTyp ?Ss) (LinTyp ?S) ] =>
                     let H := fresh "H" in
                     assert (H : SplitStoreTypings Ss S);
                     [ | inversion H; auto ]
                   end.
                   match goal with
                   | [ H : ReplaceAtIdx _ _ _ = _ |- _ ] =>
                     specialize (ReplaceAtIdx_old_nth_error H)
                   end.
                   intros.
                   match goal with
                   | [ H : Forall3 _ _ ?L2 ?L3,
                       H' : nth_error ?L2 _ = _,
                       H'' : nth_error ?L3 _ = _ |- _ ] =>
                     specialize (forall3_nth_error_args23 H H' H'')
                   end.
                   intros; destructAll.
                   match goal with
                   | [ H : SplitStoreTypings ?Ss (f_lin ?TPL),
                       H' : nth_error ?Ss _ = Some ?S |- _ ] =>
                     eapply (SplitStoreTypings_StructSet_add_one (S':=f_lin TPL) (S'':=S));
                     [ eauto | | exact H | exact H'
                     | | eauto | eauto ]
                   end.
                   -- rewrite nth_error_app1;
                        [ | eapply nth_error_Some_length ];
                        eapply nth_error_map; eauto.
                   -- eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                      match goal with
                      | [ H : Function_Ctx_empty ?F |- _ ] =>
                        revert H; unfold Function_Ctx_empty;
                        destruct F; subst; simpl in *
                      end.
                      intros; destructAll; auto. }
                          
               destruct Hsubgoal as [S_lin' [S_unr']].
               destructAll.

               unfold update_mem in *.
               destruct st'; subst; simpl in *.
               match goal with
               | [ H : context[set ?L ?Q ?MEM ?V] |- _ ] =>
                 remember (set L Q MEM V) as new_mem; revert H
               end.
               revert Heqnew_mem.
               case new_mem; [ | intros _ H'; inversion H' ].
               intros t' H' H''.
               inversion H''; subst; simpl in *.
               
               eapply (MeminstT _ S_lin' S_unr').
                 
               - eapply Same_set_trans.
                 -- eapply Same_set_sym.
                    eapply proj1.
                    eapply set_preserves_doms; [ | apply eq_sym; eauto ].
                    unfold get_mem in *; eauto.
                 -- eapply Same_set_trans; [ eauto | ].
                    constructor.
                    --- unfold Dom_ht.
                        unfold Ensembles.Included.
                        unfold Ensembles.In.
                        unfold Dom_map.
                        intros.
                        match goal with
                        | [ H : context[(_ =? ?L)%N]
                            |- Ensembles.Union _ _ _ ?L2 ] =>
                          assert (Hloc_dec : L = L2 \/ L <> L2) by apply eq_dec_N
                        end.
                        case Hloc_dec; intros; subst.
                        ---- right.
                             unfold Ensembles.In.
                             match goal with
                             | [ H : context[M.add (N.succ_pos ?L) ?HT _]
                                 |- context[map_util.M.find (N.succ_pos ?L) _] ] =>
                               exists HT
                             end.
                             match goal with
                             | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP
                                 |- context[?SP] ] =>
                               eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                             end.
                             simpl.
                             unfold get_heaptype.
                             rewrite M.gss; auto.
                        ---- match goal with
                             | [ H : ?L1 <> ?L2 |- _ ] =>
                               assert (Hloc_neq : (L2 =? L1)%N = false)
                             end.
                             { rewrite N.eqb_neq; auto. }
                             match goal with
                             | [ H : Ensembles.Union _ _ _ _ |- _ ] =>
                               inversion H; subst; simpl in *
                             end.
                             ----- unfold Ensembles.In in *.
                                   destructAll.
                                   match goal with
                                   | [ H : map_util.M.find (N.succ_pos ?L) _ = Some ?HT
                                       |- context[?L] ] =>
                                     specialize (Hlemma _ HT Hloc_neq)
                                   end.
                                   match goal with
                                   | [ H : ?A \/ ?B -> _ |- _ ] =>
                                     let H' := fresh "H" in
                                     assert (H' : A \/ B);
                                     [ | specialize (H H'); case H ]
                                   end.
                                   { left; auto. }
                                   ------ left; eexists; eauto.
                                   ------ right; eexists; eauto.
                             ----- unfold Ensembles.In in *.
                                   destructAll.
                                   match goal with
                                   | [ H : map_util.M.find (N.succ_pos ?L) _ = Some ?HT
                                       |- context[?L] ] =>
                                     specialize (Hlemma _ HT Hloc_neq)
                                   end.
                                   match goal with
                                   | [ H : ?A \/ ?B -> _ |- _ ] =>
                                     let H' := fresh "H" in
                                     assert (H' : A \/ B);
                                     [ | specialize (H H'); case H ]
                                   end.
                                   { right; auto. }
                                   ------ left; eexists; eauto.
                                   ------ right; eexists; eauto.
                    --- unfold Dom_ht.
                        unfold Ensembles.Included.
                        unfold Ensembles.In.
                        unfold Dom_map.
                        intros.
                        match goal with
                        | [ H : Ensembles.Union _ _ _ _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        ---- unfold Ensembles.In in *.
                             destructAll.
                             match goal with
                             | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = _,
                                 H' : SplitStoreTypings _ ?S |-
                                 context[?L] ] =>
                               specialize (SplitStoreTypings_inv H H')
                             end.
                             intros; destructAll.
                             match goal with
                             | [ H : In _ [_; _] |- _ ] =>
                               inversion H; subst; simpl in *
                             end.
                             ----- match goal with
                                   | [ H : get_heaptype ?L (LinTyp ?S) = Some ?T,
                                       H' : SplitStoreTypings [?S; ?SA] ?S2,
                                       H'' : SplitStoreTypings [?SB; ?S2] ?S3,
                                       H''' : SplitStoreTypings (?S3 :: ?Ss1 ++ ?Ss2) ?SP |- _ ] =>
                                     let H0 := fresh "H" in
                                     let H1 := fresh "H" in
                                     let H2 := fresh "H" in
                                     let H3 := fresh "H" in
                                     let H4 := fresh "H" in
                                     assert (H0 : In S [S; SA]);
                                     [
                                     | specialize (SplitStoreTypings_get_heaptype_LinTyp H H0 H');
                                       intro H1;
                                       assert (H2 : In S2 [SB; S2]);
                                       [
                                       | specialize (SplitStoreTypings_get_heaptype_LinTyp H1 H2 H'');
                                         intro H3;
                                         assert (H4 : In S3 (S3 :: Ss1 ++ Ss2));
                                         [
                                         | specialize (SplitStoreTypings_get_heaptype_LinTyp H3 H4 H''') ] ] ]
                                   end.
                                   { constructor; auto. }
                                   { constructor 2; constructor; auto. }
                                   { constructor; auto. }
                                   intros.
                                   right; eexists; eauto.
                             ----- match goal with
                                   | [ H : _ \/ False |- _ ] =>
                                     case H;
                                       [ | intros; exfalso; auto ]
                                   end.
                                   intros; subst.
                                   left; eexists; eauto.
                        ---- unfold Ensembles.In in *.
                             destructAll.
                             match goal with
                             | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = _,
                                 H' : SplitStoreTypings _ ?S |-
                                 context[?L] ] =>
                               specialize (SplitStoreTypings_inv H H')
                             end.
                             intros; destructAll.
                             match goal with
                             | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                               inversion H; subst; simpl in *
                             end.
                             ----- unfold get_heaptype in *.
                                   match goal with
                                   | [ H : map_util.M.find
                                             (N.succ_pos ?L1)
                                             (M.add
                                                (N.succ_pos ?L2)
                                                _ _) = _ |- _ ] =>
                                     assert (Hloc_dec : L1 = L2 \/ L1 <> L2)
                                   end.
                                   { apply eq_dec_N. }
                                   case Hloc_dec; intros; subst.
                                   ------ right.
                                          unfold Ensembles.In.
                                          match goal with
                                          | [ H : HasTypeValue _ _ (Ref (LocP _ Linear)) _ |- _ ] =>
                                            inversion H; subst; simpl in *
                                          end.
                                          match goal with
                                          | [ H : SplitStoreTypings (?S :: ?Ss1 ++ ?Ss2) ?SP,
	                                          H' : SplitStoreTypings [?S1; ?S2] ?S,
                                              H'' : eq_map (LinTyp ?S1) (map_util.M.add _ ?HT _)
                                              |- context[?SP] ] =>
                                            exists HT;
                                            eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S));
                                            [ | | exact H ];
                                            [ | constructor; auto ];
                                            eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1));
                                            [ | | exact H' ];
                                            [ | constructor; auto ];
                                            unfold eq_map in H'';
                                            rewrite H''
                                          end.
                                          unfold get_heaptype.
                                          rewrite M.gss; auto.
                                   ------ rewrite M.gso in *.
                                          ------- rewrite M.gempty in *.
                                                  match goal with
                                                  | [ H : None = Some _ |- _ ] =>
                                                    inversion H
                                                  end.
                                          ------- intro.
                                                  match goal with
                                                  | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                                    let H' := fresh "H" in
                                                    assert (H' : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2));
                                                    [ rewrite H;
                                                      auto | ];
                                                    repeat rewrite N.pos_pred_succ in H'
                                                  end.
                                                  auto.
                             ----- right.
                                   unfold Ensembles.In.
                                   match goal with
                                   | [ H : SplitStoreTypings (?S :: ?Ss1 ++ ?Ss2) ?SP,
                                       H' : In ?S0 (?Ss1 ++ ?Ss2),
                                       H'' : get_heaptype ?L (LinTyp ?S0) = Some ?HT
                                       |- context[map_util.M.find (N.succ_pos ?L) (LinTyp ?SP)] ] =>
                                     exists HT;
                                     eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S0));
                                     [ | | exact H ];
                                     [ | constructor 2; exact H' ]
                                   end.
                                   auto.
               - assert (Hunr_eq1 : UnrTyp Sh' = UnrTyp Sh).
                 { solve_inst_or_unr_typ_eq. }
                 assert (Hunr_eq2 : UnrTyp Sp' = UnrTyp Sp).
                 { solve_inst_or_unr_typ_eq. }
                 rewrite Hunr_eq1.
                 rewrite Hunr_eq2.
                 assert (Heq : MemUtils.dom_unr meminst0 <--> MemUtils.dom_unr (meminst s)).
                 { unfold MemUtils.dom_unr.
                   unfold MemUtils.dom.
                   unfold Ensembles.Same_set.
                   split.
                   - unfold Ensembles.Included.
                     unfold Ensembles.In.
                     intros.
                     destructAll.
                     assert (Huneq : Linear <> Unrestricted).
                     { intro H'''; inversion H'''. }
                     match goal with
                     | [ H : get ?L Unrestricted _ = Some _ |- _ ] =>
                       
                       specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H') Huneq)
                     end.
                     intros.
                     match goal with
                     | [ H : ?A = ?B, H' : ?B = ?C |- _ ] =>
                       rewrite H; rewrite H'
                     end.
                     eexists; eauto.
                   - unfold Ensembles.Included.
                     unfold Ensembles.In.
                     intros.
                     destructAll.
                     assert (Huneq : Linear <> Unrestricted).
                     { intro H'''; inversion H'''. }
                     match goal with
                     | [ H : get ?L Unrestricted (meminst s) = Some _ |- _ ] =>
                       
                       specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H') Huneq)
                     end.
                     intros.
                     match goal with
                     | [ H : ?A = ?B, H' : ?A = ?C |- _ ] =>
                       rewrite (eq_sym H'); rewrite H
                     end.
                     eexists; eauto. }
                 eapply Same_set_trans; eauto.
               - constructor; auto.
               - auto.
               - auto. }
             unfold update_out_set.
             destruct (L.has_urn_ptr_HeapValue (Struct (set_nth vis j v))); destruct (L.has_urn_ptr_HeapValue (Struct vis)); auto. }
      
      split; [ | split; [ | split; [ | split; [ | split ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite (eq_sym Hunr).
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow ?A (?B ++ ?C ++ ?D ++ ?E)] ] =>
           replace A with (A ++ []) at 1 by apply app_nil_r;
           replace (B ++ C ++ D ++ E) with (A ++ E) at 1
         end.
         2:{
           rewrite app_assoc_reverse.
           match goal with
           | [ |- _ ++ ?A = _ ++ ?B ] =>
             let H := fresh "H" in
             assert (H : A = B); [ | rewrite H; eauto ]
           end.
           rewrite app_assoc.
           auto.
         }
         eapply FrameTyp.
         --- reflexivity.
         --- apply Forall_trivial.
             intro qt.
             destruct qt.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- econstructor.
             match goal with
             | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
               inversion H; simpl in *; subst
             end.
             ---- (* Old array of types = new array of types when qualifier is unrestricted. *)
                  match goal with
                  | [ H : ReplaceAtIdx _ ?L1 _ = Some (?L2, _) |- _ ] =>
                    assert (Heq_typs : L1 = L2)
                  end.
                  { match goal with
                    | [ H : _ \/ _ |- _ ] =>
                      inversion H; subst; simpl in *
                    end.
                    - exfalso.
                      eapply QualLeq_Const_False.
                      destruct F; simpl in *; subst.
                      unfold Function_Ctx_empty in *.
                      simpl in *; destructAll; auto.
                      eapply QualLeq_Trans; [ eauto | ].
                      eauto.
                    - eapply ReplaceAtIdx_no_change; eauto. }
                  simpl in *; subst.
                  constructor.
                  ----- simpl; auto.
                  ----- simpl.
                        match goal with
                        | [ H : HasTypeValue ?S _ (Ref (LocP _ _)) _ |- _ ] =>
                          assert (Hunr2 : UnrTyp S = UnrTyp Sstack) by solve_inst_or_unr_typ_eq
                        end.
                        rewrite (eq_sym Hunr2).
                        auto.
                  ----- destruct F; simpl in *; subst; eauto.
                  ----- match goal with
                        | [ H : TypeValid _ _ |- _ ] =>
                          inversion H; subst
                        end.
                        constructor; destruct F; simpl in *; subst; eauto.
                        replace_heaptypevalid_parts label ret size type location.
                        apply HeapTypeValid_linear.
                        auto.
             ---- simpl in *; subst.
                  constructor.
                  ----- simpl.
                        apply eq_map_refl.
                  ----- destruct F; simpl in *; subst; eauto.
                  ----- match goal with
                        | [ H : TypeValid _ _ |- _ ] =>
                          inversion H; subst
                        end.
                        constructor; destruct F; simpl in *; subst; eauto.
                        replace_heaptypevalid_parts label ret size type location.
                        apply HeapTypeValid_linear.
                        constructor.
                        simpl in *.

                        eapply Forall_combine_ReplaceAtIdx.
                        ------- match goal with
                                | [ H : HeapTypeValid _ _ |- _ ] =>
                                  inversion H
                                end.
                        
                                subst; simpl in *; eauto.
                        ------- eauto.
                        ------- eauto.
                        ------- match goal with
                                | [ H : sizeOfType _ _ = Some ?SZ |- _ ] => exists SZ
                                end.
                                simpl in *.
                                split; [ eauto | ].
                                match goal with
                                | [ H : HeapTypeValid _ _ |- _ ] =>
                                  inversion H
                                end.
                                subst; simpl in *.
                                match goal with
                                | [ H : HeapTypeValid _ (StructType (combine ?L1 ?L2)),
                                    H' : Forall _ (combine ?L1 ?L2),
                                    H'' : nth_error ?L2 _ = _,
                                    H''' : length ?L1 = length ?L2 |- _ ] =>
                                  specialize (Forall_combine_nth_error _ _ _ _ _ H''' H' H'')
                                end.
                                intro Hold.
                                destructAll; simpl in *.
                                split; [ eauto | ].
                                split; eauto.
                                replace_typevalid_parts label ret size type location.
                                apply TypeValid_linear.
                                eauto.
             ---- destruct F; subst; simpl in *; solve_lcvs.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- do 3 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- rewrite (eq_sym Hinst); eauto.
      -- split; eauto. rewrite Hunr.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans; [ eapply LCSizeEqual_trans | ].
         all: apply LCEffEqual_LCSizeEqual; eauto.
     
    - (* StructSwap *)
      match goal with
      | [ H : context[[Val ?V1; Val ?V2; ?C]] |- _ ] =>
        replace [Val V1; Val V2; C] with ([Val V1] ++ [Val V2; C]) in H by ltac:(simpl; congruence)
      end.
      specialize (composition_typing _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val ?V; ?C] _ _ |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H by ltac:(simpl; congruence);
        specialize (composition_typing _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hb.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [StructSwap _] _ _ |- _ ] =>
        show_tlvs H; apply StructSwap_HasTypeInstruction in H
      end.
      simpl in *.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D; ?E] |- _ ] =>
        assert (Heq : A = C ++ [D] /\ B = E)
      end.
      { eapply app_inj_tail_iff.
        rewrite app_assoc_reverse.
        auto. }
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ ?D ++ [?E] |- _ ] =>
        assert (Heq3 : A = C ++ D /\ B = E)
      end.
      { eapply app_inj_tail_iff.
        rewrite app_assoc_reverse.
        auto. }
      destructAll.
      match goal with
      | [ H : HasTypeStore _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : HasTypeMeminst _ _ _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      derive_mappings f_lin f_unr.
      unfold get_mem in *.
      match goal with
      | [ H : get _ _ _ = Some _ |- _ ] =>
        specialize (get_implies_in_to_list _ _ _ _ _ H)
      end.
      intros; destructAll.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        specialize (nth_error_In _ _ H)
      end.
      intros.
      match goal with
      | [ H : In (?L, ?HV, ?SZ) (M.to_list ?M ?MEM),
          H' : HasTypeValue _ _ (Ref (LocP ?L ?M))
                            (QualT (RefT _ _ ?HT) _) |- _ ] =>
        assert (Hheap0 :
                  NoCapsHeapType [] HT = true /\
                  (if qualconstr_eq_dec M Linear then
                     get_heaptype L (LinTyp Sh) = Some HT \/
                     get_heaptype L (LinTyp Sp) = Some HT else
                     get_heaptype L (UnrTyp (f_unr (L, HV, SZ))) = Some HT) /\
                  HasHeapType
                    (if qualconstr_eq_dec M Linear then
                       f_lin (L, HV, SZ) else
                       f_unr (L, HV, SZ))
                    empty_Function_Ctx HV HT /\
                  RoomForStrongUpdates SZ HT /\
                  HeapTypeValid empty_Function_Ctx HT)
      end.
      { destruct m; simpl in *; subst.
        all:
          match goal with
          | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
            inversion H; subst; simpl in *
          end.
        all:
          match goal with
          | [ H : In ?TPL (M.to_list ?M ?MEM),
              H' : forall _, In _ (M.to_list ?M ?MEM) -> _ |- _ ] =>
            specialize (H' TPL H)
          end.
        all: simpl in *.
        all: destructAll.
        1:
          match goal with
          | [ H : get_heaptype ?L _ = Some ?HT1,
              H' : get_heaptype ?L _ = Some ?HT2 |- _ ] =>
            assert (Heq_typ : HT1 = HT2)
          end.
        { match goal with
          | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?SH,
              H' : get_heaptype _ (UnrTyp (?F ?TPL)) = _ |- _ ] =>
            assert (Hunr_eq : UnrTyp (F TPL) = UnrTyp SH);
              [ eapply proj1;
                eapply SplitStoreTypings_eq_typs2;
                [ exact H | ] | ]
          end.
          { apply in_or_app; right.
            apply in_map.
            auto. }
          match goal with
          | [ H : get_heaptype ?L ?UN1 = Some ?HT1,
              H' : get_heaptype ?L ?UN2 = Some ?HT2 |- _ ] =>
            assert (Hunr_eq2 : UN1 = UN2);
            [ | rewrite Hunr_eq2 in H;
                rewrite H in H';
                inversion H'; subst; simpl in * ]
          end.
          { match goal with
            | [ H : UnrTyp ?X = UnrTyp _ |- UnrTyp ?X = _ ] =>
              rewrite H
            end.
            solve_inst_or_unr_typ_eq. }
          auto. }          
        2:
          match goal with
          | [ H : get_heaptype ?L _ = Some ?T \/
                  get_heaptype ?L _ = Some ?T,
              H' : HasTypeValue
                     _ _ (Ref (LocP ?L _))
                     (QualT
                        (RefT _ _ (StructType ?TPL)) _) |- _ ] =>
            assert (Htyp_eq : T = StructType TPL)
          end.
        2:{
          apply eq_sym.
          eapply EqualTyps_StructLinInstruction.
          5: eauto.
          3: eauto.
          2: eauto.
          all: eauto.
        }
        all: subst.
        all: split; [ eauto | ].
        all: split; [ | eauto ].
        - auto.
        - right.
          match goal with
          | [ H : SplitStoreTypings (?S1 :: _ ++ _) ?SP,
              H' : SplitStoreTypings [?SPP; _] ?S1
              |- context[?SP] ] =>
            eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1));
            [ eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=SPP));
              [ | | exact H' ]; [ | constructor; auto ]
              | | exact H ]; [ | constructor; auto ]
          end.
          unfold eq_map in *.
          match goal with
          | [ H : context[get_heaptype _ ?LT] |- context[?LT] ] =>
            rewrite H
          end.
          unfold get_heaptype.
          rewrite M.gss; auto. }
      destructAll.
      match goal with
      | [ H : HasHeapType _ _ (Struct _) (StructType _) |- _ ] =>
        inversion H; subst; simpl in *
      end.
      match goal with
      | [ H : (_, _) = split (combine _ _) |- _ ] =>
        rewrite combine_split in H; [ | auto ];
        inversion H; subst; simpl in *
      end.
      destructAll.

      match goal with
      | [ H : ReplaceAtIdx _ _ _ = Some (_, ?T),
          H' : nth_error ?VIS ?IDX = Some ?VO,
          H'' : Forall3 _ ?SS0 _ _
          |- context[Val ?VO] ] =>
        assert (Hheap1 : exists Svo Sh_rest,
                   nth_error SS0 IDX = Some Svo /\
                   SplitStoreTypings [Svo; Sh_rest] Sh /\
                   HasTypeValue Svo empty_Function_Ctx VO T)
      end.
      { match goal with
        | [ H : ReplaceAtIdx _ _ _ = Some _ |- _ ] =>
          specialize (ReplaceAtIdx_old_nth_error H)
        end.
        intros.
        match goal with
        | [ H : Forall3 _ _ ?L2 ?L3,
            H' : nth_error ?L2 ?IDX = Some _,
            H'' : nth_error ?L3 ?IDX = Some _ |- _ ] =>
          specialize (forall3_nth_error_args23 H H' H'')
        end.
        intros; destructAll; simpl.

        match goal with
        | [ H : nth_error ?SS _ = Some ?S,
            H' : SplitStoreTypings ?SS (if _ then _ else _),
            H'' : SplitStoreTypings (map _ _ ++ map _ _) ?SH |- _ ] =>
          let H0 := fresh "H" in
          assert (H0 : exists S'', SplitStoreTypings [S; S''] SH);
          [ eapply SplitStoreTypings_extract_nested;
            [ eapply nth_error_In; eauto | | | exact H'' ];
            [ eauto | ] | ]
        end.
        { match goal with
          | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
            destruct M; subst; simpl in *
          end.
          - apply in_or_app; right.
            apply in_map.
            auto.
          - apply in_or_app; left.
            apply in_map.
            auto. }
          
        destructAll.
        do 2 eexists; eauto. }
        
      destruct Hheap1 as [Svo [Sh_rest]].
      destructAll.
      match goal with
      | [ H : context[set_nth _ _ ?V],
          H' : HasTypeValue ?SV _ ?V _ |-
          context[combine ?TAUSP ?SZSP] ] =>
        assert (Hheap2 : exists Sref' Sstack' Sp' Sh' S',
                  SplitStoreTypings [Sp'; Sh'] S' /\
                  SplitStoreTypings [SV; Sh_rest] Sh' /\
                  SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' /\
                  SplitStoreTypings [Sref'; Svo] Sstack' /\
                  if qualconstr_eq_dec m Linear then
                      Sref' = {|InstTyp:=InstTyp Sstack; UnrTyp:=UnrTyp Sstack; LinTyp:=(M.add (N.succ_pos l1) (StructType (combine TAUSP SZSP)) (M.empty HeapType))|}
                    else
                      Sref' = empty_LinTyp Sstack)
      end.
      { match goal with
        | [ H : HasTypeStore _ ?SH ?SP,
            H' : SplitStoreTypings [?SP; ?SH] ?S,
            H'' : SplitStoreTypings [?SVO; ?SHR] ?SH |- _ ] =>
          let H0 := fresh "H" in
          assert (H0 : SplitStoreTypings [SH; SP] S);
          [ | specialize (SplitStoreTypings_move_one H0 H'') ]
        end.
        { eapply SplitStoreTypings_permut; [ | eauto ].
          constructor. }
        intros; destructAll.

        match goal with
        | [ H : SplitStoreTypings [?SH] ?S1,
            H' : SplitStoreTypings [?S1; ?S2] ?S |- _ ] =>
          specialize (SplitStoreTypings_trans_gen H H');
          clear H
        end.
        simpl; intros.
        
        match goal with
        | [ H0 : SplitStoreTypings [?SVO; ?SP] ?S2,
            H1 : SplitStoreTypings [?S1; ?S2] ?SW,
            H2 : SplitStoreTypings [?SH; ?SP] ?SW,
            H3 : HasTypeStore _ ?SH ?SP,
            H4 : SplitStoreTypings (?SST :: ?SS1 ++ ?SS2) ?SP,
            H5 : SplitStoreTypings [?SB1; ?SB2] ?SST,
            H6 : SplitStoreTypings [?SBB1; ?SBB2] ?SB2 |- _ ] =>
          let H := fresh "H" in
          let H' := fresh "H" in
          assert (H : SplitStoreTypings [SP; SVO] S2);
          [ eapply SplitStoreTypings_permut; [ | eauto ];
            constructor | ];
          assert (H' : SplitStoreTypings [SB2; SB1] SST);
          [ eapply SplitStoreTypings_permut; [ | eauto ];
            constructor | ];
          let H'' := fresh "H" in
          specialize (SplitStoreTypings_trans_gen H' H4); intro H'';
          let H''' := fresh "H" in
          specialize (SplitStoreTypings_trans_gen H6 H''); intro H''';
          let H'''' := fresh "H" in
          specialize (SplitStoreTypings_trans_gen H''' H);
          simpl; intro H'''';
          let H''''' := fresh "H" in
          assert (H''''' : SplitStoreTypings [S2; S1] SW);
          [ eapply SplitStoreTypings_permut; [ | eauto ];
            constructor | ];
          specialize (SplitStoreTypings_move_one H''''' H'''')
        end.
        intros; destructAll.

        match goal with
        | [ H : SplitStoreTypings (?S1 :: ?A :: (?B ++ ?C) ++ ?D) ?S,
            H' : M.is_empty (LinTyp ?S1) = true |- _ ] =>
          let H'' := fresh "H" in
          assert (H'' : nth_error (S1 :: A :: (B ++ C) ++ D) 0 = Some S1) by ltac:(simpl; auto);
          specialize (SplitStoreTypings_remove_empty H H'' H')
        end.
        simpl; intros.

        match goal with
        | [ H : SplitStoreTypings (?S1 :: (?SS1 ++ ?SS2) ++ [?S2])
                                  ?S |- _ ] =>
          let H' := fresh "H" in
          assert (H' : SplitStoreTypings ([S1; S2] ++ (SS1 ++ SS2)) S);
          [ eapply SplitStoreTypings_permut; [ | exact H ]
          | specialize (SplitStoreTypings_split H') ]
        end.
        { constructor.
          apply Permutation.Permutation_app_comm. }
        intros; destructAll.

        match goal with
        | [ |- context[if ?B then _ = ?S1 else _ = ?S2] ] =>
          remember (if B then S1 else S2) as Sref';
          exists Sref'
        end.
        
        match goal with
        | [ H : SplitStoreTypings [?S1; ?S2] _,
            H' : HasTypeValue ?S1 _ (Ref (LocP _ _)) _,
            H'' : HasTypeValue ?S2 _ _ _ |- _ ] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          let H3 := fresh "H" in
          assert (H1 : InstTyp S1 = InstTyp Sref');
          [ | assert (H2 : UnrTyp S1 = UnrTyp Sref');
              [ | assert (H3 : (Dom_ht (LinTyp S1)) <--> (Dom_ht (LinTyp Sref')));
                  [ | specialize (SplitStoreTypings_change_vals H H1 H2 H3) ] ] ]
        end.
        1-2: unfold empty_LinTyp in *.
        1-2: subst.
        1-2:
          match goal with
          | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
            destruct M; subst; simpl in *; auto
          end.
        1-4: destruct Sstack; simpl in *.
        1-4:
          match goal with
          | [ H : SplitStoreTypings
                    [?S1; _]
                    {| InstTyp := _; LinTyp := _; UnrTyp := _ |}
              |- context[?S1] ] =>
            inversion H; subst; simpl in *
          end.
        1-4:
          match goal with
          | [ H : Forall _ [?S1; _] |- context[?S1] ] =>
            inversion H; subst; simpl in *
          end.
        1-4: destructAll; eauto.
        { match goal with
          | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
            destruct M; subst; simpl in *
          end.
          - apply eq_map_Dom_ht.
            apply eq_map_empty; [ | unfold empty_LinTyp; destruct Sstack; simpl; auto ].
            eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
            -- match goal with
               | [ H : HasTypeValue _ _ _ (QualT _ ?Q)
                   |- context[?Q] ] =>
                 inversion H; subst; simpl in *
               end.
               auto.
            -- destruct F; subst; simpl in *.
               unfold Function_Ctx_empty in *.
               simpl in *; destructAll; auto.
          - match goal with
            | [ H : HasTypeValue ?S _ _ _ |- context[?S] ] =>
              inversion H; subst; simpl in *
            end.
            eapply Same_set_trans; [ apply eq_map_Dom_ht; eauto | ].
            apply Dom_ht_one_loc. }
	    intros; destructAll.

        match goal with
        | [ H : SplitStoreTypings [_; _] ?S2,
            H' : InstTyp ?S1 = InstTyp ?S2,
            H'' : UnrTyp ?S1 = UnrTyp ?S2,
            H''' : Dom_ht (LinTyp ?S1) <--> Dom_ht (LinTyp ?S2),
            H'''' : SplitStoreTypings (?S1 :: _ ++ _) _ |- _ ] =>
          specialize (SplitStoreTypings_change_vals H'''' H' H'' H''')
        end.
        intros; destructAll.

        match goal with
        | [ H : SplitStoreTypings (_ :: _ ++ _) ?S2,
            H' : InstTyp ?S1 = InstTyp ?S2,
            H'' : UnrTyp ?S1 = UnrTyp ?S2,
            H''' : Dom_ht (LinTyp ?S1) <--> Dom_ht (LinTyp ?S2),
            H'''' : SplitStoreTypings [?S1; _] _ |- _ ] =>
          specialize (SplitStoreTypings_change_vals H'''' H' H'' H''')
        end.
        intros; destructAll.

        do 4 eexists.
        split; [ | split; [ eauto | ] ]; [ eauto | ].
        split; [ eauto | ].
        split; [ eauto | ].
        match goal with
        | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
          destruct M; subst; simpl in *; auto
        end. }

      destruct Hheap2 as [Sref' [Sstack' [Sp' [Sh' [S']]]]].
      destructAll.

      assert (Heq_inst_unrSp : InstTyp Sp = InstTyp Sp' /\ UnrTyp Sp = UnrTyp Sp') by ltac:(split; solve_inst_or_unr_typ_eq).
      destructAll.

      exists Sp', Sh', Sstack', Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- econstructor; eauto.
         --- match goal with
             | [ H : ?A = ?B |- context[?B] ] =>
               rewrite (eq_sym H); eauto
             end.
             match goal with
             | [ H : update_mem ?S _ _ _ = Some ?ST |- _ ] =>
               assert (Hinst_st' : inst S = inst ST);
               [ destruct S; simpl in *;
                 unfold update_mem in H; simpl in H;
                 match type of H with
                 | context[set ?A ?B ?C ?D] => destruct (set A B C D)
                 end;
                 inversion H; simpl; auto | ]
             end.
             match goal with
             | [ H : update_mem ?S _ _ _ = Some _,
                 H' : if qualconstr_eq_dec ?M _ then ?SP = _ else _ = ?SP |- _ ] =>
               assert (Hinst_s' : inst S = inst SP);
               [ destruct M; simpl in *; subst; auto | ]
             end.
             { match goal with
               | [ |- _ = _ (_ _ _ ?A ?B) ] =>
                 unfold update_out_set;
                 destruct (L.has_urn_ptr_HeapValue B);
                 destruct (L.has_urn_ptr_HeapValue A); simpl; auto
               end. }
             rewrite (eq_sym Hinst_s').
             inversion Hst.
             assert (Hinst2 : InstTyp S = InstTyp S') by solve_inst_or_unr_typ_eq.
             rewrite (eq_sym Hinst2).
             auto.
         --- 
           { inversion Hst; subst; simpl in *.
             match goal with
             | [ H : HasTypeMeminst _ _ _ |- _ ] =>
               inversion H; subst; simpl in *
             end.

             unfold update_mem in *.
             match goal with
             | [ H : context[set ?A ?B ?C ?D] |- _ ] =>
               remember (set A B C D) as o;
               repeat match goal with
               | [ H : context[o] |- _ ] => revert H
               end
             end.
             case o; [ | intros H' H''; inversion H'' ].
             intros t H' H''.
             inversion H''; subst; simpl in *.

             match goal with
             | [ H : context[?SP = update_out_set _ _ _ _] |- _ ] =>
               assert (Hm : (meminst SP) = t)
             end.
             { destruct m; simpl in *; subst.
               - simpl; auto.
               - unfold update_out_set.
                 repeat match goal with
                        | [ |- meminst (if ?B then _ else _) = _ ] =>
                          case B
                        end.
                 all: simpl; auto. }

             assert (Hlemma : forall l t,
                        (l =? l1)%N = false \/
                        is_linear m = false ->
                        get_heaptype l (LinTyp Sh) = Some t \/
                        get_heaptype l (LinTyp Sp) = Some t ->
                        get_heaptype l (LinTyp Sh') = Some t \/
                        get_heaptype l (LinTyp Sp') = Some t).
             { intros.
               match goal with
               | [ H : get_heaptype _ _ = _ \/ _ |- _ ] =>
                 inversion H; subst; simpl in *
               end.
               - match goal with
                 | [ H : get_heaptype ?L (LinTyp ?S) = _,
                     H' : SplitStoreTypings [_; _] ?S |-
                     context[?L] ] =>
                   specialize (SplitStoreTypings_inv H H')
                 end.
                 intros; destructAll.
                 match goal with
                 | [ H : In _ [_; _] |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 -- right.
                    unfold Ensembles.In.
                    match goal with
                    | [ H : get_heaptype ?L _ = Some ?HT,
                        H' : SplitStoreTypings (?S :: _ ++ _) ?SP,
                        H'' : SplitStoreTypings [_; ?S2] ?S
                        |- context[get_heaptype ?L (LinTyp ?SP)] ] =>
                      eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ]; [ | constructor; auto ];
                      eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S2)); [ | | exact H'' ]; [ | constructor 2; constructor; auto ]
                    end.
                    auto.
                 -- left.
                    match goal with
                    | [ H : _ \/ False |- _ ] =>
                      case H; [ | intros; exfalso; auto ]
                    end.
                    intros; subst.
                    unfold Ensembles.In.
                    eapply SplitStoreTypings_get_heaptype_LinTyp; [ eauto | | eauto ].
                    constructor 2; constructor; auto.
               - match goal with
                 | [ H : get_heaptype ?L (LinTyp ?S) = _,
                     H' : SplitStoreTypings (_ :: _ ++ _) ?S |-
                     context[?L] ] =>
                   specialize (SplitStoreTypings_inv H H')
                 end.
                 intros; destructAll.
                 match goal with
                 | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 -- match goal with
                    | [ H : get_heaptype ?L (LinTyp ?S) = _,
                        H' : SplitStoreTypings [_; _] ?S |-
                        context[?L] ] =>
                      specialize (SplitStoreTypings_inv H H')
                    end.
                    intros; destructAll.
                    match goal with
                    | [ H : In _ [_; _] |- _ ] =>
                      inversion H; subst; simpl in *
                    end.
                    --- match goal with
                        | [ H : get_heaptype ?L (LinTyp ?S) = _,
                            H' : HasTypeValue ?S _ _ _
                            |- context[?L] ] =>
                          inversion H'; subst; simpl in *
                        end.
                        ---- match goal with
                             | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                 H' : get_heaptype _ (LinTyp ?S) = Some _
                                 |- _ ] =>
                               rewrite get_heaptype_empty in H'; [ | exact H ]; inversion H'
                             end.
                        ---- match goal with
                             | [ H : eq_map (LinTyp _) (map_util.M.add (N.succ_pos ?L) _ _)
                                 |- context[get_heaptype ?L2 _] ] =>
                               let H' := fresh "H" in
                               assert (H' : L = L2 \/ L <> L2) by apply eq_dec_N;
                               case H'; intros; subst
                             end.
                             ----- match goal with
                                   | [ H : (?A =? ?A)%N = false \/ true = false |- _ ] =>
                                     rewrite N.eqb_refl in H;
                                     case H;
                                     let H' := fresh "H" in
                                     intro H'; inversion H'
                                   end.
                             ----- match goal with
                                   | [ H : get_heaptype ?L (LinTyp ?S) = Some _,
                                       H' : eq_map (LinTyp ?S) _ |- _ ] =>
                                     unfold eq_map in H';
                                     rewrite H' in H;
                                     unfold get_heaptype in H;
                                     rewrite M.gso in H
                                   end.
                                   2:{
                                     intro.
                                     match goal with
                                     | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                       let H' := fresh "H" in
                                       assert (H' : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2));
                                       [ rewrite H; auto | ];
                                       repeat rewrite N.pos_pred_succ in H'
                                     end.
                                     eauto.
                                   } 
                                   rewrite M.gempty in *.
                                   match goal with
                                   | [ H : None = Some _ |- _ ] => inversion H
                                   end.
                    --- match goal with
                        | [ H : _ \/ False |- _ ] =>
                          case H;
                          [ | intros; exfalso; auto ]
                        end.
                        intros; subst.
                        match goal with
                        | [ H : SplitStoreTypings [?S1; _] ?S,
                            H' : SplitStoreTypings [_; ?S] ?S0,
                            H'' : SplitStoreTypings (?S0 :: _ ++ _) _,
                            H''' : HasTypeValue ?S1 _ _ _,
                            H'''' : get_heaptype _ (LinTyp ?S) = Some _
                            |- _ ] =>
                          specialize (SplitStoreTypings_inv H'''' H)
                        end.
                        intros; destructAll.
                        match goal with
                        | [ H : In _ [_; _] |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        ---- left.
                             unfold Ensembles.In.
                             match goal with
                             | [ H : SplitStoreTypings [?S; _] ?SH
                                 |- context[?SH] ] =>
                               eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                             end.
                             eauto.
                        ---- match goal with
                             | [ H : _ \/ False |- _ ] =>
                               case H;
                               [ | intros; exfalso; auto ]
                             end.
                             intros; subst.
                             match goal with
                             | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                 H' : get_heaptype _ (LinTyp ?S) = Some _
                                 |- _ ] =>
                               rewrite (get_heaptype_empty _ _ H) in H';
                               inversion H'
                             end.
                 -- right.
                    unfold Ensembles.In.
                    match goal with
                    | [ H : In ?S (?Ss1 ++ ?Ss2),
                        H' : SplitStoreTypings (_ :: ?Ss1 ++ ?Ss2) ?SP
                        |- context[?SP] ] =>
                      eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ]; [ | constructor 2; auto ]
                    end.
                    eauto. }

             match goal with
             | [ |- HasTypeMeminst _ _ ?MEM ] =>
               assert (Hsubgoal : exists S_lin' S_unr',
                          Forall2
                            (fun (S0 : StoreTyping) '(loc, hv, len) =>
                               exists ht : HeapType,
                                 NoCapsHeapType [] ht = true /\
                                 (get_heaptype loc (LinTyp Sh') = Some ht \/
                                  get_heaptype loc (LinTyp Sp') = Some ht) /\
                                 HasHeapType S0 empty_Function_Ctx hv ht /\
                                 RoomForStrongUpdates len ht /\
                                 HeapTypeValid empty_Function_Ctx ht) S_lin'
                            (M.to_list Linear MEM) /\
                          Forall2
                            (fun (S0 : StoreTyping) '(loc, hv, len) =>
                               exists ht : HeapType,
                                 NoCapsHeapType [] ht = true /\
                                 get_heaptype loc (UnrTyp S0) = Some ht /\
                                 HasHeapType S0 empty_Function_Ctx hv ht /\
                                 RoomForStrongUpdates len ht /\
                                 HeapTypeValid empty_Function_Ctx ht) S_unr'
                            (M.to_list Unrestricted MEM) /\
                          Forall
                            (fun S' : StoreTyping =>
                               InstTyp Sh' = InstTyp S' /\ UnrTyp Sh' = UnrTyp S')
                            (S_lin' ++ S_unr') /\
                          SplitHeapTypings (map LinTyp (S_lin' ++ S_unr')) (LinTyp Sh'))
             end.
             { match goal with
               | [ H : HasTypeValue ?SV _ ?V _, H' : Some _ = set _ _ _ (Struct (set_nth ?VIS ?IDX ?V)), H'' : Forall3 _ ?SS ?VIS _ |- _ ] =>
                 assert (Hcombine : exists S', SplitStoreTypings ((set_nth SS IDX SV)) S')
               end.
               { match goal with
                 | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?SH
                     |- context[set_nth _ _ ?S1] ] =>
                   let H' := fresh "H" in
                   assert (H' : exists S', SplitStoreTypings [S1; SH] S')
                 end.
                 { match goal with
                   | [ H : HasTypeStore _ ?SH ?SP,
                       H' : SplitStoreTypings (?SST :: ?SS1 ++ ?SS2) ?SP,
                       H'' : SplitStoreTypings [?S1; ?S2] ?SST,
                       H''' : SplitStoreTypings [?SB1; ?SB2] ?S2,
                       H'''' : SplitStoreTypings [?SP; ?SH] _ |- _ ] =>
                     specialize (SplitStoreTypings_trans_gen H'' H');
                     let H0 := fresh "H" in
                     intro H0;
                     let H''''' := fresh "H" in
                     assert (H''''' : SplitStoreTypings ([S2; S1] ++ SS1 ++ SS2) SP);
                     [ eapply SplitStoreTypings_permut; [ | exact H0 ];
                       constructor | ];
                     specialize (SplitStoreTypings_trans_gen H''' H''''');
                     let H1 := fresh "H" in
                     intro H1;
                     specialize (SplitStoreTypings_move_one H'''' H1)
                   end.
                   intros; destructAll.
                   eexists; eauto. }
                 destructAll.
                 
                 eapply SplitStoreTypings_safe_set_nth;
                   [ eauto | |
                     match goal with
                     | [ H : SplitStoreTypings
                               (map _ _ ++ map _ _) _ |- _ ] =>
                       exact H
                     end | ];
                   [ | eauto ].
                 match goal with
                 | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
                   destruct M; subst; simpl in *
                 end.
                 - apply in_or_app; right.
                   apply in_map.
                   auto.
                 - apply in_or_app; left.
                   apply in_map.
                   auto. }
               destruct Hcombine as [Snew].
               
               match goal with
               | [ H : get ?L ?M ?MEM1 = Some (?HV, ?SZ) |- _ ] =>
                 remember (map (fun '(loc, hv, len) => if (andb (is_linear M) (BinNatDef.N.eqb loc L)) then Snew else f_lin (loc, hv, len)) (M.to_list Linear t)) as S_lin';
                 remember (map (fun '(loc, hv, len) => if (andb (negb (is_linear M)) (BinNatDef.N.eqb loc L)) then Snew else f_unr (loc, hv, len)) (M.to_list Unrestricted t)) as S_unr'
               end.
               simpl in *.

               match goal with
               | [ H : Forall2 _ _ (M.to_list Unrestricted (meminst ?S)),
                   H' : Forall2 _ _ (M.to_list Linear (meminst ?S))
                   |- _ ] =>
                 rewrite forall2_map in H;
                 rewrite forall2_map in H';
                 assert (Hperm :
                           if qualconstr_eq_dec m Linear
                           then Permutation.Permutation (M.to_list Unrestricted t) (M.to_list Unrestricted (meminst S))
                           else Permutation.Permutation (M.to_list Linear t) (M.to_list Linear (meminst S)))
               end.
               { destruct m; subst; simpl in *.
                 all: apply Permutation.NoDup_Permutation;
                   [ apply to_list_NoDup | apply to_list_NoDup | ].
                 all: let x := fresh "x" in
                      intro x; destruct x as [[curL curHV] curSz].
                 all: constructor.
                 all: let H := fresh "H" in
                      intro H; apply In_nth_error in H.
                 all: destructAll.
                 all:
                   match goal with
                   | [ H : nth_error (M.to_list ?M _) _ = _ |-
                       context[M.to_list ?M _] ] =>
                     apply in_to_list_implies_get in H
                   end.
                 all:
                   match goal with
                   | [ |- context[M.to_list ?M _] ] =>
                     assert (Hneq : if qualconstr_eq_dec M Linear
                                    then Unrestricted <> Linear
                                    else Linear <> Unrestricted);
                     [ simpl;
                       let H := fresh "H" in intro H; inversion H
                     | simpl in Hneq ]
                   end.
                 all:
                   match goal with
                   | [ H : Some _ = set _ ?M _ _,
                       H' : ?M <> ?M2,
                       H'' : get ?L ?M2 _ = _ |- _ ] =>
                     specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H) H')
                   end.
                 all: intros.
                 all:
                   match goal with
                   | [ H : ?A = Some _, H' : ?B = ?A |- _ ] =>
                     rewrite H in H';
                     apply get_implies_in_to_list in H'
                   | [ H : ?A = Some _, H' : ?A = ?B |- _ ] =>
                     rewrite H' in H;
                     apply get_implies_in_to_list in H
                   end.
                 all: destructAll.
                 all: eapply nth_error_In; eauto. }

               exists S_lin', S_unr'; subst.
               split; [ | split; [ | split ] ].
               - destruct m; subst; simpl in *.
                 -- rewrite forall2_map.
                    let x := fresh "x" in
                    intro x; destruct x as [[curL curHV] curSz].
                    let H := fresh "H" in
                    intro H;
                    match goal with
                    | [ H' : Permutation.Permutation _ _ |- _ ] =>
                      specialize (Permutation.Permutation_in _ H' H)
                    end.
                    intros.
                    match goal with
                    | [ H : forall _, In _ ?LST -> _,
                        H' : In _ ?LST |- _ ] =>
                      specialize (H _ H');
                      simpl in H;
                      let ht := fresh "ht" in
                      destruct H as [ht];
                      exists ht
                    end.
                    destructAll.
                    split; [ eauto | ].
                    split; [ | eauto ].
                    apply Hlemma; eauto.
                 -- eapply StructLinear_WellTyped.
                    1,3-13,15-20,23: eauto.
                    --- apply eq_sym; auto.
                    --- destruct F; subst; simpl in *.
                        unfold Function_Ctx_empty in *; auto.
                    --- let x := fresh "x" in
                        intro x; destruct x as [[curL curHV] curSz].
                        auto.
                    --- match goal with
                        | [ H' : SplitStoreTypings (?S :: ?S1 ++ ?S2) ?SP |- context[?SP] ] =>
                          eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H' ]; [ | constructor; auto ]
                        end.
                        match goal with
                        | [ H' : SplitStoreTypings [?S1; ?S2] ?SP |- context[?SP] ] =>
                          eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); [ | | exact H' ]; [ | constructor; auto ]
                        end.
                        subst.
                        simpl.
                        unfold get_heaptype.
                        rewrite M.gss; auto.
               - destruct m; subst; simpl in *.
                 -- rewrite forall2_map.
                    let x := fresh "x" in
                    intro x; destruct x as [[curL curHV] curSz].
                    intros.
                    match goal with
                    | [ |- context[(?A =? ?B)%N] ] =>
                      remember ((A =? B)%N) as locb;
                      revert Heqlocb;
                      case locb; intros
                    end.
                    --- match goal with
                        | [ H : true = (?A =? ?B)%N |- _ ] =>
                          assert (Hloc_eq : A = B); [ | subst ]
                        end.
                        { rewrite (iff_sym (N.eqb_eq _ _)); eauto. }
                        match goal with
                        | [ H : In _ (M.to_list _ ?MEM2),
                            H' : Some ?MEM2 = _ |- _ ] =>
                          apply In_nth_error in H;
                          let x := fresh "x" in
                          destruct H as [x H];
                          apply in_to_list_implies_get in H
                        end.
                        match goal with
                        | [ H : Some _ = set _ _ _ _ |- _ ] =>
                          specialize (get_set_same _ _ _ _ _ (eq_sym H))
                        end.
                        intros; destructAll.
                        match goal with
                        | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                          rewrite H in H'; inversion H'
                        end.
                        subst; simpl in *.

                        match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        match goal with
                        | [ H : _ \/ ?A = ?B |- _ ] =>
                          assert (Heq_typ : A = B);
                          [ case H; eauto | subst ]
                        end.
                        { intros.
                          destruct F; subst; simpl in *.
                          unfold Function_Ctx_empty in *.
                          simpl in *; destructAll; subst.
                          exfalso; eapply QualLeq_Const_False.
                          eapply QualLeq_Trans; eauto. }
                        match goal with
                        | [ H : ReplaceAtIdx _ _ _ = Some _ |- _ ] =>
                          specialize (ReplaceAtIdx_no_change H)
                        end.
                        intros; subst.
                        
                        match goal with
                        | [ H : get_heaptype _ (UnrTyp _) = Some ?HT |- _ ] =>
                          exists HT
                        end.
                        split; [ eauto | ].
                        split; [ | split; [ | split; [ | eauto ] ] ].
                        ---- use_StructLinear_SplitStoreTypings_eq_typs2.
                             let H := fresh "H" in
                             let H1 := fresh "H" in
                             intro H;
                             destruct H as [H H1];
                             rewrite (eq_sym H).
                             match goal with
                             | [ H : M.is_empty (LinTyp ?S) = _,
                                 H' : get_heaptype _ (UnrTyp ?S) = Some ?HT
                                 |- get_heaptype _ (UnrTyp ?S2) = Some ?HT ] =>
                               let H0 := fresh "H" in
                               assert (H0 : UnrTyp S = UnrTyp S2);
	                           [ | rewrite (eq_sym H0) ]
                             end.
                             { solve_inst_or_unr_typ_eq. }
                             auto.
                        ---- eapply HasHeapType_Struct_replace; eauto.
                             destruct F; subst; simpl in *.
                             unfold Function_Ctx_empty in *.
                             simpl in *.
                             auto.
                        ---- match goal with
                             | [ H : get ?L ?M ?MEM = Some _,
                                 H' : Some _ = set ?L ?M ?MEM _ |- _ ] =>
                               specialize (get_set_same_size _ _ _ _ _ _ _ H (eq_sym H'))
                             end.
                             intros.
                             match goal with
                             | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                               rewrite H in H'; inversion H'
                             end.
                             subst; simpl in *; auto.
                    --- match goal with
                        | [ H : Some ?MEM2 = set _ _ _ _,
                            H' : In (?L, _, _) (M.to_list _ ?MEM2) |- _ ] =>
                          apply In_nth_error in H';
                          let x := fresh "x" in
                          destruct H' as [x H' ];
                          apply in_to_list_implies_get in H';
                          specialize (get_set_other_loc _ _ _ L _ _ (eq_sym H))
                        end.
                        match goal with
                        | [ |- (?A -> _) -> _ ] =>
                          let H := fresh "H" in
                          let H' := fresh "H" in
                          assert (H : A);
                          [ | intro H'; specialize (H' H) ]
                        end.
                        { rewrite (iff_sym (OrdersEx.N_as_OT.eqb_neq _ _)).
                          rewrite N.eqb_sym; eauto. }
                        match goal with
                        | [ H : ?A = ?B, H' : ?B = Some _ |- _ ] =>
                          rewrite H' in H;
                          apply get_implies_in_to_list in H;
                          let x := fresh "x" in
                          destruct H as [x H];
                          apply nth_error_In in H
                        end.
                        match goal with
                        | [ H : forall _, In _ ?LST -> _,
                            H' : In ?TPL ?LST |- _ ] =>
                          specialize (H _ H')
                        end.
                        simpl in *; auto.
                 -- rewrite forall2_map.
                    let x := fresh "x" in
                    intro x; destruct x as [[curL curHV] curSz].
                    let H := fresh "H" in
                    intro H;
                    match goal with
                    | [ H' : Permutation.Permutation _ _ |- _ ] =>
                      specialize (Permutation.Permutation_in _ H' H)
                    end.
                    intros.
                    match goal with
                    | [ H : forall _, In _ ?LST -> _,
                        H' : In _ ?LST |- _ ] =>
                      specialize (H _ H');
                      simpl in H;
                      let ht := fresh "ht" in
                      destruct H as [ht];
                      exists ht
                    end.
                    eauto.
               - match goal with
                 | [ H : SplitStoreTypings (set_nth _ _ _) ?SNEW
                     |- context[InstTyp ?SH = _ /\ UnrTyp ?SH = _] ] =>
                   let H' := fresh "H" in
                   assert (H' : InstTyp SH = InstTyp SNEW /\ UnrTyp SH = UnrTyp SNEW)
                 end.
                 { use_StructLinear_SplitStoreTypings_eq_typs2.
                   intros; destructAll; split.
                   - eapply eq_trans; [ | eauto ].
                     solve_inst_or_unr_typ_eq.
                   - eapply eq_trans; [ | eauto ].
                     solve_inst_or_unr_typ_eq. }
                 rewrite Forall_app.
                 split; apply subst.Forall_comp_map; rewrite Forall_forall.
                 all:
                   let x := fresh "x" in
                   intro x; destruct x as [[curL curHV] curSz];
                   intros.
                 all:
                   match goal with
                    | [ |- context[if ?B then _ else _] ] =>
                      remember B as critb;
                      revert Heqcritb;
                      case critb; eauto
                   end.
                 all: intros.
                 all:
                   match goal with
                   | [ H : SplitStoreTypings (map _ _ ++ map _ _) _ |-
                       context[InstTyp (?F ?TPL)] ] =>
                     specialize (SplitStoreTypings_eq_typs2 (S:=F TPL) H)
                   end.
                 all:
                   match goal with
                   | [ |- (?A -> _) -> _ ] =>
                     let H := fresh "H" in
                     let H' := fresh "H" in
                     assert (H : A);
                     [ | intro H'; specialize (H' H) ]
                   end.
                 1,3:
                    match goal with
                    | [ H : false = (_ && _)%bool |- _ ] =>
                      specialize (Bool.andb_false_elim _ _ (eq_sym H));
                      let H' := fresh "H" in intro H'; case H';
                      intros
                    end.
                 1,3: destruct m; subst; simpl in *.
                 all:
                   try match goal with
                       | [ H : true = false |- _ ] => inversion H
                       end.
                 1-4: apply in_or_app.
                 1,3: left.
                 3,4: right.
                 1-4: apply in_map.
                 1,3: eapply Permutation.Permutation_in; eauto.
                 1-2: destruct m; subst; simpl in *.
                 1,4: eapply Permutation.Permutation_in; eauto.
                 1-2:
                   match goal with
                   | [ H : (?B =? ?A)%N = false |- _ ] =>
                     let H' := fresh "H" in
                     assert (H' : A <> B);
                     [ rewrite (iff_sym (N.eqb_neq _ _));
                       rewrite N.eqb_sym; auto | ]
                   end.
                 1-2:
                   match goal with
                   | [ H : In ?TPL _ |- In ?TPL _ ] =>
                     apply In_nth_error in H;
                     let x := fresh "x" in
                     destruct H as [x H];
                     apply in_to_list_implies_get in H
                   end.
                 1-2:
                   match goal with
                   | [ H : Some ?MEM2 = set _ _ _ _,
                       H' : _ <> _ |- _ ] =>
                     specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) H')
                   end.
                 1-2: intros.
                 1-2:
                   match goal with
                   | [ H : ?A = ?B, H' : ?B = Some _ |- _ ] =>
                     rewrite H' in H;
                     apply get_implies_in_to_list in H;
                     let x := fresh "x" in
                     destruct H as [x H];
                     apply nth_error_In in H; auto
                   end.
                 all: destructAll.
                 all: split; apply eq_sym; eapply eq_trans;
                   [ eauto | | eauto | ].
                 -- solve_inst_or_unr_typ_eq.
                 -- solve_inst_or_unr_typ_eq.
                 -- solve_inst_or_unr_typ_eq.
                 -- solve_inst_or_unr_typ_eq.
               - destruct m; subst; simpl in *.
                 all:
                   match goal with
                   | [ H : Permutation.Permutation ?L1 ?L2
                       |- context[map ?F ?L1] ] =>
                     let H' := fresh "H" in
                     assert (H' : Permutation.Permutation (map F L1) (map F L2));
                     [ apply Permutation.Permutation_map; auto | ]
                   end.
                 all:
                   match goal with
                   | [ H : Some _ = set _ _ _ _ |- _ ] =>
                     specialize (get_set_same _ _ _ _ _ (eq_sym H))
                   end.
                 all: intros; destructAll.
                 all:
                   match goal with
                   | [ H : nth_error (M.to_list ?M ?MEM1) ?IDX = Some (?L, ?HV1, ?SZ1),
                       H' : Some ?MEM2 = set ?L ?M ?MEM1 ?NEWV,
                       H'' : SplitStoreTypings (set_nth _ _ _) ?NEWEL,
                       H''' : context[map ?F1 (M.to_list ?M ?MEM1)],
                       H'''' : get ?L ?M ?MEM2 = Some (?NEWV, ?NEWSZ)
                       |- context[map ?F2 (M.to_list ?M ?MEM2)] ] =>
                       specialize (set_to_list_Permutation (f1:=F1) (f2:=F2) (newel:=NEWEL) H (eq_sym H') H'''')
                   end.
                 all:
                   match goal with
                   | [ |- (?A -> _) -> _ ] =>
                     let H := fresh "H" in
                     let H' := fresh "H" in
                     assert (H : A);
                     [ | intro H'; specialize (H' H) ]
                   end.
                 1,3:
                   let x := fresh "x" in
                   intro x; destruct x as [[curL curHV] curSz]; auto.
                 Ltac apply_SplitHeapTypings_permut_StructSwap L1 L2 L1P L2P :=
                   let H'' := fresh "H" in
                   assert (H'' : Permutation.Permutation
                                   (L1 ++ L2) (L1P ++ L2P));
                   [ apply Permutation.Permutation_app | ]; auto;
                   try ltac:(apply Permutation.Permutation_sym; auto);
                   eapply SplitHeapTypings_permut;
                   [ eapply Permutation.Permutation_map;
                     eapply Permutation.Permutation_sym;
                     exact H'' | ].

                 all:
                   match goal with
                   | [ H : Permutation.Permutation ?L1 ?L1P,
                       H' : Permutation.Permutation ?L2P ?L2
                       |- context[?L1 ++ ?L2] ] =>
                     apply_SplitHeapTypings_permut_StructSwap L1 L2 L1P L2P
                   | [ H : Permutation.Permutation ?L2 ?L2P,
                       H' : Permutation.Permutation ?L1P ?L1
                       |- context[?L1 ++ ?L2] ] =>
                     apply_SplitHeapTypings_permut_StructSwap L1 L2 L1P L2P
                   end.

                 all:
                   match goal with
                   | [ |- SplitHeapTypings (map LinTyp ?Ss) (LinTyp ?S) ] =>
                     let H := fresh "H" in
                     assert (H : SplitStoreTypings Ss S);
                     [ | inversion H; auto ]
                   end.

                 1: rewrite set_nth_app2.
                 2:
                   rewrite set_nth_app;
                   [ | eapply nth_error_Some_length;
                       eapply nth_error_map; eauto ].

                 all:
                   match goal with
                   | [ H : SplitStoreTypings (map ?F1 ?L1 ++ map ?F2 ?L2) _
                       |- context[map ?F3 ?L1 ++ map ?F4 ?L2] ] =>
                     let H' := fresh "H" in
                     let H'' := fresh "H" in
                     assert (H' : map F1 L1 = map F3 L1);
                     [ try auto
                     | assert (H'' : map F2 L2 = map F4 L2);
                       [ try auto
                       | try rewrite (eq_sym H');
                         try rewrite (eq_sym H'') ] ]
                   end.
                 1,3: apply map_ext.
                 1-2:
                   let x := fresh "x" in
                   intro x; destruct x as [[curL curHV] curSz];
                   auto.

                 all:
                   eapply SplitStoreTypings_StructSwap_remove_add_one;
                   [ eauto | | | | | eauto | eauto ];
                   [ | eauto | eauto | eauto ].
                 -- rewrite nth_error_app2;
                      [ | apply OrdersEx.Nat_as_OT.le_add_r ].
                    rewrite minus_plus.
                    apply map_nth_error; auto.
                 -- rewrite nth_error_app1;
                    [ apply map_nth_error; auto | ].
                    rewrite map_length.
                    eapply nth_error_Some_length; eauto. }
                 
             destruct Hsubgoal as [S_lin' [S_unr']].
             destructAll.
             
             eapply (MeminstT _ S_lin' S_unr').
             - eapply Same_set_trans.
               -- eapply Same_set_sym.
                  eapply proj1.
                  eapply set_preserves_doms; [ | apply eq_sym; eauto ].
                  unfold get_mem in *; eauto.
               -- eapply Same_set_trans; [ eauto | ].
                  constructor.
                  all:
                    unfold Dom_ht;
                    unfold Ensembles.Included;
                    unfold Ensembles.In;
                    unfold Dom_map;
                    intros.
                  all:
                    match goal with
                    | [ H : Ensembles.Union _ _ _ _ |- _ ] =>
                      inversion H; subst; simpl in *
                    end.
                  all: unfold Ensembles.In in *.
                  all: destructAll.
                  1-2:
                    match goal with
                    | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp _) = Some ?HT |- _ ] =>
                      specialize (Hlemma L HT)
                    end.
                  1-2:
                    match goal with
                    | [ H : ?A = false \/ ?B = false -> _ |- _ ] =>
                      remember A as ba;
                      revert H;
                      revert Heqba;
                      case ba;
                      [ let H' := fresh "H" in
                        intros H' H;
                        remember B as bb;
                        revert H;
                        revert Heqbb;
                        case bb;
                        [ | let H'' := fresh "H" in
                            intros H'' H;
                            specialize (H (or_intror eq_refl)) ]
                      | let H' := fresh "H" in
                        intros H' H;
                        specialize (H (or_introl eq_refl)) ]
                    end.
                  1,4: intros.
                  1-2: destruct m; subst; simpl in *.
                  1,3:
                    match goal with
                    | [ H : true = false |- _ ] => inversion H
                    end.
                  1-2:
                    match goal with
                    | [ H : true = (?A =? ?B)%N |- _ ] =>
                      let H' := fresh "H" in
                      assert (H' : A = B); [ apply Neqb_ok; eauto | subst ]
                    end.
                  1-2: right.
                  1-2: unfold Ensembles.In.
                  1-2: eexists.
                  1-2:
                    match goal with
                    | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP
                        |- context[?SP] ] =>
                      eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                    end.
                  1-2:
                    match goal with
                    | [ H : SplitStoreTypings [?S; _] ?SP
                        |- context[?SP] ] =>
                      eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                    end.
                  1-2: simpl.
                  1-2: unfold get_heaptype.
                  1-2: rewrite M.gss; eauto.
                  1-4: unfold get_heaptype in *.
                  1-4:
                    match goal with
                    | [ H : ?A, H' : ?A \/ ?B -> _ |- _ ] =>
                      specialize (H' (or_introl H));
                      case H'; [ left | right ]
                    | [ H : ?B, H' : ?A \/ ?B -> _ |- _ ] =>
                      specialize (H' (or_intror H));
                      case H'; [ left | right ]
                    end.
                  1-8: unfold Ensembles.In.
                  1-8: eexists; eauto.
                  --- match goal with
                      | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some _,
                          H' : SplitStoreTypings [_; _] ?S
                          |- context[?L] ] =>
                          specialize (SplitStoreTypings_inv H H')
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ [_; _] |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      ---- right; unfold Ensembles.In.
                           match goal with
                           | [ H : get_heaptype ?L (LinTyp _) = Some ?HT
                               |- context[?L] ] =>
                               exists HT
                           end.
                           match goal with
                           | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP
                               |- context[?SP] ] =>
                             eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                           end.
                           match goal with
                           | [ H : SplitStoreTypings [_; ?S] ?SP
                               |- context[?SP] ] =>
                             eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor 2; constructor; auto ]
                           end.
                           match goal with
                           | [ H : SplitStoreTypings [?S; _] ?SP
                               |- context[?SP] ] =>
                             eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                           end.
                           auto.
                      ---- left; unfold Ensembles.In.
                           match goal with
                           | [ H : get_heaptype ?L (LinTyp _) = Some ?HT
                               |- context[?L] ] =>
                               exists HT
                           end.
                           match goal with
                           | [ H : SplitStoreTypings [_; ?S] ?SP
                               |- context[?SP] ] =>
                             eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor 2; constructor; auto ]
                           end.
                           match goal with
                           | [ H : _ \/ False |- _ ] =>
                             case H; [ | intros; exfalso; eauto ]
                           end.
                           intros; subst; auto.
                  --- match goal with
                      | [ H : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some _,
                          H' : SplitStoreTypings (_ :: _ ++ _) ?S
                          |- context[?L] ] =>
                          specialize (SplitStoreTypings_inv H H')
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      ---- match goal with
                           | [ H : get_heaptype ?L (LinTyp ?S) = Some _,
                               H' : SplitStoreTypings [_; _] ?S
                               |- context[?L] ] =>
                               specialize (SplitStoreTypings_inv H H')
                           end.
                           intros; destructAll.
                           match goal with
                           | [ H : In _ [_; _] |- _ ] =>
                             inversion H; subst; simpl in *
                           end.
                           ----- destruct m; subst; simpl in *; subst; simpl in *.
                                 ------ match goal with
                                        | [ H : context[empty_LinTyp ?S] |- _ ] =>
                                          unfold empty_LinTyp in H;
                                          destruct S; subst; simpl in *;
                                          unfold get_heaptype in H;
                                          rewrite M.gempty in H;
                                          inversion H
                                        end.
                                 ------ match goal with
                                        | [ H : get_heaptype ?L (M.add (N.succ_pos ?L2) _ _) = _
                                            |- context[?L] ] =>
                                          unfold get_heaptype in H;
                                          assert (Hloc_dec : L = L2 \/ L <> L2) by apply eq_dec_N;
                                          case Hloc_dec; intros; subst;
                                          [ | rewrite M.gso in H;
                                            [ rewrite M.gempty in H;
                                              inversion H | ] ]
                                        end.
                                        ------- right; unfold Ensembles.In.
                                                match goal with
                                                | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP,
                                                    H' : SplitStoreTypings [?S0; _] ?S,
                                                    H'' : HasTypeValue ?S0 _ _ _
                                                    |- context[?SP] ] =>
                                                  inversion H''; subst; simpl in *
                                                end.
                                                eexists.
                                                match goal with
                                                | [ H : SplitStoreTypings (?S :: _ ++ _) ?SP
                                                    |- context[?SP] ] =>
                                                  eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                                                end.
                                                match goal with
                                                | [ H : SplitStoreTypings [?S; _] ?SP
                                                    |- context[?SP] ] =>
                                                  eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                                                end.
                                                match goal with
                                                | [ H : eq_map _ _ |- _ ] =>
                                                  unfold eq_map in H;
                                                  rewrite H
                                                end.
                                                unfold get_heaptype.
                                                rewrite M.gss.
                                                eauto.
                                        ------- intro.
                                                match goal with
                                                | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                                  assert (Hloc_eq : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                                end.
                                                repeat rewrite N.pos_pred_succ in Hloc_eq; eauto.
                           ----- match goal with
                                 | [ H : _ \/ False |- _ ] =>
                                   case H; [ | intros; exfalso; auto ]
                                 end.
                                 intros; subst.
                                 left; unfold Ensembles.In.
                                 eexists.
                                 match goal with
                                 | [ H : SplitStoreTypings [?S; _] ?SP
                                     |- context[?SP] ] =>
                                   eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | exact H ]; [ | constructor; auto ]
                                 end.
                                 eauto.
                      ---- right; unfold Ensembles.In.
                           eexists.
                           match goal with
                           | [ H : SplitStoreTypings (_ :: _ ++ _) ?SP
                               |- context[?SP] ] =>
                             eapply (SplitStoreTypings_get_heaptype_LinTyp); [ | | exact H ]; [ eauto | ]
                           end.
                           constructor 2; auto.
             - assert (Hunr_eq1 : UnrTyp Sh' = UnrTyp Sh).
               { solve_inst_or_unr_typ_eq. }
               assert (Hunr_eq2 : UnrTyp Sp' = UnrTyp Sp).
               { solve_inst_or_unr_typ_eq. }
               rewrite Hunr_eq1.
               rewrite Hunr_eq2.
               eapply Same_set_trans; [ | eauto ].
               eapply Same_set_sym.
               eapply proj2.
               eapply set_preserves_doms; [ | apply eq_sym; eauto ].
               unfold get_mem in *; eauto.
             - constructor; auto.
             - auto.
             - auto. }
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         match goal with
         | [ H : ?A = ?B |- context[?B] ] =>
           rewrite (eq_sym H)
         end.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow ?IN _ ] ] =>
           replace IN with (IN ++ []) at 1 by apply app_nil_r
         end.
         match goal with
         | [ |- context[Arrow _ (?A ++ ?B ++ ?C ++ ?OUT)] ] =>
           replace (A ++ B ++ C ++ OUT) with ((A ++ B ++ C) ++ OUT) at 1
         end.
         2:{
           repeat rewrite app_assoc.
           auto.
         }
         eapply FrameTyp.
         --- reflexivity.
         --- apply Forall_trivial.
             intro qt.
             destruct qt.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- match goal with
             | [ |- context[[Val ?A; Val ?B]] ] =>
               replace [Val A; Val B] with ([Val A] ++ [Val B])
             end.
             2:{
               simpl; auto.
             }
             eapply ConsTyp.
             ---- eauto.
             ---- match goal with
                  | [ H : HasTypeValue _ _ (Ref (LocP _ _)) (QualT (RefT W ?A (StructType (combine ?L1 ?B))) ?C),
                      H' : ReplaceAtIdx _ ?L1 _ = Some (?L2, _) |- _ ] =>
                    eapply (ValTyp _ _ _ _ _ (QualT (RefT W A (StructType (combine L2 B))) C))
                  end.
                  destruct m; simpl in *; subst.
                  ----- match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] => inversion H; subst
                        end.
                        
                        (* Old array of types = new array of types when qualifier is unrestricted. *)
                        match goal with
                        | [ H : ReplaceAtIdx _ ?L _ = Some (?L2, _) |- _ ] =>
                          assert (Heq_typs : L = L2)
                        end.
                        { match goal with
                          | [ H : _ \/ _ |- _ ] =>
                            inversion H; subst; simpl in *
                          end.
                          - exfalso.
                            eapply QualLeq_Const_False.
                            destruct F; simpl in *; subst.
                            unfold Function_Ctx_empty in *.
                            simpl in *; destructAll; auto.
                            eapply QualLeq_Trans; [ eauto | ].
                            eauto.
                          - eapply ReplaceAtIdx_no_change; eauto. }
                        subst.
                        eapply RefTypUnr; subst; eauto.
                        ------ unfold empty_LinTyp.
                               destruct Sstack; subst.
                               simpl; eauto.
                        ------ match goal with
                               | [ H : SplitStoreTypings _ Sstack |- _ ] => inversion H
                               end.
                               match goal with
                               | [ H : Forall _ [_; _] |- _ ] =>
                                 inversion H; subst
                               end.
                               destructAll.
                               unfold empty_LinTyp.
                               destruct Sstack; simpl in *; subst.
                               auto.
                        ------ destruct F; simpl in *; subst; eauto.
                        ------ match goal with
                               | [ H : TypeValid _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               constructor; destruct F; simpl in *; subst; eauto.                  
                               replace_heaptypevalid_parts label ret size type location.
                               apply HeapTypeValid_linear.
                               auto.
                  ----- match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] => inversion H; subst
                        end.
                        eapply RefTypLin; subst; eauto.
                        ------ simpl.
                               specialize (eq_map_equiv HeapType).
                               intro H'.
                               inversion H'.
                               apply Equivalence_Reflexive.
                        ------ destruct F; simpl in *; eauto.
                        ------ match goal with
                               | [ H : TypeValid _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               constructor; destruct F; simpl in *; subst; eauto.
                               replace_heaptypevalid_parts label ret size type location.
                               apply HeapTypeValid_linear.
                               constructor.
                               simpl in *.
                               eapply Forall_combine_ReplaceAtIdx.
                               ------- match goal with
                                       | [ H : HeapTypeValid _ _ |- _ ] =>
                                         inversion H; subst; simpl in *; eauto
                                       end.
                               ------- eauto.
                               ------- eauto.
                               ------- match goal with
                                       | [ H : sizeOfType _ _ = Some ?SZ |- _ ] => exists SZ
                                       end.
                                       simpl in *.
                                       split; [ eauto | ].
                                       match goal with
                                       | [ H : HeapTypeValid _ _ |- _ ] =>
                                         inversion H; subst; simpl in *; eauto
                                       end.
                                       match goal with
                                       | [ H : length ?L1 = length ?L2,
                                           H' : Forall _ (combine ?L1 ?L2),
                                           H'' : nth_error ?L2 _ = _ |- _ ] =>
                                         specialize (Forall_combine_nth_error _ _ _ _ _ H H' H'')
                                       end.
                                       intro Hold.
                                       destructAll; simpl in *.
                                       split; [ eauto | ].
                                       split; eauto.
                                       replace_typevalid_parts label ret size type location.
                                       apply TypeValid_linear.
                                       eauto.
                  ----- destruct F; subst; simpl in *; solve_lcvs.
             ---- match goal with
                  | [ |- context[Arrow [?A] [?A; ?B]] ] =>
                    replace [A] with ([A] ++ []) at 1 by ltac:(simpl; auto);
                    replace [A; B] with ([A] ++ [B]) at 1 by ltac:(simpl; auto)
                  end.
                  eapply FrameTyp.
                  ----- reflexivity.
                  ----- apply Forall_trivial.
                        intro qt.
                        destruct qt.
                        apply QualLeq_Top.
                  ----- apply QualLeq_Top.
                  ----- constructor.
                        ------ apply HasTypeValue_empty_function_ctx; eauto.
                               destruct Hempty; destruct F; simpl in *.
                               constructor; simpl; eauto.
                        ------ destruct F; subst; simpl in *; solve_lcvs.
                  ----- destruct F; subst; simpl in *; constructor; solve_tvs.
                        match goal with
                        | [ H : Forall _ [?T; _] |- context[?T] ] =>
                          inv H
                        end.
                        eapply TypeValid_Function_Ctx; eauto.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- do 3 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- match goal with
         | [ H : ?A = ?B |- context[?B] ] =>
           rewrite (eq_sym H); eauto
         end.
      -- match goal with
         | [ H : ?A = ?B |- context[?B] ] =>
           rewrite (eq_sym H)
         end.
         split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans; [ eapply LCSizeEqual_trans | ].
         all: apply LCEffEqual_LCSizeEqual; eauto.

    - (* VariantCase Unr *)
      match goal with
      | [ H : context[[Val ?V; ?C]] |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H by ltac:(simpl; auto)
      end.

      rewrite app_assoc in Hi.
      specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ [_]) _ _ |- _ ] =>
        specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hb.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction_moreinfo in H
      end.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [VariantCase _ _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; apply VariantCaseTypUnr_HasTypeInstruction in H
      end.
      2:{
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
      }
      simpl in *.
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : ?A ++ ?B ++ [?C] = ?D ++ ?E ++ [?F] |- _ ] =>
        repeat rewrite app_assoc in H;
        assert (Heq2 : A ++ B = D ++ E /\ C = F) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ ?LP ?VS _ ?L,
          H' : values ?VS |- _ ] =>
        assert (LCEffEqual [] L LP);
        [ apply LCEffEqual_sym; eauto;
          specialize (HasTypeInstruction_values_locals H H') | ]
      end.
      { destruct F; subst; simpl in *; auto.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto. }
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (?VS ++ _) (Arrow (_ ++ ?BTS) (_ ++ ?ATS ++ _)) _,
          H' : HasTypeInstruction ?S _ ?F _ _ (Arrow ?BTS ?ATS) _ |- _ ] =>
        assert (exists x Ss,
                   ATS = BTS ++ x /\
                   SplitStoreTypings Ss S /\
                   Forall3
                     (fun t e S =>
                        exists v,
                          e = Val v /\
                          HasTypeValue S F v t)
                     x VS Ss)
      end.
      { (* Also used in ExistUnpack Unr *)
        Ltac use_Values_HasTypeInstruction :=
          match goal with
          | [ H : HasTypeInstruction _ _ _ _ ?VS _ _,
              H' : values ?VS |- _ ] =>
            specialize (Values_HasTypeInstruction _ _ _ _ _ _ _ _ H' H)
          end;
          intros; destructAll;
          do 2 eexists;
          split; [ | split ];
          [ reflexivity
          | eauto
          | rewrite Forall3_forall;
            match goal with
            | [ H : Forall3 _ _ _ _ |- _ ] =>
              specialize (Forall3_length _ _ _ _ H)
            end;
            intros; destructAll;
            rewrite to_values_len in *;
            split; [ | split ]; auto;
            intros;
            match goal with
            | [ H : values ?VS, H' : nth_error ?VS _ = Some _ |- _ ] =>
              rewrite (map_to_values H) in H';
              apply nth_error_map_inv in H'
            end;
            destructAll;
            eexists; split; [ eauto | ];
            match goal with
            | [ H : Forall3 _ ?L1 ?L2 ?L3,
                H' : nth_error ?L1 _ = Some _,
                H'' : nth_error ?L2 _ = Some _,
                H''' : nth_error ?L3 _ = Some _ |- _ ] =>
              rewrite Forall3_forall in H;
              destruct H as [H];
              exact (H _ _ _ _ H' H'' H''')
            end ].
        use_Values_HasTypeInstruction. }

      destructAll; subst.
      match goal with
      | [ H : _ ++ _ ++ _ = _ ++ _ |- _ ] =>
        rewrite app_assoc in H
      end.
      match goal with
      | [ H : Forall3 _ _ _ _ |- _ ] =>
        generalize (Forall3_length _ _ _ _ H)
      end.
      intro; destructAll.
      match goal with
      | [ H : length ?VS = length ?INTS,
          H' : length _ = length ?VS,
          H'' : HasTypeInstruction _ _ _ _ (?VS ++ _) _ _,
          H''' : context[Arrow ?INTS _] |- _ ] =>
        rewrite H in H'
      end.
      match goal with
      | [ H : (_ ++ _) ++ _ = _ ++ _ |- _ ] =>
        apply app_eq_len in H; [ | assumption ]
      end.
      destructAll; subst.
      
      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow _ (?A ++ (?B ++ ?C) ++ _)] ] =>
           rewrite (app_assoc A (B ++ C) _);
           replace (A ++ B ++ C) with ((A ++ B ++ C) ++ []) at 1 by apply app_nil_r
         end.
         (* Matching for Q under function doesn't work, so create H' instead: *)
         match goal with
         | [ H : Forall ?P (?A ++ ?B)
             |- context[Arrow ((_ ++ ?A ++ ?B) ++ _) _] ] =>
           let H' := fresh "H" in
           assert (H' : P (QualT Unit Unrestricted) \/ True) by ltac:(right; constructor);
           simpl in H';
           match type of H' with
           | QualLeq _ _ ?Q = _ \/ _ => eapply (FrameTyp _ _ _ _ _ Q)
           end;
           clear H'
         end.
         --- reflexivity.
         --- rewrite Forall_app.
             split.
             ---- prepare_Forall.
                  eapply (QualLeq_Trans _ _ _); eauto.
                  destruct F; simpl in *; destruct linear; simpl in *; eauto.
             ---- destruct F; simpl in *; eauto.
         --- destruct F.
             simpl in *.
             destruct linear; simpl in *; eapply QualLeq_Trans; eauto.
         --- rewrite app_comm_cons.
             match goal with
             | [ H : SplitStoreTypings [?S1; ?S2] Sstack
                 |- HasTypeInstruction
                      _ _ _ ?L
                      (_ ++ [_ (Arrow ?BTS ?ATS) _ _])
                      (Arrow _ (?T :: _))
                      ?LP ] =>
               eapply (ConsTyp _ S1 S2 _ _ _ L LP _ _ _ ([T] ++ BTS))
             end.
             ---- eassumption.
             ---- match goal with
                  | [ H : SplitStoreTypings [?S1; ?S2] ?S
                      |- HasTypeInstruction
                           ?S _ _ ?L (?E :: ?VS)
                           (Arrow _ ([?T] ++ _)) _ ] =>
                    replace (E :: VS) with ([E] ++ VS) by ltac:(simpl; congruence);
                    apply (HasTypeInstruction_app _ S2 S1 _ _ _ _ _ L _ _ [T])
                  end.
                  ----- apply ValTyp.
                        2:{ destruct F; subst; simpl in *; solve_lcvs. }
                        apply HasTypeValue_update_linear_ctx.
                        eapply HasTypeValue_Function_Ctx; try eassumption;
                        unfold update_linear_ctx;
                        destruct F;
                        simpl;
                        eauto.
                  ----- match goal with
                        | [ |- context[Arrow ?A _] ] =>
                          replace A with (A ++ []) by apply app_nil_r
                        end.
                        eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
                        ------ reflexivity.
                        ------ apply Forall_trivial.
                               intro qt.
                               destruct qt.
                               apply QualLeq_Top.
                        ------ apply QualLeq_Top.
                        ------ use_HasTypeValues_imp_HasTypeInstruction F.
                        ------ destruct F; subst; simpl in *; solve_tvs.
                  ----- eapply SplitStoreTypings_permut; [ | eassumption ]; constructor.
             ---- match goal with
                  | [ |- context[Arrow _ (?A :: ?B)] ] =>
                    replace (A :: B) with ([A] ++ B) by ltac:(simpl; auto)
                  end.
                  match goal with
                  | [ H : QualLeq _ ?Q1 ?Q2 = Some true
                      |- context[QualT _ ?Q1] ] =>
                    eapply (FrameTyp _ _ _ _ _ Q2)
                  end.
                  ----- reflexivity.
                  ----- constructor; eauto.
                        destruct F; simpl in *.
                        eauto.
                  ----- destruct F; simpl in *.
                        unfold get_hd; destruct linear; simpl; eauto.
                  ----- eapply ChangeEndLocalTyp.
                        { destruct F; subst; simpl in *; eauto. }
                        eapply ChangeBegLocalTyp.
                        { destruct F; subst; simpl in *.
                          unfold Function_Ctx_empty in *.
                          simpl in *; destructAll; eauto. }
                        eapply ChangeBegLocalTyp.
                        { destruct F; subst; simpl in *.
                          eapply LCEffEqual_sym; eauto. }
                        eapply BlockTyp.
                        match goal with
                        | [ |- HasTypeInstruction _ _ _ _ (?A :: ?B) _ _ ] =>
                          replace (A :: B) with ([A] ++ B) by ltac:(simpl; apply eq_refl)
                        end.
                        match goal with
                        | [ H : nth_error ?ESS _ = Some ?ES,
                            H' : Forall2 _ ?ESS _
                            |- HasTypeInstruction _ _ _ _ (_ ++ ?ES) _ _ ] =>
                          specialize (forall2_args_1 _ _ _ _ _ H' H)
                        end.
                        
                        intro Hhti.
                        destructAll.

                        match goal with
                        | [ H : nth_error ?TS _ = Some ?T,
                            H' : context[VariantType ?TS]
                            |- HasTypeInstruction
                                 ?S _ _ _ _ (Arrow ?BTS _) _ ] =>
                          eapply (HasTypeInstruction_app _ S S _ _ _ _ _ _ _ _ (BTS ++ [T]))
                        end.
                        ------ match goal with
                               | [ |- context[Arrow ?TS _] ] =>
                                 replace TS with (TS ++ []) at 1 by apply app_nil_r
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- apply Forall_trivial.
                                       let t := fresh "t" in
                                       intro t; destruct t.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- apply ValTyp.
                                       apply HasTypeValue_update_linear_ctx.
                                       match goal with
                                       | [ H : get_mem _ _ _ = Some _ |- _ ] =>
                                         unfold get_mem in H
                                       end.
                                       match goal with
                                       | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                                         inversion H; subst
                                       end.
                                       -------- inversion Hst.
                                                subst.
                                                match goal with
                                                | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                match goal with
                                                | [ H : get _ _ _ = Some _ |- _ ] =>
                                                  specialize (get_implies_in_to_list _ _ _ _ _ H)
                                                end.
                                                intro Hne.
                                                destructAll.

                                                match goal with
                                                | [ H : Forall2 _ _ ?L2,
                                                    H' : nth_error ?L2 _ = Some _
                                                    |- _ ] =>
                                                  specialize (forall2_args_2 _ _ _ _ _ H H')
                                                end.
                                                intro Hne2.
                                                destructAll.

                                                match goal with
                                                | [ H : get_heaptype _ ?UT = Some _,
                                                    H' : get_heaptype _ ?UT2 = Some (VariantType _) |- _ ] =>
                                                  assert (Hunr_eq : UT = UT2);
                                                  [ assert (Hunr_eq' : UT2 = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                                  | rewrite Hunr_eq in H ]
                                                end.
                                                { rewrite Hunr_eq'.
                                                  eapply proj1.
                                                  eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                  apply in_or_app; right.
                                                  eapply nth_error_In; eauto. }

                                                match goal with
                                                | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                                                  rewrite H in H';
                                                  inversion H'; subst
                                                end.
                                                match goal with
                                                | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                match goal with
                                                | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                                                  rewrite H in H';
                                                  inversion H'; subst
                                                end.
                                                apply HasTypeValue_empty_function_ctx.
                                                match goal with
                                                | [ H : HasHeapType ?S _ _ _
                                                    |- HasTypeValue ?S2 _ _ _ ] =>
                                                  assert (Htyps_eq : InstTyp S = InstTyp S2 /\ UnrTyp S = UnrTyp S2)
                                                end.
                                                { split.
                                                  - match goal with
                                                    | [ |- _ = ?A ] =>
                                                      assert (Hinst_eq' : A = InstTyp Sh) by solve_inst_or_unr_typ_eq
                                                    end.
                                                    rewrite Hinst_eq'.
                                                    eapply proj2.
                                                    eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                    apply in_or_app; right.
                                                    eapply nth_error_In; eauto.
                                                  - match goal with
                                                    | [ |- _ = ?A ] =>
                                                      assert (Hunr_eq' : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                                    end.
                                                    rewrite Hunr_eq'.
                                                    eapply proj1.
                                                    eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                    apply in_or_app; right.
                                                    eapply nth_error_In; eauto. }
                                                destructAll.

                                                eapply HasTypeValue_same_envs.
                                                --------- eassumption.
                                                --------- assumption.
                                                --------- assumption.
                                                --------- apply eq_map_empty; try assumption.
                                                          match goal with
                                                          | [ H : nth_error _ _ = Some ?T,
                                                              H' : HasTypeValue _ _ _ ?T |- _ ] =>
                                                            destruct T
                                                          end.
                                                          match goal with
                                                          | [ H : context[(update_linear_ctx (set_hd ?Q1 (linear (update_linear_ctx (set_hd ?Q2 (linear F)) F))))],
                                                              H' : HasTypeValue ?S _ _ _
                                                              |- M.is_empty (LinTyp ?S) = true ] =>
                                                            specialize (HasTypeValue_empty_function_ctx _ (update_linear_ctx (set_hd Q1 (linear (update_linear_ctx (set_hd Q2 (linear F)) F))) (update_linear_ctx (set_hd Q1 (linear F)) F)) _ _ H')
                                                          end.
                                                          match goal with
                                                          | [ |- (?A -> ?B) -> ?C ] =>
                                                            intro Hhtv; assert (Hhtv' : A); [ | specialize (Hhtv Hhtv') ]
                                                          end.
                                                          { destruct Hempty; destruct F; simpl in *; constructor; simpl in *; eauto. }
                                                          eapply (HasTypeValue_Unrestricted_LinEmpty _ _ _ _ _ Hhtv).
                                                          2:{
                                                            destruct F; subst; simpl in *.
                                                            unfold Function_Ctx_empty in *.
                                                            simpl in *; destructAll; auto.
                                                          }
                                                          match goal with
                                                          | [ H : nth_error _ _ = Some ?T,
                                                              H' : HasTypeValue _ _ _ ?T |- _ ] =>
                                                            specialize (nth_error_In _ _ H)
                                                          end.
                                                          intro Hin.
                                                          repeat match goal with
                                                          | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
                                                            rewrite Forall_forall in H;
                                                            specialize (H _ H')
                                                          end.
                                                          simpl in *.
                                                          destruct F; subst; simpl in *; auto.
                                                --------- destruct F; simpl in *.
                                                          constructor; simpl in *; destruct Hempty; eauto.
                                       -------- inversion Hst.
                                                subst.
                                                match goal with
                                                | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                match goal with
                                                | [ H : get _ _ _ = Some _ |- _ ] =>
                                                  specialize (get_implies_in_to_list _ _ _ _ _ H)
                                                end.
                                                intro Hne.
                                                destructAll.

                                                match goal with
                                                | [ H : Forall2 _ _ ?L2,
                                                    H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                                  specialize (forall2_args_2 _ _ _ _ _ H H')
                                                end.
                                                intro Hne2.
                                                destructAll.

                                                (* Use eq_map to show get_heaptype assertion *)
                                                match goal with
                                                | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                                  assert (Hght : get_heaptype L LT = Some T)
                                                end.
                                                { match goal with
                                                  | [ H : eq_map _ _ |-
                                                      get_heaptype ?L _ = _] =>
                                                    rewrite (H L)
                                                  end.
                                                  unfold get_heaptype.
                                                  rewrite typing.M.gss.
                                                  eauto. }
                                                (* LinTyp x13 is a subset of LinTyp Sstack is a subset of LinTyp Sp *)
                                                match goal with
                                                | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                                  assert (HghtSp : get_heaptype L (LinTyp Sp) = Some T)
                                                end.
                                                { match goal with
                                                  | [ H : SplitStoreTypings [?S1; ?S2] ?S,
                                                      H' : get_heaptype ?L (LinTyp ?S2) = Some _
                                                      |- get_heaptype ?L _ = _ ] =>
                                                    specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=[S1;S2]) (S2:=S) Hght)
                                                  end.
                                                  match goal with
                                                  | [ |- (?A -> ?B -> _) -> _ ] =>
                                                    let H1 := fresh "H" in
                                                    let H2 := fresh "H" in
                                                    let H3 := fresh "H" in
                                                    assert (H1 : A);
                                                      [ constructor 2; constructor; eauto
                                                      | assert (H2 : B);
                                                        [ eauto
                                                        | intro H3;
                                                          specialize (H3 H1 H2); 
                                                          match goal with
                                                          | [ H : SplitStoreTypings ?SS Sstack |- _ ] =>
                                                            specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=Sstack) H3)
                                                          end ] ]
                                                  end.
                                                  match goal with
                                                  | [ |- (?A -> ?B -> _) -> _ ] =>
                                                    let H1 := fresh "H" in
                                                    let H2 := fresh "H" in
                                                    let H3 := fresh "H" in
                                                    assert (H1 : A);
                                                      [ constructor; eauto
                                                      | assert (H2 : B);
                                                        [ eauto
                                                        | intro H3;
                                                          specialize (H3 H1 H2); 
                                                          specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=(Sstack :: S_ignore ++ Ss)) (S2:=Sp) H3) ] ]
                                                  end.
                                                  match goal with
                                                  | [ |- (?A -> ?B -> _) -> _ ] =>
                                                    let H1 := fresh "H" in
                                                    let H2 := fresh "H" in
                                                    let H3 := fresh "H" in
                                                    assert (H1 : A);
                                                      [ constructor; eauto
                                                      | assert (H2 : B);
                                                        [ eauto
                                                        | intro H3;
                                                          specialize (H3 H1 H2) ] ]
                                                  end.
                                                  eauto. }
                                                
                                                (* Sp and Sh are disjoint *)
                                                match goal with
                                                | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                                  assert (HnghtSh : forall x, get_heaptype L (LinTyp Sh) = Some x -> False)
                                                end.
                                                { intros.
                                                  match goal with
                                                  | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
                                                    inversion H
                                                  end.
                                                  simpl in *.
                                                  match goal with
                                                  | [ H : SplitHeapTypings [LinTyp Sp; LinTyp Sh] _ |- _ ] =>
                                                    inversion H
                                                  end.
                                                  unfold get_heaptype in *.
                                                  match goal with
                                                  | [ H : _ <--> _ |- _ ] =>
                                                    inversion H
                                                  end.
                                                  match goal with
                                                  | [ H : _ \subset (Dom_ht (LinTyp S)),
                                                      H' : M.find (N.succ_pos ?L) (LinTyp Sh) = _ |- _ ] =>
                                                    specialize (H L)
                                                  end.
                                                  match goal with
                                                  | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
                                                    let H' := fresh "H" in
                                                    assert (H' : A); [ | specialize (H H') ]
                                                  end.
                                                  { unfold Ensembles.In.
                                                    unfold Dom_ht.
                                                    simpl.
                                                    constructor.
                                                    unfold Ensembles.In.
                                                    unfold Dom_map.
                                                    eexists; eauto. }
                                                  unfold Ensembles.In in *.
                                                  unfold Dom_ht in *.
                                                  unfold Ensembles.In in *.
                                                  unfold Dom_map in *.
                                                  destructAll.
                                                  match goal with
                                                  | [ H : forall _ _, M.find (N.succ_pos _) (LinTyp S) = _ -> _,
                                                      H' : M.find (N.succ_pos ?L) (LinTyp S) = Some ?T |- _ ] =>
                                                    specialize (H L T H'); inversion H; subst; simpl in *
                                                  end.
                                                  1:
                                                    match goal with
                                                    | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                                                      inversion H; subst; simpl in *
                                                    end.
                                                  all: unfold get_heaptype in *.
                                                  all:
                                                    match goal with
                                                    | [ H : ?A = Some _, H' : ?A = None |- _ ] => rewrite H in H'; inversion H'
                                                    end. }
                                                match goal with
                                                | [ H : _ \/ _ |- _ ] =>
                                                  case H
                                                end.
                                                { intro Hbad.
                                                  specialize (HnghtSh _ Hbad).
                                                  exfalso.
                                                  assumption. }
                                                intro Hhl1.
                                                rewrite HghtSp in Hhl1.
                                                inversion Hhl1.
                                                subst.

                                                match goal with
                                                | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                match goal with
                                                | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                                                  rewrite H in H';
                                                  inversion H'; subst
                                                end.

                                                apply HasTypeValue_empty_function_ctx.
                                                2:{
                                                  destruct F; subst; simpl in *.
                                                  unfold Function_Ctx_empty in *.
                                                  destructAll.
                                                  simpl in *; destructAll.
                                                  repeat constructor.
                                                }
                                                match goal with
                                                | [ H : HasTypeValue ?S1 ?A ?B ?C
                                                    |- HasTypeValue ?S2 ?A ?B ?C ] =>
                                                  assert (Htyps_eq : InstTyp S1 = InstTyp S2 /\ UnrTyp S1 = UnrTyp S2)
                                                end.
                                                { split.
                                                  - match goal with
                                                    | [ |- _ = ?A ] =>
                                                      assert (Hinst_eq' : A = InstTyp Sh) by solve_inst_or_unr_typ_eq
                                                    end.
                                                    rewrite Hinst_eq'.
                                                    eapply proj2.
                                                    eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                    apply in_or_app; left.
                                                    eapply nth_error_In; eauto.
                                                  - match goal with
                                                    | [ |- _ = ?A ] =>
                                                      assert (Hunr_eq' : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                                    end.
                                                    rewrite Hunr_eq'.
                                                    eapply proj1.
                                                    eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                    apply in_or_app; left.
                                                    eapply nth_error_In; eauto. }
                                                destructAll.

                                                eapply HasTypeValue_same_envs.
                                                --------- eassumption.
                                                --------- assumption.
                                                --------- assumption.
                                                --------- apply eq_map_empty; try assumption.
                                                          destruct tau.
                                                          match goal with
                                                          | [ H : QualValid (qual ?F) ?Q,
                                                              H' : context[QualT _ ?Q],
                                                              H'' : HasTypeValue ?S _ _ _
                                                              |- M.is_empty (LinTyp ?S) = true ] =>
                                                            specialize (HasTypeValue_empty_function_ctx _ F _ _ H'')
                                                          end.
                                                          
                                                          match goal with
                                                          | [ |- (?A -> ?B) -> ?C ] =>
                                                            intro Hhtv; assert (Hhtv' : A); [ | specialize (Hhtv Hhtv') ]
                                                          end.
                                                          { destruct Hempty; destruct F; simpl in *; constructor; simpl in *; eauto. }
                                                          eapply (HasTypeValue_Unrestricted_LinEmpty _ _ _ _ _ Hhtv).
                                                          2:{
                                                            destruct F; subst; simpl in *.
                                                            unfold Function_Ctx_empty in *.
                                                            simpl in *; destructAll; auto.
                                                          }
                                                          match goal with
                                                          | [ H : nth_error _ _ = Some (QualT _ _) |- _ ] =>
                                                            specialize (nth_error_In _ _ H)
                                                          end.
                                                          intro Hin.
                                                          repeat match goal with
                                                          | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
                                                            rewrite Forall_forall in H;
                                                            specialize (H _ H')
                                                          end.
                                                          simpl in *; eauto.
                                       -------- destruct F; subst; simpl in *; solve_lcvs.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                       ------ destruct F; simpl in *.
                              repeat rewrite set_set_hd in *; eauto.
                              eapply ChangeEndLocalTyp.
                              { eapply LCEffEqual_sym; eauto. }
                              eauto.
                       ------ unfold SplitStoreTypings.
                              split; [ apply Forall_cons; eauto | ].
                              simpl.
                              apply SplitHeapTypings_EmptyHeapTyping_r.
                              assumption.
                       ------ destruct F; subst; simpl in *.
                              eapply LCEffEqual_trans; eauto.
                  ----- destruct F; subst; simpl in *; solve_tvs.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* VariantCase Lin *)
      match goal with
      | [ H : context[[Val ?V1; ?C]] |- _ ] =>
        replace [Val V1; C] with ([Val V1] ++ [C]) in H by ltac:(simpl; congruence)
      end.
          
      specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction_moreinfo in H
      end.
      destructAll.
 
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [VariantCase _ _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; apply VariantCaseTypLin_HasTypeInstruction in H
      end.
      2:{
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
      }
      simpl in *.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ ?D ++ [?E] |- _ ] =>
        rewrite app_assoc in H;
        assert (Heq2 : A = C ++ D /\ B = E) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.
      inversion Hst.
      subst.
      match goal with
      | [ H : HasTypeMeminst _ _ _ |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : get_mem _ _ _ = Some _ |- _ ] =>
        specialize (get_implies_in_to_list _ _ _ _ _ H)
      end.
      intro Hne.
      destructAll.

      match goal with
      | [ H : Forall2 _ _ ?L2,
          H' : nth_error ?L2 _ = Some _ |- _ ] =>
        specialize (forall2_args_2 _ _ _ _ _ H H')
      end.
      intro Hne2.
      destructAll.

      match goal with
      | [ H : HasHeapType _ _ _ _ |- _ ] =>
        inversion H; subst
      end.
      match goal with
      | [ H : HasTypeValue ?S empty_Function_Ctx _ _,
          H' : update_mem _ ?L _ _ = Some _ |- _ ] =>
        assert (Hstack :
                  exists Sstack' Sp' Sh' S',
                    SplitStoreTypings [Sp'; Sh'] S' /\
                    SplitStoreTypings [S; Sh'] Sh /\
                    SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' /\
                    SplitStoreTypings [S; {| InstTyp:=InstTyp Sh; UnrTyp:=UnrTyp Sh; LinTyp:=(M.add (N.succ_pos L) (ArrayType (QualT Unit Unrestricted)) (M.empty HeapType)) |}] Sstack')
      end.
      { eapply SplitStoreTypings_LinInstruction; eauto. }

      destruct Hstack as [Sstack' [Sp' [Sh' [S']]]].
      destructAll.

      assert (Hinst : InstTyp Sp = InstTyp Sp') by solve_inst_or_unr_typ_eq.
      assert (Hunr : UnrTyp Sp = UnrTyp Sp') by solve_inst_or_unr_typ_eq.

      match goal with
      | [ H : HasTypeInstruction _ _ _ ?L _ _ _ |- _ ] =>
        exists Sp', Sh', Sstack', Ss, L
      end.
      split.
      { eapply HasTypeStore_LinInstruction; eauto. }
            
      split; [ | split; [ | split; [ | split; [ | split ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite (eq_sym Hunr).
         rewrite Heq.
         eauto.
      -- rewrite app_assoc.
         rewrite app_assoc.
         eapply FrameTyp.
         --- reflexivity.
         --- rewrite Forall_app; split;
               [ | destruct F; subst; simpl in *; eauto ].
             prepare_Forall.
             eapply QualLeq_Trans; [ eauto | ].
             destruct F; subst; simpl in *.
             rewrite get_set_hd in *.
             auto.
         --- eapply QualLeq_Trans; [ eauto | ].
             destruct F; subst; simpl in *.
             rewrite get_set_hd in *.
             auto.
         --- match goal with
             | [ |- context[[?A; ?B; ?C; ?D]] ] =>
               replace [A; B; C; D] with ([A; B; C] ++ [D]) by ltac:(simpl; congruence)
             end.
             match goal with
             | [ H : HasTypeValue ?SP empty_Function_Ctx _ _,
                 H' : update_mem _ ?L _ _ = Some _,
                 H'' : map_util.M.is_empty (LinTyp ?S2) = true |- _ ] =>
               assert (Hstack2 :
                         exists S,
                           SplitStoreTypings [SP; {| InstTyp:=InstTyp Sh; UnrTyp:=UnrTyp Sh; LinTyp:=(M.add (N.succ_pos L) (ArrayType (QualT Unit Unrestricted)) (M.empty HeapType)) |}] S /\
                           SplitStoreTypings [S; S2] Sstack')
             end.
             { match goal with
               | [ |- context[_ /\ SplitStoreTypings [_; _] ?S] ] =>
                 exists S
               end.
               split; auto.
               constructor.
               - constructor; eauto.
                 constructor; eauto.
                 split; solve_inst_or_unr_typ_eq.
               - simpl.
                 apply SplitHeapTypings_EmptyHeapTyping_r.
                 auto. }
             destruct Hstack2.
             destructAll.
             eapply ConsTyp.
             ---- eauto.
             ---- match goal with
                  | [ |- context[[?A; ?B; ?C]] ] =>
                    replace [A; B; C] with ([A; B] ++ [C]) by ltac:(simpl; congruence)
                  end.
                  match goal with
                  | [ |- HasTypeInstruction ?S _ _ _ _ _ _ ] =>
                    eapply (ConsTyp _ S (empty_LinTyp Sstack))
                  end.
                  ----- match goal with
                        | [ |- context[[?S1; empty_LinTyp ?S2]] ] =>
                          let H := fresh "H" in
                          assert (H : empty_LinTyp S2 = empty_LinTyp S1);
                          [ destruct S1; destruct S2 | rewrite H ]
                        end.
                        { simpl.
                          match goal with
                          | [ |- {| InstTyp := ?IT1; LinTyp := _; UnrTyp := ?UT1 |} = {| InstTyp := ?IT2; LinTyp := _; UnrTyp := ?UT2 |} ] =>
                            let H := fresh "H" in
                            let H' := fresh "H" in
                            assert (H : IT1 = IT2) by solve_inst_or_unr_typ_eq;
                            assert (H' : UT1 = UT2) by solve_inst_or_unr_typ_eq;
                            rewrite H; rewrite H'
                          end.
                          auto. }                          
                        eapply SplitStoreTypings_EmptyHeapTyping_r.
                  ----- match goal with
                        | [ |- context[[?A; ?B]] ] =>
                          replace [A; B] with ([A] ++ [B]) by ltac:(simpl; congruence)
                        end.
                        match goal with
                        | [ H : SplitStoreTypings [?S1; ?S2] x7 |- _ ] =>
                          eapply (ConsTyp _ S1 S2)
                        end.
                        ------ assumption.
                        ------ match goal with
                               | [ |- context[Arrow ?A _] ] =>
                                 replace A with (A ++ []) at 1 by apply app_nil_r
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- apply Forall_trivial.
                                       let t := fresh "t" in
                                       intro t; destruct t.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- eapply ValTyp.
                                       2:{ destruct F; subst; simpl in *; solve_lcvs. }
                                       eapply HasTypeValue_empty_function_ctx.
                                       eassumption.
                                       destruct F; simpl in *.
                                       constructor; simpl; destruct Hempty; eauto.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                        ------ match goal with
                               | [ |- context[Arrow (?TS ++ ?A) _] ] =>
                                 replace (TS ++ A) with ((TS ++ A) ++ []) at 1 by apply app_nil_r
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- apply Forall_trivial.
                                       let t := fresh "t" in
                                       intro t; destruct t.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- eapply ValTyp.
                                       eapply (RefTypLin _ _ _ _ (ArrayType (QualT Unit Unrestricted))).
                                       -------- simpl.
                                                unfold eq_map.
                                                intros.
                                                reflexivity.
                                       -------- eapply QualLeq_Refl.
                                       -------- constructor; try econstructor; eauto.
                                                --------- constructor; econstructor; eauto.
                                                --------- eapply QualLeq_Refl.
                                       -------- destruct F; subst; simpl in *; solve_lcvs.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                                       constructor; auto.
                                       match goal with
                                       | [ H : Forall (TypeValid _) ?L,
                                           H' : nth_error ?L _ = Some _ |- _ ] =>
                                         rewrite Forall_forall in H;
                                         apply nth_error_In in H';
                                         specialize (H _ H')
                                       end.
                                       apply TypeValid_empty_ctx; auto.                                    
                  ----- eapply FrameTyp.
                        ------ reflexivity.
                        ------ apply Forall_trivial.
                               let t := fresh "t" in
                               intro t; destruct t.
                               apply QualLeq_Top.
                        ------ apply QualLeq_Top.
                        ------ match goal with
                               | [ |- HasTypeInstruction ?S ?C ?F ?L ?ES (Arrow [QualT (RefT _ ?LOC ?T) _] _) _ ] =>
                                 assert (Hhti : HasTypeInstruction S C F L [Free] (EmptyRes (QualT (RefT W LOC T) Linear)) L)
                               end.
                               { eapply FreeTyp.
                                 - unfold empty_LinTyp; destruct Sstack.
                                   simpl.
                                   auto.
                                 - destruct F; subst; simpl in *; eauto.
                                   eapply QualLeq_Refl.
                                 - destruct F; subst; simpl in *; eauto.
                                   econstructor; eauto.
                                 - constructor.
                                   eapply QualLeq_Refl.
                                 - destruct F; subst; simpl in *; solve_lcvs.
                                 - constructor.
                                   -- econstructor; eauto.
                                   -- econstructor; eauto.
                                   -- constructor.
                                      --- constructor.
                                          econstructor; eauto.
                                      --- apply QualLeq_Refl. }
                               unfold EmptyRes in Hhti.
                               eassumption.
                        ------ destruct F; subst; simpl in *; solve_tvs.
                               constructor; auto.
                               match goal with
                               | [ H : Forall (TypeValid _) ?L,
                                   H' : nth_error ?L _ = Some _ |- _ ] =>
                                 rewrite Forall_forall in H;
                                 apply nth_error_In in H';
                                 specialize (H _ H')
                               end.
                               apply TypeValid_empty_ctx; auto.
             ---- rewrite app_nil_r.
                  assert (taus = tausv).
                  { match goal with
                    | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                      inversion H; subst
                    end.
                    match goal with
                    | [ H : VariantType _ = VariantType _ |- _ ] =>
                      inversion H; subst
                    end.
                    (* Use eq_map to show get_heaptype assertion *)
                    match goal with
                    | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] => 
                      assert (Hght : get_heaptype L LT = Some T)
                    end.
                    { match goal with
                      | [ H : eq_map _ _ |-
                          get_heaptype ?L _ = _] =>
                        rewrite (H L)
                      end.
                      unfold get_heaptype.
                      rewrite typing.M.gss.
                      eauto. }
                    (* LinTyp x4 is a subset of LinTyp Sstack is a subset of LinTyp Sp *)
                    match goal with
                    | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] => 
                      assert (HghtSp : get_heaptype L (LinTyp Sp) = Some T)
                    end.
                    { match goal with
                      | [ H : SplitStoreTypings ?SS Sstack |- _ ] =>
                        specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=Sstack) Hght)
                      end.
                      match goal with
                      | [ |- (?A -> ?B -> _) -> _ ] =>
                        let H1 := fresh "H" in
                        let H2 := fresh "H" in
                        let H3 := fresh "H" in
                        assert (H1 : A);
                          [ constructor; eauto
                          | assert (H2 : B);
                            [ eauto
                            | intro H3;
                              specialize (H3 H1 H2); 
                              specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=Sstack :: S_ignore ++ Ss) (S2:=Sp) H3) ] ]
                      end.
                      match goal with
                      | [ |- (?A -> ?B -> _) -> _ ] =>
                        let H1 := fresh "H" in
                        let H2 := fresh "H" in
                        let H3 := fresh "H" in
                        assert (H1 : A);
                          [ constructor; eauto
                          | assert (H2 : B);
                            [ eauto
                            | intro H3;
                              specialize (H3 H1 H2) ] ]
                      end.
                      eauto. }
                    (* Sp and Sh are disjoint *)
                    match goal with
                    | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] => 
                      assert (HnghtSh : forall x, get_heaptype L (LinTyp Sh) = Some x -> False)
                    end.
                    { intros.
                      match goal with
                      | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
                        inversion H
                      end.
                      simpl in *.
                      match goal with
                      | [ H : SplitHeapTypings [LinTyp Sp; LinTyp Sh] _ |- _ ] =>
                        inversion H
                      end.
                      unfold get_heaptype in *.
                      match goal with
                      | [ H : _ <--> _ |- _ ] =>
                        inversion H
                      end.
                      match goal with
                      | [ H : _ \subset (Dom_ht (LinTyp S)),
                          H' : M.find (N.succ_pos ?L) (LinTyp Sh) = _ |- _ ] =>
                        specialize (H L)
                      end.
                      match goal with
                      | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
                        let H' := fresh "H" in
                        assert (H' : A); [ | specialize (H H') ]
                      end.
                      { unfold Ensembles.In.
                        unfold Dom_ht.
                        simpl.
                        constructor.
                        unfold Ensembles.In.
                        unfold Dom_map.
                        eexists; eauto. }
                      unfold Ensembles.In in *.
                      unfold Dom_ht in *.
                      unfold Ensembles.In in *.
                      unfold Dom_map in *.
                      destructAll.
                      match goal with
                      | [ H : forall _ _, M.find (N.succ_pos _) (LinTyp S) = _ -> _,
                          H' : M.find (N.succ_pos ?L) (LinTyp S) = Some ?T |- _ ] =>
                        specialize (H L T H'); inversion H; subst; simpl in *
                      end.
                      1:
                        match goal with
                        | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                      all: unfold get_heaptype in *.
                      all:
                        match goal with
                        | [ H : ?A = Some _, H' : ?A = None |- _ ] => rewrite H in H'; inversion H'
                        end. }
                    match goal with
                    | [ H : _ \/ _ |- _ ] => case H
                    end.
                    { intro Hbad.
                      specialize (HnghtSh _ Hbad).
                      exfalso.
                      assumption. }
                    intro Hx.
                    rewrite HghtSp in Hx.
                    inversion Hx; subst.
                    auto. }

                  subst.
                  match goal with
                  | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
                    inversion H; subst
                  end.
                  match goal with
                  | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                    rewrite H in H'; inversion H'; subst
                  end.
                  eapply ChangeEndLocalTyp.
                  { destruct F; subst; simpl in *; eauto. }
                  eapply ChangeBegLocalTyp.
                  { destruct F; subst; simpl in *.
                    eapply LCEffEqual_sym; eauto. }
                  eapply BlockTyp.
                  ----- match goal with
                        | [ H : Forall2 _ ?L1 _,
                            H' : nth_error ?L1 _ = Some ?ES
                            |- HasTypeInstruction _ _ _ _ ?ES _ _ ] =>
                          specialize (forall2_args_1 _ _ _ _ _ H H')
                        end.
                        intro Hhti.
                        destructAll.
                        destruct F; subst; simpl in *.
                        match goal with
                        | [ H : VariantType _ = VariantType _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        match goal with
                        | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                          rewrite H in H'; inversion H'; subst
                        end.
                        rewrite set_set_hd in *.
                        eapply ChangeEndLocalTyp.
                        { simpl.
                          eapply LCEffEqual_sym; eauto. }
                        eauto.
                  ----- destruct F; subst; simpl in *.
                        eapply LCEffEqual_trans; eauto.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- rewrite (eq_sym Hinst); eauto.
      -- split; eauto.
         rewrite Hunr.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* ArrayGet *)
      match goal with
      | [ H : context[[Val ?V1; Val ?V2; ?C]] |- _ ] =>
        replace [Val V1; Val V2; C] with ([Val V1; Val V2] ++ [C]) in H by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ArrayGet] _ _ |- _ ] =>
        show_tlvs H; apply ArrayGet_HasTypeInstruction in H
      end.
      destructAll.

      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ H : context[[Val ?V1; Val ?V2]] |- _ ] =>
           replace [Val V1; Val V2] with ([Val V1] ++ [Val V2]) in H by ltac:(simpl; congruence);
           specialize (composition_typing_single _ _ _ _ _ _ _ _ _ H)
         end.
         intro Hb.
         destructAll.
         repeat match goal with
         | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
           show_tlvs H; apply Val_HasTypeInstruction in H
         end.
         destructAll.
         match goal with
         | [ H : ?A ++ [?B; ?G] = ?C ++ (?E ++ [?D]) ++ [?F] |- _ ] =>
           assert (Heq3 : A = C ++ E /\ B = D /\ G = F);
             [ assert (subgoal : A ++ [B] = C ++ E ++ [D] /\ G = F) | ]
         end.
         { apply app_inj_tail_iff.
           repeat rewrite app_assoc_reverse.
           simpl.
           repeat rewrite app_assoc_reverse in *.
           simpl in *.
           auto. }
         { destructAll.
           rewrite (iff_sym (and_assoc _ _ _)).
           split; eauto.
           apply app_inj_tail_iff.
           rewrite app_assoc_reverse.
           auto. }
         destructAll.

         match goal with
         | [ |- context[Arrow (?A ++ ?B ++ ?C) (?A ++ (?B ++ ?C) ++ ?D)] ] =>
           replace (A ++ B ++ C) with ((A ++ B ++ C) ++ []) by ltac:(rewrite app_nil_r; auto);
           replace (A ++ (B ++ C) ++ D) with ((A ++ B ++ C) ++ D) by ltac:(repeat rewrite app_assoc_reverse; auto)
         end.
         eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intro qt.
             destruct qt.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- match goal with
             | [ |- context[[Val ?V1; Val ?V2]] ] =>
               replace [Val V1; Val V2] with ([Val V1] ++ [Val V2]) by ltac:(simpl; auto)
             end.
             eapply ConsTyp.
             ---- match goal with
                  | [ H : SplitStoreTypings [?S1; _] Sstack,
                      H' : SplitStoreTypings ?SS ?S1 |- _ ] =>
                    assert (Hsplit' : SplitStoreTypings SS Sstack)
                  end.
                  (* Use the fact that Sstack splits into x4 and x5, x5 has empty LinTyp, and x4 splits into x14 and x15 to prove Sstack splits into x14 and x15 *)
                  { eapply SplitStoreTypings_trans; [ eauto | ].
                    match goal with
                    | [ H : SplitStoreTypings ?SS ?S
                        |- SplitStoreTypings ?SSP ?S ] =>
                      let H' := fresh "H" in
                      assert (H' : SSP = remove_nth SS 1) by ltac:(simpl; auto);
                      rewrite H'
                    end.
                    eapply SplitStoreTypings_remove_empty; auto.
                    - simpl; eauto.
                    - auto. }
                  eassumption.
             ---- eapply ValTyp.
                  ----- apply HasTypeValue_update_linear_ctx.
                        eassumption.
                  ----- destruct F; subst; simpl in *; solve_lcvs.
             ---- match goal with
                  | [ |- context[Arrow [?A] [?A; ?B]] ] =>
                    replace [A] with ([A] ++ []) by ltac:(simpl; auto);
                    replace [A; B] with ([A] ++ [B]) by ltac:(simpl; auto)
                  end.
                  eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
                  ----- reflexivity.
                  ----- apply Forall_trivial.
                        intro qt.
                        destruct qt.
                        apply QualLeq_Top.
                  ----- apply QualLeq_Top.
                  ----- eapply ChangeEndLocalTyp.
                        { destruct F; subst; simpl in *; eauto. }
                        eapply ChangeEndLocalTyp.
                        { destruct F; subst; simpl in *; eauto. }
                        eapply ChangeEndLocalTyp.
                        { destruct F; subst; simpl in *; eauto. }
                        eapply ValTyp.
                        apply HasTypeValue_update_linear_ctx.
                        apply HasTypeValue_update_linear_ctx.
                        unfold get_mem in *.
                        match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                          inversion H; subst
                        end.
                        ------ inversion Hst.
                               subst.
                               match goal with
                               | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : get _ _ _ = Some _ |- _ ] =>
                                 specialize (get_implies_in_to_list _ _ _ _ _ H)
                               end.
                               intro Hne.
                               destructAll.

                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hne2.
                               destructAll.

                               match goal with
                               | [ H : HasHeapType ?S _ _ _ |- _ ] =>
                                 assert (Hinstunr : UnrTyp S = UnrTyp Sh /\ InstTyp S = InstTyp Sh)
                               end.
                               { eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                 apply in_or_app; right.
                                 eapply nth_error_In; eauto. }

                               match goal with
                               | [ H : HasTypeValue ?S _ (Ref (LocP _ _)) _,
                                   H' : HasHeapType ?S2 _ _ _ |- _ ] =>
                                 assert (Hunr_eq : UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ |- ?A = _ ] =>
                                   assert (Hunr_eq' : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                 end.
                                 destructAll.
                                 eapply eq_trans; eauto. }

                               match goal with
                               | [ H : get_heaptype ?L ?A = Some _,
                                   H' : get_heaptype ?L ?B = Some _,
                                   H'' : ?A = ?B |- _ ] =>
                                 rewrite H'' in H;
                                 rewrite H in H';
                                 inversion H'; subst
                               end.
                               match goal with
                               | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.

                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _,
                                   H'' : context[Array (length ?L2) ?L2] |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hhtv.
                               destructAll.

                               match goal with
                               | [ H : HasTypeValue ?S _ ?V ?T
                                   |- HasTypeValue ?S2 _ ?V ?T ] =>
                                 assert (Hinstunr : InstTyp S = InstTyp S2 /\ UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ |- _ = ?A /\ _ ] =>
                                   assert (Hinst1 : A = InstTyp Sh) by solve_inst_or_unr_typ_eq
                                 end.
                                 rewrite Hinst1.
                                 match goal with
                                 | [ |- _ /\ _ = ?A ] =>
                                   assert (Hunr1 : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                 end.
                                 rewrite Hunr1.
                                 match goal with
                                 | [ H : SplitStoreTypings _ ?S,
                                     H' : InstTyp ?S = ?A,
                                     H'' : UnrTyp ?S = ?B
                                     |- _ = ?A /\ _ = ?B ] =>
                                   rewrite <-H'; rewrite <-H''
                                 end.
                                 apply and_comm.
                                 eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                 eapply nth_error_In; eauto. }
                               destructAll.

                               apply HasTypeValue_empty_function_ctx; try assumption.
                               eapply HasTypeValue_same_envs; try eassumption.
                               apply eq_map_empty; try assumption.
                               all:
                                 match goal with
                                 | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
                                   inversion H; subst
                                 end.
                               all: try assumption.
                               eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                        ------ inversion Hst.
                               subst.
                               match goal with
                               | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : get _ _ _ = Some _ |- _ ] =>
                                 specialize (get_implies_in_to_list _ _ _ _ _ H)
                               end.
                               intro Hne.
                               destructAll.
                               
                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hne2.
                               destructAll.

                               (* Use eq_map to show get_heaptype assertion *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                 assert (Hght : get_heaptype L LT = Some T)
                               end.
                               { match goal with
                                 | [ H : eq_map _ _ |-
                                     get_heaptype ?L _ = _] =>
                                   rewrite (H L)
                                 end.
                                 unfold get_heaptype.
                                 rewrite typing.M.gss.
                                 eauto. }
                               (* LinTyp x14 is a subset of LinTyp x4 is a subset of LinTyp Sstack is a subset of LinTyp Sp *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                 assert (HghtSp : get_heaptype L (LinTyp Sp) = Some T)
                               end.
                               { match goal with
                                 | [ H : get_heaptype _ (LinTyp ?S1) = Some _,
                                     H' : SplitStoreTypings [?S1; ?S2] ?S |- _ ] =>
                                   specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=[S1; S2]) (S2:=S) Hght)
                                 end.
                                 match goal with
                                 | [ |- (?A -> ?B -> _) -> _ ] =>
                                   let H1 := fresh "H" in
                                   let H2 := fresh "H" in
                                   let H3 := fresh "H" in
                                   assert (H1 : A);
                                     [ constructor; eauto
                                     | assert (H2 : B);
                                       [ eauto
                                       | intro H3;
                                         specialize (H3 H1 H2);
                                         match goal with
                                         | [ H : SplitStoreTypings ?SS Sstack |- _ ] =>
                                           specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=Sstack) H3)
                                         end ] ]
                                 end.
                                 match goal with
                                 | [ |- (?A -> ?B -> _) -> _ ] =>
                                   let H1 := fresh "H" in
                                   let H2 := fresh "H" in
                                   let H3 := fresh "H" in
                                   assert (H1 : A);
                                     [ constructor; eauto
                                     | assert (H2 : B);
                                       [ eauto
                                       | intro H3;
                                         specialize (H3 H1 H2); 
                                         specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=(Sstack :: S_ignore ++ Ss)) (S2:=Sp) H3) ] ]
                                 end.
                                 match goal with
                                 | [ |- (?A -> ?B -> _) -> _ ] =>
                                   let H1 := fresh "H" in
                                   let H2 := fresh "H" in
                                   let H3 := fresh "H" in
                                   assert (H1 : A);
                                     [ constructor; eauto
                                     | assert (H2 : B);
                                       [ eauto
                                       | intro H3;
                                         specialize (H3 H1 H2) ] ]
                                 end.
                                 eauto. }
                               (* Sp and Sh are disjoint *)
                               match goal with
                               | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?T _) |- _ ] =>
                                 assert (HnghtSh : forall x, get_heaptype L (LinTyp Sh) = Some x -> False)
                               end.
                               { intros.
                                 match goal with
                                 | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
                                   inversion H
                                 end.
                                 simpl in *.
                                 match goal with
                                 | [ H : SplitHeapTypings [LinTyp Sp; LinTyp Sh] _ |- _ ] =>
                                   inversion H
                                 end.
                                 unfold get_heaptype in *.
                                 match goal with
                                 | [ H : _ <--> _ |- _ ] =>
                                   inversion H
                                 end.
                                 match goal with
                                 | [ H : _ \subset (Dom_ht (LinTyp S)),
                                     H' : M.find (N.succ_pos ?L) (LinTyp Sh) = _ |- _ ] =>
                                   specialize (H L)
                                 end.
                                 match goal with
                                 | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
                                   let H' := fresh "H" in
                                   assert (H' : A); [ | specialize (H H') ]
                                 end.
                                 { unfold Ensembles.In.
                                   unfold Dom_ht.
                                   simpl.
                                   constructor.
                                   unfold Ensembles.In.
                                   unfold Dom_map.
                                   eexists; eauto. }
                                 unfold Ensembles.In in *.
                                 unfold Dom_ht in *.
                                 unfold Ensembles.In in *.
                                 unfold Dom_map in *.
                                 destructAll.
                                 match goal with
                                 | [ H : forall _ _, M.find (N.succ_pos _) (LinTyp S) = _ -> _,
                                     H' : M.find (N.succ_pos ?L) (LinTyp S) = Some ?T |- _ ] =>
                                   specialize (H L T H'); inversion H; subst; simpl in *
                                 end.
                                 1:
                                   match goal with
                                   | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                                     inversion H; subst; simpl in *
                                   end.
                                 all: unfold get_heaptype in *.
                                 all:
                                   match goal with
                                   | [ H : ?A = Some _, H' : ?A = None |- _ ] => rewrite H in H'; inversion H'
                                   end. }
                               match goal with
                               | [ H : _ \/ _ |- _ ] => case H
                               end.
                               { intro Hbad.
                                 specialize (HnghtSh _ Hbad).
                                 exfalso.
                                 assumption. }
                               intro Hx3.
                               rewrite HghtSp in Hx3.
                               inversion Hx3; subst.

                               match goal with
                               | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H : Forall2 _ _ ?L2,
                                   H' : nth_error ?L2 _ = Some _,
                                   H'' : context[Array (length ?L2) ?L2] |- _ ] =>
                                 specialize (forall2_args_2 _ _ _ _ _ H H')
                               end.
                               intro Hhtv.
                               destructAll.

                               match goal with
                               | [ H : HasTypeValue ?S _ ?V ?T
                                   |- context[HasTypeValue _ _ ?V ?T] ] =>
                                 assert (Hempty2 : M.is_empty (LinTyp S) = true)
                               end.
                               { eapply HasTypeValue_Unrestricted_LinEmpty; try eassumption.
                                 simpl; auto. }

                               match goal with
                               | [ H : SplitStoreTypings ?SS ?S,
                                   H' : nth_error ?SS _ = Some _ |- _ ] =>
                                 assert (Hinstunr' : UnrTyp S = UnrTyp Sh /\ InstTyp S = InstTyp Sh)
                               end.
                               { eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                 apply in_or_app; left.
                                 eapply nth_error_In; eauto. }
                               destructAll.

                               match goal with
                               | [ H : HasTypeValue ?S _ ?V ?T
                                   |- context[HasTypeValue ?S2 _ ?V ?T] ] =>
                                 assert (Hinstunr : InstTyp S = InstTyp S2 /\ UnrTyp S = UnrTyp S2)
                               end.
                               { match goal with
                                 | [ |- _ = ?A /\ _ ] =>
                                   assert (Hinst1 : A = InstTyp Sh) by solve_inst_or_unr_typ_eq
                                 end.
                                 rewrite Hinst1.
                                 match goal with
                                 | [ |- _ /\ _ = ?A ] =>
                                   assert (Hunr1 : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                 end.
                                 rewrite Hunr1.
                                 match goal with
                                 | [ H : SplitStoreTypings _ ?S,
                                     H' : InstTyp ?S = ?A,
                                     H'' : UnrTyp ?S = ?B
                                     |- _ = ?A /\ _ = ?B ] =>
                                   rewrite <-H'; rewrite <-H''
                                 end.
                                 rewrite and_comm.
                                 eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                 eapply nth_error_In; eauto. }
                               
                               destructAll.

                               apply HasTypeValue_empty_function_ctx.
                               eapply HasTypeValue_same_envs; try eassumption.
                               apply eq_map_empty; try assumption.
                               match goal with
                               | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
                                 inversion H; subst
                               end.
                               all: assumption.
                        ------ destruct F; subst; simpl in *; solve_lcvs.
                  ----- destruct F; subst; simpl in *; solve_tvs.
         --- solve_tvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* ArrayGet - Trap *)
      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- specialize (HasTypeInstruction_local_is_tl _ _ _ _ _ _ _ Hi).
         intro Htl.
         destructAll.
         eapply ChangeEndLocalTyp; eauto.
         show_tlvs Hi.
         eapply TrapTyp; auto.
         solve_lcvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* ArraySet *)
      match goal with
      | [ H : context[[Val ?V1; Val ?V2; Val ?V3; ?C]] |- _ ] =>
        replace [Val V1; Val V2; Val V3; C] with ([Val V1; Val V2; Val V3] ++ [C]) in H by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ArraySet] _ _ |- _ ] =>
        show_tlvs H; apply ArraySet_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : context[[Val ?V1; Val ?V2; Val ?V3]] |- _ ] =>
        replace [Val V1; Val V2; Val V3] with ([Val V1; Val V2] ++ [Val V3]) in H by ltac:(simpl; congruence);
        specialize (composition_typing_single _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hb.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val ?V1; Val ?V2] _ _ |- _ ] =>
        replace [Val V1; Val V2] with ([Val V1] ++ [Val V2]) in H by ltac:(simpl; congruence);
        specialize (composition_typing_single _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hc.
      destructAll.
      repeat match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      simpl in *; destructAll.
      
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- destruct Hst.
         econstructor; eauto.
         --- match goal with
             | [ H : update_mem ?S _ _ _ = Some ?ST |- _ ] =>
                assert (Hinst_st' : inst S = inst ST);
                [ destruct S; simpl in *;
                  unfold update_mem in H; simpl in H;
                  match type of H with
                  | context[set ?A ?B ?C ?D] => destruct (set A B C D)
                  end;
                  inversion H; simpl; auto | ]
             end.
             match goal with
             | [ H : update_mem ?S _ _ _ = Some _,
                 H' : if qualconstr_eq_dec ?M _ then ?SP = _ else _ = ?SP |- _ ] =>
               assert (Hinst_s' : inst S = inst SP);
               [ destruct M; simpl in *; subst; auto | ]
             end.
             { match goal with
               | [ |- _ = _ (_ _ _ ?A ?B) ] =>
                 unfold update_out_set;
                 destruct (L.has_urn_ptr_HeapValue B);
                 destruct (L.has_urn_ptr_HeapValue A); simpl; auto
               end. }
             rewrite <-Hinst_s'.
             auto.
         --- match goal with
             | [ H : HasTypeMeminst _ _ _ |- _ ] =>
               inversion H; subst
             end.
             
             assert (Hsubgoal : exists S_lin' S_unr',
                     Forall2
                       (fun (S0 : StoreTyping) '(loc, hv, len) =>
                        exists ht : HeapType,
                          NoCapsHeapType [] ht = true /\
                          (get_heaptype loc (LinTyp Sh) = Some ht \/
                           get_heaptype loc (LinTyp Sprog) = Some ht) /\
                          HasHeapType S0 empty_Function_Ctx hv ht /\
                          RoomForStrongUpdates len ht /\
                          HeapTypeValid empty_Function_Ctx ht) S_lin'
                       (M.to_list Linear (meminst s')) /\
                     Forall2
                       (fun (S0 : StoreTyping) '(loc, hv, len) =>
                        exists ht : HeapType,
                          NoCapsHeapType [] ht = true /\
                          get_heaptype loc (UnrTyp S0) = Some ht /\
                          HasHeapType S0 empty_Function_Ctx hv ht /\
                          RoomForStrongUpdates len ht /\
                          HeapTypeValid empty_Function_Ctx ht) S_unr'
                       (M.to_list Unrestricted (meminst s')) /\
                     Forall
                       (fun S' : StoreTyping =>
                        InstTyp Sh = InstTyp S' /\ UnrTyp Sh = UnrTyp S')
                       (S_lin' ++ S_unr') /\
                     SplitHeapTypings (map LinTyp (S_lin' ++ S_unr')) (LinTyp Sh)).
             { unfold update_mem in *.
               match goal with
               | [ H : context[set ?A ?B ?C ?D] |- _ ] =>
                 remember (set A B C D) as o;
                   repeat match goal with
                   | [ H : context[o] |- _ ] => revert H
                   end
               end.
               case o; [ | intros H' H''; inversion H'' ].
               intros t H' H''.
               inversion H''; subst; simpl in *.

               derive_mappings f_lin f_unr.

               match goal with
               | [ H : get_mem _ ?L ?M = Some (?HV, ?SZ) |- _ ] =>
                 remember (map (fun '(loc, hv, len) => if (andb (is_linear M) (BinNatDef.N.eqb loc L)) then f_lin (L, HV, SZ) else f_lin (loc, hv, len)) (M.to_list Linear t)) as S_lin';
                 remember (map (fun '(loc, hv, len) => if (andb (negb (is_linear M)) (BinNatDef.N.eqb loc L)) then f_unr (L, HV, SZ) else f_unr (loc, hv, len)) (M.to_list Unrestricted t)) as S_unr'
               end.
               assert (Hperm : Permutation.Permutation (S_lin ++ S_unr) (S_lin' ++ S_unr')).
               { apply Permutation.Permutation_app.
                 all: destructAll; subst.
                 all: unfold get_mem in *.
                 all: eapply Permutation_StoreTypings; eauto.
                 all: intros.
                 all:
                   destruct m; simpl;
                   match goal with
                   | [ X : _ * _ * _ |- _ ] =>
                     destruct X as [[curLoc curHV] curSz]
                   end;
                   eauto.
                 all: rewrite N.eqb_sym.
                 all:
                   match goal with
                   | [ |- context[(?L1 =? ?L2)%N] ] =>
                     remember (L1 =? L2)%N as loceqb;
                     revert Heqloceqb;
                     case loceqb; intros; auto
                   end.
                 all:
                   assert (Hloc_eq : l1 = curLoc); [ | subst; auto ].
                 all:
                   rewrite (iff_sym (N.eqb_eq _ _)); eauto. }                               
               assert (Hm : meminst s' = t).
               { destruct m; simpl in *; subst.
                 - simpl; auto.
                 - unfold update_out_set.
                   case (L.has_urn_ptr_HeapValue (Array i (set_nth vs0 j v))).
                   all: case (L.has_urn_ptr_HeapValue (Array i vs0)).
                   all: simpl; auto. }

               exists S_lin', S_unr'; destructAll; subst.
               split; [ | split; [ | split ] ].
               - (* Use In x (to_list Linear (meminst s)) -> ... hypothesis *)
                 apply Forall2_map_l_strong.
                 intros.
                 match goal with
                 | [ H : In ?X (M.to_list _ _) |- _ ] =>
                   apply In_nth_error in H;
                   destructAll;
                   destruct X as [[l' hv] ln];
                   apply in_to_list_implies_get in H
                 end.
                 destruct m; subst; simpl in *.
                 -- assert (Hneq : Unrestricted <> Linear) by solve_ineqs.
                    match goal with
                    | [ H : Some _ = set _ _ _ _,
                        H' : get ?L _ _ = Some (_, _) |- _ ] =>
                      specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H) Hneq)
                    end.
                    intros.
                    match goal with
                    | [ H : ?A = _, H' : ?B = ?A |- _ ] =>
                      rewrite <-H' in H;
                      specialize (get_implies_in_to_list _ _ _ _ _ H)
                    end.
                    intros; destructAll.
                    match goal with
                    | [ H : forall _, In _ ?L -> _,
                        H' : nth_error ?L _ = Some _ |- _ ] =>
                      apply nth_error_In in H';
                      specialize (H _ H')
                    end.
                    simpl in *; eauto.
                 -- assert (Hloc_eq : l1 = l' \/ l1 <> l').
                    { apply eq_dec_N. }
                    case Hloc_eq.
                    --- intros; subst.
                        rewrite N.eqb_refl.
                        match goal with
                        | [ H : _ = _ ++ [?A; ?B; ?C] |- _ ] =>
                          assert (Heq1' : [A; B; C] = (([A] ++ [B]) ++ [C])) by ltac:(simpl; auto);
                          rewrite Heq1' in H;
                          repeat rewrite app_assoc in H;
                          apply app_inj_tail in H;
                          let H' := fresh "H" in
                          destruct H as [H H'];
                          apply app_inj_tail in H;
                          let H'' := fresh "H" in
                          destruct H as [H H''];
                          apply app_inj_tail in H
                        end.
                        destructAll; subst.
                        match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        match goal with
                        | [ H : eq_map ?L (_ _ ?T _) |- _ ] =>
                          assert (Hght : get_heaptype l' L = Some T);
                            [ |
                              assert (Hght2 : get_heaptype l' (LinTyp Sprog) = Some T);
                              [ | 
                                assert (Hght3 : get_heaptype l' (LinTyp S) = Some T);
                                [ | assert (Hght4 : get_heaptype l' (LinTyp Sh) = None);
                                    [ |
                                      exists T ] ] ] ]
                        end.
                        { match goal with
                          | [ H : eq_map _ _ |- _ ] =>
                            unfold eq_map in H;
                            specialize (H l');
                            rewrite H
                          end.
                          unfold get_heaptype.
                          apply M.gss. }
                        { eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sstack)); [ | | eauto ].
                          - match goal with
                            | [ H : SplitStoreTypings [?S1; _] Sstack |- _ ] =>
                              eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); [ | | eauto ]
                            end.
                            -- match goal with
                               | [ H : SplitStoreTypings [?S1; _] ?S
                                   |- get_heaptype _ (LinTyp ?S) = Some _ ] =>
                                 eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); [ | | eauto ]
                               end.
                               --- match goal with
                                   | [ H : eq_map (LinTyp ?S) _ |- _ ] =>
                                     eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S)); [ | | eauto ]
                                   end.
                                   ---- auto.
                                   ---- constructor; eauto.
                               --- constructor; eauto.
                            -- constructor; eauto.
                          - constructor; eauto. }
                        { eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sprog)); [ | | eauto ].
                          - auto.
                          - constructor; eauto. }
                        { match goal with
                          | [ H : SplitStoreTypings [Sprog; Sh] _ |- _ ] => inversion H
                          end.
                          simpl in *.
                          match goal with
                          | [ H : SplitHeapTypings [LinTyp Sprog; _] _ |- _ ] => inversion H
                          end.
                          match goal with
                          | [ H : forall _ _, get_heaptype _ _ = Some _ -> _ |- _ ] => specialize (H _ _ Hght3)
                          end.
                          match goal with
                          | [ H : ExactlyInOne false _ _ _ |- _ ] => inversion H; subst
                          end.
                          - match goal with
                            | [ H : ExactlyInOne true _ _ _ |- _ ] => inversion H; auto
                            end.
                          - match goal with
                            | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                              rewrite H in H'; inversion H'
                            end. }
                        unfold get_mem in *.
                        match goal with
                        | [ H : get l' _ (meminst s) = Some (_, _) |- _ ] =>
                          specialize (get_implies_in_to_list _ _ _ _ _ H)
                        end.
                        intros [curIdx Hnth]; destructAll.
                        apply nth_error_In in Hnth.
                        match goal with
                        | [ H : forall _, In _ (M.to_list Linear _) -> _ |- _ ] => apply H in Hnth
                        end.
                        destruct Hnth as [ht'].
                        destructAll.
                        match goal with
                        | [ H : get_heaptype l' (LinTyp Sprog) = Some ?T |- _ ] =>
                          assert (Hht_eq : ht' = T)
                        end.
                        { match goal with
                          | [ H : get_heaptype _ _ = _ \/ _ |- _ ] => case H; intros
                          end.
                          - match goal with
                            | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                              rewrite H in H'; inversion H'
                            end.
                          - match goal with
                            | [ H : ?A = Some _, H' : ?A = Some ht' |- _ ] =>
                              rewrite H' in H; inversion H; auto
                            end. }
                        subst.
                        split; auto.
                        split; auto.
                        split; [ | split; [ | auto ] ].
                        ---- match goal with
                             | [ H : HasHeapType _ _ _ _ |- _ ] => inversion H; subst; simpl in *
                             end.
                             match goal with
                             | [ H : Some _ = set _ _ _ _ |- _ ] =>
                               specialize (get_set_same _ _ _ _ _ (eq_sym H))
                             end.
                             intros; destructAll.
                             match goal with
                             | [ H : ?A = Some (hv, _), H' : ?A = Some _ |- _ ] =>
                               rewrite H in H'; inversion H'; subst
                             end.
                             match goal with
                             | [ H : HasHeapType _ _ _ _ |- _ ] => inversion H; subst; simpl in *
                             end.
                             eapply ArrayHT; eauto.
                             ----- apply length_set_nth.
                             ----- match goal with
                                     [ H : Forall2 _ ?S _ |- context[?S] ] => specialize (Forall2_length _ _ _ H)
                                   end.
                                   intros.
                                   match goal with
                                   | [ |- Forall2 _ ?SS (set_nth _ ?IDX _ ) ] =>
                                     assert (Hnths : exists S, nth_error SS IDX = Some S)
                                   end.
                                   { apply nth_error_some_exists.
                                     match goal with
                                     | [ H : ?A = ?B |- _ < ?A ] => rewrite H
                                     end.
                                     auto. }
                                   let S := fresh "S" in destruct Hnths as [S Hnths].
                                   specialize (set_nth_nth_error _ _ _ Hnths).
                                   intro Hnth_eq.
                                   rewrite Hnth_eq.
                                   apply Forall2_set_nth; auto.
                                   match goal with
                                   | [ H : HasTypeValue _ _ ?V _
                                       |- HasTypeValue _ _ ?V _ ] =>
                                     apply HasTypeValue_empty_function_ctx_rev in H
                                   end.
                                   eapply HasTypeValue_StoreTyping_eq; eauto.
                                   2: auto.
                                   unfold StoreTyping_eq.
                                   match goal with
                                   | [ |- context[InstTyp ?A = _] ] =>
                                     assert (Hinst_eq : InstTyp A = InstTyp Sprog) by solve_inst_or_unr_typ_eq;
                                     assert (Hunr_eq : UnrTyp A = UnrTyp Sprog) by solve_inst_or_unr_typ_eq
                                   end.
                                   rewrite Hinst_eq.
                                   rewrite Hunr_eq.
                                   match goal with
                                   | [ H : SplitStoreTypings _ (f_lin ?TPL) |- context[_ = InstTyp ?A] ] =>
                                     assert (Hinst_eq2 : InstTyp A = InstTyp (f_lin TPL));
                                       [ | assert (Hunr_eq2 : UnrTyp A = UnrTyp (f_lin TPL)) ]
                                   end.
                                   1-2: apply nth_error_In in Hnths.
                                   1-2:
                                     match goal with
                                     | [ H : SplitStoreTypings ?SS _, H' : In ?S ?SS |- context[?S] ] =>
                                       specialize (SplitStoreTypings_eq_typs2 H H')
                                     end.
                                   1-2: intros; destructAll; auto.
                                   rewrite Hinst_eq2.
                                   rewrite Hunr_eq2.
                                   match goal with
                                   | [ H : SplitStoreTypings (?A ++ ?B) Sh |- context[f_lin ?TPL] ] =>
                                     assert (Hin : In (f_lin TPL) (A ++ B));
                                     [ |
                                       assert (Hinst_eq3 : InstTyp (f_lin TPL) = InstTyp Sh);
                                       [ |
                                         assert (Hunr_eq3 : UnrTyp (f_lin TPL) = UnrTyp Sh) ] ]
                                   end.
                                   { apply in_or_app.
                                     left.
                                     apply in_map.
                                     match goal with
                                     | [ H : get _ _ ?M = _ |- context[?M] ] =>
                                       specialize (get_implies_in_to_list _ _ _ _ _ H)
                                     end.
                                     intros Hnth_err.
                                     let j := fresh "j" in destruct Hnth_err as [j Hnth_err].
                                     apply nth_error_In in Hnth_err.
                                     auto. }
                                   1-2:
                                     match goal with
                                     | [ H : SplitStoreTypings ?SS _, H' : In ?S ?SS |- context[?S] ] =>
                                       specialize (SplitStoreTypings_eq_typs2 H H')
                                     end.
                                   1-2: intros; destructAll; auto.
                                   rewrite Hinst_eq3.
                                   rewrite Hunr_eq3.
                                   split; [ solve_inst_or_unr_typ_eq | split; [ | solve_inst_or_unr_typ_eq ] ].
                                   apply eq_map_empty.
                                   ------ eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                                   ------ match goal with
                                          | [ H : _ < _ |- _ ] =>
                                            apply nth_error_some_exists in H
                                          end.
                                          destructAll.
                                          match goal with
                                          | [ H : Forall2 _ ?SS ?VS,
                                              H' : nth_error ?SS _ = Some _,
                                              H'' : nth_error ?VS _ = Some _ |- _ ] =>
                                            specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
                                          end.
                                          intros; simpl in *.
                                          eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                        ---- constructor; auto.
                    --- intros.
                        match goal with
                        | [ H : Some _ = set _ _ _ _,
                            H' : _ <> _ |- _ ] =>
                          specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) H')
                        end.
                        intros.
                        match goal with
                        | [ H : ?A = _, H' : _ = ?A |- _ ] =>
                          rewrite <-H' in H;
                          apply get_implies_in_to_list in H;
                          destructAll;
                          apply nth_error_In in H
                        end.
                        match goal with
                        | [ H : forall _, In _ ?L -> _,
                            H' : In _ ?L |- _ ] =>
                          specialize (H _ H')
                        end.
                        simpl in *.
                        assert (Hneq : (l' =? l1)%N = false).
                        { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
                        rewrite Hneq.
                        simpl in *; eauto.
               - (* Use In x (to_list Unrestricted (meminst s)) -> ... hypothesis *)
                 apply Forall2_map_l_strong.
                 intros.
                 match goal with
                 | [ H : In ?X (M.to_list _ _) |- _ ] =>
                   apply In_nth_error in H;
                   destructAll;
                   destruct X as [[l' hv] ln];
                   apply in_to_list_implies_get in H
                 end.
                 destruct m; subst; simpl in *.
                 -- assert (Hloc_eq : l1 = l' \/ l1 <> l').
                    { apply eq_dec_N. }
                    case Hloc_eq.
                    --- intros; subst.
                        rewrite N.eqb_refl.
                        match goal with
                        | [ H : _ = _ ++ [?A; ?B; ?C] |- _ ] =>
                          assert (Heq1' : [A; B; C] = (([A] ++ [B]) ++ [C])) by ltac:(simpl; auto);
                          rewrite Heq1' in H;
                          repeat rewrite app_assoc in H;
                          apply app_inj_tail in H;
                          let H' := fresh "H" in
                          destruct H as [H H'];
                          apply app_inj_tail in H;
                          let H'' := fresh "H" in
                          destruct H as [H H''];
                          apply app_inj_tail in H
                        end.
                        subst.
                        match goal with
                        | [ H : HasTypeValue _ _ (Ref (LocP _ Unrestricted)) _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.
                        match goal with
                        | [ H : get_heaptype ?L (UnrTyp ?SP) = Some ?T |- _ ] =>
                          assert (Hunr_eq' : UnrTyp SP = UnrTyp S) by solve_inst_or_unr_typ_eq;
                          rewrite Hunr_eq' in H;
                          exists T
                        end.
                        unfold get_mem in *.
                        match goal with
                        | [ H : get l' _ (meminst s) = Some (_, _) |- _ ] =>
                          specialize (get_implies_in_to_list _ _ _ _ _ H)
                        end.
                        intros [curIdx Hnth]; destructAll.
                        apply nth_error_In in Hnth.
                        match goal with
                        | [ H : forall _, In _ (M.to_list Unrestricted _) -> _ |- _ ] => apply H in Hnth
                        end.
                        destruct Hnth as [ht'].
                        destructAll.
                        match goal with
                        | [ H : get_heaptype l' (UnrTyp ?A) = _ |- _ ] =>
                          assert (Hunr_eq2' : UnrTyp A = UnrTyp S);
                            [ | rewrite Hunr_eq2' in H ]
                        end.
                        { match goal with
                          | [ H : SplitStoreTypings (?A ++ ?B) Sh |- context[f_unr ?TPL] ] =>
                            assert (Hin : In (f_unr TPL) (A ++ B));
                            [ |
                              assert (Hunr_eq_sub : UnrTyp (f_unr TPL) = UnrTyp Sh) ]
                          end.
                          { apply in_or_app.
                            right.
                            apply in_map.
                            match goal with
                            | [ H : get _ _ ?M = _ |- context[?M] ] =>
                              specialize (get_implies_in_to_list _ _ _ _ _ H)
                            end.
                            intros Hnth_err.
                            let j := fresh "j" in destruct Hnth_err as [j Hnth_err].
                            apply nth_error_In in Hnth_err.
                            auto. }
                          { match goal with
                            | [ H : SplitStoreTypings ?SS _, H' : In ?S ?SS |- context[?S] ] =>
                              specialize (SplitStoreTypings_eq_typs2 H H')
                            end.
                            intros; destructAll; auto. }
                          rewrite Hunr_eq_sub.
                          solve_inst_or_unr_typ_eq. }
                        match goal with
                        | [ H : QualT _ _ = QualT _ _ |- _ ] =>
                          inversion H; subst; simpl in *
                        end.                        
                        match goal with
                        | [ H : ?A = Some (ArrayType _), H' : ?A = _ |- _ ] =>
                          rewrite H' in H; inversion H; subst
                        end.
                        split; auto.
                        split.
                        { unfold M.Loc in Hunr_eq2'.
                          unfold M.Val in Hunr_eq2'.
                          unfold Ptr.
                          rewrite Hunr_eq2'; auto. }
                        split; [ | split; [ | auto ] ].
                        ---- match goal with
                             | [ H : HasHeapType _ _ _ _ |- _ ] => inversion H; subst; simpl in *
                             end.
                             match goal with
                             | [ H : Some _ = set _ _ _ _ |- _ ] =>
                               specialize (get_set_same _ _ _ _ _ (eq_sym H))
                             end.
                             intros; destructAll.
                             match goal with
                             | [ H : ?A = Some (hv, _), H' : ?A = Some _ |- _ ] =>
                               rewrite H in H'; inversion H'; subst
                             end.
                             match goal with
                             | [ H : HasHeapType _ _ _ _ |- _ ] => inversion H; subst; simpl in *
                             end.
                             eapply ArrayHT; eauto.
                             ----- apply length_set_nth.
                             ----- match goal with
                                     [ H : Forall2 _ ?S _ |- context[?S] ] => specialize (Forall2_length _ _ _ H)
                                   end.
                                   intros.
                                   match goal with
                                   | [ |- Forall2 _ ?SS (set_nth _ ?IDX _ ) ] =>
                                     assert (Hnths : exists S, nth_error SS IDX = Some S)
                                   end.
                                   { apply nth_error_some_exists.
                                     match goal with
                                     | [ H : ?A = ?B |- _ < ?A ] => rewrite H
                                     end.
                                     auto. }
                                   let S := fresh "S" in destruct Hnths as [S Hnths].
                                   specialize (set_nth_nth_error _ _ _ Hnths).
                                   intro Hnth_eq.
                                   rewrite Hnth_eq.
                                   apply Forall2_set_nth; auto.
                                   subst.
                                   match goal with
                                   | [ H : HasTypeValue _ _ ?V _
                                       |- HasTypeValue _ _ ?V _ ] =>
                                     apply HasTypeValue_empty_function_ctx_rev in H
                                   end.
                                   eapply HasTypeValue_StoreTyping_eq; eauto.
                                   2: auto.
                                   unfold StoreTyping_eq.
                                   match goal with
                                   | [ |- context[InstTyp ?A = _] ] =>
                                     assert (Hinst_eq : InstTyp A = InstTyp Sprog) by solve_inst_or_unr_typ_eq;
                                     assert (Hunr_eq : UnrTyp A = UnrTyp Sprog) by solve_inst_or_unr_typ_eq
                                   end.
                                   rewrite Hinst_eq.
                                   rewrite Hunr_eq.
                                   match goal with
                                   | [ H : SplitStoreTypings _ (f_unr ?TPL) |- context[_ = InstTyp ?A] ] =>
                                     assert (Hinst_eq2 : InstTyp A = InstTyp (f_unr TPL));
                                       [ | assert (Hunr_eq2 : UnrTyp A = UnrTyp (f_unr TPL)) ]
                                   end.
                                   1-2: apply nth_error_In in Hnths.
                                   1-2:
                                     match goal with
                                     | [ H : SplitStoreTypings ?SS _, H' : In ?S ?SS |- context[?S] ] =>
                                       specialize (SplitStoreTypings_eq_typs2 H H')
                                     end.
                                   1-2: intros; destructAll; auto.
                                   rewrite Hinst_eq2.
                                   rewrite Hunr_eq2.
                                   match goal with
                                   | [ H : SplitStoreTypings (?A ++ ?B) Sh |- context[f_unr ?TPL] ] =>
                                     assert (Hin : In (f_unr TPL) (A ++ B));
                                     [ |
                                       assert (Hinst_eq3 : InstTyp (f_unr TPL) = InstTyp Sh);
                                       [ |
                                         assert (Hunr_eq3 : UnrTyp (f_unr TPL) = UnrTyp Sh) ] ]
                                   end.
                                   { apply in_or_app.
                                     right.
                                     apply in_map.
                                     match goal with
                                     | [ H : get _ _ ?M = _ |- context[?M] ] =>
                                       specialize (get_implies_in_to_list _ _ _ _ _ H)
                                     end.
                                     intros Hnth_err.
                                     let j := fresh "j" in destruct Hnth_err as [j Hnth_err].
                                     apply nth_error_In in Hnth_err.
                                     auto. }
                                   1-2:
                                     match goal with
                                     | [ H : SplitStoreTypings ?SS _, H' : In ?S ?SS |- context[?S] ] =>
                                       specialize (SplitStoreTypings_eq_typs2 H H')
                                     end.
                                   1-2: intros; destructAll; auto.
                                   rewrite Hinst_eq3.
                                   rewrite Hunr_eq3.
                                   split; [ solve_inst_or_unr_typ_eq | split; [ | solve_inst_or_unr_typ_eq ] ].
                                   apply eq_map_empty.
                                   ------ eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                                   ------ match goal with
                                          | [ H : _ < _ |- _ ] =>
                                            apply nth_error_some_exists in H
                                          end.
                                          destructAll.
                                          match goal with
                                          | [ H : Forall2 _ ?SS ?VS,
                                              H' : nth_error ?SS _ = Some _,
                                              H'' : nth_error ?VS _ = Some _ |- _ ] =>
                                            specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
                                          end.
                                          intros; simpl in *.
                                          eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                        ---- constructor; auto.
                    --- intros.
                        match goal with
                        | [ H : Some _ = set _ _ _ _,
                            H' : _ <> _ |- _ ] =>
                          specialize (get_set_other_loc _ _ _ _ _ _ (eq_sym H) H')
                        end.
                        intros.
                        match goal with
                        | [ H : ?A = _, H' : _ = ?A |- _ ] =>
                          rewrite <-H' in H;
                          apply get_implies_in_to_list in H;
                          destructAll;
                          apply nth_error_In in H
                        end.
                        match goal with
                        | [ H : forall _, In _ ?L -> _,
                            H' : In _ ?L |- _ ] =>
                          specialize (H _ H')
                        end.
                        simpl in *.
                        assert (Hneq : (l' =? l1)%N = false).
                        { rewrite OrdersEx.N_as_OT.eqb_neq; auto. }
                        rewrite Hneq.
                        simpl in *; eauto.
                 -- assert (Hneq : Linear <> Unrestricted).
                    { intro H''''; inversion H''''. }
                    match goal with
                    | [ H : get ?L _ _ = Some (_, _),
                        H' : Some _ = set _ _ _ _ |- _ ] =>
                      specialize (get_set_other_mem _ _ _ L _ _ _ (eq_sym H') Hneq)
                    end.
                    intros.
                    match goal with
                    | [ H : ?A = _, H' : _ = ?A |- _ ] =>
                      rewrite <-H' in H;
                      apply get_implies_in_to_list in H;
                      destructAll;
                      apply nth_error_In in H
                    end.
                    match goal with
                    | [ H : forall _, In _ ?L -> _,
                        H' : In _ ?L |- _ ] =>
                      specialize (H _ H')
                    end.
                    simpl in *; eauto.
               - eapply Forall_Permutation_lst; eauto.
                 match goal with
                 | [ H : SplitStoreTypings (map _ _ ++ map _ _) _ |- _ ] =>
                   inversion H; subst; auto
                 end.
               - (* Use Permutation.Permutation *)
                 eapply SplitHeapTypings_Permutation.
                 -- eapply Permutation.Permutation_map; eauto.
                 -- match goal with
                    | [ H : SplitStoreTypings (map _ _ ++ map _ _) _ |- _ ] =>
                      inversion H; subst; auto
                    end. }
             destruct Hsubgoal as [S_lin' [S_unr']].
             destructAll.

             econstructor.
             4-5: eauto.
             ---- destruct m; simpl in *; subst.
                  all: unfold update_mem in *.
                  all: unfold get_mem in *.
                  all:
                    match goal with
                    | [ H : context[set ?L ?Q ?M ?A] |- _ ] =>
                      let P := fresh "O" in
                      remember (set L Q M A) as P;
                      destruct P
                    end.
                  all:
                    match goal with
                    | [ H : None = Some _ |- _ ] => inversion H
                    | [ H : Some _ = Some _ |- _ ] =>
                      inversion H; subst; simpl
                    end.

                  all:
                    match goal with
                    | [ H : Some _ = set _ _ _ _,
                        H' : get _ _ _ = Some _ |- _ ] =>
                      specialize (set_preserves_doms H' (eq_sym H))
                    end.
                  all: intro Hdoms.
                  all: destructAll.
                  ----- eapply Same_set_trans; eauto; eapply Same_set_sym; eauto.
                  ----- unfold update_out_set.
                        do 2 match goal with
                             | [ |- context[meminst (if ?A then _ else _)] ] =>
                               case A
                             end.
                        all: simpl.
                        all: eapply Same_set_trans; eauto; eapply Same_set_sym; eauto.
             ---- destruct m; simpl in *; subst.
                  all: unfold update_mem in *.
                  all: unfold get_mem in *.
                  all:
                    match goal with
                    | [ H : context[set ?L ?Q ?M ?A] |- _ ] =>
                      let P := fresh "O" in
                      remember (set L Q M A) as P;
                      destruct P
                    end.
                  all:
                    match goal with
                    | [ H : None = Some _ |- _ ] => inversion H
                    | [ H : Some _ = Some _ |- _ ] =>
                      inversion H; subst; simpl
                    end.

                  all:
                    match goal with
                    | [ H : Some _ = set _ _ _ _,
                        H' : get _ _ _ = Some _ |- _ ] =>
                      specialize (set_preserves_doms H' (eq_sym H))
                    end.
                  all: intro Hdoms.
                  all: destructAll.
                  ----- eapply Same_set_trans; eauto; eapply Same_set_sym; eauto.
                  ----- unfold update_out_set.
                        do 2 match goal with
                             | [ |- context[meminst (if ?A then _ else _)] ] =>
                               case A
                             end.
                        all: simpl.
                        all: eapply Same_set_trans; eauto; eapply Same_set_sym; eauto.
             ---- econstructor; eauto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- repeat rewrite app_assoc in *.
         match goal with
         | [ H : ?A ++ [?B] = ?C ++ [?E; ?F; ?D] |- _ ] =>
           assert (Heq_typs1 : A = C ++ [E; F] /\ B = D)
         end.
         { apply app_inj_tail_iff.
           repeat rewrite app_assoc_reverse in *.
           simpl.
           auto. }
         destructAll.
         match goal with
         | [ H : ?A ++ [?B] = ?C ++ [?E; ?D] |- _ ] =>
           assert (Heq_typs2 : A = C ++ [E] /\ B = D)
         end.
         { apply app_inj_tail_iff.
           repeat rewrite app_assoc_reverse in *.
           simpl.
           auto. }
         destructAll.
         match goal with
         | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
           assert (Heq_typs3 : A = C /\ B = D)
         end.
         { apply app_inj_tail_iff.
           repeat rewrite app_assoc_reverse in *.
           simpl.
           auto. }
         repeat rewrite app_assoc_reverse in *.
         destructAll; subst.
         match goal with
         | [ |- context[Arrow ?A (?B ++ ?C ++ ?D)] ] =>
           replace A with (A ++ []) by apply app_nil_r;
           replace (B ++ C ++ D) with (A ++ D) by ltac:(repeat rewrite app_assoc_reverse; auto)
         end.
         eapply FrameTyp.
         --- reflexivity.
         --- apply Forall_trivial.
             intro qt.
             destruct qt.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- econstructor.
             match goal with
             | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
               inversion H; simpl in *; subst; simpl in *; subst
             end.
             ---- econstructor.
                  ----- match goal with
                        | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
                          inversion H; subst
                        end.
                        eapply SplitStoreTypings_Empty'; eauto.
                        constructor; [ | constructor; eauto ].
                        ------ eapply SplitStoreTypings_Empty'; eauto.
                               constructor.
                               ------- eapply SplitStoreTypings_Empty'; eauto; constructor; eauto.
                               ------- constructor; eauto.
                                       eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
                                       -------- apply QualLeq_Refl.
                                       -------- unfold Function_Ctx_empty in *; destructAll; auto.
                  ----- match goal with
                        | [ H : get_heaptype _ ?A = Some ?X
                            |- get_heaptype _ ?B = Some ?X ] =>
                          assert (Heq_unr : A = B) by solve_inst_or_unr_typ_eq
                        end.
                        rewrite (eq_sym Heq_unr); eauto.
                  ----- destruct F; simpl in *; subst; eauto.
                  ----- destruct F; simpl in *; subst.
                        replace_typevalid_parts label ret size type location.
                        apply TypeValid_linear.
                        eauto.
             ---- econstructor.
                  ----- match goal with
                        | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
                          inversion H; subst
                        end.
                        unfold eq_map.
                        intros.
                        unfold get_heaptype.
                        match goal with
                        | [ |- context[map_util.M.find (N.succ_pos ?L1) (map_util.M.add (N.succ_pos ?L2) _ _)] ] =>
                          let H := fresh "H" in
                          assert (H : L2 = L1 \/ L2 <> L1) by apply eq_dec_N;
                          case H; intros; subst
                        end.
                        ------ rewrite M.gss.
                               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                               match goal with
                               | [ H : eq_map _ _ |- _ ] =>
                                 unfold eq_map in H; rewrite H
                               end.
                               unfold get_heaptype.
                               rewrite M.gss; auto.
                        ------ rewrite M.gso.
                               2:{
                                 intro.
                                 match goal with
                                 | [ H : N.succ_pos ?L = N.succ_pos ?L2 |- _ ] =>
                                   let H' := fresh "H" in
                                   assert (H' : Pos.pred_N (N.succ_pos L) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                 end.
                                 repeat rewrite N.pos_pred_succ in *.
                                 eauto.
                               }
                               rewrite M.gempty.
                               match goal with
                               | [ |- context[?A = None] ] =>
                                 remember A as opt;
                                 generalize (eq_sym Heqopt);
                                 case opt; [ | auto ]
                               end.
                               intros.
                               match goal with
                               | [ H : map_util.M.find _ (LinTyp ?S) = Some _,
                                   H' : SplitStoreTypings _ ?S |- _ ] =>
                                 specialize (SplitStoreTypings_inv H H')
                               end.
                               intros; destructAll.
                               match goal with
                               | [ H : In _ [_; _] |- _ ] =>
                                 inversion H; subst
                               end.
                               ------- match goal with
                                       | [ H : get_heaptype _ (LinTyp ?S) = Some _,
                                           H' : SplitStoreTypings _ ?S |- _ ] =>
                                         specialize (SplitStoreTypings_inv H H')
                                       end.
                                       intros; destructAll.
                                       match goal with
                                       | [ H : In _ [_; _] |- _ ] =>
                                         inversion H; subst
                                       end.
                                       -------- match goal with
                                                | [ H : get_heaptype _ (LinTyp ?S) = Some _,
                                                    H'' : get_heaptype _ (LinTyp ?SP) = Some _,
                                                    H''' : SplitStoreTypings [?S; _] ?SP,
                                                    H' : SplitStoreTypings _ ?S |- _ ] =>
                                                  specialize (SplitStoreTypings_inv H H')
                                                end.
                                                intros; destructAll.
                                                match goal with
                                                | [ H : In _ [_; _] |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                --------- match goal with
                                                          | [ H : get_heaptype _ (LinTyp ?S) = Some _,
                                                              H' : eq_map (LinTyp ?S) _
                                                              |- _ ] =>
                                                            unfold eq_map in H';
                                                            rewrite H' in H;
                                                            unfold get_heaptype in H;
                                                            rewrite M.gso in H
                                                          end.
                                                          2:{
                                                            intro.
                                                            match goal with
                                                            | [ H : N.succ_pos ?L = N.succ_pos ?L2 |- _ ] =>
                                                              let H' := fresh "H" in
                                                              assert (H' : Pos.pred_N (N.succ_pos L) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                                            end.
                                                            repeat rewrite N.pos_pred_succ in *.
                                                            eauto.
                                                          }
                                                          rewrite M.gempty in *.
                                                          apply eq_sym; auto.
                                                --------- match goal with
                                                          | [ H : In _ [_] |- _ ] =>
                                                            simpl in H;
                                                            case H;
                                                            [ | intros; exfalso; auto ]
                                                          end.
                                                          intros; subst.
                                                          match goal with
                                                          | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                                              H' : get_heaptype ?L (LinTyp ?S) = Some _ |- _ ] =>
                                                            specialize (get_heaptype_empty L _ H);
                                                            let H'' := fresh "H" in
                                                            intro H'';
                                                            rewrite H'' in H';
                                                            inversion H'
                                                          end.
                                       -------- match goal with
                                                | [ H : In _ [_] |- _ ] =>
                                                  simpl in H;
                                                  case H;
                                                  [ | intros; exfalso; auto ]
                                                end.
                                                intros; subst.
                                                match goal with
                                                | [ H : get_heaptype _ (LinTyp ?S) = Some _,
                                                    H' : HasTypeValue ?S _ _ (QualT _ (QualConst Unrestricted)) |- _ ] =>
                                                  specialize (HasTypeValue_Unrestricted_LinEmpty _ _ _ _ _ H')
                                                end.
                                                match goal with
                                                | [ |- (?A -> _) -> _ ] =>
                                                  let H := fresh "H" in
                                                  let H' := fresh "H" in
                                                  assert (H : A);
                                                  [ | intro H';
                                                      specialize (H' H) ]
                                                end.
                                                { apply QualLeq_Refl. }
                                                match goal with
                                                | [ H : ?A = ?B -> _ |- _ ] =>
                                                  let H' := fresh "H" in
                                                  assert (H' : A = B);
                                                  [ | specialize (H H') ]
                                                end.
                                                { unfold Function_Ctx_empty in *; destructAll; auto. }
                                                match goal with
                                                | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                                    H' : get_heaptype ?L (LinTyp ?S) = Some _ |- _ ] =>
                                                  specialize (get_heaptype_empty L _ H);
                                                  let H'' := fresh "H" in
                                                  intro H'';
                                                  rewrite H'' in H';
                                                  inversion H'
                                                end.
                               ------- match goal with
                                       | [ H : In _ [_] |- _ ] =>
                                         simpl in H;
                                         case H;
                                         [ | intros; exfalso; auto ]
                                       end.
                                       intros; subst.
                                       match goal with
                                       | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                           H' : get_heaptype ?L (LinTyp ?S) = Some _ |- _ ] =>
                                         specialize (get_heaptype_empty L _ H);
                                         let H'' := fresh "H" in
                                         intro H'';
                                         rewrite H'' in H';
                                         inversion H'
                                       end.
                  ----- destruct F; simpl in *; subst; eauto.
                  ----- destruct F; simpl in *; subst.
                        replace_typevalid_parts label ret size type location.
                        apply TypeValid_linear; eauto.
             ---- destruct F; subst; simpl in *; solve_lcvs.
         --- solve_tvs.
      -- do 4 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans; eapply LCSizeEqual_trans.
         all: apply LCEffEqual_LCSizeEqual; eauto.

    - (* ArraySet - Trap *)
      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- specialize (HasTypeInstruction_local_is_tl _ _ _ _ _ _ _ Hi).
         intro Htl.
         destructAll.
         eapply ChangeEndLocalTyp; eauto.
         show_tlvs Hi.
         eapply TrapTyp; auto.
         solve_lcvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* ArrayFree *)
      show_tlvs Hi.
      apply ArrayFree_HasTypeInstruction in Hi.
      destructAll.
      exists Sp, Sh, Sstack, Ss, L'.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[Arrow _ ?A] ] =>
           replace A with (A ++ []) at 2 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ Linear); auto.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- apply FreeTyp.
             ---- eassumption.
             ---- destruct F.
                  simpl in *.
                  eassumption.
             ---- destruct F.
                  simpl in *.
                  assumption.
             ---- constructor.
                  eapply QualLeq_Refl.
             ---- destruct F; subst; simpl in *; solve_lcvs.
             ---- destruct F; subst; simpl in *; solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- split; eauto.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         apply LCEffEqual_LCSizeEqual; auto.

    - (* ExistsUnpack Unr *)
      match goal with
      | [ H : context[[Val ?V; ?C]] |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H by ltac:(simpl; congruence);
        rewrite app_assoc in H
      end.
      specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ [Val _]) _ _ |- _ ] =>
        specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ H)
      end.
      intro Hb.
      simpl in *.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction_moreinfo in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ExistUnpack _ _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; apply ExistUnpackUnr_HasTypeInstruction in H
      end.
      2:{
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
      }
      simpl in *.
      destructAll.
      match goal with
      | [ H : ?A ++ ?B ++ [?C] = ?D ++ ?E ++ [?F] |- _ ] =>
        do 2 rewrite app_assoc in H;
        assert (Heq2 : A ++ B = D ++ E /\ C = F) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ ?LP ?VS _ ?L,
          H' : values ?VS |- _ ] =>
        assert (LCEffEqual [] L LP);
        [ apply LCEffEqual_sym; eauto;
          specialize (HasTypeInstruction_values_locals H H') | ]
      end.
      { destruct F; subst; simpl in *; auto.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto. }

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (?VS ++ _) (Arrow (_ ++ ?BTS) (_ ++ ?ATS ++ _)) _,
          H' : HasTypeInstruction ?S _ ?F _ _ (Arrow ?BTS ?ATS) _ |- _ ] =>
        assert (exists x Ss,
                   ATS = BTS ++ x /\
                   SplitStoreTypings Ss S /\
                   Forall3
                     (fun t e S =>
                        exists v,
                          e = Val v /\
                          HasTypeValue S F v t)
                     x VS Ss)
      end.
      { use_Values_HasTypeInstruction. }
      destructAll; subst.
      match goal with
      | [ H : _ ++ _ ++ _ = _ ++ _ |- _ ] =>
        rewrite app_assoc in H
      end.
      match goal with
      | [ H : Forall3 _ _ _ _ |- _ ] =>
        generalize (Forall3_length _ _ _ _ H)
      end.
      intro.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.
      match goal with
      | [ H : ?A = _, H' : _ = ?A /\ ?A = _ |- _ ] =>
        rewrite H in H'; destructAll
      end.
      match goal with
      | [ H : (_ ++ _) ++ _ = _ ++ _ |- _ ] =>
        apply app_eq_len in H; [ | assumption ]
      end.
      destructAll; subst.
      
      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- match goal with
         | [ |- context[?A ++ (?B ++ ?C) ++ ?D :: ?E] ] =>
           replace (A ++ B ++ C) with ((A ++ B ++ C) ++ []) by ltac:(rewrite app_nil_r; auto); replace (A ++ (B ++ C) ++ D :: E) with ((A ++ B ++ C) ++ [D] ++ E)
         end.
         2:{
           repeat rewrite app_assoc.
           rewrite app_assoc_reverse.
           match goal with
           | [ |- ?A ++ ?B = ?A ++ ?C ] =>
             let H := fresh "H" in
             assert (H : B = C); [ | rewrite H; auto ]
           end.
           simpl; auto.
         }
         match goal with
         | [ H : QualLeq (qual (update_linear_ctx (set_hd ?Q _) _)) ?Q2 _ = _,
             H' : context[QualT _ ?Q2] |- _ ] =>
           eapply (FrameTyp _ _ _ _ _ Q)
         end.
         --- reflexivity.
         --- rewrite Forall_app; split.
             ---- prepare_Forall.
                  eapply QualLeq_Trans; eauto.
                  destruct F; simpl in *.
                  rewrite get_set_hd in *; eauto.
             ---- destruct F; simpl in *; eauto.
         --- destruct F; simpl in *.
             rewrite get_set_hd in *.
             eapply QualLeq_Trans; eauto.
         --- match goal with
             | [ |- context[?A :: ?B ++ ?C] ] =>
               replace (A :: B ++ C) with (([A] ++ B) ++ C) by ltac:(simpl; auto)
             end.
             match goal with
             | [ H : Forall3 _ ?L1 _ _
                 |- HasTypeInstruction _ _ _ ?L _ (Arrow _ (?A ++ _)) _ ] =>
               eapply (ConsTyp _ _ _ _ _ _ L _ _ _ _ (A ++ L1))
             end.
             ---- eassumption.
             ---- match goal with
                  | [ H : SplitStoreTypings [?S1; ?S2] ?S
                      |- HasTypeInstruction ?S _ _ ?L _ (Arrow _ (?A ++ _)) _ ] =>
                    apply (HasTypeInstruction_app _ S2 S1 _ _ _ _ _ L _ _ A)
                  end.
                  ----- apply ValTyp.
                        2:{ destruct F; subst; simpl in *; solve_lcvs. }
                        apply HasTypeValue_update_linear_ctx.
                        eapply HasTypeValue_Function_Ctx; try eassumption;
                        unfold update_linear_ctx;
                        destruct F;
                        simpl;
                        eauto.
                  ----- match goal with
                        | [ |- context[Arrow ?A _] ] =>
                          replace A with (A ++ []) by apply app_nil_r
                        end.
                        eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
                        ------ reflexivity.
                        ------ apply Forall_trivial.
                               intro qt.
                               destruct qt.
                               apply QualLeq_Top.
                        ------ apply QualLeq_Top.
                        ------ use_HasTypeValues_imp_HasTypeInstruction F.
                        ------ destruct F; subst; simpl in *; solve_tvs.
                  ----- eapply SplitStoreTypings_permut; [ | eassumption ].
                        constructor.
             ---- match goal with
                  | [ H : QualLeq (qual (update_linear_ctx (set_hd ?Q _) _)) ?Q2 ?Q3 = _,
                      H' : context[QualT _ ?Q2] |- _ ] =>
                    eapply (FrameTyp _ _ _ _ _ Q3)
                  end.
                  ----- reflexivity.
                  ----- constructor; eauto.
                        destruct F; simpl in *.
                        eauto.
                  ----- destruct F; simpl in *.
                        unfold get_hd; destruct linear; simpl; eauto.
                  ----- eapply ChangeEndLocalTyp.
                        { destruct F; subst; simpl in *; eauto. }
                        eapply ChangeBegLocalTyp.
                        { destruct F; subst; simpl in *.
                          unfold Function_Ctx_empty in *.
                          simpl in *; destructAll; eauto. }
                        eapply ChangeBegLocalTyp.
                        { destruct F; subst; simpl in *.
                          apply LCEffEqual_sym.
                          eauto. }
                        eapply BlockTyp.
                        match goal with
                        | [ |- context[Val ?V :: ?B] ] =>
                          replace (Val V :: B) with ([Val V] ++ B) by ltac:(simpl; auto)
                        end.
                        match goal with
                        | [ H : context[Ex _ _ ?T]
                            |- HasTypeInstruction _ _ _ _ (_ ++ map (_ (_ ?S)) _) (Arrow ?INTS ?OUTS) _ ] =>
                          eapply (HasTypeInstruction_app _ _ _ _ _ _ _ _ _ _ _ (INTS ++ [(debruijn.subst_ext S T)]))
                        end.
                        ------ match goal with
                               | [ |- context[Arrow ?A _] ] =>
                                 replace A with (A ++ []) at 1 by apply app_nil_r
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- apply Forall_trivial.
                                       intro t.
                                       destruct t.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- eapply ValTyp.
                                       inversion Hst; subst.
                                       match goal with
                                       | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                         inversion H; subst
                                       end.
                                       match goal with
                                       | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                                         inversion H; subst
                                       end.
                                       -------- unfold get_mem in *.
                                                match goal with
                                                | [ H : get _ _ _ = Some _ |- _ ] =>
                                                  specialize (get_implies_in_to_list _ _ _ _ _ H)
                                                end.
                                                intro Htl.
                                                destructAll.
                                                match goal with
                                                | [ H : Forall2 _ _ ?L2,
                                                    H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                                  specialize (forall2_args_2 _ _ _ _ _ H H')
                                                end.
                                                intro Hhht.
                                                destructAll.
                                                match goal with
                                                | [ H : HasTypeValue ?S _ (Ref (LocP _ _)) _,
                                                    H' : get_heaptype _ (UnrTyp ?S) = Some _,
                                                    H'' : get_heaptype _ (UnrTyp ?S2) = Some _ |- _ ] =>
                                                  assert (Hunr : UnrTyp S2 = UnrTyp S)
                                                end.
                                                { match goal with
                                                  | [ |- _ = ?A ] =>
                                                    assert (Hunr' : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                                  end.
                                                  rewrite Hunr'.
                                                  eapply proj1.
                                                  eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                  apply in_or_app; right.
                                                  eapply nth_error_In; eauto. }
                                                match goal with
                                                | [ H : HasTypeValue ?S _ (Ref (LocP _ _)) _,
                                                    H' : get_heaptype _ (UnrTyp ?S) = Some _,
                                                    H'' : get_heaptype _ (UnrTyp ?S2) = Some _ |- _ ] =>
                                                  assert (Hinst : InstTyp S2 = InstTyp S)
                                                end.
                                                { match goal with
                                                  | [ |- _ = ?A ] =>
                                                    assert (Hinst' : A = InstTyp Sh) by solve_inst_or_unr_typ_eq
                                                  end.
                                                  rewrite Hinst'.
                                                  eapply proj2.
                                                  eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                  apply in_or_app; right.
                                                  eapply nth_error_In; eauto. }
                                                match goal with
                                                | [ H : get_heaptype _ ?A = _,
                                                    H' : get_heaptype _ ?B = _,
                                                    H'' : ?A = ?B |- _ ] =>
                                                  rewrite H'' in H;
                                                  rewrite H in H';
                                                  inversion H'; subst
                                                end.
                                                match goal with
                                                | [ H : HasHeapType _ _ _ (Ex _ _ _) |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                eapply HasTypeValue_empty_function_ctx.
                                                --------- eapply HasTypeValue_same_envs.
                                                ---------- eassumption.
                                                ---------- match goal with
                                                           | [ H : ?A = InstTyp ?S
                                                               |- ?A = _ ] =>
                                                             assert (Hinst' : A = InstTyp (empty_LinTyp S))
                                                           end.
                                                           { match goal with
                                                             | [ |- _ = InstTyp (_ ?S) ] =>
                                                               unfold empty_LinTyp; destruct S
                                                             end.
                                                             simpl in *.
                                                             auto. }
                                                           exact Hinst'.
                                                ---------- match goal with
                                                           | [ |- _ = UnrTyp (_ ?S) ] =>
                                                             unfold empty_LinTyp; destruct S
                                                           end.
                                                           simpl in *; auto.
                                                ---------- Ltac prove_unrestricted_pack_empty F :=
                                                             match goal with
                                                             | [ H : HasHeapType _ _ _ (Ex _ _ _) |- _ ] =>
                                                               inversion H; subst; simpl in *
                                                             end;
                                                             match goal with
                                                             | [ H : context[subst.subst'_qual ?S ?M] |- _ ] =>
                                                               let H' := fresh "H" in
                                                               assert (H' : subst.subst'_qual S M = M); [ | rewrite H' in H ]
                                                             end;
                                                             [ match goal with
                                                               | [ |- _ = ?A ] => case A
                                                               end;
                                                               [ intros; simpl;
                                                                 unfold debruijn.get_var';
                                                                 unfold debruijn.subst'_of;
                                                                 unfold debruijn.shifts';
                                                                 unfold debruijn.subst';
                                                                 unfold subst.BindVar_rwasm;
                                                                 unfold subst.subst'_rwasm;
                                                                 unfold subst.subst'_qual;
                                                                 simpl;
                                                                 unfold debruijn.get_var';
                                                                 unfold debruijn.weaks';
                                                                 unfold debruijn.var;
                                                                 unfold subst.VarKind;
                                                                 simpl;
                                                                 auto
                                                               | intros; simpl; auto ] | ];
                                                             eapply HasTypeValue_Unrestricted_LinEmpty; [ eauto | | ];
                                                             destruct F; subst; simpl in *; auto;
                                                             unfold Function_Ctx_empty in *; simpl in *; destructAll; subst; auto.
                                                           apply eq_map_empty; [ prove_unrestricted_pack_empty F | ].
                                                           match goal with
                                                           | [ |- context[empty_LinTyp ?S] ] =>
                                                             unfold empty_LinTyp; destruct S; simpl; auto
                                                           end.
                                                --------- destruct F; simpl in *; constructor; destruct Hempty; simpl in *; eauto.
                                       -------- unfold get_mem in *.
                                                match goal with
                                                | [ H : get _ _ _ = Some _ |- _ ] =>
                                                  specialize (get_implies_in_to_list _ _ _ _ _ H)
                                                end.
                                                intro Htl.
                                                destructAll.
                                                match goal with
                                                | [ H : Forall2 _ _ ?L2,
                                                    H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                                  specialize (forall2_args_2 _ _ _ _ _ H H')
                                                end.
                                                intro Hhht.
                                                destructAll.
                                                match goal with
                                                | [ H : eq_map _ (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                                  assert (Hght : get_heaptype L (LinTyp Sp) = Some HT)
                                                end.
                                                { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                                                  eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                                                  eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor 2; constructor; auto ].
                                                  match goal with
                                                  | [ H : eq_map _ _ |- _ ] =>
                                                    unfold eq_map in H;
                                                    rewrite H
                                                  end.
                                                  unfold get_heaptype.
                                                  rewrite M.gss; auto. }
                                                (* For the first subgoal, use disjointness of LinTyp Sh and LinTyp Sp *)
                                                match goal with
                                                | [ H : _ \/ _ |- _ ] =>
                                                  destruct H
                                                end.
                                                { match goal with
                                                  | [ H : SplitStoreTypings [?S1; ?S2] ?S,
                                                      H0 : get_heaptype ?L (LinTyp ?S1) = Some ?HT,
                                                      H1 : get_heaptype ?L (LinTyp ?S2) = Some _,
                                                      H' : HasTypeStore _ ?S2 ?S1 |- _ ] =>
                                                    let H''' := fresh "H" in
                                                    assert (H''' : get_heaptype L (LinTyp S) = Some HT);
                                                    [ | let H'' := fresh "H" in
                                                        destruct H as [H'' H];
                                                        destruct H ]
                                                  end.
                                                  { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                                                    auto. }
                                                  match goal with
                                                  | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT,
                                                      H' : forall _ _, get_heaptype _ (LinTyp ?S) = Some _ -> _ |- _ ] =>
                                                    specialize (H' _ _ H);
                                                    inversion H'; subst; simpl in *
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
                                                    | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                                                      rewrite H in H'; inversion H'
                                                    end. }
                                                match goal with
                                                | [ H : ?A = _, H' : ?A = _ |- _ ] =>
                                                  rewrite H in H'; inversion H'; subst
                                                end.
                                                match goal with
                                                | [ H : HasHeapType _ _ _ (Ex _ _ _) |- _ ] =>
                                                  inversion H; subst
                                                end.
                                                eapply HasTypeValue_empty_function_ctx.
                                                --------- eapply HasTypeValue_same_envs.
                                                ---------- eassumption.
                                                ---------- match goal with
                                                           | [ |- context[empty_LinTyp ?S] ] =>
                                                             assert (Hinst' : InstTyp S = InstTyp Sh) by solve_inst_or_unr_typ_eq;
                                                             unfold empty_LinTyp; destruct S
                                                           end.
                                                           simpl in *.
                                                           rewrite Hinst'.
                                                           eapply proj2.
                                                           eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                           apply in_or_app; left.
                                                           eapply nth_error_In; eauto.
                                                ---------- match goal with
                                                           | [ |- context[empty_LinTyp ?S] ] =>
                                                             assert (Hunr' : UnrTyp S = UnrTyp Sh) by solve_inst_or_unr_typ_eq;
                                                             unfold empty_LinTyp; destruct S
                                                           end.
                                                           simpl in *.
                                                           rewrite Hunr'.
                                                           eapply proj1.
                                                           eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                                           apply in_or_app; left.
                                                           eapply nth_error_In; eauto.
                                                ---------- apply eq_map_empty; [ prove_unrestricted_pack_empty F | ].
                                                           match goal with
                                                           | [ |- context[empty_LinTyp ?S] ] =>
                                                             unfold empty_LinTyp; destruct S; simpl; auto
                                                           end.
                                                --------- destruct F; simpl in *; constructor; destruct Hempty; simpl in *; eauto.
                                       -------- destruct F; subst; simpl in *; solve_lcvs.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                        ------ match goal with
                               | [ H : SplitStoreTypings [_; ?S] Sstack
                                   |- context[HasTypeInstruction _ ?A ?B ?C ?D ?E ?F] ] =>
                                 assert (real_goal : HasTypeInstruction S A B C D E F)
                               end.                        
                               { rewrite label_update_linear_ctx.
                                 rewrite update_label_linear_ctx.
                                 rewrite update_linear_ctx_idempotent.
                                 rewrite linear_update_linear_ctx.

                                 rewrite linear_update_linear_ctx in *.
                                 rewrite label_update_linear_ctx in *.
                                 rewrite update_label_linear_ctx in *.
                                 rewrite update_linear_ctx_idempotent in *.

                                 match goal with
                                 | [ H : context[Pack ?PT ?V ?HT],
                                     H' : context[Ex ?A ?B (QualT ?C ?D)] |- _ ] =>
                                   assert (Hneeded : exists S, HasHeapType S empty_Function_Ctx (Pack PT V HT) (Ex A B (QualT C D)))
                                 end.
                                 { inversion Hst; subst.
                                   match goal with
                                   | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                                     inversion H; subst
                                   end.
                                   match goal with
                                   | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
                                     inversion H; subst
                                   end.
                                   - match goal with
                                     | [ H : get_mem _ _ _ = Some _ |- _ ] =>
                                       specialize (get_implies_in_to_list _ _ _ _ _ H)
                                     end.
                                     intro Hne.
                                     destructAll.
                                     match goal with
                                     | [ H : Forall2 _ _ ?L2,
                                         H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                       specialize (forall2_args_2 _ _ _ _ _ H H')
                                     end.
                                     intro Hne2.
                                     destructAll.
                                     match goal with
                                     | [ H : HasHeapType ?S _ _ _,
                                         H' : get_heaptype _ (UnrTyp ?S) = _,
                                         H'' : get_heaptype _ (UnrTyp ?S2) = _ |- _ ] =>
                                       assert (Hunr : UnrTyp S = UnrTyp S2)
                                     end.
                                     { match goal with
                                       | [ |- _ = ?A ] =>
                                         assert (Hunr' : A = UnrTyp Sh) by solve_inst_or_unr_typ_eq
                                       end.
                                       rewrite Hunr'.
                                       eapply proj1.
                                       eapply SplitStoreTypings_eq_typs2; [ eauto | ].
                                       apply in_or_app; right.
                                       eapply nth_error_In; eauto. }
                                     match goal with
                                     | [ H : get_heaptype _ ?A = _,
                                         H' : get_heaptype _ ?B = _,
                                         H'' : ?A = ?B |- _ ] =>
                                       rewrite H'' in H;
                                       rewrite H in H';
                                       inversion H'; subst
                                     end.
                                     eexists; eassumption.
                                   - match goal with
                                     | [ H : get_mem _ _ _ = Some _ |- _ ] =>
                                       specialize (get_implies_in_to_list _ _ _ _ _ H)
                                     end.
                                     intro Hne.
                                     destructAll.
                                     match goal with
                                     | [ H : Forall2 _ _ ?L2,
                                         H' : nth_error ?L2 _ = Some _ |- _ ] =>
                                       specialize (forall2_args_2 _ _ _ _ _ H H')
                                     end.
                                     intro Hne2.
                                     destructAll.

                                     (* Use eq_map to show get_heaptype assertion *)
                                     match goal with
                                     | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                       assert (Hght : get_heaptype L LT = Some HT)
                                     end.
                                     { match goal with
                                       | [ H : eq_map _ _ |-
                                           get_heaptype ?L _ = _] =>
                                         rewrite (H L)
                                       end.
                                       unfold get_heaptype.
                                       rewrite typing.M.gss.
                                       eauto. }
                                     (* LinTyp x13 is a subset of LinTyp Sstack is a subset of LinTyp Sp *)
                                     match goal with
                                     | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                       assert (HghtSp : get_heaptype L (LinTyp Sp) = Some HT)
                                     end.
                                     { match goal with
                                       | [ H : SplitStoreTypings [?S1; _] Sstack,
                                           H' : SplitStoreTypings ?SS ?S1 |- _ ] =>
                                         specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=S1) Hght)
                                       end.
                                       match goal with
                                       | [ |- (?A -> ?B -> _) -> _ ] =>
                                         let H1 := fresh "H" in
                                         let H2 := fresh "H" in
                                         let H3 := fresh "H" in
                                         assert (H1 : A);
                                           [ constructor 2; constructor; eauto
                                           | assert (H2 : B);
                                             [ eauto
                                             | intro H3;
                                               specialize (H3 H1 H2); 
                                               match goal with
                                               | [ H : SplitStoreTypings ?SS Sstack |- _ ] =>
                                                 specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=SS) (S2:=Sstack) H3) 
                                               end ] ]
                                       end.
                                       match goal with
                                       | [ |- (?A -> ?B -> _) -> _ ] =>
                                         let H1 := fresh "H" in
                                         let H2 := fresh "H" in
                                         let H3 := fresh "H" in
                                         assert (H1 : A);
                                           [ constructor; eauto
                                           | assert (H2 : B);
                                             [ eauto
                                             | intro H3;
                                               specialize (H3 H1 H2); 
                                               specialize (SplitStoreTypings_get_heaptype_LinTyp (Ss:=(Sstack :: S_ignore ++ Ss)) (S2:=Sp) H3) ] ]
                                       end.
                                       match goal with
                                       | [ |- (?A -> ?B -> _) -> _ ] =>
                                         let H1 := fresh "H" in
                                         let H2 := fresh "H" in
                                         let H3 := fresh "H" in
                                         assert (H1 : A);
                                           [ constructor; eauto
                                           | assert (H2 : B);
                                             [ eauto
                                             | intro H3;
                                               specialize (H3 H1 H2) ] ]
                                       end.
                                       eauto. }
                                     (* Sp and Sh are disjoint *)
                                     match goal with
                                     | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                       assert (HnghtSh : forall x, get_heaptype L (LinTyp Sh) = Some x -> False)
                                     end.
                                     { intros.
                                       match goal with
                                       | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
                                         inversion H
                                       end.
                                       simpl in *.
                                       match goal with
                                       | [ H : SplitHeapTypings [LinTyp Sp; LinTyp Sh] _ |- _ ] =>
                                         inversion H
                                       end.
                                       unfold get_heaptype in *.
                                       match goal with
                                       | [ H : _ <--> _ |- _ ] =>
                                         inversion H
                                       end.
                                       match goal with
                                       | [ H : _ \subset (Dom_ht (LinTyp S)),
                                           H' : M.find (N.succ_pos ?L) (LinTyp Sh) = _ |- _ ] =>
                                         specialize (H L)
                                       end.
                                       match goal with
                                       | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
                                         let H' := fresh "H" in
                                         assert (H' : A); [ | specialize (H H') ]
                                       end.
                                       { unfold Ensembles.In.
                                         unfold Dom_ht.
                                         simpl.
                                         constructor.
                                         unfold Ensembles.In.
                                         unfold Dom_map.
                                         eexists; eauto. }
                                       unfold Ensembles.In in *.
                                       unfold Dom_ht in *.
                                       unfold Ensembles.In in *.
                                       unfold Dom_map in *.
                                       destructAll.
                                       match goal with
                                       | [ H : forall _ _, M.find (N.succ_pos _) (LinTyp S) = _ -> _,
                                           H' : M.find (N.succ_pos ?L) (LinTyp S) = Some ?T |- _ ] =>
                                         specialize (H L T H'); inversion H; subst; simpl in *
                                       end.
                                       1:
                                         match goal with
                                         | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                                           inversion H; subst; simpl in *
                                         end.
                                       all: unfold get_heaptype in *.
                                       all:
                                         match goal with
                                         | [ H : ?A = Some _, H' : ?A = None |- _ ] => rewrite H in H'; inversion H'
                                         end. }
                                     match goal with
                                     | [ H : _ \/ _ |- _ ] =>
                                       case H
                                     end.
                                     { intro Hbad.
                                       specialize (HnghtSh _ Hbad).
                                       exfalso.
                                       assumption. }

                                     intro HghtSp2.
                                     rewrite HghtSp in HghtSp2.
                                     inversion HghtSp2; subst.
                                     eexists; eassumption. }

                                 destructAll.
                                 match goal with
                                 | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                   inversion H; subst
                                 end.

                                 eapply HasTypeInstruction_debruijn_subst; try eassumption.
                                 - apply sizeOfPretype_empty_ctx.
                                   eassumption.
                                 - apply SizeLeq_empty_ctx.
                                   eassumption.
                                 - simpl in *.
                                   eapply SizeValid_empty_imp_all_SizeValid; eauto.
                                 - apply NoCapsPretype_empty_ctx.
                                   eassumption.
                                 - apply TypeValid_empty_ctx.
                                   eassumption.
                                 - destruct F; subst; simpl in *.
                                   unfold Function_Ctx_empty in *.
                                   destructAll; auto.
                                 - destruct F; simpl in *.
                                   rewrite set_set_hd.
                                   do 2 rewrite set_set_hd in *.
                                   eapply ChangeEndLocalTyp; [ | eauto ].
                                   simpl.
                                   apply LCEffEqual_subst_weak_pretype.
                                   rewrite sizepairs_debruijn_weak_pretype.
                                   apply LCEffEqual_sym; auto. }
                               eassumption.
                        ------ match goal with
                               | [ |- context[[empty_LinTyp ?S1; ?S2]] ] =>
                                 let H := fresh "H" in
                                 assert (H : empty_LinTyp S1 = empty_LinTyp S2);
                                 [ destruct S1; destruct S2 | rewrite H ]
                               end.
                               { unfold empty_LinTyp.
                                 match goal with
                                 | [ |- {| InstTyp := ?IT1; LinTyp := _; UnrTyp := ?UT1 |}
                                        =
                                        {| InstTyp := ?IT2; LinTyp := _; UnrTyp := ?UT2 |} ] =>
                                   let H := fresh "H" in
                                   let H' := fresh "H" in
                                   assert (H : IT1 = IT2) by solve_inst_or_unr_typ_eq;
                                   assert (H' : UT1 = UT2) by solve_inst_or_unr_typ_eq;
                                   rewrite H; rewrite H'
                                 end.
                                 auto. }
                               apply SplitStoreTypings_EmptyHeapTyping_l.
                        ------ destruct F; subst; simpl in *.
                               eapply LCEffEqual_trans; eauto.
                  ----- destruct F; subst; simpl in *; solve_tvs.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* ExistsUnpack Lin *)
      match goal with
      | [ H : context[[Val ?V; ?B]] |- _ ] =>
        replace [Val V; B] with ([Val V] ++ [B]) in H by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single_moreinfo _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction_moreinfo in H
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ExistUnpack _ _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; apply ExistUnpackLin_HasTypeInstruction in H
      end.
      2:{
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.
      }
      simpl in *; destructAll.
      match goal with
      | [ H : _ = _ ++ _ ++ _ |- _ ] => rewrite app_assoc in H
      end.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inversion H; subst
      end.

      match goal with
      | [ H : HasTypeStore _ _ _ |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : HasTypeMeminst _ _ _ |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : get_mem _ _ _ = Some _ |- _ ] =>
        specialize (get_implies_in_to_list _ _ _ _ _ H)
      end.
      intro Hne.
      destructAll.

      match goal with
      | [ H : Forall2 _ _ (M.to_list Linear _),
          H' : nth_error (M.to_list Linear _) _ = _ |- _ ] =>
        specialize (forall2_args_2 _ _ _ _ _ H H')
      end.
      intro Hne2.
      destructAll.

      match goal with
      | [ H : HasHeapType ?S empty_Function_Ctx _ _,
          H' : update_mem _ ?L _ _ = Some _ |- _ ] =>
        assert (Hstack :
                  exists Sstack' Sp' Sh' S',
                    SplitStoreTypings [Sp'; Sh'] S' /\
                    SplitStoreTypings [S; Sh'] Sh /\
                    SplitStoreTypings (Sstack' :: S_ignore ++ Ss) Sp' /\
                    SplitStoreTypings [S; {| InstTyp:=InstTyp Sh; UnrTyp:=UnrTyp Sh; LinTyp:=(M.add (N.succ_pos L) (ArrayType (QualT Unit Unrestricted)) (M.empty HeapType)) |}] Sstack')
      end.      
      { eapply SplitStoreTypings_LinInstruction; eauto. }
      destruct Hstack as [Sstack' [Sp' [Sh' [S']]]].
      destructAll.
      
      assert (Hunr : UnrTyp Sp = UnrTyp Sp').
      { solve_inst_or_unr_typ_eq. }
      assert (Hinst : InstTyp Sp = InstTyp Sp').
      { solve_inst_or_unr_typ_eq. }

      match goal with
      | [ |- context[Block (Arrow (_ ++ [?T]) _)] ] =>
        assert (Htypv : TypeValid F T)
      end.
      { solve_tvs.
        match goal with
        | [ H : TypeValid _ (QualT (RefT _ _ (Ex _ _ _)) _) |- _ ] => inv H
        end.
        match goal with
        | [ H : HeapTypeValid _ (Ex _ _ _) |- _ ] => inv H
        end.

        match goal with
        | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
          inversion H; subst; simpl in *
        end.
        match goal with
        | [ H : eq_map ?LT (_ (N.succ_pos ?L) ?T _) |- _ ] =>
          assert (Hght : get_heaptype L LT= Some T);
            [ |
              assert (Hght2 : get_heaptype L (LinTyp Sp) = Some T);
              [ | 
                assert (Hght3 : get_heaptype L (LinTyp S) = Some T);
                [ | assert (Hght4 : get_heaptype L (LinTyp Sh) = None)  ] ] ]
        end.
        { match goal with
          | [ H : eq_map _ _ |- get_heaptype ?L _ = Some _ ] =>
            unfold eq_map in H;
            specialize (H L);
            rewrite H
          end.
          unfold get_heaptype.
          apply M.gss. }
        { eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sstack)); [ | | eauto ].
          - match goal with
            | [ H : SplitStoreTypings [?S1; _] Sstack |- _ ] =>
              eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=S1)); [ | | eauto ]
            end.
            -- auto.
            -- constructor; auto.
          - constructor; auto. }
        { eapply (SplitStoreTypings_get_heaptype_LinTyp (S1:=Sp)); [ | | eauto ].
          - auto.
          - constructor; eauto. }
        { match goal with
          | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] => inversion H
          end.
          simpl in *.
          match goal with
          | [ H : SplitHeapTypings [LinTyp Sp; _] _ |- _ ] => inversion H
          end.
          match goal with
          | [ H : forall _ _, get_heaptype _ _ = Some _ -> _ |- _ ] => specialize (H _ _ Hght3)
          end.
          match goal with
          | [ H : ExactlyInOne false _ _ _ |- _ ] => inversion H; subst
          end.
          - match goal with
            | [ H : ExactlyInOne true _ _ _ |- _ ] => inversion H; auto
            end.
          - match goal with
            | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
              rewrite H in H'; inversion H'
            end. }
        match goal with
        | [ H : _ \/ _ |- _ ] => case H; intros
        end.
        all:
          match goal with
          | [ H : ?A = _, H' : ?A = _ |- _ ] =>
            rewrite H in H'; inversion H'; subst
          end.
        match goal with
        | [ H : HasHeapType _ _ _ _ |- _ ] => inv H
        end.
        eapply TypeValid_Function_Ctx.
        { eapply TypeValid_debruijn_subst_nonfree_var.
          - match goal with
            | [ H : TypeValid (debruijn.subst_ext _ _) _ |- _ ] => exact H
            end.
          - simpl in *; eapply sizeOfPretype_empty_ctx; eauto.
          - auto.
          - auto. }
        all: simpl.
        all: unfold Function_Ctx_empty in *.
        all: simpl in *; destructAll; auto. }

      match goal with
      | [ H : HasTypeLocals _ _ _ ?L |- _ ] =>
        exists Sp', Sh', Sstack', Ss, L
      end.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- eapply HasTypeStore_LinInstruction; eauto.
      -- match goal with
         | [ H : SplitStoreTypings (_ :: _ ++ _) ?SP,
             H' : HasTypeStore _ _ ?SP |- _ ] =>
           specialize (SplitStoreTypings_unr_same H)
         end.
         intro Heq.
         rewrite (eq_sym Hunr).
         rewrite Heq.
         eauto.
      -- rewrite app_assoc.
         rewrite app_assoc.
         eapply FrameTyp.
         --- reflexivity.
         --- rewrite Forall_app; split;
             [ | destruct F; simpl in *; eauto ].
             prepare_Forall.
             eapply QualLeq_Trans; [ eauto | ].
             destruct F; subst; simpl in *.
             rewrite get_set_hd in *; eauto.
         --- eapply QualLeq_Trans; [ eauto | ].
             destruct F; subst; simpl in *.
             rewrite get_set_hd in *; eauto.
         --- match goal with
             | [ |- context[[?A; ?B; ?C; ?D]] ] =>
               replace [A; B; C; D] with ([A; B; C] ++ [D]) by ltac:(simpl; auto)
             end.

             match goal with
             | [ H : SplitStoreTypings [?S1; {| InstTyp := ?IT; LinTyp := ?LT; UnrTyp := ?UT |}] ?SP,
                 H' : HasTypeInstruction ?S2 _ _ (subst'_local_ctx _ _) _ _ (subst'_local_ctx _ _) |- _ ] =>
               assert (Hsplit' : exists S,
                        SplitStoreTypings [S1; {| InstTyp := IT; LinTyp := LT; UnrTyp := UT |}] S /\
                        SplitStoreTypings [S; S2] SP)
             end.
             { match goal with
               | [ |- context[_ /\ SplitStoreTypings [_; _] ?S] ] =>
                 exists S
               end.
               split; auto.
               constructor.
               - constructor; eauto.
                 constructor; eauto.
                 split; solve_inst_or_unr_typ_eq.
               - simpl.
                 apply SplitHeapTypings_EmptyHeapTyping_r.
                 auto. }
             destructAll.

             match goal with
             | [ |- HasTypeInstruction
                      _ _ _ ?L
                      (_ ++ [Block (Arrow ?TAUS1 _) _ _]) _ _ ] =>
               eapply (ConsTyp _ _ _ _ _ _ L _ _ _ _ TAUS1)
             end.             
             ---- eassumption.
             ---- match goal with
                  | [ |- HasTypeInstruction
                           _ _ _ _ [?A; ?B; ?C] _ _ ] =>
                    replace [A; B; C] with ([A; B] ++ [C]) by ltac:(simpl; auto)
                  end.
                  match goal with
                  | [ H : SplitStoreTypings (?S1 :: _ ++ _) ?SP,
                      H' : HasTypeStore _ _ ?SP,
                      H'' : HasTypeValue _ _ _ (QualT (RefT ?A ?B _) ?C)
                      |- HasTypeInstruction
                           ?S2 _ _ ?L _
                           (Arrow _ (?TAUS1 ++ [?TAU])) _ ] =>
                    eapply (ConsTyp
                              _
                              S2
                              {| InstTyp := (InstTyp S1); UnrTyp := (UnrTyp S1); LinTyp := map_util.M.empty HeapType |}
                              _ _ _
                              L
                              _ _ _ _
                              (TAUS1 ++ [TAU; QualT (RefT A B (ArrayType (QualT Unit Unrestricted))) C]))
                  end.
                  ----- constructor.
                        ------ constructor; [ auto | ].
                               constructor; [ | auto ].
                               simpl.
                               split; solve_inst_or_unr_typ_eq.
                        ------ simpl.
                               apply SplitHeapTypings_EmptyHeapTyping_r.
                               simpl; auto.
                  ----- match goal with
                        | [ |- context[[?A; ?B]] ] =>
                          replace [A; B] with ([A] ++ [B]) by ltac:(simpl; auto)
                        end.
                        match goal with
                        | [ H : SplitStoreTypings [?S1; ?S2] ?S
                            |- HasTypeInstruction
                                 ?S _ _ ?L _
                                 (Arrow _ (?TAUS ++ [?TAU1; ?TAU2]))
                                 _ ] =>
                          eapply (ConsTyp
                                    _
                                    S1 S2
                                    _ _ _
                                    L
                                    _ _ _ _
                                    (TAUS ++ [TAU1]))
                        end.
                        ------ eauto.
                        ------ match goal with
                               | [ |- context[Arrow ?TAUS _] ] =>
                                 replace TAUS with (TAUS ++ []) at 1 by apply app_nil_r
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- rewrite Forall_forall.
                                       let t := fresh "t" in
                                       intro t; destruct t.
                                       intros.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- eapply ValTyp.
                                       2:{ destruct F; subst; simpl in *; solve_lcvs. }
                                       apply HasTypeValue_update_linear_ctx.
                                       apply HasTypeValue_update_linear_ctx.
                                       match goal with
                                       | [ H : HasHeapType _ _ _ _ |- _ ] =>
                                         inversion H; subst
                                       end.
                                       match goal with
                                       | [ H : HasTypeValue _ _ (Ref (LocP _ Linear)) _ |- _ ] =>
                                         inversion H; subst
                                       end.
                                       match goal with
                                       | [ H : eq_map (LinTyp _) (M.add _ (Ex _ _ ?TAU) _),
                                           H' : get_heaptype _ _ = Some (Ex _ _ ?TAU0) \/ _ |- _ ] =>
                                         assert (Heq : TAU = TAU0)
                                       end.
                                       { match goal with
                                         | [ H : eq_map ?LT (map_util.M.add (N.succ_pos ?L) ?HT _) |- _ ] =>
                                           let H' := fresh "H" in
                                           assert (H' : get_heaptype L LT = Some HT);
                                           [ unfold eq_map in H;
                                             rewrite H | ]
                                         end.
                                         { unfold get_heaptype.
                                           rewrite M.gss; auto. }
                                         match goal with
                                         | [ H : SplitStoreTypings [?S; ?S2] _,
                                             H' : get_heaptype _ (LinTyp ?S) = Some _
                                             |- _ ] =>
                                           let H'' := fresh "H" in
                                           assert (H'' : In S [S; S2]) by ltac:(constructor; auto);
                                           specialize (SplitStoreTypings_get_heaptype_LinTyp H' H'' H)
                                         end.
                                         intros.
                                         match goal with
                                         | [ H : SplitStoreTypings (?S :: ?Ss1 ++ ?Ss2) _,
                                             H' : get_heaptype _ (LinTyp ?S) = Some _
                                             |- _ ] =>
                                           let H'' := fresh "H" in
                                           assert (H'' : In S (S :: Ss1 ++ Ss2)) by ltac:(constructor; auto);
                                           specialize (SplitStoreTypings_get_heaptype_LinTyp H' H'' H)
                                         end.
                                         match goal with
                                         | [ H' : get_heaptype _ _ = Some (Ex _ _ ?TAU0) \/ _ |- _ ] =>
                                           case H'; intros
                                         end.
                                         - match goal with
                                           | [ H : get_heaptype ?L (LinTyp ?S1) = Some ?HT,
                                               H' : get_heaptype _ (LinTyp ?S2) = Some _,
                                               H'' : SplitStoreTypings [?S1; ?S2] ?S
                                               |- _ ] =>
                                             let H0 := fresh "H" in
                                             let H1 := fresh "H" in
                                             generalize H'';
                                             destruct H'' as [H0 H''];
                                             simpl in H'';
                                             destruct H'' as [H1 H''];
                                             generalize (H'' L HT)
                                           end.
                                           match goal with
                                           | [ |- (?A -> _) -> ?B -> _ ] =>
                                             let H := fresh "H" in
                                             let H' := fresh "H" in
                                             let H'' := fresh "H" in
                                             intro H';
                                             intro H'';
                                             assert (H : A);
                                             [ | specialize (H' H);
                                                 inversion H';
                                                 subst; simpl in * ]
                                           end.
                                           { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                                             auto. }
                                           -- match goal with
                                              | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                                                inversion H; subst; simpl in *
                                              end.
                                              match goal with
                                              | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                                                rewrite H in H'; inversion H'
                                              end.
                                           -- match goal with
                                              | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                                                rewrite H in H'; inversion H'
                                              end.
                                         - match goal with
                                           | [ H : ?A = Some _,
                                               H' : ?A = Some _
                                               |- _ ] =>
                                             rewrite H in H';
                                             inversion H'
                                           end.
                                           auto. }
                                       subst.
                                       apply HasTypeValue_empty_function_ctx.
                                       all: assumption.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                        ------ match goal with
                               | [ |- context[?A ++ [?B; ?C]] ] =>
                                 replace (A ++ [B]) with ((A ++ [B]) ++ []) by ltac:(apply app_nil_r; auto);
                                 replace (A ++ [B; C]) with ((A ++ [B]) ++ [C]) by ltac:(rewrite app_assoc_reverse; simpl; auto)
                               end.
                               eapply FrameTyp.
                               ------- reflexivity.
                               ------- rewrite Forall_forall.
                                       let t := fresh "t" in
                                       intro t; destruct t.
                                       intros.
                                       apply QualLeq_Top.
                               ------- apply QualLeq_Top.
                               ------- eapply ValTyp.
                                       2:{ destruct F; subst; simpl in *; solve_lcvs. }
                                       apply HasTypeValue_update_linear_ctx.
                                       apply HasTypeValue_update_linear_ctx.
                                       match goal with
                                       | [ H : HasTypeValue _ _ _ (QualT (RefT _ _ _) _) |- _ ] =>
                                         inversion H; subst
                                       end.
                                       eapply RefTypLin.
                                       -------- constructor.
                                       -------- destruct F; subst; simpl in *; assumption.
                                       -------- constructor.
                                                --------- destruct F; subst; simpl in *; eassumption.
                                                --------- econstructor; eauto.
                                                --------- econstructor.
                                                          constructor.
                                                          ---------- econstructor; eauto.
                                                          ---------- eapply QualLeq_Refl.
                               ------- destruct F; subst; simpl in *; solve_tvs.
                  ----- match goal with
                        | [ |- context[?A ++ [?B; ?C]] ] =>
                          replace (A ++ [B]) with ((A ++ [B]) ++ []) by ltac:(apply app_nil_r; auto);
                          replace (A ++ [B; C]) with ((A ++ [B]) ++ [C]) by ltac:(rewrite app_assoc_reverse; simpl; auto)
                        end.
                        eapply FrameTyp.
                        ------ reflexivity.
                        ------ rewrite Forall_forall.
                               let t := fresh "t" in
                               intro t; destruct t.
                               intros.
                               apply QualLeq_Top.
                        ------ apply QualLeq_Top.
                        ------ match goal with
                               | [ |- context[Arrow [?A] []] ] =>
                                 replace (Arrow [A] []) with (EmptyRes A) by ltac:(simpl; auto)
                               end.
                               eapply FreeTyp.
                               ------- unfold EmptyStoreTyping.
                                       simpl.
                                       auto.
                               ------- destruct F; subst; simpl in *; eauto.
                               ------- destruct F; subst; simpl in *; eauto.
                               ------- constructor.
                                       eapply QualLeq_Refl.
                               ------- destruct F; subst; simpl in *; solve_lcvs.
                               ------- solve_tvs.
                                       destruct F; subst; simpl in *.
                                       match goal with
                                       | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] => inv H
                                       end.
                                       econstructor; eauto.
                                       constructor.
                                       -------- constructor.
                                                econstructor; eauto.
                                       -------- apply QualLeq_Refl.
                        ------ destruct F; subst; simpl in *; solve_tvs.
             ---- eapply ChangeEndLocalTyp.
                  { destruct F; subst; simpl in *; eauto. }
                  eapply ChangeBegLocalTyp.
                  { destruct F; subst; simpl in *.
                    apply LCEffEqual_sym; eauto. }
                  eapply BlockTyp.
                  match goal with
                  | [ H : HasHeapType _ _ _ ?HT,
                      H' : HasTypeValue
                             _ _ _
                             (QualT (RefT _ _ (Ex ?A ?B ?C)) _)
                      |- _ ] =>
                    let H'' := fresh "H" in
                    assert (H'' : HT = Ex A B C);
                    [ inversion H'; subst; simpl in *
                    | rewrite H'' in H;
                      inversion H; subst; simpl in * ]
                  end.
                  { match goal with
                    | [ H : eq_map (LinTyp ?S)
                                   (map_util.M.add
                                      (N.succ_pos ?L)
                                      ?HT _),
                        H' : SplitStoreTypings [?S; _] ?S2,
                        H'' : SplitStoreTypings (?S2 :: _ ++ _) ?SP
                        |- _ ] =>
                      let H0 := fresh "H" in
                      assert (H0 : get_heaptype L (LinTyp SP) = Some HT)
                    end.
                    { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                      eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                      match goal with
                      | [ H : eq_map (LinTyp ?S) _ |- context[LinTyp ?S] ] =>
                        unfold eq_map in H; rewrite H
                      end.
                      unfold get_heaptype.
                      rewrite M.gss; auto. }
                    match goal with
                    | [ H : get_heaptype _ _ = _ \/ _ |- _ ] =>
                      case H; intros
                    end.
                    - match goal with
                      | [ H : SplitStoreTypings [?S1; ?S2] ?S,
                          H' : HasTypeStore _ ?S2 ?S1,
                          H'' : get_heaptype ?L (LinTyp ?S1) = Some ?HT |- _ ] =>
                        let H0 := fresh "H" in
                        assert (H0 : get_heaptype L (LinTyp S) = Some HT);
                        [ | destruct H ]
                      end.
                      { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                        auto. }
                      simpl in *.
                      match goal with
                      | [ H : SplitHeapTypings [LinTyp ?S1; LinTyp ?S2] _,
                          H' : HasTypeStore _ ?S2 ?S1 |- _ ] =>
                        destruct H
                      end.
                      match goal with
                      | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT,
                          H' : forall _ _, get_heaptype _ (LinTyp ?S) = Some _ -> _
                          |- _ ] =>
                        specialize (H' _ _ H)
                      end.
                      match goal with
                      | [ H : ExactlyInOne false _ _ _ |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      -- match goal with
                         | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                           inversion H; subst; simpl in *
                         end.
                         match goal with
                         | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                           rewrite H in H'; inversion H'
                         end.
                      -- match goal with
                         | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                           rewrite H in H'; inversion H'
                         end.
                    - match goal with
                      | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                        rewrite H in H'; inversion H'; subst; auto
                      end. }
                      
                  eapply HasTypeInstruction_debruijn_subst.
                  ----- apply sizeOfPretype_empty_ctx.
                        eassumption.
                  ----- apply SizeLeq_empty_ctx.
                        eassumption.
                  ----- eapply SizeValid_empty_imp_all_SizeValid; eauto.
                  ----- apply NoCapsPretype_empty_ctx.
                        eassumption.
                  ----- apply TypeValid_empty_ctx.
                        eassumption.
                  ----- destruct F; subst; simpl in *.
                        unfold Function_Ctx_empty in *.
                        destructAll; auto.
                  ----- destruct F; subst; simpl in *.
                        repeat rewrite set_set_hd in *.
                        eapply ChangeEndLocalTyp; [ | eauto ].
                        simpl.
                        apply LCEffEqual_subst_weak_pretype.
                        rewrite sizepairs_debruijn_weak_pretype.
                        apply LCEffEqual_sym; auto.
                  ----- destruct F; subst; simpl in *.
                        eapply LCEffEqual_trans; eauto.
         --- destruct F; subst; simpl in *; solve_tvs.
      -- rewrite (eq_sym Hinst); assumption.
      -- split; eauto.
         rewrite Hunr.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.

    - (* Free *)
      match goal with
      | [ H : context[[Val ?V; ?C]] |- _ ] =>
        replace [Val V; C] with ([Val V] ++ [C]) in H by ltac:(simpl; congruence)
      end.
      specialize (composition_typing_single _ _ _ _ _ _ _ _ _ Hi).
      intro Ha.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; apply Val_HasTypeInstruction in H
      end.
      destructAll.
      
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Free] _ _ |- _ ] =>
        show_tlvs H; apply Free_HasTypeInstruction in H
      end.
      destructAll.
      match goal with
      | [ H : ?A ++ [?B] = ?C ++ [?D] |- _ ] =>
        assert (Heq2 : A = C /\ B = D) by ltac:(apply app_inj_tail; eassumption)
      end.
      destructAll.

      match goal with
      | [ H : HasTypeValue _ _ (Ref (LocP _ _)) _ |- _ ] =>
        inversion H; subst
      end.
      generalize (conj Hsplit I).
      intro Hsplit2.
      destructAll.
      match goal with
      | [ H : SplitStoreTypings (_ :: _ ++ _) _ |- _ ] =>
        inversion H
      end.
      match goal with
      | [ H : Forall _ (_ :: _ ++ _) |- _ ] =>
        inversion H; subst
      end.
      destructAll.
      match goal with
      | [ H : SplitStoreTypings _ Sstack |- _ ] => inversion H
      end.
      match goal with
      | [ H : Forall _ [_; _] |- _ ] => inversion H; subst
      end.
      match goal with
      | [ H : Forall _ [_] |- _ ] => inversion H; subst
      end.
      destructAll.
            
      apply SplitStoreTypings_cons' in Hsplit.
      destructAll.

      match goal with
      | [ H : SplitStoreTypings (_ ++ _) ?S,
          H' : SplitStoreTypings [_; ?S2] _ |- _ ] =>
        exists S, Sh, S2, Ss, L'
      end.
      split.
      { inversion Hst.
        subst.
        match goal with
        | [ H : SplitStoreTypings [Sp; Sh] _ |- _ ] =>
          inversion H; simpl in *
        end.
        match goal with
        | [ H : HasTypeMeminst _ _ _ |- _ ] =>
          inversion H; subst
        end.

        match goal with
        | [ |- HasTypeStore _ _ ?S ] =>
          assert (Hsst : exists S', SplitStoreTypings [S; Sh] S')
        end.
        { eapply SplitStoreTypings_remove_cons; try eassumption. 
          all: apply eq_sym; auto. }
        destructAll.
        
        econstructor.
        - eassumption.
        - match goal with
          | [ H : SplitStoreTypings [Sp; Sh] _,
              H' : SplitStoreTypings [_; Sh] _ |- _ ] =>
            inversion H'; simpl in *
          end.
          match goal with
          | [ H : Forall _ [_; _] |- _ ] =>
            inversion H; subst
          end.
          destructAll.
          match goal with
          | [ H : _ = ?A |- context[?A] ] => rewrite H
          end.
          match goal with
          | [ H : ?A = InstTyp Sp |- context[?A] ] =>
            rewrite H
          end.
          
          assert (Hinst : InstTyp S = InstTyp Sp).
          { solve_inst_or_unr_typ_eq. }
          rewrite (eq_sym Hinst).
          rewrite Hinst at 1.

          apply free_mem_range_inst in H.
          rewrite (eq_sym H).
          assumption.
        - match goal with
          | [ H : HasTypeMeminst _ _ _ |- _ ] =>
            inversion H; subst
          end.
          unfold remove_out_set.
          simpl.
          unfold free_mem_range in *.
          match goal with
          | [ H : context[free ?L Linear (meminst ?S)] |- _ ] =>
            remember (free L Linear (meminst S)) as f;
              revert Heqf; revert H; case f
          end.
          2:{
            intro H'.
            inversion H'.
          }
          intros.
          match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst
          end.
          simpl.
          derive_mappings f_lin f_unr.
          destructAll.

          match goal with
          | [ H : Some ?MEM2 = free _ _ ?MEM1 |- _ ] =>
            assert (Hperm1 : Permutation.Permutation (M.to_list Unrestricted MEM1) (M.to_list Unrestricted MEM2))
          end.
          { apply Permutation.NoDup_Permutation;
              [ apply to_list_NoDup | apply to_list_NoDup | ].
            constructor; intros.
            all:
              assert (Hqneq : Linear <> Unrestricted) by ltac:(let H := fresh "H" in intro H; inversion H).
            all:
              match goal with
              | [ H : In ?D (M.to_list _ _),
                  H' : Some ?MEM2 = free _ _ ?MEM1 |- _ ] =>
                apply In_nth_error in H;
                let x := fresh "x" in
                let a := fresh "x" in
                let b := fresh "x" in
                let c := fresh "x" in
                destruct H as [x H];
                destruct D as [[a b] c];
                apply in_to_list_implies_get in H;
                specialize (get_free_diff_mem _ _ _ _ _ a (eq_sym H') Hqneq);
                let H'' := fresh "H" in
                intro H'';
                match goal with
                | [ |- _ ] => rewrite H'' in H
                | [ |- _ ] => rewrite (eq_sym H'') in H
                end;
                apply get_implies_in_to_list in H
              end.
            all: destructAll.
            all: eapply nth_error_In; eauto. }            

          match goal with
          | [ |- HasTypeMeminst _ _ ?T ] =>
            apply (MeminstT _ (map f_lin (M.to_list Linear T)) (map f_unr (M.to_list Unrestricted T)))
          end.
          -- unfold Ensembles.Same_set.
             constructor.
             --- unfold MemUtils.dom_lin.
                 unfold MemUtils.dom.
                 unfold Ensembles.Included.
                 unfold Ensembles.In.
                 intros.
                 unfold Dom_ht.
                 unfold Dom_map.
                 unfold Ensembles.In.
                 destructAll.
                 (* x3 is in t0 so x3 is in meminst s *)
                 match goal with
                 | [ H : get ?L _ _ = Some ?X,
                     H' : Some _ = free ?L2 _ _ |- _ ] =>
                   assert (Hget : L2 <> L /\ get L Linear (meminst s) = Some X)
                 end.
                 { match goal with
                   | [ H : Some _ = free ?L2 _ _
                       |- _ /\ get ?L _ _ = _ ] =>
                     assert (Hloc_eq : L2 = L \/ L2 <> L) by apply eq_dec_N
                   end.
                   case Hloc_eq; intros; subst.
                   - match goal with
                     | [ H : Some _ = free ?L2 _ _ |- _ ] =>
                       specialize (get_free_s _ _ _ _ (eq_sym H))
                     end.
                     intros.
                     match goal with
                     | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                       rewrite H in H'; inversion H'
                     end.
                   - match goal with
                     | [ H : Some _ = free ?L2 _ _,
                         H' : ?L2 <> _ |- _ ] =>
                       specialize (get_free_o _ _ _ _ _ (eq_sym H) H')
                     end.
                     intros.
                     match goal with
                     | [ H : get ?A ?B ?C = get _ _ _,
                         H' : get ?A ?B ?C = Some _ |- _ ] =>
                       rewrite H in H'; auto
                     end. }
                 destructAll.
                 (* Therefore, x3 is either in Sh or Sp *)
                 match goal with
                 | [ H : get ?L _ _ = Some _ |- _ ] =>
                   assert (Hor : (exists y : HeapType, M.find (N.succ_pos L) (LinTyp Sh) = Some y) \/ (exists y : HeapType, M.find (N.succ_pos L) (LinTyp Sp) = Some y))
                 end.
                 { match goal with
                   | [ H : MemUtils.dom_lin (meminst ?S) <--> _,
                       H' : get ?L Linear (meminst ?S) = Some _ |- _ ] =>
                     unfold Ensembles.Same_set in H;
                     destruct H as [H];
                     unfold Ensembles.Included in H;
                     unfold MemUtils.dom_lin in H;
                     unfold MemUtils.dom in H;
                     unfold Ensembles.In in H;
                     generalize (H L)
                   end.
                   match goal with
                   | [ |- (?A -> _) -> _ ] =>
                     let H := fresh "H" in
                     assert (H : A) by ltac:(eexists; eauto);
                     let H' := fresh "H" in
                     intro H'; specialize (H' H);
                     inversion H';
                     unfold Dom_ht in *;
                     unfold Ensembles.In in *;
	                 unfold Dom_map in *;
                     [ left | right ]; auto
                   end. }
                 case Hor.
                 ---- intros.
                      constructor.
                      unfold Ensembles.In.
                      auto.
                 ---- intros.
                      constructor 2.
                      unfold Ensembles.In.
                      destructAll.
                      match goal with
                      | [ H : M.find (N.succ_pos ?L) (LinTyp ?S) = Some _,
                          H' : SplitStoreTypings (_ :: _ ++ _) ?S
                          |- context[?L] ] =>
                        specialize (SplitStoreTypings_inv H H')
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      ----- match goal with
                            | [ H : get_heaptype ?L (LinTyp ?S) = Some _,
                                H' : SplitStoreTypings [_; _] ?S
                                |- context[?L] ] =>
                              specialize (SplitStoreTypings_inv H H')
                            end.
                            intros; destructAll.
                            match goal with
                            | [ H : In _ [_; _] |- _ ] =>
                              inversion H; subst; simpl in *
                            end.
                            ------ match goal with
                                   | [ H : eq_map (LinTyp ?S) _,
                                       H' : get_heaptype _ (LinTyp ?S) = _
                                       |- _ ] =>
                                     unfold eq_map in H;
                                     rewrite H in H';
                                     unfold get_heaptype in H';
                                     rewrite M.gso in H';
                                     [ rewrite M.gempty in H';
                                       inversion H' | ]
                                   end.
                                   intro.
                                   match goal with
                                   | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                     assert (Hloc_eq : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                   end.
                                   repeat rewrite N.pos_pred_succ in Hloc_eq; eauto.
                            ------ match goal with
                                   | [ H : _ \/ False |- _ ] =>
                                     case H; [ | intros; exfalso; auto ]
                                   end.
                                   intros; subst.
                                   match goal with
                                   | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                       H' : get_heaptype ?L (LinTyp ?S) = Some _ 
                                       |- _ ] =>
                                     rewrite (get_heaptype_empty _ _ H) in H';
                                     inversion H'
                                   end.
                      ----- eexists.
                            eapply SplitStoreTypings_get_heaptype_LinTyp; [ | eauto | eauto ].
                            eauto.
             --- unfold MemUtils.dom_lin.
                 unfold MemUtils.dom.
                 unfold Ensembles.Included.
                 unfold Ensembles.In.
                 intros.
                 unfold Dom_ht.
                 unfold Dom_map.
                 unfold Ensembles.In.
                 match goal with
                 | [ H : context[MemUtils.dom_lin] |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 unfold Ensembles.Included in *.
                 match goal with
                 | [ H : (Dom_ht _ :|: Dom_ht _) _ |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 ---- match goal with
                      | [ |- context[get ?L Linear _] ] =>
                        assert (Hin : (Dom_ht (LinTyp Sh) :|: Dom_ht (LinTyp Sp)) L)
                      end.
                      { constructor; auto. }
                      match goal with
                      | [ H : forall _, _ -> Ensembles.In _ (MemUtils.dom_lin _) _ |- _ ] =>
                        specialize (H _ Hin)
                      end.
                      unfold Ensembles.In in *.
                      unfold MemUtils.dom_lin in *.
                      unfold MemUtils.dom in *.
                      destructAll.
                      match goal with
                      | [ H : get ?L _ _ = Some _ |- _ ] =>
                        assert (Hneq : l1 <> L)
                      end.
                      { intro; subst.
                        unfold Dom_ht in *.
                        unfold Dom_map in *.
                        unfold Ensembles.In in *.
                        destructAll.
                        unfold SplitHeapTypings in *.
                        destructAll.
                        match goal with
                        | [ H : context[ExactlyInOne _ _ _ [LinTyp _; LinTyp ?S]],
                            H' : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some ?HT
                            |- _ ] =>
                          generalize (H L HT)
                        end.
                        match goal with
                        | [ |- (?A -> _) -> _ ] =>
                          let H := fresh "H" in
                          let H' := fresh "H" in
                          assert (H : A);
                            [ | intro H'; specialize (H' H);
                                inversion H'; subst; simpl in * ]
                        end.
                        { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor 2; constructor; auto ].
                          auto. }
                        - match goal with
                          | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                            inversion H; subst; simpl in *
                          end.
                          unfold get_heaptype in *.
                          match goal with
                          | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                            rewrite H in H'; inversion H'
                          end.
                        - match goal with
                          | [ H : get_heaptype ?L ?LT = None |- _ ] =>
                            let H' := fresh "H" in
                            let y := fresh "y" in
                            assert (H' :
                                      exists y,
                                        get_heaptype L LT = Some y);
                            [ | destruct H' as [y H'];
                                rewrite H in H'; inversion H' ]
                          end.
                          eexists.
                          eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                          eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                          match goal with
                          | [ H : eq_map (LinTyp ?S) _
                              |- context[LinTyp ?S] ] =>
                            unfold eq_map in H; rewrite H
                          end.
                          unfold get_heaptype.
                          rewrite M.gss; eauto. }
                      specialize (get_free_o _ _ _ _ _ (eq_sym Heqf) Hneq).
                      intro H'.
                      rewrite H'.
                      eexists; eauto.
                 ---- match goal with
                      | [ |- context[get ?L Linear _] ] =>
                        assert (Hin : (Dom_ht (LinTyp Sh) :|: Dom_ht (LinTyp Sp)) L)
                      end.
                      { constructor 2; auto.
                        unfold Dom_ht in *.
                        unfold Dom_map in *.
                        unfold Ensembles.In in *.
                        destructAll.
                        match goal with
                        | [ H : map_util.M.find (N.succ_pos _) (LinTyp ?S) = Some _,
                            H' : SplitStoreTypings (_ ++ _) ?S
                            |- _ ] =>
                          specialize (SplitStoreTypings_inv H H')
                        end.
                        intros; destructAll.
                        eexists.
                        eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor 2; eauto ].
                        eauto. }
                      match goal with
                      | [ H : forall _, _ -> Ensembles.In _ (MemUtils.dom_lin _) _ |- _ ] =>
                        specialize (H _ Hin)
                      end.
                      unfold Ensembles.In in *.
                      unfold MemUtils.dom_lin in *.
                      unfold MemUtils.dom in *.
                      destructAll.
                      match goal with
                      | [ H : get ?L _ _ = Some _ |- _ ] =>
                        assert (Hneq : l1 <> L)
                      end.
                      { intro; subst.
                        unfold Dom_ht in *.
                        unfold Dom_map in *.
                        unfold Ensembles.In in *.
                        destructAll.
                        match goal with
                        | [ H : map_util.M.find (N.succ_pos _) (LinTyp ?S) = Some _,
                            H' : SplitStoreTypings (_ ++ _) ?S
                            |- _ ] =>
                          specialize (SplitStoreTypings_inv H H')
                        end.
                        intros; destructAll.
                        match goal with
                        | [ H : In ?S (?Ss1 ++ ?Ss2),
                            H' : get_heaptype ?L (LinTyp ?S) = Some ?HT |- _ ] =>
                          eapply (ExactlyInOne_true_get_heaptype (map LinTyp (Ss1 ++ Ss2)) (LinTyp S) L HT HT); eauto; [ | apply in_map; eauto ]
                        end.
                        match goal with
                        | [ H : SplitHeapTypings (_ :: map _ (_ ++ _)) _
                            |- ExactlyInOne true ?L ?HT _ ] =>
                          let H' := fresh "H" in
                          destruct H as [H' H];
                          generalize (H L HT)
                        end.
                        match goal with
                        | [ |- (?A -> _) -> _ ] =>
                          let H := fresh "H" in
                          let H' := fresh "H" in
                          assert (H : A);
                          [ | intro H'; specialize (H' H) ]
                        end.
                        { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor 2; eauto ].
                          auto. }
                        match goal with
                        | [ H : ExactlyInOne false _ _ _ |- _ ] =>
                          inversion H; subst; simpl in *; eauto
                        end.
                        match goal with
                        | [ H : ?A = None |- _ ] =>
                          let H' := fresh "H" in
                          assert (H' : exists y, A = Some y)
                        end.
                        { eexists.
                          eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                          match goal with
                          | [ H : eq_map (LinTyp ?S) _
                              |- context[LinTyp ?S] ] =>
                            unfold eq_map in H;
                            rewrite H
                          end.
                          unfold get_heaptype.
                          rewrite M.gss; eauto. }
                        destructAll.
                        match goal with
                        | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                          rewrite H in H'; inversion H'
                        end. }                        
                      specialize (get_free_o _ _ _ _ _ (eq_sym Heqf) Hneq).
                      intro H'.
                      rewrite H'.
                      eexists; eauto.
          -- assert (Heq : UnrTyp x0 = UnrTyp Sp).
             { solve_inst_or_unr_typ_eq. }
             match goal with
             | [ |- context[MemUtils.dom_unr ?T] ] =>
               assert (Heq' : MemUtils.dom_unr T <--> MemUtils.dom_unr (meminst s))
             end.
             { split.
               all: unfold MemUtils.dom_unr.
               all: unfold MemUtils.dom.
               all: unfold Ensembles.Included.
               all: unfold Ensembles.In.
               all: intros.
               all: unfold Dom_ht.
               all: unfold Dom_map.
               all: unfold Ensembles.In.
               all: destructAll.
               all: assert (Hneq : Linear <> Unrestricted) by ltac:(intro H'; inversion H').
               all:
                 match goal with
                 | [ |- context[get ?L _ _] ] =>
                   specialize (get_free_diff_mem _ _ _ _ _ L (eq_sym Heqf) Hneq)
                 end;
                 intro H'.
               all: rewrite (eq_sym H') || rewrite H'.
               all: eexists; eauto. }
             rewrite Heq.
             eapply Same_set_trans; eauto.
          -- match goal with
             | [ H : Some _ = free ?L ?M ?MEM |- _ ] =>
               let H' := fresh "H" in
               assert (H' : exists mem, get L M MEM = Some mem)
             end.
             { unfold Ensembles.Same_set in *.
               unfold Ensembles.Included in *.
               unfold MemUtils.dom_lin in *.
               unfold MemUtils.dom in *.
               unfold Ensembles.In in *.
               destructAll.
               match goal with
               | [ H : context[get _ Linear (meminst ?S)]
                   |- context[get ?L Linear (meminst ?S)] ] =>
                 apply H
               end.
               right.
               unfold Dom_ht.
               unfold Dom_map.
               unfold Ensembles.In.
               eexists.
               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
               match goal with
               | [ H : eq_map (LinTyp ?S) _
                   |- context[LinTyp ?S] ] =>
                 unfold eq_map in H; rewrite H
               end.
               unfold get_heaptype.
               rewrite M.gss; eauto. }

             destructAll.
             match goal with
             | [ X : _ * _ |- _ ] => destruct X
             end.
             match goal with
             | [ H : get _ _ _ = Some _ |- _ ] =>
               specialize (get_implies_in_to_list _ _ _ _ _ H)
             end.
             intros; destructAll.
             match goal with
             | [ H : nth_error (M.to_list Linear ?MEM1) ?IDX = Some _
                 |- context[M.to_list Linear ?MEM2] ] =>
               assert (Hperm2 :
                         Permutation.Permutation
                           (remove_nth (M.to_list Linear MEM1) IDX)
                           (M.to_list Linear MEM2))
             end.
             { apply Permutation.NoDup_Permutation;
                 [ apply NoDup_remove_nth;
                   apply to_list_NoDup | apply to_list_NoDup | ].
               let x := fresh "x" in
               intro x; destruct x as [[curL curHV] curSz].
               match goal with
               | [ H : nth_error (M.to_list Linear _) _ = Some ?EL |- _ ] =>
                 rewrite (In_NoDup_remove_nth (el:=EL));
                 [ | apply to_list_NoDup | auto ]
               end.
               constructor; intros; destructAll.
               all:
                 match goal with
                 | [ H : In (_, _, _) (M.to_list _ _) |- _ ] =>
                   apply In_nth_error in H;
                   let x := fresh "x" in
                   destruct H as [x H];
                   apply in_to_list_implies_get in H
                 end.
               - match goal with
                 | [ H : (?L1, _, _) <> (?L2, _, _) |- _ ] =>
                   assert (Hloc_eq : L2 <> L1);
                   [ assert (Hloc_dec : L1 = L2 \/ L1 <> L2) by apply eq_dec_N | ]
                 end.
                 { case Hloc_dec; eauto.
                   intros; subst.
                   match goal with
                   | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                     rewrite H in H'; inversion H'; subst; eauto
                   end. }
                 match goal with
                 | [ H : get ?L2 _ _ = Some (?V, ?SZ),
                     H' : Some _ = free ?L1 _ _,
                     H'' : _ <> _
                     |- context[(_, ?V, ?SZ)] ] =>
                   specialize (get_free_o _ _ _ _ _ (eq_sym H') H'')
                 end.
                 intros.
                 match goal with
                 | [ H : get _ _ _ = get ?A ?B ?C,
                     H' : get ?A ?B ?C = Some _ |- _ ] =>
                   rewrite (eq_sym H) in H';
                   apply get_implies_in_to_list in H'
                 end.
                 destructAll; eapply nth_error_In; eauto.
               - match goal with
                 | [ |- context[(?L1, _, _) <> (?L2, _, _)] ] =>
                   assert (Hloc_neq : L2 <> L1)
                 end.
                 { intro; subst.
                   match goal with
                   | [ H : Some _ = free _ _ _ |- _ ] =>
                     specialize (get_free_s _ _ _ _ (eq_sym H))
                   end.
                   intros.
                   match goal with
                   | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                     rewrite H in H'; inversion H'
                   end. }
                 split;
                 [ | let H := fresh "H" in
                     intro H; inversion H; subst; eauto ].
                 match goal with
                 | [ H : Some _ = free ?L1 _ _,
                     H' : ?L1 <> ?L2 |- _ ] =>
                   specialize (get_free_o _ _ _ _ _ (eq_sym H) H')
                 end.
                 intros.
                 match goal with
                 | [ H : get ?A ?B ?C = get _ _ _,
                     H' : get ?A ?B ?C = Some _ |- _ ] =>
                   rewrite H in H';
                   apply get_implies_in_to_list in H'
                 end.
                 destructAll; eapply nth_error_In; eauto. }

             eapply SplitStoreTypings_permut;
             [ exact (Permutation.Permutation_app (Permutation.Permutation_map f_lin Hperm2) (Permutation.Permutation_map f_unr Hperm1)) | ].
             match goal with
             | [ H : nth_error (M.to_list Linear _) _ = _ |- _ ] =>
               specialize (nth_error_map _ _ _ f_lin H);
               let H' := fresh "H" in
               intro H';
               specialize (nth_error_Some_length _ _ _ H')
             end.
             rewrite (eq_sym remove_nth_map).
             let H := fresh "H" in
             intro H;
             rewrite (eq_sym (remove_nth_app1 H)).

             eapply SplitStoreTypings_remove_empty;
               [ eauto | rewrite nth_error_app1; eauto | ].
             
             match goal with
             | [ H : Forall2 _ (map _ _) (M.to_list Linear _) |- _ ] =>
               rewrite forall2_map in H
             end.
             match goal with
             | [ H : nth_error (M.to_list Linear _) _ = _ |- _ ] =>
               specialize (nth_error_In _ _ H)
             end.
             match goal with
             | [ H : forall _, In _ (M.to_list Linear _) -> _ |- _ ] =>
               let H' := fresh "H" in
               intro H'; specialize (H _ H')
             end.
             simpl in *; destructAll.
             match goal with
             | [ H : get_heaptype _ _ = Some ?HT \/ _,
                 H' : context[map_util.M.add (N.succ_pos _) ?HT2 _]
                 |- _ ] =>
               assert (Htyp_eq : HT = HT2)
             end.
             { match goal with
               | [ H : get_heaptype _ _ = Some ?HT \/ ?B |- _ ] =>
                 let H' := fresh "H" in
                 assert (H' : B); [ case H; intros; eauto | ]
               end.
               { match goal with
                 | [ H : context[map_util.M.add (N.succ_pos _) ?HT2 _]
                     |- get_heaptype ?L (LinTyp ?S) = _ ] =>
                   let H' := fresh "H" in
                   assert (H' : get_heaptype L (LinTyp S) = Some HT2)
                 end.
                 { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                   eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                   match goal with
                   | [ H : eq_map (LinTyp ?S) _ |- context[?S] ] =>
                     unfold eq_map in H;
                     rewrite H
                   end.
                   unfold get_heaptype.
                   rewrite M.gss; auto. }
                 match goal with
                 | [ H : SplitHeapTypings [LinTyp ?S1; LinTyp ?S2] (LinTyp ?S),
                     H' : get_heaptype ?L (LinTyp ?S1) = Some ?HT,
                     H'' : get_heaptype ?L (LinTyp ?S2) = Some _
                     |- _ ] =>
                   let H0 := fresh "H" in
                   let H1 := fresh "H" in
                   destruct H as [H0 H1];
                   generalize (H1 L HT)
                 end.
                 match goal with
                 | [ |- (?A -> _) -> _ ] =>
                   let H := fresh "H" in
                   let H' := fresh "H" in
                   assert (H : A);
                   [ | intro H'; specialize (H' H);
                       inversion H'; subst; simpl in * ]
                 end.
                 { eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                   auto. }
                 - match goal with
                   | [ H : ExactlyInOne true _ _ _ |- _ ] =>
                     inversion H; subst; simpl in *
                   end.
                   match goal with
                   | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                     rewrite H in H'; inversion H'
                   end.
                 - match goal with
                   | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                     rewrite H in H'; inversion H'
                   end. }
               match goal with
               | [ H : get_heaptype ?L (LinTyp ?S) = Some ?HT
                   |- ?HT = ?HT2 ] =>
                 let H' := fresh "H" in
                 assert (H' : get_heaptype L (LinTyp S) = Some HT2);
                 [ | rewrite H in H'; inversion H'; eauto ]
               end.
               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
               eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
               match goal with
               | [ H : eq_map (LinTyp ?S) _ |- context[?S] ] =>
                 unfold eq_map in H;
                 rewrite H
               end.
               unfold get_heaptype.
               rewrite M.gss; auto. }
             subst.
             eapply HasHeapType_Unrestricted_LinEmpty; [ eauto | | ].
             --- eapply HeapTypeUnrestricted_empty_function_ctx_rev; eauto.
             --- simpl; auto.
          -- rewrite forall2_map.
             assert (Hin : forall x, In x (M.to_list Linear t0) -> In x (M.to_list Linear (meminst s))).
             { let x := fresh "x" in
               intro x; destruct x as [[curL curHV] curSz].
               let H := fresh "H" in
               intro H;
               apply In_nth_error in H;
               let x := fresh "x" in
               destruct H as [x H];
               apply in_to_list_implies_get in H.
               match goal with
               | [ H : get ?L _ ?MEM2 = Some _,
                   H' : Some ?MEM2 = free ?L2 _ ?MEM1 |- _ ] =>
                 assert (Hloc_neq : L2 <> L);
                 [ specialize (get_free_s _ _ _ _ (eq_sym H'))
                 | specialize (get_free_o _ _ _ _ _ (eq_sym H') Hloc_neq);
                   let H'' := fresh "H" in
                   intro H''; rewrite H'' in H;
                   apply get_implies_in_to_list in H ]
               end.
               { intros; intro; subst.
                 match goal with
                 | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                   rewrite H in H'; inversion H'
                 end. }
               destructAll; eapply nth_error_In; eauto. }
             intros.
             match goal with
             | [ H : In _ (M.to_list _ _) |- _ ] =>
               specialize (Hin _ H)
             end.
             match goal with
             | [ H : forall _, In _ (M.to_list Linear ?S) -> _,
                 H' : In _ (M.to_list Linear ?S) |- _ ] =>
               specialize (H _ H') as Hht
             end.
             match goal with
             | [ H : In ?X (M.to_list _ _) |- _ ] =>
               destruct X as [T]; destruct T; subst; simpl in *
             end.
             destruct Hht as [ht].
             destructAll.
             exists ht.
             split; [ auto | ].
             split; [ | eauto ].
             match goal with
             | [ H : _ \/ _ |- _ ] =>
               case H; intros
             end.
             --- constructor; auto.
             --- constructor 2.
                 match goal with
                 | [ H : get_heaptype ?L (LinTyp ?S) = Some _,
                     H' : SplitStoreTypings (_ :: _ ++ _) ?S
                     |- _ ] =>
                   specialize (SplitStoreTypings_inv H H')
                 end.
                 intros; destructAll.
                 match goal with
                 | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                   inversion H; subst; simpl in *
                 end.
                 ---- match goal with
                      | [ H : SplitStoreTypings [_; _] ?S,
                          H' : get_heaptype _ (LinTyp ?S) = _ |- _ ] =>
                        specialize (SplitStoreTypings_inv H' H)
                      end.
                      intros; destructAll.
                      match goal with
                      | [ H : In _ [_; _] |- _ ] =>
                        inversion H; subst; simpl in *
                      end.
                      ----- match goal with
                            | [ H : eq_map (LinTyp ?S) _,
                                H' : get_heaptype _ (LinTyp ?S) = _
                                |- _ ] =>
                              unfold eq_map in H;
                              rewrite H in H';
                              unfold get_heaptype in H
                            end.
                            match goal with
                            | [ H : get_heaptype ?L (map_util.M.add (N.succ_pos ?L2) _ _) = _ |- _ ] =>
                              assert (Hloc_dec : L = L2 \/ L <> L2) by apply eq_dec_N
                            end.
                            case Hloc_dec; intros; subst.
                            ------ match goal with
                                   | [ H : In _ (M.to_list Linear ?MEM2),
                                       H' : Some ?MEM2 = free _ _ _
                                       |- _ ] =>
                                     apply In_nth_error in H;
                                     let x := fresh "x" in
                                     destruct H as [x H];
                                     apply in_to_list_implies_get in H;
                                     specialize (get_free_s _ _ _ _ (eq_sym H'));
                                     let H'' := fresh "H" in
                                     intro H''; rewrite H'' in H;
                                     inversion H
                                   end.
                            ------ unfold get_heaptype in *.
                                   match goal with
                                   | [ H : map_util.M.find (N.succ_pos ?L1) (map_util.M.add (N.succ_pos ?L2) _ _) = _ |- _ ] =>
                                     rewrite M.gso in H;
                                     [ rewrite M.gempty in H;
                                       inversion H | ]
                                   end.
                                   intro.
                                   match goal with
                                   | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                                     assert (Hloc_eq : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                   end.
                                   repeat rewrite N.pos_pred_succ in Hloc_eq.
                                   eauto.
                      ----- match goal with
                            | [ H : _ \/ False |- _ ] =>
                              case H; [ | intros; exfalso; auto ]
                            end.
                            intros; subst.
                            match goal with
                            | [ H : map_util.M.is_empty (LinTyp ?S) = true,
                                H' : get_heaptype ?L (LinTyp ?S) = Some _ |- _ ] =>
                              rewrite (get_heaptype_empty _ _ H) in H';
                              inversion H'
                            end.
                 ---- eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; eauto.
          -- rewrite forall2_map.
             assert (Hin : forall x, In x (M.to_list Unrestricted t0) -> In x (M.to_list Unrestricted (meminst s))).
             { intro; apply Permutation.Permutation_in.
               apply Permutation.Permutation_sym; auto. }
             intros.
             match goal with
             | [ H : In _ (M.to_list _ _) |- _ ] =>
               specialize (Hin _ H)
             end.
             match goal with
             | [ H : forall _, In _ (M.to_list Unrestricted ?S) -> _,
                 H' : In _ (M.to_list Unrestricted ?S) |- _ ] =>
               specialize (H _ H') as Hht
             end.
             match goal with
             | [ H : In ?X (M.to_list _ _) |- _ ] =>
               destruct X as [T]; destruct T; subst; simpl in *
             end.
             destruct Hht as [ht].
             destructAll.
             exists ht.
             eauto. }
            
      split.
      { unfold SplitStoreTypings.
        split.
        - apply Forall_cons.
          -- split; congruence.
          -- match goal with
             | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
               inversion H
             end.
             match goal with
             | [ H : UnrTyp ?S = _ |- context[UnrTyp ?S] ] =>
               rewrite H
             end.
             match goal with
             | [ H : SplitStoreTypings (_ :: _ ++ _) _ |- _ ] =>
               specialize (SplitStoreTypings_unr_same H)
             end.
             intro Heq.
             rewrite Heq.
             match goal with
             | [ H : InstTyp ?S = _ |- context[InstTyp ?S] ] =>
               rewrite H
             end.
             assumption.
        - simpl.
          apply SplitHeapTypings_cons_Empty.
          -- match goal with
             | [ H : SplitStoreTypings (_ ++ _) _ |- _ ] =>
               inversion H
             end.
             simpl in *.
             match goal with
             | [ H : UnrTyp ?S = _ |- context[UnrTyp ?S] ] =>
               rewrite H
             end.
             match goal with
             | [ H : SplitStoreTypings (_ :: _ ++ _) _ |- _ ] =>
               specialize (SplitStoreTypings_unr_same H)
             end.
             intro Heq.
             rewrite Heq.
             assumption.
          -- assumption. }
      split; [ | split; [ | split; [ | split ] ] ]; auto.
      -- match goal with
         | [ |- context[Arrow ?A ?A] ] =>
           replace A with (A ++ []) by apply app_nil_r
         end.
         eapply FrameTyp.
         --- reflexivity.
         --- eapply Forall_trivial.
             intro t.
             destruct t.
             eapply QualLeq_Top.
         --- eapply QualLeq_Top.
         --- eapply EmptyTyp; auto.
             destruct F; subst; simpl in *; solve_lcvs.
         --- solve_tvs.
      -- do 2 ltac:(eapply LCEffEqual_HasTypeLocals; eauto).
      -- match goal with
         | [ H : InstTyp ?S = _ |- context[InstTyp ?S] ] =>
           rewrite H
         end.
         auto.
      -- split; [ | congruence ].
         match goal with
         | [ H : ?A = ?B |- sub_map ?B ?A ] => rewrite H
         end.
         eapply sub_map_refl.
      -- destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         eapply LCSizeEqual_trans.
         all: apply LCEffEqual_LCSizeEqual; eauto.
      
    - (* Malloc *)
      show_tlvs Hi.
      apply Malloc_HasTypeInstruction in Hi.
      destructAll.
      inversion Hst; subst.

      match goal with
      | [ H : alloc_mem_range _ ?Q _ _ _ = Some (?L, _),
          H' : NoCapsHeapType _ ?HT = true |- _ ] =>
        assert (Hsp' :
                  exists Sstack' Ss' Sp' Sh' S',
                    InstTyp Sp = InstTyp Sp' /\
                    SplitStoreTypings (Sstack' :: map (update_unr (UnrTyp Sp')) S_ignore ++ Ss') Sp' /\
                    SplitStoreTypings [update_unr (UnrTyp Sp') Sstack; update_unr (UnrTyp Sp') Sh] Sh' /\
                    SplitStoreTypings [Sp'; Sh'] S' /\
                    if qualconstr_eq_dec Q Linear
                    then Ss' = Ss /\
                         UnrTyp Sp = UnrTyp Sp' /\
                         eq_map (LinTyp Sstack') (M.add (N.succ_pos L) HT (M.empty HeapType))
                    else Ss' = map (fun S => {|InstTyp:=InstTyp S; LinTyp:=LinTyp S; UnrTyp:=M.add (N.succ_pos L) HT (UnrTyp S)|}) Ss /\
                         UnrTyp Sp' = M.add (N.succ_pos L) HT (UnrTyp Sp) /\
                         M.is_empty (LinTyp Sstack') = true)
      end.
      { match goal with
        | [ H : HasTypeStore _ ?SH ?SP,
            H' : SplitStoreTypings [?SP; ?SH] _,
            H'' : SplitStoreTypings (_ :: _ ++ _) ?SP |- _ ] =>
          specialize (SplitStoreTypings_move_one H' H'')
        end.

        match goal with
        | [ |- context[qualconstr_eq_dec ?M Linear] ] =>
          destruct M; subst; simpl in *
        end.
        - match goal with
          | [ |- context[UnrTyp _ = ?UT] ] =>
            let S1 := fresh "S" in
            let S2 := fresh "S" in
            let H := fresh "H" in
            let H1 := fresh "H" in
            let H2 := fresh "H" in
            let H3 := fresh "H" in
            let H4 := fresh "H" in
            intro H; destruct H as [S1 [S2 [H1 [H2 [H3 H4]]]]];
            specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H1);
            specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H2);
            specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H3);
            specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H4)
          end.
          intros.

          match goal with
          | [ H : SplitStoreTypings
                    (map (update_unr _) (_ ++ ?SS))
                    (update_unr ?UT ?SPP),
              H' : SplitStoreTypings
                     (map (update_unr _) [_; ?SH]) ?SHP,
              H'' : HasTypeStore _ ?SH _,
              H''' : SplitStoreTypings
                       (map (update_unr _) [?SPP; _]) ?S |- _ ] =>
            exists (empty_LinTyp (update_unr UT SPP));
            exists (map (update_unr UT) SS);
            exists (update_unr UT SPP);
            exists SHP;
            exists S
          end.

          split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ].
          -- unfold update_unr.
             simpl.
             solve_inst_or_unr_typ_eq.
          -- match goal with
             | [ |- SplitStoreTypings _ ?S ] =>
               specialize (SplitStoreTypings_EmptyHeapTyping_r S)
             end.
             intros.
             match goal with
             | [ H : SplitStoreTypings ?Ss ?S,
                 H' : SplitStoreTypings [?S; empty_LinTyp ?S] ?S |- _ ] =>
               specialize (SplitStoreTypings_trans_gen H H')
             end.
             let H := fresh "H" in
             intro H; eapply SplitStoreTypings_permut; [ | exact H ].
             eapply Permutation.Permutation_trans; [ apply Permutation.Permutation_app_comm | ].
             simpl.
             rewrite map_app.
             apply Permutation.Permutation_refl.
          -- auto.
          -- auto.
          -- apply map_ext_in.
             let S := fresh "S" in intro S; destruct S.
             simpl; intros.
             unfold update_unr; simpl.
             match goal with
             | [ |- {| InstTyp := _; LinTyp := _; UnrTyp := M.add _ _ ?UT1 |} = {| InstTyp := _; LinTyp := _; UnrTyp := M.add _ _ ?UT2 |} ] =>
               let H := fresh "H" in
               assert (H : UT1 = UT2); [ | rewrite H; auto ]
             end.
             match goal with
             | [ H : In {| InstTyp := ?IT; LinTyp := ?LT; UnrTyp := ?UT |} ?SS |- context[?UT] ] =>
               let H' := fresh "H" in
               assert (H' : UT = typing.UnrTyp {| InstTyp := IT; LinTyp := LT; UnrTyp := UT |}) by ltac:(simpl; auto);
               rewrite H'
             end.
             apply eq_sym.
             eapply proj1.
             eapply SplitStoreTypings_eq_typs2;
             [ match goal with
               | [ H : SplitStoreTypings (_ :: _ ++ _) ?SP
                   |- SplitStoreTypings _ ?SP ] =>
                 exact H
               end | ].
             constructor 2.
             apply in_or_app; right; auto.
          -- unfold update_unr; simpl; auto.
          -- unfold empty_LinTyp; simpl; auto.
        - let H := fresh "H" in
          intro H; destruct H as [Sp'' [Sh']].
          destructAll.

          match goal with
          | [ H : HasTypeStore _ ?SH ?SP,
              H' : SplitStoreTypings [?SP; ?SH] ?S
              |- context[M.add (N.succ_pos ?LOC) ?HT _] ] =>
            let H'' := fresh "H" in
            assert (H'' : get_heaptype LOC (LinTyp S) = None);
            [ | specialize (SplitStoreTypings_add_loc (ht:=HT) H'') ]
          end.
          { match goal with
            | [ |- ?A = None ] =>
              remember A as opt;
              generalize (eq_sym Heqopt);
              case opt; intros; [ exfalso | auto ]
            end.
            match goal with
            | [ H : HasTypeStore _ ?SH ?SP,
                H' : SplitStoreTypings [?SP; ?SH] ?S,
                H'' : get_heaptype _ (LinTyp ?S) = Some _ |- _ ] =>
              specialize (SplitStoreTypings_inv H'' H')
            end.
            intros; destructAll.
            match goal with
            | [ H : In _ [_; _] |- _ ] =>
              inversion H; subst; simpl in *
            end.
            all:
              match goal with
              | [ H : HasTypeMeminst _ _ _ |- _ ] =>
                inversion H; subst; simpl in *
              end.
            all:
              match goal with
              | [ H : MemUtils.dom_lin _ <--> _ |- _ ] =>
                destruct H
              end.
            all:
              match goal with
              | [ H : (_ :|: _) \subset MemUtils.dom_lin _ |- _ ] =>
                specialize (Union_Included_l _ _ _ H);
                specialize (Union_Included_r _ _ _ H)
              end.
            all: intros.
            all: unfold Ensembles.Included in *.
            all: unfold Dom_ht in *.
            all: unfold MemUtils.dom_lin in *.
            all: unfold MemUtils.dom in *.
            all: unfold Dom_map in *.
            all: unfold Ensembles.In in *.
            all: unfold get_heaptype in *.
            2:
              match goal with
              | [ H : _ \/ False |- _ ] =>
                case H; intros; [ subst | exfalso; auto ]
              end.
            all:
              match goal with
              | [ H : forall _, (exists _, map_util.M.find (N.succ_pos _) (LinTyp ?S) = Some _) -> _,
                  H' : map_util.M.find (N.succ_pos ?L) (LinTyp ?S) = Some ?HT |- _ ] =>
                generalize (H L)
              end.
            all:
              match goal with
              | [ |- (?A -> _) -> _ ] =>
                let H := fresh "H" in
                intro H;
                let H' := fresh "H" in
                assert (H' : A);
                [ eexists; eauto | specialize (H H') ]
              end.
            all: destructAll.
            all: unfold alloc_mem_range in *.
            all:
              match goal with
              | [ H : context[alloc ?A ?B ?C ?D] |- _ ] =>
                remember (alloc A B C D) as opt;
                generalize (eq_sym Heqopt);
                revert H;
                case opt; intros;
                try match goal with
                    | [ H : None = Some _ |- _ ] => inversion H
                    end
              end.
            all:
              match goal with
              | [ X : _ * _ * _ |- _ ] =>
                let X1 := fresh "x" in
                let X2 := fresh "x" in
                destruct X as [[X1 X2] X]
              end.
            all:
              match goal with
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; subst; simpl in *
              end.
            all:
              match goal with
              | [ H : alloc _ _ _ _ = Some _ |- _ ] =>
                specialize (alloc_same_size _ _ _ _ _ _ _ H);
                intros; subst
              end.
            all:
              match goal with
              | [ H : alloc _ _ _ _ = Some (_, ?L, _) |- _ ] =>
                specialize (alloc_fresh _ _ _ _ _ _ H L)
              end.
            all:
              match goal with
              | [ |- (?A -> _) -> _ ] =>
                let H := fresh "H" in
                intro H;
                let H' := fresh "H" in
                assert (H' : A);
                [ | specialize (H H');
                    match goal with
                    | [ H : ?A = None, H' : ?A = Some _ |- _ ] =>
                      rewrite H in H'; inversion H'
                    end ]
              end.
            all: split; [ apply N.le_refl | ].
            all:
              apply N.lt_add_pos_r.
            all:
              match goal with
              | [ H : alloc _ _ _ _ = Some _ |- _ ] =>
                specialize (alloc_size _ _ _ _ _ _ H)
              end.
            all: apply N.lt_lt_0. }
          let H := fresh "H" in
          intro H; destruct H as [S'].

          match goal with
          | [ H : SplitStoreTypings [Sp''; Sh'] S,
              H' : SplitStoreTypings [?A; S] S',
              H''''' : SplitStoreTypings (?SS1 ++ ?SS2) Sp'' |- _ ] =>
            let H'' := fresh "H" in
            assert (H'' : SplitStoreTypings [S; A] S');
            [ eapply SplitStoreTypings_permut; [ | exact H' ];
              constructor | ];
            specialize (SplitStoreTypings_trans_gen H H'');
            let H''' := fresh "H" in
            intro H''';
            let H'''' := fresh "H" in
            assert (H'''' : SplitStoreTypings ([Sp''; A] ++ [Sh']) S');
            [ eapply SplitStoreTypings_permut; [ | exact H''' ];
              repeat constructor | ];
            specialize (SplitStoreTypings_split H'''');
            let H0 := fresh "H" in
            let H1 := fresh "H" in
            intro H0; destruct H0 as [Sp' [H0 H1]];
            specialize (SplitStoreTypings_trans_gen H''''' H0);
            let H2 := fresh "H" in
            intro H2;
            let H3 := fresh "H" in
            assert (H3 : SplitStoreTypings (A :: (SS1 ++ SS2)) Sp');
            [ eapply SplitStoreTypings_permut; [ | exact H2 ];
              apply Permutation.Permutation_app_comm | ]
          end.

          match goal with
          | [ H : SplitStoreTypings [Sp''; ?A] Sp' |- _ ] =>
            exists A, Ss, Sp', Sh', S'
          end.
          split; [ solve_inst_or_unr_typ_eq | ].
          split.
          { match goal with
            | [ H : SplitStoreTypings (_ :: _ ++ _) ?SPP
                |- SplitStoreTypings _ ?SPP ] =>
              specialize (SplitStoreTypings_unr_same H)
            end.
            let H := fresh "H" in
            intro H; rewrite H; auto. }
          split; [ | split; [ auto | split; [ auto | split; [ solve_inst_or_unr_typ_eq | simpl; apply eq_map_refl ] ] ] ].

          match goal with
          | [ H : SplitStoreTypings [?S1; ?S2] ?S
              |- SplitStoreTypings [_ ?UT ?S1; _ _ ?S2] ?S ] =>
            specialize (SplitStoreTypings_apply_update_unr (UT:=UT) H);
            intros;
            let H' := fresh "H" in
            assert (H' : S = update_unr UT S);
            [ | rewrite H'; auto ]
          end.
          destruct Sh'.
          unfold update_unr.
          simpl.
          match goal with
          | [ |- {| InstTyp := _; LinTyp := _; UnrTyp := ?UT1 |} = {| InstTyp := _; LinTyp := _; UnrTyp := ?UT2 |} ] =>
            let H := fresh "H" in
            assert (H : UT1 = UT2); [ | rewrite H; auto ]
          end.
          solve_inst_or_unr_typ_eq. }
        
      destruct Hsp' as [Sstack' [Ss' [Sp' [Sh' [S']]]]].
      destructAll.

      match goal with
      | [ H : alloc_mem_range _ ?Q _ _ _ = Some (?L, _) |- _ ] =>
        assert (Hdisjoint : is_linear Q = true \/ get_heaptype L (UnrTyp Sp) = None)
      end.
      { match goal with
        | [ |- is_linear ?Q = true \/ _ ] =>
          destruct Q; subst; simpl in *; [ right | left; eauto ]
        end.
        match goal with
        | [ |- ?A = None ] =>
          remember A as opt
        end.
        revert Heqopt.
        case opt; eauto.
        intros; subst.
        repeat match goal with
        | [ H : ?A = ?B, H' : context[?A] |- _ ] => rewrite H in H'
        end.
        match goal with
        | [ H : HasTypeMeminst _ _ _ |- _ ] => inversion H; subst; simpl in *
        end.
        repeat match goal with
        | [ H : _ <--> _ |- _ ] => inversion H; subst; simpl in *; clear H
        end.
        match goal with
        | [ H : Dom_ht _ :|: Dom_ht (UnrTyp Sp) \subset _,
            H' : Some _ = get_heaptype ?L _ |- _ ] =>
          specialize (H L)
        end.
        unfold Ensembles.In in *.
        match goal with
        | [ H : ?A -> MemUtils.dom_unr _ _ |- _ ] =>
          let H' := fresh "H" in
          assert (H' : A); [ | specialize (H H'); unfold MemUtils.dom_unr in H; unfold MemUtils.dom in H ]
        end.
        { constructor 2.
          unfold Ensembles.In.
          unfold Dom_ht.
          unfold Ensembles.In.
          unfold Dom_map.
          eexists; eauto. }
        destructAll.
        match goal with
        | [ H : get ?L ?M ?MEM = Some _ |- _ ] =>
          let H' := fresh "H" in
          assert (H' : get L M MEM = None);
          [ | rewrite H' in H; inversion H ]
        end.
        unfold alloc_mem_range in *.
        match goal with
        | [ H : context[alloc ?A ?B ?C ?D] |- _ ] =>
          remember (alloc A B C D) as allobj;
          revert Heqallobj; revert H;
          case allobj; intros; subst; simpl in *;
            try match goal with
                | [ H : None = Some _ |- _ ] => inversion H
                end
        end.
        match goal with
        | [ X : _ * _ * _  |- _ ] =>
          destruct X as [[curT curL] curSz]
        end.
        match goal with
        | [ H : Some _ = Some _ |- _ ] =>
          inversion H; subst; simpl in *
        end.
        match goal with
        | [ H : Some _ = alloc _ _ _ _ |- _ ] =>
          specialize (alloc_same_size _ _ _ _ _ _ _ (eq_sym H))
        end.
        intros; subst.
        eapply alloc_fresh; [ eapply eq_sym; eauto | ].
        split.
        ---- apply N.le_refl.
        ---- apply N.lt_add_pos_r.
             match goal with
             | [ H : Some _ = alloc _ _ _ _ |- _ ] =>
               specialize (alloc_size _ _ _ _ _ _ (eq_sym H))
             end.
             apply N.lt_lt_0. }

      exists Sp', Sh', Sstack', Ss', L'.
      split.
      { econstructor; try eassumption.
        - match goal with
          | [ H : alloc_mem_range ?S _ _ _ _ = Some (_, ?ST) |- _ ] =>
            assert (Hinst1 : inst S = inst ST);
            [ unfold alloc_mem_range in H; simpl in H | ]
          end.
          { match goal with
            | [ H : context[alloc ?A ?B ?C ?D] |- _ ] =>
              remember (alloc A B C D) as obj'
            end.
            destruct obj'.
            - destruct_prs.
              match goal with
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; subst; auto
              end.
            - match goal with
              | [ H : None = Some _ |- _ ] => inversion H
              end. }
          
          match goal with
          | [ H : alloc_mem_range _ _ _ _ _ = Some (_, ?S),
              H' : if qualconstr_eq_dec ?M _ then ?SP = _ else _ = ?SP |- _ ] =>
            assert (Hinst2 : inst S = inst SP);
            [ destruct M; simpl in *; subst; auto | ]
          end.
          { unfold add_out_set in *.
            match goal with
            | [ |- context[inst (if ?B then _ else _)] ] =>
              remember B as obj''; destruct obj'';
              subst; simpl; auto
            end. }
          rewrite (eq_sym Hinst1) in Hinst2.
          rewrite (eq_sym Hinst2).
          match goal with
          | [ H : _ = ?A |- Forall2 _ _ ?A ] => rewrite <-H
          end.
          assert (Hinsttyp : InstTyp S = InstTyp S') by solve_inst_or_unr_typ_eq.
          rewrite <-Hinsttyp.
          auto.
        - unfold alloc_mem_range in *.
          match goal with
          | [ H : context[alloc ?MEM ?M ?SZ ?HV] |- _ ] =>
            remember (alloc MEM M SZ HV) as allocm;
            revert H; revert Heqallocm;
            case allocm; intros;
            [ | match goal with
                | [ H : None = Some _ |- _ ] => inversion H
                end ]
          end.
          match goal with
          | [ X : _ * _ * _ |- _ ] =>
            destruct X as [[newT newL] newSz]
          end.
          match goal with
          | [ H : Some _ = Some _ |- _ ] =>
            inversion H; subst; simpl in *
          end.          
          match goal with
          | [ H : HasTypeMeminst _ _ _ |- _ ] =>
            inversion H; subst; simpl in *
          end.
          match goal with
          | [ H : Some (?NEWMEM, _, _) = alloc _ _ _ _
              |- context[meminst ?S] ] =>
            let H' := fresh "H" in
            assert (H' : meminst S = NEWMEM);
            [ | subst ]
          end.
          { match goal with
            | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
              destruct M; subst; simpl in *; subst; simpl in *;
              [ auto | ]
            end.
            unfold add_out_set.
            match goal with
            | [ |- context[L.has_urn_ptr_HeapValue ?HV] ] =>
              case (L.has_urn_ptr_HeapValue HV); simpl in *; auto
            end. }
            
          derive_mappings f_lin f_unr.

          match goal with
          | [ H : Some (_, ?L, _) = alloc _ ?M _ ?HV |- _ ] =>
            specialize (alloc_same_size _ _ _ _ _ _ _ (eq_sym H))
          end.
          intros; subst.

          match goal with
          | [ H : MemUtils.dom_unr ?MEM <--> _ :|: Dom_ht (UnrTyp ?S) |- _ ] =>
            let H' := fresh "H" in
            assert (H' : forall l hv,
                       get l Unrestricted MEM = Some hv ->
                       exists ht,
                         get_heaptype l (UnrTyp S) = Some ht);
            [ destruct H | ]
          end.
          { unfold Dom_ht in *.
            unfold Dom_map in *.
            unfold MemUtils.dom_unr in *.
            unfold MemUtils.dom in *.
            unfold Ensembles.Included in *.
            unfold Ensembles.In in *.
            intros.
            match goal with
            | [ H : forall _, _ -> (_ :|: (fun l => exists y, map_util.M.find _ (UnrTyp ?SP) = Some _)) _
                |- context[get_heaptype ?L (UnrTyp ?SP)] ] =>
              generalize (H L)
            end.
            match goal with
            | [ |- (?A -> _) -> _ ] =>
              let H := fresh "H" in
              let H' := fresh "H" in
              assert (H : A);
              [ | intro H'; specialize (H' H) ]
            end.
            { eexists; eauto. }
            match goal with
            | [ H : Ensembles.Union _ _ _ _ |- _ ] =>
              inversion H; subst; simpl in *
            end.
            all: unfold Ensembles.In in *.
            all: destructAll.
            ----- match goal with
                  | [ H : map_util.M.find (N.succ_pos ?L) (UnrTyp ?S1) = Some _,
                      H' : SplitStoreTypings [?S2; ?S1] ?S
                      |- context[UnrTyp ?S2] ] =>
                    let H'' := fresh "H" in
                    assert (H'' : UnrTyp S2 = UnrTyp S1) by solve_inst_or_unr_typ_eq;
                    rewrite H''
                  end.
                  eexists; eauto.
            ----- eexists; eauto. }

          match goal with
          | [ H : Some (?MEM2, _, _) = alloc ?MEM _ _ _ |- _ ] =>
            let H' := fresh "H" in
            assert (H' : forall loc q ht,
                       get loc q MEM = Some ht ->
                       get loc q MEM2 = Some ht)
          end.
          { intros.
            match goal with
            | [ H : Some (_, _, _) = alloc _ ?M _ _
                |- get _ ?M2 _ = Some _ ] =>
              specialize (qualconstr_eq_dec M2 M)
            end.
            let H := fresh "H" in intro H; case H; intros; subst.
            - match goal with
              | [ H : Some (_, ?L, _) = alloc _ _ _ _,
                  H' : get ?L2 _ _ = Some _ |- _ ] =>
                let H'' := fresh "H" in
                assert (H'' : L2 = L \/ L2 <> L) by apply eq_dec_N;
                case H''; intros; subst
              end.
              -- match goal with
                 | [ H : Some (_, ?L, _) = alloc _ _ _ _ |- _ ] =>
                   specialize (alloc_fresh _ _ _ _ _ _ (eq_sym H) L)
                 end.
                 match goal with
                 | [ |- (?A -> _) -> _ ] =>
                   let H := fresh "H" in
                   let H' := fresh "H" in
                   assert (H : A);
                   [ | intro H'; specialize (H' H) ]
                 end.
                 { split; [ apply N.le_refl | ].
                   apply N.lt_add_pos_r.
                   eapply OrdersEx.N_as_OT.lt_lt_0; eauto.
                   eapply alloc_size.
                   eapply eq_sym; eauto. }
                 match goal with
                 | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                   rewrite H in H'; inversion H'
                 end.
              -- match goal with
                 | [ H : Some (_, ?L, _) = alloc _ _ _ _,
                     H' : ?L2 <> ?L |- _ ] =>
                   specialize (get_alloc_other_loc _ _ _ _ _ _ _ (eq_sym H) H');
                   let H'' := fresh "H" in
                   intro H''; rewrite H''; auto
                 end.
            - match goal with
              | [ H : Some _ = alloc _ ?M _ _,
                  H' : ?M2 <> ?M,
                  H'' : get ?L2 ?M2 _ = Some _ |- _ ] =>
                specialize (get_alloc_other_mem _ _ _ L2 _ _ _ _ (eq_sym H) H');
                let H''' := fresh "H" in
                intro H'''; rewrite H'' in H'''
              end.
              auto. }

          match goal with
          | [ H : Some _ = alloc ?MEM _ _ _,
              H' : MemUtils.dom_lin ?MEM <-->
                   Dom_ht (LinTyp ?OSH) :|: Dom_ht (LinTyp ?OSP)
              |- HasTypeMeminst ?SH ?SP _ ] =>
            let H' := fresh "H" in
            assert (H' : forall loc ht,
                       (get_heaptype loc (LinTyp OSH) = Some ht \/
                        get_heaptype loc (LinTyp OSP) = Some ht) ->
                       (get_heaptype loc (LinTyp SH) = Some ht \/
                        get_heaptype loc (LinTyp SP) = Some ht))
          end.
          { intros.
            match goal with
            | [ H : get_heaptype _ _ = Some _ \/ _ |- _ ] =>
              case H; intros
            end.
            - left.
              eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor 2; constructor; auto ].
              unfold update_unr.
              simpl.
              unfold get_heaptype; auto.
            - match goal with
              | [ H : get_heaptype ?L (LinTyp ?SP) = Some _,
                  H' : SplitStoreTypings (_ :: _ ++ _) ?SP |- _ ] =>
                specialize (SplitStoreTypings_inv H H')
              end.
              intros; destructAll.
              match goal with
              | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                inversion H; subst; simpl in *
              end.
              -- left.
                 unfold Ensembles.In.
                 eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                 unfold update_unr; simpl.
                 eauto.
              -- right.
                 unfold Ensembles.In.
                 
                 eapply SplitStoreTypings_get_heaptype_LinTyp_gen;
                   [ | | eauto ]; [ eauto | ].
                 constructor 2.
                 rewrite map_app; apply in_or_app.
                 match goal with
                 | [ H : In _ (_ ++ _) |- _ ] =>
                   apply in_app_or in H; case H; intros
                 end.
                 --- left.
                     rewrite map_map_compose.
                     unfold update_unr; simpl.
                     apply in_map; auto.
                 --- right.
                     match goal with
                     | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
                       destruct M; subst; simpl in *;
                       destructAll; subst; simpl in *
                     end.
                     ---- rewrite map_map_compose.
                          unfold update_unr; simpl.
                          apply in_map; auto.
                     ---- apply in_map; auto. } 

          match goal with
          | [ H : Some _ = alloc ?MEM _ _ _
              |- HasTypeMeminst ?SH ?SP _ ] =>
            let H' := fresh "H" in
            assert (H' : MemUtils.dom_lin MEM \subset Dom_ht (LinTyp SH) :|: Dom_ht (LinTyp SP))
          end.
          { match goal with
            | [ H : ?A <--> ?B |- ?A \subset ?C ] =>
              inversion H; subst; simpl in *
            end.
            eapply Included_trans; [ eauto | ].
            unfold Dom_ht.
            unfold Dom_map.
            unfold Ensembles.Included.
            unfold Ensembles.In.
            intros.
            match goal with
            | [ H : (_ :|: _) _ |- _ ] =>
              inversion H; subst; simpl in *
            end.
            all: unfold Ensembles.In in *.
            all: destructAll.
            - match goal with
              | [ H : forall _ _, get_heaptype _ (LinTyp ?S) = Some _ \/ _ -> _,
                  H' : map_util.M.find _ (LinTyp ?S) = Some _ |- _ ] =>
                specialize (H _ _ (or_introl H'));
                case H; [ left | right ]
              end.
              all: unfold Ensembles.In.
              all: eexists; eauto.
            - match goal with
              | [ H : forall _ _, _ \/ get_heaptype _ (LinTyp ?S) = Some _ -> _,
                  H' : map_util.M.find _ (LinTyp ?S) = Some _ |- _ ] =>
                specialize (H _ _ (or_intror H'));
                case H; [ left | right ]
              end.
              all: unfold Ensembles.In.
              all: eexists; eauto. }

          match goal with
          | [ H : Some _ = alloc ?MEM _ _ _,
              H' : HasTypeStore _ _ ?OSP
              |- HasTypeMeminst ?SH ?SP _ ] =>
            let H' := fresh "H" in
            assert (H' : forall loc ht,
                       get_heaptype loc (UnrTyp OSP) = Some ht ->
                       get_heaptype loc (UnrTyp SP) = Some ht)
          end.
          { intros.
            match goal with
            | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
              destruct M; subst; simpl in *;
              destructAll; subst; simpl in *
            end.
            - match goal with
              | [ H : UnrTyp ?SP = _
                  |- context[UnrTyp ?SP] ] =>
                rewrite H
              end.
              match goal with
              | [ H : Some (_, ?L, _) = alloc _ _ _ _ |- _ ] =>
                specialize (alloc_fresh _ _ _ _ _ _ (eq_sym H) L)
              end.
              match goal with
              | [ |- (?A -> _) -> _ ] =>
                let H := fresh "H" in
                let H' := fresh "H" in
                assert (H : A);
                [ | intro H'; specialize (H' H) ]
              end.
              { split; [ apply N.le_refl | ].
                apply N.lt_add_pos_r.
                eapply OrdersEx.N_as_OT.lt_lt_0; eauto.
                eapply alloc_size.
                eapply eq_sym; eauto. }
              match goal with
              | [ H : MemUtils.dom_unr _ <--> _ |- _ ] =>
                inversion H; subst; simpl in *
              end.
              unfold Ensembles.Included in *.
              unfold MemUtils.dom_unr in *.
              unfold MemUtils.dom in *.
              unfold Dom_ht in *.
              unfold Dom_map in *.
              unfold Ensembles.In in *.
              match goal with
              | [ H : forall _, (_ :|: _) _ -> exists v, get _ _ _ = Some _
                  |- get_heaptype ?L _ = Some _ ] =>
                generalize (H L)
              end.
              match goal with
              | [ |- (?A -> _) -> _ ] =>
                let H := fresh "H" in
                let H' := fresh "H" in
                assert (H : A);
                [ | intro H'; specialize (H' H) ]
              end.
              { right.
                unfold Ensembles.In.
                eexists; eauto. }
              destructAll.
              match goal with
              | [ H : get ?L1 ?M ?MEM = Some _,
                  H' : get ?L2 ?M ?MEM = None |- _ ] =>
                let H'' := fresh "H" in
                assert (H'' : L1 <> L2);
                [ intro; subst; rewrite H in H'; inversion H' | ]
              end.
              unfold get_heaptype.
              rewrite M.gso; [ unfold get_heaptype in *; auto | ].
              intro.
              match goal with
              | [ H : N.succ_pos ?L1 = N.succ_pos ?L2 |- _ ] =>
                let H' := fresh "H" in
                assert (H' : Pos.pred_N (N.succ_pos L1) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
              end.
              repeat rewrite N.pos_pred_succ in *; eauto.
            - match goal with
              | [ H : ?A = ?UT |- context[?UT] ] =>
                rewrite (eq_sym H)
              end.
              auto. }

          match goal with
          | [ H : Some _ = alloc ?MEM _ _ _
              |- HasTypeMeminst ?SH ?SP _ ] =>
            let H' := fresh "H" in
            assert (H' : MemUtils.dom_unr MEM \subset Dom_ht (UnrTyp SP))
          end.
          { match goal with
            | [ H : HasTypeStore _ ?SH ?SP |- _ ] =>
              let H' := fresh "H" in
              assert (H' : UnrTyp SH = UnrTyp SP) by solve_inst_or_unr_typ_eq;
              repeat ltac:(
                     revert H';
                     match goal with
                     | [ H'' : context[UnrTyp SH] |- _ ] =>
                       intro H'; rewrite H' in H''
                     end
                     )
            end.
            match goal with
            | [ H : ?ST1 <-->
                    Dom_ht (UnrTyp ?S) :|: Dom_ht (UnrTyp ?S) |- _ ] =>
              specialize (Same_set_trans _ _ _ H (Union_idempotent (Dom_ht (UnrTyp S))))
            end.
            let H := fresh "H" in intro H; inversion H.
            eapply Included_trans; [ eauto | ].
            unfold Dom_ht.
            unfold Dom_map.
            unfold Ensembles.Included.
            unfold Ensembles.In.
            intros.
            destructAll.
            match goal with
            | [ H : forall _ _, get_heaptype _ (UnrTyp ?S) = Some _ -> _,
                H' : map_util.M.find _ (UnrTyp ?S) = Some _ |- _ ] =>
              specialize (H _ _ H')
            end.
            eexists; eauto. }

          match goal with
          | [ H : HasTypeStore _ _ ?SP,
              H' : Some (_, ?L, _) = alloc _ _ _ _,
              H'' : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
            let H'' := fresh "H" in
            assert (H'' : M = Unrestricted -> get_heaptype L (UnrTyp SP) = None)
          end.
          { intros; subst.
            match goal with
            | [ |- ?A = None ] =>
              remember A as opt;
              generalize (eq_sym Heqopt); case opt; try auto;
              intros
            end.
            match goal with
            | [ H : context[Dom_ht (UnrTyp _)] |- _ ] =>
              inversion H; subst; simpl in *
            end.
            match goal with
            | [ H : Ensembles.Included _ (Ensembles.Union _ _ _) _,
                H' : get_heaptype ?L (UnrTyp _) = Some _ |- _ ] =>
              unfold Ensembles.Included in H;
              specialize (H L)
            end.
            match goal with
            | [ H : ?A -> Ensembles.In _ _ _ |- _ ] =>
              let H' := fresh "H" in
              assert (H' : A); [ | specialize (H H') ]
            end.
            { right.
              unfold Dom_ht.
              unfold Dom_map.
              unfold Ensembles.In.
              unfold get_heaptype in *.
              eexists; eauto. }
            unfold Ensembles.In in *.
            unfold MemUtils.dom_unr in *.
            unfold MemUtils.dom in *.
            destructAll.
            match goal with
            | [ H : Some (_, ?L, _) = alloc _ _ _ _ |- _ ] =>
              specialize (alloc_fresh _ _ _ _ _ _ (eq_sym H) L)
            end.
            match goal with
            | [ |- (?A -> _) -> _ ] =>
              let H := fresh "H" in
              let H' := fresh "H" in
              assert (H : A);
              [ | intro H'; specialize (H' H) ]
            end.
            { split; [ apply N.le_refl | ].
              apply N.lt_add_pos_r.
              eapply OrdersEx.N_as_OT.lt_lt_0; eauto.
              eapply alloc_size.
              eapply eq_sym; eauto. }
            match goal with
            | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
              rewrite H in H'; inversion H'
            end. }

          destructAll.
          match goal with
          | [ H : Some (_, ?L, _) = alloc _ ?M _ ?HV,
              H' : HasHeapType ?S _ ?HV _,
              H'' : context[update_unr ?UT ?S]
              |- HasTypeMeminst ?SH ?SP ?NEWMEM ] =>
            remember (map (update_unr UT) (map (fun '(loc, hv, len) => if (andb (is_linear M) (BinNatDef.N.eqb loc L)) then S else f_lin (loc, hv, len)) (M.to_list Linear NEWMEM))) as S_lin';
            remember (map (update_unr UT) (map (fun '(loc, hv, len) => if (andb (negb (is_linear M)) (BinNatDef.N.eqb loc L)) then S else f_unr (loc, hv, len)) (M.to_list Unrestricted NEWMEM))) as S_unr'
          end.
          apply (MeminstT _ S_lin' S_unr').
          4-5: destructAll.
          4-5: rewrite map_map_compose.
          4-5: rewrite forall2_map; intros.
          4-5:
             match goal with
             | [ X : _ * _ * _ |- _ ] =>
               destruct X as [[curL curHV] curSz]
             end.
          4-5:
            match goal with
            | [ H : In (_, _, _) (M.to_list _ _) |- _ ] =>
              specialize (In_nth_error _ _ H)
            end.
          4-5: intros; destructAll.
          4-5:
            match goal with
            | [ H : nth_error (M.to_list _ _) _ = Some _ |- _ ] =>
              specialize (in_to_list_implies_get _ _ _ _ _ _ H)
            end.
          4-5: intros.
          4-5: unfold alloc_mem_range in *.
          all:
            assert (Hqneq1 : Linear <> Unrestricted) by
              ltac:(let H := fresh "H" in
                    intro H; inversion H).
          all:
            assert (Hqneq2 : Unrestricted <> Linear) by
              ltac:(let H := fresh "H" in
                    intro H; inversion H).
          4-5:
            match goal with
            | [ H : Some (_, ?L1, _) = alloc ?MEM ?M1 ?SZ1 ?HV1,
                H' : In (?L2, ?HV2, ?SZ2) (M.to_list ?M2 _)
                |- context[(?L2 =? ?L1)%N] ] =>
              let H0 := fresh "H" in
              assert (H0 :
                        (L1 = L2 /\ HV1 = HV2 /\ SZ1 = SZ2 /\ M1 = M2) \/
                        ((M1 <> M2 \/ L1 <> L2) /\ In (L2, HV2, SZ2) (M.to_list M2 MEM)));
              [ destruct M1; subst; simpl in *;
                match goal with
                | [ H : Some _ = alloc _ ?M _ _,
                    H' : In (_, _, _) (M.to_list ?M _) |- _ ] =>
                  assert (Hloc_eq : L2 = L1 \/ L2 <> L1) by apply eq_dec_N;
                  case Hloc_eq; intros;
                  [ subst; left | right ]
                | [ |- _ ] => right
                end
              | case H0; intros; destructAll; subst; simpl in * ]
            | [ |- _ ] => idtac
            end.
          all:
            match goal with
            | [ H : Some _ = alloc _ ?M _ _,
                H' : ?M2 <> ?M
                |- _ /\ In (?L, _, _) (M.to_list ?M2 _) ] =>
              specialize (get_alloc_other_mem _ _ _ L _ _ _ _ (eq_sym H) H')
            | [ H : Some _ = alloc _ ?M _ _,
                H' : ?L2 <> ?L
                |- _ /\ In (?L2, _, _) (M.to_list ?M _) ] =>
              specialize (get_alloc_other_loc _ _ _ L2 _ _ _ (eq_sym H) H')
            | [ |- _ ] => idtac
            end.
         all:
           match goal with
           | [ H : get ?L ?M ?MEM = Some _
               |- get ?L ?M ?MEM = get ?L ?M ?MEM2 -> _ ] =>
             let H' := fresh "H" in
             intro H'; rewrite H' in H;
             apply get_implies_in_to_list in H;
             destructAll; split;
             [ eauto | eapply nth_error_In; eauto ]
           | [ |- _ ] => idtac
           end.
         all:
           match goal with
           | [ H : get ?L ?M ?MEM2 = Some _,
               H' : Some (_, ?L, _) = alloc ?MEM1 ?M _ _
               |- _ ] =>
             specialize (get_alloc_same _ _ _ _ _ _ (eq_sym H'));
             let H'' := fresh "H" in
             intro H''; rewrite H'' in H; inversion H; subst; eauto
           | [ |- _ ] => idtac
           end.
         all: try rewrite N.eqb_refl.
         all:
           try match goal with
               | [ |- context[if ?B then _ else _ ] ] =>
                 let H' := fresh "H" in
                 assert (H' : B = false); [ | rewrite H' ]
               end.               
         all:
           try match goal with
               | [ |- context[is_linear ?M] ] =>
                 destruct M; subst; simpl in *; try auto
               end.
         all:
           try match goal with
               | [ H : ?A <> ?A \/ ?B |- _ ] =>
                 case H; intros;
                 [ exfalso | rewrite OrdersEx.N_as_OT.eqb_neq ];
                 eauto
               end.
         all: 
           try match goal with
               | [ H : HasHeapType _ _ ?HV ?HT |-
                   context[HasHeapType _ _ ?HV _] ] =>
                 exists HT
               end.
         all:
           try match goal with
               | [ H : NoCapsHeapType (heapable ?F) _ = true,
                   H' : Function_Ctx_empty ?F
                   |- NoCapsHeapType _ _ = true /\ _ ] =>
                 split; [ destruct F; subst; simpl in *;
                          unfold heapable in H; simpl in *;
                          unfold Function_Ctx_empty in H';
                          destructAll; simpl in *;
                          subst; simpl in *; eauto | ]
               end.
         all:
           try match goal with
               | [ |- ?A /\ _ ] => split
               end.
         4:{
           right.
           eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
           destructAll.
           match goal with
           | [ H : eq_map (LinTyp ?S) _ |- context[LinTyp ?S] ] =>
             unfold eq_map in H; rewrite H
           end.
           unfold get_heaptype; rewrite M.gss; eauto.
         }
         6:{
           unfold update_unr.
           simpl.
           destructAll.
           match goal with
           | [ H : UnrTyp ?S = _ |- context[UnrTyp ?S] ] =>
             rewrite H
           end.
           unfold get_heaptype; rewrite M.gss; eauto.
         }

         all:
           try match goal with
               | [ |- HasHeapType _ _ _ _ /\ _ ] =>
                 split;
                 [ eapply HasHeapType_empty_function_ctx_rev;
                   [ | eauto ] | ]
               end.
         4:{
           destructAll.
           match goal with
           | [ H : ?A = ?B |- context[?B] ] => rewrite (eq_sym H)
           end.
           match goal with
           | [ |- context[update_unr ?A ?B] ] =>
             let H := fresh "H" in
             assert (H : update_unr A B = B);
             [ destruct B; subst; simpl in * | rewrite H ]
           end.
           { unfold update_unr; simpl.
             match goal with
             | [ H : SplitStoreTypings (_ :: _ ++ _) ?SP
                 |- context[typing.UnrTyp ?SP] ] =>
               inversion H; subst; simpl in *
             end.
             match goal with
             | [ H : Forall _ (_ :: ?Ss1 ++ ?Ss2),
                 H' : SplitStoreTypings (_ :: ?Ss1 ++ ?Ss2) ?SP
                 |- context[typing.UnrTyp ?SP] ] =>
               inversion H; subst; simpl in *
             end.
             destructAll; subst; auto. }
           eapply HasHeapType_update_linear_ctx_rev; eauto.
         }
         6:{
           destructAll.
           match goal with
           | [ H : UnrTyp ?SP = _ |- context[UnrTyp ?SP] ] =>
             rewrite H
           end.
           match goal with
           | [ |- context[update_unr (M.add _ _ ?UT) ?S] ] =>
             let H := fresh "H" in
             assert (H : UT = UnrTyp S) by solve_inst_or_unr_typ_eq;
             rewrite H
           end.
           apply HasHeapType_update_unr_add_loc;
             [ eapply HasHeapType_update_linear_ctx_rev; eauto | ].
           match goal with
           | [ H : UnrTyp ?S1 = UnrTyp ?S2 |- context[UnrTyp ?S2] ] =>
             rewrite (eq_sym H)
           end.
           eauto.
         }
         all:
           try match goal with
               | [ H : Function_Ctx_empty ?F
                   |- _ /\ HeapTypeValid _ _ ] =>
                 split; [ | eapply HasHeapType_HeapTypeValid;
                            eapply HasHeapType_empty_function_ctx_rev;
                            eauto;
                            destruct F; subst; simpl in *;
                            unfold Function_Ctx_empty in H;
                            destructAll; simpl in *;
                            subst; simpl in *;
                            unfold Function_Ctx_empty; eauto ]
               end.
         
         all:
           try match goal with
               | [ H : RoomForStrongUpdates (N.of_nat ?SZ1) ?HT
                   |- RoomForStrongUpdates (N.of_nat ?SZ2) ?HT ] =>
                 let H' := fresh "H" in
                 assert (H' : SZ2 = SZ1);
                 [ | rewrite H'; auto ]
               end.
         all:
           try match goal with
               | [ |- to_size _ ?P1 = to_size _ ?P2 ] =>
                 rewrite ProofIrrelevance.proof_irrelevance
                   with (p1 := P1) (p2 := P2);
                 auto
               end.         

         all:
           try match goal with
               | [ H : (_ = _ /\ _ = _ /\ _ = _ /\ _ = _) \/ _ |- _ ] =>
                 case H; intros; destructAll; subst;
                 try match goal with
                     | [ H' : ?A <> ?A \/ ?B <> ?B |- _ ] =>
                       case H'; intros; exfalso; eauto
                     end
               end.
         all:
           try match goal with
               | [ H : forall _, In _ (M.to_list ?M _) -> _,
                   H' : In _ (M.to_list ?M _) |- _ ] =>
                 specialize (H _ H'); simpl in *;
                 let ht := fresh "ht" in destruct H as [ht];
                 destructAll; exists ht;
                 split;
                 [ auto | split; [ try auto | split; [ | eauto ] ] ]
               end.
         all:
           try match goal with
               | [ H : context[qualconstr_eq_dec ?M Linear]
                   |- HasHeapType _ _ _ _ ] =>
                 destruct M; subst; simpl in *; destructAll
               end.
         all:
           try match goal with
               | [ H : UnrTyp ?S1 = UnrTyp ?S2
                   |- context[update_unr (UnrTyp ?S2) ?S3] ] =>
                 rewrite (eq_sym H);
                 let H' := fresh "H" in
	             assert (H' : UnrTyp S1 = UnrTyp S3);
                 [ | rewrite H';
                     remember S3 as curs;
                     generalize (eq_sym Heqcurs);
                     case curs; intros;
                     unfold update_unr; subst; simpl in *;
                     match goal with
                     | [ H : ?B = ?A |- HasHeapType ?A _ _ _ ] =>
                       rewrite (eq_sym H); auto
                     end ]
               end.

         all:
           try match goal with
               | [ H : UnrTyp ?S1 = M.add _ _ (UnrTyp ?S2)
                   |- context[update_unr (UnrTyp ?S1) ?S3] ] =>
                 rewrite H;
                 let H' := fresh "H" in
                 assert (H' : UnrTyp S2 = UnrTyp S3);
                 [ | rewrite H';
                     apply HasHeapType_update_unr_add_loc; auto ]
               end.
         all:
           try match goal with
               | [ H' : HasTypeStore _ _ ?SP
                   |- get_heaptype ?L ?UT1 = None ] =>
                 let H'' := fresh "H" in
                 assert (H'' : UT1 = UnrTyp SP);
                 [ apply eq_sym | rewrite H''; auto ]
               end.
         

         all:
           try match goal with
               | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?SH
                   |- UnrTyp ?SP = _ ] =>
                 let H' := fresh "H" in
                 assert (H' : UnrTyp SP = UnrTyp SH) by solve_inst_or_unr_typ_eq;
                 rewrite H';
                 apply eq_sym; eapply proj1;
                 eapply SplitStoreTypings_eq_typs2; [ eauto | ]
               end.
         all:
           try match goal with
               | [ |- In (?F1 _) (map ?F1 _ ++ _) ] =>
                 apply in_or_app; left; apply in_map; auto
               | [ |- In (?F2 _) (_ ++ map ?F2 _) ] =>
                 apply in_or_app; right; apply in_map; auto
               end.

         1-2: constructor.
         1-4: unfold Ensembles.Included in *.
         1-4: intros.
         1-4: unfold MemUtils.dom_lin in *.
         1-4: unfold MemUtils.dom_unr in *.
         1-4: unfold MemUtils.dom in *.
         1-4: unfold Dom_ht in *.
         1-4: unfold Dom_map in *.
         1-4: unfold Ensembles.In in *.
         1-4: destructAll.

         -- match goal with
            | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
              destruct M; subst; simpl in *;
              destructAll; subst; simpl in *
            end.
            --- match goal with
                | [ H : Some (_, _, _) = alloc _ ?M _ _,
                    H' : get ?L ?M2 _ = Some _,
                    H'' : ?M2 <> ?M |- _ ] =>
                  specialize (get_alloc_other_mem _ _ _ L _ _ _ _ (eq_sym H) H'');
                  let H''' := fresh "H" in
                  intro H'''; rewrite H''' in H'
                end.
                match goal with
                | [ H : forall _, _ -> Ensembles.Union _ _ _ _ |- _ ] =>
                  eapply H
                end.
                eexists; eauto.
            --- match goal with
                | [ H : Some (?MEM2, ?L, _) = alloc _ _ _ _,
                    H' : get ?L2 Linear ?MEM2 = Some _ |- _ ] =>
                  let H'' := fresh "H" in
                  assert (H'' : L2 = L \/ L2 <> L) by apply eq_dec_N;
                  case H''; intros; subst
                end.
                ---- right.
                     unfold Ensembles.In.
                     eexists.
                     eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                     match goal with
                     | [ H : eq_map (LinTyp ?S) _ |- context[LinTyp ?S] ] =>
                       rewrite H
                     end.
                     unfold get_heaptype.
                     rewrite M.gss; auto.
                ---- match goal with
                     | [ H : Some (_, ?L, _) = alloc _ _ _ _,
                         H' : get ?L2 _ _ = Some _,
                         H'' : ?L2 <> ?L |- _ ] =>
                       specialize (get_alloc_other_loc _ _ _ _ _ _ _ (eq_sym H) H'');
                       let H''' := fresh "H" in
                       intro H'''; rewrite H''' in H'
                     end.
                     match goal with
                     | [ H : forall _, _ -> Ensembles.Union _ _ _ _ |- _ ] =>
                       eapply H
                     end.
                     eexists; eauto.
         -- match goal with
            | [ H : Ensembles.Union _ _ _ _ |- _ ] =>
              inversion H; subst; simpl in *
            end.
            --- unfold Ensembles.In in *.
                destructAll.
                match goal with
                | [ H : map_util.M.find _ (LinTyp ?SH) = Some _,
                    H' : SplitStoreTypings [_; _] ?SH |- _ ] =>
                  specialize (SplitStoreTypings_inv H H')
                end.
                intros; destructAll.
                match goal with
                | [ H : In _ [_; _] |- _ ] =>
                  inversion H; subst; simpl in *
                end.
                all:
                  match goal with
                  | [ H : (fun l => exists v, get _ Linear ?MEM = Some _) <--> _ |- _ ] =>
                    inversion H
                  end.
                all: unfold Ensembles.Included in *.
                all: unfold Ensembles.In in *.
                all:
                  match goal with
                  | [ H : forall _, _ -> exists v, get _ Linear ?MEM = Some _
                      |- context[get ?L _ _] ] =>
                    generalize (H L)
                  end.
                all:
                  match goal with
                  | [ |- (?A -> _) -> _ ] =>
                    let H := fresh "H" in
                    let H' := fresh "H" in
                    assert (H : A);
                    [ | intro H'; specialize (H' H) ]
                  end.

                1:{
                  right.
                  unfold Ensembles.In.
                  eexists.
                  eapply SplitStoreTypings_get_heaptype_LinTyp; [ | | eauto ]; [ | constructor; auto ].
                  eauto.
                }
                2:{
                  match goal with
                  | [ H : _ \/ False |- _ ] =>
                    case H; [ | intros; exfalso; auto ]
                  end.
                  intros; subst.
                  simpl in *.
                  left; eexists; eauto.
                }

                all: destructAll.
                all:
                  match goal with
                  | [ H : forall _ _ _, get _ _ ?MEM = Some _ -> _,
                      H' : get _ _ ?MEM = Some _ |- _ ] =>
                    specialize (H _ _ _ H')
                  end.
                all: eexists; eauto.
            --- unfold Ensembles.In in *.
                destructAll.
                match goal with
                | [ H : map_util.M.find _ (LinTyp ?S) = Some _,
                    H' : SplitStoreTypings (_ :: _ ++ _) ?S |- _ ] =>
                  specialize (SplitStoreTypings_inv H H')
                end.
                intros; destructAll.
                match goal with
                | [ H : In _ (_ :: _ ++ _) |- _ ] =>
                  inversion H; subst; simpl in *
                end.
                ---- match goal with
                     | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
                       destruct M; subst; simpl in *;
                       destructAll; subst; simpl in *
                     end.
                     ----- match goal with
                           | [ H : M.is_empty (LinTyp ?S) = true,
                               H' : get_heaptype ?L (LinTyp ?S) = Some _
                               |- _ ] =>
                             specialize (get_heaptype_empty L _ H);
                             let H'' := fresh "H" in
                             intro H''; rewrite H'' in H';
                             inversion H'
                           end.
                     ----- match goal with
                           | [ H : eq_map (LinTyp ?S) _,
                               H' : get_heaptype _ (LinTyp ?S) = Some _ |- _ ] =>
                             rewrite H in H';
                             unfold get_heaptype in H'
                           end.
                           match goal with
                           | [ H : map_util.M.find
                                     (N.succ_pos ?L)
                                     (M.add
                                        (N.succ_pos ?L2)
                                        _ (M.empty HeapType))
                                   =
                                   Some _
                               |- _ ] =>
                             let H' := fresh "H" in
                             assert (H' : L = L2 \/ L <> L2) by apply eq_dec_N;
                             case H'; intros; subst
                           end.
                           ------ match goal with
                                  | [ H : Some _ = alloc _ _ _ _ |- _ ] =>
                                    specialize (get_alloc_same _ _ _ _ _ _ (eq_sym H))
                                  end.
                                  intros; eexists; eauto.
                           ------ rewrite M.gso in *.
                                  2:{
                                    intro.
                                    match goal with
                                    | [ H : N.succ_pos ?L = N.succ_pos ?L2 |- _ ] =>
                                      let H' := fresh "H" in
                                      assert (H' : Pos.pred_N (N.succ_pos L) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                                    end.
                                    repeat rewrite N.pos_pred_succ in *.
                                    eauto.
                                  }
                                  rewrite M.gempty in *.
                                  match goal with
                                  | [ H : None = Some _ |- _ ] =>
                                    inversion H
                                  end.
                ---- match goal with
                     | [ H : (fun l => exists v, get _ Linear ?MEM = Some _) <--> _ |- _ ] =>
                       inversion H
                     end.
                     unfold Ensembles.Included in *.
                     unfold Ensembles.In in *.
                     match goal with
                     | [ H : forall _, _ -> exists v, get _ Linear ?MEM = Some _
                         |- context[get ?L _ _] ] =>
                       generalize (H L)
                     end.
                     match goal with
                     | [ |- (?A -> _) -> _ ] =>
                       let H := fresh "H" in
                       let H' := fresh "H" in
                       assert (H : A);
                       [ | intro H'; specialize (H' H) ]
                     end.
                     { right.
                       unfold Ensembles.In.
                       eexists.
                       eapply SplitStoreTypings_get_heaptype_LinTyp_gen; [ | | eauto ]; [ eauto | ].
                       constructor 2.
                       rewrite map_app.
                       apply in_or_app.
                       match goal with
                       | [ H : In _ (_ ++ _) |- _ ] =>
                         apply in_app_or in H; case H; intros
                       end.
                       - left. 
                         match goal with
                         | [ H : In _ (map _ _) |- _ ] =>
                           specialize (in_map LinTyp _ _ H)
                         end.
                         rewrite map_map_compose; simpl.
                         auto.
                       - right.
                         match goal with
                         | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
                           destruct M; subst; simpl in *;
                           destructAll; subst; simpl in *
                         end.
                         -- match goal with
                            | [ H : In _ (map _ _) |- _ ] =>
                              specialize (in_map LinTyp _ _ H)
                            end.
                            rewrite map_map_compose; simpl.
                            auto.
                         -- apply in_map; auto. }
                     destructAll.
                     match goal with
                     | [ H : forall _ _ _, get _ _ ?MEM = Some _ -> _,
                         H' : get _ _ ?MEM = Some _ |- _ ] =>
                       specialize (H _ _ _ H')
                     end.
                     eexists; eauto.
         -- right.
            unfold Ensembles.In.
            match goal with
            | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
              destruct M; subst; simpl in *;
              destructAll; subst; simpl in *
            end.
            --- match goal with
                | [ H : UnrTyp ?S = _ |- context[UnrTyp ?S] ] =>
                  rewrite H
                end.
                match goal with
                | [ H : Some (_, ?L, _) = alloc _ _ _ _
                    |- context[N.succ_pos ?L2] ] =>
                  let H' := fresh "H" in
                  assert (H' : L2 = L \/ L2 <> L) by apply eq_dec_N;
                  case H'; intros; subst
                end.
                ---- rewrite M.gss; eexists; eauto.
                ---- rewrite M.gso.
                     2:{
                       intro.
                       match goal with
                       | [ H : N.succ_pos ?L = N.succ_pos ?L2 |- _ ] =>
                         let H' := fresh "H" in
                         assert (H' : Pos.pred_N (N.succ_pos L) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                       end.
                       repeat rewrite N.pos_pred_succ in *.
                       eauto.
                     }
                     match goal with
                     | [ H : Some (_, ?L, _) = alloc _ _ _ _,
                         H' : ?L2 <> ?L |- _ ] =>
                       specialize (get_alloc_other_loc _ _ _ _ _ _ _ (eq_sym H) H')
                     end.
                     intros.
                     match goal with
                     | [ H : get ?A ?B ?C = Some _,
                         H' : get ?A ?B ?C = get _ _ _ |- _ ] =>
                       rewrite H' in H
                     end.
                     match goal with
                     | [ H : forall _ _, _ -> exists ht, get_heaptype _ (UnrTyp ?S) = Some _
                         |- context[UnrTyp ?S] ] =>
                       eapply H
                     end.
                     eauto.
            --- match goal with
                | [ H : UnrTyp ?S1 = UnrTyp ?S2
                    |- context[UnrTyp ?S2] ] =>
                  rewrite (eq_sym H)
                end.
                match goal with
                | [ H : Some _ = alloc _ ?M _ _,
                    H' : ?M2 <> ?M,
                    H'' : get ?L2 ?M2 _ = Some _ |- _ ] =>
                  specialize (get_alloc_other_mem _ _ _ L2 _ _ _ _ (eq_sym H) H')
                end.
                match goal with
                | [ H : ?A = Some _ |- (?A = _) -> _ ] =>
                  let H' := fresh "H" in
                  intro H'; rewrite H' in H
                end.
                match goal with
                | [ H : forall _ _, _ -> exists ht, get_heaptype _ (UnrTyp ?S) = Some _
                    |- context[UnrTyp ?S] ] =>
                  eapply H
                end.
                eauto.
         -- match goal with
            | [ H : (_ :|: (fun l => exists y, map_util.M.find (N.succ_pos _) (UnrTyp ?S) = Some _)) ?L,
                H' : context[UnrTyp ?S = M.add _ _ (UnrTyp ?S2)]
                |- ?G ] =>
              let H' := fresh "H" in
              assert (H' : exists y, map_util.M.find (N.succ_pos L) (UnrTyp S) = Some y);
              [ inversion H; eauto |
              assert (H'' : (exists y, map_util.M.find (N.succ_pos L) (UnrTyp S2) = Some y) -> G) ]
            end.
            { unfold Ensembles.In in *; destructAll.
              match goal with
              | [ H : map_util.M.find _ (UnrTyp ?S1) = Some _,
                  H' : SplitStoreTypings [?S2; ?S1] _
                  |- context[UnrTyp ?S2] ] =>
                let H'' := fresh "H" in
                assert (H'' : UnrTyp S2 = UnrTyp S1) by solve_inst_or_unr_typ_eq;
                rewrite H''
              end.
              eexists; eauto. }
            { intros; destructAll.
              match goal with
              | [ H : (fun l => exists v, get _ Unrestricted _ = Some _) <--> _ :|: _ |- _ ] =>
                destruct H
              end.
              unfold Ensembles.Included in *.
              unfold Ensembles.In in *.
              match goal with
              | [ H : forall _, _ -> exists v, get _ Unrestricted _ = Some _
                  |- context[get ?L _ _] ] =>
                generalize (H L)
              end.
              match goal with
              | [ |- (?A -> _) -> _ ] =>
                let H := fresh "H" in
                let H' := fresh "H" in
                assert (H : A);
                [ | intro H'; specialize (H' H) ]
              end.
              { right; eexists; eauto. }
              destructAll.
              eexists.
              match goal with
              | [ H : forall _ _ _, _ -> get _ _ ?MEM = Some _
                  |- get _ _ ?MEM = Some _ ] =>
                eapply H
              end.
              eauto. }
            match goal with
            | [ H : context[qualconstr_eq_dec ?M Linear] |- _ ] =>
              destruct M; subst; simpl in *;
              destructAll; subst; simpl in *
            end.
            --- match goal with
                | [ H : UnrTyp ?S2 = M.add _ _ _,
                    H' : map_util.M.find _ (UnrTyp ?S2) = Some _
                    |- _ ] =>
                  rewrite H in H'
                end.
                match goal with
                | [ H : map_util.M.find (N.succ_pos ?L) (M.add (N.succ_pos ?L2) _ _) = Some _ |- _ ] =>
                  let H' := fresh "H" in
                  assert (H' : L = L2 \/ L <> L2) by apply eq_dec_N;
                  case H'; intros; subst
                end.
                ---- eexists.
                     eapply get_alloc_same.
                     eapply eq_sym; eauto.
                ---- rewrite M.gso in *.
                     2:{
                       intro.
                       match goal with
                       | [ H : N.succ_pos ?L = N.succ_pos ?L2 |- _ ] =>
                         let H' := fresh "H" in
                         assert (H' : Pos.pred_N (N.succ_pos L) = Pos.pred_N (N.succ_pos L2)) by ltac:(rewrite H; auto)
                       end.
                       repeat rewrite N.pos_pred_succ in *.
                       eauto.
                     }
                     eauto.
            --- match goal with
                | [ H : UnrTyp ?S1 = UnrTyp ?S2,
                    H' : map_util.M.find _ (UnrTyp ?S2) = Some _
                    |- _ ] =>
                  rewrite (eq_sym H) in H'
                end.
                eauto.
         -- destructAll; subst.
            rewrite (eq_sym (map_app _ _ _)).

            match goal with
            | [ H : SplitStoreTypings [update_unr _ ?S1; update_unr _ ?S2] ?SH |- _ ] =>
              let H' := fresh "H" in
              assert (H' : exists Sh'', SplitStoreTypings [S1; S2] Sh'')
            end.
            { eapply SplitStoreTypings_undo_update_unr.
              - simpl; eauto.
              - constructor; [ eauto | ].
                constructor; [ | eauto ].
                solve_inst_or_unr_typ_eq. }
            destructAll.
            eapply SplitStoreTypings_update_unr_two_lists; [ eauto | | | ]; [ | simpl; auto | simpl; auto ].
            match goal with
            | [ H : SplitStoreTypings (map ?F1 ?L1 ++ map ?F2 ?L2) ?SH,
                H' : SplitStoreTypings [?S1; ?SH] ?SHP
                |- SplitStoreTypings ?LST ?SHP ] =>
              let H'' := fresh "H" in
              assert (H'' : Permutation.Permutation (S1 :: (map F1 L1 ++ map F2 L2)) LST)
            end.
            { match goal with
              | [ |- context[is_linear ?M] ] =>
                destruct M; subst; simpl in *;
                destructAll; subst; simpl in *
              end.
              - eapply Permutation.Permutation_trans;
                [ eapply Permutation.Permutation_middle | ].
                apply Permutation.Permutation_app.
                -- apply Permutation_map_gen.
                   --- eapply alloc_to_list_Permutation_diff_qual; [ | eauto ].
                       apply eq_sym; eauto.
                   --- left.
                       let x := fresh "x" in
                       intro x; destruct x as [[curL curHV] curSz].
                       auto.
                -- eapply Permutation.Permutation_trans.
                   2:{
                     eapply Permutation.Permutation_map.
                     eapply alloc_to_list_Permutation.
                     apply eq_sym; eauto.
                   }
                   simpl.
                   rewrite N.eqb_refl.
                   apply Permutation.perm_skip.
                   apply Permutation_map_gen; [ eauto | ].
                   left.
                   let x := fresh "x" in
                   intro x; destruct x as [[curL curHV] curSz].
                   intros.
                   match goal with
                   | [ |- context[(?L1 =? ?L2)%N] ] =>
                     let H := fresh "H" in
                     assert (H : (L1 =? L2)%N = false);
                     [ | rewrite H; auto ]
                   end.
                   rewrite OrdersEx.N_as_OT.eqb_neq.
                   intro; subst.
                   match goal with
                   | [ H : In _ (M.to_list Unrestricted _) |- _ ] =>
                     apply In_nth_error in H
                   end.
                   destructAll.
                   match goal with
                   | [ H : nth_error (M.to_list Unrestricted _) _ = Some _ |- _ ] =>
                     apply in_to_list_implies_get in H
                   end.
                   match goal with
                   | [ H : ?A = ?A -> _ |- _ ] =>
                     specialize (H eq_refl)
                   end.
                   match goal with
                   | [ H : MemUtils.dom_unr _ <--> _ |- _ ] =>
                     destruct H
                   end.
                   unfold MemUtils.dom_unr in *.
                   unfold MemUtils.dom in *.
                   unfold Dom_ht in *.
                   unfold Dom_map in *.
                   unfold Ensembles.Included in *.
                   unfold Ensembles.In.
                   match goal with
                   | [ H : forall _ _, get _ ?M ?MEM = Some _ -> _,
                       H' : get _ ?M ?MEM = Some _ |- _ ] =>
                     specialize (H _ _ H')
                   end.
                   destructAll.
                   match goal with
                   | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                     rewrite H in H'; inversion H'
                   end.
              - rewrite app_comm_cons.
                apply Permutation.Permutation_app.
                -- eapply Permutation.Permutation_trans.
                   2:{
                     eapply Permutation.Permutation_map.
                     eapply alloc_to_list_Permutation.
                     apply eq_sym; eauto.
                   }
                   simpl.
                   rewrite N.eqb_refl.
                   apply Permutation.perm_skip.
                   apply Permutation_map_gen; [ eauto | ].
                   left.
                   let x := fresh "x" in
                   intro x; destruct x as [[curL curHV] curSz].
                   intros.
                   match goal with
                   | [ |- context[(?L1 =? ?L2)%N] ] =>
                     let H := fresh "H" in
                     assert (H : (L1 =? L2)%N = false);
                     [ | rewrite H; auto ]
                   end.
                   rewrite OrdersEx.N_as_OT.eqb_neq.
                   match goal with
                   | [ |- ?L1 <> ?L2 ] =>
                     let H := fresh "H" in
                     assert (H : L1 = L2 \/ L1 <> L2) by apply eq_dec_N;
                     case H; [ | auto ]
                   end.
                   intros; subst.
                   match goal with
                   | [ H : In _ (M.to_list Linear _) |- _ ] =>
                     apply In_nth_error in H
                   end.
                   destructAll.
                   match goal with
                   | [ H : nth_error (M.to_list Linear _) _ = Some _ |- _ ] =>
                     apply in_to_list_implies_get in H
                   end.
                   match goal with
                   | [ H : Some (_, ?L, _) = alloc _ _ _ _ |- _ ] =>
                     specialize (alloc_fresh _ _ _ _ _ _ (eq_sym H) L)
                   end.
                   match goal with
                   | [ |- (?A -> _) -> _ ] =>
                     let H := fresh "H" in
                     let H' := fresh "H" in
                     assert (H : A);
                     [ | intro H'; specialize (H' H) ]
                   end.
                   { split; [ apply N.le_refl | ].
                     apply N.lt_add_pos_r.
                     eapply N.lt_lt_0.
                     eapply alloc_size.
                     apply eq_sym; eauto. }
                   match goal with
                   | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                     rewrite H in H'; inversion H'
                   end.
                -- apply Permutation_map_gen.
                   --- eapply alloc_to_list_Permutation_diff_qual; [ | eauto ].
                       apply eq_sym; eauto.
                   --- left.
                       let x := fresh "x" in
                       intro x; destruct x as [[curL curHV] curSz].
                       auto. }
                     
            eapply SplitStoreTypings_permut; [ eauto | ].
            eapply SplitStoreTypings_add_one; eauto.
         -- match goal with
            | [ H : forall _ _, _ -> get_heaptype _ ?UT = Some _
                |- get_heaptype _ ?UT = Some _ ] =>
              apply H
            end.
            match goal with
            | [ H : get_heaptype _ ?UT1 = Some _
                |- get_heaptype _ ?UT2 = Some _ ] =>
              let H' := fresh "H" in
              assert (H' : UT2 = UT1); [ | rewrite H'; auto ]
            end.
            match goal with
            | [ H : SplitStoreTypings (map _ _ ++ map _ _) ?SH
                |- UnrTyp ?SP = _ ] =>
              let H' := fresh "H" in
              assert (H' : UnrTyp SP = UnrTyp SH) by solve_inst_or_unr_typ_eq;
              rewrite H'
            end.
            apply eq_sym; eapply proj1.
            eapply SplitStoreTypings_eq_typs2; [ eauto | ].
            apply in_or_app; right.
            apply in_map.
            auto. }

      split; [ | split; [ | split; [ | split; [ | split ] ] ] ]; auto.
      -- match goal with
         | [ |- context[Arrow ?L _] ] =>
           replace L with (L ++ []) at 1 by apply app_nil_r
         end.
         eapply (FrameTyp _ _ _ _ _ (QualConst Linear)).
         --- reflexivity.
         --- apply Forall_trivial.
             intro t.
             destruct t.
             apply QualLeq_Top.
         --- apply QualLeq_Top.
         --- eapply ValTyp.
             apply HasTypeValue_update_linear_ctx.
             econstructor.
             ---- econstructor; eauto.
             ---- simpl in *.
                  destructAll.
                  match goal with
                  | [ H : HasHeapType _ _ _ _ |- _ ] =>
                    eapply HasHeapType_HeapTypeValid in H
                  end.
                  econstructor;
                  [ econstructor; eauto | apply QualLeq_Refl | ].
                  econstructor;
                  [ econstructor; eauto | | ].
                  ----- simpl.
                        destruct F; subst; simpl in *.
                        econstructor 2; [ eauto | ].
                        apply OrdersEx.Nat_as_OT.add_pos_r.
                        exact Nat.lt_0_1.
                  ----- apply HeapTypeValid_debruijn_subst_SLoc.
                        eapply HeapTypeValid_update_linear_ctx_rev; eauto.
             ---- simpl.
                  unfold debruijn.get_var'.
                  simpl.
                  unfold debruijn.ext at 1.
                  simpl.
                  match goal with
                  | [ |- context[RefT _ _
                                      (subst.subst'_heaptype
                                         ?S
                                         (subst.subst'_heaptype
                                            ?S2 ?T))] ] =>
                    assert (Hdb :
                              subst.subst'_heaptype
                                S
                                (subst.subst'_heaptype
                                   S2 T)
                              =
                              T)
                  end.
                  { eapply HeapTypeValid_debruijn_subst_SLoc_weak. }
                  rewrite Hdb.
                  match goal with
                  | [ H : context[qualconstr_eq_dec ?Q _] |- _ ] =>
                    destruct Q
                  end.
                  ----- econstructor; simpl in *; destructAll.
                        ------ assumption.
                        ------ match goal with
                               | [ H : SplitStoreTypings
                                         (_ :: map _ _ ++ map _ _)
                                         _ |- _ ] =>
                                 inversion H; subst
                               end.
                               match goal with
                               | [ H :
                                     Forall
                                       _ (_ :: map _ _ ++ map _ _)
                                   |- _ ] =>
                                 inversion H; subst
                               end.
                               destructAll.
                               match goal with
                               | [ H : _ = ?A |- context[?A] ] =>
                                 rewrite <-H
                               end.
                               match goal with
                               | [ H : ?A = M.add _ _ _ |- context[?A] ] =>
                                 rewrite H
                               end.
                               unfold get_heaptype.
                               rewrite typing.M.gss.
                               auto.
                        ------ apply QualLeq_Refl.
                        ------ econstructor.
                               eapply QualConstValid; eauto.
                               eapply LocPValid; eauto.
                               destruct F; simpl in *; subst.
                               match goal with
                               | [ H : HasHeapType _ ?F _ _ |- _ ] =>
                                 replace label with (typing.label F) by ltac:(simpl; eauto); replace ret with (typing.ret F) by ltac:(simpl; eauto); replace size with (typing.size F) by ltac:(simpl; eauto); replace type with (typing.type F) by ltac:(simpl; eauto); replace location with (typing.location F) by ltac:(simpl; eauto)
                               end.
                               eapply HeapTypeValid_linear.
                               eapply HasHeapType_HeapTypeValid; eauto.
                  ----- econstructor; simpl in *; destructAll.
                        ------ assumption.
                        ------ apply QualLeq_Refl.
                        ------ econstructor.
                               eapply QualConstValid; eauto.
                               eapply LocPValid; eauto.
                               destruct F; simpl in *; subst.
                               match goal with
                               | [ H : HasHeapType _ ?F _ _ |- _ ] =>
                                 replace label with (typing.label F) by ltac:(simpl; eauto); replace ret with (typing.ret F) by ltac:(simpl; eauto); replace size with (typing.size F) by ltac:(simpl; eauto); replace type with (typing.type F) by ltac:(simpl; eauto); replace location with (typing.location F) by ltac:(simpl; eauto)
                               end.
                               eapply HeapTypeValid_linear.
                               eapply HasHeapType_HeapTypeValid; eauto.
             ---- destruct F; subst; simpl in *; solve_lcvs.
         --- auto.
      -- match goal with
         | [ H : context[qualconstr_eq_dec ?Q _] |- _ ] =>
           destruct Q; simpl in *; destructAll; try assumption
         end.
         match goal with
         | [ H : HasTypeLocals _ _ _ _ |- _ ] =>
           inversion H; subst; simpl in *
         end.
         constructor.

         rewrite Forall3_forall.
         split.
         2:{
           rewrite map_length.
           match goal with
           | [ H : Forall3 _ _ _ ?L |- _ /\ _ = length ?L2 ] =>
             replace (length L2) with (length L)
           end.
           2:{
             eapply LCEffEqual_length; eauto.
           }
           eapply Forall3_length; eauto.
         }
         match goal with
         | [ H : Forall3 _ _ _ _ |- _ ] =>
           rewrite Forall3_forall in H
         end.
         intros; destructAll.
         match goal with
         | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
           apply nth_error_map_inv in H; destructAll
         end.
         match goal with
         | [ X : _ * _ |- _ ] => destruct X
         end.
         use_LCEffEqual_nth_error_right.
         match goal with
         | [ H : forall _ _ _ _,
               nth_error ?L1 _ = _ ->
               nth_error ?L2 _ = _ ->
               nth_error ?L3 _ = _ -> _,
             H' : nth_error ?L1 _ = _,
             H'' : nth_error ?L2 _ = _,
             H''' : nth_error ?L3 _ = _ |- _ ] =>
           specialize (H _ _ _ _ H' H'' H''')
         end.
         simpl in *.
         apply HasTypeValue_update_unr.
         --- match goal with
             | [ H : HasTypeValue ?S _ _ _ |- context[?S] ] =>
               revert H; destruct S; subst; simpl in *
             end.
             eauto.
         --- match goal with
             | [ H : false = true \/ _ |- _ ] =>
               let H' := fresh "H" in
               case H; [ intro H'; inversion H' | ]
             end.
             match goal with
             | [ |- get_heaptype _ ?UT1 = _ ->
                    get_heaptype _ ?UT2 = _ ] =>
               let H := fresh "H" in
               assert (H : UT1 = UT2); [ | rewrite H; eauto ]
             end.
             apply eq_sym.
             eapply proj1.
             eapply SplitStoreTypings_eq_typs2; [ eauto | ].
             constructor 2.
             apply in_or_app.
             right.
             eapply nth_error_In; eauto.
         --- eapply LCEffEqual_HasTypeLocals; eauto.
      -- match goal with
         | [ H : ?A = ?B |- nth_error ?B _ = Some _ ] =>
           rewrite <-H; auto
         end.
      -- split; eauto.
         match goal with
         | [ H : context[qualconstr_eq_dec ?Q1 ?Q2] |- _ ] =>
           destruct (qualconstr_eq_dec Q1 Q2); destructAll;
           simpl in *;
           match goal with
           | [ H : UnrTyp ?S = _ |- context[UnrTyp ?S] ] =>
             rewrite H; try eapply sub_map_refl
           end
         end.
         unfold alloc_mem_range in *.
         match goal with
         | [ H : context[alloc ?A ?B ?C ?D] |- _ ] =>
           assert (exists x, alloc A B C D = Some x);
           [ destruct (alloc A B C D); try discriminate | ]
         end.
         { eexists; eauto. }
         destructAll.
         destruct_prs.
         unfold sub_map; intros.
         match goal with
         | [ |- get_heaptype ?L (M.add (N.succ_pos ?L2) _ _) = Some _ ] =>
           assert (Heq_or_uneq : (L = L2) \/ (L <> L2))
         end.
         { apply eq_dec_N. }
         inversion Heq_or_uneq.
         --- subst.
             match goal with
             | [ H : alloc _ ?Q _ _ = Some _ |- _ ] =>
               destruct Q; subst; simpl in *; [ | exfalso; eauto ]
             end.
             match goal with
             | [ H : false = true \/ _ |- _ ] =>
               case H;
               [ let H' := fresh "H" in
                 intro H'; inversion H' | ]
             end.
             intros.
             match goal with
             | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
               rewrite H in H'; inversion H'
             end.
         --- unfold get_heaptype in *.
             rewrite M.gso; auto.
             intro.
             match goal with
             | [ H' : ?A = ?B |- _ ] =>
               let H := fresh "H" in
               assert (H : Pos.pred_N A = Pos.pred_N B); [ rewrite H'; auto | repeat rewrite N.pos_pred_succ in H ]
             end.
             subst.
             auto.
      -- simpl in *; destructAll.
         destruct F; subst; simpl in *.
         unfold Function_Ctx_empty in *.
         simpl in *; destructAll.
         apply LCEffEqual_LCSizeEqual; auto.
      
    - (* Malloc - Trap *)
      exists Sp, Sh, Sstack, Ss, L.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ]; auto.
      -- specialize (SplitStoreTypings_unr_same Hsplit).
         intro Heq.
         rewrite Heq.
         eauto.
      -- specialize (HasTypeInstruction_local_is_tl _ _ _ _ _ _ _ Hi).
         intro Htl.
         destructAll.
         show_tlvs Hi.
         eapply ChangeEndLocalTyp; eauto.
         eapply TrapTyp; auto.
         solve_lcvs.
      -- split; eauto.
         eapply sub_map_refl.
      -- apply LCSizeEqual_refl.
  Qed.
End PreservationFull.
