From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Classes.Morphisms.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.map_util
        RWasm.typing_util RWasm.tactics RWasm.list_util RWasm.EnsembleUtil RWasm.debruijn
        RWasm.splitting RWasm.surface RWasm.misc_util RWasm.hti_subst_indices RWasm.progress.

Lemma eq_dec_size : forall r1 r2 : Size,
    {r1 = r2} + {r1 <> r2}.
Proof.
  apply (Size_rect (fun r1 => forall r2, {r1 = r2} + {r1 <> r2}));
  intros; case r2; intros.
  2-4,6-8: right; intro H'; inversion H'; subst; eauto.
  - specialize (OrderedTypeEx.Nat_as_OT.eq_dec v v0).
    intro H; case H; intros; subst;
      [ | right; intro H'; inversion H'; subst; eauto ].
    left; eauto.
  - specialize (H s1).
    specialize (H0 s2).
    case H; intros; subst;
      [ | right; intro H'; inversion H'; subst; eauto ].
    case H0; intros; subst;
      [ | right; intro H'; inversion H'; subst; eauto ].
    left; eauto.
  - specialize (OrderedTypeEx.Nat_as_OT.eq_dec n n0).
    intro H; case H; intros; subst;
      [ | right; intro H'; inversion H'; subst; eauto ].
    left; eauto.
Defined.

Lemma nth_error_combine : forall {idx} {A B} {l1 : list A} {l2 : list B} {el1 el2},
    nth_error (combine l1 l2) idx = Some (el1, el2) ->
    nth_error l1 idx = Some el1 /\
    nth_error l2 idx = Some el2.
Proof.
  induction idx.
  - intros.
    destruct l1; simpl in *; destruct l2; simpl in *.
    all:
      try match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          end.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst
    end.
    auto.
  - intros.
    destruct l1; simpl in *; destruct l2; simpl in *.
    all:
      try match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          end.
    eauto.
Qed.

Lemma nth_error_combine_fst : forall {A B C} {idx} {l1 : list (A * C)} {l2} {obj1 : A} {obj2 : B},
    nth_error (combine (map fst l1) l2) idx =
    Some (obj1, obj2) ->
    length l1 = length l2 ->
    exists obj2',
      nth_error l1 idx = Some (obj1, obj2').
Proof.
  intros.
  match goal with
  | [ H : nth_error (combine _ _) _ = Some _ |- _ ] =>
    apply nth_error_combine in H
  end.
  destructAll.
  match goal with
  | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
    apply nth_error_map_inv in H
  end.
  destructAll.
  match goal with
  | [ X : _ * _ |- _ ] => destruct X
  end.
  simpl.
  eauto.
Qed.

Lemma In_combine_fst : forall {A B C} {l1 : list (A * C)} {l2} {obj1 : A} {obj2 : B},
    In (obj1, obj2)
       (combine (map fst l1) l2) ->
    length l1 = length l2 ->
    exists obj2',
      In (obj1, obj2') l1.
Proof.
  intros.
  apply In_nth_error in H.
  destructAll.
  specialize (nth_error_combine_fst H H0).
  intros; destructAll.
  eexists; eapply nth_error_In; eauto.
Qed.

Lemma split_app : forall {A B l l'} {l1 : list A} {l2 : list B} {l1' l2'},
    split l = (l1, l2) ->
    split l' = (l1', l2') ->
    split (l ++ l') = (l1 ++ l1', l2 ++ l2').
Proof.
  induction l; intros; simpl in *.
  - match goal with
    | [ H : (_, _) = _ |- _ ] =>
      inversion H; subst; simpl in *; auto
    end.
  - match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    match goal with
    | [ H : context[split ?L], H' : split _ = (_, _) |- _ ] =>
      revert H; remember (split L) as obj;
      generalize (eq_sym Heqobj); case obj; intros
    end.
    match goal with
    | [ H : (_, _) = _ |- _ ] =>
      inversion H; subst; simpl in *; auto
    end.
    match goal with
    | [ H : forall _ _ _ _ _,
          split ?L1 = _ -> _,
        H' : split ?L1 = _,
        H'' : split ?L2 = _ |- _ ] =>
      specialize (H _ _ _ _ _ H' H''); rewrite H
    end.
    auto.
Qed.

Lemma split_map_const_arg1_gen : forall {A B C} {f} {f' : B -> C} {obj : A} {l},
    (forall x, In x l -> f x = (obj, f' x)) ->
    split (map f l) = (repeat obj (length l), map f' l).
Proof.
  induction l; intros; simpl in *; auto.
  match goal with
  | [ H : forall _, ?A = _ \/ _ -> _ |- _ ] =>
    generalize (H _(or_introl eq_refl));
    let H' := fresh "H" in intro H'; rewrite H'
  end.
  match goal with
  | [ H : ?A -> split _ = _ |- _ ] =>
    let H' := fresh "H" in
    assert (H' : A); [ | specialize (H H'); rewrite H ]
  end.
  { intros; eauto. }
  auto.
Qed.

Lemma split_map_const_arg1 : forall {A B} {f} {obj : A} {l : list B},
    (forall x, In x l -> f x = (obj, x)) ->
    split (map f l) = (repeat obj (length l), l).
Proof.
  intros.
  replace (repeat obj (length l), l) with (repeat obj (length l), map Datatypes.id l); [ | rewrite map_id; auto ].
  eapply split_map_const_arg1_gen.
  unfold id; auto.
Qed.

Lemma nth_error_repeat : forall {idx} {A} {l} {el : A} {el' n},
    l = repeat el' n ->
    nth_error l idx = Some el ->
    el = el'.
Proof.
  induction idx; intros; simpl in *.
  - destruct l.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    destruct n; simpl in *.
    1:{
      match goal with
      | [ H : _ :: _ = [] |- _ ] => inversion H
      end.
    }
    match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst
    end.
    auto.
  - destruct l.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    destruct n; simpl in *.
    1:{
      match goal with
      | [ H : _ :: _ = [] |- _ ] => inversion H
      end.
    }
    match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst
    end.
    eauto.
Qed.    

Lemma in_repeat : forall {A} {el : A} {el' n},
    In el (repeat el' n) -> el = el'.
Proof.
  intros.
  apply In_nth_error in H; destructAll.
  eapply nth_error_repeat; eauto.
Qed.

Lemma Forall2_split : forall {A B C D} {l : list (A * B)} {l' : list (C * D)} {l1 l1' l2 l2'} {P : A * B -> C * D -> Prop} {P1 P2},
    (forall '(a, b) '(c, d),
        P1 a c /\ P2 b d -> P (a, b) (c, d)) ->
    split l = (l1, l2) ->
    split l' = (l1', l2') ->
    Forall2 P1 l1 l1' ->
    Forall2 P2 l2 l2' ->
    Forall2 P l l'.
Proof.
  induction l; intros; simpl in *.
  2:
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
  2:
    match goal with
    | [ H : context[split ?L], H' : context[split ?L] |- _ ] =>
      revert H; revert H';
      remember (split L) as obj; generalize (eq_sym Heqobj);
      case obj; intros
    end.
  all:
    match goal with
    | [ H : (_, _) = _ |- _ ] => inversion H; subst
    end.
  all:
    match goal with
    | [ H : Forall2 _ _ _, H' : Forall2 _ _ _ |- _ ] =>
      inversion H; subst; simpl in *;
      inversion H'; subst; simpl in *
    end.
  all: destruct l'; subst; simpl in *.
  all:
    try match goal with
        | [ X : _ * _ |- _ ] => destruct X
        end.
  all:
    try match goal with
        | [ H : split _ = _ |- _ ] =>
          match goal with
          | [ H : context[split ?L], H' : split ?LP = _ |- _ ] =>
            revert H;
            remember (split L) as obj2;
            generalize (eq_sym Heqobj2); case obj2; intros
          end
        | [ |- _ ] =>
          try match goal with
              | [ H : context[split ?L] |- _ ] =>
                revert H;
                remember (split L) as obj2;
                generalize (eq_sym Heqobj2); case obj2; intros
              end
        end.
  all:
    repeat match goal with
           | [ H : (_, _) = (_, _) |- _ ] =>
             inversion H; subst; simpl in *; clear H
           end.
  all: constructor; eauto.
  match goal with
  | [ H : context[_ -> ?P _ _] |- ?P ?A ?B ] => apply (H A B)
  end.
  auto.
Qed.

(* TODO (noble): Find the lemma that is more general *)
Lemma HasTypeValue_update_linear_ctx : forall S F L v t,
    HasTypeValue S F v t ->
    HasTypeValue S
                 (update_linear_ctx L F)
                 v
                 t.
Proof.
  intros.
  destruct F; eapply HasTypeValue_Function_Ctx; try eassumption; reflexivity.
Qed.

Lemma HasTypeValue_update_linear_ctx_rev : forall S F L v t,
    HasTypeValue S
                 (update_linear_ctx L F)
                 v
                 t ->
    HasTypeValue S F v t.
Proof.
  intros.
  destruct F; eapply HasTypeValue_Function_Ctx; try eassumption; reflexivity.
Qed.

Lemma HasTypeValue_empty_function_ctx : forall S1 F v t,
    HasTypeValue S1 empty_Function_Ctx v t ->
    Function_Ctx_empty F ->
    HasTypeValue S1 F v t.
Proof.
  intros.
  unfold Function_Ctx_empty in *. destructAll.
  eapply HasTypeValue_Function_Ctx; try eassumption;
    unfold empty_Function_Ctx; simpl; congruence.
Qed.

Lemma HasTypeValue_empty_function_ctx_rev : forall S1 F v t,
    HasTypeValue S1 F v t ->
    Function_Ctx_empty F ->
    HasTypeValue S1 empty_Function_Ctx v t.
Proof.
  intros.
  unfold Function_Ctx_empty in *. destructAll.
  eapply HasTypeValue_Function_Ctx; try eassumption;
    unfold empty_Function_Ctx; simpl; congruence.
Qed.

Lemma LCEffEqual_subst_loc : forall {C L1 L2 loc},
  LCEffEqual C L1 L2 ->
  subst'_local_ctx (debruijn.subst'_of (debruijn.ext subst.SLoc loc debruijn.id)) L1 = L1 ->
  subst'_local_ctx (debruijn.subst'_of (debruijn.ext subst.SLoc loc debruijn.id)) L2 = L2.
Proof.
  intros.
  apply Forall_eq.
  rewrite Forall_forall.
  intros.
  destruct_prs.
  erewrite size_debruijn_subst_ext;
    [ | | apply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  match goal with
  | [ H : In _ _ |- _ ] => apply In_nth_error in H; destructAll
  end.
  use_LCEffEqual_nth_error_right.
  unfold subst'_local_ctx in *.
  match goal with
  | [ H : map ?F ?L = ?L,
      H' : nth_error ?L _ = Some _ |- _ ] =>
    specialize (@map_nth_error _ _ F _ _ _ H');
    let H'' := fresh "H" in
    intro H''; rewrite H in H''; rewrite H' in H'';
    inversion H''; subst
  end.
  match goal with
  | [ H : ?A = ?B |- context[?B] ] => repeat rewrite <-H
  end.
  auto.
Qed.

Ltac show_tlvs H :=
  specialize (HasTypeInstruction_TypeAndLocalValid H);
  intros; destructAll.

Ltac solve_forall_apps :=
  repeat match goal with
         | [ H : Forall _ (_ ++ _) |- _ ] =>
           apply Forall_app in H; destructAll
         end;
  repeat match goal with
         | [ H : Forall _ [_] |- _ ] =>
           inversion H; subst; simpl in *; clear H
         end;
  repeat match goal with
         | [ |- Forall _ (_ ++ _) ] => apply Forall_app; split
         end;
  auto.

Ltac solve_lcvs :=
  repeat match goal with
         | [ H : LocalCtxValid ?F ?L, H' : LCEffEqual _ ?L ?LP |- _ ] =>
           let H0 := fresh "H" in
           assert (H0 := LocalCtxValid_LCEffEqual H H');
           clear H'
         | [ H : LocalCtxValid ?F ?L, H' : LCEffEqual _ ?LP ?L |- _ ] =>
           let H0 := fresh "H" in
           assert (H0 := LocalCtxValid_LCEffEqual
                           H (LCEffEqual_sym H'));
           clear H'
         end;
  auto;
  eapply LocalCtxValid_Function_Ctx; eauto.
        
Ltac solve_tvs :=
  solve_forall_apps;
  match goal with
  | [ H : Forall (TypeValid _) _ |- _ ] =>
    eapply Forall_TypeValid_Function_Ctx; eauto
  | [ H : TypeValid _ _ |- _ ] =>
    eapply TypeValid_Function_Ctx; eauto
  end.

Module Preservation (M : Memory) (T : MemTyping M).

  Module Red := Reduction M T.

  Import M T Red Utils.

  (* TODO move StructFree and ArrayFree to reduce_simpl *)

  Set Nested Proofs Allowed.


  (* TODO move *)

  Lemma eq_map_is_empty A m :
    M.is_empty m = true ->
    eq_map m (M.empty A).
  Proof.
    intros H z. unfold get_heaptype.
    eapply typing.M.is_empty_2 in H.
    rewrite typing.M.gempty.
    destruct (M.find (N.succ_pos z) m) eqn:Heq; eauto.

    exfalso. eapply H.
    eapply PositiveMap.find_2; eauto.
  Qed.


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


  (* TODO move *)
  Lemma Forall_split A B P (l : list (A * B)) l1 l2 :
    Forall (fun '(x , _) => P x) l ->
    split l = (l1, l2) ->
    Forall P l1.
  Proof.
    intros Hall; revert l1 l2; induction Hall; intros l1 l2 Hs; inv Hs; eauto.

    destruct x. destruct (split l). inv H1.
    constructor; eauto.
  Qed.


  (* TODO move *)
  Lemma Forall3_HasTypeValue_Unrestricted_LinEmpty' F Ss vs (ts : list (Typ * Size)) :
        Forall3 (fun S v '(t, _) => HasTypeValue S F v t) Ss vs ts ->
        Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) ts ->
        qual F = [] ->
        Forall (fun S => M.is_empty (LinTyp S) = true) Ss.
  Proof.
    intros H3 Hall; induction H3; simpl in *; eauto.
    inv Hall.
    constructor; eauto.
    destruct z. destruct t0. eapply HasTypeValue_Unrestricted_LinEmpty; eauto.
  Qed.

  Hint Constructors HasTypeInstruction.
  Hint Constructors HasTypeValue.

  Lemma to_size_proof sz H1 H2 :
    to_size sz H1 = to_size sz H2.
  Proof.
    rewrite ProofIrrelevance.proof_irrelevance with (p1 := H1) (p2 := H2).
    reflexivity.
  Qed.

  Lemma size_to_nat_eq_to_size : forall {sz n},
      size_to_nat sz = Some n ->
      exists H, n = to_size sz H.
  Proof.
    intro sz; elim sz.
    - intros; simpl in *.
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    - intros; simpl in *.
      match goal with
      | [ H : context[size_to_nat ?S1],
          H' : context[size_to_nat ?S1]
          |- context[size_closed ?S1 /\ _] ] =>
        remember (size_to_nat S1) as opt1;
        revert H; revert H';
        generalize (eq_sym Heqopt1);
        case opt1; intros;
        try match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            end
      end.
      match goal with
      | [ H : context[size_to_nat ?S1],
          H' : context[size_to_nat ?S1]
          |- context[_ /\ size_closed ?S1] ] =>
        remember (size_to_nat S1) as opt2;
        revert H; revert H';
        generalize (eq_sym Heqopt2);
        case opt2; intros;
        try match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            end
      end.
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; simpl in *
      end.
      repeat match goal with
             | [ H : forall n, Some ?A = Some n -> _ |- _ ] =>
               specialize (H _ eq_refl)
             end.
      destructAll.
      match goal with
      | [ H : size_closed ?S1, H' : size_closed ?S2
          |- context[size_closed ?S1 /\ size_closed ?S2] ] =>
        exists (conj H H')
      end.
      auto.
    - intros; simpl in *.
      exists I.
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; simpl in *; auto
      end.
  Qed.

  Lemma fold_SizePlus_reducible_imp_base_reducible : forall {ss base},
      size_closed (fold_left SizePlus ss base) ->
      size_closed base.
  Proof.
    intro ss; elim ss.
    - intros; simpl in *; auto.
    - intros; simpl in *.
      match goal with
      | [ H : forall _, size_closed _ -> _,
          H' : size_closed _ |- _ ] =>
        specialize (H _ H')
      end.
      simpl in *.
      destructAll; auto.
  Qed.

  Lemma fold_size_to_nat_eq_to_size_fold_SizePlus : forall {ss base Hredss Hredbase},
      (fold_left
         (fun (acc : N) (sz : Size) =>
            match size_to_nat sz with
            | Some n => acc + N.of_nat n
            | None => acc
            end)
         ss
         (N.of_nat (to_size base Hredbase))
       <=
       N.of_nat
         (to_size
            (fold_left SizePlus ss base)
            Hredss))%N.
  Proof.
    intro ss; elim ss.
    - intros; simpl in *.
      match goal with
      | [ |- (_ <= N.of_nat (to_size _ ?H2))%N ] =>
        rewrite (to_size_proof _ _ H2)
      end.
      apply N.le_refl.
    - intros; simpl in *.
      match goal with
      | [ |- (fold_left _ _ ?BASESZ <= N.of_nat (to_size (fold_left _ _ ?BASE) _))%N ] =>
        let H := fresh "H" in
        let H' := fresh "H" in
        assert (H : exists H, BASESZ = N.of_nat (to_size BASE H));
        [ | destruct H as [H H']; rewrite H'; auto ]
      end.
      simpl.
      match goal with
      | [ H : size_closed ?B
          |- context[size_closed ?B /\ size_closed ?A] ] =>
        let H0 := fresh "H" in
        assert (H0 : size_closed A);
        [ | exists (conj H H0) ]
      end.
      { match goal with
        | [ H : size_closed (fold_left _ _ _) |- _ ] =>
          specialize (fold_SizePlus_reducible_imp_base_reducible H)
        end.
        intros; simpl in *.
        destructAll; auto. }
      match goal with
      | [ H : size_closed ?A |- context[size_to_nat ?A] ] =>
        specialize (is_size_to_nat _ H)
      end.
      intros; destructAll.
      match goal with
      | [ H : ?A = Some _ |- context[?A] ] => rewrite H
      end.
      rewrite Nnat.Nat2N.inj_add.
      match goal with
      | [ |- context[(N.of_nat _ + N.of_nat ?SZ1)%N =
                     (N.of_nat _ + N.of_nat ?SZ2)%N] ] =>
        let H := fresh "H" in
        assert (H : SZ1 = SZ2); [ | rewrite H; auto ]
      end.
      match goal with
      | [ H : size_to_nat ?A = Some _ |- _ ] =>
        specialize (size_to_nat_eq_to_size H)
      end.
      intros; destructAll.
      apply to_size_proof.
  Qed.

  Lemma subst_pretype_in_qual q pt :
    subst.subst'_qual
      (debruijn.subst'_of
         (debruijn.ext subst.SPretype pt debruijn.id)) q = q.
  Proof. destruct q. reflexivity. reflexivity. Qed.

  Lemma subst_loc_in_qual q l :
    subst.subst'_qual
      (debruijn.subst'_of
         (debruijn.ext subst.SLoc l debruijn.id)) q = q.
  Proof. destruct q. reflexivity. reflexivity. Qed.


  Lemma StructType_subst x10 ss:
    (StructType (combine (subst.subst'_types (debruijn.subst'_of (debruijn.weak subst.SLoc)) x10) ss)) = (debruijn.subst_ext (debruijn.weak subst.SLoc) (StructType (combine x10 ss))).
  Proof.
    simpl.
    erewrite subst.map_combine.
    do 2 f_equal.
    clear.
    induction ss; eauto.
    simpl.
    f_equal; eauto.
    clear IHss ss.
    induction a; eauto.
    simpl.
    f_equal; eauto.
  Qed.

  Lemma VariantType_subst ts:
    (VariantType (subst.subst'_types (debruijn.subst'_of (debruijn.weak subst.SLoc)) ts)) =
    (debruijn.subst_ext (debruijn.weak subst.SLoc) (VariantType ts)).
  Proof.
    simpl.
    f_equal.
  Qed.

  Lemma ArrayType_subst x10 x11:
    (ArrayType (QualT (subst.subst'_pretype (debruijn.subst'_of (debruijn.weak subst.SLoc)) x10)
                      (subst.subst'_qual (debruijn.subst'_of (debruijn.weak subst.SLoc)) x11))) =
    (debruijn.subst_ext (debruijn.weak subst.SLoc) (ArrayType (QualT x10 x11))).
  Proof.
    simpl.
    easy.
  Qed.

  Lemma under_pretype_subst_eq x y z:
    debruijn.under' subst.SPretype (debruijn.subst'_of (debruijn.weak subst.SLoc)) x y z =
      debruijn.subst'_of (debruijn.weak subst.SLoc) x y z.
  Proof.
    destruct x.
    - simpl. compute.
      f_equal. f_equal.
      induction y; eauto.
    - simpl. compute.
      f_equal. f_equal.
      induction y; eauto.
    - simpl. compute.
      f_equal. f_equal.
      induction y; eauto.
    - simpl.
      unfold under'.
      unfold under_ks'.
      simpl.
      unfold get_var'.
      unfold weaks'.
      unfold var'.
      unfold var.
      simpl.
      unfold zero.
      rewrite Nat.add_0_r.
      match goal with
      | [ |- context[if ?B then _ else _] ] =>
        remember B as b; generalize (eq_sym Heqb); case b; intros; auto
      end.
      f_equal.
      unfold sing in *.
      simpl in *.
      rewrite <-Nat.add_succ_r.
      rewrite Nat.sub_1_r.
      erewrite Nat.lt_succ_pred; [ rewrite Nat.add_comm; auto | ].
      rewrite Nat.ltb_ge in *.
      rewrite OrdersEx.Nat_as_DT.le_succ_l in *; eauto.
  Qed.

  Lemma subst'_pretype_subst_eq pt f g :
    (forall x y z, f x y z = g x y z) ->
    subst.subst'_pretype f pt = subst.subst'_pretype g pt.
  Proof.
    intros Heq. f_equal.
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros. eapply Heq.
  Qed.


  Lemma ExistType_subst x9 x10 x11 x12 :
    (Ex x9 x10 (QualT (subst.subst'_pretype (debruijn.subst'_of (debruijn.weak subst.SLoc)) x11)
                      (subst.subst'_qual (debruijn.subst'_of (debruijn.weak subst.SLoc)) x12))) =
    (debruijn.subst_ext (debruijn.weak subst.SLoc) (Ex x9 x10 (QualT x11 x12))).
  Proof.
    simpl.
    f_equal.
    - simpl.
      induction x9; eauto. simpl; f_equal; eauto.
    - simpl.
      induction x10; eauto.
    - f_equal.
      2: { induction x12; eauto; simpl. induction v; simpl; eauto. }

      eapply subst'_pretype_subst_eq.
      intros.
      rewrite under_pretype_subst_eq. reflexivity.
  Qed.

  Lemma InstIndsValid_app F chi chi' zs zs' :
    InstIndsValid F chi zs ->
    InstIndsValid F chi' zs' ->
    InstInds chi zs = Some chi' ->
    InstIndsValid F chi (zs ++ zs').
  Proof.
    intros Hv1 Hv2 Hi; induction Hv1; unfold InstInds in *; simpl in *; eauto.
    - inv Hi. eassumption.
    - econstructor. eassumption. eassumption.
      eapply IHHv1. eassumption. rewrite H0 in *. eassumption.
  Qed.

  Lemma InstIndValid_Function_Ctx_strong F F' chi zs :
    InstIndValid F chi zs ->
    type F = type F' ->
    qual F = qual F' ->
    size F = size F' ->
    location F = location F' ->
    InstIndValid F' chi zs.
  Proof.
    intros.
    destruct chi.
    eapply InstIndValid_Function_Ctx_stronger; eauto.
  Qed.

  Lemma InstIndsValid_Function_Ctx_strong F F' chi zs :
    InstIndsValid F chi zs ->
    type F = type F' ->
    qual F = qual F' ->
    size F = size F' ->
    location F = location F' ->
    InstIndsValid F' chi zs.
  Proof.
    intros.
    destruct chi.
    eapply InstIndsValid_Function_Ctx_stronger; eauto.
  Qed.

  Lemma size_to_nat_is_size sz n :
    size_to_nat sz = Some n -> exists (H : size_closed sz), to_size sz H = n.
  Proof.
    revert n; induction sz; simpl; intros n1 H; eauto.
    - congruence.
    - destruct (size_to_nat sz1) eqn:Hs1; try congruence.
      destruct (size_to_nat sz2) eqn:Hs2; try congruence.
      inv H. edestruct IHsz1. reflexivity. edestruct IHsz2. reflexivity.
      eexists (conj x x0).
      congruence.
    - exists I. congruence.
  Qed.


  Lemma size_val_leq S F v tau ts sz :
    HasTypeValue S F v tau ->
    Function_Ctx_empty F ->
    sizeOfType (type F) tau = Some ts ->
    SizeValid (size F) sz ->
    SizeLeq (size F) ts sz = Some true ->
    exists H, size_val v <= to_size sz H.
  Proof.
    intros Htyp He Hsz Hszvalid Hleq.
    destruct F; unfold Function_Ctx_empty in *; inv He.
    destructAll; simpl in *; subst.
    specialize (size_valid_empty_implies_to_nat _ Hszvalid).
    intro H100.
    destruct H100 as [n Hszval].
    specialize (SizeOfType_empty_valid Hsz).
    intro Htsvalid.
    specialize (size_valid_empty_implies_to_nat _ Htsvalid).
    intro H100.
    destruct H100 as [n' Htsval].
    eapply (SizeLeq_Const _ _ _ _ Htsval Hszval) in Hleq.
    eapply SizeOfValue_Typecheck_Actual in Htyp; eauto.
    rewrite Htyp.
    eapply size_to_nat_is_size in Hszval. destructAll. eauto.
  Qed.

  Lemma size_val_leq_list_strong F Ss vs taus ss n s Hs:
    Forall3 (fun (S : StoreTyping) (v : Value) (t : Typ) =>
               HasTypeValue S F v t) Ss vs taus ->

    Function_Ctx_empty F ->

    Forall2 (fun (tau : Typ) (sz : Size) =>
               exists tausz : Size,
                 sizeOfType (type F) tau = Some tausz /\
                   SizeLeq (size F) tausz sz = Some true) taus ss ->

    n <= to_size s Hs ->

    Forall (fun sz => SizeValid (size F) sz) ss ->

    exists H, fold_left (fun (n : nat) (v : Value) => size_val v + n) vs n <=
                to_size
                  (fold_left (fun sz1 sz2 : Size => SizePlus sz1 sz2) ss s) H.
  Proof.
    intros Hall. revert n s Hs ss.
    induction Hall; intros n s Hs ss Hemp Hall' Hleq Hvalid.
    - inv Hall'. simpl. eauto.
    - inv Hall'. destructAll. simpl.
      assert (Hsz : size_closed (SizePlus s y0)).
      { destruct F; inv Hemp. destructAll; simpl in *; subst.
        split; eauto.
        inversion Hvalid; subst.
        apply size_valid_empty_implies_to_nat in H5.
        destruct H5 as [n' H5].
        eapply size_to_nat_is_size in H5. destructAll. eassumption. }

      edestruct IHHall with (n := size_val y + n) (s := SizePlus s y0) (Hs := Hsz); eauto.

      -- simpl. destruct Hsz. rewrite to_size_proof with (H2 := Hs).
         eapply size_val_leq with (sz := y0) in H; eauto.
         2:{
           inversion Hvalid; subst; auto.
         }
         destructAll. rewrite to_size_proof with (H2 := x1). lia.
      -- inversion Hvalid; subst; auto.
  Qed.

  Corollary size_val_leq_list F Ss vs taus ss :
    Forall3 (fun (S : StoreTyping) (v : Value) (t : Typ) =>
               HasTypeValue S F v t) Ss vs taus ->

    Function_Ctx_empty F ->

    Forall2 (fun (tau : Typ) (sz : Size) =>
               exists tausz : Size,
                 sizeOfType (type F) tau = Some tausz /\
                   SizeLeq (size F) tausz sz = Some true) taus ss ->

    Forall (fun sz => SizeValid (size F) sz) ss ->

    exists H, fold_left (fun (n : nat) (v : Value) => size_val v + n) vs 0 <=
                to_size
                  (fold_left (fun sz1 sz2 : Size => SizePlus sz1 sz2) ss (SizeConst 0)) H.
  Proof.
    intros Hall3 Hf Hall2.
    assert (H0 : size_closed (SizeConst 0)). { exact I. }
    eapply size_val_leq_list_strong with (Hs := H0); eauto.
  Qed.

  Lemma Forall3_repeat (A B C : Type) (P : A -> B -> C -> Prop) (x1 : A)
        (x2 : B) (x3 : C) (j : nat) :
    P x1 x2 x3 -> Forall3 P (repeat x1 j) (repeat x2 j) (repeat x3 j).
  Proof.
    intros Hp. induction j; simpl; constructor; eauto.
  Qed.

  Lemma InstInds_coderef_TypeValid ft ft' zs F q :
     InstInds ft zs = Some ft' ->
     InstIndsValid F ft zs ->
     TypeValid F (QualT (CoderefT ft) q) ->
     TypeValid F (QualT (CoderefT ft') q).
  Proof.
    revert ft ft' F q.
    induction zs; simpl; intros; try (inv H; eassumption).
    unfold InstInds in H. simpl in H.
    inv H0.
    rewrite H7 in H.
    eapply (IHzs chi'); eauto.
    clear - H1 H4 H7.
    inv H1.
    eapply TCoderefValid; eauto.
    clear - H4 H7 H5.
    eapply FunTypeValid_InstInd; eauto.
  Qed.
  (*   inv H5. *)
  (*   destruct chi'. *)
  (*   econstructor. *)
  (*   (* substitution lemmas needed, but simple to prove otherwise *) *)

  Lemma split_combine: forall {A B} (l1 : list A) (l2: list B),
      length l1 = length l2 ->
      (split (combine l1 l2)) = (l1, l2).
  Proof.
    induction l1; intros; destruct l2; auto; try inversion H.
    simpl.
    rewrite IHl1; auto.
  Qed.


  Lemma TypeValid_Linear_Ctx F tau l :
    TypeValid F tau ->
    TypeValid (update_linear_ctx l F) tau.
  Proof.
    destruct F; subst; simpl in *.
    intros.
    eapply TypeValid_Function_Ctx; eauto.
  Qed.

  Lemma length_subst_index : forall {idx} {szs : list Size},
      length (subst.subst_index idx szs) = length szs.
  Proof.
    destruct idx.
    all: induction szs; intros; simpl in *; auto.
  Qed.

  Lemma length_subst_in_size : forall {idxs szs},
      length (subst_in_size idxs szs) = length szs.
  Proof.
    induction idxs; intros; simpl in *; auto.
    rewrite length_subst_index.
    rewrite IHidxs; auto.
  Qed.

  Lemma length_to_sizes : forall {szs H},
      length (to_sizes szs H) = length szs.
  Proof.
    induction szs; intros; simpl in *; auto.
  Qed.

  Lemma to_sizes_to_to_size : forall {szs} {H : sizes_closed szs},
      exists f,
        Forall (fun sz => exists H, f sz = to_size sz H) szs.
  Proof.
    induction szs.
    - intros.
      exists (fun _ => 0).
      auto.
    - intros.
      inversion H; subst.
      specialize (IHszs H3).
      destructAll.
      exists (fun sz =>
                if eq_dec_size a sz
                then to_size a H2
                else x sz).
      constructor.
      -- remember (eq_dec_size a a).
         case s.
         2:{
           intro H'; exfalso; apply H'; auto.
         }
         intros.
         exists H2; auto.
      -- rewrite Forall_forall.
         rewrite Forall_forall in H0.
         intros.
         specialize (H0 _ H1).
         remember (eq_dec_size a x0).
         case s; intros; subst; eauto.
  Qed.   

  Lemma to_sizes_cons : forall {sz} {szs} {H : sizes_closed (sz :: szs)},
      exists H1 H2,
        to_sizes (sz :: szs) H = (to_size sz H1) :: (to_sizes szs H2).
  Proof.
    intros.
    do 2 eexists.
    simpl in *; eauto.
  Qed.

  Lemma to_sizes_to_map : forall {szs} {H : sizes_closed szs} {f},
      Forall (fun sz => exists H, f sz = to_size sz H) szs ->
      to_sizes szs H = map f szs.
  Proof.
    induction szs; intros; auto.
    specialize (to_sizes_cons (sz:=a) (szs:=szs) (H:=H)).
    intros; destructAll.
    rewrite H1.
    replace (map f (a :: szs)) with (f a :: map f szs) by auto.
    inversion H0; subst.
    erewrite IHszs; eauto.
    destructAll.
    rewrite H2.
    erewrite to_size_proof; eauto.
  Qed.

  Lemma to_size_eq_size_to_nat : forall {sz} {H : size_closed sz},
      size_to_nat sz = Some (to_size sz H).
  Proof.
    intros.
    specialize (is_size_to_nat sz H).
    intros; destructAll.
    specialize (size_to_nat_eq_to_size H0).
    intros; destructAll.
    rewrite H0.
    erewrite to_size_proof; eauto.
  Qed.

  Lemma closed_sizes_eq : forall {szs} {H : sizes_closed szs},
      Forall2
        (fun sz0 sz1 =>
           SizeLeq [] sz0 sz1 = Some true /\
           SizeLeq [] sz1 sz0 = Some true)
        szs
        (map SizeConst (to_sizes szs H)).
  Proof.
    intros.
    specialize (to_sizes_to_to_size (H:=H)).
    intros; destructAll.
    specialize (to_sizes_to_map (H:=H) H0).
    intros.
    rewrite H1.
    rewrite map_map.
    apply Forall2_map_r_strong.
    intros.
    rewrite Forall_forall in H0.
    specialize (H0 _ H2).
    destructAll.
    specialize (to_size_eq_size_to_nat (H:=x1)).
    intros.
    rewrite <-H0 in H3.
    intros; split; eapply SizeLeq_leq; eauto.
    all: simpl; auto.
  Qed.

  Lemma nth_error_subst_index : forall {i} {idx} {tau sz} {L : Local_Ctx},
      nth_error (subst.subst_index idx L) i = Some (tau, sz) ->
      exists tau' sz',
        nth_error L i = Some (tau', sz') /\
        tau = subst.subst_index idx tau' /\
        sz = subst.subst_index idx sz'.
  Proof.
    induction i.
    - intros.
      destruct L; subst; simpl in *.
      -- destruct idx; simpl in *;
           match goal with
           | [ H : None = Some _ |- _ ] => inversion H
           end.
      -- destruct idx; simpl in *.
         all:
           match goal with
           | [ X : _ * _ |- _ ] => destruct X
           end.
         all:
           match goal with
           | [ H : Some _ = Some _ |- _ ] => inversion H; subst
           end.
         all: eauto.
    - intros.
      destruct L; subst; simpl in *.
      -- destruct idx; simpl in *;
           match goal with
           | [ H : None = Some _ |- _ ] => inversion H
           end.
      -- destruct idx; simpl in *.
         all:
           match goal with
           | [ H : context[ext subst.SLoc ?L] |- _ ] =>
             specialize (IHi (LocI L))
           | [ H : context[ext subst.SSize ?SZ] |- _ ] =>
             specialize (IHi (SizeI SZ))
           | [ H : context[ext subst.SQual ?Q] |- _ ] =>
             specialize (IHi (QualI Q))
           | [ H : context[ext subst.SPretype ?PT] |- _ ] =>
             specialize (IHi (PretypeI PT))
           end.
         all: simpl in *.
         all:
           match goal with
           | [ H' : nth_error _ _ = Some _ |- _ ] =>
             specialize (IHi _ _ _ H')
           end.
         all: eauto.
  Qed.

  Lemma in_subst_index : forall {idx} {tau sz} {L : Local_Ctx},
      In (tau, sz) (subst.subst_index idx L) ->
      exists tau' sz',
        In (tau', sz') L /\
        tau = subst.subst_index idx tau' /\
        sz = subst.subst_index idx sz'.
  Proof.
    intros.
    apply In_nth_error in H.
    destructAll.
    apply nth_error_subst_index in H.
    destructAll.
    do 2 eexists.
    split; eauto.
    eapply nth_error_In; eauto.
  Qed.

  Lemma subst_index_function_ctx : forall {idx} {F : Function_Ctx},
      subst.subst_index idx F =
      {| label := map (fun '(taus, L) => (subst.subst_index idx taus, subst.subst_index idx L)) (label F);
         ret := option_map (subst.subst_index idx) (ret F);
         qual := map (fun '(qs0, qs1) => (subst.subst_index idx qs0, subst.subst_index idx qs1)) (qual F);
         size := map (fun '(szs0, szs1) => (subst.subst_index idx szs0, subst.subst_index idx szs1)) (size F);
         type := map (fun '(sz, q, hc) => (subst.subst_index idx sz, subst.subst_index idx q, hc)) (type F);
         location := location F;
         linear := pmap (subst.subst_index idx) (linear F) |}.
  Proof.
    intros.
    destruct idx.
    all: simpl in *.
    all: destruct F; subst; simpl in *.
    all: unfold subst'_function_ctx; simpl in *; auto.
  Qed.

  Lemma option_map_option_map : forall {A B C} {f : A -> B} {g : B -> C} {maybe_obj},
      option_map g (option_map f maybe_obj) =
      option_map (fun x => g (f x)) maybe_obj.
  Proof.
    intros.
    destruct maybe_obj; simpl; auto.
  Qed.

  Lemma subst_indices_function_ctx : forall {idxs} {F : Function_Ctx},
      subst.subst_indices idxs F =
      {| label := map (fun '(taus, L) => (subst.subst_indices idxs taus, subst.subst_indices idxs L)) (label F);
         ret := option_map (subst.subst_indices idxs) (ret F);
         qual := map (fun '(qs0, qs1) => (subst.subst_indices idxs qs0, subst.subst_indices idxs qs1)) (qual F);
         size := map (fun '(szs0, szs1) => (subst.subst_indices idxs szs0, subst.subst_indices idxs szs1)) (size F);
         type := map (fun '(sz, q, hc) => (subst.subst_indices idxs sz, subst.subst_indices idxs q, hc)) (type F);
         location := location F;
         linear := pmap (subst.subst_indices idxs) (linear F) |}.
  Proof.
    induction idxs; intros; destruct F; subst; simpl in *; auto.
    - apply function_ctx_eq; simpl; auto.
      all:
        try match goal with
            | [ |- context[map _ ?L] ] =>
              rewrite <-(map_id L) at 1;
              apply map_ext_in;
              intros;
              repeat match goal with
                     | [ X : _ * _ |- _ ] => destruct X; auto
                     end
            end.
      -- destruct ret; simpl in *; auto.
      -- induction linear; simpl; auto.
         rewrite <-IHlinear; auto.
    - rewrite IHidxs.
      repeat rewrite subst_index_function_ctx.
      simpl in *.
      repeat rewrite map_map.
      rewrite option_map_option_map.
      rewrite pmap_pmap.
      apply function_ctx_eq; simpl; auto.
      all: apply map_ext_in.
      all: intros.
      all:
        repeat match goal with
               | [ X : _ * _ |- _ ] => destruct X
               end.
      all: auto.
  Qed.

  Lemma subst_index_types : forall {idx} {l : list Typ},
      subst.subst_index idx l =
      map (subst.subst_index idx) l.
  Proof.
    induction l; simpl; auto.
    - destruct idx; simpl; auto.
    - destruct idx; simpl in *.
      all: rewrite IHl; auto.
  Qed.

  Lemma subst_indices_types : forall {idxs} {l : list Typ},
      subst.subst_indices idxs l =
      map (subst.subst_indices idxs) l.
  Proof.
    induction idxs; simpl; auto.
    - intros; rewrite map_id; auto.
    - intros.
      rewrite <-map_map.
      rewrite IHidxs.
      rewrite subst_index_types; auto.
  Qed.

  Lemma subst_index_types_sizes : forall {idx} {l : list (Typ * Size)},
      subst.subst_index idx l =
      map (fun '(a, b) => (subst.subst_index idx a, subst.subst_index idx b)) l.
  Proof.
    induction l; simpl; auto.
    - destruct idx; simpl; auto.
    - destruct idx; simpl in *.
      all: rewrite IHl; auto.
  Qed.

  Lemma subst_indices_types_sizes : forall {idxs} {l : list (Typ * Size)},
      subst.subst_indices idxs l =
      map (fun '(a, b) => (subst.subst_indices idxs a, subst.subst_indices idxs b)) l.
  Proof.
    induction idxs; simpl; auto.
    - intro l; induction l; simpl in *; auto.
      destruct a.
      rewrite IHl.
      rewrite map_map.
      match goal with
      | [ |- _ :: ?A = _ :: ?B ] =>
        replace A with B; auto
      end.
      apply map_ext_in.
      intros.
      destruct a; auto.
    - intros.
      match goal with
      | [ |- _ = ?A ] =>
        replace A with
            (map
               (fun '(a0, b) =>
                  (subst.subst_index a a0,
                   subst.subst_index a b))
               (map
                  (fun '(a, b) =>
                     (subst.subst_indices idxs a,
                      subst.subst_indices idxs b))
                  l))
      end.
      2:{
        generalize l.
        intro l'; induction l'; simpl; auto.
        destruct a0.
        rewrite IHl'; auto.
      }
      rewrite IHidxs.
      rewrite subst_index_types_sizes; auto.
  Qed.

  Lemma subst_indices_types_sizes_app : forall {idxs} {l1 : list (Typ * Size)} {l2},
      subst.subst_indices idxs (l1 ++ l2) =
      (subst.subst_indices idxs l1)
        ++
        (subst.subst_indices idxs l2).
  Proof.
    intros.
    repeat rewrite subst_indices_types_sizes.
    apply map_app.
  Qed.

  Lemma subst_indices_types_sizes_combine : forall {idxs} {l1 : list Typ} {l2 : list Size},
      subst.subst_indices idxs (combine l1 l2) =
      combine (map (subst.subst_indices idxs) l1) (map (subst.subst_indices idxs) l2).
  Proof.
    intros.
    rewrite <-subst.map_combine.
    rewrite subst_indices_types_sizes.
    auto.
  Qed.

  Lemma subst_indices_type : forall {idxs p q},
      subst.subst_indices idxs (QualT p q) =
      QualT (subst.subst_indices idxs p)
            (subst.subst_indices idxs q).
  Proof.
    induction idxs; intros; simpl in *; auto.
    rewrite IHidxs.
    match goal with
    | [ X : Index |- _ ] => destruct X; simpl; auto
    end.
  Qed.
  
  Lemma subst_indices_Unit : forall {idxs},
      subst.subst_indices idxs Unit
      =
      Unit.
  Proof.
    induction idxs; intros; simpl in *; auto.
    rewrite IHidxs.
    match goal with
    | [ X : Index |- _ ] => destruct X; simpl; auto
    end.
  Qed.

  Lemma subst_indices_Unrestricted : forall {idxs},
      subst.subst_indices idxs (QualConst Unrestricted)
      =
      Unrestricted.
  Proof.
    induction idxs; intros; simpl in *; auto.
    rewrite IHidxs.
    match goal with
    | [ X : Index |- _ ] => destruct X; simpl; auto
    end.
  Qed.

  Lemma in_subst_indices : forall {idxs} {tau sz} {L : Local_Ctx},
      In (tau, sz) (subst.subst_indices idxs L) ->
      exists tau' sz',
        In (tau', sz') L /\
        tau = subst.subst_indices idxs tau' /\
        sz = subst.subst_indices idxs sz'.
  Proof.
    induction idxs; intros; simpl in *; eauto.
    apply in_subst_index in H.
    destructAll.
    specialize (IHidxs _ _ _ H).
    destructAll.
    eauto.
  Qed.

  Lemma InstInds_cons : forall {idxs idx foralls tau1 tau2 foralls' tau1' tau2' foralls'' tau1'' tau2''},
      InstInds (FunT foralls (Arrow tau1 tau2)) (idx :: idxs) =
      Some (FunT foralls'' (Arrow tau1'' tau2'')) ->
      InstInd (FunT foralls (Arrow tau1 tau2)) idx =
      Some (FunT foralls' (Arrow tau1' tau2')) ->
      InstInds (FunT foralls' (Arrow tau1' tau2')) idxs =
      Some (FunT foralls'' (Arrow tau1'' tau2'')).
  Proof.
    intros.
    unfold InstInds in *.
    simpl in *.
    rewrite H0 in H.
    auto.
  Qed.

  Lemma subst_of_indices_commute_qual : forall {idxs kvs kvs' idx q atyp atyp' F kvs'' atyp''},
      Function_Ctx_empty F ->
      InstIndsValid F (FunT kvs atyp) idxs ->
      InstInds (FunT kvs atyp) idxs = Some (FunT kvs' atyp') ->
      InstIndValid F (FunT kvs'' atyp'') idx ->
      subst.subst'_qual
        (subst.under_kindvars'
           kvs'
           (subst'_of (subst_of_indices idxs))
           ∘'
           subst.under_kindvars'
           kvs
           (subst'_of (subst_of_index idx)))
        q
      =
      subst.subst'_qual
        (subst.under_kindvars'
           kvs'
           (subst'_of (subst_of_index idx ∘ subst_of_indices idxs)))
        q.
  Proof.
    intros.
    erewrite subst_of_indices_commute_gen; eauto.
  Qed.

  Lemma subst_of_indices_commute_types : forall {kvs kvs' idxs idx taus atyp atyp' F kvs'' atyp''},
      Function_Ctx_empty F ->
      InstIndsValid F (FunT kvs atyp) idxs ->
      InstInds (FunT kvs atyp) idxs = Some (FunT kvs' atyp') ->
      InstIndValid F (FunT kvs'' atyp'') idx ->
      subst.subst'_types
        (subst.under_kindvars'
           kvs'
           (subst'_of (subst_of_indices idxs))
           ∘'
           subst.under_kindvars'
           kvs
           (subst'_of (subst_of_index idx)))
        taus
      =
      subst.subst'_types
        (subst.under_kindvars'
           kvs'
           (subst'_of (subst_of_index idx ∘ subst_of_indices idxs)))
        taus.
  Proof.
    intros.
    erewrite subst_of_indices_commute_gen; eauto.
  Qed.

  Lemma InstInd_subst_index_atyp : forall {kvs tau1 tau2 idx kvs' tau1' tau2'},
      InstInd (FunT kvs (Arrow tau1 tau2)) idx =
      Some (FunT kvs' (Arrow tau1' tau2')) ->
      tau1' = subst_ext' (subst.under_kindvars' kvs' (subst'_of (subst_of_index idx))) tau1 /\
      tau2' = subst_ext' (subst.under_kindvars' kvs' (subst'_of (subst_of_index idx))) tau2.
  Proof.
    intros.
    destruct idx; simpl in *.
    all: destruct kvs; simpl in *.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      | [ X : KindVar |- _ ] => destruct X; simpl in *
      end.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; simpl in *; clear H
      end.
    all: rewrite subst.under_kindvars'_subst'_kindvars; auto.
  Qed.

  Lemma InstInds_subst_indices : forall {idxs kvs tau1 tau2 kvs' tau1' tau2' F},
      Function_Ctx_empty F ->
      InstIndsValid F (FunT kvs (Arrow tau1 tau2)) idxs ->
      InstInds (FunT kvs (Arrow tau1 tau2)) idxs =
      Some (FunT kvs' (Arrow tau1' tau2')) ->
      tau1' = subst_ext' (subst.under_kindvars' kvs' (subst'_of (subst_of_indices idxs))) tau1 /\
      tau2' = subst_ext' (subst.under_kindvars' kvs' (subst'_of (subst_of_indices idxs))) tau2.
  Proof.
    induction idxs; intros; auto.
    - unfold InstInds in *.
      simpl in *.
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst; auto
      end.
      rewrite under_kindvars_id.
      repeat rewrite id_no_effect_on_types; auto.
    - match goal with
      | [ H : InstInds _ (_ :: _) = Some _ |- _ ] =>
        specialize (InstInds_cons_inv H)
      end.
      intros; destructAll.
      match goal with
      | [ H : InstInd _ _ = Some _ |- _ ] =>
        specialize (InstInd_subst_index_atyp H)
      end.
      intros; destructAll.
      match goal with
      | [ H : InstIndsValid _ _ (_ :: _) |- _ ] =>
        specialize (InstIndsValid_cons_inv H)
      end.
      intros; destructAll.
      match goal with
      | [ H : ?A = _, H' : ?A = _ |- _ ] =>
        rewrite H in H'; inversion H'; subst
      end.
      match goal with
      | [ H : forall _ _ _ _ _ _ _,
            _ ->
            InstIndsValid _ _ ?L -> _,
          H' : Function_Ctx_empty _,
          H'' : InstIndsValid _ _ ?L,
          H''' : InstInds _ ?L = Some _ |- _ ] =>
        specialize (H _ _ _ _ _ _ _ H' H'' H''')
      end.
      destructAll.
      repeat match goal with
             | [ |- context[subst.subst'_types ?F ?TS] ] =>
               replace (subst.subst'_types F TS)
                 with (subst_ext' F TS) by auto
             end.      
      repeat rewrite subst_ext'_assoc.
      simpl.
      split; eapply subst_of_indices_commute_types; eauto.
  Qed.

  Ltac handle_qual :=
    erewrite qual_debruijn_subst_ext;
      [ | | eapply debruijn_subst_ext_under_kindvars;
            apply simpl_debruijn_subst_ext_conds ];
      solve_ineqs.
  Ltac handle_quals :=
    erewrite weak_non_qual_no_effect_on_quals;
      [ | | apply single_weak_debruijn_weak_conds ];
      solve_ineqs.

  Lemma non_qual_kv_does_not_effect_qual : forall {F kv},
      (forall qs0 qs1, kv <> QUAL qs0 qs1) ->
      qual (add_constraint F kv) = qual F.
  Proof.
    intros.
    destruct kv; simpl in *.
    2:{
      specialize (H _ _ eq_refl).
      exfalso; auto.
    }
    all: destruct F; subst; simpl in *.
    all: rewrite <-map_id.
    all: apply map_ext.
    all: intros.
    all:
      match goal with
      | [ X : _ * _ |- _ ] => destruct X
      end.
    all: do 2 handle_quals; auto.
  Qed.

  Lemma kv_is_qual_or_non_qual : forall kv,
      (forall qs0 qs1, kv <> QUAL qs0 qs1) \/
      (exists qs0 qs1, kv = QUAL qs0 qs1).
  Proof.
    destruct kv.
    2:{
      right; eauto.
    }
    all: left; intros; intro H'; inversion H'.
  Qed.

  Lemma qual_add_constraints_inv_gen : forall {kvs1 kvs2 F1 F2},
      qual F1 = qual F2 ->
      Forall2
        (fun kv1 kv2 =>
           forall qs0 qs1,
             kv1 = QUAL qs0 qs1 <-> kv2 = QUAL qs0 qs1)
        kvs1
        kvs2 ->
      qual (add_constraints F1 kvs1) =
      qual (add_constraints F2 kvs2).
  Proof.
    induction kvs1; intros;
      match goal with
      | [ H : Forall2 _ _ _ |- _ ] => inversion H; subst
      end;
      simpl in *; auto.
    - eapply IHkvs1; eauto.
      match goal with
      | [ |- _ (add_constraint _ ?KV1) =
             _ (add_constraint _ ?KV2) ] =>
        specialize (kv_is_qual_or_non_qual KV1);
        let H := fresh "H" in intro H; case H;
        specialize (kv_is_qual_or_non_qual KV2);
        let H := fresh "H" in intro H; case H
      end.
      1:{
        intros.
        do 2 ltac:(rewrite non_qual_kv_does_not_effect_qual; auto).
      }
      all: intros.
      all: destructAll.
      all:
        match goal with
        | [ H : context[_ = QUAL _ _ <-> _ = QUAL _ _]
            |- context[QUAL ?QS0 ?QS1] ] =>
          specialize (H QS0 QS1);
          let H' := fresh "H" in
          destruct H as [H H'];
          try specialize (H eq_refl);
          try specialize (H' eq_refl)
        end.
      all: subst.
      all:
        try match goal with
            | [ H : QUAL _ _ = QUAL _ _ |- _ ] =>
              inversion H; subst
            end.
      all: destruct F1; destruct F2; subst; simpl in *.
      all:
        match goal with
        | [ H : ?A = ?B |- _ :: _ _ ?A = _ :: _ _ ?B ] =>
          rewrite H; auto
        end.
  Qed.

  Lemma qual_add_constraints_inv : forall {idxs F1 F2},
      qual F1 = qual F2 ->
      qual (add_constraints F1 idxs) = qual (add_constraints F2 idxs).
  Proof.
    induction idxs; intros; simpl in *; auto.
    apply IHidxs.
    match goal with
    | [ X : KindVar |- _ ] => destruct X
    end.
    all: simpl in *.
    all: destruct F1; destruct F2; simpl in *.
    all:
      match goal with
      | [ H : _ = _ |- _ ] => rewrite H; auto
      end.
  Qed.

  Lemma under_kindvar_comm : forall {kv kv' su},
      subst.under_kindvar' kv (subst.under_kindvar' kv' su) =
      subst.under_kindvar' kv' (subst.under_kindvar' kv su).
  Proof.
    destruct kv; destruct kv'; intros; simpl in *; auto.
    all: unfold subst.under_kindvar'.
    all: unfold Subst'.
    all: apply FunctionalExtensionality.functional_extensionality_dep.
    all: intros.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all:
      match goal with
      | [ X : subst.Ind |- _ ] => destruct X
      end.
    all: simpl.
    all: unfold under'.
    all: unfold under_ks'.
    all: simpl.
    all: unfold var'.
    all: unfold var.
    all: simpl.
    all: unfold sing.
    all: simpl.
    all: unfold plus.
    all: simpl.
    all: repeat rewrite Nat.sub_0_r.
    all: repeat rewrite Nat.add_0_l.
    all:
      try match goal with
          | [ |- context[if ?B then _ else _] ] =>
            remember B as b;
            generalize (eq_sym Heqb); case b; intros; auto
          end.
    all:
      match goal with
      | [ |- _ _ _ ?F1 = _ _ _ ?F2 ] =>
        replace F1 with F2; auto
      end.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all: repeat rewrite Nat.add_assoc.
    all:
      match goal with
      | [ |- ?A + ?B + _ = _ ] =>
        rewrite (Nat.add_comm A B); auto
      end.
  Qed.

  Lemma under_kindvars_under_kindvar_comm : forall {kvs kv su},
      subst.under_kindvars' kvs (subst.under_kindvar' kv su) =
      subst.under_kindvar' kv (subst.under_kindvars' kvs su).
  Proof.
    induction kvs; intros; simpl in *; auto.
    rewrite IHkvs.
    rewrite under_kindvar_comm; auto.
  Qed.

  Lemma subst_kindvars_snoc : forall {kvs kv su},
      subst.subst'_kindvars su (kvs ++ [kv]) =
      (subst.subst'_kindvars su kvs)
        ++
        [subst.subst'_kindvar
           (subst.under_kindvars' kvs su) kv].
  Proof.
    induction kvs; intros; simpl in *; auto.
    rewrite IHkvs.
    rewrite under_kindvars_under_kindvar_comm; auto.
  Qed.

  Lemma under_kindvars_snoc : forall {kvs kv su},
      subst.under_kindvars' (kvs ++ [kv]) su =
      subst.under_kindvars' kvs (subst.under_kindvar' kv su).
  Proof.
    induction kvs; intros; simpl in *; auto.
    rewrite IHkvs; auto.
  Qed.

  Lemma under_kindvar_subst_diff_knd : forall {kv knd obj},
      subst.kind_of_kindvar kv <> knd ->
      knd <> subst.SPretype ->
      subst.under_kindvar' kv (subst'_of (ext knd obj id)) =
      subst'_of (ext knd obj id).
  Proof.
    destruct kv; destruct knd; intros; simpl in *.
    all: solve_impossibles.
    all: unfold subst.under_kindvar'.
    all: unfold under'.
    all: unfold Subst'.
    all: apply FunctionalExtensionality.functional_extensionality_dep.
    all: intros.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all: apply FunctionalExtensionality.functional_extensionality.
    all: intros.
    all:
      match goal with
      | [ X : subst.Ind |- _ ] => destruct X
      end.
    all: simpl.
    all: unfold get_var'.
    all: unfold weaks'.
    all: unfold var.
    all: simpl.
    all: unfold under_ks'.
    all: simpl.
    all: unfold get_var'.
    all: unfold weaks'.
    all: unfold var'.
    all: unfold var.
    all: simpl.
    all: unfold plus.
    all: unfold zero.
    all: unfold sing.
    all: simpl.
    all: repeat rewrite Nat.add_0_r.
    all: repeat rewrite Nat.add_0_l.
    all: repeat rewrite Nat.sub_0_r.
    all: auto.
    all:
      try match goal with
          | [ |- context[if ?B then _ else _] ] =>
            remember B as b;
            generalize (eq_sym Heqb); case b; intros; auto
          end.
    all: try rewrite Nat.add_comm.
    all: try rewrite <-Nat.add_succ_l.
    all: try rewrite Nat.sub_1_r.
    all: try ltac:(rewrite Nat.succ_pred; [ rewrite Nat.add_comm; auto | ]).
    all: try intro; subst.
    all: unfold Nat.ltb in *.
    all: simpl in *.
    all:
      try match goal with
          | [ H : true = false |- _ ] => inversion H
          end.
    
    all:
      match goal with
      | [ |- _ _ ?SZ = _ ] => generalize SZ
      end.
    all: let sz := fresh "sz" in intro sz; induction sz.
    all: simpl in *; auto.
    all: rewrite IHsz1.
    all: rewrite IHsz2; auto.
  Qed.

  Lemma weak_under_comm_qual_gen : forall {f1 f2 f3 ks q q'},
      debruijn_weaks_conds f1 debruijn.zero
                           (debruijn.sing subst.SQual 1) ->
      debruijn_subst_ext_conds f2 ks subst.SQual q' ->
      debruijn_subst_ext_conds
        f3
        (debruijn.plus ks (debruijn.sing subst.SQual 1))
        subst.SQual q' ->
      subst.subst'_qual f3 (subst.subst'_qual f1 q) =
      subst.subst'_qual f1 (subst.subst'_qual f2 q).
  Proof.
    intros.
    destruct q; simpl in *; auto.
    unfold get_var'.
    unfold debruijn_weaks_conds in *.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ >= _ -> ?F _ _ _ = _]
        |- _ _ (?F _ _ _) = _ ] =>
      rewrite H
    end.
    2:{
      unfold zero.
      unfold Peano.ge.
      apply Nat.le_0_l.
    }
    simpl.
    unfold get_var'.
    unfold zero.
    match goal with
    | [ H : context[_ <> ?T -> ?F _ _ _ = _]
        |- _ = _ _ (?F _ ?V _) ] =>
      let H0 := fresh "H" in
	  assert (H0 : V = T \/ V <> T) by apply eq_dec_nat;
      case H0; intros; subst; [ | rewrite H; auto ]
    end.
    - match goal with
      | [ H : context[?F _ ?IDX _ = _] |- context[?F _ ?IDX _] ] =>
        rewrite H
      end.
      simpl.
      rewrite plus_zero.
      match goal with
      | [ |- _ _ (Datatypes.S (?F ?S)) _ = _ ] =>
        replace (Datatypes.S (F S)) with (plus F (sing S 1) S)
      end.
      2:{
        unfold plus.
        unfold sing; simpl.
        rewrite Nat.add_1_r; auto.
      }
      match goal with
      | [ H : context[?F _ ?IDX _] |- context[?F _ ?IDX _] ] =>
        rewrite H
      end.
      rewrite plus_zero.
      simpl.
      match goal with
      | [ |- subst.subst'_qual _ ?Q = _ ] =>
        destruct Q; simpl in *; auto
      end.
      unfold get_var'.
      unfold weaks'.
      unfold var.
      simpl.
      match goal with
      | [ H : context[_ >= _ -> ?F _ _ _ = _]
          |- _ = ?F _ _ _ ] =>
        rewrite H
      end.
      2:{
        unfold zero.
        unfold Peano.ge.
        apply Nat.le_0_l.
      }
      simpl.
      unfold plus.
      unfold zero.
      repeat rewrite Nat.add_0_r.
      rewrite Nat.add_1_r.
      rewrite Nat.add_succ_l; auto.
    - simpl.
      unfold get_var'.
      match goal with
      | [ H : context[_ >= _ -> ?F _ _ _ = _]
          |- _ = ?F _ _ _ ] =>
        rewrite H
      end.
      2:{
        unfold zero.
        unfold Peano.ge.
        apply Nat.le_0_l.
      }
      simpl.
      unfold zero.
      unfold shift_down_after.
      rewrite Nat.add_0_l.
      match goal with
      | [ H : context[_ <> plus _ _ _ -> ?F _ _ _ = _]
          |- ?F _ _ _ = _ ] =>
        rewrite H
      end.
      2:{
        unfold plus.
        unfold sing.
        simpl.
        rewrite <-Nat.add_1_r.
        rewrite Nat.add_cancel_r; auto.
      }
      simpl.
      unfold shift_down_after.
      rewrite Nat.add_0_l.
      match goal with
      | [ |- _ = _ (Datatypes.S (if ?B then _ else _)) ] =>
        remember B as b; generalize (eq_sym Heqb); case b; intros
      end.
      -- match goal with
         | [ |- context[if ?B then _ else _] ] =>
           replace B with true; auto
         end.
         unfold plus.
         rewrite Nat.add_comm.
         apply eq_sym.
         rewrite Nat.ltb_lt.
         rewrite Nat.add_comm.
         rewrite <-Nat.add_1_r.
         apply plus_lt_compat_r.
         rewrite <-Nat.ltb_lt; auto.
      -- match goal with
         | [ |- context[if ?B then _ else _] ] =>
           replace B with false
         end.
         2:{
           unfold plus.
           rewrite Nat.add_comm.
           apply eq_sym.
           rewrite Nat.ltb_ge.
           unfold sing.
           rewrite Nat.add_comm.
           simpl.
           match goal with
           | [ |- _ <= Datatypes.S ?V ] =>
             rewrite <-(Nat.add_1_r V)
           end.
           apply plus_le_compat_r.
           rewrite <-Nat.ltb_ge; auto.
         }
         rewrite Nat.sub_1_r.
         rewrite Nat.pred_succ.
         match goal with
         | [ |- QualVar ?V = _ ] => destruct V
         end.
         --- rewrite Nat.ltb_ge in *.
             match goal with
             | [ H : _ <= 0 |- _ ] => apply le_n_0_eq in H
             end.
             exfalso; eauto.
         --- rewrite Nat.sub_1_r.
             rewrite Nat.pred_succ; auto.
  Qed.

  Lemma weak_under_comm_qual : forall {kvs q q'},
      subst.subst'_qual
        (subst.under_kindvars'
           kvs
           (under'
              subst.SQual
              (subst'_of (ext subst.SQual q' id))))
        (subst.subst'_qual
           (subst'_of (weak subst.SQual))
           q)
      =
      subst.subst'_qual
        (subst'_of (weak subst.SQual))
        (subst.subst'_qual
           (subst.under_kindvars'
              kvs
              (subst'_of (ext subst.SQual q' id)))
           q).
  Proof.
    intros.
    erewrite weak_under_comm_qual_gen; auto.
    - apply single_weak_debruijn_weak_conds.
    - eapply debruijn_subst_ext_under_kindvars.
      apply simpl_debruijn_subst_ext_conds.
    - assert (H' : forall f ks ks' knd obj, ks = ks' -> debruijn_subst_ext_conds f ks knd obj -> debruijn_subst_ext_conds f ks' knd obj).
      { intros; subst; auto. }

      eapply H'.
      2:{
        eapply debruijn_subst_ext_under_kindvars.
        eapply debruijn_subst_ext_under_knd.
        apply simpl_debruijn_subst_ext_conds.
      }

      apply FunctionalExtensionality.functional_extensionality.
      intros.
      rewrite fold_right_plus_comm.
      unfold plus.
      apply Nat.add_comm.
  Qed.

  Lemma weak_under_comm_quals : forall {qs kvs q},
      subst.subst'_quals
        (subst.under_kindvars'
           kvs
           (under'
              subst.SQual
              (subst'_of (ext subst.SQual q id))))
        (subst.subst'_quals
           (subst'_of (weak subst.SQual))
           qs)
      =
      subst.subst'_quals
        (subst'_of (weak subst.SQual))
        (subst.subst'_quals
           (subst.under_kindvars'
              kvs
              (subst'_of (ext subst.SQual q id)))
           qs).
  Proof.
    induction qs; intros; simpl in *; auto.
    rewrite weak_under_comm_qual.
    rewrite IHqs; auto.
  Qed.

  Lemma collect_qctx_subst_qual : forall {kvs q},
      collect_qctx
        (subst.subst'_kindvars
           (subst'_of (ext subst.SQual q id))
           kvs)
      =
      map
        (fun '(qs0, qs1) =>
           (subst.subst'_quals
              (subst.under_kindvars'
                 kvs
                 (subst'_of (ext subst.SQual q id)))
              qs0,
            subst.subst'_quals
              (subst.under_kindvars'
                 kvs
                 (subst'_of (ext subst.SQual q id)))
              qs1))
        (collect_qctx kvs).
  Proof.
    apply
      (rev_ind
         (fun kvs =>
            forall q,
              collect_qctx
                (subst.subst'_kindvars
                   (subst'_of (ext subst.SQual q id))
                   kvs)
              =
              map
                (fun '(qs0, qs1) =>
                   (subst.subst'_quals
                      (subst.under_kindvars'
                         kvs
                         (subst'_of (ext subst.SQual q id)))
                      qs0,
                    subst.subst'_quals
                      (subst.under_kindvars'
                         kvs
                         (subst'_of (ext subst.SQual q id)))
                      qs1))
                (collect_qctx kvs))).
    all: intros.
    all: simpl in *.
    - unfold collect_qctx.
      simpl; auto.
    - rewrite collect_qctx_snoc.
      rewrite subst_kindvars_snoc.
      rewrite collect_qctx_snoc.
      match goal with
      | [ H : forall _, _ = _ |- _ ] => rewrite H
      end.
      match goal with
      | [ X : KindVar |- _ ] => destruct X; simpl in *; auto
      end.
      
      1,3-4: rewrite under_kindvars_snoc.
      1-3: rewrite under_kindvar_subst_diff_knd; auto; solve_ineqs.

      match goal with
      | [ |- ?A :: ?B = ?C :: ?D ] =>
        replace A with C; [ replace B with D; auto | ]
      end.
      -- repeat rewrite map_map.
         apply map_ext.
         let x := fresh "x" in intro x; destruct x.
         repeat rewrite under_kindvars_snoc.
         unfold subst.under_kindvar'.
         simpl.
         repeat rewrite weak_under_comm_quals; auto.
      -- repeat rewrite under_kindvars_snoc.
         unfold subst.under_kindvar'.
         simpl.
         repeat rewrite weak_under_comm_quals; auto.
  Qed.
  
  Lemma ks_of_kvs_susbt'_kindvars : forall {kvs su},
      ks_of_kvs (subst.subst'_kindvars su kvs) =
      ks_of_kvs kvs.
  Proof.
    induction kvs; simpl in *; auto.
    intros.
    rewrite IHkvs.
    unfold subst.subst'_kindvar.
    destruct a; simpl; auto.
  Qed.

  Lemma non_qual_subst_does_not_effect_quals : forall {kvs kndspec f ks obj},
      kndspec <> subst.SQual ->
      debruijn_subst_ext_conds f ks kndspec obj ->
      Forall2
        (fun kv1 kv2 =>
           forall qs0 qs1,
             kv1 = QUAL qs0 qs1 <-> kv2 = QUAL qs0 qs1)
        kvs
        (subst.subst'_kindvars f kvs).
  Proof.
    induction kvs; intros; simpl in *; auto.
    constructor.
    - intros.
      match goal with
      | [ |- ?KV = _ <-> _ ] => destruct KV
      end.
      all: simpl.
      all: split.
      all: intro H'; inversion H'; subst; simpl in *.
      all: repeat erewrite quals_debruijn_subst_ext; eauto.
    - match goal with
      | [ |- context[subst.under_kindvar' ?KV _] ] =>
        destruct KV
      end.
      all: eapply IHkvs.
      all: unfold subst.under_kindvar'.
      all: try eapply debruijn_subst_ext_under_knd.
      all: eauto.
  Qed.

  Lemma QualLeq_susbt_index_gen : forall {foralls idx F foralls' tau1 tau2 tau1' tau2' q1 q2},
      InstIndValid F (FunT foralls (Arrow tau1 tau2)) idx ->
      InstInd (FunT foralls (Arrow tau1 tau2)) idx =
      Some (FunT foralls' (Arrow tau1' tau2')) ->
      QualLeq
        (qual (add_constraints F foralls))
        q1 q2
      = Some true ->
      QualLeq
        (qual (add_constraints F foralls'))
        (subst_ext' (subst.under_kindvars' foralls' (subst'_of (subst_of_index idx))) q1)
        (subst_ext' (subst.under_kindvars' foralls' (subst'_of (subst_of_index idx))) q2)
      = Some true.
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

    destruct foralls; intros.
    1:{
      simpl in *.
      match goal with
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    }
    match goal with
    | [ H : InstIndValid _ _ _ |- _ ] =>
      inversion H; subst; simpl in *
    end.

    all:
      match goal with
      | [ H : Some _ = Some _ |- _ ] =>
        inversion H; subst; clear H
      end.
    1-2,4: do 2 handle_qual.
    1-3:
      match goal with
      | [ H : QualLeq ?A _ _ = Some _
          |- QualLeq ?B _ _ = Some _ ] =>
        replace B with A; auto
      end.
    1-3: apply qual_add_constraints_inv_gen.
    all: try eapply non_qual_subst_does_not_effect_quals.
    all: try apply simpl_debruijn_subst_ext_conds.
    all: solve_ineqs.
    1-3: destruct F; subst; simpl in *.
    1-3: rewrite <-map_id.
    1-3: apply map_ext_in.
    1-3: intros.
    1-3:
      match goal with
      | [ X : _ * _ |- _ ] => destruct X
      end.
    1-3: do 2 handle_quals; auto.

    eapply QualLeq_subst'; eauto.
    match goal with
    | [ |- context[subst.under_kindvars' ?KVS] ] =>
      match goal with
      | [ |- context[ks_of_kvs ?KVS2] ] =>
        replace (ks_of_kvs KVS2) with (ks_of_kvs KVS)
      end
    end.
    2:{ rewrite ks_of_kvs_subst_kindvars; auto. }
    apply pure_under_kindvars.
  Qed.

  Lemma QualLeq_susbt_indices_gen : forall {idxs F foralls foralls' tau1 tau2 tau1' tau2' q1 q2},
      InstIndsValid F (FunT foralls (Arrow tau1 tau2)) idxs ->
      Function_Ctx_empty F ->
      InstInds (FunT foralls (Arrow tau1 tau2)) idxs =
      Some (FunT foralls' (Arrow tau1' tau2')) ->
      QualLeq
        (qual (add_constraints F foralls))
        q1 q2
      = Some true ->
      QualLeq
        (qual (add_constraints F foralls'))
        (subst_ext' (subst.under_kindvars' foralls' (subst'_of (subst_of_indices idxs))) q1)
        (subst_ext' (subst.under_kindvars' foralls' (subst'_of (subst_of_indices idxs))) q2)
      = Some true.
  Proof.
    induction idxs; intros.
    - unfold InstInds in *; simpl in *.
      match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H; subst; auto
      end.
      rewrite under_kindvars_id.
      repeat rewrite id_no_effect_on_qual; auto.
    - match goal with
      | [ H : InstIndsValid _ _ (_ :: _) |- _ ] =>
        specialize (InstIndsValid_cons_inv H)
      end.
      intros; destructAll.

      match goal with
      | [ H : InstIndValid _ _ ?IDX,
          H' : InstInd _ ?IDX = Some _,
          H'' : QualLeq _ _ _ = Some _ |- _ ] =>
        specialize (QualLeq_susbt_index_gen H H' H'')
      end.
      intros.
      match goal with
      | [ H : InstInds _ (?A :: _) = Some _,
          H' : InstInd _ ?A = Some _ |- _ ] =>
        specialize (InstInds_cons H H')
      end.
      intros.
      match goal with
      | [ H : context[InstIndsValid _ _ ?L -> _],
          H' : InstIndsValid _ _ ?L,
          H'''' : Function_Ctx_empty _,
          H'' : InstInds _ ?L = Some _,
          H''' : QualLeq _ _ _ = Some _ |- _ ] =>
        specialize (H _ _ _ _ _ _ _ _ _ H' H'''' H'' H''')
      end.

      repeat rewrite subst_ext'_assoc in IHidxs.
      erewrite subst_of_indices_commute_qual in IHidxs; eauto.
      erewrite subst_of_indices_commute_qual in IHidxs; eauto.
  Qed.

  Ltac solve_se_soi idxs IHidxs lem :=
    induction idxs; simpl in *;
    [ intros; erewrite lem; eauto
    | intros;
      match goal with
      | [ X : Index |- _ ] => destruct X
      end;
      simpl;
      rewrite IHidxs;
      match goal with
      | [ |- ?F ?A (?F ?B ?C) = _ ] =>
        replace (F A (F B C)) with (subst_ext' A (subst_ext' B C)) by auto
      end;
      rewrite subst_ext'_assoc;
      simpl;
      rewrite subst'_of_comp; auto ].
  
  Lemma subst_ext_subst_of_indices_qual : forall {idxs} {q : Qual},
      subst.subst_indices idxs q =
      subst_ext' (subst'_of (subst_of_indices idxs)) q.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_qual).
  Qed.
  
  Lemma subst_ext_subst_of_indices_type : forall {idxs} {t : Typ},
      subst.subst_indices idxs t =
      subst_ext' (subst'_of (subst_of_indices idxs)) t.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_type).
  Qed.

  Lemma subst_ext_subst_of_indices_types : forall {idxs} {taus : list Typ},
      subst.subst_indices idxs taus =
      subst_ext' (subst'_of (subst_of_indices idxs)) taus.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_types).
  Qed.

  Ltac solve_id_no_effect :=
    rewrite id_eq_var';
    intros;
    match goal with
    | [ |- ?F ?A ?B = _ ] =>
      replace (F A B) with (subst_ext' A B) by auto
    end;
    rewrite subst_ext'_var_e; auto.

  Lemma id_no_effect_on_instruction : forall {e},
      subst.subst'_instruction (debruijn.subst'_of debruijn.id) e = e.
  Proof.
    solve_id_no_effect.
  Qed.
  
  Lemma subst_ext_subst_of_indices_inst : forall {idxs} {e : Instruction},
      subst.subst_indices idxs e =
      subst_ext' (subst'_of (subst_of_indices idxs)) e.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_instruction).
  Qed.

  Lemma id_no_effect_on_local_ctx : forall L,
      subst'_local_ctx (debruijn.subst'_of debruijn.id) L = L.
  Proof.
    solve_id_no_effect.
  Qed.
  
  Lemma subst_ext_subst_of_indices_local_ctx : forall {idxs} {L : Local_Ctx},
      subst.subst_indices idxs L =
      subst_ext' (subst'_of (subst_of_indices idxs)) L.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_local_ctx).
  Qed.

  Lemma id_no_effect_on_function_ctx : forall F,
      subst'_function_ctx (debruijn.subst'_of debruijn.id) F = F.
  Proof.
    solve_id_no_effect.
  Qed.
  
  Lemma subst_ext_subst_of_indices_function_ctx : forall {idxs} {F : Function_Ctx},
      subst.subst_indices idxs F =
      subst_ext' (subst'_of (subst_of_indices idxs)) F.
  Proof.
    solve_se_soi idxs IHidxs (@id_no_effect_on_function_ctx).
  Qed.

  Lemma QualLeq_susbt_indices : forall {idxs F foralls tau1 tau2 tau1' tau2' q1 q2},
      InstIndsValid F (FunT foralls (Arrow tau1 tau2)) idxs ->
      InstInds (FunT foralls (Arrow tau1 tau2)) idxs =
      Some (FunT [] (Arrow tau1' tau2')) ->
      Function_Ctx_empty F ->
      QualLeq
        (qual (add_constraints empty_Function_Ctx foralls))
        q1 q2
      = Some true ->
      QualLeq
        []
        (subst.subst_indices idxs q1)
        (subst.subst_indices idxs q2)
      = Some true.
  Proof.
    intros.
    unfold Function_Ctx_empty in *.
    destructAll.
    match goal with | [ H : qual _ = [] |- _ ] => rewrite <-H end.
    match goal with
    | [ |- context[qual ?F] ] =>
      replace F with (add_constraints F []) by auto
    end.
    repeat rewrite subst_ext_subst_of_indices_qual.
    match goal with
    | [ |- context[subst_ext' ?F] ] =>
      replace F with (subst.under_kindvars' [] F) by auto
    end.
    eapply QualLeq_susbt_indices_gen; eauto;
      [ constructor; auto | ].
    match goal with
    | [ H : QualLeq ?A _ _ = Some _
        |- QualLeq ?B _ _ = Some _ ] =>
      replace B with A; auto
    end.
    apply qual_add_constraints_inv.
    simpl; auto.
  Qed.

  Lemma add_local_effects_length : forall tl L,
      length (add_local_effects L tl) = length L.
  Proof.
    induction tl; simpl in *; auto.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    intros.
    match goal with
    | [ |- context[get_localtype ?N ?L] ] =>
      remember (get_localtype N L) as obj;
      generalize (eq_sym Heqobj); case obj; intros
    end.
    - match goal with
      | [ X : _ * _ |- _ ] => destruct X
      end.
      rewrite IHtl.
      unfold set_localtype.
      rewrite <-nth_upd_length; auto.
    - rewrite IHtl; auto.
  Qed.

  Lemma HasTypeInstruction_length_eq : forall {S C F L es atyp L'},
      HasTypeInstruction S C F L es atyp L' ->
      length L = length L'.
  Proof.
    apply
      (HasTypeInstruction_mind'
         (fun S C F L es atyp L' => length L = length L')
         (fun S cl ft => True)
         (fun S C f ex ft => True)
         (fun S maybe_ret i locvis locsz es taus => True)).
    all: auto.
    all: intros.
    all:
      match goal with
      | [ |- length _ = length ?L ] => try unfold L
      end.
    all: unfold set_localtype.
    all: try rewrite <-nth_upd_length; auto.
    all: try rewrite add_local_effects_length; auto.
    all:
      try match goal with
          | [ H : LCEffEqual _ _ _ |- _ ] =>
            apply LCEffEqual_length in H
          end.
    all: eapply eq_trans; eauto.
    eapply eq_trans; [ | eauto ].
    apply eq_sym; auto.
  Qed.

  Lemma HasTypeInstruction_eq_sizes : forall {S C F L es tau1 tau2 L' L1},
      Forall2
        (fun '(t1, sz0) '(t2, sz1) =>
           t1 = t2 /\
           SizeLeq [] sz0 sz1 = Some true /\
           SizeLeq [] sz1 sz0 = Some true)
        L L1 ->
      HasTypeInstruction
        S C F L es (Arrow tau1 tau2) L' ->
      HasTypeInstruction
        S C F L1 es (Arrow tau1 tau2) L'.
  Proof.
    intros.
    eapply ChangeBegLocalTyp; [ | eauto ].
    unfold LCEffEqual.
    apply forall2_nth_error_inv; [ | eapply Forall2_length; eauto ].
    intros.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.
    intros; simpl in *.
    destruct_prs.
    destructAll.
    split; auto.
    split; eapply SizeLeq_Bigger_Ctx; eauto; constructor.
  Qed.

  Lemma HasTypeInstruction_subst_loc : forall {S C F L es tau1 tau2 L' loc},
      HasTypeInstruction S C (update_location_ctx ((location F) + 1) F) L es (Arrow tau1 tau2) L' ->
      LocValid (location F) loc ->
      Function_Ctx_empty
        (subst'_function_ctx
           (subst'_of (ext subst.SLoc loc id))
           F) ->
      HasTypeInstruction
        S C
        (subst'_function_ctx
           (subst'_of (ext subst.SLoc loc id))
           F)
        (subst'_local_ctx
           (subst'_of (ext subst.SLoc loc id))
           L)
        (map
           (subst.subst'_instruction
              (subst'_of (ext subst.SLoc loc id)))
           es)
        (Arrow
           (map
              (subst.subst'_type
                 (subst'_of (ext subst.SLoc loc id)))
              tau1)
           (map
              (subst.subst'_type
                 (subst'_of (ext subst.SLoc loc id)))
              tau2))
        (subst'_local_ctx
           (subst'_of (ext subst.SLoc loc id))
           L').
  Proof.
    intros.
    replace (ext subst.SLoc loc id) with (subst_of_indices [LocI loc]).
    2:{
      simpl.
      rewrite comp_right_id; auto.
    }
    replace (subst'_function_ctx (subst'_of (subst_of_indices [LocI loc])) F) with (subst.subst_indices [LocI loc] F).
    2:{
      rewrite subst_ext_subst_of_indices_function_ctx; auto.
    }
    replace (subst'_local_ctx (subst'_of (subst_of_indices [LocI loc])) L) with (subst.subst_indices [LocI loc] L).
    2:{
      rewrite subst_ext_subst_of_indices_local_ctx; auto.
    }
    replace (subst'_local_ctx (subst'_of (subst_of_indices [LocI loc])) L') with (subst.subst_indices [LocI loc] L').
    2:{
      rewrite subst_ext_subst_of_indices_local_ctx; auto.
    }
    replace (subst.subst'_instruction (subst'_of (subst_of_indices [LocI loc]))) with (@subst.subst_indices _ _ _ _ subst.BindExtInstruction [LocI loc]).
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      rewrite subst_ext_subst_of_indices_inst; auto.
    }
    replace (subst.subst'_type (subst'_of (subst_of_indices [LocI loc]))) with (@subst.subst_indices _ _ _ _ subst.BindExtTyp [LocI loc]).
    2:{
      apply FunctionalExtensionality.functional_extensionality.
      intros.
      rewrite subst_ext_subst_of_indices_type; auto.
    }
    repeat rewrite <-subst_indices_types.
    eapply HasTypeInstruction_subst_indices; eauto.
    - assert (H' : InstIndValid (subst.subst_indices [LocI loc] F) (FunT [LOC] (Arrow tau1 tau2)) (LocI loc)); eauto.
      -- econstructor.
         simpl; auto.
      -- econstructor.
         --- econstructor; simpl; auto.
         --- simpl.
             eauto.
         --- constructor.
    - simpl.
      destruct F; subst; simpl in *.
      rewrite Nat.add_1_r; auto.
    - match goal with
      | [ |- context[LOC :: ?X] ] =>
        replace X with (@nil KindVar) by auto
      end.      
      destruct F; subst; simpl in *.
      unfold simple_fields_eq; simpl.
      unfold Function_Ctx_empty in *.
      destructAll.
      simpl in *.
      repeat match goal with
             | [ H : map _ _ = [] |- _ ] =>
               apply map_eq_nil in H
             end.
      subst; simpl.
      auto.
    - constructor; constructor.
  Qed.

  Lemma simple_fields_eq_update_ret : forall {kvs F maybe_ret1 maybe_ret2},
      simple_fields_eq
        (update_ret_ctx maybe_ret1
                        (add_constraints F kvs))
        (add_constraints
           (update_ret_ctx maybe_ret2 F)
           kvs).
  Proof.
    intros.
    destruct F; subst; simpl in *.
    repeat rewrite add_constraints_to_ks_of_kvs; simpl.
    constructor; auto.
  Qed.

  Lemma Preservation_reduce_simpl S M F L es es' arrt L' addr :
    nth_error (InstTyp S) addr = Some M ->
    Function_Ctx_empty F ->
    forallb well_formed_Inst es = true->

    HasTypeInstruction S M F L es arrt L' ->

    Reduce_simple addr es es' ->


    HasTypeInstruction S M F L es' arrt L'.
  Proof.
    intros Hmod Hempty Hall Htyp Hred. inv Hred; destruct arrt; eauto.
    - assert (Hn : 0 = 0) by congruence. revert L0 Hn Htyp Hall. generalize 0 at 2.
      intros.
      assert (Hn' : n = 0) by eauto.
      revert L0 Hn Htyp Hall. generalize 0.
      intros.
      destruct L0; try lia.
      simpl in *.
      show_tlvs Htyp.
      eapply HasTypeInstruction_local_is_tl in Htyp.
      destruct Htyp.
      eapply ChangeEndLocalTyp; [ | eapply TrapTyp ]; eauto.
      eapply LocalCtxValid_LCEffEqual; eauto.
      apply LCEffEqual_sym; eauto.

    - show_tlvs Htyp.
      eapply Unreachable_HasTypeInstruction in Htyp.
      destructAll.
      eapply ChangeEndLocalTyp; [ | eapply TrapTyp ]; eauto.
      eapply LocalCtxValid_LCEffEqual; eauto.
      apply LCEffEqual_sym; eauto.
      
    - (* Nop *)
      show_tlvs Htyp.
      eapply Nop_HasTypeInstruction in Htyp. destructAll.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply HasTypeInstruction_empty_list; eauto.
      
    - (* Drop *)
      eapply composition_typing_double in Htyp. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Drop] _ _ |- _ ] =>
        show_tlvs H; eapply Drop_HasTypeInstruction in H; destructAll
      end.

      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_inj_tail in H; destructAll
      end.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply HasTypeInstruction_empty_list.

      eapply SplitStoreTypings_Empty'. eassumption.
      constructor; eauto.

      eapply HasTypeValue_Unrestricted_LinEmpty.
      -- eassumption.
      -- eassumption.
      -- unfold Function_Ctx_empty in *; destructAll; auto.
      -- auto.
      -- apply Forall_app; split; auto.

    - (* Select 0 *)
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [?A; ?B; ?C; ?D] _ _ |- _ ] =>
        replace [A; B; C; D] with
            (([A; B] ++ [C]) ++ [D]) in H by reflexivity
      end.
      eapply composition_typing_single in Htyp. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ _) _ _ |- _ ] =>
        show_tlvs H; eapply composition_typing_single in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [_; _] _ _ |- _ ] =>
        eapply composition_typing_double in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Select] _ _ |- _ ] =>
        show_tlvs H; eapply Select_HasTypeInstruction in H; destructAll
      end.
      repeat match goal with
             | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
               show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
             end.
      match goal with
      | [ H : _ ++ _ ++ _ = _ |- _ ] =>
        do 3 rewrite <- app_assoc in H;
        simpl in H;
        do 2 rewrite app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_; _; _] = [_; _; _] |- _ ] => inv H
      end.
      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; auto)
      end.

      eapply FrameTyp. reflexivity.

      eapply Forall_trivial. intros [? ?]. now eapply QualLeq_Top.
      now eapply QualLeq_Top.

      do 4 ltac:(eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ]).
      eapply ValTyp.
      eapply HasTypeValue_Function_Ctx.
      5:{ match goal with
          | [ H : SplitStoreTypings [?A; ?B] ?C,
              H' : SplitStoreTypings [?C; ?D] ?E,
              H'' : SplitStoreTypings [?E; ?F] ?G |- _ ] =>
            eapply SplitStoreTypings_comm in H;
            edestruct SplitStoreTypings_assoc; [ eapply H | | ]
          end.
          
          eassumption. destructAll.

          edestruct SplitStoreTypings_assoc.
          match goal with
          | [ H : SplitStoreTypings [?A; ?B] ?C,
              H' : SplitStoreTypings [?B; ?D] ?E,
              H'' : SplitStoreTypings [?A; ?E] ?F |- _ ] =>
            eapply H''
          end.
          eassumption. destructAll.

          eapply HasTypeValue_StoreTyping_eq. eassumption.
          eapply SplitStoreTypings_Empty_eq.

          eapply SplitStoreTypings_comm. eassumption.

          eapply SplitStoreTypings_Empty'.
          eassumption.
          econstructor; eauto.
          eapply SplitStoreTypings_Empty'.
          eassumption.
          econstructor; eauto.

          eapply HasTypeValue_Unrestricted_LinEmpty; try eassumption.
          - unfold Function_Ctx_empty in *; destructAll; auto.
          - econstructor.
            match goal with
            | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
              inv H
            end.
            eassumption.
            now constructor. }

      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; subst; simpl in *; eapply LocalCtxValid_Function_Ctx; eauto.
      solve_forall_apps.

    - (* Select <> 0 *)
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [?A; ?B; ?C; ?D] _ _ |- _ ] =>
        replace [A; B; C; D] with
            (([A; B] ++ [C]) ++ [D]) in H by reflexivity
      end.
      eapply composition_typing_single in Htyp. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ (_ ++ _) _ _ |- _ ] =>
        eapply composition_typing_single in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [_; _] _ _ |- _ ] =>
        eapply composition_typing_double in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Select] _ _ |- _ ] =>
        show_tlvs H; eapply Select_HasTypeInstruction in H; destructAll
      end.
      repeat match goal with
             | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
               show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
             end.
      match goal with
      | [ H : _ ++ _ ++ _ = _ |- _ ] =>
        do 3 rewrite <- app_assoc in H;
        simpl in H;
        do 2 rewrite app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_; _; _] = [_; _; _] |- _ ] => inv H
      end.
      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; reflexivity)
      end.

      eapply FrameTyp. reflexivity.

      eapply Forall_trivial. intros [? ?]. now eapply QualLeq_Top.
      now eapply QualLeq_Top.

      do 4 ltac:(eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ]).
      eapply ValTyp.
      eapply HasTypeValue_Function_Ctx.
      5: {edestruct SplitStoreTypings_assoc.
          match goal with
          | [ H : SplitStoreTypings [?A; ?B] ?C,
              H' : SplitStoreTypings [?C; ?D] ?E,
              H'' : SplitStoreTypings [?E; ?F] ?G |- _ ] =>
            eapply H
          end.
          eassumption. destructAll.

          edestruct SplitStoreTypings_assoc.
          match goal with
          | [ H : SplitStoreTypings [?A; ?B] ?C,
              H' : SplitStoreTypings [?B; ?D] ?E,
              H'' : SplitStoreTypings [?A; ?E] ?F |- _ ] =>
            eapply H''
          end.
          eassumption. destructAll.

          eapply HasTypeValue_StoreTyping_eq. eassumption.
          eapply SplitStoreTypings_Empty_eq.

          eapply SplitStoreTypings_comm. eassumption.

          eapply SplitStoreTypings_Empty'.
          eassumption.
          econstructor; eauto.
          eapply SplitStoreTypings_Empty'.
          eassumption.
          econstructor; eauto.

          eapply HasTypeValue_Unrestricted_LinEmpty; try eassumption.
          - unfold Function_Ctx_empty in *; destructAll; auto.
          - econstructor.
            match goal with
            | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
              inv H
            end.
            eassumption.
            now constructor. }
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; subst; simpl in *; eapply LocalCtxValid_Function_Ctx; eauto.
      solve_forall_apps.

    - (* Block *)
      eapply composition_typing_single_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Block _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply Block_HasTypeInstruction in H1; destructAll
      end.
      simpl in *.
      rewrite set_set_hd in *.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
      end.
      edestruct Values_HasTypeInstruction with (H := Hv). eassumption. destructAll.

      match goal with
      | [ H : _ ++ ?A = _ ++ ?B |- _ ] =>
        assert (Hlen : length A = length B)
      end.
      { match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] =>
          eapply Forall3_length in H; rewrite to_values_len in H
        end.
        destructAll. congruence. }

      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_eq_len in H; [| eassumption ]
      end.
      destructAll; subst.

      rewrite app_assoc.
      match goal with
      | [ |- HasTypeInstruction _ _ _ _ _ (Arrow ?A _) _ ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; reflexivity)
      end.
      eapply FrameTyp.

      4:{ simpl.
          eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
          eapply LabelTyp. reflexivity. simpl.

          eapply HasTypeInstruction_app.

          2:{ eapply ChangeEndLocalTyp; [ eauto | ]. eassumption. }

          simpl in *.
          eapply ChangeEndLocalTyp; [ eauto | ].
          eapply HasTypeInstruction_Values.

          2: eapply Forall3_monotonic; [| eassumption ].
          eauto.

          simpl.
          intros st v1 tau1 Hhtv.
          eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity.

          eapply LocalCtxValid_LCEffEqual.
          2:{ apply LCEffEqual_sym; eauto. }
          eapply LocalCtxValid_Function_Ctx; eauto.

          eassumption.

          eapply HasTypeInstruction_empty_list.
          1:{ eapply is_empty_LinTyp. }
          1:{ eapply LocalCtxValid_LCEffEqual; [ | eauto ].
              eapply LocalCtxValid_Function_Ctx; eauto. }

          solve_forall_apps.
          eapply Forall_TypeValid_Function_Ctx; eauto. }

      simpl. reflexivity.

      eapply Forall_app. split; [ | eassumption ].
      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      solve_forall_apps.
      eapply Forall_TypeValid_Function_Ctx; eauto.

    - (* Loop *)
      eapply composition_typing_single_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Loop _ _] _ _ |- _ ] =>
        show_tlvs H; eapply Loop_HasTypeInstruction in H; destructAll
      end.
      simpl in *.
      rewrite set_set_hd in *.

      match goal with
      | [ H' : values ?VS |- _ ] =>
        edestruct Values_HasTypeInstruction with (H := H')
      end.
      eassumption. destructAll.

      match goal with
      | [ H : _ ++ ?A = _ ++ ?B |- _ ] =>
        assert (Hlen : length A = length B);
        [ | eapply app_eq_len in H; [ | eassumption ] ]
      end.
      { match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] =>
          eapply Forall3_length in H; rewrite to_values_len in H
        end.
        destructAll. congruence. }

      destructAll; subst.

      rewrite app_assoc.
      match goal with
      | [ |- HasTypeInstruction _ _ _ _ _ (Arrow ?A _) _ ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; reflexivity)
      end.

      simpl in *.
      match goal with
      | [ H : Arrow _ _ = Arrow _ _ |- _ ] =>
        inversion H; subst
      end.


      eapply FrameTyp.


      4:{ simpl.
          eapply ChangeEndLocalTyp; [ simpl; eauto | ].
          eapply ChangeEndLocalTyp; [ simpl; apply LCEffEqual_sym; eauto | ].
          eapply LabelTyp. reflexivity. simpl.

          eapply HasTypeInstruction_app.

          eapply HasTypeInstruction_Values.
          2:{ eapply Forall3_monotonic; [| eassumption ].

              simpl. intros st v1 tau1 H1.
              eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity. }

          eassumption.

          eapply LocalCtxValid_LCEffEqual.
          2:{ apply LCEffEqual_sym; eauto. }
          eapply LocalCtxValid_Function_Ctx; eauto.
          
          eapply ChangeBegLocalTyp; [ | eapply ChangeEndLocalTyp; [ | eauto ] ]; simpl; eauto.
          apply LCEffEqual_sym; auto.
          eassumption.
          simpl.
          eapply LoopTyp. simpl.
          eapply HasTypeInstruction_StoreTyping_eq.
          eapply ChangeBegLocalTyp; [ | eapply ChangeEndLocalTyp; eauto ].
          simpl; auto.

          match goal with
          | [ H : HasTypeInstruction _ _ _ _ ?ES _ _,
              H' : context[Loop _ ?ES] |- _ ] =>
            eapply HasTypeInstruction_surface in H
          end.
          2:{ rewrite forallb_app in Hall. eapply andb_prop in Hall. destructAll.
              match goal with
              | [ H : forallb _ [Loop _ _] = _ |- _ ] => inv H
              end.
              rewrite Bool.andb_true_r. congruence. }

          { match goal with
            | [ H : SplitStoreTypings [?A; ?B] ?C |- _ ] =>
              destruct A; destruct C; destruct B; simpl in *; inv H
            end.
            simpl in *.
            match goal with
            | [ H : length _ = length ?X, H' : values ?X |- _ ] =>
              destruct H
            end.
            match goal with
            | [ H : Forall _ [_; _] |- _ ] => inv H
            end.
            destructAll.
            match goal with
            | [ H : Forall _ [_] |- _ ] => inv H
            end.
            destructAll.
            simpl in *. subst.
            split; eauto. split; eauto. simpl.
            eapply eq_map_is_empty.
            simpl in *; auto. } }

      simpl. reflexivity.

      eapply Forall_app. split; [ | eassumption ].
      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      solve_forall_apps.
      eapply Forall_TypeValid_Function_Ctx; eauto.

    - (* ITE true *)
      eapply composition_typing_double_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ITE _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply ITE_HasTypeInstruction in H; destructAll
      end.
      simpl in *. destructAll.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
        rewrite app_assoc in H; eapply app_inj_tail in H
      end.
      destructAll.
      rewrite !app_assoc.
      match goal with
      | [ |- HasTypeInstruction _ _ _ _ _ (Arrow (?A ++ _) _) _ ] =>
        eapply FrameTyp with (taus := A)
      end.

      reflexivity.

      eapply Forall_app. split; [ | eassumption ].
      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply BlockTyp. simpl.
      rewrite set_set_hd in *.
      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].

      eapply HasTypeInstruction_StoreTyping_eq; eauto.
      eapply SplitStoreTypings_Empty_eq; eauto.
      match goal with
      | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
        inv H; auto
      end.

      simpl.
      eapply LCEffEqual_trans; eauto.

      solve_forall_apps.
      eapply Forall_TypeValid_Function_Ctx; eauto.

    - (* ITE false *)
      eapply composition_typing_double_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ITE _ _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply ITE_HasTypeInstruction in H; destructAll
      end.
      simpl in *. destructAll.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
        rewrite app_assoc in H; eapply app_inj_tail in H
      end.
      destructAll.
      rewrite !app_assoc.
      match goal with
      | [ |- HasTypeInstruction _ _ _ _ _ (Arrow (?A ++ _) _) _ ] =>
        eapply FrameTyp with (taus := A)
      end.

      reflexivity.

      eapply Forall_app. split; [ | eassumption ].
      prepare_Forall. eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      eapply QualLeq_Trans. eassumption.
      rewrite get_set_hd in *. eassumption.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply BlockTyp. simpl.
      rewrite set_set_hd in *.

      match goal with
      | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
        inv H; auto
      end.
      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply HasTypeInstruction_StoreTyping_eq. eassumption.
      eapply SplitStoreTypings_Empty_eq. eassumption. eassumption.
      eapply LCEffEqual_trans; eauto.
      solve_forall_apps.
      eapply Forall_TypeValid_Function_Ctx; eauto.

    - (* Label vs *)
      show_tlvs Htyp.
      eapply Label_HasTypeInstruction in Htyp. destructAll.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; reflexivity)
      end.
      eapply FrameTyp. simpl. reflexivity. eassumption. eassumption.
      simpl.
      edestruct Values_HasTypeInstruction with (H := H). eassumption. destructAll.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply HasTypeInstruction_Values.

      eassumption.
      eapply Forall3_monotonic; [ | eassumption ].
      simpl. intros st v tau Hv. eapply HasTypeValue_Function_Ctx; [ | | | | eassumption ]; reflexivity.

      eapply LocalCtxValid_Function_Ctx; eauto.
      solve_forall_apps.

    - (* Label Trap *)
      show_tlvs Htyp.
      eapply Label_HasTypeInstruction in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Trap] _ _ |- _ ] =>
        show_tlvs H; eapply HasTypeInstruction_local_is_tl in H; destruct H
      end.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply TrapTyp.

      eapply LocalCtxValid_Function_Ctx; eauto.
      solve_forall_apps.
      solve_forall_apps.
      eapply LocalCtxValid_LCEffEqual.
      2:{ apply LCEffEqual_sym; eauto. }
      eapply LocalCtxValid_Function_Ctx; eauto.

    - (* Label vs *)
      show_tlvs Htyp.
      eapply Label_HasTypeInstruction in Htyp. destructAll.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        replace A with (A ++ []) at 1 by (rewrite app_nil_r; reflexivity)
      end.
      eapply FrameTyp. simpl. reflexivity. eassumption. eassumption.
      simpl.

      eapply HasTypeInstruction_app.

      2:{ eassumption. }
      2:{ eapply SplitStoreTypings_EmptyHeapTyping_r. }

      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ _ (Arrow [] _) _
          |- HasTypeInstruction _ _ _ _ _ _ ?L ] =>
        show_tlvs H; eapply Context_HasTypeInstruction_Br with (L0 := L) in H; try eassumption
      end.

      + destructAll.
        match goal with
        | [ H : HasTypeInstruction _ _ _ _ ?VS _ _,
            H' : values ?VS |- _ ] =>
          eapply Values_HasTypeInstruction in H; destructAll
        end.
        eapply ChangeEndLocalTyp; [ | eapply HasTypeInstruction_Values ].
        simpl in *; apply LCEffEqual_sym; eauto.
        eauto. simpl.

        eapply Forall3_monotonic; [ | eassumption ].
        simpl. intros. eapply HasTypeValue_Function_Ctx; [ | | | | eassumption ]; reflexivity.
        eapply LocalCtxValid_Function_Ctx; eauto.

      +  rewrite Bool.andb_true_r in Hall.
         eapply andb_prop in Hall; destruct Hall.
         match goal with
         | [ H : (_ && _)%bool = true |- _ ] =>
           eapply andb_prop in H; destruct H
         end.
         eapply well_formews_Inst_list_is_well_formed_in_context.
         eassumption.
      + rewrite Bool.andb_true_r in Hall.
        eapply andb_prop in Hall; destruct Hall.
        match goal with
        | [ H : (_ && _)%bool = true |- _ ] =>
          eapply andb_prop in H; destruct H
        end.
        eassumption.
      + lia.

      + simpl. rewrite Nat.sub_diag. simpl. reflexivity.

      + simpl. reflexivity.
        
      + unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto.

      + solve_forall_apps.

    - (* Br_if, z = 0*)

      eapply composition_typing_double_strong in Htyp; destruct F; simpl in *.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Br_if _] _ _ |- _ ] =>
        show_tlvs H; eapply Br_if_HasTypeInstruction in H
      end.
      simpl in *; destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      
      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
        rewrite app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply HasTypeInstruction_empty_list.
      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] => inv H
      end.
      simpl in *.
      eapply SplitHeapTypings_Empty'. eassumption.
      match goal with
      | [ H : Forall _ [_; _] |- _ ] => inv H
      end.
      constructor; eauto.
      match goal with
      | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
        inv H; auto
      end.

      eapply LocalCtxValid_Function_Ctx; eauto.
      solve_forall_apps.
      all: eapply Forall_TypeValid_Function_Ctx; eauto.

    - (* Br_if, z <> 0 *)

      eapply composition_typing_double_strong in Htyp; destruct F; simpl in *.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Br_if _] _ _ |- _ ] =>
        show_tlvs H; eapply Br_if_HasTypeInstruction in H
      end.
      simpl in *; destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
        rewrite app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.
      rewrite get_set_hd in *.
      rewrite app_assoc. eapply FrameTyp.
      simpl. reflexivity.

      eapply Forall_app. split; [| eassumption ].
      prepare_Forall.
      eapply QualLeq_Trans; eassumption.

      simpl. eapply QualLeq_Trans; eassumption.

      match goal with
      | [ |- context[Arrow ?A ?A] ] =>
        replace x8 with ([] ++ x8) by reflexivity
      end.

      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      match goal with
      | [ |- HasTypeInstruction _ _ _ ?L _ _ ?L ] =>
        replace (L) with (add_local_effects L []) at 2 by (simpl; congruence)
      end.

      eapply BrTyp.

      + match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] => inv H
        end.
        match goal with
        | [ H : Forall _ [_; _] |- _ ] => simpl in H
        end.
        eapply SplitHeapTypings_Empty'. eassumption.
        match goal with
        | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
          inv H; auto
        end.
        constructor; [ | constructor ]; eauto.

      + simpl. eassumption.

      + simpl. now constructor.

      + simpl. rewrite set_set_hd in *. eauto.

      + simpl in *.
        eapply LocalCtxValid_LCEffEqual; [ | eauto ].
        eapply LocalCtxValid_Function_Ctx; eauto.

      + simpl in *.
        solve_forall_apps.
        eapply Forall_TypeValid_Function_Ctx; eauto.

      + simpl in *.
        solve_forall_apps.
        eapply Forall_TypeValid_Function_Ctx; eauto.

      + simpl in *.
        eapply LocalCtxValid_LCEffEqual; [ | eauto ].
        eapply LocalCtxValid_Function_Ctx; eauto.

      + solve_forall_apps.
        eapply Forall_TypeValid_Function_Ctx; eauto.  

    - (* Br_table *)

      eapply composition_typing_double_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Br_table _ _] _ _ |- _ ] =>
        show_tlvs H; eapply Br_table_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ _ ++ [_] |- _ ] =>
        rewrite !app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow _ (?A ++ _)] ] =>
        rewrite <- (app_assoc A)
      end.

      rewrite get_set_hd in *.

      eapply FrameTyp. reflexivity.

      eapply Forall_app. split; [| eassumption ].

      prepare_Forall.
      eapply QualLeq_Trans; eassumption.
      eapply QualLeq_Trans; eassumption.

      simpl.
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].

      match goal with
      | [ H : LCEffEqual ?C ?L1 ?L2,
          H' : context[add_local_effects ?L1 ?TL] |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : LCEffEqual C (add_local_effects L1 TL) (add_local_effects L2 TL))
      end.
      { apply LCEffEqual_add_local_effects; auto. }
      
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply BrTyp.

      + match goal with
        | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
          inv H
        end.
        match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] => inv H
        end.
        eapply SplitHeapTypings_Empty'. eassumption.
        now constructor; eauto.

      + simpl in *.
        match goal with
        | [ H : Forall _ (_ ++ [_]) |- _ ] =>
          eapply Forall_forall in H; [ eapply H | ]
        end.
        eapply in_or_app. left.
        eapply nth_error_In. eassumption.

      + eapply Forall_impl; [| eassumption ].
        intros []; simpl; eauto.

      + simpl. rewrite set_set_hd in *.
        intros.
        match goal with
        | [ H : forall _, _ <= _ -> _ |- _ ] => eapply H
        end.
        
        simpl. rewrite list_max_app.
        eapply le_trans. eassumption.
        eapply le_trans; [| eapply OrdersEx.Nat_as_OT.le_max_l ].

        eapply list_max_In.

        eapply nth_error_In. eassumption.

      + eapply LocalCtxValid_LCEffEqual; [ | eauto ].
        eapply LocalCtxValid_Function_Ctx; eauto.

      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.

      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.

      + eapply LocalCtxValid_LCEffEqual; [ | eauto ].
        eapply LocalCtxValid_LCEffEqual; [ | apply LCEffEqual_sym ].
        2:{
          match goal with
          | [ H : LCEffEqual _ ?A (add_local_effects _ _),
              H' : LCEffEqual _ ?A _ |- LCEffEqual _ ?A _ ] =>
            exact H'
          end.
        }
        eapply LocalCtxValid_Function_Ctx; eauto.

      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.     

    - (* Br_table *)

      eapply composition_typing_double_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Br_table _ _] _ _ |- _ ] =>
        show_tlvs H; eapply Br_table_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ _ ++ [_] |- _ ] =>
        rewrite !app_assoc in H;
        eapply app_eq_len in H; [ | reflexivity ]
      end.
      destructAll.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow _ (?A ++ _)] ] =>
        rewrite <- (app_assoc A)
      end.

      rewrite get_set_hd in *.

      eapply FrameTyp. reflexivity.

      eapply Forall_app. split; [| eassumption ].

      prepare_Forall.
      eapply QualLeq_Trans; eassumption.
      eapply QualLeq_Trans; eassumption.

      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      simpl.
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].

      match goal with
      | [ H : LCEffEqual ?C ?L1 ?L2,
          H' : context[add_local_effects ?L1 ?TL] |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : LCEffEqual C (add_local_effects L1 TL) (add_local_effects L2 TL))
      end.
      { apply LCEffEqual_add_local_effects; auto. }
      
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply BrTyp.

      + match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] => inv H
        end. simpl in *.
        eapply SplitHeapTypings_Empty'. eassumption.
        match goal with
        | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] =>
          inv H
        end.
        now constructor; eauto.

      + simpl.  simpl in *.
        solve_forall_apps.

      + eapply Forall_impl; [| eassumption ].
        intros []; simpl; eauto.

      + simpl. rewrite set_set_hd in *.
        intros.
        match goal with
        | [ H : forall _, _ <= _ -> _ |- _ ] => eapply H
        end.
        simpl. rewrite list_max_app.
        simpl. lia.

      + solve_lcvs.
      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.
      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.
      + solve_lcvs.
      + solve_forall_apps; eapply Forall_TypeValid_Function_Ctx; eauto.
        

    - (* Tee_local *)

      eapply composition_typing_double_strong in Htyp. destructAll.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Tee_local _] _ _ |- _ ] =>
        show_tlvs H; eapply Tee_local_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      eapply FrameTyp. reflexivity. eassumption. eassumption.
      simpl in *.

      match goal with
      | [ |- context[[?A; ?B; ?C]] ] =>
        replace [A; B; C] with (([A] ++ [B]) ++ [C]) by reflexivity
      end.

      eapply ConsTyp. eassumption.


      2:{ match goal with
          | [ |- context[Arrow _ ?A] ] =>
            rewrite <- (app_nil_r A)
          end.
          eapply FrameTyp. reflexivity. simpl.
          eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
          eapply QualLeq_Top. simpl.
          eapply ChangeEndLocalTyp; [ eauto | ].
          eapply SetlocalTyp. eassumption.
          eassumption. eassumption. eassumption. eassumption.
          solve_lcvs.
          solve_tvs.
          solve_tvs.
      }

      rewrite <- app_assoc. simpl.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.

      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      match goal with
      | [ |- context[[?A; ?A]] ] =>
        replace [A; A] with ([A] ++ [A]) by reflexivity
      end.
      eapply ConsTyp.

      2:{ eapply ValTyp. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity. solve_lcvs. }

      2:{ match goal with
          | [ |- context[Arrow [?T] _] ] =>
            rewrite <- (app_nil_r [T]) at 1;
            replace [T; T] with ([T] ++ [T]) by reflexivity
          end.

          eapply FrameTyp. reflexivity. simpl.

          eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
          eapply QualLeq_Top.

          simpl.
          eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
          eapply ValTyp. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity. solve_lcvs. solve_tvs. }

      match goal with
      | [ H : HasTypeValue _ _ _ _ |- _ ] =>
        eapply HasTypeValue_Unrestricted_LinEmpty in H; [| eassumption | ]
      end.
      -- eapply SplitStoreTypings_EmptyHeapTyping.
         match goal with
         | [ |- HasEmptyLinTyping ?S ] => destruct S
         end.
         unfold HasEmptyLinTyping. eassumption.
      -- unfold Function_Ctx_empty in *; simpl in *; destructAll; auto.
      -- solve_tvs.
      -- solve_tvs.

    - (* CoderefI *)
      show_tlvs Htyp.
      eapply CoderefI_HasTypeInstruction in Htyp. destructAll.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply ValTyp. eapply HasTypeValue_Function_Ctx.
      5:{ econstructor; try eassumption. reflexivity. econstructor. }
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      destruct F; reflexivity.
      solve_lcvs; destruct F; reflexivity.
      solve_tvs.

    - (* Inst *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeValue _ _ (Coderef _ _ _) _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Inst _] _ _ |- _ ] =>
        show_tlvs H; eapply Inst_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.

      rewrite app_assoc.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.
      simpl.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp. eapply HasTypeValue_Function_Ctx.
      5:{ match goal with
          | [ H : SplitStoreTypings _ _ |- _ ] => inv H
          end.
          match goal with
          | [ H : Forall _ [_; _] |- _ ] => inv H
          end.
          match goal with
          | [ H : [_] = [_] |- _ ] => inv H
          end. destructAll. simpl in *. eapply CoderefTyp.

          eapply SplitHeapTypings_Empty'.
          eassumption. now constructor; eauto.

          match goal with
          | [ H : ?A = _ |- context[?A] ] => rewrite H
          end.
          eassumption.
          eassumption.

          unfold InstInds in *. rewrite fold_left_app.
          match goal with
          | [ H : ?A = _ |- context[?A] ] => rewrite H
          end.
          eassumption.

          eapply InstIndsValid_app; try eassumption.
          eapply InstIndsValid_Function_Ctx_strong; [ eassumption | | | | ];
            simpl; eapply Hempty.
          eapply InstInds_coderef_TypeValid; eauto.
      }
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      solve_lcvs.
      solve_tvs.

    - (* RecFold *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [RecFold _] _ _ |- _ ] =>
        show_tlvs H; eapply RecFold_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : TypeValid _ (QualT (Rec _ _) _) |- _ ] => inv H
      end.

      rewrite app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      match goal with
      | [ H : [_] = [_] |- _ ] => inversion H; subst
      end.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp. eapply HasTypeValue_Function_Ctx.
      5:{ eapply RecTyp; try eassumption.
          - econstructor; eauto.
          - simpl. eapply HasTypeValue_StoreTyping_eq.
            repeat match goal with
                   | [ H : context[subst.subst'_qual (subst'_of (ext subst.SPretype _ _)) _] |- _ ] =>
                     rewrite subst_pretype_in_qual in H
                   end.
            eassumption.
            eapply SplitStoreTypings_Empty_eq.
            eapply SplitStoreTypings_comm. eassumption.
            eassumption.
          }

      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      solve_lcvs.
      solve_tvs.

    - (* RecUnfold *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeValue _ _ (Fold _) _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [RecUnfold] _ _ |- _ ] =>
        show_tlvs H; eapply RecUnfold_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll; inv H
      end.

      rewrite app_assoc.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp. simpl.

      eapply HasTypeValue_StoreTyping_eq.

      rewrite subst_pretype_in_qual.
      eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity.

      eapply SplitStoreTypings_Empty_eq.
      eapply SplitStoreTypings_comm. eassumption.
      eassumption.

      solve_lcvs.
      solve_tvs.

    - (* Group *)
      eapply composition_typing_single_strong in Htyp.
      destruct F; simpl in *; destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Group _ _] _ _ |- _ ] =>
        show_tlvs H; eapply Group_HasTypeInstruction in H; destructAll
      end.

      match goal with
      | [ H'' : HasTypeInstruction _ _ _ _ ?VS _ _, H' : values ?VS |- _ ] =>
        show_tlvs H''; eapply Values_HasTypeInstruction with (H := H') in H''
      end.
      
      destructAll.
      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_eq_len in H
      end.
      2:{
        match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] =>
          eapply Forall3_length in H
        end.
        destructAll.
        rewrite to_values_len in *.
        congruence.
      }

      destructAll.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      rewrite app_assoc.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp.

      eapply HasTypeValue_StoreTyping_eq.

      eapply HasTypeValue_Function_Ctx.
      5:{ eapply ProdTyp. 2:{ eassumption. } eassumption. eassumption. }
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.

      eapply SplitStoreTypings_Empty_eq. eapply SplitStoreTypings_comm.
      eassumption. eassumption.

      solve_lcvs.
      solve_tvs.

    - (* Unroup *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Ungroup] _ _ |- _ ] =>
        show_tlvs H; eapply Ungroup_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeValue _ _ (term.Prod _) _ |- _ ] => inv H
      end.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      rewrite app_assoc.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      assert (Hval : values (map Val vs)).
      { eapply values_Val. }

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply HasTypeInstruction_Values.

      2:{ simpl. rewrite to_values_Val.

          eapply Forall3_monotonic; [| eassumption ].
          simpl. intros st1 v1 t1 Hv.
          eapply HasTypeValue_Function_Ctx; [ | | | | eassumption ]; reflexivity. }

      match goal with
      | [ H : SplitStoreTypings [_; _] _ |- _ ] =>
        eapply SplitStoreTypings_comm in H;
        eapply SplitStoreTypings_Empty_eq in H; [| eassumption ]
      end.

      eapply SplitStoreTyping_eq. eassumption.
      eassumption.

      solve_lcvs.
      solve_tvs.

    - (* CapSplit *)

      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [CapSplit] _ _ |- _ ] =>
        show_tlvs H; eapply CapSplit_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      rewrite app_assoc.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.
      replace [Val Cap; Val Own] with ([Val Cap] ++ [Val Own])
        by reflexivity.
      eapply ConsTyp.

      3:{ match goal with
          | [ |- context[Arrow _ [?A; ?B]] ] =>
            replace [A; B] with ([A] ++ [B]) by reflexivity
          end.

          eapply FrameTyp. reflexivity. simpl.

          eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
          eapply QualLeq_Top.

          simpl. eapply ValTyp. econstructor. eassumption.
          eapply TOwnValid; simpl.
          eapply QualConstValid; eauto.
          eapply QualLeq_Refl.
          match goal with
          | [ H : HasTypeValue _ _ Cap _ |- _ ] =>
            inv H; eapply LocPValid; eauto
          end.
          match goal with
          | [ H : [_] = [_] |- _ ] => inv H; eauto
          end.

          solve_lcvs.
          constructor; solve_tvs.
          match goal with
          | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] => inv H
          end.
          econstructor; eauto.
          match goal with
          | [ H : HeapTypeValid ?F ?HT |- HeapTypeValid {| label := ?LAB; ret := ?RET; qual := ?Q; size := ?SZ; type := ?T; location := ?L; linear := _ |} ?HT ] =>
            replace LAB with (typing.label F) by auto;
            replace RET with (typing.ret F) by auto;
            replace Q with (typing.qual F) by auto;
            replace SZ with (typing.size F) by auto;
            replace T with (typing.type F) by auto;
            replace L with (typing.location F) by auto
          end.
          eapply HeapTypeValid_linear; eauto.
      }

      eassumption.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp. simpl.
      match goal with
      | [ H : HasTypeValue _ _ Cap _ |- _ ] => inv H
      end.
      
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.
      econstructor; eauto.
      eapply TypeValid_Function_Ctx.

      match goal with
      | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] => inv H
      end.
      econstructor; eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      solve_lcvs.
      solve_tvs.

    - (* CapJoin *)
      replace ([Val Cap; Val Own; CapJoin]) with
          ([Val Cap; Val Own] ++ [CapJoin]) in Htyp by reflexivity.

      eapply composition_typing in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [_; _] _ _ |- _ ] =>
        eapply composition_typing_double_strong in H
      end.
      simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val Cap] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [CapJoin] _ _ |- _ ] =>
        show_tlvs H; eapply CapJoin_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val Own] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : _ ++ (_ ++ _) ++ _ = ?A ++ [?B; ?C] |- _ ] =>
        rewrite app_assoc in H;
        replace (A ++ [B; C]) with ((A ++ [B]) ++ [C]) in H
      end.
      2:{ rewrite <- app_assoc. reflexivity. }

      match goal with
      | [ H : (_ ++ _ ++ _) ++ _ = (_ ++ _) ++ _ |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.

      match goal with
      | [ H : _ ++ _ ++ [_] = _ ++ [_] |- _ ] =>
        rewrite app_assoc in H;
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.

      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.
      replace [Val Cap; Val Own] with ([Val Cap] ++ [Val Own])
        by reflexivity.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp.
      match goal with
      | [ H : HasTypeValue _ _ Cap _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeValue _ _ Own _ |- _ ] => inv H
      end.
      simpl in *.

      econstructor.

      + match goal with
        | [ H : SplitStoreTypings [?A; ?B] ?C,
            H' : SplitStoreTypings [?C; ?D] ?S |- context[?S] ] =>
          eapply SplitStoreTypings_comm in H;
          eapply SplitStoreTypings_Empty_eq in H; inv H; destructAll;
          eapply SplitStoreTypings_comm in H';
          eapply SplitStoreTypings_Empty_eq in H'; inv H'; destructAll
        end.
        eapply eq_map_trans; [| eassumption ].
        eapply eq_map_sym.
        eapply eq_map_trans; try eassumption.
        all: eassumption.

      + eassumption.

      + eapply TypeValid_Function_Ctx.
        match goal with
        | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] => inv H
        end.
        econstructor; eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

      + solve_lcvs.
      + solve_tvs.

    - (* RefDemote *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [RefDemote] _ _ |- _ ] =>
        show_tlvs H; eapply RefDemote_HasTypeInstruction in H; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp.

      match goal with
      | [ H : HasTypeValue _ _ (Ref _) _ |- _ ] => inv H
      end.
      2:{
        match goal with
        | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] => inv H
        end.
        exfalso; eapply QualLeq_Const_False; eauto.
        unfold Function_Ctx_empty in *; simpl in *; destructAll; auto.
      }
      
      econstructor.

      eapply SplitStoreTypings_Empty'. eassumption.
      now constructor; eauto.

      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] => inv H; simpl in *
      end.
      match goal with
      | [ H : Forall _ [_; _] |- _ ] => inv H; destructAll
      end.
      congruence.

      simpl in *. eassumption.

      eapply TypeValid_Function_Ctx.
      match goal with
      | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] => inv H
      end.
      econstructor; eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      solve_lcvs.
      solve_tvs.
      
    - (* RefSplit *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [RefSplit] _ _ |- _ ] =>
        show_tlvs H; eapply RefSplit_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      match goal with
      | [ |- context[[Val ?A; Val ?B]] ] =>
        replace [Val A; Val B] with ([Val A] ++ [Val B]) by reflexivity
      end.

      eapply ConsTyp. eassumption.

      2:{ match goal with
          | [ |- context[Arrow _ [?A; ?B]] ] =>
            replace [A; B] with ([A] ++ [B]) by reflexivity
          end.

          eapply FrameTyp. reflexivity. simpl.

          eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
          eapply QualLeq_Top.

          simpl. eapply ValTyp.
          match goal with
          | [ H : HasTypeValue _ _ (Ref _) _ |- _ ] => inv H
          end.
          econstructor.
          eassumption.

          econstructor. eapply QualConstValid; eauto. eapply LocPValid; eauto.

          econstructor. eassumption.
          econstructor. eapply QualConstValid; eauto. eapply LocPValid; eauto.
          solve_lcvs.

          solve_forall_apps.
          match goal with
          | [ H : Forall _ [_; _] |- _ ] => inv H
          end.
          solve_tvs.
      }

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp. simpl in *.
      match goal with
      | [ H : HasTypeValue _ _ (Ref _) _ |- _ ] => inv H
      end.
      + simpl in *. inv Hempty. destructAll. simpl in *. subst.
        match goal with
        | [ H : QualLeq [] (QualConst Linear) _ = Some _ |- _ ] =>
          eapply QualLeq_Top_Const in H; subst
        end.
        match goal with
        | [ H : QualLeq [] (QualConst Linear) _ = Some _ |- _ ] =>
          eapply QualLeq_Top_Const in H; congruence
        end.
      + econstructor; try eassumption.
        match goal with
        | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] =>
          inv H
        end.
        eapply TypeValid_Function_Ctx. econstructor; eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      + solve_lcvs.
      + solve_tvs.

    - (* RefJoin *)

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [?A; ?B; ?C] _ _ |- _ ] =>
        replace [A; B; C] with ([A; B] ++ [C]) in H by reflexivity
      end.

      eapply composition_typing in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [_; _] _ _ |- _ ] =>
        eapply composition_typing_double_strong in H
      end.      
      simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val (PtrV _)] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [RefJoin] _ _ |- _ ] =>
        show_tlvs H; eapply RefJoin_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val Cap] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.

      match goal with
      | [ H : _ ++ _ ++ [_] = ?A ++ [?B; ?C] |- _ ] =>
        rewrite app_assoc in H;
        replace (A ++ [B; C]) with ((A ++ [B]) ++ [C]) in H
      end.
      2:{ rewrite <- app_assoc. reflexivity.  }

      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.

      match goal with
      | [ H : _ ++ _ ++ _ = _ ++ _ |- _ ] =>
        rewrite app_assoc in H;
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      
      repeat match goal with
             | [ H : [_] = [_] |- _ ] => inv H
             end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl in *.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp.
      simpl in *.
      match goal with
      | [ H : HasTypeValue _ _ (PtrV _) _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeValue _ _ Cap _ |- _ ] => inv H
      end.

      eapply RefTypLin.

      eapply eq_map_trans; [|  eassumption ].
      eapply eq_map_sym.
      eapply eq_map_trans.

      eapply SplitStoreTypings_Empty_eq.
      eapply SplitStoreTypings_comm. eassumption. eassumption.

      eapply SplitStoreTypings_Empty_eq.
      eapply SplitStoreTypings_comm. eassumption. eassumption.


      eassumption.

      match goal with
      | [ H : TypeValid _ (QualT (CapT _ _ _) _) |- _ ] => inv H
      end.
      eapply TypeValid_Function_Ctx. econstructor; eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.

      solve_lcvs.
      solve_tvs.

    - (* Mempack *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [MemPack _] _ _ |- _ ] =>
        show_tlvs H; eapply MemPack_HasTypeInstruction in H; simpl in *; destructAll
      end.
      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      (* eapply Forall_app. split. eassumption. *)


      (* eapply Forall_impl; [ | eassumption ].  *)
      (* intros [? ?] Hyp. eapply QualLeq_Trans; eassumption.       *)

      (* eapply QualLeq_Trans; eassumption. *)

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ValTyp.
      econstructor.
      simpl; auto.

      match goal with
      | [ |- context[ExLoc ?A] ] => destruct A
      end.
      econstructor; eauto.
      match goal with
      | [ H : TypeValid _ (QualT _ ?Q) |- _ _ ?Q ] => inv H; eauto
      end.
      match goal with
      | [ |- _ _ ?Q1 ?Q2 = _ ] => enough (Q1 = Q2)
      end.
      subst. eapply QualLeq_Refl.
      { simpl in *.
        match goal with
        | [ H : QualT _ _ = QualT _ _ |- _ ] => inv H
        end.
        rewrite subst_loc_in_qual.
        congruence.
      }
      match goal with
      | [ H : subst.subst'_type _ _ = QualT _ _ |- _ ] => inv H
      end.
      simpl in *.
      simpl.

      eapply TypeValid_subst with (F := {|
                                         label := label;
                                         ret := ret;
                                         qual := qual;
                                         size := size;
                                         type := type;
                                         location := location;
                                         linear := set_hd (QualConst Linear) linear
                                       |}) (l := l).
      simpl.

      simpl in *.
      now eapply TypeValid_Function_Ctx; try eassumption; try reflexivity.


      eapply HasTypeValue_StoreTyping_eq.
      eapply HasTypeValue_Function_Ctx.
      5:{ simpl in *.
          match goal with
          | [ H : ?A = _ |- context[?A] ] => rewrite H
          end.
          eassumption. }
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.

      eapply SplitStoreTypings_Empty_eq.
      eapply SplitStoreTypings_comm. eassumption. eassumption.

      solve_lcvs.
      solve_tvs.

    - (* MemUnpack *) assert (Htyp' := Htyp).
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [MemUnpack _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply MemUnpack_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
        rewrite app_assoc in H; eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.

      rewrite get_set_hd in *.

      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_app. split. 2:{ eassumption. }

      prepare_Forall. eapply QualLeq_Trans; eassumption.

      eapply QualLeq_Trans; eassumption.

      simpl.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeBegLocalTyp; [ apply LCEffEqual_sym; eauto | ].
      eapply BlockTyp. simpl.

      match goal with
      | [ H : HasTypeValue _ _ (Mempack _ _) _ |- _ ] => inv H
      end.
      simpl in *. rewrite set_set_hd in *.

      match goal with
      | [ |- context[Val ?A :: ?B] ] =>
        replace (Val A :: B) with ([Val A] ++ B) by reflexivity
      end.

      eapply HasTypeInstruction_app.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <- (app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      eapply ValTyp.
      eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; reflexivity.
      simpl.
      simpl in *.
      solve_lcvs.
      solve_tvs.
      4: solve_tvs.
      2: eassumption.

      unfold Function_Ctx_empty in *.
      simpl in *.
      destructAll; simpl in *.
      specialize (HasTypeInstruction_TypeAndLocalValid Htyp').
      unfold LocalCtxValid.
      intros; destructAll; simpl in *.
      repeat match goal with
             | [ H : Forall _ (_ ++ _) |- _ ] =>
               rewrite Forall_app in H; destructAll
             end.

      match goal with
      | [ |- HasTypeInstruction _ _ ?F ?L _ (Arrow (?TAU1 ++ [?A ?B ?TAU]) ?TAU2) ?LP ] =>
        replace F with
            (subst'_function_ctx
               (subst'_of (ext subst.SLoc loc id))
               (subst'_function_ctx
                  (subst'_of (weak subst.SLoc))
                  F));
        [ replace LP with
              (subst'_local_ctx
                 (subst'_of (ext subst.SLoc loc id))
                 (subst'_local_ctx
                    (subst'_of (weak subst.SLoc))
                    LP));
          [ replace (TAU1 ++ [A B TAU]) with
                (map
                   (A B)
                   (map
                      (subst.subst'_type
                         (subst'_of (weak subst.SLoc)))
                      TAU1
                      ++ [TAU]));            
            [ replace TAU2 with
                  (map
                     (A B)
                     (map
                        (subst.subst'_type
                           (subst'_of (weak subst.SLoc)))
                        TAU2)) at 2;
              [ replace L with
                    (subst'_local_ctx
                       (subst'_of (ext subst.SLoc loc id))
                       (subst'_local_ctx
                          (subst'_of (weak subst.SLoc))
                          L)) at 1 | ] | ] | ] | ]
      end.
      + eapply HasTypeInstruction_subst_loc.
        * unfold subst'_function_ctx in *.
          simpl in *.
          unfold subst.subst'_types in *.
          eapply ChangeEndLocalTyp; [ | eauto ].
          simpl.
          apply LCEffEqual_sym.
          apply LCEffEqual_subst_weak_loc; auto.
        * simpl; auto.
        * unfold subst'_function_ctx; simpl.
          constructor; auto.
      + apply local_ctx_debruijn_subst_weak.
      + rewrite map_map.
        rewrite <-map_id.
        apply map_ext_in.
        intros.
        apply type_debruijn_subst_weak.
      + rewrite map_app.
        simpl in *.
        match goal with
        | [ |- ?A ++ _ = ?B ++ _ ] => replace B with A at 2; auto
        end.
        rewrite map_map.
        rewrite <-map_id.
        apply map_ext_in.
        intros.
        apply type_debruijn_subst_weak.
      + apply local_ctx_debruijn_subst_weak.
      + apply function_ctx_debruijn_subst_weak.
      + simpl.
        eapply LCEffEqual_trans; eauto.

    - (* StructMalloc *)
      eapply composition_typing in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H'' : values ?VS,
          H' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        show_tlvs H'; eapply Values_HasTypeInstruction with (H := H'') in H'
      end.
      destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [StructMalloc _ _] _ _ |- _ ] =>
        show_tlvs H; eapply StructMalloc_HasTypeInstruction in H; simpl in *; destructAll
      end.
      
      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] => eapply app_eq_len in H
      end.
      2:{ match goal with
          | [ H : Forall3 _ _ _ _ |- _ ] =>
            eapply Forall3_length in H
          end.
          destructAll.
          match goal with
          | [ H : Forall2 _ _ _ |- _ ] =>
            eapply Forall2_length in H
          end.
          rewrite to_values_len in *. congruence. }

      destructAll.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.
      rewrite StructType_subst.
      edestruct size_val_leq_list.
      eassumption. eassumption. eassumption. eassumption.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      match goal with
      | [ H : size_closed _ |- _ ] =>
        eapply (MallocTyp _ _ _ _ _ _ _ _ H)
      end.
      2 : { econstructor 2.
            - rewrite combine_split; [ eauto | ].
              eapply Forall2_length; eauto.
            - match goal with
              | [ |- context[to_size (fold_left _ _ ?BASE) _] ] =>
                let H' := fresh "H" in
                let H'' := fresh "H" in
                assert (H' : exists H, N.of_nat 0 = N.of_nat (to_size BASE H));
                [ | destruct H' as [H' H'']; rewrite H'' ]
              end.
              { exists I.
                simpl; auto. }
              eapply fold_size_to_nat_eq_to_size_fold_SizePlus. }
      2 : {simpl. eassumption. }
      econstructor.
      + match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] =>
          eapply SplitStoreTypings_comm in H;
          eapply SplitStoreTypings_Empty_eq in H
        end.
        match goal with
        | [ H : SplitStoreTypings ?A ?B |- _ _ ?C ] =>
          eapply (SplitStoreTyping_eq A B C) in H
        end.
        all: eauto.
      + eapply Forall3_monotonic; [ | eassumption ].
        simpl. intros.
        eapply HasTypeValue_Function_Ctx; [ | | | | eassumption ]; try reflexivity.
      + rewrite combine_split; eauto.
        eapply Forall2_length; eauto.
      + simpl; split; eauto.
      + simpl.
        rewrite combine_split. auto.
        eapply Forall2_length; eauto.
      + solve_lcvs.
      + solve_tvs.
        match goal with
        | [ H : context[RefT _ _ (StructType ?L)]
            |- context[RefT _ _ (StructType ?L2)] ] =>
          replace L2 with L
        end.
        * eapply TypeValid_Function_Ctx; eauto.
        * rewrite subst.map_combine.
          match goal with
          | [ |- combine _ ?A = combine _ ?B ] =>
            replace A with B at 1; auto
          end.
          rewrite <-map_id.
          apply map_ext.
          intros.
          apply loc_weak_no_effect_on_size.
      + solve_tvs.

    - (* VariantMalloc *)
      eapply composition_typing_double_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [VariantMalloc _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply VariantMalloc_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]
      end.
      destructAll.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      simpl.
      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      assert (Hs : size_closed (SizePlus (SizeConst 32) (size_of_value v))).
      { now eauto. }

      rewrite VariantType_subst.
      assert (Hsz : size_closed (SizePlus (SizeConst 32) (size_of_value v))).
      { split; exact I. }
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply MallocTyp with (H := Hsz).
      2 : { simpl. destruct Hsz. constructor. exact I. }
      2 : { simpl. eassumption. }
      simpl. econstructor.
      + eapply Forall_impl.
        2: { eauto. }
        intros.
        simpl in *.
        eapply TypeValid_Function_Ctx; eauto.
      + eauto.
      + match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] =>
          eapply SplitStoreTypings_comm in H;
          eapply SplitStoreTypings_Empty_eq in H
        end.
        eapply HasTypeValue_StoreTyping_eq.
        eapply HasTypeValue_Function_Ctx.
        5:{ eauto. }
        all: eauto.
      + simpl. eassumption.
      + solve_lcvs.
      + solve_tvs.
      + solve_tvs.

    - (* ArrayMalloc *)
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [?A; ?B; ?C] _ _ |- _ ] =>
        replace [A; B; C] with (([A] ++ [B]) ++ [C]) in H
      end.
      2:{ rewrite <- app_assoc. reflexivity. }

      eapply composition_typing_single_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val ?A; Val ?B] _ _ |- _ ] =>
        eapply composition_typing_double_strong in H; simpl in *; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val (NumConst _ _)] _ _,
          H' : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H'; eapply Val_HasTypeInstruction in H'; destructAll;
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ArrayMalloc _] _ _ |- _ ] =>
        show_tlvs H; eapply ArrayMalloc_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ _ ++ _ = ?A ++ [?B; ?C] |- _ ] =>
        rewrite !app_assoc in H;
        replace (A ++ [B; C]) with ((A ++ [B]) ++ [C]) in H
      end.
      2:{ rewrite <- app_assoc. reflexivity. }

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.
      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      match goal with
      | [ H : HasTypeValue _ _ (NumConst _ _) _ |- _ ] => inv H
      end.

      edestruct HasTypeValue_sizeOfType_concrete. eassumption.
      simpl. now eapply Hempty. destructAll.
      replace type with (@nil (Size * Qual * HeapableConstant)) in *.
      2:{ symmetry; eapply Hempty. }

      edestruct size_val_leq_list with (ss := repeat (size_of_value v) j).

      eapply Forall3_repeat. eassumption.
      eassumption. eapply Forall2_repeat.
      simpl. eexists. split. eassumption.
      match goal with
      | [ H : HasTypeValue _ _ _ _ |- _ ] =>
        eapply SizeOfValue_Typecheck_Actual in H; [ | eassumption | | ]
      end.
      2:{ simpl. eapply Hempty. }
      2:{ eassumption. }

      unfold size_of_value.
      match goal with
      | [ H : ?A = _ |- context[?A] ] =>
        rewrite H
      end.
      eapply SizeLeq_leq. eassumption. reflexivity. lia.

      rewrite Forall_forall.
      intros.
      match goal with
      | [ H : In _ (repeat _ _) |- _ ] =>
        apply in_repeat in H
      end.
      subst.
      unfold size_of_value.
      econstructor; eauto.

      assert (Hsz'' : size_closed (SizePlus (SizeConst 32) sz)).
      { simpl. split. exact I. eassumption. }

      rewrite ArrayType_subst.
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply ChangeEndLocalTyp; [ eauto | ].
      eapply MallocTyp with (H := Hsz'').
      2 : { constructor. exact I. }
      2 : { simpl. eassumption. }
      simpl. econstructor.
      + eapply HasType_Valid.
        eapply HasTypeValue_update_linear_ctx_rev.
        simpl; eauto.
      + simpl; auto.
      + match goal with
        | [ H : SplitStoreTypings _ ?A,
            H' : SplitStoreTypings [?A; _] _ |- _ ] =>
          eapply SplitStoreTypings_comm in H';
          eapply SplitStoreTypings_Empty_eq in H'
        end.
        match goal with
        | [ H : SplitStoreTypings _ ?S |- SplitStoreTypings _ ?S2 ] =>
          eapply (SplitStoreTyping_eq _ S S2) in H
        end.
        match goal with
        | [ H : SplitStoreTypings _ _ |- _ ] =>
          eapply SplitStoreTypings_comm in H;
          eapply SplitStoreTypings_Empty_eq in H
        end.
        match goal with
        | [ H : HasTypeValue ?S _ _ _,
            H' : StoreTyping_eq ?S ?S2 |- context[?S2] ] =>
          eapply (SplitStoreTyping_eq _ S S2); eauto;
          eapply HasTypeValue_Unrestricted_LinEmpty in H
        end.
        eapply SplitStoreTypings_repeat.
        match goal with
        | [ |- HasEmptyLinTyping ?S ] => destruct S; eauto
        end.
        simpl. all: eauto.
        unfold Function_Ctx_empty in *.
        simpl in Hempty; destructAll; auto.
      + eapply repeat_length.
      + eapply Forall2_repeat.
        eapply HasTypeValue_Function_Ctx.
        5 : { eauto. }
        eauto.
        eauto.
        eauto.
        eauto.
      + eassumption.
      + solve_lcvs.
      + simpl.
        match goal with
        | [ H : Forall _ (_ ++ [?T]) |- context[?T] ] =>
          apply Forall_app in H; destructAll
        end.
        match goal with
        | [ H : Forall _ [_] |- _ ] => inv H
        end.
        eapply TypeValid_Function_Ctx; eauto.
      + solve_tvs.

    - (* ExistPack *)

      eapply composition_typing_double_strong in Htyp. simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [ExistPack _ _ _] _ _ |- _ ] =>
        show_tlvs H; eapply ExistsPack_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      assert (Hs : size_closed (SizePlus (SizeConst 64) (size_of_value v))).
      { now eauto. }

      rewrite ExistType_subst.
      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply MallocTyp with (H := Hs).

      2 : { constructor. exact I. }
      2 : { destruct F. eassumption. }
      2 : { destruct F. simpl in *.  eassumption. }

      simpl in *.
      rewrite loc_weak_no_effect_on_size in *; auto.
      rewrite loc_weak_no_effect_on_qual in *; auto.
      match goal with
      | [ |- context[QualT (?X ?Y) _] ] =>
        assert (Heq3 : X Y = Y)
      end.
      { eapply weak_loc_no_effect_on_valid_typ_empty_Function_Ctx; eauto.
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *.
        simpl in *; destructAll; auto. }
      match goal with
      | [ |- context[QualT _ (?X ?Y)] ] =>
        assert (Heq4 : X Y = Y)
      end.
      { destruct x12; simpl in *; auto.
        unfold get_var'.
        unfold under'.
        unfold under_ks'.
        simpl.
        unfold get_var'.
        unfold weaks'.
        unfold var.
        simpl.
        unfold plus.
        unfold zero.
        unfold sing.
        simpl.
        repeat rewrite plus_O_n.
        rewrite Nat.sub_0_r; auto. }

      rewrite Heq3, Heq4 in *.

      eapply ExHT.
      + destruct F. simpl in *. eassumption.
      + destruct F. simpl in *. eassumption.
      + destruct F. simpl in *. eassumption.
      + destruct F. unfold heapable in *. simpl in *. eassumption.
      + destruct F. eapply TypeValid_Function_Ctx; try eassumption; try (simpl; reflexivity).
      + destruct F. simpl in *.
        unfold Function_Ctx_empty in Hempty. destructAll. simpl in *. subst.
        unfold subst'_function_ctx. simpl.
        eapply TypeValid_Function_Ctx; try eassumption; try (simpl; reflexivity).

      + destruct F. simpl.
        eapply HasTypeValue_Function_Ctx.
        5:{ match goal with
            | [ H : SplitStoreTypings _ _ |- _ ] =>
              eapply SplitStoreTypings_comm in H;
              eapply SplitStoreTypings_Empty_eq in H
            end.
            eapply HasTypeValue_StoreTyping_eq; eassumption. eassumption. }
        reflexivity. reflexivity. reflexivity. reflexivity.
      + solve_lcvs; destruct F; subst; simpl in *; auto.
      + simpl in *.
        rewrite loc_weak_no_effect_on_size.
        rewrite loc_weak_no_effect_on_qual.
        destruct F; subst; simpl in *.
        replace (under' subst.SPretype (subst'_of (weak subst.SLoc))) with (subst'_of (weak subst.SLoc)).
        * solve_tvs.
        * unfold Subst'.
          apply FunctionalExtensionality.functional_extensionality_dep.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          rewrite under_pretype_subst_eq; auto.
      + destruct F; subst; simpl in *; solve_tvs.

    - (* Qualify *)

      eapply composition_typing_double_strong in Htyp. simpl in *; destructAll.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Val _] _ _ |- _ ] =>
        show_tlvs H; eapply Val_HasTypeInstruction in H; destructAll
      end.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [Qualify _] _ _ |- _ ] =>
        show_tlvs H; eapply Qualify_HasTypeInstruction in H; simpl in *; destructAll
      end.

      match goal with
      | [ H : _ ++ [_] = _ ++ [_] |- _ ] =>
        eapply app_eq_len in H; [| reflexivity ]; destructAll
      end.
      match goal with
      | [ H : [_] = [_] |- _ ] => inv H
      end.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply ValTyp.
      simpl.

      eapply HasTypeValue_QualLt; eauto.

      eapply HasTypeValue_StoreTyping_eq.
      eapply HasTypeValue_Function_Ctx; [| | | | eassumption  ]; destruct F; reflexivity.

      match goal with
      | [ H : SplitStoreTypings _ _ |- _ ] =>
        eapply SplitStoreTypings_comm in H;
        eapply SplitStoreTypings_Empty_eq in H; [ | eassumption ]
      end.
      eassumption.

      destruct F; eassumption.
      destruct F; eassumption.
      destruct F; solve_lcvs.
      destruct F; solve_tvs.

    - (* Local *)
      show_tlvs Htyp.
      eapply Local_HasTypeInstruction in Htyp. destructAll.
      match goal with
      | [ H : HasTypeConf _ _ _ _ _ _ _ |- _ ] => inv H
      end.

      match goal with
      | [ H'' : values ?VS,
          H' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        show_tlvs H'; eapply Values_HasTypeInstruction with (H := H'') in H'
      end.
      destructAll.
      simpl.

      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      eapply ChangeEndLocalTyp; [ destruct F; subst; simpl in *; eauto | ].
      eapply HasTypeInstruction_Values with (H := Hvs).

      2:{ eapply Forall3_monotonic; [ | eassumption ].

          simpl. intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; destruct F; destruct Hempty as [Ha [Hb [Hc Hd]]]; simpl in *; congruence. }

      { match goal with
        | [ H : SplitStoreTypings (?A :: _) _,
            H' : SplitStoreTypings _ ?A |- _ ] =>
          eapply SplitStoreTypings_merge' in H; [| eassumption ]
        end.
        eapply SplitHeapTypings_empty_app.
        eapply SplitStoreTypings_comm'. eassumption.

        unfold F0 in *. simpl in *.
        match goal with
        | [ H : HasTypeLocals _ _ _ _,
            H' : LCEffEqual _ _ ?L,
	        H'' : Forall _ ?L |- _ ] =>
          revert H'' H';
          repeat match goal with
                 | [ H''' : context[L] |- _ ] => clear H'''
                 end;
          revert H L
        end.
        clear. intros Hall L'0 Hloc Hlceq. inv Hall.

        revert L'0 Hloc Hlceq.
        match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] => induction H
        end.

        - constructor.

        - intros.
          unfold LCEffEqual in Hlceq.
          inv Hlceq.
          destruct_prs. simpl in *. inv Hloc.
          constructor; eauto. simpl.
          match goal with
          | [ H : forall _, _ -> _ -> _,
              H' : Forall _ _, H'' : Forall2 _ _ _ |- _ ] =>
            specialize (H _ H' H'')
          end.
          destructAll. destruct t0.

          eapply HasTypeValue_Unrestricted_LinEmpty. eassumption.
          auto.
          simpl; auto.
      }
      destruct F; subst; simpl in *; solve_lcvs.
      solve_tvs.      

    - (* Local - Trap *)
      show_tlvs Htyp.
      eapply Local_HasTypeInstruction in Htyp. destructAll.
      eapply ChangeEndLocalTyp; [ eauto | ].
      match goal with
      | [ |- HasTypeInstruction _ _ _ ?L _ _ _ ] =>
        replace L with (add_local_effects L []) at 2 by (simpl; congruence)
      end.
      eapply TrapTyp; auto.
      
    - (* Local *)
      show_tlvs Htyp.
      eapply Local_HasTypeInstruction in Htyp. destructAll.
      match goal with
      | [ H : HasTypeConf _ _ _ _ _ _ _ |- _ ] => inv H
      end.
      clear H.
      inv Hall. simpl in *. destructAll.

      unfold F0 in *.
      match goal with
      | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] =>
        show_tlvs H; eapply Context_HasTypeInstruction_Ret in H; try eassumption; try (now simpl; eauto)
      end.
      2:{ eapply well_formews_Inst_list_is_well_formed_in_context.
          match goal with
          | [ H : (_ && _)%bool = true |- _ ] =>
            rewrite Bool.andb_true_r in H;
            eapply andb_prop in H
          end.
          destructAll.
          eassumption. }
      2:{ match goal with
          | [ H : (_ && _)%bool = true |- _ ] =>
            rewrite Bool.andb_true_r in H;
            eapply andb_prop in H
          end.
          destructAll.
          eassumption. }

      simpl in *. destructAll.

      match goal with
      | [ H' : HasTypeInstruction _ _ _ _ ?VS _ _ |- _ ] =>
        show_tlvs H'; eapply Values_HasTypeInstruction in H'
      end.
      destructAll.
      simpl in *.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp.  reflexivity.

      eapply Forall_trivial.
      intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      eapply ChangeEndLocalTyp; [ | eapply HasTypeInstruction_Values ].
      1:{
        destruct F; subst; simpl in *.
        unfold Function_Ctx_empty in *; destructAll; simpl in *; destructAll; subst.
        eauto.
      }
      
      2:{ eapply Forall3_monotonic; [| eassumption ].
          simpl. intros. eapply HasTypeValue_Function_Ctx; [| | | | eassumption ]; destruct F; destruct Hempty as [Ha [Hb [Hc Hd]]]; simpl in *; congruence. }

      { simpl in *.
        match goal with
        | [ H : Forall3 _ ?L1 ?L2 ?L3 |- _ ] =>
          let H0 := fresh "H" in
          assert (H0 :
                    Forall3
                      (fun (S' : StoreTyping) (v : Value) tau =>
                         HasTypeValue S' empty_Function_Ctx v tau)
                      L1 L2 L3)
        end.
        { eapply Forall3_monotonic; eauto.
          intros.
          simpl in *.
          eapply HasTypeValue_empty_function_ctx_rev; [ eauto | ].
          unfold Function_Ctx_empty in *.
          simpl in *; destructAll; auto. }

        (* eapply Forall3_HasTypeValue_Unrestricted_LinEmpty' in H8; [| eassumption ]. *)
        (* eapply Forall_split in H9; eauto. *)
        (* eapply Forall3_HasTypeValue_Unrestricted_LinEmpty in H13. ; [| eassumption ]. *)

        match goal with
        | [ H : SplitStoreTypings (?A :: ?B) _ |- _ ] =>
          replace (A :: B) with ([A] ++ B) in H by reflexivity;
          eapply SplitStoreTypings_comm' in H;
          eapply SplitStoreTyping_app in H; destructAll
        end.
        eapply SplitStoreTyping_eq. eassumption.
        eapply SplitStoreTypings_Empty_eq. eassumption.
        eapply SplitStoreTypings_Empty'; eauto.
        match goal with
        | [ H : HasTypeLocals _ _ _ _ |- _ ] => inv H
        end.
        eapply Forall3_HasTypeValue_Unrestricted_LinEmpty'; eauto. }
      destruct F; subst; simpl in *; solve_lcvs.
      solve_tvs.

    - (* CallAdm *)

      eapply composition_typing_single_strong in Htyp.
      destruct F; simpl in *. destructAll.

      match goal with
      | [ H' : HasTypeInstruction _ _ _ _ (map Val ?VS) _ _ |- _ ] =>
        show_tlvs H'; eapply Values_HasTypeInstruction with (H := values_Val VS) in H'
      end.
      destructAll.

      match goal with
      | [ H : HasTypeInstruction _ _ _ _ [CallAdm _ _] _ _ |- _ ] =>
        show_tlvs H; eapply CallAdm_HasTypeInstruction in H; simpl in *; destructAll
      end.
      match goal with
      | [ H : HasTypeClosure _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HasTypeFunc _ _ _ _ _ |- _ ] => inv H
      end.

      unfold chi0 in *. simpl in *.

      Ltac use_InstInds_subst_indices :=
        match goal with
        | [ H' : InstIndsValid ?F _ _,
            H'' : InstInds _ _ = Some _ |- _ ] =>
          let H := fresh "H" in
          assert (H : Function_Ctx_empty F);
          [ unfold Function_Ctx_empty in *; destructAll;
            simpl in *; subst; auto
          | specialize (InstInds_subst_indices H H' H'') ]
        end.

      match goal with
      | [ H : _ ++ ?A = _ ++ ?B |- _ ] =>
        assert (Hlen : length A = length B)
      end.
      { use_InstInds_subst_indices.
        intros; destructAll.
        simpl.
        unfold subst.subst'_types.
        rewrite map_length.
        match goal with
        | [ H : Forall3 _ _ _ _ |- _ ] =>
          eapply Forall3_length in H; destructAll
        end.
        rewrite to_values_len, map_length in *. congruence. }

      match goal with
      | [ H : _ ++ _ = _ ++ _ |- _ ] =>
        eapply app_eq_len in H; [| eassumption ]
      end.
      destructAll.

      rewrite !app_assoc.
      match goal with
      | [ |- context[Arrow ?A _] ] =>
        rewrite <-(app_nil_r A) at 1
      end.
      eapply FrameTyp. reflexivity. simpl.

      eapply Forall_trivial. intros [? ?]. eapply QualLeq_Top.
      eapply QualLeq_Top.

      simpl.

      econstructor. eapply LCEffEqual_refl.

      use_InstInds_subst_indices.
      intros; destructAll.
      simpl.
      unfold subst.subst'_types.

      rewrite to_values_Val in *.

      match goal with
      | [ H : Forall3 _ _ _ ?L3
          |- context[to_sizes (subst_in_size _ ?L) _ ++ _] ] =>
        let H' := fresh "H" in
        assert (H' : length L3 = length L)
      end.
      { match goal with
        | [ H : Forall2 _ _ ?L |- _ = length ?L ] =>
          specialize (Forall2_length _ _ _ H);
          let H' := fresh "H" in intro H'; rewrite <-H'
        end.
        match goal with
        | [ H : Forall3 _ _ ?L2 ?L3,
            H' : length ?LP = length ?L2
            |- length ?L3 = length ?LP ] =>
          rewrite H'
        end.
        apply eq_sym.
        eapply proj2.
        eapply Forall3_length; eauto. }

      { simpl.
        eapply ChangeEndLocalTyp; [ eauto | ].
        eapply ChangeEndLocalTyp; [ eauto | ].
        eapply LocalTyp; eauto.
        rewrite map_length; auto.
        eapply ConfTypFull with
          (L := combine (subst.subst'_types (subst'_of (subst_of_indices zs1)) ts1) (map SizeConst (to_sizes (subst_in_size zs1 sz1) H')) ++ map (fun s : Size => (QualT Unit Unrestricted, s)) (map SizeConst (to_sizes (subst_in_size zs1 szs) H)))
          (Ss := x8 ++ map (fun _ => empty_LinTyp S) szs).
        + left. reflexivity.
        + match goal with
          | [ H : nth_error ?L ?IDX = Some _
              |- nth_error ?L2 ?IDX = Some _ ] =>
            replace L2 with L; eauto
          end.
          solve_inst_or_unr_typ_eq.
        + match goal with
          | [ H : SplitStoreTypings [_; _] _ |- _ ] =>
            eapply SplitStoreTypings_comm in H;
            eapply SplitStoreTypings_merge in H
          end.
          2:{ eapply SplitStoreTypings_Singl. }
          2:{ eassumption. }
          match goal with
          | [ |- context[map _ ?L] ] => generalize L
          end.
          let x := fresh "x" in intro x; induction x.
          * simpl in *.
            rewrite app_nil_r.
            eauto.
          * simpl in *.
            match goal with
            | [ |- context[?A :: map ?F ?B] ] =>
              replace (A :: map F B) with ([A] ++ map F B) by auto
            end.
            rewrite app_comm_cons.
            eapply SplitStoreTypings_permut.
            1:{
              apply Permutation.Permutation_app; [ eauto | ].
              apply Permutation.Permutation_app_comm.
            }
            rewrite app_assoc.
            match goal with
            | [ |- _ _ ?S ] =>
              specialize (SplitStoreTypings_EmptyHeapTyping_r S)
            end.
            intros.
            eapply SplitStoreTypings_trans_gen; eauto.
            
        + constructor. simpl in *.
          eapply Forall3_app.

          * match goal with
            | [ |- context[combine ?L1 ?L2] ] =>
              let H := fresh "H" in
              assert (H : length L1 = length L2)
            end.
            { rewrite map_length.
              rewrite length_to_sizes.
              rewrite length_subst_in_size; auto. }
            
            rewrite Forall3_forall.
            split.
            2:{
              rewrite combine_length.
              match goal with
              | [ H : ?A = ?B |- context[Init.Nat.min ?A ?B] ] =>
                rewrite <-H
              end.
              rewrite Nat.min_id.
              match goal with
              | [ H : Forall3 _ _ _ _ |- _ ] =>
                eapply Forall3_length in H
              end.
              destructAll; split; auto.
            }
            intros.
            match goal with
            | [ X : _ * _ |- _ ] => destruct X
            end.
            match goal with
            | [ H : nth_error (combine _ _) _ = Some _ |- _ ] =>
              apply nth_error_combine in H
            end.
            destructAll.
            match goal with
            | [ H : Forall3 _ ?L1 ?L2 ?L3,
                H' : nth_error ?L1 _ = Some _,
                H'' : nth_error ?L2 _ = Some _,
                H''' : nth_error ?L3 _ = Some _ |- _ ] =>
              rewrite Forall3_forall in H;
              destruct H as [H];
              specialize (H _ _ _ _ H' H'' H''')
            end.
            eapply HasTypeValue_empty_function_ctx_rev; [ eauto | ].
            unfold Function_Ctx_empty in *.
            simpl in *.
            auto.
          * clear.
            rewrite Forall3_forall.
            split.
            2:{
              repeat rewrite map_length.
              rewrite length_to_sizes.
              rewrite length_subst_in_size.
              auto.
            }
            intros.
            repeat match goal with
                   | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
                     apply nth_error_map_inv in H
                   end.
            destructAll.
            constructor.
            ** apply is_empty_LinTyp.
            ** constructor.
               econstructor; eauto.

        + simpl. unfold F, F_cnstr in *. simpl in *.
          simpl.
          assert (Heq : split (combine (subst.subst'_types (subst'_of (subst_of_indices zs1)) ts1) (map (fun v : Value => SizeConst (size_val v)) vs)) = ((subst.subst'_types (subst'_of (subst_of_indices zs1)) ts1), (map (fun v : Value => SizeConst (size_val v)) vs))).
          { rewrite combine_split. reflexivity.
            rewrite map_length.
            match goal with
            | [ H : Forall3 _ _ _ _ |- _ ] =>
              eapply Forall3_length in H
            end.
            destructAll. eauto. }

          assert (Heq' :
                   split
                     (combine (subst.subst'_types (subst'_of (subst_of_indices zs1)) ts1) (map SizeConst (to_sizes (subst_in_size zs1 sz1) H')) ++
                              map (fun s : Size => (QualT Unit Unrestricted, s))
                              (map SizeConst (to_sizes (subst_in_size zs1 szs) H))) =
                     ((subst.subst'_types (subst'_of (subst_of_indices zs1)) ts1) ++ repeat (QualT Unit Unrestricted) (length szs), (map SizeConst (to_sizes (subst_in_size zs1 sz1) H')) ++ (map SizeConst (to_sizes (subst_in_size zs1 szs) H)))).
          { apply split_app.
            - apply split_combine.
              rewrite map_length.
              rewrite length_to_sizes.
              rewrite length_subst_in_size; auto.
            - match goal with
              | [ |- _ = (repeat _ (length ?L1), ?L2) ] =>
                replace (length L1) with (length L2)
              end.
              2:{
                rewrite map_length.
                rewrite length_to_sizes.
                rewrite length_subst_in_size; auto.
              }
              apply split_map_const_arg1; auto. }
          
          rewrite Heq'. simpl.

          rewrite map_app. reflexivity.

        + unfold F_cnstr in *. unfold F, F_cnstr0, L0 in *.

          match goal with
          | [ H : HasTypeInstruction ?S ?C _ ?L ?ES (Arrow ?TAU1 ?TAU2) _,
              H' : InstIndsValid _ (FunT ?KVS _) ?IDXS
              |- HasTypeInstruction ?S ?C _ ?LP ?ESP (Arrow ?TAU1P ?TAU2P) _ ] =>
            replace TAU1P with (subst.subst_indices IDXS TAU1);
            [ replace TAU2P with (subst.subst_indices IDXS TAU2) at 2 | ]
          end.
          * eapply HasTypeInstruction_eq_sizes.
            2:{
              eapply HasTypeInstruction_subst_indices; eauto.
              - eapply InstIndsValid_Function_Ctx_stronger; [ | | | | eauto ].
                all: unfold update_ret_ctx.
                all: simpl.
                all: unfold Function_Ctx_empty in *; destructAll; auto.
              - unfold empty_Function_Ctx; constructor; auto.
              - use_InstInds_subst_indices.
                intros; destructAll.
                unfold subst.under_kindvars'.
                match goal with
                | [ |- context[map (subst.subst'_type ?F) ?TS] ] =>
                  replace (map (subst.subst'_type F) TS) with (subst_ext' F TS) by auto
                end.
                rewrite <-subst_ext_subst_of_indices_types.
                match goal with
                | [ |- context[Some (subst.subst_indices ?IDXS ?T)] ] =>
                  replace (Some (subst.subst_indices IDXS T)) with (option_map (subst.subst_indices IDXS) (Some T)) by auto
                end.
                apply InstFunctionCtxInds_update_ret_ctx.
                eapply InstInds_to_empty_InstFunctionCtxInds; eauto.
              - apply simple_fields_eq_update_ret.
              - match goal with
                | [ H : FunTypeValid _ _ |- _ ] =>
                  inv H
                end.
                eapply KindVarsValid_empty_ctx; eauto.
            }

            match goal with
            | [ |- context[subst.subst_indices _ (_ ++ ?L2)] ] =>
              rewrite (subst_indices_types_sizes_app (l2:=L2))
            end.
            unfold update_ret_ctx.
            simpl.
            apply Forall2_app.
            all: eapply (Forall2_split (P1:=(fun t1 t2 => t1 = t2)) (P2:=(fun sz0 sz1 => SizeLeq [] sz0 sz1 = Some true /\ SizeLeq [] sz1 sz0 = Some true))).
            1,6: intros.
            1-2:
              match goal with
              | [ X : _ * _ |- _ ] => destruct X
              end.
            1-2: intro.
            1-2:
              match goal with
              | [ X : _ * _ |- _ ] => destruct X
              end.
            1-2: auto.
            ** rewrite subst_indices_types_sizes_combine.
               rewrite split_combine; eauto.
               repeat rewrite map_length; auto.
            ** rewrite split_combine; eauto.
               rewrite map_length.
               rewrite length_to_sizes.
               rewrite length_subst_in_size; auto.
            ** use_InstInds_subst_indices.
               intros; destructAll; auto.
               unfold subst.under_kindvars'.
               rewrite <-subst_ext_subst_of_indices_types.
               rewrite subst_indices_types.
               apply forall2_nth_error_inv; auto.
               intros.
               match goal with
               | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                 rewrite H in H'; inversion H'; subst
               end.
               auto.
            ** match goal with
               | [ |- _ _ (map _ ?L) _ ] =>
                 match goal with
                 | [ |- context[subst_in_size _ ?L2] ] =>
                   replace L with L2
                 end
               end.
               2:{
                 apply Forall2_eq.
                 apply forall2_nth_error_inv.
                 2:{
                   eapply eq_trans; [ apply eq_sym | ].
                   all: eapply Forall2_length; eauto.
                 }
                 intros.
                 match goal with
                 | [ H : Forall2 _ ?L ?L1,
                     H' : Forall2 _ ?L ?L2,
                     H'' : nth_error ?L1 ?IDX = Some _,
                     H''' : nth_error ?L2 ?IDX = Some _ |- _ ] =>
                   let H0 := fresh "H" in
                   assert (H0 : exists y, nth_error L IDX = Some y)
                 end.
                 { apply nth_error_some_exists.
                   match goal with
                   | [ H : length ?A = length ?B,
                       H' : nth_error ?B _ = Some _
                       |- _ < length ?A ] =>
                     rewrite H
                   end.
                   eapply nth_error_Some_length; eauto. }
                 destructAll.
                 match goal with
                 | [ H : Forall2 _ ?L ?L1,
                     H' : Forall2 _ ?L ?L2,
                     H'' : nth_error ?L ?IDX = Some _,
                     H''' : nth_error ?L1 ?IDX = Some _,
                     H'''' : nth_error ?L2 ?IDX = Some _ |- _ ] =>
                   specialize (forall2_nth_error _ _ _ _ _ _ H H'' H''');
                   specialize (forall2_nth_error _ _ _ _ _ _ H' H'' H'''')
                 end.
                 intros; simpl in *.
                 unfold F_cnstr1 in *.
                 match goal with
                 | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                   rewrite H in H'; inversion H'; subst
                 end.
                 auto.
               }
               match goal with
               | [ |- context[to_sizes _ ?H] ] => revert H
               end.
               rewrite subst_in_size_eq_map.
               intros.
               apply closed_sizes_eq.
            ** rewrite subst_indices_types_sizes.
               rewrite map_map.
               rewrite subst_indices_type.
               rewrite subst_indices_Unit.
               rewrite subst_indices_Unrestricted.
               eapply split_map_const_arg1_gen; eauto.
            ** eapply split_map_const_arg1; eauto.
            ** apply forall2_nth_error_inv.
               *** intros.
                   eapply eq_trans; [ | apply eq_sym ].
                   all: eapply in_repeat.
                   all: eapply nth_error_In; eauto.
               *** repeat rewrite repeat_length.
                   rewrite map_length.
                   rewrite length_to_sizes.
                   rewrite length_subst_in_size.
                   auto.
            ** match goal with
               | [ |- context[to_sizes _ ?H] ] => revert H
               end.
               rewrite subst_in_size_eq_map.
               intros.
               apply closed_sizes_eq.
              
          * use_InstInds_subst_indices.
            intros; destructAll.
            unfold subst.under_kindvars'.
            rewrite subst_ext_subst_of_indices_types; auto.
          * rewrite subst_indices_types.
            auto.

        + rewrite Forall_forall.
          intros.
          match goal with
          | [ X : _ * _ |- _ ] => destruct X
          end.
          match goal with
          | [ X : Typ |- _ ] => destruct X
          end.
          unfold update_ret_ctx.
          unfold empty_Function_Ctx.
          simpl.

          intros; destructAll.
          match goal with
          | [ H : In _ (subst.subst_indices _ _) |- _ ] =>
            apply in_subst_indices in H
          end.
          destructAll.
          match goal with
          | [ X : Typ |- _ ] => destruct X
          end.
          match goal with
          | [ H : QualT _ _ = subst.subst_indices _ _ |- _ ] =>
            rewrite subst_indices_type in H;
            inversion H; subst
          end.
          match goal with
          | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
            rewrite Forall_forall in H; specialize (H _ H')
          end.
          simpl in *.

          match goal with
          | [ |- context[subst.subst_indices ?L _] ] =>
            rewrite <-(subst_indices_Unrestricted (idxs:=L))
          end.
          eapply QualLeq_susbt_indices; eauto.
          match goal with
          | [ H : QualLeq ?A _ _ = Some true
              |- QualLeq ?B _ _ = Some true ] =>
            replace B with A; auto
          end.
          unfold F.
          match goal with
          | [ |- _ (_ _ ?A) = _ ?B ] =>
            replace B with A by auto;
            destruct A; subst; simpl in *; auto
          end.
        + solve_lcvs.
        + solve_tvs. }
      solve_tvs.

    Unshelve.
    all: auto.
  Qed.

  (* Unused *)

  Ltac invert_list_eq :=
    match goal with
    | [ H : _ ++ _ :: _ = [ _ ] |- _] =>
      eapply elt_eq_unit in H; destructAll;
      first
        [ congruence
        | match goal with
          | [ H : _ = Val _ |- _ ] => now inv H
          end
            (* not sure why congruence does not catch this *)
        ]
    end.

  Lemma reduce_simpl_value addr (v : Value) es :
    Reduce_simple addr [Val v] es -> False.
  Proof.
    intros Hred. inv Hred; eauto; try (now invert_list_eq ()).

    (destruct L; simpl in *; [ invert_list_eq ()  | invert_list_eq () ]).
  Qed.

  Lemma reduce_simpl_drop addr es :
    Reduce_simple addr [Drop] es -> False.
  Proof.
    intros Hred. inv Hred; eauto; try (now invert_list_eq ()).

    (destruct L; simpl in *); [ invert_list_eq ()  | invert_list_eq () ].
     Qed.

  Lemma reduce_simpl_unreachable addr es :
    Reduce_simple addr [Unreachable] es -> es = [ Trap ].
  Proof.
    intros Hred. inv Hred; try (now invert_list_eq ()).
    (destruct L; simpl in *); [ invert_list_eq ()  | invert_list_eq () ].
     reflexivity.
  Qed.

  Lemma reduce_simpl_nop addr es :
    Reduce_simple addr [Nop] es -> es = [].
  Proof.
    intros Hred. inv Hred; try (now invert_list_eq ()).
    (destruct L; simpl in *); [ invert_list_eq ()  | invert_list_eq () ].
     reflexivity.
  Qed.


End Preservation.
