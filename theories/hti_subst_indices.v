From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive micromega.Lia Classes.Morphisms Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Require Import RWasm.term RWasm.memory RWasm.reduction RWasm.typing RWasm.map_util
        RWasm.typing_util RWasm.tactics RWasm.list_util RWasm.EnsembleUtil
        RWasm.splitting RWasm.surface RWasm.memory RWasm.subst RWasm.debruijn RWasm.misc_util.

Lemma get_localtype_subst : forall {n L su},
    get_localtype n (subst'_local_ctx su L) =
    option_map
      (fun '(t, s) =>
         (subst.subst'_type su t, subst.subst'_size su s))
      (get_localtype n L).
Proof.
  induction n.
  - intros.
    destruct L; simpl; auto.
  - intros.
    destruct L; simpl; eauto.
Qed.

Lemma set_localtype_subst : forall {n t s L su},
    subst'_local_ctx su (set_localtype n t s L)
    =
    set_localtype
      n
      (subst.subst'_type su t)
      (subst.subst'_size su s)
      (subst'_local_ctx su L).
Proof.
  induction n.
  - intros.
    destruct L; simpl; auto.
  - intros.
    destruct L; simpl; eauto.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    unfold set_localtype in *.
    simpl.
    rewrite IHn; auto.
Qed.

Lemma add_local_effects_apply_subst : forall {tl L L' su},
    add_local_effects L tl = L' ->
    add_local_effects
      (subst'_local_ctx su L)
      (subst.subst'_localeffect su tl)
    =
    (subst'_local_ctx su L').
Proof.
  induction tl.
  - intros.
    simpl in *; subst; auto.
  - intros; simpl in *.
    match goal with
    | [ X : _ * _ |- _ ] => destruct X
    end.
    rewrite get_localtype_subst.
    match goal with
    | [ H : context[get_localtype ?N ?L] |- _ ] =>
      remember (get_localtype N L) as obj;
      revert H;
      generalize (eq_sym Heqobj); case obj; intros
    end.
    -- simpl.
       match goal with
       | [ X : _ * _ |- _ ] => destruct X
       end.
       match goal with
       | [ H : forall _ _ _, _,
           H' : add_local_effects _ _ = _ |- _ ] =>
         erewrite <-(H _ _ _ H')
       end.
       match goal with
       | [ |- _ ?A _ = _ ?B _ ] =>
         let H := fresh "H" in
         assert (H : A = B); [ | rewrite H; auto ]
       end.
       apply eq_sym.
       apply set_localtype_subst.
    -- simpl.
       eauto.
Qed.

Lemma subst_local_ctx_add_local_effects : forall {tl L su},
    subst'_local_ctx su (add_local_effects L tl)
    =
    add_local_effects
      (subst'_local_ctx su L)
      (subst.subst'_localeffect su tl).
Proof.
  intros.
  erewrite add_local_effects_apply_subst; eauto.
Qed.

Lemma add_local_effects_subst L L' tl :
  add_local_effects (subst'_local_ctx (debruijn.subst'_of (debruijn.weak subst.SPretype)) L) tl =
  subst'_local_ctx (debruijn.subst'_of (debruijn.weak subst.SPretype)) L' ->
  exists tl',
    add_local_effects L tl' = L'.
Proof.
  intros.
  specialize (add_local_effects_apply_subst (su:=(debruijn.subst'_of (debruijn.ext subst.SPretype Unit debruijn.id))) H).
  repeat rewrite local_ctx_debruijn_subst_weak.
  intros; eexists; eauto.
Qed.

(* easy *)
Lemma under_ks_under_ks_subst_of : forall {ks ks' su},
    under_ks' ks (under_ks' ks' (subst'_of su)) =
    under_ks' (plus ks ks') (subst'_of su).
Proof.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  unfold under_ks'.
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
      remember B as bool1; destruct bool1
  end.
  - unfold plus.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
        remember B as bool2; destruct bool2; auto
    end.
    match goal with
    | [ H : true = _ |- _ ] =>
        apply eq_sym in H;
        rewrite OrdersEx.Nat_as_DT.ltb_lt in H
    end.
    match goal with
    | [ H : false = _ |- _ ] =>
        apply eq_sym in H;
        rewrite OrdersEx.Nat_as_DT.ltb_ge in H
    end.
    lia.
  - match goal with
    | [ H : false = _ |- _ ] =>
        apply eq_sym in H;
        rewrite OrdersEx.Nat_as_DT.ltb_ge in H
    end.
    unfold plus.
    match goal with
    | [ |- context[if ?B then _ else _] ] =>
        remember B as bool2; destruct bool2; auto
    end.
    -- match goal with
       | [ H : true = _ |- _ ] =>
           apply eq_sym in H;
           rewrite OrdersEx.Nat_as_DT.ltb_lt in H
       end.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
           replace B with true
       end.
       2:{
         apply eq_sym.
         rewrite OrdersEx.Nat_as_DT.ltb_lt.
         lia.
       }
       unfold var'.
       match goal with
       | [ |- var _ ?A = var _ ?B ] => replace B with A; auto
       end.
       lia.
    -- match goal with
       | [ H : false = _ |- _ ] =>
           apply eq_sym in H;
           rewrite OrdersEx.Nat_as_DT.ltb_ge in H
       end.
       match goal with
       | [ |- context[if ?B then _ else _] ] =>
           replace B with false
       end.
       2:{
         apply eq_sym.
         rewrite OrdersEx.Nat_as_DT.ltb_ge.
         lia.
       }
       match goal with
       | [ |- subst'_of _ _ ?A _ = subst'_of _ _ ?B _ ] =>
           replace B with A by lia
       end.
       match goal with
       | [ |- subst'_of _ _ _ ?A = subst'_of _ _ _ ?B ] =>
           replace B with A; auto
       end.
       extensionality n.
       lia.
Qed.

Lemma under_ks'_unroll : forall {I} {Kind : I -> Type} {H : Var Kind} {ks : I -> nat} {s : Subst' Kind} {i' : I} {n' : nat} {ks' : I -> nat},
    @under_ks' I Kind H ks s i' n' ks' =
      if n' <? ks i'
      then var' i' n' ks'
      else s i' (n' - ks i') (plus ks ks').
Proof.
  intros.
  unfold under_ks'; auto.
Qed.

Lemma weak_non_loc_no_effect_on_loc : forall {f ks knd l},
    knd <> subst.SLoc ->
    debruijn_weaks_conds f ks (debruijn.sing knd 1) ->
    subst.subst'_loc f l = l.
Proof.
  destruct l; simpl; auto.
  unfold debruijn.get_var'.
  intros.
  erewrite weak_no_effect_on_other_vars; eauto.
Qed.

Ltac handle_ineq :=
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
      remember B as bool2; destruct bool2
  end;
  [ match goal with
     | [ H : true = _ |- _ ] =>
         apply eq_sym in H;
         rewrite OrdersEx.Nat_as_DT.ltb_lt in H
     end
    |
    match goal with
    | [ H : false = _ |- _ ] =>
        apply eq_sym in H;
        rewrite OrdersEx.Nat_as_DT.ltb_ge in H
    end ];
  try lia; simpl.

Lemma ext_plus_sing : forall {knd1 knd2 obj n},
    ext knd1 obj id knd2 (sing knd1 1 knd2 + n)
    = var knd2 n.
Proof.
  intros.
  destruct knd1; destruct knd2; simpl.
  all: unfold ext; simpl.
  all: unfold id.
  all: try rewrite Nat.sub_0_r; auto.
Qed.

Lemma subst_weak_comp'_under_ks : forall {ks knd obj},
    (under_ks' ks (subst'_of (ext knd obj debruijn.id)))
      ∘'
      (under_ks' ks (subst'_of (weak knd)))
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
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: unfold get_var'.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: unfold var'.
  all:
    try 
      match goal with
      | [ |- var _ ?A = var _ ?B ] =>
          unfold plus in *; unfold zero in *;
          simpl in *;
          match goal with
          | [ |- var _ ?AP = var _ ?BP ] =>
              replace BP with AP by lia; auto
          end
      end.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: unfold var'.
  all:
    try 
      match goal with
      | [ |- var _ ?A = var _ ?B ] =>
          unfold plus in *; unfold zero in *;
          simpl in *;
          match goal with
          | [ |- var _ ?AP = var _ ?BP ] =>
              replace AP with BP by lia; auto
          end
      end.
  all: destruct knd.

  all:
    match goal with
    | [ |- context[plus ?A ?B ?TYP + zero ?TYP + (?S + (?C - ?D)) - ?B ?TYP - ?A ?TYP] ] =>
        replace (plus A B TYP + zero TYP + (S + (C - D)) - B TYP - A TYP) with (S + (C - D)) by ltac:(unfold plus; unfold zero; lia)
    end.
  all: rewrite ext_plus_sing.

  all: unfold var.
  all: simpl.
  all: unfold get_var'.
  all: unfold weaks'.
  all: unfold var.
  all: simpl.
  all: unfold plus.
  all: unfold zero.
  all:
    match goal with
    | [ |- ?A ?B = ?A ?C ] => replace C with B by lia; auto
    end.
Qed.

Lemma ext_zero : forall {knd expr},
    ext knd expr id knd 0 = expr.
Proof.
  intros.
  destruct knd; unfold ext; simpl; auto.
Qed.

Lemma under_ks_weaks_comp_gen : forall {ks ks' ks''},
  under_ks' ks' (weaks' ks'') ∘' weaks' (plus ks ks') =
    weaks' (plus (plus ks'' ks) ks').
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
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: try now ltac:(unfold plus in *; lia).
  all: unfold weaks'.
  all: unfold var.
  all: simpl.
  all: unfold plus in *.
  all: unfold zero in *.
  1-4:
    match goal with
    | [ |- ?A ?B = ?A ?C ] => replace C with B by lia; auto
    end.
Qed.

Lemma weaks_subst_comm_under_ks : forall {ks' su ks},
  under_ks' ks (under_ks' ks' (subst'_of su)) ∘' weaks' ks =
  weaks' ks ∘' (under_ks' ks' (subst'_of su)).
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
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  
  1,3,5,7: unfold var'.
  1-4: unfold var.
  1-4: simpl.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1-4: unfold get_var'.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1-4: unfold weaks'.
  1-4: unfold var.
  1-4: simpl.
  1-4: unfold plus.
  1-4: unfold zero.
  1-4:
    match goal with
    | [ |- ?A ?B = ?A ?C ] => replace C with B by lia; auto
    end.

  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: rewrite plus_zero.
  all: rewrite plus_assoc.
  all:
    match goal with
    | [ |- context[plus (plus ?A ?B) _] ] =>
        rewrite (plus_comm A B)
    end.
  all:
    repeat match goal with
      | [ |- context[subst'_loc ?A ?B] ] =>
          replace (subst'_loc A B) with (subst_ext' A B) by auto
      | [ |- context[subst'_qual ?A ?B] ] =>
          replace (subst'_qual A B) with (subst_ext' A B) by auto
      | [ |- context[subst'_size ?A ?B] ] =>
          replace (subst'_size A B) with (subst_ext' A B) by auto
      | [ |- context[subst'_pretype ?A ?B] ] =>
          replace (subst'_pretype A B) with (subst_ext' A B) by auto
      end.
  all: rewrite subst_ext'_assoc.
  all: rewrite under_ks_weaks_comp_gen.
  all:
    match goal with
    | [ |- subst_ext' _ (_ _ ?A) = subst_ext' _ (_ _ ?B) ] =>
        replace B with A by lia; auto
    end.
Qed.

Lemma weaks'_weaks : forall ks,
    weaks' ks = subst'_of (weaks ks).
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
  all: unfold weaks'.
  all: unfold get_var'.
  all: unfold var.
  all: simpl.
  all:
    match goal with
    | [ |- ?A ?B = ?A ?C ] => replace C with B; auto
    end.
  all: unfold zero.
  all: lia.
Qed.  

Lemma weaks'_sing : forall knd,
  weaks' (sing knd 1) = subst'_of (weak knd).
Proof.
  intros.
  unfold weak.
  apply weaks'_weaks.
Qed.

Lemma weak_subst_under_ks_comm : forall {ks knd su},
    under' knd (under_ks' ks (subst'_of su)) ∘' (subst'_of (weak knd)) =
    (subst'_of (weak knd)) ∘' (under_ks' ks (subst'_of su)).
Proof.
  intros.
  repeat rewrite <-weaks'_sing.
  apply weaks_subst_comm_under_ks.
Qed.
  

Lemma weak_subst_comm : forall {knd su},
    under' knd (subst'_of su) ∘' (subst'_of (weak knd)) =
    (subst'_of (weak knd)) ∘' (subst'_of su).
Proof.
  intros.
  replace (subst'_of su) with (under_ks' zero (subst'_of su)).
  2:{ apply under_ks'_zero. }
  apply weak_subst_under_ks_comm.
Qed.

(*
1. Substitute idx2 at var 0 into main expression
2. Substitute idx1 at var n into main expression

vs

1. Substitute idx1 at var n+1 into main expression
2. Substitute idx1 at var n into idx2
3. Substitute the resulting idx2 at var 0 into main expression
*)

(* hard *)
Lemma subst_of_index_commute_not_closed : forall {ks idx1 idx2},
    (under_ks' ks (subst'_of (subst_of_index idx1)))
      ∘'
      (subst'_of (subst_of_index idx2))
    =
    (subst'_of (subst_of_index (subst'_index (under_ks' ks (subst'_of (subst_of_index idx1))) idx2)))
      ∘'
      (under_ks' (plus (sing (kind_of_index idx2) 1) ks)
         (subst'_of (subst_of_index idx1))).
Proof.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  simpl.

  assert (SQual <> SLoc) by solve_ineqs.
  assert (SSize <> SLoc) by solve_ineqs.
  assert (SPretype <> SLoc) by solve_ineqs.
  assert (SLoc <> SQual) by solve_ineqs.
  assert (SSize <> SQual) by solve_ineqs.
  assert (SPretype <> SQual) by solve_ineqs.
  assert (SLoc <> SSize) by solve_ineqs.
  assert (SQual <> SSize) by solve_ineqs.
  assert (SPretype <> SSize) by solve_ineqs.

  match goal with
  | [ X : Ind |- _ ] => destruct X
  end.
  all: destruct idx2; simpl.

  (* Ind=SLoc, idx2 does not match *)
  2-4: erewrite loc_debruijn_subst_ext; auto.
  4,7,10: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
  3,5,7: solve_ineqs.

  (* Ind=SQual, idx2 does not match *)
  5-6,8: erewrite qual_debruijn_subst_ext; auto.
  7,10,13: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
  6,8,10: solve_ineqs.

  (* Ind=SSize, idx2 does not match *)
  9,11-12: erewrite size_debruijn_subst_ext; auto.
  11,14,17: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
  10,12,14: solve_ineqs.

  (* Ind=SLoc/SQual/SSize and idx2 does not match *)
  2-4,5-7,9-11: unfold get_var'.
  2-10: rewrite under_ks_under_ks_subst_of.
  2-10: unfold under_ks'.
  2-10: unfold plus.
  2-10: unfold zero.
  2-10: simpl.
  2-10: repeat handle_ineq.
  2,4,6,8,10,12,14,16,18:
    unfold var';
    match goal with
    | [ |- var _ ?A = var _ ?B ] =>
        replace B with A; auto; lia
    end.
  2-10: destruct idx1; simpl.

  (* Ind=SLoc/SQual/SSize, both idx1 and idx2 do not match Ind *)
  all:
    match goal with
    | [ |- get_var' ?A _ _ = get_var' _ _ _ ] =>
        (* Use 0 <> 3 as our marker for future tactics *)
        assert (0 <> 3) by solve_ineqs; unfold get_var'
    | [ |- _ ] => idtac
    end.
  all:
    match goal with
    | [ H : 0 <> 3 |- _] => unfold weaks'
    | [ |- _ ] => idtac
    end.
  all:
    match goal with
    | [ H : 0 <> 3 |- _] => unfold zero; simpl
    | [ |- _ ] => idtac
    end.
  all:
    match goal with
    | [ |- var _ ?A = var _ ?B ] =>
        replace B with A; auto; lia
    | [ |- _ ] => idtac
    end.

  (* Ind=SLoc/SQual/SSize, idx1 matches Ind, idx2 does not match Ind *)
  2-10:
    match goal with
    | [ |- _ _ (ext _ _ _ _ ?A) =
           _ _ (ext _ _ _ _ ?B) ] =>
        replace A with B by lia
    end.
  2-10:
    match goal with
    | [ |- context[fun z => ?A z + ?B z + 0] ] =>
        replace (fun z => A z + B z + 0) with (plus (plus A B) zero) by auto
    end.
  2-10: rewrite plus_zero.
  2-10:
    match goal with
    | [ |- context[fun z => ?A z + ?B z + ?C z] ] =>
        replace (fun z => A z + B z + C z) with (plus (plus A B) C) by auto
    end.
  2-10: rewrite <-plus_assoc.
  2-10: rewrite compose_weak_weaks.
  2-10:
    match goal with
    | [ |- context[subst'_loc (?A ∘' ?B) ?C] ] =>
        replace (subst'_loc (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    | [ |- context[subst'_qual (?A ∘' ?B) ?C] ] =>
        replace (subst'_qual (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    | [ |- context[subst'_size (?A ∘' ?B) ?C] ] =>
        replace (subst'_size (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    end.
  2-10: rewrite <-subst_ext'_assoc.
  2-10: simpl.
  2-10: apply eq_sym.
  8-10: erewrite weak_non_size_no_effect_on_size.
  5-7: erewrite weak_non_qual_no_effect_on_qual.
  2-4: erewrite weak_non_loc_no_effect_on_loc.
  4,7,10,13,16,19,22,25,28: eapply single_weak_debruijn_weak_conds.
  3,5,7,9,11,13,15,17,19: solve_ineqs.
  2-10: rewrite plus_comm; auto.

  (* Ind=SPretype, idx2 does not match Ind *)
  4-6: unfold get_var'.
  4-6: destruct idx1; simpl.
  4-15: rewrite under_ks'_unroll.
  4-15: handle_ineq.
  4-15: rewrite under_ks'_unroll.
  4-15: handle_ineq.
  4-27: rewrite under_ks'_unroll.
  4-27: handle_ineq.
  4-51: unfold get_var'.
  4-51: try ltac:(rewrite under_ks'_unroll; handle_ineq).
  4-69: unfold get_var'.

  (* Ind=SPretype, both idx1 and idx2 do not match Ind *)
  4-69:
    try match goal with
        | [ |- weaks' _ _ _ _ = _ ] => unfold weaks'
        | [ |- _ = weaks' _ _ _ _ ] => unfold weaks'
        end.
  4-69:
    try match goal with
        | [ |- var' _ _ _ = _ ] => unfold var'
        | [ |- _ = var' _ _ _ ] => unfold var'
        end.
  4-69:
    try 
      match goal with
      | [ |- var _ ?A = var _ ?B ] =>
          unfold plus in *; unfold zero in *;
          simpl in *;
          match goal with
          | [ |- var _ ?AP = var _ ?BP ] =>
              replace BP with AP by lia; auto
          end
      end.
  4-12: try ltac:(unfold plus in *; unfold zero in *; simpl in *; lia).

  (* Ind=SPretype, idx1 matches Ind, idx2 does not match Ind *)
  4:
    erewrite loc_debruijn_subst_ext;
      [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
      [ | solve_ineqs ].
  5:
    erewrite size_debruijn_subst_ext;
      [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
      [ | solve_ineqs ].
  6:
    erewrite qual_debruijn_subst_ext;
      [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
      [ | solve_ineqs ].
  4-6: rewrite <-under_ks_weaks_comp.

  4-6:
    match goal with
    | [ |- context[subst'_pretype (?A ∘' ?B) ?C] ] =>
        replace (subst'_pretype (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    end.
  4-6: rewrite <-subst_ext'_assoc.
  4-6:
    match goal with
    | [ |- _ = subst'_pretype ?SU ?A ] =>
        replace (subst'_pretype SU A) with (subst_ext' SU A) by auto
    end.
  4-6: rewrite subst_ext'_assoc.
  4-6: rewrite subst_weak_comp'_under_ks.
  4-6: rewrite subst_ext'_var_e.
  4-6: rewrite plus_zero.
  4-6: simpl.
  4-6:
    match goal with
    | [ |- subst'_pretype _ (ext _ _ _ _ ?A) =
           subst'_pretype _ (ext _ _ _ _ ?B) ] =>
        replace B with A; auto
    end.
  4-6: unfold plus.
  4-6: unfold zero.
  4-6: simpl; lia.

  (* Ind=SLoc/SQual/SSize/SPretype, idx2 matches Ind *)
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  
  1,3,5,7: unfold get_var'.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1-4:
    match goal with
    | [ |- context[?A + ?B - ?A] ] =>
        replace (A + B - A) with B by lia;
        destruct B; simpl
    end.
  
  1,3,5,7: repeat rewrite ext_zero.
  1-4: rewrite plus_zero.
  1-4:
    repeat match goal with
           | [ |- context[subst'_loc ?A ?B] ] =>
               replace (subst'_loc A B) with (subst_ext' A B) by auto
           | [ |- context[subst'_qual ?A ?B] ] =>
               replace (subst'_qual A B) with (subst_ext' A B) by auto
           | [ |- context[subst'_size ?A ?B] ] =>
               replace (subst'_size A B) with (subst_ext' A B) by auto
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
  1-4: repeat rewrite subst_ext'_assoc.
  1-4: rewrite weaks_subst_comm_under_ks; auto.
  
  1-4: unfold get_var'.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.

  1,3,5,7: unfold var'.
  1-4: unfold weaks'.
  1-4: unfold var.
  1-4: simpl.
  1-4: unfold plus.
  1-4: unfold zero.
  1-4:
    match goal with
    | [ |- ?A ?B = ?A ?C ] => replace C with B by lia; auto
    end.

  1-4: unfold plus in *.
  1-4: unfold zero in *.
  1-4: simpl in *.
  1-4: lia.

  1-4:
    match goal with
    | [ |- subst'_loc _ (subst'_loc _ (_ _ _ _ _ ?IDX)) = _ ] =>
        destruct IDX
    | [ |- subst'_qual _ (subst'_qual _ (_ _ _ _ _ ?IDX)) = _ ] =>
        destruct IDX
    | [ |- subst'_size _ (subst'_size _ (_ _ _ _ _ ?IDX)) = _ ] =>
        destruct IDX
    | [ |- subst'_pretype _ (subst'_pretype _ (_ _ _ _ _ ?IDX)) = _ ] =>
        destruct IDX
    end.
  1,3,5,7: unfold plus in *; simpl in *; lia.
  1-4: simpl.
  1-4: unfold get_var'.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1-4: rewrite under_ks'_unroll.
  1-4: handle_ineq.
  1,3,5,7: unfold plus in *; simpl in *; lia.
  1-4: rewrite plus_zero.
  1-4: rewrite <-under_ks_weaks_comp_gen.
  1-4:
    match goal with
    | [ |- context[subst'_loc (?A ∘' ?B) ?C] ] =>
        replace (subst'_loc (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    | [ |- context[subst'_qual (?A ∘' ?B) ?C] ] =>
        replace (subst'_qual (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    | [ |- context[subst'_size (?A ∘' ?B) ?C] ] =>
        replace (subst'_size (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    | [ |- context[subst'_pretype (?A ∘' ?B) ?C] ] =>
        replace (subst'_pretype (A ∘' B) C) with (subst_ext' (A ∘' B) C) by auto
    end.
  1-4: rewrite <-subst_ext'_assoc.
  1-4:
    match goal with
    | [ |- _ = subst'_loc ?SU ?L ] =>
        replace (subst'_loc SU L) with (subst_ext' SU L) by auto
    | [ |- _ = subst'_qual ?SU ?L ] =>
        replace (subst'_qual SU L) with (subst_ext' SU L) by auto
    | [ |- _ = subst'_size ?SU ?L ] =>
        replace (subst'_size SU L) with (subst_ext' SU L) by auto
    | [ |- _ = subst'_pretype ?SU ?L ] =>
        replace (subst'_pretype SU L) with (subst_ext' SU L) by auto
    end.
  1-4:
    match goal with
    | [ |- _ = subst_ext' ?SU (subst_ext' ?SU2 ?L) ] =>
        replace (subst_ext' SU (subst_ext' SU2 L)) with (subst_ext' (SU ∘' SU2) L) by ltac:(apply eq_sym; rewrite subst_ext'_assoc; auto)
    end.
  1-4: rewrite weaks'_sing.
  1-4: rewrite subst_weak_comp'_under_ks.
  1-4: rewrite subst_ext'_var_e.
  1-4: simpl.
  1-4:
    match goal with
    | [ |- subst'_loc _ (subst_of_index _ _ ?A) =
           subst'_loc _ (subst_of_index _ _ ?B) ] =>
        replace B with A; auto
    | [ |- subst'_qual _ (subst_of_index _ _ ?A) =
           subst'_qual _ (subst_of_index _ _ ?B) ] =>
        replace B with A; auto
    | [ |- subst'_size _ (subst_of_index _ _ ?A) =
           subst'_size _ (subst_of_index _ _ ?B) ] =>
        replace B with A; auto
    | [ |- subst'_pretype _ (subst_of_index _ _ ?A) =
           subst'_pretype _ (subst_of_index _ _ ?B) ] =>
        replace B with A; auto
    end.
  all: unfold zero in *.
  all: lia.
Qed.

Lemma rec_inner_type : forall {ks idx qa pt q},
    subst_ext'
      (under_ks' ks (subst'_of (subst_of_index idx)))
      [QualT
         (subst'_pretype
            (subst'_of (ext SPretype (Rec qa (QualT pt q)) id))
            pt)
         (subst'_qual
            (subst'_of (ext SPretype (Rec qa (QualT pt q)) id))
            q)]
    =
    [subst_ext
       (ext SPretype
            (Rec
               (subst'_qual
                  (under_ks' ks (subst'_of (subst_of_index idx)))
                  qa)
               (QualT
                  (subst'_pretype
                     (under' SPretype
                        (under_ks' ks
                           (subst'_of (subst_of_index idx)))) pt)
                  (subst'_qual
                     (under_ks' ks
                        (subst'_of (subst_of_index idx))) q))) id)
         (QualT
            (subst'_pretype
               (under' SPretype
                  (under_ks' ks (subst'_of (subst_of_index idx))))
               pt)
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx))) q))].
Proof.
  intros.
  match goal with
  | [ |- context[QualT (subst'_pretype ?SU ?PT)
                       (subst'_qual ?SU ?Q)] ] =>
    replace [QualT (subst'_pretype SU PT)
                   (subst'_qual SU Q)]
      with
        (subst_ext' SU [QualT PT Q])
        by auto
  end.
  rewrite subst_ext'_assoc.
  match goal with
  | [ |- context[ext SPretype ?A ?B] ] =>
    replace (ext SPretype A B) with (subst_of_index (PretypeI A)) by auto
  end.
  rewrite subst_of_index_commute_not_closed.
  rewrite <-subst_ext'_assoc.
  simpl.
  rewrite <-under_ks_under_ks_subst_of.
  replace (under_ks' (sing SPretype 1)) with (under' SPretype) by auto.
  match goal with
  | [ |- context[ext SPretype (Rec _ (QualT _ (subst'_qual (under' SPretype ?F) ?Q)))] ] =>
    replace (subst'_qual (under' SPretype F) Q) with (subst'_qual F Q); auto
  end.
  destruct idx; simpl.
  all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  all: eapply debruijn_subst_under_ks.
  all: eapply simpl_debruijn_subst_ext_conds; eauto.
Qed.

Lemma subst_ext_subst_of : forall {A : Type} {H : @BindExt Ind Kind VarKind BindVar_rwasm BindRWasm A} {su} {obj : A},
    subst_ext' (subst'_of su) obj = subst_ext su obj.
Proof.
  intros; auto.
Qed.

Lemma rec_inner_type_inv : forall {ks idx qa pt q},
    (subst_ext
       (ext SPretype
          (Rec
             (subst'_qual
                (under_ks' ks (subst'_of (subst_of_index idx))) qa)
             (QualT
                (subst'_pretype
                   (under' SPretype
                      (under_ks' ks
                         (subst'_of (subst_of_index idx)))) pt)
                (subst'_qual
                   (under_ks' ks (subst'_of (subst_of_index idx)))
                   q))) id)
       (QualT
          (subst'_pretype
             (under' SPretype
                (under_ks' ks (subst'_of (subst_of_index idx))))
             pt)
          (subst'_qual
             (under_ks' ks (subst'_of (subst_of_index idx))) q)))
    =
    subst'_type (under_ks' ks (subst'_of (subst_of_index idx)))
                (subst_ext'
                   (subst'_of (subst_of_index (Rec qa (QualT pt q))))
                   (QualT pt q)).
Proof.
  intros.
  match goal with
  | [ |- context[QualT (subst'_pretype ?F2 ?PT) (subst'_qual ?F ?Q)] ] =>
    replace (QualT (subst'_pretype F2 PT) (subst'_qual F Q)) with (subst_ext' F2 (QualT PT Q))
  end.
  2:{
    simpl; auto.
    destruct idx; simpl.
    all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
    all: eapply debruijn_subst_under_ks.
    all: eapply simpl_debruijn_subst_ext_conds; eauto.
  }
  rewrite <-subst_ext_subst_of.
  rewrite subst_ext'_assoc.
  match goal with
  | [ |- context[ext SPretype ?PT id] ] =>
    replace (ext SPretype PT id) with (subst_of_index (PretypeI PT)) by auto
  end.
  match goal with
  | [ |- context[PretypeI (Rec (subst'_qual ?F ?Q) (subst_ext' ?F2 ?T))] ] =>
    replace (PretypeI (Rec (subst'_qual F Q) (subst_ext' F2 T))) with (subst'_index F (Rec Q T)) by auto
  end.
  match goal with
  | [ |- context[Rec ?A ?B] ] =>
    replace SPretype with (kind_of_index (PretypeI (Rec A B))) by auto
  end.
  unfold under'.
  rewrite under_ks_under_ks_subst_of.
  rewrite <-subst_of_index_commute_not_closed.
  rewrite <-subst_ext'_assoc; auto.
Qed.

Lemma rec_inner_pretype_inv : forall {ks idx qa pt q},
    (subst'_pretype
       (subst'_of
          (ext SPretype
             (Rec
                (subst'_qual
                   (under_ks' ks (subst'_of (subst_of_index idx))) qa)
                (QualT
                   (subst'_pretype
                      (under' SPretype
                         (under_ks' ks
                            (subst'_of (subst_of_index idx)))) pt)
                   (subst'_qual
                      (under_ks' ks (subst'_of (subst_of_index idx)))
                      q))) id))
       (subst'_pretype
          (under' SPretype
             (under_ks' ks (subst'_of (subst_of_index idx))))
          pt))
    =
      subst'_pretype
        (under_ks' ks (subst'_of (subst_of_index idx)))
        (subst_ext'
           (subst'_of (subst_of_index (Rec qa (QualT pt q))))
           pt).
Proof.
  intros.
  specialize (@rec_inner_type_inv ks idx qa pt q).
  intros.
  simpl in *.
  inv H.
  auto.
Qed.

Lemma rec_pretype : forall {ks idx qa pt q},
  subst'_pretype
    (under_ks' ks (subst'_of (subst_of_index idx)))
    (Rec qa (QualT pt q))
  =
  Rec
    (subst'_qual
       (under_ks' ks (subst'_of (subst_of_index idx))) qa)
    (QualT
       (subst'_pretype
          (under' SPretype
                  (under_ks' ks (subst'_of (subst_of_index idx))))
          pt)
       (subst'_qual
          (under_ks' ks (subst'_of (subst_of_index idx))) q)).
Proof.
  intros; simpl.
  destruct idx; simpl.
  all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  all: eapply debruijn_subst_under_ks.
  all: eapply simpl_debruijn_subst_ext_conds; eauto.
Qed.

Ltac handle_ineq_le :=
  match goal with
  | [ |- context[if ?B then _ else _] ] =>
      remember B as bool2; destruct bool2
  end;
  [ match goal with
     | [ H : true = _ |- _ ] =>
         apply eq_sym in H;
         rewrite OrdersEx.Nat_as_DT.leb_le in H
     end
    |
    match goal with
    | [ H : false = _ |- _ ] =>
        apply eq_sym in H;
        rewrite OrdersEx.Nat_as_DT.leb_gt in H
    end ];
  try lia; simpl.

Lemma LocValid_subst_index : forall {F ks idx l},
    InstIndValid_at F ks idx ->
    LocValid (location F) l ->
    LocValid (location (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_loc (under_ks' ks (subst'_of (subst_of_index idx))) l).
Proof.
  intros.
  destruct l.
  2:{ econstructor; simpl; eauto. }
  simpl.
  unfold get_var'.
  unfold under_ks'.
  handle_ineq.
  - unfold var'.
    unfold var.
    simpl.
    destruct idx; destruct F; simpl in *; auto.
    econstructor 2; eauto.
    unfold shift_down_after_eq.
    handle_ineq_le.
    match goal with
    | [ H : LocValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : LocV _ = _ |- _ ] => inv H
      end.
    auto.
  - destruct idx; simpl.
    2-4: unfold get_var'.
    2-4: unfold weaks'.
    2-4: unfold var.
    2-4: simpl.
    2-4: econstructor 2; eauto.
    2-4: unfold plus.
    2-4: unfold zero.
    2-4: destruct F; subst; simpl in *.
    2-4:
      match goal with
      | [ H : LocValid _ _ |- _ ] => inv H
      end.
    2-7:
      match goal with
      | [ H : LocV _ = _ |- _ ] => inv H
      end.
    2-4: lia.

    match goal with
    | [ |- context[ext _ _ _ _ ?A] ] =>
        remember A as obj; destruct obj
    end.
    -- rewrite ext_zero.
       match goal with
       | [ |- context[subst'_loc _ ?L] ] => destruct L; simpl
       end.
       2:{ econstructor; simpl; eauto. }
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.
       econstructor 2; eauto.
       destruct F; subst; simpl in *.
       unfold plus.
       unfold zero.
       match goal with
       | [ H : LocValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : LocV _ = _ |- _ ] => inv H
         end.
       match goal with
       | [ H : InstIndValid_at _ _ _ |- _ ] => inv H; simpl in *
       end.
       --- lia.
       --- match goal with
           | [ H : InstIndValid _ _ _ |- _ ] => inv H
           end.
           simpl in *.
           all: unfold get_var' in *.
           all: unfold weaks' in *.
           all: unfold debruijn.var in *.
           all: simpl in *.
           match goal with
           | [ H : LocValid _ _ |- _ ] => inv H
           end.
           all:
             match goal with
             | [ H : LocV _ = _ |- _ ] => inv H
             end.
           lia.
    -- simpl.
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.
       econstructor 2; eauto.
       destruct F; subst; simpl in *.
       unfold plus.
       unfold zero.
       unfold shift_down_after_eq.
       match goal with
       | [ H : LocValid _ _ |- _ ] =>
           inv H
       end.
       all:
         match goal with
         | [ H : LocV _ = _ |- _ ] => inv H
         end.
       handle_ineq_le.
Qed.

Lemma LocValid_subst_index_general : forall {F ks idx l newloc newl},
    InstIndValid_at F ks idx ->
    LocValid (location F) l ->
    newloc = location (InstFunctionCtxInd_under_ks F ks idx) ->
    newl = subst'_loc (under_ks' ks (subst'_of (subst_of_index idx))) l ->
    LocValid newloc newl.
Proof.
  intros; subst.
  apply LocValid_subst_index; auto.
Qed.

Lemma LocValid_subst_index_loc : forall {F ks f l l'},
    InstIndValid_at F ks (LocI l') ->
    debruijn_subst_ext_conds f ks SLoc l' ->
    LocValid (location F) l ->
    LocValid
      (location
         (subst'_function_ctx
            (under_ks' ks (subst'_of (ext SLoc l' id)))
            (update_location_ctx
               (shift_down_after_eq (location F) (ks SLoc) 0) F)))
      (subst'_loc f l).
Proof.
  intros.
  eapply LocValid_subst_index_general; eauto.
  match goal with
  | [ |- subst'_loc ?F1 _ = subst'_loc ?F2 _ ] =>
      replace F2 with F1; auto
  end.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma TypeValid_empty_imp_value_closed_type : forall {F t},
    TypeValid F t ->
    Function_Ctx_empty F ->
    forall ks idx,
      subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) t = t.
Proof.
  intros.
  eapply TypesValid_under_conds_no_effect; eauto.
  eapply debruijn_under_change_ks.
  - apply trivial_debruijn_under_conds.
  - unfold Function_Ctx_empty in *.
    destructAll.
    unfold zero.
    prove_ks_eq F; subst; auto.
Qed.

Lemma HeapTypeValid_empty_imp_value_closed : forall {F ht},
    HeapTypeValid F ht ->
    Function_Ctx_empty F ->
    forall ks idx,
      subst'_heaptype (under_ks' ks (subst'_of (subst_of_index idx))) ht = ht.
Proof.
  intros.
  eapply TypesValid_under_conds_no_effect; eauto.
  eapply debruijn_under_change_ks.
  - apply trivial_debruijn_under_conds.
  - unfold Function_Ctx_empty in *.
    destructAll.
    unfold zero.
    prove_ks_eq F; subst; auto.
Qed.

Lemma FunTypeValid_empty_imp_value_closed : forall {F ft},
    FunTypeValid F ft ->
    Function_Ctx_empty F ->
    forall ks idx,
      subst'_funtype (under_ks' ks (subst'_of (subst_of_index idx))) ft = ft.
Proof.
  intros.
  eapply TypesValid_under_conds_no_effect; eauto.
  eapply debruijn_under_change_ks.
  - apply trivial_debruijn_under_conds.
  - unfold Function_Ctx_empty in *.
    destructAll.
    unfold zero.
    prove_ks_eq F; subst; auto.
Qed.

Lemma HasTypeClosure_imp_funtype_closed : forall {S cl ft},
    HasTypeClosure S cl ft ->
    forall ks idx,
      subst'_funtype (under_ks' ks (subst'_of (subst_of_index idx))) ft = ft.
Proof.
  intros.
  match goal with
  | [ H : HasTypeClosure _ _ _ |- _ ] => inv H
  end.
  match goal with
  | [ H : HasTypeFunc _ _ _ _ _ |- _ ] => inv H
  end.
  eapply FunTypeValid_empty_imp_value_closed; eauto.
  constructor; auto.
Qed.

Lemma nth_error_shift_down_usable : forall {A} {l : list A} {v v' v''},
    v <> v' ->
    v'' = shift_down_after v v' 0 ->
    nth_error (remove_nth l v') v'' =
    nth_error l v.
Proof.
  intros; subst.
  apply nth_error_shift_down.
  auto.
Qed.

Lemma nth_error_Some_usable : forall {A} {l : list A} {n obj},
    nth_error l n = Some obj -> n < length l.
Proof.
  intros.
  eapply nth_error_Some.
  rewrite H; solve_ineqs.
Qed.

Inductive InstIndValidSize_at_weak : Function_Ctx -> (Ind -> nat) -> Size -> Prop :=
| InstIndValidSize_at_weak_None : forall F ks sz,
    nth_error (size F) (ks SSize) = None ->
    InstIndValidSize_at_weak F ks sz
| InstIndValidSize_at_weak_Some : forall F ks sz szs0 szs1,
    nth_error (size F) (ks SSize) = Some (szs0, szs1) ->
    SizeValid
      (size (InstFunctionCtxInd_under_ks F ks (SizeI sz)))
      (subst'_size (weaks' ks) sz) ->
    InstIndValidSize_at_weak F ks sz.

Lemma InstIndValid_at_to_weak : forall {F ks sz},
    InstIndValid_at F ks (SizeI sz) ->
    InstIndValidSize_at_weak F ks sz.
Proof.
  intros.
  inv H.
  - constructor 1; auto.
  - econstructor 2; eauto.
    match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inv H
    end.
    auto.
Qed.

Lemma InstIndValidSize_at_weak_SizePlus_inv : forall {F ks sz1 sz2},
    InstIndValidSize_at_weak F ks (SizePlus sz1 sz2) ->
    InstIndValidSize_at_weak F ks sz1 /\
    InstIndValidSize_at_weak F ks sz2.
Proof.
  intros.
  inv H.
  - split; constructor 1; auto.
  - split; econstructor 2; eauto.
    all:
      match goal with
      | [ H : SizeValid _ _ |- _ ] => inv H
      end.
    all: simpl in *.
    all:
      match goal with
      | [ H : SizePlus _ _ = _ |- _ ] => inv H
      end.
    all: eapply SizeValid_length; eauto.
    all: repeat rewrite map_length; auto.
Qed.

Lemma SizeValid_subst_size : forall {sz sz' F ks},
    SizeValid (size F) (SizeVar (ks SSize)) ->
    InstIndValidSize_at_weak F ks sz ->
    SizeValid
      (map
         (fun '(ss1, ss2) =>
            (subst'_sizes (under_ks' ks (subst'_of (ext SSize sz' id)))
               ss1,
             subst'_sizes (under_ks' ks (subst'_of (ext SSize sz' id)))
               ss2))
         (remove_nth (size F) (ks SSize)))
    (subst'_size (weaks' ks) sz).
Proof.
  induction sz; intros.
  2:{
    match goal with
    | [ H : InstIndValidSize_at_weak _ _ _ |- _ ] =>
        apply InstIndValidSize_at_weak_SizePlus_inv in H
    end.
    destructAll.
    simpl; econstructor 2; eauto.
  }
  2:{ econstructor; simpl; eauto. }

  unfold get_var'.
  unfold weaks'.
  unfold var.
  simpl.

  match goal with
  | [ H : InstIndValidSize_at_weak _ _ _ |- _ ] => inv H
  end.
  --- match goal with
      | [ H : SizeValid _ _ |- _ ] => inv H
      end.
      all:
        match goal with
        | [ H : SizeVar _ = _ |- _ ] => inv H
        end.
      rewrite nth_error_None in *.
      match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
          apply nth_error_Some_usable in H
      end.
      lia.
  --- simpl in *.
      unfold get_var' in *.
      unfold weaks' in *.
      unfold var in *.
      simpl in *.
      match goal with
      | [ H : SizeValid _ _ |- _ ] => inv H
      end.
      all:
        match goal with
        | [ H : SizeVar _ = _ |- _ ] => inv H
        end.
      rewrite size_update_size_ctx in *.
      match goal with
      | [ H : nth_error (map _ _) _ = _ |- _ ] =>
          apply nth_error_map_inv in H
      end.
      destructAll.
      econstructor 3; eauto.
      erewrite nth_error_map; eauto.
Qed.

Lemma size_InstFunctionCtxInd_under_ks_non_size : forall {F ks idx},
    kind_of_index idx <> SSize ->
    size (InstFunctionCtxInd_under_ks F ks idx) = size F.
Proof.
  destruct idx; intros; simpl in *; solve_impossibles.
  all: destruct F; simpl in *.
  all:
    match goal with
    | [ |- map ?F _ = _ ] => replace F with (fun (x : (list Size * list Size)) => x); [ apply map_id | ]
    end.
  all: eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all: erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  all: erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  all: auto.
Qed.

Lemma SizeValid_subst_index : forall {sz F ks idx},
    SizeValid (size F) sz ->
    InstIndValid_at F ks idx ->
    SizeValid
      (size (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_size
         (under_ks' ks (subst'_of (subst_of_index idx)))
         sz).
Proof.
  intros.
  destruct idx.
  all: try ltac:(erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | now solve_ineqs ]).
  all: try ltac:(rewrite size_InstFunctionCtxInd_under_ks_non_size; simpl; [ | now solve_ineqs ]).
  all: auto.
  
  induction sz.
  2:{
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizePlus _ _ = _ |- _ ] => inv H
      end.
    econstructor 2; simpl in *; eauto.
  }
  2:{ econstructor; simpl; eauto. }
  
  simpl.
  unfold get_var'.
  rewrite under_ks'_unroll.
  rewrite size_update_size_ctx.
  handle_ineq.
  - unfold var'.
    unfold var.
    simpl.
    match goal with
    | [ H : SizeValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : SizeVar _ = _ |- _ ] => inv H
      end.
    econstructor 3; eauto.
    erewrite nth_error_map; eauto.
    erewrite nth_error_shift_down_usable; eauto; [ lia | ].
    unfold shift_down_after.
    handle_ineq.
  - match goal with
    | [ |- context[ext _ _ _ _ ?A] ] =>
        remember A as obj; destruct obj
    end.
    -- rewrite ext_zero.
       match goal with
       | [ H : 0 = ?A - ?B |- _ ] =>
           assert (A = B) by lia; subst
       end.
       rewrite plus_zero.
       apply SizeValid_subst_size; auto.
       apply InstIndValid_at_to_weak; auto.
    -- simpl.
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.
       match goal with
       | [ H : SizeValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : SizeVar _ = _ |- _ ] => inv H
         end.
       econstructor 3; eauto.
       destruct F; subst; simpl in *.
       unfold plus.
       unfold zero.
       erewrite nth_error_map; eauto.
       erewrite nth_error_shift_down_usable; eauto.
       --- lia.
       --- unfold shift_down_after.
           handle_ineq.
Qed.

Lemma SizeValid_subst_index_general : forall {sz F ks idx F' sz'},
    SizeValid (size F) sz ->
    InstIndValid_at F ks idx ->
    F' = size (InstFunctionCtxInd_under_ks F ks idx) ->
    sz' = subst'_size (under_ks' ks (subst'_of (subst_of_index idx))) sz ->
    SizeValid F' sz'.
Proof.
  intros; subst; eapply SizeValid_subst_index; eauto.
Qed.

Lemma SizeValids_subst_index : forall {szs F ks idx},
    Forall (SizeValid (size F)) szs ->
    InstIndValid_at F ks idx ->
    Forall
      (SizeValid (size (InstFunctionCtxInd_under_ks F ks idx)))
      (subst'_sizes (under_ks' ks (subst'_of (subst_of_index idx)))
         szs).
Proof.
  induction szs; intros; constructor; auto.
  all:
    match goal with
    | [ H : Forall _ (_ :: _) |- _ ] => inv H
    end.
  - apply SizeValid_subst_index; auto.
  - apply IHszs; auto.
Qed.

Lemma qual_InstFunctionCtxInd_under_ks_non_qual : forall {F ks idx},
    kind_of_index idx <> SQual ->
    qual (InstFunctionCtxInd_under_ks F ks idx) = qual F.
Proof.
  destruct idx; intros; simpl in *; solve_impossibles.
  all: destruct F; simpl in *.
  all:
    match goal with
    | [ |- map ?F _ = _ ] => replace F with (fun (x : (list Qual * list Qual)) => x); [ apply map_id | ]
    end.
  all: eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all: erewrite quals_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  all: erewrite quals_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  all: auto.
Qed.

(* pretty easy *)
Lemma QualValid_subst_index : forall {F ks idx q},
    InstIndValid_at F ks idx ->
    QualValid (qual F) q ->
    QualValid
      (qual (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros.
  destruct idx.
  all: try ltac:(erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | now solve_ineqs ]).
  all: try ltac:(rewrite qual_InstFunctionCtxInd_under_ks_non_qual; simpl; [ | now solve_ineqs ]).
  all: auto.
  
  destruct q.
  2:{ econstructor; simpl; eauto. }
  simpl.
  unfold get_var'.
  rewrite under_ks'_unroll.
  rewrite qual_update_qual_ctx.
  handle_ineq.
  - unfold var'.
    unfold var.
    simpl.
    match goal with
    | [ H : QualValid _ _ |- _ ] => inv H
    end.
    all:
      match goal with
      | [ H : QualVar _ = _ |- _ ] => inv H
      end.
    econstructor 2; eauto.
    erewrite nth_error_map; eauto.
    erewrite nth_error_shift_down_usable; eauto; [ lia | ].
    unfold shift_down_after.
    handle_ineq.
  - match goal with
    | [ |- context[ext _ _ _ _ ?A] ] =>
        remember A as obj; destruct obj
    end.
    -- rewrite ext_zero.
       match goal with
       | [ |- context[subst'_qual _ ?L] ] => destruct L; simpl
       end.
       2:{ econstructor; simpl; eauto. }
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.

       match goal with
       | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
       end.
       --- match goal with
           | [ H : QualValid _ _ |- _ ] => inv H
           end.
           all:
             match goal with
             | [ H : QualVar _ = _ |- _ ] => inv H
             end.
           rewrite nth_error_None in *.
           match goal with
           | [ H : nth_error _ _ = Some _ |- _ ] =>
               apply nth_error_Some_usable in H
           end.
           lia.
       --- match goal with
           | [ H : InstIndValid _ _ _ |- _ ] => inv H
           end.
           unfold get_var' in *.
           unfold weaks' in *.
           unfold var in *.
           simpl in *.
           match goal with
           | [ H : QualValid _ _ |- _ ] => inv H
           end.
           all:
             match goal with
             | [ H : QualVar _ = _ |- _ ] => inv H
             end.
           rewrite qual_update_qual_ctx in *.
           econstructor 2; eauto.
           match goal with
           | [ H : nth_error ?L ?A = _ |- nth_error ?L ?B = _ ] =>
               replace B with A; eauto
           end.
    -- simpl.
       unfold get_var'.
       unfold weaks'.
       unfold var.
       simpl.
       match goal with
       | [ H : QualValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : QualVar _ = _ |- _ ] => inv H
         end.
       econstructor 2; eauto.
       destruct F; subst; simpl in *.
       unfold plus.
       unfold zero.
       erewrite nth_error_map; eauto.
       erewrite nth_error_shift_down_usable; eauto.
       --- lia.
       --- unfold shift_down_after.
           handle_ineq.
Qed.

Lemma subst_non_qual_index_no_effect_on_qual : forall {knd ks qual obj},
    knd <> SQual ->
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (under_ks' ks (subst'_of (ext knd obj id))) qs1,
          subst'_quals (under_ks' ks (subst'_of (ext knd obj id))) qs2))
      qual = qual.
Proof.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (x : list Qual * list Qual) => x); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite quals_debruijn_subst_ext.
  3:{
    eapply debruijn_subst_under_ks.
    eapply simpl_debruijn_subst_ext_conds.
  }
  2: auto.
  erewrite quals_debruijn_subst_ext.
  3:{
    eapply debruijn_subst_under_ks.
    eapply simpl_debruijn_subst_ext_conds.
  }
  all: auto.
Qed.

Lemma qual_fctx_subst_loc : forall {F ks l},
    qual
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SLoc l id)))
         (update_location_ctx
            (shift_down_after_eq (location F) (ks SLoc) 0) F)) =
    qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma qual_fctx_subst_size : forall {F ks sz},
    qual
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SSize sz id)))
         (update_size_ctx (remove_nth (size F) (ks SSize)) F))
    =
      qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma qual_fctx_subst_size_alternate : forall {F ks sz},
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (under_ks' ks (subst'_of (ext SSize sz id)))
            qs1,
          subst'_quals (under_ks' ks (subst'_of (ext SSize sz id)))
            qs2))
      (qual (update_size_ctx (remove_nth (size F) (ks SSize)) F))
    =
    qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma qual_fctx_subst_pretype : forall {F ks pt},
    qual
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SPretype pt id)))
         (update_type_ctx (remove_nth (type F) (ks SPretype)) F))
    =
    qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma qual_fctx_subst_pretype_alternate : forall {F ks pt},
    map
      (fun '(qs1, qs2) =>
         (subst'_quals
            (under_ks' ks (subst'_of (ext SPretype pt id))) qs1,
          subst'_quals
            (under_ks' ks (subst'_of (ext SPretype pt id))) qs2))
      (qual
         (update_type_ctx (remove_nth (type F) (ks SPretype)) F))
    =
    qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma loc_fctx_subst_qual : forall {F ks q},
    location
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SQual q id)))
         (update_qual_ctx (remove_nth (qual F) (ks SQual)) F))
    =
    location F.
Proof.
  destruct F; simpl; auto.
Qed.

Lemma qual_fctx_subst_loc_alternate : forall {F ks l},
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (under_ks' ks (subst'_of (ext SLoc l id)))
            qs1,
           subst'_quals (under_ks' ks (subst'_of (ext SLoc l id)))
             qs2))
      (qual
         (update_location_ctx
            (shift_down_after_eq (location F) (ks SLoc) 0) F))
    =
    qual F.
Proof.
  destruct F; subst; simpl.
  intros.
  rewrite subst_non_qual_index_no_effect_on_qual; auto.
  solve_ineqs.
Qed.

Lemma type_fctx_subst_loc : forall {F ks l},
    type
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SLoc l id)))
         (update_location_ctx
            (shift_down_after_eq (location F) (ks SLoc) 0) F))
    =
    type F.
Proof.
  destruct F; subst; simpl.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : Size * Qual * HeapableConstant) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma type_fctx_subst_loc_alternate : forall {F ks l},
  map
    (fun '(s, q0, hc) =>
       (subst'_size (under_ks' ks (subst'_of (ext SLoc l id)))
          s,
         subst'_qual (under_ks' ks (subst'_of (ext SLoc l id)))
           q0, hc))
    (type
       (update_location_ctx
          (shift_down_after_eq (location F) (ks SLoc) 0) F))
  = type F.
Proof.
  destruct F; subst; simpl.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : Size * Qual * HeapableConstant) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma type_fctx_subst_qual_eifc : forall {F ks q},
    equal_in_first_comp
      (map
         (fun '(s, q1, hc) =>
            (subst'_size (under_ks' ks (subst'_of (ext SQual q id)))
               s,
             subst'_qual (under_ks' ks (subst'_of (ext SQual q id)))
               q1,
             hc))
         (type (update_qual_ctx (remove_nth (qual F) (ks SQual)) F)))
      (type F).
Proof.
  destruct F; intros; simpl.
  induction type; intros; destruct_prs; simpl.
  1: constructor.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  constructor.
  apply IHtype.
Qed.

Lemma size_fctx_subst_qual_index : forall {F ks q},
    size
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SQual q id)))
         (update_qual_ctx (remove_nth (qual F) (ks SQual)) F))
    =
    size F.
Proof.
  destruct F; subst; simpl.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : list Size * list Size) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  auto.
Qed.

Lemma size_fctx_subst_loc_alternate : forall {F ks l},
    map
      (fun '(ss1, ss2) =>
         (subst'_sizes (under_ks' ks (subst'_of (ext SLoc l id)))
            ss1,
          subst'_sizes (under_ks' ks (subst'_of (ext SLoc l id)))
            ss2))
      (size
         (update_location_ctx
            (shift_down_after_eq (location F) (ks SLoc) 0) F))
    = size F.
Proof.
  destruct F; subst; simpl.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : list Size * list Size) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  auto.
Qed.

Lemma size_fctx_subst_pretype_alternate : forall {F ks pt},
    map
      (fun '(ss1, ss2) =>
         (subst'_sizes
            (under_ks' ks (subst'_of (ext SPretype pt id))) ss1,
          subst'_sizes
            (under_ks' ks (subst'_of (ext SPretype pt id))) ss2))
      (size
         (update_type_ctx (remove_nth (type F) (ks SPretype)) F))
    =
    size F.
Proof.
  destruct F; subst; simpl.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : list Size * list Size) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  auto.
Qed.

Lemma size_fctx_subst_qual_index_alternate : forall {F ks q},
    map
      (fun '(ss1, ss2) =>
         (subst'_sizes (under_ks' ks (subst'_of (ext SQual q id)))
            ss1,
          subst'_sizes (under_ks' ks (subst'_of (ext SQual q id)))
            ss2))
      (size (update_qual_ctx (remove_nth (qual F) (ks SQual)) F))
    =
    size F.
Proof.
  intros.
  destruct F; subst; simpl in *.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (tpl : list Size * list Size) => tpl); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  erewrite sizes_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ].
  auto.
Qed.

Lemma qual_InstFunctionCtxInd_subst_weak_pretype : forall {F knd ks sz qa hc q},
    knd <> SQual ->
    qual
       (InstFunctionCtxInd_under_ks
          (subst_ext (weak knd)
             (update_type_ctx ((sz, qa, hc) :: type F) F))
          (plus (sing knd 1) ks) (QualI q)) =
    qual (InstFunctionCtxInd_under_ks F ks (QualI q)).
Proof.
  destruct F; subst; simpl in *.
  intros.
  unfold subst'_function_ctx.
  unfold plus; simpl.
  match goal with
  | [ |- context[remove_nth (map ?F _)] ] =>
      replace F with (fun (x : list Qual * list Qual) => x); [ rewrite map_id | ]
  end.
  2:{
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    destruct_prs.
    erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
    2: eapply single_weak_debruijn_weak_conds; eauto.
    2:{
      destruct knd; auto.
      solve_impossibles.
    }
    erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
    - eapply single_weak_debruijn_weak_conds; eauto.
    - destruct knd; auto.
      solve_impossibles.
  }
  destruct knd.
  all:
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; auto
    end.
  all: solve_impossibles.
Qed.

Lemma under_non_size_no_effect_on_size : forall {sz f ks knd' obj knd},
    debruijn_subst_ext_conds f ks knd' obj ->
    knd <> SSize ->
    subst'_size (under' knd f) sz = subst'_size f sz.
Proof.
  induction sz; intros; simpl in *; auto.
  - unfold get_var'.
    unfold under'.
    rewrite under_ks'_unroll.
    handle_ineq.
    -- destruct knd; unfold sing in *; simpl in *; try lia.
       solve_impossibles.
    -- unfold debruijn_subst_ext_conds in *.
       destructAll.
       destruct knd'.
       1-2,4:
         match goal with
         | [ H : context[not (@Logic.eq Ind _ _) -> _] |- _ ] =>
             erewrite H; eauto; solve_ineqs;
             erewrite H; eauto; solve_ineqs
         end.
       1-3: simpl.
       1-3: unfold plus.
       1-3: unfold zero.
       1-3:
         match goal with
         | [ |- ?A ?B = ?A ?C ] => replace B with C by lia; auto
         end.

       destruct knd; solve_impossibles.
       all:
         match goal with
         | [ |- context[?A - sing ?B 1 SSize] ] =>
             replace (A - sing B 1 SSize) with A by ltac:(unfold sing; simpl; lia)
         end.

       all:
         match goal with
         | [ H : context[_ <> ?KS SSize -> _] |- _ _ ?IDX _ = _ ] =>
             let H := fresh "H" in
             assert (H : IDX = KS SSize \/ IDX <> KS SSize) by apply eq_dec_nat;
             case H;
             [ let H' := fresh "H" in intro H'; rewrite H' | intro ]
         end.
       
       1,3,5:
         match goal with
         | [ H : forall _, _ = _ |- _ ] => repeat rewrite H
         end.
       1-3: simpl.
       1-3: rewrite plus_zero.
       1-3: rewrite plus_comm.
       1-3: rewrite <-compose_weak_weaks_size.
       1-3: erewrite weak_non_size_no_effect_on_size.
       3,6,9: eapply single_weak_debruijn_weak_conds; eauto.
       2,4,6: solve_ineqs.
       1-3: rewrite plus_zero; auto.

       all:
         match goal with
         | [ H : context[_ <> _ SSize -> _] |- _ ] =>
             do 2 ltac:(rewrite H; auto)
         end.
  - erewrite IHsz1; eauto.
    erewrite IHsz2; eauto.
Qed.

Lemma under_non_size_no_effect_on_sizes : forall {szs f ks knd knd' obj},
    debruijn_subst_ext_conds f ks knd' obj ->
    knd <> SSize ->
    subst'_sizes (under' knd f) szs = subst'_sizes f szs.
Proof.
  induction szs; intros; auto.
  simpl.
  erewrite IHszs; eauto.
  erewrite under_non_size_no_effect_on_size; eauto.
Qed.

Lemma size_InstFunctionCtxInd_subst_weak_pretype : forall {F knd ks sz qa hc sz'},
    knd <> SSize ->
    size
       (InstFunctionCtxInd_under_ks
          (subst_ext (weak knd)
             (update_type_ctx ((sz, qa, hc) :: type F) F))
          (plus (sing knd 1) ks) (SizeI sz')) =
    size (InstFunctionCtxInd_under_ks F ks (SizeI sz')).
Proof.
  destruct F; subst; simpl in *.
  intros.
  unfold subst'_function_ctx.
  match goal with
  | [ |- context[remove_nth (map ?F _)] ] =>
      replace F with (fun (x : list Size * list Size) => x); [ rewrite map_id | ]
  end.
  2:{
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    destruct_prs.
    erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
    2: eapply single_weak_debruijn_weak_conds; eauto.
    2:{
      destruct knd; auto.
      solve_impossibles.
    }
    erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
    - eapply single_weak_debruijn_weak_conds; eauto.
    - destruct knd; auto.
      solve_impossibles.
  }
  all:
    match goal with
    | [ |- map _ (remove_nth _ (plus ?A ?B SSize)) = _ ] =>
        replace (plus A B SSize) with (B SSize)
    end.
  2:{
    unfold plus.
    destruct knd; auto.
    solve_impossibles.
  }
  
  match goal with
  | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  rewrite <-under_ks_under_ks_subst_of.
  match goal with
  | [ |- context[under_ks' (sing ?KND 1)] ] =>
      replace (under_ks' (sing KND 1)) with (under' KND) by auto
  end.
  erewrite under_non_size_no_effect_on_sizes.
  2:{
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  }
  all: auto.
  erewrite under_non_size_no_effect_on_sizes.
  2:{
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  }
  all: auto.
Qed.

Lemma Function_Ctx_eq : forall {F F'},
    label F = label F' ->
    ret F = ret F' ->
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    linear F = linear F' ->
    F = F'.
Proof.
  destruct F; destruct F'; simpl; intros; subst; auto.
Qed.
       
Lemma InstFunctionCtxInd_under_ks_weak_pretype : forall {F ks idx sz qa hc},
    InstFunctionCtxInd_under_ks
      (subst_ext
         (weak SPretype)
         (update_type_ctx ((sz, qa, hc) :: type F) F))
      (plus (sing SPretype 1) ks)
      idx
    =
    subst_ext
      (weak SPretype)
      (update_type_ctx
         ((subst'_size (under_ks' ks (subst'_of (subst_of_index idx))) sz,
            subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) qa,
            hc)
            ::
            type (InstFunctionCtxInd_under_ks F ks idx))
         (InstFunctionCtxInd_under_ks F ks idx)).
Proof.
  destruct idx; intros; simpl.
  all: unfold subst'_function_ctx; simpl.
  all: apply Function_Ctx_eq; simpl.
  all: repeat rewrite remove_nth_map.
  all: repeat rewrite map_map.
  all: destruct F; simpl; subst.
  all:
    try match goal with
    | [ |- ?A :: ?C = ?B :: ?D ] =>
        replace B with A; [ replace D with C; auto | ]
    end.
  all:
    try match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; [ auto | ]
    end.
  all: try eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_types ?SU ?T] ] =>
        replace (subst'_types SU T) with (subst_ext' SU T) by auto
      end.
  all:
    repeat match goal with
    | [ |- context[subst'_local_ctx ?SU ?T] ] =>
        replace (subst'_local_ctx SU T) with (subst_ext' SU T) by auto
           end.
  all:
    repeat match goal with
    | [ |- context[subst'_qual ?SU ?T] ] =>
        replace (subst'_qual SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_quals ?SU ?T] ] =>
        replace (subst'_quals SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_size ?SU ?T] ] =>
        replace (subst'_size SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_sizes ?SU ?T] ] =>
        replace (subst'_sizes SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite ret_comp.
  all: repeat rewrite linear_comp.
  all: repeat rewrite subst_ext'_assoc.
  all: try rewrite <-under_ks_under_ks_subst_of.
  all:
    try match goal with
    | [ |- context[under_ks' (sing ?KND 1)] ] =>
        replace (under_ks' (sing KND 1)) with (under' KND) by auto
    end.
  all: try rewrite weak_subst_under_ks_comm; auto.
Qed.
       
Lemma InstFunctionCtxInd_under_ks_weak_pretype_add_constraint : forall {F ks idx sz qa hc},
    InstFunctionCtxInd_under_ks
      (subst_ext
         (weak SPretype)
         (update_type_ctx ((sz, qa, hc) :: type F) F))
      (plus (sing SPretype 1) ks)
      idx
    =
    (add_constraints (InstFunctionCtxInd_under_ks F ks idx) [TYPE (subst'_size (under_ks' ks (subst'_of (subst_of_index idx))) sz) (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) qa) hc]).
Proof.
  intros; simpl.
  repeat match goal with
         | [ |- context[subst'_function_ctx (subst'_of ?SU) ?F] ] =>
             replace (subst'_function_ctx (subst'_of SU) F) with (subst_ext SU F) by auto
         end.
  apply InstFunctionCtxInd_under_ks_weak_pretype.
Qed.
       
Lemma InstFunctionCtxInd_under_ks_weak_pretype_loc : forall {F ks l sz qa hc},
    InstFunctionCtxInd_under_ks
      (subst_ext
         (weak SPretype)
         (update_type_ctx ((sz, qa, hc) :: type F) F))
      (plus (sing SPretype 1) ks)
      (LocI l)
    =
    subst_ext
      (weak SPretype)
      (update_type_ctx
         ((sz,
            qa,
            hc)
            ::
            type (InstFunctionCtxInd_under_ks F ks (LocI l)))
         (InstFunctionCtxInd_under_ks F ks (LocI l))).
Proof.
  intros.
  rewrite InstFunctionCtxInd_under_ks_weak_pretype.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.
       
Lemma InstFunctionCtxInd_under_ks_weak_pretype_pretype : forall {F ks pt sz qa hc},
    InstFunctionCtxInd_under_ks
      (subst_ext
         (weak SPretype)
         (update_type_ctx ((sz, qa, hc) :: type F) F))
      (plus (sing SPretype 1) ks)
      (PretypeI pt)
    =
    subst_ext
      (weak SPretype)
      (update_type_ctx
         ((sz,
            qa,
            hc)
            ::
            type (InstFunctionCtxInd_under_ks F ks (PretypeI pt)))
         (InstFunctionCtxInd_under_ks F ks (PretypeI pt))).
Proof.
  intros.
  rewrite InstFunctionCtxInd_under_ks_weak_pretype.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.
       
Lemma InstFunctionCtxInd_under_ks_weak_pretype_qual : forall {F ks l sz qa hc},
    InstFunctionCtxInd_under_ks
      (subst_ext
         (weak SPretype)
         (update_type_ctx ((sz, qa, hc) :: type F) F))
      (plus (sing SPretype 1) ks)
      (QualI l)
    =
    subst_ext
      (weak SPretype)
      (update_type_ctx
         ((sz,
            subst'_qual (under_ks' ks (subst'_of (subst_of_index l))) qa,
            hc)
            ::
            type (InstFunctionCtxInd_under_ks F ks (QualI l)))
         (InstFunctionCtxInd_under_ks F ks (QualI l))).
Proof.
  intros.
  rewrite InstFunctionCtxInd_under_ks_weak_pretype.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma add_non_qual_constraint_no_effect_on_qual : forall {knd qual},
    knd <> SQual ->
    map
      (fun '(qs1, qs2) =>
         (subst'_quals (subst'_of (weak knd)) qs1,
          subst'_quals (subst'_of (weak knd)) qs2))
      qual = qual.
Proof.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (x : list Qual * list Qual) => x); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
  2:{
    eapply single_weak_debruijn_weak_conds; eauto.
  }
  2:{
    destruct knd; simpl; auto.
    solve_impossibles.
  }
  erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
  - eapply single_weak_debruijn_weak_conds; eauto.
  - destruct knd; simpl; auto.
    solve_impossibles.
Qed.

Lemma debruijn_weaks_under_ks : forall {f ks ks' ks''},
    debruijn_weaks_conds f ks ks' ->
    debruijn_weaks_conds (under_ks' ks'' f) (plus ks ks'') ks'.
Proof.
  unfold debruijn_weaks_conds.
  intros.
  destructAll.
  split; intros; unfold plus in *.
  - unfold under_ks'.
    handle_ineq.
    -- unfold var'; auto.
    -- match goal with
       | [ H : context[_ < _ -> _] |- _ ] => rewrite H by lia
       end.
       unfold plus.
       match goal with
       | [ |- VarKind _ ?A = VarKind _ ?B ] =>
           replace B with A by lia
       end.
       auto.
  - unfold under_ks'.
    handle_ineq.
    match goal with
    | [ H : context[_ >= _ -> _] |- _ ] => rewrite H by lia
    end.
    unfold plus.
    match goal with
    | [ |- VarKind _ ?A = VarKind _ ?B ] =>
       replace B with A by lia
    end.
    auto.
Qed.

Lemma weak_plus_non_qual_no_effect_on_qual : forall {knd ks q},
    knd <> SQual ->
    subst'_qual (weaks' (plus (sing knd 1) ks)) q =
    subst'_qual (weaks' ks) q.
Proof.
  intros.
  rewrite <-under_ks_weaks_comp'.
  match goal with
  | [ |- subst'_qual ?SU ?Q = _ ] =>
      replace (subst'_qual SU Q) with (subst_ext' SU Q) by auto
  end.
  rewrite <-subst_ext'_assoc.
  simpl.
  erewrite weak_non_qual_no_effect_on_qual_gen; eauto.
  - eapply debruijn_weaks_under_ks.
    apply simpl_debruijn_weak_conds.
  - destruct knd; simpl; auto.
    solve_impossibles.
Qed.

Lemma weak_plus_non_qual_no_effect_on_quals : forall {knd ks qs},
    knd <> SQual ->
    subst'_quals (weaks' (plus (sing knd 1) ks)) qs =
    subst'_quals (weaks' ks) qs.
Proof.
  induction qs.
  all: intros; simpl; auto.
  rewrite IHqs; auto.
  rewrite weak_plus_non_qual_no_effect_on_qual; auto.
Qed.

Lemma weak_plus_non_size_no_effect_on_size : forall {knd ks sz},
    knd <> SSize ->
    subst'_size (weaks' (plus (sing knd 1) ks)) sz =
    subst'_size (weaks' ks) sz.
Proof.
  intros.
  rewrite <-under_ks_weaks_comp'.
  match goal with
  | [ |- subst'_size ?SU ?Q = _ ] =>
      replace (subst'_size SU Q) with (subst_ext' SU Q) by auto
  end.
  rewrite <-subst_ext'_assoc.
  simpl.
  erewrite weak_non_size_no_effect_on_size_gen; eauto.
  - eapply debruijn_weaks_under_ks.
    apply simpl_debruijn_weak_conds.
  - destruct knd; simpl; auto.
    solve_impossibles.
Qed.

Lemma weak_plus_non_size_no_effect_on_sizes : forall {knd ks szs},
    knd <> SSize ->
    subst'_sizes (weaks' (plus (sing knd 1) ks)) szs =
    subst'_sizes (weaks' ks) szs.
Proof.
  induction szs.
  all: intros; simpl; auto.
  rewrite IHszs; auto.
  rewrite weak_plus_non_size_no_effect_on_size; auto.
Qed.

Lemma under_non_qual_no_effect_on_quals : forall {qs f ks knd' obj knd},
    debruijn_subst_ext_conds f ks knd' obj ->
    knd <> SQual ->
    subst'_quals (under' knd f) qs = subst'_quals f qs.
Proof.
  induction qs; intros; auto.
  simpl.
  erewrite under_non_qual_no_effect_on_qual; eauto.
  erewrite IHqs; eauto.
Qed.

Lemma add_non_size_constraint_no_effect_on_size : forall {knd size},
    knd <> SSize ->
    map
      (fun '(szs1, szs2) =>
         (subst'_sizes (subst'_of (weak knd)) szs1,
          subst'_sizes (subst'_of (weak knd)) szs2))
      size = size.
Proof.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (x : list Size * list Size) => x); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
  2:{
    eapply single_weak_debruijn_weak_conds; eauto.
  }
  2:{
    destruct knd; simpl; auto.
    solve_impossibles.
  }
  erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
  - eapply single_weak_debruijn_weak_conds; eauto.
  - destruct knd; simpl; auto.
    solve_impossibles.
Qed.

Lemma InstIndValid_at_subst_weak_pretype : forall {F ks idx sz qa hc},
    InstIndValid_at F ks idx ->
    InstIndValid_at (subst_ext (weak SPretype) (update_type_ctx ((sz, qa, hc) :: type F) F)) (plus (sing SPretype 1) ks) idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - constructor 1.
    simpl.
    destruct F; simpl in *; subst.
    unfold plus; simpl.
    lia.
  - constructor 2.
    -- simpl.
       destruct F; simpl in *; subst.
       unfold plus; simpl.
       lia.
    -- econstructor.
       match goal with
       | [ X : Loc |- _ ] => destruct X
       end.
       2:{ simpl; econstructor; eauto. }
       simpl in *.
       unfold get_var' in *.
       unfold weaks' in *.
       unfold var in *.
       simpl in *.
       unfold plus.
       simpl.
       match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       match goal with
       | [ H : LocValid _ _ |- _ ] => inv H
       end.
       all:
         match goal with
         | [ H : LocV _ = _ |- _ ] => inv H
         end.
       destruct F; subst; simpl in *; auto.
       econstructor 2; eauto.
  - constructor 3.
    destruct F; simpl in *; subst; auto.
    rewrite add_non_qual_constraint_no_effect_on_qual.
    2: solve_ineqs.
    auto.
  - econstructor 4.
    -- destruct F; simpl in *; subst; auto.
       rewrite add_non_qual_constraint_no_effect_on_qual.
       2: solve_ineqs.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       all: rewrite qual_InstFunctionCtxInd_subst_weak_pretype.
       all: solve_ineqs.
       all: rewrite weak_plus_non_qual_no_effect_on_qual.
       all: solve_ineqs.
       
       2-3:
         try match goal with
           | [ |- context[under_ks' (plus (sing ?TYP 1) ?KS) ?SU] ] =>
               replace (under_ks' (plus (sing TYP 1) KS) SU) with
               (under' TYP (under_ks' KS SU))
           end.
       3,5: unfold under'.
       3-4: rewrite under_ks_under_ks_subst_of; auto.
       2-3: erewrite under_non_qual_no_effect_on_quals.
       3,6: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       all: solve_ineqs.
       all: auto.
  - constructor 5.
    unfold plus; simpl.
    destruct F; subst; simpl in *.
    rewrite add_non_size_constraint_no_effect_on_size.
    2: solve_ineqs.
    auto.
  - econstructor 6.
    -- unfold plus; simpl.
       destruct F; subst; simpl in *.
       rewrite add_non_size_constraint_no_effect_on_size.
       2: solve_ineqs.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       all: rewrite size_InstFunctionCtxInd_subst_weak_pretype.
       all: solve_ineqs.
       all: rewrite weak_plus_non_size_no_effect_on_size.
       all: solve_ineqs.
       
       2-3:
         try match goal with
           | [ |- context[under_ks' (plus (sing ?TYP 1) ?KS) ?SU] ] =>
               replace (under_ks' (plus (sing TYP 1) KS) SU) with
               (under' TYP (under_ks' KS SU))
           end.
       3,5: unfold under'.
       3-4: rewrite under_ks_under_ks_subst_of; auto.
       2-3: erewrite under_non_size_no_effect_on_sizes.
       3,6: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       all: solve_ineqs.
       all: auto.
  - constructor 7.
    destruct F; subst; simpl in *.
    rewrite weak_pretype_on_tctx.
    unfold plus; simpl.
    auto.
  - econstructor 8.
    -- unfold plus; simpl.
       rewrite weak_pretype_on_tctx.
       destruct F; subst; simpl in *.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       --- rewrite InstFunctionCtxInd_under_ks_weak_pretype.
           match goal with
           | [ H : sizeOfPretype ?T _ = _
               |- sizeOfPretype ?T2 _ = _ ] =>
               match goal with
               | [ |- context[update_type_ctx ?NEWT] ] =>
                   replace T2 with NEWT
               end
           end.
           2:{
             match goal with
             | [ |- _ :: type ?FP = _ ] =>
                 remember FP as F'; destruct F'
             end.
             simpl in *.
             rewrite weak_pretype_on_tctx; auto.
             rewrite pretype_weak_no_effect_on_size.
             rewrite pretype_weak_no_effect_on_qual.
             auto.
           }
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           match goal with
           | [ |- context[?A :: ?B] ] =>
               replace (A :: B) with ([A] ++ B) by auto
           end.
           rewrite <-weaks'_sing.
           erewrite sizeOfPretype_weaks.
           ---- simpl.
                match goal with
                | [ H : sizeOfPretype _ _ = _ |- _ ] => rewrite H
                end.
                simpl.
                eauto.
           ---- simpl; auto.
           ---- apply map_ext.
                intros.
                destruct_prs.
                rewrite weaks'_sing.
                rewrite pretype_weak_no_effect_on_size; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_pretype.
           rewrite pretype_weak_no_effect_on_size_field.
           rewrite size_update_type_ctx.
           rewrite weaks'_sing.
           rewrite pretype_weak_no_effect_on_size; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_pretype.
           rewrite pretype_weak_no_effect_on_size_field.
           rewrite size_update_type_ctx; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_pretype.
           match goal with
           | [ H : SizeLeq ?T _ _ = _
               |- SizeLeq ?T2 _ _ = _ ] =>
               replace T2 with T
           end.
           2:{
             match goal with
             | [ |- size ?FP = _ ] =>
                 remember FP as F'; destruct F'
             end.
             simpl in *.
             rewrite add_non_size_constraint_no_effect_on_size; auto.
             solve_ineqs.
           }
           rewrite weaks'_sing.
           rewrite pretype_weak_no_effect_on_size; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_pretype_add_constraint.
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           match goal with
           | [ |- context[QualT (subst_ext' ?SU ?PT) ?Q] ] =>
               replace (QualT (subst_ext' SU PT) Q) with (subst'_type SU (QualT PT Q))
           end.
           2:{
             simpl.
             rewrite pretype_weak_no_effect_on_qual; auto.
           }
           eapply TypeValid_add_constraint_pretype; eauto.
           apply single_weak_debruijn_weak_conds.
       --- intros.
           match goal with
           | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
           end.
           rewrite InstFunctionCtxInd_under_ks_weak_pretype.
           match goal with
           | [ H : context[heapable ?F] |- context[heapable ?FP] ] =>
               match goal with
               | [ |- context[(_, _, ?HC)] ] =>
                   replace (heapable FP) with (HC :: (heapable F))
               end
           end.
           2:{
             match goal with
             | [ |- _ :: heapable ?F = heapable ?FP ] => generalize F
             end.
             intro F'; destruct F'; simpl in *.
             unfold subst'_function_ctx in *; simpl.
             unfold heapable; simpl.
             rewrite weak_pretype_on_tctx; auto.
           }
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           apply NoCapsPretype_subst_weak; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_unroll_loc : forall {F ks l},
    InstFunctionCtxInd_under_ks F ks (LocI l) =
    subst'_function_ctx
      (under_ks' ks (subst'_of (ext SLoc l id)))
      (update_location_ctx
         (shift_down_after_eq (location F) (ks SLoc) 0) F).
Proof.
  simpl; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_unroll_qual : forall {F ks q},
    InstFunctionCtxInd_under_ks F ks (QualI q) =
    subst'_function_ctx
      (under_ks' ks (subst'_of (ext SQual q id)))
      (update_qual_ctx (remove_nth (qual F) (ks SQual)) F).
Proof.
  simpl; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_unroll_size : forall {F ks sz},
    InstFunctionCtxInd_under_ks F ks (SizeI sz) =
    subst'_function_ctx
      (under_ks' ks (subst'_of (ext SSize sz id)))
      (update_size_ctx (remove_nth (size F) (ks SSize)) F).
Proof.
  simpl; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_unroll_pretype : forall {F ks pt},
    InstFunctionCtxInd_under_ks F ks (PretypeI pt) =
    subst'_function_ctx
      (under_ks' ks (subst'_of (ext SPretype pt id)))
      (update_type_ctx (remove_nth (type F) (ks SPretype)) F).
Proof.
  simpl; auto.
Qed.

Lemma InstIndValid_at_Function_Ctx_stronger : forall {F ks idx F'},
    location F = location F' ->
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    InstIndValid_at F ks idx ->
    InstIndValid_at F' ks idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - constructor 1; lia.
  - constructor 2.
    -- lia.
    -- eapply InstIndValid_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; destruct F'; simpl in *; subst; auto.
  - constructor 3.
    destruct F; destruct F'; simpl in *; subst; auto.
  - econstructor 4.
    -- destruct F; destruct F'; simpl in *; subst; eauto.
    -- eapply InstIndValid_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; destruct F'; simpl in *; subst; auto.
  - constructor 5.
    destruct F; destruct F'; simpl in *; subst; auto.
  - econstructor 6.
    -- destruct F; destruct F'; simpl in *; subst; eauto.
    -- eapply InstIndValid_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; destruct F'; simpl in *; subst; auto.
  - constructor 7.
    destruct F; destruct F'; simpl in *; subst; auto.
  - econstructor 8.
    -- destruct F; destruct F'; simpl in *; subst; eauto.
    -- eapply InstIndValid_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; destruct F'; simpl in *; subst; auto.
Qed.

Lemma qual_InstFunctionCtxInd_subst_weak_loc : forall {F knd ks q},
  knd <> SQual ->
  qual
    (InstFunctionCtxInd_under_ks
       (subst_ext (weak knd)
          (update_location_ctx (location F + 1) F))
       (plus (sing knd 1) ks) (QualI q))
  =
    qual (InstFunctionCtxInd_under_ks F ks (QualI q)).
Proof.
  destruct F; subst; simpl in *.
  intros.
  unfold subst'_function_ctx.
  unfold plus; simpl.
  match goal with
  | [ |- context[remove_nth (map ?F _)] ] =>
      replace F with (fun (x : list Qual * list Qual) => x); [ rewrite map_id | ]
  end.
  2:{
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    destruct_prs.
    erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
    2: eapply single_weak_debruijn_weak_conds; eauto.
    2:{
      destruct knd; auto.
      solve_impossibles.
    }
    erewrite weak_non_qual_no_effect_on_quals_gen; eauto.
    - eapply single_weak_debruijn_weak_conds; eauto.
    - destruct knd; auto.
      solve_impossibles.
  }
  destruct knd.
  all:
    match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; auto
    end.
  all: solve_impossibles.
Qed.

Lemma size_InstFunctionCtxInd_subst_weak_loc : forall {F knd ks sz},
  knd <> SSize ->
  size
    (InstFunctionCtxInd_under_ks
       (subst_ext (weak knd)
          (update_location_ctx (location F + 1) F))
       (plus (sing knd 1) ks) (SizeI sz))
  =
    size (InstFunctionCtxInd_under_ks F ks (SizeI sz)).
Proof.
  destruct F; subst; simpl in *.
  intros.
  unfold subst'_function_ctx.
  match goal with
  | [ |- context[remove_nth (map ?F _)] ] =>
      replace F with (fun (x : list Size * list Size) => x); [ rewrite map_id | ]
  end.
  2:{
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    destruct_prs.
    erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
    2: eapply single_weak_debruijn_weak_conds; eauto.
    2:{
      destruct knd; auto.
      solve_impossibles.
    }
    erewrite weak_non_size_no_effect_on_sizes_gen; eauto.
    - eapply single_weak_debruijn_weak_conds; eauto.
    - destruct knd; auto.
      solve_impossibles.
  }
  all:
    match goal with
    | [ |- map _ (remove_nth _ (plus ?A ?B SSize)) = _ ] =>
        replace (plus A B SSize) with (B SSize)
    end.
  2:{
    unfold plus.
    destruct knd; auto.
    solve_impossibles.
  }
  
  match goal with
  | [ |- map ?F1 _ = map ?F2 _ ] =>
      replace F2 with F1; auto
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  rewrite <-under_ks_under_ks_subst_of.
  match goal with
  | [ |- context[under_ks' (sing ?KND 1)] ] =>
      replace (under_ks' (sing KND 1)) with (under' KND) by auto
  end.
  erewrite under_non_size_no_effect_on_sizes.
  2:{
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  }
  all: auto.
  erewrite under_non_size_no_effect_on_sizes.
  2:{
    eapply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  }
  all: auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_weak_loc : forall {F ks idx},
    InstFunctionCtxInd_under_ks
      (subst_ext (weak SLoc) (update_location_ctx (location F + 1) F))
      (plus (sing SLoc 1) ks)
      idx
    =
    subst_ext (weak SLoc)
      (update_location_ctx
         (location (InstFunctionCtxInd_under_ks F ks idx) + 1)
         (InstFunctionCtxInd_under_ks F ks idx)).
Proof.
  destruct idx; simpl.
  all: unfold subst'_function_ctx; simpl.
  all: apply Function_Ctx_eq; simpl.
  all: repeat rewrite remove_nth_map.
  all: repeat rewrite map_map.
  all: destruct F; simpl; subst.
  all:
    try match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; [ auto | ]
    end.
  all: try eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_types ?SU ?T] ] =>
        replace (subst'_types SU T) with (subst_ext' SU T) by auto
      end.
  all:
    repeat match goal with
    | [ |- context[subst'_local_ctx ?SU ?T] ] =>
        replace (subst'_local_ctx SU T) with (subst_ext' SU T) by auto
           end.
  all:
    repeat match goal with
    | [ |- context[subst'_qual ?SU ?T] ] =>
        replace (subst'_qual SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_quals ?SU ?T] ] =>
        replace (subst'_quals SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_size ?SU ?T] ] =>
        replace (subst'_size SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_sizes ?SU ?T] ] =>
        replace (subst'_sizes SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite ret_comp.
  all: repeat rewrite linear_comp.
  all: repeat rewrite subst_ext'_assoc.
  all: try rewrite <-under_ks_under_ks_subst_of.
  all:
    try match goal with
    | [ |- context[under_ks' (sing ?KND 1)] ] =>
        replace (under_ks' (sing KND 1)) with (under' KND) by auto
    end.
  all: try rewrite weak_subst_under_ks_comm; auto.

  unfold shift_down_after_eq.
  repeat handle_ineq_le.
  all: unfold plus in *.
  all: simpl in *.
  all: lia.
Qed.

Lemma loc_weak_no_effect_on_size_field : forall {F},
    size (subst_ext (weak SLoc) F) = size F.
Proof.
  destruct F; simpl; auto.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  repeat rewrite loc_weak_no_effect_on_sizes.
  auto.
Qed.

Lemma InstIndValid_at_subst_weak_loc : forall {F ks idx},
    InstIndValid_at F ks idx ->
    InstIndValid_at (subst_ext (weak SLoc) (update_location_ctx (location F + 1) F)) (plus (sing SLoc 1) ks) idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - constructor 1.
    simpl.
    destruct F; simpl in *; subst.
    unfold plus; simpl.
    lia.
  - constructor 2.
    -- destruct F; simpl in *; subst.
       unfold plus; simpl.
       lia.
    -- econstructor.
       simpl.
       match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       simpl in *.
       destruct F; subst; simpl in *.
       unfold plus.
       destruct l.
       --- simpl in *.
           unfold get_var' in *.
           unfold weaks' in *.
           unfold var in *.
           unfold shift_down_after_eq in *.
           handle_ineq_le.
           ---- match goal with
                | [ H : context[if ?B then _ else _] |- _ ] =>
                    replace B with true in H
                end.
                2:{
                  apply eq_sym.
                  rewrite OrdersEx.Nat_as_DT.leb_le.
                  lia.
                }
                unfold zero in *.
                simpl in *.
                match goal with
                | [ H : LocValid _ _ |- _ ] => inv H
                end.
                all:
                  match goal with
                  | [ H : LocV _ = _ |- _ ] => inv H
                  end.
                econstructor 2; eauto.
                lia.
           ---- match goal with
                | [ H : context[if ?B then _ else _] |- _ ] =>
                    replace B with false in H
                end.
                2:{
                  apply eq_sym.
                  rewrite OrdersEx.Nat_as_DT.leb_gt.
                  lia.
                }
                unfold zero in *.
                simpl in *.
                match goal with
                | [ H : LocValid _ _ |- _ ] => inv H
                end.
                all:
                  match goal with
                  | [ H : LocV _ = _ |- _ ] => inv H
                  end.
                econstructor 2; eauto.
                lia.
       --- simpl in *.
           econstructor; eauto.
  - constructor 3.
    unfold plus; simpl.
    destruct F; subst; simpl in *.
    rewrite add_non_qual_constraint_no_effect_on_qual.
    2: solve_ineqs.
    auto.
  - econstructor 4.
    -- unfold plus; simpl.
       destruct F; subst; simpl in *.
       rewrite add_non_qual_constraint_no_effect_on_qual.
       2: solve_ineqs.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       all: rewrite qual_InstFunctionCtxInd_subst_weak_loc.
       all: solve_ineqs.
       all: rewrite weak_plus_non_qual_no_effect_on_qual.
       all: solve_ineqs.
       
       2-3:
         try match goal with
           | [ |- context[under_ks' (plus (sing ?TYP 1) ?KS) ?SU] ] =>
               replace (under_ks' (plus (sing TYP 1) KS) SU) with
               (under' TYP (under_ks' KS SU))
           end.
       3,5: unfold under'.
       3-4: rewrite under_ks_under_ks_subst_of; auto.
       2-3: erewrite under_non_qual_no_effect_on_quals.
       3,6: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       all: solve_ineqs.
       all: auto.
  - constructor 5.
    unfold plus; simpl.
    destruct F; subst; simpl in *.
    rewrite add_non_size_constraint_no_effect_on_size.
    2: solve_ineqs.
    auto.
  - econstructor 6.
    -- unfold plus; simpl.
       destruct F; subst; simpl in *.
       rewrite add_non_size_constraint_no_effect_on_size.
       2: solve_ineqs.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       all: rewrite size_InstFunctionCtxInd_subst_weak_loc.
       all: solve_ineqs.
       all: rewrite weak_plus_non_size_no_effect_on_size.
       all: solve_ineqs.
       
       2-3:
         try match goal with
           | [ |- context[under_ks' (plus (sing ?TYP 1) ?KS) ?SU] ] =>
               replace (under_ks' (plus (sing TYP 1) KS) SU) with
               (under' TYP (under_ks' KS SU))
           end.
       3,5: unfold under'.
       3-4: rewrite under_ks_under_ks_subst_of; auto.
       2-3: erewrite under_non_size_no_effect_on_sizes.
       3,6: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       all: solve_ineqs.
       all: auto.
  - constructor 7.
    destruct F; subst; simpl in *.
    rewrite weak_loc_on_tctx.
    unfold plus; simpl.
    auto.
  - econstructor 8.
    -- unfold plus; simpl.
       rewrite weak_loc_on_tctx.
       destruct F; subst; simpl in *.
       eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       
       econstructor.
       --- rewrite InstFunctionCtxInd_under_ks_weak_loc.
           match goal with
           | [ H : sizeOfPretype ?T _ = _
               |- sizeOfPretype ?T2 _ = _ ] =>
               replace T2 with T
           end.
           2:{
             match goal with
             | [ |- type ?FP = _ ] =>
                 remember FP as F'; destruct F'
             end.
             simpl in *.
             rewrite weak_loc_on_tctx; auto.
           }
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           simpl in *.
           erewrite sizeOfPretype_weaks_only_size_matters; eauto.
           ----- apply single_weak_debruijn_weak_conds.
           ----- simpl; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_loc.
           rewrite loc_weak_no_effect_on_size_field.
           rewrite size_update_location_ctx.
           auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_loc.
           rewrite loc_weak_no_effect_on_size_field.
           rewrite size_update_location_ctx; auto.
       --- rewrite InstFunctionCtxInd_under_ks_weak_loc.
           match goal with
           | [ H : SizeLeq ?T _ _ = _
               |- SizeLeq ?T2 _ _ = _ ] =>
               replace T2 with T; auto
           end.
           match goal with
           | [ |- size ?FP = _ ] =>
               remember FP as F'; destruct F'
           end.
           simpl in *.
           rewrite add_non_size_constraint_no_effect_on_size; auto.
           solve_ineqs.
       --- rewrite InstFunctionCtxInd_under_ks_weak_loc.
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           match goal with
           | [ H : TypeValid ?F _ |- TypeValid ?FP _ ] =>
               replace FP with (add_constraints F [LOC]) by auto
           end.
           match goal with
           | [ |- context[QualT (subst_ext' ?SU ?PT) ?Q] ] =>
               replace (QualT (subst_ext' SU PT) Q) with (subst'_type SU (QualT PT Q))
           end.
           2:{
             simpl.
             rewrite loc_weak_no_effect_on_qual; auto.
           }
           eapply TypeValid_add_constraint_loc; eauto.
           apply single_weak_debruijn_weak_conds.
       --- intros.
           match goal with
           | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
           end.
           rewrite InstFunctionCtxInd_under_ks_weak_loc.
           match goal with
           | [ H : context[heapable ?F] |- context[heapable ?FP] ] =>
               replace (heapable FP) with (heapable F)
           end.
           2:{
             match goal with
             | [ |- heapable ?F = heapable ?FP ] => generalize F
             end.
             intro F'; destruct F'; simpl in *.
             unfold subst'_function_ctx in *; simpl.
             unfold heapable; simpl.
             rewrite weak_loc_on_tctx; auto.
           }
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?SU ?PT] ] =>
               replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
           end.
           rewrite <-subst_ext'_assoc.
           rewrite NoCapsPretype_subst_weak_SLoc; auto.
Qed.

Lemma location_update_size_ctx : forall {F szctx},
    location (update_size_ctx szctx F) = location F.
Proof.
  destruct F; auto.
Qed.

Lemma location_update_location_ctx : forall {F lctx},
    location (update_location_ctx lctx F) = lctx.
Proof.
  destruct F; auto.
Qed.

Lemma non_loc_weak_no_effect_on_loc : forall {knd ks},
    knd <> SLoc ->
    subst'_loc (weaks' (plus (sing knd 1) ks)) = subst'_loc (weaks' ks).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro l.
  destruct l; simpl; auto.
  intros.
  unfold get_var'.
  unfold weaks'.
  unfold var.
  simpl.
  match goal with
  | [ |- LocV ?A = LocV ?B ] =>
      replace B with A; auto
  end.
  unfold plus; unfold zero.
  destruct knd; simpl; try lia.
  solve_impossibles.
Qed.

Lemma non_qual_weak_no_effect_on_qual : forall {knd ks},
    knd <> SQual ->
    subst'_qual (weaks' (plus (sing knd 1) ks)) = subst'_qual (weaks' ks).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro q.
  destruct q; simpl; auto.
  unfold get_var'.
  unfold weaks'.
  unfold var.
  simpl.
  match goal with
  | [ |- QualVar ?A = QualVar ?B ] =>
      replace B with A; auto
  end.
  unfold plus; unfold zero; simpl.
  destruct knd; simpl; try lia.
  solve_impossibles.
Qed.

Lemma under_ks_non_qual_no_effect_on_qual : forall {ks knd su},
    knd <> SQual ->
    subst'_qual
      (under_ks' (plus (sing knd 1) ks)
         (subst'_of su))
    =
    subst'_qual
      (under_ks' ks
         (subst'_of su)).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro q.
  destruct q; simpl; auto.
  unfold get_var'.
  unfold under_ks'.
  match goal with
  | [ |- context[plus ?A ?B SQual] ] =>
      replace (plus A B SQual) with (B SQual)
  end.
  2:{
    unfold plus; destruct knd; simpl; auto.
    solve_impossibles.
  }
  handle_ineq; auto.
  do 2 rewrite plus_zero.
  rewrite non_qual_weak_no_effect_on_qual; auto.
Qed.

Lemma under_ks_non_qual_no_effect_on_quals : forall {ks knd su},
    knd <> SQual ->
    subst'_quals
      (under_ks' (plus (sing knd 1) ks)
         (subst'_of su))
    =
    subst'_quals
      (under_ks' ks
         (subst'_of su)).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro qs.
  induction qs; auto.
  simpl.
  rewrite under_ks_non_qual_no_effect_on_qual; auto.
  rewrite IHqs; auto.
Qed.

Lemma qual_update_size_ctx : forall {F szctx},
    qual (update_size_ctx szctx F) = qual F.
Proof.
  destruct F; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_weak_qual : forall {F ks idx qs0 qs1},
    InstFunctionCtxInd_under_ks
      (subst_ext (weak SQual) (update_qual_ctx ((qs0, qs1) :: qual F) F))
      (plus (sing SQual 1) ks)
      idx
    =
    subst_ext (weak SQual)
      (update_qual_ctx
         ((subst'_quals (under_ks' ks (subst'_of (subst_of_index idx))) qs0, subst'_quals (under_ks' ks (subst'_of (subst_of_index idx))) qs1) :: qual (InstFunctionCtxInd_under_ks F ks idx))
         (InstFunctionCtxInd_under_ks F ks idx)).
Proof.
  intros.
  destruct idx; simpl.
  all: unfold subst'_function_ctx; simpl.
  all: apply Function_Ctx_eq; simpl.
  all: repeat rewrite remove_nth_map.
  all: repeat rewrite map_map.
  all: destruct F; simpl; subst.
  all:
    try match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; [ auto | ]
    end.
  all: try eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_types ?SU ?T] ] =>
        replace (subst'_types SU T) with (subst_ext' SU T) by auto
      end.
  all:
    repeat match goal with
    | [ |- context[subst'_local_ctx ?SU ?T] ] =>
        replace (subst'_local_ctx SU T) with (subst_ext' SU T) by auto
           end.
  all:
    repeat match goal with
    | [ |- context[subst'_qual ?SU ?T] ] =>
        replace (subst'_qual SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_quals ?SU ?T] ] =>
        replace (subst'_quals SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_size ?SU ?T] ] =>
        replace (subst'_size SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_sizes ?SU ?T] ] =>
        replace (subst'_sizes SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite ret_comp.
  all: repeat rewrite linear_comp.
  all: repeat rewrite subst_ext'_assoc.
  all: try rewrite <-under_ks_under_ks_subst_of.
  all:
    try match goal with
    | [ |- context[under_ks' (sing ?KND 1)] ] =>
        replace (under_ks' (sing KND 1)) with (under' KND) by auto
    end.
  all: try rewrite weak_subst_under_ks_comm; auto.

  all:
    try match goal with
    | [ |- ?A :: ?B = ?A :: ?C ] => replace C with B; auto
      end.
  all: apply map_ext.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_quals ?SU ?T] ] =>
        replace (subst'_quals SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite subst_ext'_assoc.
  all: rewrite weak_subst_under_ks_comm; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_weak_size : forall {F ks idx szs0 szs1},
    InstFunctionCtxInd_under_ks
      (subst_ext (weak SSize) (update_size_ctx ((szs0, szs1) :: size F) F))
      (plus (sing SSize 1) ks)
      idx
    =
    subst_ext (weak SSize)
      (update_size_ctx
         ((subst'_sizes (under_ks' ks (subst'_of (subst_of_index idx))) szs0, subst'_sizes (under_ks' ks (subst'_of (subst_of_index idx))) szs1) :: size (InstFunctionCtxInd_under_ks F ks idx))
         (InstFunctionCtxInd_under_ks F ks idx)).
Proof.
  intros.
  destruct idx; simpl.
  all: unfold subst'_function_ctx; simpl.
  all: apply Function_Ctx_eq; simpl.
  all: repeat rewrite remove_nth_map.
  all: repeat rewrite map_map.
  all: destruct F; simpl; subst.
  all:
    try match goal with
    | [ |- map ?F1 _ = map ?F2 _ ] =>
        replace F2 with F1; [ auto | ]
    end.
  all: try eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_types ?SU ?T] ] =>
        replace (subst'_types SU T) with (subst_ext' SU T) by auto
      end.
  all:
    repeat match goal with
    | [ |- context[subst'_local_ctx ?SU ?T] ] =>
        replace (subst'_local_ctx SU T) with (subst_ext' SU T) by auto
           end.
  all:
    repeat match goal with
    | [ |- context[subst'_qual ?SU ?T] ] =>
        replace (subst'_qual SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_quals ?SU ?T] ] =>
        replace (subst'_quals SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_size ?SU ?T] ] =>
        replace (subst'_size SU T) with (subst_ext' SU T) by auto
    end.
  all:
    repeat match goal with
    | [ |- context[subst'_sizes ?SU ?T] ] =>
        replace (subst'_sizes SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite ret_comp.
  all: repeat rewrite linear_comp.
  all: repeat rewrite subst_ext'_assoc.
  all: try rewrite <-under_ks_under_ks_subst_of.
  all:
    try match goal with
    | [ |- context[under_ks' (sing ?KND 1)] ] =>
        replace (under_ks' (sing KND 1)) with (under' KND) by auto
    end.
  all: try rewrite weak_subst_under_ks_comm; auto.

  all:
    try match goal with
    | [ |- ?A :: ?B = ?A :: ?C ] => replace C with B; auto
      end.
  all: apply map_ext.
  all: intros.
  all: destruct_prs.
  all:
    repeat match goal with
    | [ |- context[subst'_sizes ?SU ?T] ] =>
        replace (subst'_sizes SU T) with (subst_ext' SU T) by auto
    end.
  all: repeat rewrite subst_ext'_assoc.
  all: rewrite weak_subst_under_ks_comm; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_add_constraint : forall {kv F ks idx},
    add_constraint (InstFunctionCtxInd_under_ks F ks idx) (subst'_kindvar (under_ks' ks (subst'_of (subst_of_index idx))) kv) =
    InstFunctionCtxInd_under_ks
      (add_constraint F kv)
	  (plus (sing (kind_of_kindvar kv) 1) ks)
      idx.
Proof.
  destruct kv; intros; simpl.
  - match goal with
    | [ |- context[subst'_function_ctx (subst'_of ?SU) ?F] ] =>
        replace (subst'_function_ctx (subst'_of SU) F) with (subst_ext SU F) by auto
    end.
    rewrite <-InstFunctionCtxInd_under_ks_weak_loc.
    simpl; auto.
  - match goal with
    | [ |- context[subst'_function_ctx (subst'_of ?SU) ?F] ] =>
        replace (subst'_function_ctx (subst'_of SU) F) with (subst_ext SU F) by auto
    end.
    rewrite <-InstFunctionCtxInd_under_ks_weak_qual.
    simpl; auto.
  - match goal with
    | [ |- context[subst'_function_ctx (subst'_of ?SU) ?F] ] =>
        replace (subst'_function_ctx (subst'_of SU) F) with (subst_ext SU F) by auto
    end.
    rewrite <-InstFunctionCtxInd_under_ks_weak_size.
    simpl; auto.
  - match goal with
    | [ |- context[subst'_function_ctx (subst'_of ?SU) ?F] ] =>
        replace (subst'_function_ctx (subst'_of SU) F) with (subst_ext SU F) by auto
    end.
    rewrite <-InstFunctionCtxInd_under_ks_weak_pretype.
    simpl; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_add_constraints : forall {kvs F ks idx},
    add_constraints (InstFunctionCtxInd_under_ks F ks idx) (subst'_kindvars (under_ks' ks (subst'_of (subst_of_index idx))) kvs) =
    InstFunctionCtxInd_under_ks
      (add_constraints F kvs)
      (plus (ks_of_kvs kvs) ks)
      idx.
Proof.
  induction kvs; auto.
  intros; simpl.
  rewrite InstFunctionCtxInd_under_ks_add_constraint.
  unfold under_kindvar'.
  unfold under'.
  rewrite under_ks_under_ks_subst_of.
  rewrite IHkvs.
  match goal with
  | [ |- InstFunctionCtxInd_under_ks _ ?F1 _ =
	     InstFunctionCtxInd_under_ks _ ?F2 _ ] =>
      replace F2 with F1; auto
  end.
  rewrite plus_assoc.
  match goal with
  | [ |- plus (plus ?A ?B) _ = _ ] =>
      replace (plus A B) with (plus B A); auto
  end.
  apply plus_comm.
Qed.

Lemma type_subst_weak_size : forall {F szctx},
    type (subst_ext (weak SSize) (update_size_ctx szctx F)) =
    map (fun '(sz, q, hc) => (subst'_size (subst'_of (weak SSize)) sz, q, hc)) (type F).
Proof.
  intros.
  destruct F; simpl in *.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite size_weak_no_effect_on_qual; auto.
Qed.

Lemma size_weak_on_size_field : forall {F},
    size (subst_ext (weak SSize) F) =
    map
      (fun '(szs0, szs1) =>
         (subst'_sizes (subst'_of (weak SSize)) szs0,
          subst'_sizes (subst'_of (weak SSize)) szs1))
      (size F).
Proof.
  destruct F; auto.
Qed.

Lemma NoCapsPretype_subst_weak_non_pretype : forall {pt hc f ks knd},
    knd <> SPretype ->
    debruijn_weaks_conds f ks (sing knd 1) ->
    NoCapsPretype hc pt = true ->
    NoCapsPretype hc (subst'_pretype f pt) = true.
Proof.
  eapply
    (Pretype_ind'
       (fun pt =>
          forall hc f ks knd,
            knd <> SPretype ->
            debruijn_weaks_conds f ks (sing knd 1) ->
            NoCapsPretype hc pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks knd,
            knd <> SPretype ->
            debruijn_weaks_conds f ks (sing knd 1) ->
            NoCapsTyp hc t = true ->
            NoCapsTyp hc (subst'_type f t) = true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).
  all: intros; simpl in *; auto.

  - eauto.
  - unfold get_var'.
    erewrite weak_no_effect_on_other_vars; eauto.
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

Lemma InstIndValid_at_subst_weak_size : forall {F ks idx szs0 szs1},
    InstIndValid_at F ks idx ->
    InstIndValid_at (subst_ext (weak SSize) (update_size_ctx ((szs0, szs1) :: size F) F)) (plus (sing SSize 1) ks) idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - constructor 1.
    simpl.
    destruct F; simpl in *; subst.
    unfold plus; simpl.
    lia.
  - constructor 2.
    -- destruct F; simpl in *.
       unfold plus; simpl; lia.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       simpl in *.
       rewrite location_update_size_ctx.
       match goal with
       | [ H : LocValid _ _ |- _ ] =>
           rewrite location_update_location_ctx in H
       end.
       rewrite non_loc_weak_no_effect_on_loc; [ | solve_ineqs ].
       unfold plus; simpl; auto.
  - constructor 3.
    destruct F; simpl in *.
    unfold plus; simpl.
    rewrite add_non_qual_constraint_no_effect_on_qual; auto.
    solve_ineqs.
  - econstructor 4.
    -- destruct F; simpl in *.
       unfold plus; simpl.
       rewrite add_non_qual_constraint_no_effect_on_qual; eauto.
       solve_ineqs.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       all: simpl in *.
       2-3: rewrite under_ks_non_qual_no_effect_on_quals.
       all: try solve_ineqs.
       2-3: prepare_Forall.
       2-3:
         match goal with
         | [ H : In _ (subst'_quals _ _) |- _ ] =>
             unfold subst'_quals in H; apply in_map_inv in H
         end.
       2-3: destructAll.
       2-3: repeat split.
       all: try rewrite weak_plus_non_qual_no_effect_on_qual.
       all: try now solve_ineqs.
       all: try rewrite add_non_qual_constraint_no_effect_on_qual.
       all: try now solve_ineqs.
       all: rewrite qual_update_size_ctx.
       all: rewrite qual_update_qual_ctx in *.
       all:
         match goal with
         | [ |- context[plus ?A ?B SQual] ] =>
             replace (plus A B SQual) with (B SQual) by ltac:(unfold plus; simpl; auto)
         end.
       all:
         match goal with
         | [ H : QualValid ?Q1 ?Q |- QualValid ?Q2 ?Q ] =>
             replace Q2 with Q1; auto
         | [ H : QualLeq ?Q1 ?QA ?QB = _ |- QualLeq ?Q2 ?QA ?QB = _ ] =>
             replace Q2 with Q1; auto
         end.
       all:
         match goal with
         | [ |- map ?A ?B = map ?A ?C ] => replace C with B; auto
         end.
  - constructor 5.
    destruct F; simpl in *.
    unfold plus; simpl.
    rewrite nth_error_None.
    rewrite map_length.
    apply nth_error_None.
    auto.
  - econstructor 6.
    -- destruct F; simpl in *.
       erewrite nth_error_map; eauto; simpl; eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       2-3: erewrite <-subst_sizes_comm.
       3,6:
         match goal with
         | [ |- debruijn_subst_ext_conds (under_ks' _ ?SU) ?KS _ _ ] =>
             replace KS with (plus KS zero) by apply plus_zero;
             replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
         end.
       3-4: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.

       3,5: 
         match goal with
         | [ |- debruijn_subst_ext_conds _ ?KS ?KND ?OBJ ] =>
             let H' := fresh "H" in
             assert (H' : debruijn_subst_ext_conds (under_ks' KS (subst'_of (ext KND OBJ id))) (plus KS zero) KND OBJ); [ | rewrite plus_zero in H'; eauto ]
         end.
       3-4: apply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       
       2-3: rewrite Forall_forall.
       2-3: intros.
       2-3: split.
       2-5:
         match goal with
         | [ H : In _ (subst'_sizes ?A ?B) |- _ ] =>
             replace (subst'_sizes A B) with (map (subst'_size A) B) in H by auto;
             apply in_map_inv in H
         end.
       2-5: destructAll.
       2-5:
         match goal with
         | [ H : In _ ?L, H' : Forall _ ?L |- _ ] =>
             rewrite Forall_forall in H';
             specialize (H' _ H)
         end.
       2-5: destructAll.

       1,3,5: rewrite compose_weak_weaks.
       1-3:
         match goal with
         | [ |- context[subst'_size (?A ∘' ?C) ?B] ] =>
             replace (subst'_size (A ∘' C) B) with (subst_ext' (A ∘' C) B) by auto
         end.
       1-3: rewrite <-subst_ext'_assoc.
       1-3:
         do 2 match goal with
         | [ |- context[subst_ext' ?A ?B] ] =>
             replace (subst_ext' A B) with (subst'_size A B) by auto
           end.

       all: rewrite InstFunctionCtxInd_under_ks_weak_size.
       all: rewrite size_weak_on_size_field.
       all: rewrite size_update_size_ctx.

       1,4-5: rewrite <-weaks'_sing.
       1-3: eapply SizeValid_apply_weaks; eauto.
       1-3: simpl.
       1-3: repeat rewrite map_length; auto.

       1-2:
         match goal with
         | [ |- context[map ?F (?A :: ?B)] ] =>
             replace (map F (A :: B)) with ((map F []) ++ [F A] ++ map F B) by ltac:(simpl; auto)
         end.
       1-2: eapply SizeLeq_weaks_gen; eauto.
       1,4: apply single_weak_debruijn_weak_conds.
       1,3: unfold zero; simpl; auto.
       1-2: simpl; auto.
  - constructor 7.
    unfold plus; simpl.
    rewrite nth_error_None.
    rewrite map_length.
    apply nth_error_None.
    rewrite type_update_size_ctx; auto.
  - econstructor 8.
    -- unfold plus; simpl.
       rewrite type_update_size_ctx.
       erewrite nth_error_map; eauto.
       simpl; eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       rewrite InstFunctionCtxInd_under_ks_weak_size.
       econstructor.
       --- rewrite compose_weak_weaks.
           rewrite type_subst_weak_size.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           erewrite sizeOfPretype_weaks_less_gen.
           2:{
             apply single_weak_debruijn_weak_conds.
           }
           2:{
             simpl; auto.
           }
           2:{
             unfold zero; lia.
           }
           simpl in *.
           match goal with
           | [ H : ?A = _ |- context[?A] ] => rewrite H
           end.
           simpl; eauto.
       --- unfold weak.
           rewrite <-weaks'_weaks.
           eapply SizeValid_apply_weaks; eauto.
           destruct F; simpl.
           repeat rewrite map_length; auto.
       --- unfold weak.
           rewrite <-weaks'_weaks.
           eapply SizeValid_apply_weaks; eauto.
           destruct F; simpl.
           repeat rewrite map_length; auto.
       --- rewrite size_weak_on_size_field.
           rewrite size_update_size_ctx.
           match goal with
           | [ |- context[map ?F (?A :: ?B)] ] =>
               replace (map F (A :: B)) with ((map F []) ++ [F A] ++ map F B) by ltac:(simpl; auto)
           end.
           eapply SizeLeq_weaks_gen; eauto.
           ---- apply single_weak_debruijn_weak_conds.
           ---- unfold zero; simpl; auto.
           ---- unfold sing.
                simpl; auto.
       --- match goal with
           | [ |- context[(?SZS0, ?SZS1)] ] =>
               match goal with
               | [ |- context[size ?F] ] =>
                   match goal with
                   | [ |- TypeValid ?F2 _ ] =>
                       replace F2 with (add_constraints F [SIZE SZS0 SZS1]); auto
                   end
               end
           end.
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           do 2 match goal with
           | [ |- context[subst_ext' ?A ?B] ] =>
               replace (subst_ext' A B) with (subst'_pretype A B) by auto
           end.
           match goal with
           | [ |- context[QualT (subst'_pretype ?SU ?PT) (subst'_qual ?SU ?Q)] ] =>
               replace (QualT (subst'_pretype SU PT) (subst'_qual SU q)) with (subst'_type SU (QualT PT Q)) by auto
           end.
           match goal with
           | [ |- context[[?KV]] ] =>
               replace [KV] with (KV :: subst_ext (weak SSize) []) by auto
           end.
           eapply TypeValid_add_constraint_size; eauto.
           simpl.
           apply single_weak_debruijn_weak_conds.
       --- rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           do 2 match goal with
           | [ |- context[subst_ext' ?A ?B] ] =>
               replace (subst_ext' A B) with (subst'_pretype A B) by auto
           end.
           match goal with
           | [ H : context[heapable ?F] |- context[heapable ?F2] ] =>
               replace (heapable F2) with (heapable F)
           end.
           2:{
             unfold heapable.
             simpl.
             match goal with
             | [ |- _ = map ?F1 (map ?F2 ?L) ] =>
                 rewrite (map_map F2 F1)
             end.
             apply map_ext.
             intros.
             destruct_prs; auto.
           }
           intros.
           match goal with
           | [ H : ?A, H' : ?A -> _ |- _ ] =>
               specialize (H' H)
           end.
           eapply NoCapsPretype_subst_weak_non_pretype; eauto.
           2:{
             apply single_weak_debruijn_weak_conds.
           }
           solve_ineqs.
Qed.

Lemma location_update_qual_ctx : forall {F qctx},
    location (update_qual_ctx qctx F) = location F.
Proof.
  destruct F; auto.
Qed.

Lemma type_subst_weak_qual : forall {F qctx},
    type (subst_ext (weak SQual) (update_qual_ctx qctx F)) =
    map (fun '(sz, q, hc) => (sz, subst'_qual (subst'_of (weak SQual)) q, hc)) (type F).
Proof.
  intros.
  destruct F; simpl in *.
  apply map_ext.
  intros.
  destruct_prs.
  rewrite qual_weak_no_effect_on_size; auto.
Qed.  

Lemma size_subst_weak_qual : forall {F qctx},
    size (subst_ext (weak SQual) (update_qual_ctx qctx F)) = size F.
Proof.
  intros.
  destruct F; simpl in *.
  rewrite <-map_id.
  apply map_ext.
  intros.
  destruct_prs.
  repeat rewrite qual_weak_no_effect_on_sizes; auto.
Qed.

Lemma non_size_weak_no_effect_on_size : forall {knd ks},
    knd <> SSize ->
    subst'_size (weaks' (plus (sing knd 1) ks)) = subst'_size (weaks' ks).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro sz.
  induction sz; simpl; auto.
  - unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    match goal with
    | [ |- SizeVar ?A = SizeVar ?B ] =>
        replace B with A; auto
    end.
    unfold plus; unfold zero; simpl.
    destruct knd; simpl; try lia.
    solve_impossibles.
  - rewrite IHsz1; rewrite IHsz2; auto.
Qed.

Lemma under_ks_non_size_no_effect_on_size : forall {ks knd su},
    knd <> SSize ->
    subst'_size
      (under_ks' (plus (sing knd 1) ks)
         (subst'_of su))
    =
    subst'_size
      (under_ks' ks
         (subst'_of su)).
Proof.
  intros.
  apply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intro sz.
  induction sz; simpl; auto.
  - unfold get_var'.
    unfold under_ks'.
    match goal with
    | [ |- context[plus ?A ?B SSize] ] =>
        replace (plus A B SSize) with (B SSize)
    end.
    2:{
      unfold plus; destruct knd; simpl; auto.
      solve_impossibles.
    }
    handle_ineq; auto.
    do 2 rewrite plus_zero.
    rewrite non_size_weak_no_effect_on_size; auto.
  - rewrite IHsz1; rewrite IHsz2; auto.
Qed.

Lemma under_ks_non_size_no_effect_on_sizes : forall {ks knd su},
    knd <> SSize ->
    subst'_sizes
      (under_ks' (plus (sing knd 1) ks)
         (subst'_of su))
    =
    subst'_sizes
      (under_ks' ks
         (subst'_of su)).
Proof.
  intros.
  unfold subst'_sizes.
  rewrite under_ks_non_size_no_effect_on_size; auto.
Qed.

Lemma qual_weak_on_qual_field : forall {F},
    qual (subst_ext (weak SQual) F) =
    map
      (fun '(qs0, qs1) =>
         (subst'_quals (subst'_of (weak SQual)) qs0,
          subst'_quals (subst'_of (weak SQual)) qs1))
      (qual F).
Proof.
  destruct F; auto.
Qed.

Lemma InstIndValid_at_subst_weak_qual : forall {F ks idx qs0 qs1},
    InstIndValid_at F ks idx ->
    InstIndValid_at (subst_ext (weak SQual) (update_qual_ctx ((qs0, qs1) :: qual F) F)) (plus (sing SQual 1) ks) idx.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - constructor 1.
    simpl.
    destruct F; simpl in *; subst.
    unfold plus; simpl.
    lia.
  - constructor 2.
    -- destruct F; simpl in *.
       unfold plus; simpl; lia.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       simpl in *.
       rewrite location_update_qual_ctx.
       match goal with
       | [ H : LocValid _ _ |- _ ] =>
           rewrite location_update_location_ctx in H
       end.
       rewrite non_loc_weak_no_effect_on_loc; [ | solve_ineqs ].
       unfold plus; simpl; auto.
  - constructor 3.
    destruct F; simpl in *.
    unfold plus; simpl.
    rewrite nth_error_None.
    rewrite map_length.
    apply nth_error_None.
    auto.
  - econstructor 4.
    -- destruct F; simpl in *.
       erewrite nth_error_map; eauto; simpl; eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       2-3: erewrite <-subst_quals_comm.
       3,6:
         match goal with
         | [ |- debruijn_subst_ext_conds (under_ks' _ ?SU) ?KS _ _ ] =>
             replace KS with (plus KS zero) by apply plus_zero;
             replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
         end.
       3-4: eapply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.

       3,5: 
         match goal with
         | [ |- debruijn_subst_ext_conds _ ?KS ?KND ?OBJ ] =>
             let H' := fresh "H" in
             assert (H' : debruijn_subst_ext_conds (under_ks' KS (subst'_of (ext KND OBJ id))) (plus KS zero) KND OBJ); [ | rewrite plus_zero in H'; eauto ]
         end.
       3-4: apply debruijn_subst_under_ks.
       3-4: eapply simpl_debruijn_subst_ext_conds; eauto.
       
       2-3: rewrite Forall_forall.
       2-3: intros.
       2-3: split.
       2-5:
         match goal with
         | [ H : In _ (subst'_quals ?A ?B) |- _ ] =>
             replace (subst'_quals A B) with (map (subst'_qual A) B) in H by auto;
             apply in_map_inv in H
         end.
       2-5: destructAll.
       2-5:
         match goal with
         | [ H : In _ ?L, H' : Forall _ ?L |- _ ] =>
             rewrite Forall_forall in H';
             specialize (H' _ H)
         end.
       2-5: destructAll.

       1,3,5: rewrite compose_weak_weaks.
       1-3:
         match goal with
         | [ |- context[subst'_qual (?A ∘' ?C) ?B] ] =>
             replace (subst'_qual (A ∘' C) B) with (subst_ext' (A ∘' C) B) by auto
         end.
       1-3: rewrite <-subst_ext'_assoc.
       1-3:
         do 2 match goal with
         | [ |- context[subst_ext' ?A ?B] ] =>
             replace (subst_ext' A B) with (subst'_qual A B) by auto
         end.

       all: rewrite InstFunctionCtxInd_under_ks_weak_qual.

       1,4-5: rewrite <-weaks'_sing.
       1-3:
         match goal with
         | [ |- QualValid (qual ?F) _ ] =>
             replace F with (add_constraints F (subst'_kindvars (subst'_of (weak SQual)) [])) by auto
         end.
       1-3:
         match goal with
         | [ |- context[subst_ext (weak SQual) ?F] ] =>
             replace (subst_ext (weak SQual) F) with (subst'_function_ctx (subst'_of (weak SQual)) F) by auto
         end.
       1-3: eapply QualValid_subst_weak_qual; eauto.
       1-3: rewrite weaks'_sing.
       1-3: apply single_weak_debruijn_weak_conds.

       1-2: rewrite qual_weak_on_qual_field.
       1-2: rewrite qual_update_qual_ctx.

       1-2:
         match goal with
         | [ |- context[map ?F (?A :: ?B)] ] =>
             replace (map F (A :: B)) with ((map F []) ++ [F A] ++ map F B) by ltac:(simpl; auto)
         end.
       1-2: eapply QualLeq_weaks_gen; eauto.
       1,4: apply single_weak_debruijn_weak_conds.
       1,3: unfold zero; simpl; auto.
       1-2: simpl; auto.
  - constructor 5.
    destruct F; simpl in *.
    unfold plus; simpl.
    rewrite add_non_size_constraint_no_effect_on_size; auto.
    solve_ineqs.
  - econstructor 6.
    -- destruct F; simpl in *.
       unfold plus; simpl.
       rewrite add_non_size_constraint_no_effect_on_size; eauto.
       solve_ineqs.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       econstructor.
       all: simpl in *.
       all: rewrite under_ks_non_size_no_effect_on_sizes.
       all: try solve_ineqs.
       2-3: prepare_Forall.
       2-3:
         match goal with
         | [ H : In _ (subst'_sizes _ _) |- _ ] =>
             unfold subst'_sizes in H; apply in_map_inv in H
         end.
       2-3: destructAll.
       2-3: repeat split.
       all: try rewrite weak_plus_non_size_no_effect_on_size.
       all: try now solve_ineqs.
       all: try rewrite add_non_size_constraint_no_effect_on_size.
       all: try now solve_ineqs.
       all: rewrite size_update_qual_ctx.
       all: rewrite size_update_size_ctx in *.
       all:
         match goal with
         | [ |- context[plus ?A ?B SSize] ] =>
             replace (plus A B SSize) with (B SSize) by ltac:(unfold plus; simpl; auto)
         end.
       all:
         match goal with
         | [ H : SizeValid ?Q1 ?Q |- SizeValid ?Q2 ?Q ] =>
             replace Q2 with Q1; auto
         | [ H : SizeLeq ?Q1 ?QA ?QB = _ |- SizeLeq ?Q2 ?QA ?QB = _ ] =>
             replace Q2 with Q1; auto
         end.
  - constructor 7.
    unfold plus; simpl.
    rewrite nth_error_None.
    rewrite map_length.
    apply nth_error_None.
    rewrite type_update_qual_ctx; auto.
  - econstructor 8.
    -- unfold plus; simpl.
       rewrite type_update_qual_ctx.
       erewrite nth_error_map; eauto.
       simpl; eauto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       rewrite InstFunctionCtxInd_under_ks_weak_qual.
       econstructor.
       --- rewrite compose_weak_weaks.
           rewrite type_subst_weak_qual.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           erewrite sizeOfPretype_weaks_only_size_matters.
           2:{
             apply single_weak_debruijn_weak_conds.
           }
           2:{ simpl; auto. }
           erewrite sizeOfPretype_eifc; eauto.
           apply eifc_map_second_comp.
       --- rewrite size_subst_weak_qual; auto.
       --- rewrite size_subst_weak_qual.
           rewrite qual_weak_no_effect_on_size; auto.
       --- rewrite size_subst_weak_qual.
           rewrite qual_weak_no_effect_on_size; auto.
       --- match goal with
           | [ |- context[(?QS0, ?QS1)] ] =>
               match goal with
               | [ |- context[qual ?F] ] =>
                   match goal with
                   | [ |- TypeValid ?F2 _ ] =>
                       replace F2 with (add_constraints F [QUAL QS0 QS1]); auto
                   end
               end
           end.
           rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           do 2 match goal with
           | [ |- context[subst_ext' ?A ?B] ] =>
               replace (subst_ext' A B) with (subst'_pretype A B) by auto
           end.
           match goal with
           | [ |- context[QualT (subst'_pretype ?SU ?PT) (subst'_qual ?SU ?Q)] ] =>
               replace (QualT (subst'_pretype SU PT) (subst'_qual SU q)) with (subst'_type SU (QualT PT Q)) by auto
           end.
           match goal with
           | [ |- context[[?KV]] ] =>
               replace [KV] with (KV :: subst_ext (weak SQual) []) by auto
           end.
           eapply TypeValid_add_constraint_qual; eauto.
           simpl.
           apply single_weak_debruijn_weak_conds.
       --- rewrite compose_weak_weaks.
           match goal with
           | [ |- context[subst'_pretype ?A ?B] ] =>
               replace (subst'_pretype A B) with (subst_ext' A B) by auto
           end.
           rewrite <-subst_ext'_assoc.
           do 2 match goal with
           | [ |- context[subst_ext' ?A ?B] ] =>
               replace (subst_ext' A B) with (subst'_pretype A B) by auto
           end.
           match goal with
           | [ H : context[heapable ?F] |- context[heapable ?F2] ] =>
               replace (heapable F2) with (heapable F)
           end.
           2:{
             unfold heapable.
             simpl.
             match goal with
             | [ |- _ = map ?F1 (map ?F2 ?L) ] =>
                 rewrite (map_map F2 F1)
             end.
             apply map_ext.
             intros.
             destruct_prs; auto.
           }
           intros.
           match goal with
           | [ H : ?A, H' : ?A -> _ |- _ ] =>
               specialize (H' H)
           end.
           eapply NoCapsPretype_subst_weak_non_pretype; eauto.
           2:{
             apply single_weak_debruijn_weak_conds.
           }
           solve_ineqs.
Qed.

Lemma InstIndValid_at_add_constraint : forall {kv F ks idx},
    InstIndValid_at F ks idx ->
    InstIndValid_at
      (add_constraint F kv)
      (plus (sing (kind_of_kindvar kv) 1) ks) idx.
Proof.
  destruct kv; intros.
  - apply InstIndValid_at_subst_weak_loc; auto.
  - apply InstIndValid_at_subst_weak_qual; auto.
  - apply InstIndValid_at_subst_weak_size; auto.
  - apply InstIndValid_at_subst_weak_pretype; auto.
Qed.

Lemma InstIndValid_at_add_constraints : forall {kvs F ks idx},
    InstIndValid_at F ks idx ->
    InstIndValid_at
      (add_constraints F kvs)
      (plus (ks_of_kvs kvs) ks)
      idx.
Proof.
  induction kvs; auto.
  intros; simpl.
  match goal with
  | [ |- context[plus (plus ?A ?B) ?C] ] =>
      replace (plus A B) with (plus B A) by apply plus_comm
  end.
  rewrite <-plus_assoc.
  apply IHkvs.
  apply InstIndValid_at_add_constraint; auto.
Qed.

Lemma QualValid_subst_index_usable : forall {F ks idx q F' q'},
    InstIndValid_at F ks idx ->
    QualValid (qual F) q ->
    F' = qual (InstFunctionCtxInd_under_ks F ks idx) ->
    q' = subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q ->
    QualValid F' q'.
Proof.
  intros; subst.
  eapply QualValid_subst_index; eauto.
Qed.

Lemma debruijn_subst_ext_conds_to_under_ks_pretype_index : forall {f ks pt},
    debruijn_subst_ext_conds f ks SPretype pt ->
    f = under_ks' ks (subst'_of (subst_of_index (PretypeI pt))).
Proof.
  intros.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma debruijn_subst_ext_conds_to_under_ks_loc_index : forall {f ks l},
    debruijn_subst_ext_conds f ks SLoc l ->
    f = under_ks' ks (subst'_of (subst_of_index (LocI l))).
Proof.
  intros.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma debruijn_subst_ext_conds_to_under_ks_qual : forall {f ks q},
    debruijn_subst_ext_conds f ks SQual q ->
    f = under_ks' ks (subst'_of (ext SQual q id)).
Proof.
  intros.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma debruijn_subst_ext_conds_to_under_ks_qual_index : forall {f ks q},
    debruijn_subst_ext_conds f ks SQual q ->
    f = under_ks' ks (subst'_of (subst_of_index (QualI q))).
Proof.
  intros.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma debruijn_subst_ext_conds_to_under_ks_size_index : forall {f ks sz},
    debruijn_subst_ext_conds f ks SSize sz ->
    f = under_ks' ks (subst'_of (subst_of_index (SizeI sz))).
Proof.
  intros.
  eapply debruijn_subst_ext_inj; eauto.
  match goal with
  | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
      replace KS with (plus KS zero) by apply plus_zero;
	  replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
  end.
  apply debruijn_subst_under_ks.
  simpl.
  apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma TypeValid_subst_loc_index :
  (forall F t,
      TypeValid F t ->
      forall f ks l F',
        debruijn_subst_ext_conds f ks SLoc l ->
        InstIndValid_at F ks (LocI l) ->
        F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f ks l F',
        debruijn_subst_ext_conds f ks SLoc l ->
        InstIndValid_at F ks (LocI l) ->
        F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f ks l F',
        debruijn_subst_ext_conds f ks SLoc l ->
        InstIndValid_at F ks (LocI l) ->
        F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f ks l F',
        debruijn_subst_ext_conds f ks SLoc l ->
        InstIndValid_at F ks (LocI l) ->
        F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  apply
    (TypesValid_ind'
       (fun F t =>
          forall f ks l F',
            debruijn_subst_ext_conds f ks SLoc l ->
            InstIndValid_at F ks (LocI l) ->
            F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
            TypeValid F' (subst'_type f t))
       (fun F t =>
          forall f ks l F',
            debruijn_subst_ext_conds f ks SLoc l ->
            InstIndValid_at F ks (LocI l) ->
            F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
            HeapTypeValid F' (subst'_heaptype f t))
       (fun F t =>
          forall f ks l F',
            debruijn_subst_ext_conds f ks SLoc l ->
            InstIndValid_at F ks (LocI l) ->
            F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
            ArrowTypeValid F' (subst'_arrowtype f t))
       (fun F t =>
          forall f ks l F',
            debruijn_subst_ext_conds f ks SLoc l ->
            InstIndValid_at F ks (LocI l) ->
            F' = InstFunctionCtxInd_under_ks F ks (LocI l) ->
            FunTypeValid F' (subst'_funtype f t))).
  all: intros; simpl in *; subst; auto.

  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    erewrite qual_fctx_subst_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    unfold get_var'.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> SLoc -> _] |- _ ] => rewrite H; solve_ineqs
    end.
    simpl.
    econstructor; eauto.
    1-2,4: erewrite qual_fctx_subst_loc; eauto.
    erewrite type_fctx_subst_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    match goal with
    | [ |- TypeValid _ (QualT _ (subst'_qual _ ?Q)) ] =>
      erewrite (qual_debruijn_subst_ext (q:=Q)); eauto; solve_ineqs
    end.
    econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_loc; eauto.
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
       erewrite type_fctx_subst_loc_alternate; eauto.
    -- simpl.
       erewrite size_fctx_subst_loc_alternate; eauto.
    -- rewrite <-InstFunctionCtxInd_under_ks_unroll_loc.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_weak_pretype_loc.
           simpl; auto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_loc; eauto.
  - erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
    -- prepare_Forall.
       erewrite qual_fctx_subst_loc_alternate; eauto.
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
    erewrite qual_fctx_subst_loc; eauto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_index_loc; auto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_index_loc; auto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_index_loc; auto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_loc; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_loc.
           rewrite <-InstFunctionCtxInd_under_ks_weak_loc.
           simpl; auto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- eapply LocValid_subst_index_loc; eauto.
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
    erewrite type_fctx_subst_loc_alternate; eauto.
    erewrite size_fctx_subst_loc_alternate; eauto.
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
    erewrite qual_fctx_subst_loc; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
  - econstructor; eauto.
    -- simpl.
       erewrite size_fctx_subst_loc_alternate; eauto.
       erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_loc; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_loc.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype_loc.
           simpl; auto.
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
       --- erewrite qual_fctx_subst_loc; eauto.
       --- simpl.
           erewrite size_fctx_subst_loc_alternate; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_kindvars; eauto.
       --- rewrite fold_right_ks_of_kvs.
           apply InstIndValid_at_add_constraints; auto.
       --- rewrite fold_right_ks_of_kvs.
           rewrite <-InstFunctionCtxInd_under_ks_unroll_loc.
           erewrite debruijn_subst_ext_conds_to_under_ks_loc_index; eauto.
           rewrite InstFunctionCtxInd_under_ks_add_constraints.
           simpl; auto.
Qed.

Lemma nth_error_None_remove_nth : forall {A} {idx} {l : list A},
    nth_error l idx = None ->
    remove_nth l idx = l.
Proof.
  induction idx.
  - destruct l; auto.
    simpl.
    let H := fresh "H" in intro H; inv H.
  - destruct l; auto.
    simpl.
    intros.
    rewrite IHidx; auto.
Qed.

Lemma QualValid_subst_qual_no_effect : forall {qual q su ks},
    QualValid qual q ->
    nth_error qual (ks SQual) = None ->
    subst'_qual (under_ks' ks su) q = q.
Proof.
  intros.
  match goal with
  | [ H : QualValid _ _ |- _ ] => inv H; auto
  end.
  simpl.
  unfold get_var'.
  unfold under_ks'.
  match goal with
  | [ |- context[?A <? ?B] ] =>
      replace (A <? B) with true; auto
  end.
  apply eq_sym.
  rewrite OrdersEx.Nat_as_DT.ltb_lt.
  eapply OrdersEx.Nat_as_OT.lt_le_trans.
  - eapply nth_error_Some_usable; eauto.
  - rewrite <-nth_error_None; auto.
Qed.

Lemma Forall_comp_map_inv : forall {A B : Type} (P : B -> Prop) (f : A -> B) (xs : list A),
    Forall P (map f xs) -> Forall (fun x : A => P (f x)) xs.
Proof.
  induction xs; auto.
  simpl.
  intros.
  match goal with
  | [ H : Forall _ _ |- _ ] => inv H
  end.
  constructor; auto.
Qed.

Lemma model_satisfies_context_QualLeq_quotient_for_non_existent_var : forall {idx f qctx q model model' qctx'},
    (forall qc, f (QualConst qc) = QualConst qc) ->
    (forall v,
        v <> idx ->
        f (QualVar v) = QualVar (shift_down_after v idx 0)) ->
    f (QualVar idx) = q ->
    nth_error qctx idx = None ->
    qctx'
    =
    map
      (fun '(qs0, qs1) =>
         (map f qs0, map f qs1))
      qctx ->
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
  {
    apply FunctionalExtensionality.functional_extensionality.
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
      end.
  }
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
  - match goal with
    | [ H : interp_qual _ = _ |- _ ] =>
      repeat rewrite H
    end.
    match goal with
    | [ |- context[interp_qual _ (?F _)] ] =>
        match goal with
        | [ |- context[le_qualconst _ (_ ?IDX)] ] =>
            match goal with
            | [ H : forall _ _ _, _
                |- Forall _ ?L0 /\ Forall _ ?L1 ] =>
                specialize (H IDX (map F L0) (map F L1));
                unfold shift_down_after in H
            end
        end
    end.
    unfold shift_down_after.
    match goal with
    | [ H : context[?A <? ?B] |- _ ] =>
        replace (A <? B) with true in *
    end.
    2:{
      apply eq_sym.
      rewrite OrdersEx.Nat_as_DT.ltb_lt.
      eapply OrdersEx.Nat_as_OT.lt_le_trans.
      - eapply nth_error_Some_usable; eauto.
      - rewrite <-nth_error_None; auto.
    }
    simpl in *.
    match goal with
    | [ H : context[nth_error (map _ _)] |- _ ] =>
        erewrite nth_error_map in H; eauto;
        simpl in *; specialize (H eq_refl)
    end.
    destructAll.
    do 2 match goal with
      | [ H : Forall _ (map _ _) |- _ ] =>
          apply Forall_comp_map_inv in H
      end.
    auto.
Qed.

Lemma QualLeq_quotient_for_non_existent_var : forall {f idx qctx qctx' q q1 q2},
    (forall qc, f (QualConst qc) = QualConst qc) ->
    (forall v,
        v <> idx ->
        f (QualVar v) = QualVar (shift_down_after v idx 0)) ->
    f (QualVar idx) = q ->
    f q1 = q1 ->
    f q2 = q2 ->
    qctx'
    =
    map
      (fun '(qs0, qs1) =>
         (map f qs0, map f qs1))
      qctx ->
    QualLeq qctx q1 q2 = Some true ->
    nth_error qctx idx = None ->
    QualLeq
      qctx'
      q1
      q2
    =
      Some true.
Proof.
  intros.
  rewrite QualLeq_desc in *.
  unfold ctx_imp_leq in *.
  intros.
  eapply prove_using_unknown_lemma.
  {
    eapply model_satisfies_context_QualLeq_quotient_for_non_existent_var; eauto.
    apply eq_refl.
  }

  intros; split; auto.
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.
  match goal with
  | [ H : interp_qual ?M2 = _
      |- le_qualconst (interp_qual ?M ?Q1) (interp_qual ?M ?Q2) ] =>
      replace (interp_qual M Q1) with (interp_qual M2 Q1);
      [ replace (interp_qual M Q2) with (interp_qual M2 Q2); [ | rewrite H ] | rewrite H ]
  end.
  2-3:
    match goal with
    | [ H : _ = ?Q |- _ = interp_qual _ ?Q ] => rewrite H; auto
    end.
  match goal with
  | [ H : forall _, _ -> le_qualconst _ _ |- _ ] =>
      eapply H; eauto
  end.
Qed.

Lemma subst_qual_QualVar : forall {ks v qidx},
    v <> ks SQual ->
    subst'_qual
      (under_ks' ks (subst'_of (ext SQual qidx id)))
      (QualVar v)
    = QualVar (shift_down_after v (ks SQual) 0).
Proof.
  intros.
  simpl.
  unfold get_var'.
  unfold under_ks'.
  handle_ineq.
  - unfold var'.
    unfold var.
    unfold zero.
    simpl.
    unfold shift_down_after.
    match goal with
    | [ |- context[?A <? ?B] ] =>
        replace (A <? B) with true; simpl; auto
    end.
    apply eq_sym.
    rewrite OrdersEx.Nat_as_DT.ltb_lt.
    eauto.
  - unfold ext.
    simpl.
    match goal with
    | [ |- context[dec_eq ?A ?B] ] =>
        remember (dec_eq A B) as obj; destruct obj; [ lia | ]
    end.
    simpl.
    unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    unfold plus.
    unfold zero.
    unfold shift_down_after.
    handle_ineq.
    match goal with
    | [ |- QualVar ?A = QualVar ?B ] =>
        replace B with A; auto
    end.
    lia.
Qed.

Lemma QualLeq_subst_qual_gen : forall {label ret qual size type location linear ks q1 q2 qidx},
    InstIndValid_at
      {|
        label := label;
        ret := ret;
        qual := qual;
        size := size;
        type := type;
        location := location;
        linear := linear
      |} ks (QualI qidx) ->
    QualValid qual q1 ->
    QualValid qual q2 ->
    QualLeq qual q1 q2 = Some true ->
    QualLeq
      (map
       (fun '(qs1, qs2) =>
          (subst'_quals (under_ks' ks (subst'_of (ext SQual qidx id)))
             qs1,
            subst'_quals (under_ks' ks (subst'_of (ext SQual qidx id)))
              qs2))
       (remove_nth qual (ks SQual)))
      (subst'_qual (under_ks' ks (subst'_of (ext SQual qidx id))) q1)
      (subst'_qual (under_ks' ks (subst'_of (ext SQual qidx id))) q2) =
      Some true.
Proof.
  intros.
  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H; simpl in *
  end.
  - rewrite nth_error_None_remove_nth; auto.
    erewrite QualValid_subst_qual_no_effect; eauto.
    erewrite QualValid_subst_qual_no_effect; eauto.
    eapply QualLeq_quotient_for_non_existent_var; eauto.
    5:{
      unfold subst'_quals; eauto.
    }
    -- auto.
    -- intros.
       eapply subst_qual_QualVar; eauto.
    -- erewrite QualValid_subst_qual_no_effect; eauto.
    -- erewrite QualValid_subst_qual_no_effect; eauto.
  - match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inv H
    end.
    eapply QualLeq_quotient.
    -- auto.
    -- intros.
       eapply subst_qual_QualVar; eauto.
    -- simpl.
       unfold get_var'.
       unfold under_ks'.
       handle_ineq.
       unfold ext.
       simpl.
       match goal with
       | [ |- context[dec_eq ?A ?B] ] =>
           remember (dec_eq A B) as obj; destruct obj; [ | lia ]
       end.
       rewrite plus_zero.
       eauto.
    -- rewrite <-remove_nth_map.
       eauto.
    -- auto.
    -- eauto.
    -- simpl in *.
       unfold subst'_quals in *.
       rewrite Forall_forall in *.
       intros.
       match goal with
       | [ H : context[QualLeq _ _ ?Q = _]
           |- QualLeq _ _ ?Q = _ ] =>
	       eapply H
       end.
       apply in_map; auto.
    -- simpl in *.
       unfold subst'_quals in *.
       rewrite Forall_forall in *.
       intros.
       match goal with
       | [ H : context[QualLeq _ ?Q _ = _]
           |- QualLeq _ ?Q _ = _ ] =>
	       eapply H
       end.
       apply in_map; auto.
Qed.

(* uses models, noble will do *)
Lemma QualLeq_subst_index : forall {F ks idx q1 q2},
    InstIndValid_at F ks idx ->
    QualValid (qual F) q1 ->
    QualValid (qual F) q2 ->
    QualLeq (qual F) q1 q2 = Some true ->
    QualLeq
      (qual (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q1)
      (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q2)
    =
    Some true.
Proof.
  intros.
  destruct idx; destruct F; simpl in *.
  1-2,4: do 2 ltac:(erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ]).
  1-3:
    match goal with
    | [ |- context[map ?F _] ] =>
        replace F with (fun (x : list Qual * list Qual) => x); [ rewrite map_id; auto | ]
    end.
  1-3: eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  1-3: intros.
  1-3: destruct_prs.
  1-3: do 2 ltac:(erewrite quals_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    [ | solve_ineqs ]).
  1-3: auto.

  eapply QualLeq_subst_qual_gen; eauto.
Qed.

Lemma QualLeq_subst_index_usable : forall {F ks idx q1 q2 F' q1' q2'},
    InstIndValid_at F ks idx ->
    QualValid (qual F) q1 ->
    QualValid (qual F) q2 ->
    QualLeq (qual F) q1 q2 = Some true ->
    F' = (qual (InstFunctionCtxInd_under_ks F ks idx)) ->
    q1' = (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q1) ->
    q2' = (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q2) ->
    QualLeq F' q1' q2' = Some true.
Proof.
  intros; subst.
  eapply QualLeq_subst_index; eauto.
Qed.

Lemma nth_error_type_subst_qual_index : forall {F ks idx sz qa hc q'},
    nth_error (type F) idx = Some (sz, qa, hc) ->
    nth_error
      (type
         (subst'_function_ctx
            (under_ks' ks (subst'_of (ext SQual q' id)))
            (update_qual_ctx (remove_nth (qual F) (ks SQual)) F)))
      idx =
    Some (sz, subst'_qual (under_ks' ks (subst'_of (ext SQual q' id))) qa, hc).
Proof.
  intros.
  destruct F; simpl in *.
  erewrite nth_error_map; eauto.
  simpl.
  erewrite size_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma nth_error_type_subst_size_index : forall {F ks idx sz qa hc sz'},
    nth_error (type F) idx = Some (sz, qa, hc) ->
    nth_error
      (type
         (subst'_function_ctx
            (under_ks' ks (subst'_of (ext SSize sz' id)))
            (update_size_ctx (remove_nth (size F) (ks SSize)) F)))
      idx =
    Some (subst'_size (under_ks' ks (subst'_of (ext SSize sz' id))) sz, qa, hc).
Proof.
  intros.
  destruct F; simpl in *.
  erewrite nth_error_map; eauto.
  simpl.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma nth_error_type_subst_pretype_index : forall {F ks idx pt},
    idx <> ks SPretype ->
    nth_error
      (type
         (subst'_function_ctx
            (under_ks' ks (subst'_of (ext SPretype pt id)))
            (update_type_ctx (remove_nth (type F) (ks SPretype)) F)))
      (shift_down_after idx (ks SPretype) (zero SPretype)) =
    nth_error (type F) idx.
Proof.
  destruct F; simpl.
  intros.
  match goal with
  | [ |- context[map ?F _] ] =>
      replace F with (fun (tpl : Size * Qual * HeapableConstant) => tpl); [ rewrite map_id | ]
  end.
  2:{
    eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
    intros.
    destruct_prs.
    erewrite size_debruijn_subst_ext;
      [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
      solve_ineqs.
    erewrite qual_debruijn_subst_ext;
      [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
      solve_ineqs.
    auto.
  }
  apply nth_error_shift_down; auto.
Qed.

Lemma qual_fctx_subst_weak_loc_spec : forall {F},
    qual
      (subst'_function_ctx
         (subst'_of (weak SLoc))
         (update_location_ctx (location F + 1) F))
    =
    qual F.
Proof.
  intros.
  match goal with
  | [ |- qual ?F = _ ] =>
      replace F with (add_constraints F []) by auto
  end.
  match goal with
  | [ |- _ = qual ?F ] =>
      replace F with (add_constraints F []) by auto
  end.
  apply qual_fctx_subst_weak_loc.
Qed.

Lemma KindVarsValid_subst_qual_index : forall {kvs F ks q f},
    KindVarsValid F kvs ->
    debruijn_subst_ext_conds f ks SQual q ->
    InstIndValid_at F ks q ->
    KindVarsValid
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SQual q id)))
         (update_qual_ctx (remove_nth (qual F) (ks SQual)) F))
      (subst'_kindvars f kvs).
Proof.
  induction kvs; intros; simpl in *; constructor.
  - match goal with
    | [ H : KindVarsValid _ _ |- _ ] => inv H
    end.
    match goal with
    | [ X : KindVar |- _ ] => destruct X; simpl; auto
    end.
    -- unfold subst'_quals.
       split.
       all: prepare_Forall_with_map.
       all: eapply QualValid_subst_index_usable; eauto.
       all: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
    -- unfold subst'_sizes.
       split.
       all: prepare_Forall_with_map.
       all:
         match goal with
         | [ |- context[map (subst'_size ?F)] ] =>
             replace (map (subst'_size F)) with (subst'_sizes F) by auto
         end.
       all: erewrite size_fctx_subst_qual_index_alternate; eauto.
       all: erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    -- match goal with
       | [ H : KindVarValid _ _ |- _ ] => inv H
       end.
       split.
       --- erewrite size_fctx_subst_qual_index_alternate; eauto.
           erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       --- eapply QualValid_subst_index_usable; eauto.
           erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
  - rewrite <-InstFunctionCtxInd_under_ks_unroll_qual.
    erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
    rewrite InstFunctionCtxInd_under_ks_add_constraint.
    eapply IHkvs; eauto.
    -- match goal with
       | [ H : KindVarsValid _ _ |- _ ] => inv H; auto
       end.
    -- unfold under_kindvar'.
       apply debruijn_subst_ext_under_knd.
       match goal with
       | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
           replace KS with (plus KS zero) by apply plus_zero;
           replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
       end.
       apply debruijn_subst_under_ks.
       apply simpl_debruijn_subst_ext_conds.
    -- apply InstIndValid_at_add_constraint; auto.
Qed.

Lemma KindVarsValid_subst_size_index : forall {kvs F ks sz f},
    KindVarsValid F kvs ->
    debruijn_subst_ext_conds f ks SSize sz ->
    InstIndValid_at F ks sz ->
    KindVarsValid
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SSize sz id)))
         (update_size_ctx (remove_nth (size F) (ks SSize)) F))
      (subst'_kindvars f kvs).
Proof.
  induction kvs; intros; simpl in *; constructor.
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
       all:
         match goal with
         | [ |- context[map (subst'_qual ?F)] ] =>
             replace (map (subst'_qual F)) with (subst'_quals F) by auto
         end. 
       all: erewrite qual_fctx_subst_size_alternate; eauto.
       all: erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- unfold subst'_sizes.
       split.
       all: prepare_Forall_with_map.
       all: eapply SizeValid_subst_index_general; eauto.
       all: erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
    -- destructAll.
       split.
       --- eapply SizeValid_subst_index_general; eauto.
           erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
       --- erewrite qual_fctx_subst_size_alternate; eauto.
           erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
  - rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
    erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
    rewrite InstFunctionCtxInd_under_ks_add_constraint.
    eapply IHkvs; eauto.
    -- unfold under_kindvar'.
       apply debruijn_subst_ext_under_knd.
       match goal with
       | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
           replace KS with (plus KS zero) by apply plus_zero;
           replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
       end.
       apply debruijn_subst_under_ks.
       apply simpl_debruijn_subst_ext_conds.
    -- apply InstIndValid_at_add_constraint; auto.
Qed.

Lemma TypeValid_subst_qual_index :
  (forall F t,
      TypeValid F t ->
      forall f ks q F',
        debruijn_subst_ext_conds f ks SQual q ->
        InstIndValid_at F ks (QualI q) ->
        F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
        TypeValid F t /\ TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f ks q F',
        debruijn_subst_ext_conds f ks SQual q ->
        InstIndValid_at F ks (QualI q) ->
        F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
        HeapTypeValid F t /\ HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f ks q F',
        debruijn_subst_ext_conds f ks SQual q ->
        InstIndValid_at F ks (QualI q) ->
        F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
        ArrowTypeValid F t /\ ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f ks q F',
        debruijn_subst_ext_conds f ks SQual q ->
        InstIndValid_at F ks (QualI q) ->
        F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
        FunTypeValid F t /\ FunTypeValid F' (subst'_funtype f t)).
Proof.
  apply
    (TypesValid_ind'
       (fun F t =>
          forall f ks q F',
            debruijn_subst_ext_conds f ks SQual q ->
            InstIndValid_at F ks (QualI q) ->
            F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
            TypeValid F t /\ TypeValid F' (subst'_type f t))
       (fun F t =>
          forall f ks q F',
            debruijn_subst_ext_conds f ks SQual q ->
            InstIndValid_at F ks (QualI q) ->
            F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
            HeapTypeValid F t /\ HeapTypeValid F' (subst'_heaptype f t))
       (fun F t =>
          forall f ks q F',
            debruijn_subst_ext_conds f ks SQual q ->
            InstIndValid_at F ks (QualI q) ->
            F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
            ArrowTypeValid F t /\ ArrowTypeValid F' (subst'_arrowtype f t))
       (fun F t =>
          forall f ks q F',
            debruijn_subst_ext_conds f ks SQual q ->
            InstIndValid_at F ks (QualI q) ->
            F' = InstFunctionCtxInd_under_ks F ks (QualI q) ->
            FunTypeValid F t /\ FunTypeValid F' (subst'_funtype f t))).
  all: intros; simpl in *; subst; auto.

  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    eapply QualValid_subst_index_usable; eauto.
    erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
  - split.
    1:{ econstructor; eauto. }
    unfold get_var'.
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
    4:{
      eapply QualLeq_subst_index_usable.
      4: eauto.
      all: eauto.
      erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    }
    -- eapply QualValid_subst_index_usable.
       4:{
         erewrite debruijn_subst_ext_conds_to_under_ks_qual; eauto.
         match goal with
         | [ |- context[ext SQual ?Q id] ] =>
             replace (ext SQual Q id) with (subst_of_index (QualI Q)); auto
         end.
       }
       all: eauto.
    -- eapply QualValid_subst_index_usable; eauto.
    -- erewrite nth_error_type_subst_qual_index; eauto.
  - split.
    1:{
      econstructor; eauto.
      eapply proj1.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eapply debruijn_subst_ext_under_knd; eauto.
      - apply InstIndValid_at_subst_weak_pretype; auto.
      - eauto.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable.
       4: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
    -- eapply QualValid_subst_index_usable.
       4: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualValid_subst_index_usable.
       4: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
    -- eapply RecVarUnderRefPretype_subst_non_pretype; auto.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- solve_ineqs.
    -- simpl.
       erewrite sizeOfPretype_subst_no_effect;
         [ | eapply debruijn_subst_ext_under_knd | ];
         eauto; solve_ineqs.
       erewrite sizeOfPretype_eifc; eauto.
       constructor.
       apply type_fctx_subst_qual_eifc.
    -- eapply SizeValid_subst_index_general; eauto.
       erewrite size_debruijn_subst_ext; auto.
       2:{
         eapply debruijn_subst_under_ks; eauto.
         apply simpl_debruijn_subst_ext_conds.
       }
       solve_ineqs.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_qual.
           erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype_qual.
           simpl; auto.
  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    eapply QualValid_subst_index_usable; eauto.
    erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      eapply proj1.
      simpl in *.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eauto.
      - auto.
      - eauto.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
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
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
       match goal with
       | [ H : In ?T _ |- QualValid (qual ?F) _ ] =>
           let H' := fresh "H" in
           assert (H' : TypeValid F T);
           [ | inv H'; auto ]
       end.
       eapply proj1.
       match goal with
       | [ H : forall _ _, _ |- _ ] =>
           eapply H
       end.
       --- eauto.
       --- auto.
       --- eauto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ H : In _ (map _ _) |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
           rewrite Forall_forall in H;
           specialize (H _ H'); eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eauto.
      - auto.
      - eauto.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- eapply proj2.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- erewrite loc_debruijn_subst_ext;
         [ | | eauto ];
         solve_ineqs.
       rewrite loc_fctx_subst_qual; auto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- erewrite loc_debruijn_subst_ext;
         [ | | eauto ];
         solve_ineqs.
       rewrite loc_fctx_subst_qual; auto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- erewrite loc_debruijn_subst_ext;
         [ | | eauto ];
         solve_ineqs.
       rewrite loc_fctx_subst_qual; auto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{ eapply InstIndValid_at_subst_weak_loc; eauto. }
      - eapply debruijn_subst_ext_under_knd; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
       match goal with
       | [ H : context[TypeValid ?F (QualT ?PT ?Q)] |- QualValid (qual _) ?Q ] =>
	       assert (QualValid (qual F) Q);
           [ let H' := fresh "H" in
             assert (H' : TypeValid F (QualT PT Q));
             [ | inv H'; auto ] | ]
       end.
       {
         match goal with
         | [ H : forall _ _, _ |- _ ] => eapply H
         end.
         2:{ eapply InstIndValid_at_subst_weak_loc; eauto. }
         - eapply debruijn_subst_ext_under_knd; eauto.
         - eauto.
       }
       erewrite <-qual_fctx_subst_weak_loc_spec; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H
       end.
       2:{ eapply InstIndValid_at_subst_weak_loc; eauto. }
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_qual.
           erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
           2:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           rewrite <-InstFunctionCtxInd_under_ks_weak_loc.
           simpl.
           rewrite plus_zero; auto.
  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- match goal with
       | [ |- QualLeq _ (QualConst Linear) (subst'_qual ?F _) = _ ] =>
         replace (QualConst Linear) with (subst'_qual F Linear) by auto
       end.
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
       econstructor; eauto.
    -- erewrite loc_debruijn_subst_ext;
         [ | | eauto ];
         solve_ineqs.
       rewrite loc_fctx_subst_qual; auto.
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      simpl in *.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
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
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      simpl in *.
      destructAll.
      eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
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
      apply type_fctx_subst_qual_eifc. }
    erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
    split.
    { erewrite size_fctx_subst_qual_index_alternate; eauto. }
    repeat split; eauto.
    -- erewrite size_fctx_subst_qual_index_alternate; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
    -- erewrite size_fctx_subst_qual_index_alternate; eauto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
    -- match goal with
       | [ |- QualLeq _ (subst'_qual ?F _) _ = _ ] =>
         replace (QualConst Unrestricted) with (subst'_qual F Unrestricted) by auto
       end.
       eapply QualLeq_subst_index_usable.
       6-7: erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
       all: eauto.
       --- match goal with
           | [ H : context[TypeValid _ (QualT ?P ?Q) /\ _],
               H' : InstIndValid_at ?F _ _ |- _ ] =>
               let H' := fresh "H" in
               assert (H' : TypeValid F (QualT P Q)); [ eapply H; eauto | ];
               inv H'; auto
           end.
       --- econstructor; eauto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{ eapply InstIndValid_at_subst_weak_pretype; eauto. }
      - eapply debruijn_subst_ext_under_knd; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite size_fctx_subst_qual_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_qual; simpl; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- eapply InstIndValid_at_subst_weak_pretype; eauto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_qual.
           erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype.
           simpl; auto.
  - split.
    1:{
      econstructor; eauto.
      all: eapply Forall_impl; [ | eauto ].
      all: intros; simpl in *.
      all:
        match goal with
        | [ H : forall _ _, _ |- _ ] => eapply H; eauto
        end.
    }
    econstructor; eauto.
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
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{
        eapply InstIndValid_at_add_constraints; eauto.
      }
      - rewrite <-fold_right_ks_of_kvs.
        eapply debruijn_subst_ext_under_kindvars; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- eapply KindVarsValid_subst_qual_index; auto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_kindvars; eauto.
       --- rewrite fold_right_ks_of_kvs.
           apply InstIndValid_at_add_constraints; auto.
       --- rewrite fold_right_ks_of_kvs.
           rewrite <-InstFunctionCtxInd_under_ks_unroll_qual.
           erewrite debruijn_subst_ext_conds_to_under_ks_qual_index; eauto.
           rewrite InstFunctionCtxInd_under_ks_add_constraints.
           simpl; auto.
Qed.

Lemma type_subst_size_index : forall {F ks sz},
    map
      (fun '(s, q0, hc) =>
         (subst'_size
            (under_ks' ks (subst'_of (ext SSize sz id))) s,
          subst'_qual
            (under_ks' ks (subst'_of (ext SSize sz id))) q0, hc))
      (type
         (update_size_ctx (remove_nth (size F) (ks SSize)) F))
    =
    map
      (fun '(s, q, hc) =>
         (subst'_size
            (under_ks' ks (subst'_of (ext SSize sz id)))
            s,
          q,
          hc))
      (type F).
Proof.
  destruct F; subst; simpl in *.
  intros.
  apply map_ext.
  intros.
  destruct_prs.
  erewrite qual_debruijn_subst_ext;
    [ | | eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds ];
    solve_ineqs.
  auto.
Qed.

Lemma subst_size_SizeVar : forall {ks sz v},
    v <> ks SSize ->
    subst'_size
      (under_ks' ks (subst'_of (ext SSize sz id)))
      (SizeVar v)
    = SizeVar (shift_down_after v (ks SSize) 0).
Proof.
  intros; simpl.
  unfold get_var'.
  unfold under_ks'.
  handle_ineq.
  - unfold var'.
    unfold var.
    simpl.
    unfold shift_down_after.
    handle_ineq.
    auto.
  - unfold ext.
    simpl.
    match goal with
    | [ |- context[dec_eq ?A ?B] ] =>
        remember (dec_eq A B) as obj; destruct obj; [ lia | ]
    end.
    simpl.
    unfold get_var'.
    unfold weaks'.
    unfold var.
    simpl.
    unfold plus.
    unfold zero.
    unfold shift_down_after.
    handle_ineq.
    match goal with
    | [ |- SizeVar ?A = SizeVar ?B ] =>
        replace B with A; auto
    end.
    lia.
Qed.

Lemma SizeValid_subst_size_no_effect : forall {size sz ks su},
    SizeValid size sz ->
    nth_error size (ks SSize) = None ->
    subst'_size (under_ks' ks su) sz = sz.
Proof.
  intros.
  match goal with
  | [ H : SizeValid _ _ |- _ ] => induction H; subst; auto
  end.
  1:{
    simpl.
    rewrite IHSizeValid1; auto.
    rewrite IHSizeValid2; auto.
  }
  simpl.
  unfold get_var'.
  unfold under_ks'.
  handle_ineq.
  - unfold var'.
    unfold debruijn.var.
    simpl.
    auto.
  - match goal with
    | [ H : ?A <= ?B |- _ ] =>
        assert (B < A); [ | lia ]
    end.
    eapply OrdersEx.Nat_as_OT.lt_le_trans.
    -- eapply nth_error_Some_usable; eauto.
    -- rewrite <-nth_error_None; auto.
Qed.

Lemma model_satisfies_context_SizeLeq_quotient_for_non_existent_var    : forall {idx f szctx sz model model' szctx'},
    (forall szc, f (SizeConst szc) = SizeConst szc) ->
    (forall v,
        v <> idx ->
        f (SizeVar v) = SizeVar (shift_down_after v idx 0)) ->
    f (SizeVar idx) = sz ->
    (forall sz1 sz2, f (SizePlus sz1 sz2) = SizePlus (f sz1) (f sz2)) ->
    szctx'
    =
    map
      (fun '(szs0, szs1) =>
         (map f szs0, map f szs1))
      szctx ->
    nth_error szctx idx = None ->
    model_satisfies_context Peano.le interp_size model szctx' ->
    model' =
      (fun v : nat =>
         if Nat.eq_dec v idx
         then interp_size model sz
         else model (shift_down_after v idx 0)) ->
    model_satisfies_context Peano.le interp_size model' szctx /\
    interp_size model' =
    (fun sz' : Size => interp_size model (f sz')).
Proof.
  intros.
  match goal with
  | [ |- ?A /\ ?B ] =>
    let H := fresh "H" in assert (H : B)
  end.
  {
    apply FunctionalExtensionality.functional_extensionality.
    intros; subst.
    match goal with | [ X : Size  |- _ ] => induction X end.
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
      | [ H : context[_ (SizePlus _ _) = SizePlus _ _] |- _ ] =>
          rewrite H
      end.
      simpl.
      auto.
    - match goal with
      | [ H : context[_ (SizeConst _) = SizeConst _] |- _ ] =>
          rewrite H
      end.
      simpl; auto.
  }
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
  - match goal with
    | [ H : interp_size _ = _ |- _ ] =>
      repeat rewrite H
    end.
    match goal with
    | [ |- context[interp_size _ (?F _)] ] =>
        match goal with
        | [ |- context[Peano.le _ (_ ?IDX)] ] =>
            match goal with
            | [ H : forall _ _ _, _
                |- Forall _ ?L0 /\ Forall _ ?L1 ] =>
                specialize (H IDX (map F L0) (map F L1));
                unfold shift_down_after in H
            end
        end
    end.
    unfold shift_down_after.
    match goal with
    | [ H : context[?A <? ?B] |- _ ] =>
        replace (A <? B) with true in *
    end.
    2:{
      apply eq_sym.
      rewrite OrdersEx.Nat_as_DT.ltb_lt.
      eapply OrdersEx.Nat_as_OT.lt_le_trans.
      - eapply nth_error_Some_usable; eauto.
      - rewrite <-nth_error_None; auto.
    }
    simpl in *.
    match goal with
    | [ H : context[nth_error (map _ _)] |- _ ] =>
        erewrite nth_error_map in H; eauto;
        simpl in *; specialize (H eq_refl)
    end.
    destructAll.
    do 2 match goal with
      | [ H : Forall _ (map _ _) |- _ ] =>
          apply Forall_comp_map_inv in H
      end.
    auto.
Qed.

Lemma SizeLeq_quotient_for_non_existent_var : forall {f idx szctx szctx' sz sz1 sz2},
    (forall szc, f (SizeConst szc) = SizeConst szc) ->
    (forall v,
        v <> idx ->
        f (SizeVar v) = SizeVar (shift_down_after v idx 0)) ->
    f (SizeVar idx) = sz ->
    (forall sz1 sz2, f (SizePlus sz1 sz2) = SizePlus (f sz1) (f sz2)) ->
    f sz1 = sz1 ->
    f sz2 = sz2 ->
    szctx'
    =
    map
      (fun '(szs0, szs1) =>
         (map f szs0, map f szs1))
      szctx ->
    SizeLeq szctx sz1 sz2 = Some true ->
    nth_error szctx idx = None ->
    SizeLeq
      szctx'
      sz1
      sz2
    =
      Some true.
Proof.
  intros.
  rewrite SizeLeq_desc in *.
  unfold ctx_imp_leq in *.
  intros.
  eapply prove_using_unknown_lemma.
  {
    eapply model_satisfies_context_SizeLeq_quotient_for_non_existent_var; eauto.
    apply eq_refl.
  }

  intros; split; auto.
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.
  match goal with
  | [ H : interp_size ?M2 = _
      |- Peano.le (interp_size ?M ?SZ1) (interp_size ?M ?SZ2) ] =>
      replace (interp_size M SZ1) with (interp_size M2 SZ1);
      [ replace (interp_size M SZ2) with (interp_size M2 SZ2); [ | rewrite H ] | rewrite H ]
  end.
  2-3:
    match goal with
    | [ H : _ = ?SZ |- _ = interp_size _ ?SZ ] => rewrite H; auto
    end.
  match goal with
  | [ H : forall _, _ -> Peano.le _ _ |- _ ] =>
      eapply H; eauto
  end.
Qed.

(* uses models, noble will do *)
Lemma SizeLeq_subst_index : forall {F ks idx sz1 sz2},
    InstIndValid_at F ks idx ->
    SizeValid (size F) sz1 ->
    SizeValid (size F) sz2 ->
    SizeLeq (size F) sz1 sz2 = Some true ->
    SizeLeq
      (size (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_size (under_ks' ks (subst'_of (subst_of_index idx)))
                   sz1)
      (subst'_size (under_ks' ks (subst'_of (subst_of_index idx)))
                   sz2)
    = Some true.
Proof.
  intros.
  destruct idx; simpl in *.
  1,3-4: erewrite size_debruijn_subst_ext.
  3,6,9: eapply debruijn_subst_under_ks.
  3-5: eapply simpl_debruijn_subst_ext_conds.
  all: solve_ineqs.
  1-3: erewrite size_debruijn_subst_ext.
  3,6,9: eapply debruijn_subst_under_ks.
  3-5: eapply simpl_debruijn_subst_ext_conds.
  all: solve_ineqs.
  1: rewrite size_fctx_subst_loc_alternate.
  2: rewrite size_fctx_subst_qual_index_alternate.
  3: rewrite size_fctx_subst_pretype_alternate.
  1-3: auto.

  match goal with
  | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
  end.
  - rewrite nth_error_None_remove_nth; auto.
    erewrite SizeValid_subst_size_no_effect; eauto.
    erewrite SizeValid_subst_size_no_effect; eauto.
    destruct F; subst; simpl in *.
    eapply SizeLeq_quotient_for_non_existent_var; eauto.
    6:{
      unfold subst'_sizes; eauto.
    }
    -- auto.
    -- intros.
       eapply subst_size_SizeVar.
       auto.
    -- intros; simpl; auto.
    -- erewrite SizeValid_subst_size_no_effect; eauto.
    -- erewrite SizeValid_subst_size_no_effect; eauto.
  - match goal with
    | [ H : InstIndValid _ _ _ |- _ ] => inv H
    end.
    eapply SizeLeq_quotient; eauto.
    -- intros.
       eapply subst_size_SizeVar.
       auto.
    -- match goal with
       | [ |- context[update_size_ctx (remove_nth (size ?F) _)] ] =>
           destruct F; subst; simpl in *
       end.
       rewrite remove_nth_map.
       unfold subst'_sizes; auto.
    -- unfold subst'_sizes in *.
       simpl in *.
       match goal with
       | [ H : Forall _ (map _ ?L) |- Forall _ ?L ] =>
           apply Forall_comp_map_inv in H
       end.
       unfold subst'_sizes in *.
       match goal with
       | [ |- context[get_var' ?A ?B (under_ks' ?KS (subst'_of (ext SSize ?SZ ?ID)))] ] =>
           replace (get_var' A B (under_ks' KS (subst'_of (ext SSize SZ ID)))) with (subst'_size (weaks' KS) SZ); auto
       end.
       1:{
         eapply Forall_impl; eauto.
         intros; simpl in *.
         destructAll.
         auto.
       }
       unfold get_var'.
       unfold under_ks'.
       handle_ineq.
       unfold ext.
       simpl.
       match goal with
       | [ |- context[dec_eq ?A ?B] ] =>
           remember (dec_eq A B) as obj; destruct obj; [ | lia ]
       end.
       rewrite plus_zero.
       auto.
    -- unfold subst'_sizes in *.
       simpl in *.
       match goal with
       | [ H : Forall _ (map _ ?L) |- Forall _ ?L ] =>
           apply Forall_comp_map_inv in H
       end.
       unfold subst'_sizes in *.
       match goal with
       | [ |- context[get_var' ?A ?B (under_ks' ?KS (subst'_of (ext SSize ?SZ ?ID)))] ] =>
           replace (get_var' A B (under_ks' KS (subst'_of (ext SSize SZ ID)))) with (subst'_size (weaks' KS) SZ); auto
       end.
       1:{
         eapply Forall_impl; eauto.
         intros; simpl in *.
         destructAll.
         auto.
       }
       unfold get_var'.
       unfold under_ks'.
       handle_ineq.
       unfold ext.
       simpl.
       match goal with
       | [ |- context[dec_eq ?A ?B] ] =>
           remember (dec_eq A B) as obj; destruct obj; [ | lia ]
       end.
       rewrite plus_zero.
       auto.
Qed.

Lemma SizeLeq_subst_index_general : forall {F ks idx sz1 sz2 F' sz1' sz2'},
    InstIndValid_at F ks idx ->
    SizeValid (size F) sz1 ->
    SizeValid (size F) sz2 ->
    SizeLeq (size F) sz1 sz2 = Some true ->
    F' = size (InstFunctionCtxInd_under_ks F ks idx) ->
    sz1' = subst'_size (under_ks' ks (subst'_of (subst_of_index idx))) sz1 ->
    sz2' = subst'_size (under_ks' ks (subst'_of (subst_of_index idx))) sz2 ->
    SizeLeq
      F'
      sz1'
      sz2'
    = Some true.
Proof.
  intros; subst; eapply SizeLeq_subst_index; eauto.
Qed.

Lemma TypeValid_subst_size_index :
  (forall F t,
      TypeValid F t ->
      forall f ks sz F',
        debruijn_subst_ext_conds f ks SSize sz ->
        InstIndValid_at F ks (SizeI sz) ->
        F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
        TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f ks sz F',
        debruijn_subst_ext_conds f ks SSize sz ->
        InstIndValid_at F ks (SizeI sz) ->
        F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
        HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f ks sz F',
        debruijn_subst_ext_conds f ks SSize sz ->
        InstIndValid_at F ks (SizeI sz) ->
        F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
        ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f ks sz F',
        debruijn_subst_ext_conds f ks SSize sz ->
        InstIndValid_at F ks (SizeI sz) ->
        F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
        FunTypeValid F' (subst'_funtype f t)).
Proof.
  apply
    (TypesValid_ind'
       (fun F t =>
          forall f ks sz F',
            debruijn_subst_ext_conds f ks SSize sz ->
            InstIndValid_at F ks (SizeI sz) ->
            F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
            TypeValid F' (subst'_type f t))
       (fun F t =>
          forall f ks sz F',
            debruijn_subst_ext_conds f ks SSize sz ->
            InstIndValid_at F ks (SizeI sz) ->
            F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
            HeapTypeValid F' (subst'_heaptype f t))
       (fun F t =>
          forall f ks sz F',
            debruijn_subst_ext_conds f ks SSize sz ->
            InstIndValid_at F ks (SizeI sz) ->
            F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
            ArrowTypeValid F' (subst'_arrowtype f t))
       (fun F t =>
          forall f ks sz F',
            debruijn_subst_ext_conds f ks SSize sz ->
            InstIndValid_at F ks (SizeI sz) ->
            F' = InstFunctionCtxInd_under_ks F ks (SizeI sz) ->
            FunTypeValid F' (subst'_funtype f t))).
  all: intros; subst; simpl in *; auto.

  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_size; eauto.
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
    4: erewrite qual_fctx_subst_size; eauto.
    -- erewrite qual_fctx_subst_size; eauto.
    -- erewrite qual_fctx_subst_size; eauto.
    -- erewrite nth_error_type_subst_size_index; eauto.
  - econstructor; eauto.
    -- erewrite qual_fctx_subst_size; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_size; eauto.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_size; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_size; eauto.
       erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    -- erewrite qual_fctx_subst_size; eauto.
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
       erewrite type_subst_size_index; eauto.
       match goal with
       | [ |- context[?A :: map ?F ?L] ] =>
         replace (A :: map F L) with (map F (A :: L)) by auto
       end.
       erewrite sizeOfPretype_subst_size; eauto.
       eapply debruijn_subst_under_ks.
       eapply simpl_debruijn_subst_ext_conds; eauto.
    -- eapply SizeValid_subst_index_general; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
           match goal with
           | [ |- context[(subst'_size ?SU _, subst'_qual ?SU2 _, _)] ] =>
               replace SU2 with SU
           end.
           2:{
             apply eq_sym.
             erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
             simpl; auto.
           }
           match goal with
           | [ |- context[ext SSize ?SZ id] ] =>
               replace (ext SSize SZ id) with (subst_of_index (SizeI SZ)) by auto
           end.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype.
           simpl; auto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- prepare_Forall_with_map.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size_alternate; eauto.
    -- prepare_Forall_with_map.
       match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_size; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
       eapply LocValid_subst_index_general; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
       eapply LocValid_subst_index_general; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
       eapply LocValid_subst_index_general; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- erewrite qual_debruijn_subst_ext;
         [ | | eapply debruijn_subst_ext_under_knd ];
         eauto; solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_loc; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
           rewrite <-InstFunctionCtxInd_under_ks_weak_loc.
           simpl; auto.
  - econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
       eapply LocValid_subst_index_general; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
  - econstructor; eauto.
    prepare_Forall_with_map.
    eauto.
  - econstructor; eauto.
    prepare_Forall_with_map.
    destructAll.
    eexists.
    split.
    { erewrite sizeOfPretype_subst_no_effect; eauto; solve_ineqs.
      erewrite type_subst_size_index; eauto.
      erewrite sizeOfPretype_subst_size; eauto.
      eapply debruijn_subst_under_ks.
      eapply simpl_debruijn_subst_ext_conds; eauto. }
    split.
    {
      eapply SizeValid_subst_index_general.
      4: erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
      all: eauto.
    }
    split.
    {
      eapply SizeValid_subst_index_general; eauto.
    }
    split; eauto.
    eapply SizeLeq_subst_index_general.
    4: eauto.
    all: eauto.
    erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
  - econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_size; eauto.
  - econstructor; eauto.
    -- eapply SizeValid_subst_index_general; eauto.
       erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_size; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
           erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype.
           simpl; auto.
  - econstructor; eauto.
    all: prepare_Forall_with_map.
    all: eauto.
  - econstructor; eauto.
    -- eapply KindVarsValid_subst_size_index; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_kindvars; eauto.
       --- rewrite fold_right_ks_of_kvs.
           apply InstIndValid_at_add_constraints; auto.
       --- rewrite fold_right_ks_of_kvs.
           rewrite <-InstFunctionCtxInd_under_ks_unroll_size.
           erewrite debruijn_subst_ext_conds_to_under_ks_size_index; eauto.
           rewrite InstFunctionCtxInd_under_ks_add_constraints.
           simpl; auto.
Qed.

Lemma NoCapsPretype_to_NoCapsTyp : forall {F pt},
    NoCapsPretype (heapable F) pt = NoCapsTyp (heapable F) (QualT pt Unrestricted).
Proof.
  auto.
Qed.

Lemma heapable_unroll : forall {F},
    heapable F = map (fun '(_, _, hc) => hc) (type F).
Proof.
  auto.
Qed.

Lemma subst_type_with_const : forall {pt su qc},
    subst'_type su (QualT pt (QualConst qc)) =
    QualT (subst'_pretype su pt) (QualConst qc).
Proof.
  auto.
Qed.

Lemma heapable_InstFunctionCtxInd_under_ks_size : forall {F ks sz},
    heapable (InstFunctionCtxInd_under_ks F ks (SizeI sz)) =
    heapable F.
Proof.
  intros.
  destruct F; simpl.
  unfold subst'_function_ctx.
  unfold heapable.
  simpl.
  rewrite map_map.
  apply map_ext.
  intros.
  destruct_prs.
  auto.
Qed.

Lemma NoCapsPretype_subst_size_index : forall {pt hc f ks sz},
    debruijn_subst_ext_conds f ks SSize sz ->
    NoCapsPretype hc pt = true ->
    NoCapsPretype hc (subst'_pretype f pt) = true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall hc f ks sz,
            debruijn_subst_ext_conds f ks SSize sz ->
            NoCapsPretype hc pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks sz,
            debruijn_subst_ext_conds f ks SSize sz ->
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
    | [ H : context[_ <> SSize] |- _ ] => rewrite H; solve_ineqs
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

Lemma heapable_InstFunctionCtxInd_under_ks_qual: forall {F ks q},
    heapable (InstFunctionCtxInd_under_ks F ks (QualI q)) =
    heapable F.
Proof.
  intros.
  destruct F; simpl.
  unfold subst'_function_ctx.
  unfold heapable.
  simpl.
  rewrite map_map.
  apply map_ext.
  intros.
  destruct_prs.
  auto.
Qed.

Lemma NoCapsPretype_subst_qual_index : forall {pt hc f ks q},
    debruijn_subst_ext_conds f ks SQual q ->
    NoCapsPretype hc pt = true ->
    NoCapsPretype hc (subst'_pretype f pt) = true.
Proof.
  apply
    (Pretype_ind'
       (fun pt =>
          forall hc f ks q,
            debruijn_subst_ext_conds f ks SQual q ->
            NoCapsPretype hc pt = true ->
            NoCapsPretype hc (subst'_pretype f pt) = true)
       (fun t =>
          forall hc f ks q,
            debruijn_subst_ext_conds f ks SQual q ->
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
    | [ H : context[_ <> SQual] |- _ ] => rewrite H; solve_ineqs
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

Lemma heapable_InstFunctionCtxInd_under_ks_pretype_non_existent_var : forall {F ks pt},
    length (type F) <= (ks SPretype) ->
    heapable (InstFunctionCtxInd_under_ks F ks (PretypeI pt))
    = heapable F.
Proof.
  destruct F; intros; simpl.
  unfold subst'_function_ctx.
  unfold heapable.
  simpl in *.
  rewrite map_map.
  rewrite nth_error_None_remove_nth.
  2:{
    rewrite nth_error_None; auto.
  }
  
  apply map_ext.
  intros.
  destruct_prs.
  auto.
Qed.

Lemma heapable_InstFunctionCtxInd_under_ks_pretype_existent_var : forall {F ks pt},
    ks SPretype < length (type F) ->
    heapable (InstFunctionCtxInd_under_ks F ks (PretypeI pt))
    = remove_nth (heapable F) (ks SPretype).
Proof.
  destruct F; intros; simpl in *.
  unfold subst'_function_ctx.
  unfold heapable.
  simpl.
  rewrite map_map.
  rewrite remove_nth_map.
  apply map_ext.
  intros.
  destruct_prs.
  auto.
Qed.

Lemma subst_pretype_on_tctx : forall {A} {f ks pt} {tctx : list (Size * Qual * A)},
    debruijn_subst_ext_conds f ks SPretype pt ->
    map
      (fun '(s, q0, hc) =>
         (subst'_size f s,
          subst'_qual f q0,
          hc))
      tctx
    = tctx.
Proof.
  intros.
  match goal with
  | [ |- map ?F _ = _ ] => replace F with (fun (x : Size * Qual * A) => x); [ apply map_id | ]
  end.
  eapply Coq.Logic.FunctionalExtensionality.functional_extensionality_dep.
  intros.
  destruct_prs.
  erewrite size_debruijn_subst_ext; eauto.
  2: solve_ineqs.
  erewrite qual_debruijn_subst_ext; eauto.
  solve_ineqs.
Qed.

Lemma sizeOfPretype_subst_size_index : forall {F ks sz pt sz'},
    sizeOfPretype (type F) pt = Some sz' ->
    sizeOfPretype (type (InstFunctionCtxInd_under_ks F ks (SizeI sz))) pt =
    Some
      (subst'_size
         (under_ks' ks (subst'_of (ext SSize sz id)))
         sz').
Proof.
  intros.
  simpl.
  rewrite type_subst_size_index.
  eapply sizeOfPretype_subst_size; eauto.
  eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
Qed.

Lemma TypeValid_subst_pretype_no_effect :
  (forall F t,
      TypeValid F t ->
      forall f ks pt,
        debruijn_subst_ext_conds f ks SPretype pt ->
        length (type F) <= ks SPretype ->
        subst'_type f t = t) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f ks pt,
        debruijn_subst_ext_conds f ks SPretype pt ->
        length (type F) <= ks SPretype ->
        subst'_heaptype f t = t) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f ks pt,
        debruijn_subst_ext_conds f ks SPretype pt ->
        length (type F) <= ks SPretype ->
        subst'_arrowtype f t = t) /\
  (forall F t,
      FunTypeValid F t ->
      forall f ks pt,
        debruijn_subst_ext_conds f ks SPretype pt ->
        length (type F) <= ks SPretype ->
        subst'_funtype f t = t).
Proof.
  eapply TypesValid_ind'.
  
  all: intros; simpl in *.
  - erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - unfold get_var'.
    erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    unfold debruijn_subst_ext_conds in *.
    destructAll.
    match goal with
    | [ H : context[_ <> _ _] |- _ ] => rewrite H
    end.
    2:{
      intro; subst.
      match goal with
      | [ H : ?A = Some (_,_,_) |- _ ] =>
          let H' := fresh "H" in
          assert (H' : A = None); [ | rewrite H' in H; inv H ]
      end.
      rewrite nth_error_None; auto.
    }
    simpl.
    unfold shift_down_after.
    handle_ineq; auto.
    match goal with
    | [ H : ?A = Some (_,_,_) |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A = None); [ | rewrite H' in H; inv H ]
    end.
    rewrite nth_error_None.
    eapply le_trans; eauto.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    2:{
      eapply debruijn_subst_ext_under_knd; eauto.
    }
    2:{
      unfold plus.
      simpl.
      rewrite type_update_type_ctx.
      rewrite map_length.
      simpl.
      lia.
    }
    erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    match goal with
    | [ |- QualT (ProdT ?T1) _ = QualT (ProdT ?T2) _ ] =>
        replace T1 with T2; auto
    end.
    apply eq_sym.
    rewrite <-map_id.
    apply map_ext_Forall.
    prepare_Forall.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite loc_debruijn_subst_ext; eauto.
    solve_ineqs.
  - erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite loc_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - erewrite qual_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite loc_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    2:{
      eapply debruijn_subst_ext_under_knd; eauto.
    }
    2:{
      unfold plus.
      simpl.
      rewrite weak_loc_on_tctx.
      rewrite type_update_location_ctx.
      auto.
    }
    erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - erewrite loc_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - match goal with
    | [ |- VariantType ?T1 = VariantType ?T2 ] =>
        replace T1 with T2; auto
    end.
    apply eq_sym.
    rewrite <-map_id.
    apply map_ext_Forall.
    prepare_Forall.
    eauto.
  - match goal with
    | [ |- StructType ?T1 = StructType ?T2 ] =>
        replace T1 with T2; auto
    end.
    apply eq_sym.
    rewrite <-map_id.
    apply map_ext_Forall.
    prepare_Forall.
    destruct_prs.
    destructAll.
    match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    simpl.
    erewrite size_debruijn_subst_ext; eauto.
    solve_ineqs.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    2:{
      eapply debruijn_subst_ext_under_knd; eauto.
    }
    2:{
      unfold plus.
      simpl.
      rewrite type_update_type_ctx.
      rewrite map_length.
      simpl.
      lia.
    }
    erewrite size_debruijn_subst_ext; eauto.
    2: solve_ineqs.
    erewrite qual_debruijn_subst_ext; eauto.
    solve_ineqs.
  - match goal with
    | [ |- Arrow ?T1 _ = Arrow ?T2 _ ] =>
        replace T1 with T2
    end.
    1:
      match goal with
      | [ |- Arrow _ ?T1 = Arrow _ ?T2 ] =>
          replace T1 with T2; auto
      end.
    all: apply eq_sym.
    all: rewrite <-map_id.
    all: apply map_ext_Forall.
    all: prepare_Forall.
    all: eauto.
  - match goal with
    | [ H : forall _ _, _ |- _ ] => erewrite H; eauto
    end.
    2:{
      eapply debruijn_subst_ext_under_kindvars; eauto.
    }
    2:{
      rewrite fold_right_ks_of_kvs.
      unfold plus.
      rewrite add_constraints_to_ks_of_kvs; simpl.
      rewrite app_length.
      rewrite length_collect_tctx.
      rewrite map_length.
      lia.
    }
    erewrite pretype_subst_no_effect_on_kindvars; eauto.
Qed.

Lemma TypeValid_subst_pretype_no_effect_on_pretype : forall {F pt' pt q ks f},
    TypeValid F (QualT pt q) ->
    debruijn_subst_ext_conds f ks SPretype pt' ->
    length (type F) <= ks SPretype ->
    subst'_pretype f pt = pt.
Proof.
  intros.
  assert (Hspec : subst'_type f (QualT pt q) = QualT pt q); [ | inv Hspec ].
  2:{
    match goal with
    | [ H : ?A = _ |- context[?A] ] => repeat rewrite H; auto
    end.
  }
  eapply TypeValid_subst_pretype_no_effect; eauto.
Qed.

Lemma sizeOfPretype_subst_pretype_general : forall {pt tctx szctx ks pt' tausz tausz' szc qc hc},
    sizeOfPretype tctx pt = Some tausz ->
    sizeOfPretype (remove_nth tctx (ks SPretype))
                  (subst'_pretype (weaks' ks) pt')
    = Some tausz' ->
    nth_error tctx (ks SPretype) = Some (szc, qc, hc) ->
    SizeLeq szctx tausz' szc = Some true ->
    SizeValid szctx tausz ->
    SizeValid szctx tausz' ->
    exists sz',
      sizeOfPretype
        (remove_nth tctx (ks SPretype))
        (subst'_pretype
           (under_ks' ks (subst'_of (ext SPretype pt' id)))
           pt)
      =
      Some sz' /\
      SizeValid szctx sz' /\
      SizeLeq szctx sz' tausz = Some true.
Proof.
  eapply
    (Pretype_ind'
       (fun pt =>
          forall tctx szctx ks pt' tausz tausz' szc qc hc,
            sizeOfPretype tctx pt = Some tausz ->
            sizeOfPretype (remove_nth tctx (ks SPretype))
                          (subst'_pretype (weaks' ks) pt')
            = Some tausz' ->
            nth_error tctx (ks SPretype) = Some (szc, qc, hc) ->
            SizeLeq szctx tausz' szc = Some true ->
            SizeValid szctx tausz ->
            SizeValid szctx tausz' ->
            exists sz',
              sizeOfPretype
                (remove_nth tctx (ks SPretype))
                (subst'_pretype
                   (under_ks' ks (subst'_of (ext SPretype pt' id)))
                   pt)
              =
              Some sz' /\
              SizeValid szctx sz' /\
              SizeLeq szctx sz' tausz = Some true)
       (fun t =>
          forall tctx szctx ks pt' tausz tausz' szc qc hc,
            sizeOfType tctx t = Some tausz ->
            sizeOfPretype (remove_nth tctx (ks SPretype))
                          (subst'_pretype (weaks' ks) pt')
            = Some tausz' ->
            nth_error tctx (ks SPretype) = Some (szc, qc, hc) ->
            SizeLeq szctx tausz' szc = Some true ->
            SizeValid szctx tausz ->
            SizeValid szctx tausz' ->
            exists sz',
              sizeOfType
                (remove_nth tctx (ks SPretype))
                (subst'_type
                   (under_ks' ks (subst'_of (ext SPretype pt' id)))
                   t)
              =
              Some sz' /\
              SizeValid szctx sz' /\
              SizeLeq szctx sz' tausz = Some true)
       (fun _ => True)
       (fun _ => True)
       (fun _ => True)).

  all: intros; simpl in *; eauto.
  all: try now ltac:(eexists; split; eauto;
                     split; auto;
                     apply SizeLeq_Refl).
  - unfold get_var'.
    unfold under_ks'.
    handle_ineq.
    -- erewrite nth_error_shift_down_usable.
       --- eexists; split; eauto.
           split; auto.
           apply SizeLeq_Refl.
       --- lia.
       --- unfold shift_down_after.
           handle_ineq.
    -- rewrite plus_zero.
       unfold ext.
       simpl.
       match goal with
       | [ |- context[dec_eq ?A ?B] ] =>
           remember (dec_eq A B) as obj; destruct obj
       end.
       --- eexists; split; eauto.
           split; auto.
           match goal with
           | [ H : ?A - ?B = 0 |- _ ] =>
               assert (A = B) by lia
           end.
           subst.
           match goal with
           | [ H : ?A = _, H' : context[option_map _ ?A] |- _ ] =>
               rewrite H in H'
           end.
           simpl in *.
           match goal with
           | [ H : Some _ = Some _ |- _ ] => inv H
           end.
           auto.
       --- simpl.
           erewrite nth_error_shift_down_usable.
           ---- eexists; split; eauto.
                split; auto.
                apply SizeLeq_Refl.
           ---- lia.
           ---- unfold shift_down_after.
                handle_ineq.
                unfold zero.
                lia.
  - rewrite map_map.
    match goal with
    | [ H : fold_size _ = Some ?SZ, H' : SizeValid _ ?SZ |- _ ] =>
        specialize (fold_size_SizeValid_inv H H')
    end.
    intros.
    match goal with
    | [ H : Forall _ (map _ _) |- _ ] =>
        apply Forall_comp_map_inv in H
    end.
    eapply fold_size_SizeValid_SizeLeq_inv; eauto.
    prepare_Forall.
    destructAll.
    eapply prove_using_unknown_lemma.
    {
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    intros.
    split; auto.
    destructAll.
    do 2 eexists.
    eauto.
  - erewrite qual_debruijn_subst_ext.
    3: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    2: solve_ineqs.
    unfold under'.
    rewrite under_ks_under_ks_subst_of.
    match goal with
    | [ |- context[?A :: remove_nth ?L ?IDX] ] =>
        match goal with
        | [ |- context[under_ks' ?KS] ] =>
            replace (A :: remove_nth L IDX) with (remove_nth (A :: L) (KS SPretype)) by auto
        end
    end.
    match goal with
    | [ H : forall _ _, _ |- _ ] => eapply H; eauto
    end.
    simpl.
    rewrite compose_weak_weaks.
    match goal with
    | [ |- context[subst'_pretype ?SU ?PT] ] =>
        replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
    end.
    rewrite <-subst_ext'_assoc.
    simpl.
    rewrite <-weaks'_sing.
    match goal with
    | [ |- context[?A :: ?B] ] =>
        replace (A :: B) with ([A] ++ B) by auto
    end.
    erewrite sizeOfPretype_weaks; auto.
    2:{
      apply map_ext.
      intros.
      destruct_prs.
      rewrite weaks'_sing.
      rewrite pretype_weak_no_effect_on_size.
      auto.
    }
    match goal with
    | [ H : ?A = _ |- option_map _ ?A = _ ] => rewrite H
    end.
    simpl.
    rewrite weaks'_sing.
    rewrite pretype_weak_no_effect_on_size.
    auto.
  - unfold under'.
    rewrite under_ks_under_ks_subst_of.
    match goal with
    | [ |- context[remove_nth _ ?IDX] ] =>
        match goal with
        | [ |- context[under_ks' ?KS] ] =>
            replace IDX with (KS SPretype) by auto
        end
    end.
    match goal with
    | [ H : forall _ _, _ |- _ ] => eapply H; eauto
    end.
    rewrite compose_weak_weaks.
    match goal with
    | [ |- context[subst'_pretype ?SU ?PT] ] =>
        replace (subst'_pretype SU PT) with (subst_ext' SU PT) by auto
    end.
    rewrite <-subst_ext'_assoc.
    simpl.
    rewrite <-weaks'_sing.
    match goal with
    | [ |- sizeOfPretype ?L _ = _ ] =>
        replace L with ([] ++ L) by auto
    end.
    erewrite sizeOfPretype_weaks; auto.
    2:{
      unfold plus.
      simpl.
      apply map_ext.
      intros.
      destruct_prs.
      rewrite weaks'_sing.
      rewrite loc_weak_no_effect_on_size.
      auto.
    }
    match goal with
    | [ H : ?A = _ |- option_map _ ?A = _ ] => rewrite H
    end.
    simpl.
    rewrite weaks'_sing.
    rewrite loc_weak_no_effect_on_size.
    auto.
Qed.

Lemma nth_error_set_nth_type : forall {A B C} {idx} {typ : list (A * B * C)} {sz q hc sz' q' hc' sz'' idx'},
    nth_error typ idx = Some (sz, q, hc) ->
    nth_error typ idx' = Some (sz', q', hc') ->
    nth_error (set_nth typ idx' (sz'', q', hc')) idx =
    Some (if idx =? idx' then sz'' else sz, q, hc).
Proof.
  induction idx.
  - intros.
    destruct typ.
    all: simpl in *.
    all:
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      | [ H : Some _ = Some _ |- _ ] => inv H
      end.
    destruct idx'; simpl in *; auto.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    auto.
  - intros.
    destruct typ.
    all: destruct idx'; simpl in *; auto.
    1:{
      match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
    }
    rewrite Nat.sub_0_r.
    erewrite IHidx; eauto.
Qed.

Lemma update_type_ctx_idem : forall {F typ1 typ2},
    update_type_ctx typ1 (update_type_ctx typ2 F) = 
    update_type_ctx typ1 F.
Proof.
  destruct F; simpl; auto.
Qed.

(* medium *)
Lemma sizeOfPretype_subst_index : forall {F ks idx pt tausz q},
    InstIndValid_at F ks idx ->
    TypeValid F (QualT pt q) ->
    sizeOfPretype (type F) pt = Some tausz ->
    SizeValid (size F) tausz ->
    exists sz',
      sizeOfPretype
        (type (InstFunctionCtxInd_under_ks F ks idx))
        (subst'_pretype
           (under_ks' ks (subst'_of (subst_of_index idx)))
           pt)
      =
      Some sz' /\
      SizeValid (size (InstFunctionCtxInd_under_ks F ks idx)) sz' /\
      SizeLeq
        (size (InstFunctionCtxInd_under_ks F ks idx))
        sz'
        (subst'_size
           (under_ks' ks (subst'_of (subst_of_index idx)))
           tausz)
      = Some true.
Proof.
  intros.
  destruct idx.
  - erewrite sizeOfPretype_subst_no_effect.
    2:{
      eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    }
    2: solve_ineqs.
    simpl.
    rewrite type_fctx_subst_loc_alternate.
    rewrite size_fctx_subst_loc_alternate.
    eexists.
    split; eauto.
    split; auto.
    erewrite size_debruijn_subst_ext.
    3: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    2: solve_ineqs.
    apply SizeLeq_Refl.
  - erewrite sizeOfPretype_subst_no_effect.
    2:{
      eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    }
    2: solve_ineqs.
    erewrite sizeOfPretype_subst_size_index; eauto.
    eexists.
    split; eauto.
    split.
    all:
      match goal with
      | [ |- context[ext SSize ?SZ ?ID] ] =>
          replace (ext SSize SZ ID) with (subst_of_index (SizeI SZ)) by auto
      end.
    -- eapply SizeValid_subst_index; auto.
    -- eapply SizeLeq_subst_index; eauto.
       apply SizeLeq_Refl.
  - erewrite sizeOfPretype_subst_no_effect.
    2:{
      eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    }
    2: solve_ineqs.
    simpl.
    rewrite size_fctx_subst_qual_index_alternate.
    eexists.
    split.
    {
      erewrite sizeOfPretype_eifc; eauto.
      apply type_fctx_subst_qual_eifc.
    }
    split; auto.
    erewrite size_debruijn_subst_ext.
    3: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    2: solve_ineqs.
    apply SizeLeq_Refl.
  - match goal with
    | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
    end.
    -- erewrite TypeValid_subst_pretype_no_effect_on_pretype; eauto.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       2:{
         rewrite <-nth_error_None.
         unfold plus.
         unfold zero.
         simpl.
         rewrite Nat.add_0_r; auto.
       }
       simpl.
       rewrite size_fctx_subst_pretype_alternate.
       rewrite nth_error_None_remove_nth; auto.
       rewrite type_update_type_ctx.
       erewrite subst_pretype_on_tctx.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       eexists.
       split; eauto.
       split; auto.
       erewrite size_debruijn_subst_ext.
       3: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       2: solve_ineqs.
       apply SizeLeq_Refl.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       simpl in *.
       erewrite subst_pretype_on_tctx.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       match goal with
       | [ H : context[sizeOfPretype (map _ _)] |- _ ] =>
           erewrite subst_pretype_on_tctx in H
       end.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       rewrite size_fctx_subst_pretype_alternate.
       match goal with
       | [ H : context[SizeLeq (map _ _)] |- _ ] =>
           rewrite size_fctx_subst_pretype_alternate in H
       end.
       erewrite size_debruijn_subst_ext.
       3: eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       2: solve_ineqs.
       destruct F; simpl in *.
       eapply sizeOfPretype_subst_pretype_general; eauto.
       eapply SizeValid_length; eauto.
       apply map_length.
Qed.

Lemma TypeValid_SizeLeq_usable : forall {F sz q hc t tctx sz' F'},
    TypeValid F t ->
    type F = (sz, q, hc) :: tctx ->
    SizeLeq (size F) sz' sz = Some true ->
    sizes_substitutable (size F) sz' sz ->
    F' = update_type_ctx ((sz', q, hc) :: tctx) F ->
    TypeValid F' t.
Proof.
  intros; subst; eapply TypeValid_SizeLeq; eauto.
Qed.

Lemma loc_fctx_subst_pretype : forall {F ks pt},
    location
      (subst'_function_ctx
         (under_ks' ks (subst'_of (ext SPretype pt id)))
         (update_type_ctx (remove_nth (type F) (ks SPretype)) F))
    =
    location F.
Proof.
  destruct F; simpl; auto.
Qed.

Lemma TypeValid_subst_pretype_index :
  (forall F t,
      TypeValid F t ->
      forall f ks pt F',
        debruijn_subst_ext_conds f ks SPretype pt ->
        InstIndValid_at F ks (PretypeI pt) ->
        F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
        TypeValid F t /\ TypeValid F' (subst'_type f t)) /\
  (forall F t,
      HeapTypeValid F t ->
      forall f ks pt F',
        debruijn_subst_ext_conds f ks SPretype pt ->
        InstIndValid_at F ks (PretypeI pt) ->
        F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
        HeapTypeValid F t /\ HeapTypeValid F' (subst'_heaptype f t)) /\
  (forall F t,
      ArrowTypeValid F t ->
      forall f ks pt F',
        debruijn_subst_ext_conds f ks SPretype pt ->
        InstIndValid_at F ks (PretypeI pt) ->
        F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
        ArrowTypeValid F t /\ ArrowTypeValid F' (subst'_arrowtype f t)) /\
  (forall F t,
      FunTypeValid F t ->
      forall f ks pt F',
        debruijn_subst_ext_conds f ks SPretype pt ->
        InstIndValid_at F ks (PretypeI pt) ->
        F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
        FunTypeValid F t /\ FunTypeValid F' (subst'_funtype f t)).
Proof.
  apply
    (TypesValid_ind'
       (fun F t =>
          forall f ks pt F',
            debruijn_subst_ext_conds f ks SPretype pt ->
            InstIndValid_at F ks (PretypeI pt) ->
            F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
            TypeValid F t /\ TypeValid F' (subst'_type f t))
       (fun F t =>
          forall f ks pt F',
            debruijn_subst_ext_conds f ks SPretype pt ->
            InstIndValid_at F ks (PretypeI pt) ->
            F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
            HeapTypeValid F t /\ HeapTypeValid F' (subst'_heaptype f t))
       (fun F t =>
          forall f ks pt F',
            debruijn_subst_ext_conds f ks SPretype pt ->
            InstIndValid_at F ks (PretypeI pt) ->
            F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
            ArrowTypeValid F t /\ ArrowTypeValid F' (subst'_arrowtype f t))
       (fun F t =>
          forall f ks pt F',
            debruijn_subst_ext_conds f ks SPretype pt ->
            InstIndValid_at F ks (PretypeI pt) ->
            F' = InstFunctionCtxInd_under_ks F ks (PretypeI pt) ->
            FunTypeValid F t /\ FunTypeValid F' (subst'_funtype f t))).
  all: intros; subst; simpl in *; auto.

  - split.
    1:{ econstructor; eauto. }
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    erewrite qual_fctx_subst_pretype; eauto.
  - split.
    1:{ econstructor; eauto. }
    unfold get_var'.
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
       eapply TypeValid_QualLeq.
       --- erewrite qual_fctx_subst_pretype; eauto.
       --- erewrite qual_fctx_subst_pretype; eauto.
       --- match goal with
           | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
           end.
           ---- match goal with
                | [ H : ?A = Some _, H' : ?A = None |- _ ] =>
                    rewrite H in H'; inv H'
                end.
           ---- match goal with
                | [ H : InstIndValid _ _ _ |- _ ] => inv H
                end.
                simpl in *.
                match goal with
                | [ H : ?A = Some _, H' : ?A = Some _ |- _ ] =>
                    rewrite H in H'; inv H'
                end.
                auto.
    -- match goal with
       | [ H : context[_ <> _ _] |- _ ] => rewrite H; auto
       end.
       simpl.
       econstructor.
       4: erewrite qual_fctx_subst_pretype; eauto.
       --- erewrite qual_fctx_subst_pretype; eauto.
       --- erewrite qual_fctx_subst_pretype; eauto.
       --- erewrite nth_error_type_subst_pretype_index; eauto.
  - split.
    1:{
      econstructor; eauto.
      eapply proj1.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eapply debruijn_subst_ext_under_knd; eauto.
      - apply InstIndValid_at_subst_weak_pretype; auto.
      - eauto.
    }
    match goal with
    | [ H : sizeOfPretype ((?SZ, ?Q, ?HC) :: type ?F) _ = _ |- _ ] =>
        replace ((SZ, Q, HC) :: type F) with (type (add_constraint F (TYPE SZ Q HC))) in H
    end.
    2:{
      simpl.
      rewrite weak_pretype_on_tctx.
      rewrite type_update_type_ctx; auto.
    }
    match goal with
    | [ H : context[add_constraint ?F ?KV],
        H' : InstIndValid_at ?F ?KS ?PT |- _ ] =>
        assert (InstIndValid_at (add_constraint F KV) (plus (sing (kind_of_kindvar KV) 1) KS) PT)
    end.
    { apply InstIndValid_at_add_constraint; auto. }

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst_index.
      3: eauto.
      1: eauto.
      - match goal with
        | [ H : sizeOfPretype _ _ = Some ?SZ |- context G[SizeConst 0] ] =>
            let goal := context G[SZ] in
            let H' := fresh "H" in
            assert (H' : goal)
        end.
        {
          simpl.
          match goal with
          | [ H : forall _ _, _ |- _ ] => eapply H
          end.
          2:{
            eapply InstIndValid_at_subst_weak_pretype.
            eauto.
          }
          1:{
            eapply debruijn_subst_ext_under_knd; eauto.
          }
          eauto.
        }
        eapply TypeValid_SizeLeq_usable; eauto.
        -- match goal with
           | [ |- context[add_constraint ?F ?KV] ] =>
               replace (add_constraint F KV) with (add_constraints F [KV]) by auto
           end.
           rewrite add_constraints_to_ks_of_kvs; simpl.
           eauto.
        -- apply SizeLeq_Bottom.
        -- right; left.
           split; [ apply SizeLeq_Refl | ].
           econstructor; eauto.
        -- simpl.
           match goal with
           | [ H : QualValid (qual ?F) _ |- _ ] =>
               destruct F; simpl in *
           end.
           apply Function_Ctx_eq; simpl; auto.
           rewrite pretype_weak_no_effect_on_qual.
           match goal with
           | [ |- _ :: ?A = _ :: ?B ] =>
               replace B with A; auto
           end.
           apply map_ext.
           intros.
           destruct_prs.
           rewrite plus_zero.
           rewrite weaks'_sing.
           rewrite pretype_weak_no_effect_on_size.
           rewrite pretype_weak_no_effect_on_qual.
           auto.
      - simpl.
        rewrite sizepairs_debruijn_weak_pretype.
        rewrite size_update_type_ctx.
        auto.
    }

    intros.
    split; auto.
    destructAll.
    
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext.
       3: eapply debruijn_subst_ext_under_knd; eauto.
       2: solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext.
       3: eapply debruijn_subst_ext_under_knd; eauto.
       2: solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext.
       3: eapply debruijn_subst_ext_under_knd; eauto.
       2: solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- eapply RecVarUnderRefPretype_subst_fwd; eauto.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- unfold plus; simpl; auto.
           lia.
    -- simpl in *.
       match goal with
       | [ H : sizeOfPretype (map _ _) _ = _ |- _ ] =>
           rewrite weak_pretype_on_tctx in H;
           rewrite type_update_type_ctx in H;
           erewrite subst_pretype_on_tctx in H
       end.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       erewrite subst_pretype_on_tctx.
       2:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       rewrite type_update_type_ctx.
       match goal with
       | [ H : context[plus (sing ?KND 1) ?KS ?KND] |- _ ] =>
           replace (plus (sing KND 1) KS KND) with (1 + (KS KND)) in H
       end.
       2:{
         unfold plus; simpl; lia.
       }
       simpl in *.
       erewrite qual_debruijn_subst_ext; eauto.
       2: solve_ineqs.
       match goal with
       | [ H : sizeOfPretype _ (subst'_pretype ?F _) = _
           |- context[subst'_pretype ?F2 _] ] =>
           replace F2 with F; eauto
       end.
       
       eapply debruijn_subst_ext_inj; eauto.
       --- eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       --- unfold under'.
           rewrite <-plus_assoc.
           eapply debruijn_subst_under_ks.
           rewrite plus_zero; auto.
    -- simpl in *.
       eapply SizeValid_length; eauto.
       repeat rewrite map_length.
       repeat rewrite size_update_type_ctx; auto.
    -- eapply TypeValid_SizeLeq_usable.
       --- match goal with
           | [ H : forall _ _, _ |- _ ] => eapply H; eauto
           end.
           ---- eapply debruijn_subst_ext_under_knd; eauto.
           ---- apply InstIndValid_at_subst_weak_pretype; auto.
       --- simpl.
           erewrite subst_pretype_on_tctx.
           2:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           rewrite weak_pretype_on_tctx.
           rewrite type_update_type_ctx.
           simpl.
           eauto.
       --- simpl.
           match goal with
           | [ H : SizeLeq _ _ _ = _ |- _ ] =>
               erewrite size_debruijn_subst_ext in H
           end.
           3:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           2: solve_ineqs.
           simpl in *.
           rewrite size_update_type_ctx.
           match goal with
           | [ H : SizeLeq _ _ _ = _ |- _ ] =>
               erewrite size_update_type_ctx in H
           end.
           eauto.
       --- simpl.
           right; right.
           split.
           all: eapply SizeValid_length; eauto.
           all: simpl.
           all: repeat rewrite map_length.
           all: repeat rewrite size_update_type_ctx; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_pretype.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype_pretype.
           simpl; auto.
           unfold subst'_function_ctx; simpl; auto.
           apply Function_Ctx_eq; simpl; auto.
           all: destruct C; simpl in *; auto.
           erewrite subst_pretype_on_tctx.
           2:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           rewrite weak_pretype_on_tctx.
           erewrite size_debruijn_subst_ext.
           3:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           2: solve_ineqs.
           erewrite qual_debruijn_subst_ext.
           3:{
             eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
           }
           2: solve_ineqs.
           rewrite pretype_weak_no_effect_on_size.
           rewrite pretype_weak_no_effect_on_qual.
           erewrite qual_debruijn_subst_ext; eauto.
           solve_ineqs.
  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    erewrite qual_fctx_subst_pretype; eauto.
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      eapply proj1.
      simpl in *.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eauto.
      - auto.
      - eauto.
    }
    erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
    econstructor; eauto.
    -- erewrite qual_fctx_subst_pretype; eauto.
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
       erewrite qual_fctx_subst_pretype_alternate; eauto.
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
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      - eauto.
      - auto.
      - eauto.
    }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
    }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite loc_fctx_subst_pretype; eauto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite loc_fctx_subst_pretype; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite loc_fctx_subst_pretype; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{ eapply InstIndValid_at_subst_weak_loc; eauto. }
      - eapply debruijn_subst_ext_under_knd; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto;
         [ | | eapply debruijn_subst_ext_under_knd; eauto ];
         solve_ineqs.
       erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_loc; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_pretype.
           rewrite <-InstFunctionCtxInd_under_ks_weak_loc.
           simpl; auto.
  - split.
    1:{ econstructor; eauto. }
    econstructor; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- erewrite loc_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite loc_fctx_subst_pretype; eauto.
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      simpl in *.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
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
  - split.
    1:{
      econstructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      simpl in *.
      destructAll.
      eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
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

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst_index.
      1: eauto.
      2: eauto.
      - match goal with
        | [ H : forall _ _, _ |- _ ] => eapply H; eauto
        end.
      - auto.
    }
    intros.
    split; auto.
    destructAll.
    
    eexists.
    simpl in *.
    match goal with
    | [ H : debruijn_subst_ext_conds ?F _ _ _ |- _ ] =>
        erewrite (debruijn_subst_ext_conds_to_under_ks_pretype_index (f:=F)); eauto
    end.
    split; [ eauto | ].
    erewrite size_debruijn_subst_ext.
    3:{
      eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    }
    2: solve_ineqs.
    erewrite size_fctx_subst_pretype_alternate; eauto.
    split; auto.
    split.
    {
      eapply SizeValid_length; eauto.
      rewrite map_length.
      rewrite size_update_type_ctx; auto.
    }
    split.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
       match goal with
       | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
           replace KS with (plus KS zero) by apply plus_zero;
           replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
       end.
       eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
    -- match goal with
       | [ H : SizeLeq _ ?SZ _ = _ |- SizeLeq _ ?SZ _ = _ ] =>
           erewrite size_fctx_subst_pretype_alternate in H; eauto;
           erewrite size_debruijn_subst_ext in H
       end.
       3:{
         eapply debruijn_subst_under_ks; eapply simpl_debruijn_subst_ext_conds.
       }
       2: solve_ineqs.
       eapply SizeLeq_Trans; eauto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H; eauto
      end.
    }
    econstructor; eauto.
    -- match goal with
       | [ H : forall _ _, _ |- _ ] => eapply H; eauto
       end.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{ eapply InstIndValid_at_subst_weak_pretype; eauto. }
      - eapply debruijn_subst_ext_under_knd; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- erewrite size_debruijn_subst_ext; eauto; solve_ineqs.
       simpl.
       erewrite size_fctx_subst_pretype_alternate; eauto.
    -- erewrite qual_debruijn_subst_ext; eauto; solve_ineqs.
       erewrite qual_fctx_subst_pretype; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_knd; eauto.
       --- apply InstIndValid_at_subst_weak_pretype; auto.
       --- rewrite <-InstFunctionCtxInd_under_ks_unroll_pretype.
           erewrite debruijn_subst_ext_conds_to_under_ks_pretype_index; eauto.
           rewrite <-InstFunctionCtxInd_under_ks_weak_pretype.
           simpl; auto.
  - split.
    1:{
      econstructor; eauto.
      all: eapply Forall_impl; [ | eauto ].
      all: intros; simpl in *.
      all:
        match goal with
        | [ H : forall _ _, _ |- _ ] => eapply H; eauto
        end.
    }
    econstructor; eauto.
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
  - split.
    1:{
      econstructor; eauto.
      match goal with
      | [ H : forall _ _, _ |- _ ] => eapply H
      end.
      2:{
        eapply InstIndValid_at_add_constraints; eauto.
      }
      - rewrite <-fold_right_ks_of_kvs.
        eapply debruijn_subst_ext_under_kindvars; eauto.
      - eauto.
    }
    econstructor; eauto.
    -- erewrite pretype_subst_no_effect_on_kindvars; eauto.
       eapply KindVarsValid_Function_Ctx; eauto.
       --- erewrite qual_fctx_subst_pretype; eauto.
       --- simpl.
           erewrite size_fctx_subst_pretype_alternate; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply debruijn_subst_ext_under_kindvars; eauto.
       --- rewrite fold_right_ks_of_kvs.
           apply InstIndValid_at_add_constraints; auto.
       --- rewrite fold_right_ks_of_kvs.
           rewrite <-InstFunctionCtxInd_under_ks_unroll_pretype.
           erewrite debruijn_subst_ext_conds_to_under_ks_pretype_index; eauto.
           rewrite InstFunctionCtxInd_under_ks_add_constraints.
           simpl; auto.
Qed.

(* hard *)
Lemma TypeValid_subst_index : forall {F tau ks idx},
    TypeValid F tau ->
    InstIndValid_at F ks idx ->
    TypeValid
      (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_type (under_ks' ks (subst'_of (subst_of_index idx)))
                   tau).
Proof.
  destruct idx.
  - intros.
    eapply TypeValid_subst_loc_index; eauto.
    simpl.
    match goal with
    | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
        replace KS with (plus KS zero) by apply plus_zero;
        replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
    end.
    apply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  - intros.
    eapply TypeValid_subst_size_index; eauto.
    simpl.
    match goal with
    | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
        replace KS with (plus KS zero) by apply plus_zero;
        replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
    end.
    apply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  - intros.
    eapply TypeValid_subst_qual_index; eauto.
    simpl.
    match goal with
    | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
        replace KS with (plus KS zero) by apply plus_zero;
        replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
    end.
    apply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
  - intros.
    eapply TypeValid_subst_pretype_index; eauto.
    simpl.
    match goal with
    | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
        replace KS with (plus KS zero) by apply plus_zero;
        replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
    end.
    apply debruijn_subst_under_ks.
    apply simpl_debruijn_subst_ext_conds.
Qed.

Lemma TypeValid_subst_index_usable : forall {F tau ks idx F' tau'},
    TypeValid F tau ->
    InstIndValid_at F ks idx ->
    F' = InstFunctionCtxInd_under_ks F ks idx ->
    tau' = subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) tau ->
    TypeValid F' tau'.
Proof.
  intros; subst.
  eapply TypeValid_subst_index; eauto.
Qed.

(* pretty easy *)
Lemma LocalCtxValid_subst_index : forall {F L ks idx},
    LocalCtxValid F L ->
    InstIndValid_at F ks idx ->
    LocalCtxValid
      (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_local_ctx
         (under_ks'
            ks
            (subst'_of (subst_of_index idx)))
         L).
Proof.
  intros F L.
  revert F.
  induction L; intros; inversion H; subst;  econstructor.
  - destruct a.
    destructAll.
    split.
    -- eapply TypeValid_subst_index; eauto.
    -- eapply SizeValid_subst_index; eauto.
  - eapply IHL; eauto.
Qed.

(* hard *)
Lemma HasTypeValue_subst_index_provable : forall {S F v t},
    HasTypeValue S F v t ->
    forall {ks idx},
      InstIndValid_at F ks idx ->
      HasTypeValue
        S (InstFunctionCtxInd_under_ks F ks idx)
        (subst'_value (under_ks' ks (subst'_of (subst_of_index idx))) v)
        (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) t).
Proof.
  apply
    (HasTypeValue_ind'
       (fun S F v t =>
          forall ks idx,
            InstIndValid_at F ks idx ->
            HasTypeValue
              S (InstFunctionCtxInd_under_ks F ks idx)
              (subst'_value (under_ks' ks (subst'_of (subst_of_index idx))) v)
              (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) t))).
  all: intros; simpl in *.
  - econstructor 1; auto.
    eapply TypeValid_subst_index_usable; eauto.
  - econstructor 2; auto.
    eapply TypeValid_subst_index_usable; eauto.
  - econstructor 3; eauto.
    2:{ eapply TypeValid_subst_index_usable; eauto. }
    rewrite Forall3_forall.
    split.
    2:{
      repeat rewrite map_length.
      eapply Forall3_length; eauto.
    }
    intros.
    repeat match goal with
    | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
        apply nth_error_map_inv in H
    end.
    destructAll.
    match goal with
    | [ H : Forall3 _ _ _ _ |- _ ] =>
        rewrite Forall3_forall in H
    end.
    destructAll.
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
  - econstructor 4; eauto.
    eapply TypeValid_subst_index_usable; eauto.
  - econstructor 5; eauto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           eauto.
       --- constructor; auto.
    -- unfold Function_Ctx_empty in *.
       destruct C; simpl in *; destructAll; subst.
       destruct idx; simpl.
       all:
         match goal with
         | [ H : QualLeq _ _ _ = _ |- _ ] =>
             specialize (QualLeq_Bottom_Const _ H)
         end.
       all: intros; subst; simpl; apply QualLeq_Refl.
    -- match goal with
       | [ |- context[QualT (RefT ?RW ?L (subst'_heaptype ?SU ?HT)) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT RW L (subst'_heaptype SU HT)) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT RW L HT) Q)) by auto
       end.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; simpl; auto.
  - econstructor 6; eauto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           eauto.
       --- constructor; auto.
    -- unfold Function_Ctx_empty in *.
       destruct C; simpl in *; destructAll; subst.
       destruct idx; simpl.
       all:
         match goal with
         | [ H : QualLeq _ _ _ = _ |- _ ] =>
             specialize (QualLeq_Top_Const _ H)
         end.
       all: intros; subst; simpl; apply QualLeq_Refl.
    -- match goal with
       | [ |- context[QualT (RefT ?RW ?L (subst'_heaptype ?SU ?HT)) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT RW L (subst'_heaptype SU HT)) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT RW L HT) Q)) by auto
       end.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; simpl; auto.
  - econstructor 7; eauto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           eauto.
       --- constructor; auto.
    -- unfold Function_Ctx_empty in *.
       destruct C; simpl in *; destructAll; subst.
       destruct idx; simpl.
       all:
         match goal with
         | [ H : QualLeq _ _ _ = _ |- _ ] =>
             specialize (QualLeq_Top_Const _ H)
         end.
       all: intros; subst; simpl; apply QualLeq_Refl.
    -- match goal with
       | [ |- context[QualT (CapT ?RW ?L (subst'_heaptype ?SU ?HT)) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (CapT RW L (subst'_heaptype SU HT)) (subst'_qual SU Q)) with (subst'_type SU (QualT (CapT RW L HT) Q)) by auto
       end.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; simpl; auto.
  - econstructor 8; eauto.
    eapply TypeValid_subst_index_usable; eauto.
  - econstructor 9; eauto.
    -- eapply TypeValid_subst_index_usable; eauto.
    -- match goal with
       | [ |- context[subst'_qual (under' SPretype ?SU) ?Q] ] =>
           replace (subst'_qual (under' SPretype SU) Q) with (subst'_qual SU Q)
       end.
       2:{
         destruct idx.
         all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
         all: simpl.
         all: eapply debruijn_subst_under_ks; apply simpl_debruijn_subst_ext_conds.
       }
       simpl.
       rewrite rec_inner_pretype_inv.
       match goal with
       | [ |- context[subst_of_index (PretypeI (Rec ?QA ?T))] ] =>
           replace (subst_of_index (PretypeI (Rec QA T))) with (ext SPretype (Rec QA T) id)
       end.
       match goal with
       | [ H : forall _ _, _ |- _ ] => apply H; auto
       end.
       simpl; auto.
  - econstructor 10; eauto.
    -- apply LocValid_subst_index; auto.
    -- eapply TypeValid_subst_index_usable; eauto.
    -- simpl.
       unfold under'.
       rewrite under_ks_under_ks_subst_of.
       do 2 match goal with
         | [ |- context[subst'_type ?SU ?T] ] =>
             replace (subst'_type SU T) with (subst_ext' SU T) by auto
         end.
       rewrite subst_ext'_assoc.
       match goal with
       | [ |- context[ext SLoc ?L id] ] =>
           replace (ext SLoc L id) with (subst_of_index (LocI L)) by auto
       end.
       match goal with
       | [ |- context[LocI (subst'_loc ?SU ?L)] ] =>
           replace (LocI (subst'_loc SU L)) with (subst'_index SU (LocI L)) by auto;
           replace (sing SLoc 1) with (sing (kind_of_index (LocI L)) 1) by auto
       end.
       rewrite <-subst_of_index_commute_not_closed.
       rewrite <-subst_ext'_assoc.
       auto.
  - econstructor 11; eauto.
    -- erewrite FunTypeValid_empty_imp_value_closed; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           eauto.
       --- constructor; auto.
    -- match goal with
       | [ |- context[QualT (CoderefT (subst'_funtype ?SU ?FT)) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (CoderefT (subst'_funtype SU FT)) (subst'_qual SU Q)) with (subst'_type SU (QualT (CoderefT FT) Q)) by auto
       end.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; auto.
Qed.

Lemma HasTypeValue_subst_index : forall {S F v t L ks idx},
    HasTypeValue S F v t ->
    LocalCtxValid F L ->
    InstIndValid_at F ks idx ->
    HasTypeValue
      S (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_value (under_ks' ks (subst'_of (subst_of_index idx)))
                    v)
      (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) t).
Proof.
  intros.
  eapply HasTypeValue_subst_index_provable; eauto.
Qed.

Lemma TypeValids_subst_index : forall {taus F ks idx},
    Forall (TypeValid F) taus ->
    InstIndValid_at F ks idx ->
    Forall
      (TypeValid (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_types (under_ks' ks (subst'_of (subst_of_index idx)))
                    taus).
Proof.
  induction taus; intros; simpl; constructor.
  - eapply TypeValid_subst_index; eauto.
    match goal with
    | [ H : Forall _ _ |- _ ] => inv H; auto
    end.
  - eapply IHtaus; eauto.
    match goal with
    | [ H : Forall _ _ |- _ ] => inv H; auto
    end.
Qed.

Lemma get_hd_pmap : forall {A B} {f : A -> B} {l},
    get_hd (pmap f l) = f (get_hd l).
Proof.
  destruct l; simpl; auto.
Qed.

Lemma get_hd_linear_InstFunctionCtxInd : forall {F ks idx},
    get_hd (linear (InstFunctionCtxInd_under_ks F ks idx))
    =
    subst'_qual (under_ks' ks (subst'_of (subst_of_index idx)))
      (get_hd (linear F)).
Proof.
  destruct idx; simpl.
  all: rewrite get_hd_pmap.
  all: destruct F; auto.
Qed.

Lemma QualLeq_first_linear_subst_index : forall {F q ks idx},
    InstIndValid_at F ks idx ->
    QualValid (qual F) (get_hd (linear F)) ->
    QualValid (qual F) q ->
    QualLeq (qual F) (get_hd (linear F)) q = Some true ->
    QualLeq (qual (InstFunctionCtxInd_under_ks F ks idx))
      (get_hd (linear (InstFunctionCtxInd_under_ks F ks idx)))
      (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx)))
         q)
    =
      Some true.
Proof.
  intros.
  eapply QualLeq_subst_index_usable.
  1: eauto.
  3: eauto.
  all: auto.
  destruct F; destruct idx; simpl in *.
  all: rewrite get_hd_pmap.
  all: auto.
Qed.

Lemma subst_qual_const : forall {su qc},
    subst'_qual su (QualConst qc) = QualConst qc.
Proof.
  intros; simpl; auto.
Qed.

Lemma TypQualLeq_subst_index : forall {F ks idx taus qc},
    InstIndValid_at F ks idx ->
    Forall (TypeValid F) taus ->
    Forall
      (fun tau : Typ =>
         TypQualLeq F tau (QualConst qc) = Some true) taus ->
    Forall
      (fun tau : Typ =>
         TypQualLeq (InstFunctionCtxInd_under_ks F ks idx) tau
                    (QualConst qc) = Some true)
      (subst'_types (under_ks' ks (subst'_of (subst_of_index idx)))
                    taus).
Proof.
  intros.
  eapply Forall_forall.
  intros.
  unfold subst'_types in *.
  match goal with
  | [ H : In _ (map _ _) |- _ ] => apply in_map_inv in H
  end.
  destructAll.
  rewrite Forall_forall in *.
  match goal with
  | [ H : forall _, In _ _ -> _, H' : In _ _ |- _ ] =>
    specialize (H _ H')
  end.
  match goal with
  | [ X : Typ |- _ ] => destruct X
  end.
  simpl in *.
  erewrite <-subst_qual_const.
  eapply QualLeq_subst_index; auto.
  - match goal with
    | [ H : In _ _, H' : forall _, _ -> _ |- _ ] =>
        specialize (H' _ H); inv H'; auto
    end.
  - econstructor; eauto.
Qed.

Lemma subst_type_QualT : forall {su pt q},
    subst'_type su (QualT pt q) =
    QualT (subst'_pretype su pt) (subst'_qual su q).
Proof.
  intros; simpl; auto.
Qed.

Lemma subst_pretype_uint32T : forall {su},
    subst'_pretype su uint32T = uint32T.
Proof.
  simpl; auto.
Qed.

Lemma BlockTyp_usable : forall {S C F L tl taus1 taus2 es L'' tf L' F1 F2},
  tf = Arrow taus1 taus2 ->
  L' = add_local_effects L tl ->
  F1 = update_label_ctx ((taus2, L'') :: label F) F ->
  F2 =
  update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 ->
  HasTypeInstruction S C F2 L es tf L' ->
  LCEffEqual (size F) L' L'' ->
  LocalCtxValid F L'' ->
  QualValid (qual F) (get_hd (linear F)) ->
  HasTypeInstruction S C F L [Block tf tl es] tf L'.
Proof.
  intros; subst; eapply BlockTyp; eauto.
Qed.

(* pretty easy *)
Lemma LCEffEqual_subst_index : forall {F ks idx L L'},
    LocalCtxValid F L ->
    LocalCtxValid F L' ->
    LCEffEqual (size F) L L' ->
    InstIndValid_at F ks idx ->
    LCEffEqual
      (size (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_local_ctx
         (under_ks' ks (subst'_of (subst_of_index idx)))
         L)
      (subst'_local_ctx
         (under_ks' ks (subst'_of (subst_of_index idx)))
         L').
Proof.
  unfold LCEffEqual.
  intros.
  apply forall2_nth_error_inv.
  2:{
    unfold subst'_local_ctx.
    repeat rewrite map_length.
    eapply Forall2_length; eauto.
  }
  intros.
  destruct_prs.
  unfold subst'_local_ctx in *.
  do 2 match goal with
    | [ H : nth_error (map _ _) _ = _ |- _ ] =>
        apply nth_error_map_inv in H
    end.
  destructAll.
  destruct_prs.
  do 2 match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    end.
  match goal with
  | [ H : Forall2 _ ?L1 ?L2,
      H' : nth_error ?L1 _ = Some _,
      H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
  end.
  intros; simpl in *.
  destructAll.
  split; auto.
  split; eapply SizeLeq_subst_index; eauto.
  all: unfold LocalCtxValid in *.
  all:
    match goal with
    | [ H : Forall _ ?L,
        H' : nth_error ?L _ = Some (_, ?SZ)
        |- SizeValid _ ?SZ ] =>
        apply nth_error_In in H';
        rewrite Forall_forall in H;
        specialize (H _ H'); simpl in *
    end.
  all: destructAll; auto.
Qed.

Lemma subst_types_app : forall {su tau1 tau2},
    subst'_types su (tau1 ++ tau2) =
    subst'_types su tau1 ++ subst'_types su tau2.
  Proof.
    intros su tau1.
    induction tau1; simpl; intros; auto.
    f_equal. eauto.
 Qed.

Lemma subst_type_singleton : forall {su tau},
    subst'_types su [tau] = [subst'_type su tau].
  Proof.
    intros. simpl. auto.
  Qed.

Lemma subst_pretype_CoderefT : forall {su ft},
    subst'_pretype su (CoderefT ft) =
    CoderefT (subst'_funtype su ft).
Proof.
  intros.
  auto.
Qed.

(* medium *)
Lemma QualLeq_local_ctx_subst_index : forall {F ks idx L},
    LocalCtxValid F L ->
    Forall
      (fun '(QualT _ q, _) =>
         QualLeq (qual F) q Unrestricted = Some true) L ->
    InstIndValid_at F ks idx ->
    Forall
      (fun '(QualT _ q, _) =>
         QualLeq (qual (InstFunctionCtxInd_under_ks F ks idx)) q
                 Unrestricted = Some true)
      (subst'_local_ctx
         (under_ks' ks (subst'_of (subst_of_index idx))) L).
Proof.
  intros.
  unfold subst'_local_ctx.
  apply Forall_comp_map.
  rewrite Forall_forall.
  intros.
  destruct_prs.
  repeat destyp.
  simpl.
  erewrite <-subst_qual_const.
  eapply QualLeq_subst_index; auto.
  - unfold LocalCtxValid in *.
    rewrite Forall_forall in *.
    match goal with
    | [ H : context[TypeValid], H' : In _ ?L |- _ ] =>
        specialize (H _ H')
    end.
    simpl in *.
    destructAll.
    match goal with
    | [ H : TypeValid _ _ |- _ ] => inv H; auto
    end.
  - econstructor; eauto.
  - match goal with
    | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ H')
    end.
    simpl in *; auto.
Qed.

Lemma Forall_plist_pmap : forall {A B} {f : A -> B} {pl P},
    Forall_plist (fun x => P (f x)) pl ->
    Forall_plist P (pmap f pl).
Proof.
  induction pl; intros.
  all:
    match goal with
    | [ H : Forall_plist _ _ |- _ ] => inv H
    end.
  all: constructor; auto.
Qed.

Lemma Forall_plist_impl : forall {A} {pl : plist A} {P : A -> Prop} {P' : A -> Prop},
    Forall_plist P pl ->
    (forall x, P x -> P' x) ->
    Forall_plist P' pl.
Proof.
  induction pl; intros.
  all:
    match goal with
    | [ H : Forall_plist _ _ |- _ ] => inv H
    end.
  all: constructor; eauto.
Qed.

(* medium *)
Lemma QualLeq_linear_subst_index : forall {F ks idx},
    Forall_plist
      (fun q : Qual =>
         QualValid (qual F) q /\ QualLeq (qual F) q Unrestricted = Some true)
      (linear F) ->
    InstIndValid_at F ks idx ->
    Forall_plist
      (fun q : Qual =>
         QualValid (qual (InstFunctionCtxInd_under_ks F ks idx)) q /\
         QualLeq (qual (InstFunctionCtxInd_under_ks F ks idx)) q
                 Unrestricted = Some true)
      (linear (InstFunctionCtxInd_under_ks F ks idx)).
Proof.
  intros.
  destruct F; destruct idx; simpl in *.
  all: apply Forall_plist_pmap.
  all: eapply Forall_plist_impl; eauto.
  all: intros.
  1-2,4: rewrite subst_non_qual_index_no_effect_on_qual; [ | solve_ineqs ].
  1-3: erewrite qual_debruijn_subst_ext.
  3,6,9: eapply debruijn_subst_under_ks.
  3-5: eapply simpl_debruijn_subst_ext_conds.
  all: solve_ineqs.
  all: auto.

  simpl in *; destructAll.
  split.
  - eapply QualValid_subst_index_usable; eauto.
  - erewrite <-subst_qual_const.
    eapply QualLeq_subst_qual_gen; eauto.
    econstructor; eauto.
Qed.

Lemma sizeOfType_subst_index : forall {F ks idx tau tausz},
    InstIndValid_at F ks idx ->
    TypeValid F tau ->
    sizeOfType (type F) tau = Some tausz ->
    SizeValid (size F) tausz ->
    exists sz',
      sizeOfType
        (type (InstFunctionCtxInd_under_ks F ks idx))
        (subst'_type (under_ks' ks (subst'_of (subst_of_index idx)))
                     tau)
      =
      Some sz' /\
      SizeValid (size (InstFunctionCtxInd_under_ks F ks idx)) sz' /\
      SizeLeq
        (size (InstFunctionCtxInd_under_ks F ks idx))
        sz'
        (subst'_size
           (under_ks' ks (subst'_of (subst_of_index idx)))
           tausz)
      =
      Some true.
Proof.
  intros.
  repeat destyp.
  simpl in *.
  eapply sizeOfPretype_subst_index; eauto.
Qed.

Lemma rec_type : forall {ks idx qa pt q},
    subst_ext'
      (under_ks' ks (subst'_of (subst_of_index idx)))
      [QualT (Rec qa (QualT pt q)) q]
    =
    [QualT
       (Rec
          (subst'_qual
             (under_ks' ks (subst'_of (subst_of_index idx))) qa)
          (QualT
             (subst'_pretype
                (under' SPretype
                        (under_ks' ks
                                   (subst'_of (subst_of_index idx)))) pt)
             (subst'_qual
                (under_ks' ks (subst'_of (subst_of_index idx)))
                q)))
       (subst'_qual
          (under_ks' ks (subst'_of (subst_of_index idx))) q)].
Proof.
  intros.
  destruct idx; simpl.
  all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  all: eapply debruijn_subst_under_ks.
  all: eapply simpl_debruijn_subst_ext_conds; eauto.
Qed.

Lemma rec_type_inv : forall {ks idx qa pt q},
    QualT
      (Rec
         (subst'_qual
            (under_ks' ks (subst'_of (subst_of_index idx))) qa)
         (QualT
            (subst'_pretype
               (under' SPretype
                  (under_ks' ks (subst'_of (subst_of_index idx))))
               pt)
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx))) q)))
      (subst'_qual
         (under_ks' ks (subst'_of (subst_of_index idx))) q)
    =
    subst'_type
      (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (Rec qa (QualT pt q)) q).
Proof.
  intros.
  match goal with
  | [ |- context[QualT (Rec (subst'_qual ?F2 ?QA) (QualT (subst'_pretype ?F3 ?PT) (subst'_qual ?F4 ?Q))) (subst'_qual ?F ?Q)] ] =>
    replace (QualT (Rec (subst'_qual F2 QA) (QualT (subst'_pretype F3 PT) (subst'_qual F4 Q))) (subst'_qual F Q)) with (subst'_type F (QualT (Rec QA (QualT PT Q)) Q)); auto
  end.
  simpl.
  match goal with
  | [ |- context[QualT (Rec _ (QualT _ ?Q)) ?Q2] ] =>
    replace Q with Q2; auto
  end.
  destruct idx; simpl.
  all: erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
  all: eapply debruijn_subst_under_ks.
  all: eapply simpl_debruijn_subst_ext_conds; eauto.
Qed.

Lemma NoCapsPretype_subst_index : forall {F ks idx pt q},
    InstIndValid_at F ks idx ->
    TypeValid F (QualT pt q) ->
    NoCapsPretype (heapable F) pt = true ->
    NoCapsPretype (heapable (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_pretype (under_ks' ks (subst'_of (subst_of_index idx)))
         pt)
    =
    true.
Proof.
  destruct idx.
  - intros.
    unfold heapable.
    simpl.
    rewrite type_fctx_subst_loc_alternate.
    rewrite <-heapable_unroll in *.
    rewrite NoCapsPretype_to_NoCapsTyp.
    rewrite <-subst_type_with_const.
    eapply NoCaps_subst_SLoc_provable; eauto.
    eapply debruijn_subst_under_ks; apply simpl_debruijn_subst_ext_conds.
  - intros.
    rewrite heapable_InstFunctionCtxInd_under_ks_size.
    eapply NoCapsPretype_subst_size_index; eauto.
    eapply debruijn_subst_under_ks; apply simpl_debruijn_subst_ext_conds.
  - intros.
    rewrite heapable_InstFunctionCtxInd_under_ks_qual.
    eapply NoCapsPretype_subst_qual_index; eauto.
    eapply debruijn_subst_under_ks; apply simpl_debruijn_subst_ext_conds.
  - intros.
    match goal with
    | [ H : InstIndValid_at _ _ _ |- _ ] => inv H
    end.
    -- rewrite heapable_InstFunctionCtxInd_under_ks_pretype_non_existent_var.
       2:{
         rewrite <-nth_error_None; auto.
       }
       erewrite TypeValid_subst_pretype_no_effect_on_pretype; eauto.
       --- simpl.
           eapply debruijn_subst_under_ks.
           apply simpl_debruijn_subst_ext_conds.
       --- unfold plus.
           unfold zero.
           rewrite Nat.add_0_r.
           rewrite <-nth_error_None; auto.
    -- match goal with
       | [ H : InstIndValid _ _ _ |- _ ] => inv H
       end.
       rewrite heapable_InstFunctionCtxInd_under_ks_pretype_existent_var.
       2:{
         eapply nth_error_Some_usable; eauto.
       }
       eapply NoCapsPretype_subst_provable; eauto.
       --- match goal with
           | [ |- debruijn_subst_ext_conds (under_ks' ?KS ?SU) ?KS _ _ ] =>
               replace KS with (plus KS zero) by apply plus_zero;
               replace (under_ks' (plus KS zero) SU) with (under_ks' KS SU) by ltac:(rewrite plus_zero; auto)
           end.
           eapply debruijn_subst_under_ks; apply simpl_debruijn_subst_ext_conds.
       --- unfold heapable.
           erewrite nth_error_map; eauto.
       --- simpl.
           match goal with
           | [ H: context[heapable (InstFunctionCtxInd_under_ks _ _ _)] |- _ ] =>
               rewrite heapable_InstFunctionCtxInd_under_ks_pretype_existent_var in H
           end.
           2:{
             eapply nth_error_Some_usable; eauto.
           }
           auto.
Qed.

Lemma NoCapsTyp_subst_index : forall {F ks idx t},
    TypeValid F t ->
    InstIndValid_at F ks idx ->
    NoCapsTyp (heapable F) t = true ->
    NoCapsTyp (heapable (InstFunctionCtxInd_under_ks F ks idx))
      (subst'_type (under_ks' ks (subst'_of (subst_of_index idx)))
         t)
    =
      true.
Proof.
  intros.
  destyp.
  simpl in *.
  eapply NoCapsPretype_subst_index; eauto.
Qed.

Lemma HeapTypeUnrestricted_subst_index : forall {F ks idx ht},
    InstIndValid_at F ks idx ->
    HeapTypeUnrestricted F ht ->
    HeapTypeUnrestricted (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_heaptype (under_ks' ks (subst'_of (subst_of_index idx)))
         ht).
Proof.
  intros.
  match goal with
  | [ H : HeapTypeUnrestricted _ _ |- _ ] => inv H
  end.
  - simpl.
    constructor 1.
    apply Forall_comp_map.
    eapply Forall_impl; eauto.
    intros.
    destyp.
    simpl.
    erewrite <-subst_qual_const.
    destructAll.
    split.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
  - simpl.
    constructor 2.
    apply Forall_comp_map.
    eapply Forall_impl; eauto.
    intros.
    destruct_prs.
    destyp.
    simpl.
    erewrite <-subst_qual_const.
    destructAll.
    split.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
  - simpl.
    constructor 3.
    -- eapply QualValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
  - simpl.
    constructor 4.
    -- eapply QualValid_subst_index; eauto.
    -- erewrite under_non_qual_no_effect_on_qual; eauto; solve_ineqs.
       2:{
         eapply debruijn_subst_under_ks; apply idx_debruijn_subst_ext_conds.
       }
       eapply QualValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- erewrite under_non_qual_no_effect_on_qual.
       2: eapply debruijn_subst_under_ks; apply idx_debruijn_subst_ext_conds.
       2: solve_ineqs.
       erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
Qed.

Lemma StructMalloc_typ_subst_index : forall {ks idx tau1 szs q},
    subst_ext' (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (ExLoc
                (QualT (RefT W (LocV 0)
                          (StructType (combine (subst_ext (weak SLoc) tau1) szs))) q))
         q)
    =
    QualT
      (ExLoc
         (QualT
            (RefT W (LocV 0)
               (StructType
                  (combine
                     (subst_ext' (subst'_of (weak SLoc))
                        (subst_ext'
                           (under_ks' ks
                              (subst'_of (subst_of_index idx)))
                           tau1))
                     (subst'_sizes
                        (under_ks' ks
                           (subst'_of (subst_of_index idx)))
                        szs))))
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx)))
               q)))
      (subst'_qual
         (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros.
  subst; simpl.
  rewrite map_combine.
  match goal with
  | [ |- context[map (subst'_type ?SU) ?TS] ] =>
      replace (map (subst'_type SU) TS)
      with
      (subst_ext' SU TS) by auto
  end.
  match goal with
  | [ |- context[subst_ext' ?SUP (subst'_types ?SU ?TS)] ] =>
      replace (subst_ext' SUP (subst'_types SU TS))
      with
      (subst_ext' SUP (subst_ext' SU TS)) by auto
  end.
  rewrite subst_ext'_assoc.
  rewrite weak_subst_under_ks_comm.
  rewrite <-subst_ext'_assoc.
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | | solve_ineqs ].
  2:{
    eapply debruijn_subst_under_ks.
    eapply idx_debruijn_subst_ext_conds.
  }
  match goal with
  | [ |- context[map (subst'_size ?SU)] ] =>
      replace (map (subst'_size SU))
      with
      (subst'_sizes SU) by auto
  end.
  erewrite under_non_size_no_effect_on_sizes; eauto; [ | solve_ineqs ].
  eapply debruijn_subst_under_ks.
  eapply idx_debruijn_subst_ext_conds.
Qed.

Lemma VariantMalloc_typ_subst_index : forall {ks idx tau1 q},
    subst_ext' (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (ExLoc
                (QualT (RefT W (LocV 0)
                          (VariantType (subst_ext (weak SLoc) tau1))) q))
         q)
    =
    QualT
      (ExLoc
         (QualT
            (RefT W (LocV 0)
               (VariantType
                  (subst_ext' (subst'_of (weak SLoc))
                     (subst_ext'
                        (under_ks' ks
                           (subst'_of (subst_of_index idx)))
                        tau1))))
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx)))
               q)))
      (subst'_qual
         (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros.
  subst; simpl.
  match goal with
  | [ |- context[map (subst'_type ?SU) ?TS] ] =>
      replace (map (subst'_type SU) TS)
      with
      (subst_ext' SU TS) by auto
  end.
  match goal with
  | [ |- context[subst_ext' ?SUP (subst'_types ?SU ?TS)] ] =>
      replace (subst_ext' SUP (subst'_types SU TS))
      with
      (subst_ext' SUP (subst_ext' SU TS)) by auto
  end.
  rewrite subst_ext'_assoc.
  rewrite weak_subst_under_ks_comm.
  rewrite <-subst_ext'_assoc.
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | solve_ineqs ].
  eapply debruijn_subst_under_ks.
  eapply idx_debruijn_subst_ext_conds.
Qed.

Lemma ArrayMalloc_typ_subst_index : forall {ks idx tau1 q},
    subst_ext' (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (ExLoc
                (QualT (RefT W (LocV 0)
                          (ArrayType (subst_ext (weak SLoc) tau1))) q))
         q)
    =
    QualT
      (ExLoc
         (QualT
            (RefT W (LocV 0)
               (ArrayType
                  (subst_ext' (subst'_of (weak SLoc))
                     (subst_ext'
                        (under_ks' ks
                           (subst'_of (subst_of_index idx)))
                        tau1))))
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx)))
               q)))
      (subst'_qual
         (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros.
  subst; simpl.
  match goal with
  | [ |- context[get_var' ?A ?B ?C] ] =>
      replace (get_var' A B C) with (LocV 0)
  end.
  2:{
    unfold get_var'.
    unfold under'.
    rewrite under_ks_under_ks_subst_of.
    unfold under_ks'.
    simpl; auto.
  }
  match goal with
  | [ |- context[subst'_type ?SUP (subst'_type ?SU ?TS)] ] =>
      replace (subst'_type SUP (subst'_type SU TS))
      with
      (subst_ext' SUP (subst_ext' SU TS)) by auto
  end.
  rewrite subst_ext'_assoc.
  rewrite weak_subst_under_ks_comm.
  rewrite <-subst_ext'_assoc.
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | solve_ineqs ].
  eapply debruijn_subst_under_ks.
  eapply idx_debruijn_subst_ext_conds.
Qed.

Lemma ExistPack_ExLoc_typ_subst_index : forall {ks idx tau1 q sz q'},
    subst_ext' (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (ExLoc
                (QualT (RefT W (LocV 0)
                          (Ex sz q' (subst_ext (weak SLoc) tau1)))
                   q))
         q)
    =
    QualT
      (ExLoc
         (QualT
            (RefT W (LocV 0)
               (Ex
                  (subst'_size
                     (under_ks' ks
                        (subst'_of (subst_of_index idx)))
                     sz)
                  (subst'_qual
                     (under_ks' ks
                        (subst'_of (subst_of_index idx)))
                     q')
                  (subst_ext' (subst'_of (weak SLoc))
                     (subst_ext'
                        (under' SPretype
                           (under_ks' ks
                              (subst'_of (subst_of_index idx))))
                        tau1))))
            (subst'_qual
               (under_ks' ks (subst'_of (subst_of_index idx)))
               q)))
      (subst'_qual
         (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros.
  subst; simpl.
  match goal with
  | [ |- context[get_var' ?A ?B ?C] ] =>
      replace (get_var' A B C) with (LocV 0)
  end.
  2:{
    unfold get_var'.
    unfold under'.
    rewrite under_ks_under_ks_subst_of.
    unfold under_ks'.
    simpl; auto.
  }
  match goal with
  | [ |- context[subst'_type ?SUP (subst'_type ?SU ?TS)] ] =>
      replace (subst'_type SUP (subst'_type SU TS))
      with
      (subst_ext' SUP (subst_ext' SU TS)) by auto
  end.
  rewrite subst_ext'_assoc.
  match goal with
  | [ |- context[under' SPretype (under' SLoc ?SU)] ] =>
      replace (under' SPretype (under' SLoc SU))
      with
      (under' SLoc (under' SPretype SU))
  end.
  2:{
    unfold under'.
    repeat rewrite under_ks_under_ks_subst_of.
    rewrite plus_assoc.
    rewrite plus_comm.
    rewrite plus_assoc.
    rewrite plus_comm.
    rewrite (plus_comm _ (sing SLoc 1)).
    auto.
  }
  match goal with
  | [ |- context[under' SPretype (under_ks' ?KS ?SU)] ] =>
      replace (under' SPretype (under_ks' KS SU))
      with
      (under_ks' (plus (sing SPretype 1) KS) SU)
  end.
  2:{
    unfold under'.
    rewrite under_ks_under_ks_subst_of; auto.
  }
  rewrite weak_subst_under_ks_comm.
  rewrite <-subst_ext'_assoc.
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | | solve_ineqs ].
  2:{
    eapply debruijn_subst_under_ks.
    eapply idx_debruijn_subst_ext_conds.
  }
  erewrite under_non_size_no_effect_on_size; eauto; [ | | solve_ineqs ].
  2:{
    eapply debruijn_subst_under_ks.
    eapply idx_debruijn_subst_ext_conds.
  }
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | solve_ineqs ].
  eapply debruijn_subst_under_ks.
  eapply idx_debruijn_subst_ext_conds.
Qed.

Lemma Malloc_typ_subst_index : forall {ks idx ht q},
    subst_ext' (under_ks' ks (subst'_of (subst_of_index idx)))
      (QualT (ExLoc
                (QualT (RefT W (LocV 0) (subst'_heaptype (subst'_of (weak SLoc)) ht))
                   q))
         q)
    =
      QualT
        (ExLoc
           (QualT
              (RefT
                 W
                 (LocV 0)
                 (subst_ext (weak SLoc)
                    (subst'_heaptype (under_ks' ks (subst'_of (subst_of_index idx)))
                       ht)))
              (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q)))
        (subst'_qual (under_ks' ks (subst'_of (subst_of_index idx))) q).
Proof.
  intros; simpl.
  do 2 match goal with
    | [ |- context[subst'_heaptype ?SU (subst'_heaptype ?SU2 ?HT)] ] =>
        replace (subst'_heaptype SU (subst'_heaptype SU2 HT))
        with
        (subst_ext' SU (subst_ext' SU2 HT))
        by auto
    end.
  do 2 rewrite subst_ext'_assoc.
  rewrite weak_subst_under_ks_comm.
  match goal with
  | [ |- context[get_var' SLoc 0 ?SU] ] =>
      replace (get_var' SLoc 0 SU) with (LocV 0) by auto
  end.
  unfold get_var'.
  erewrite under_non_qual_no_effect_on_qual; eauto; [ | solve_ineqs ].
  eapply debruijn_subst_under_ks.
  eapply idx_debruijn_subst_ext_conds.
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
  rewrite Nat.sub_0_r in *.

  destruct (ReplaceAtIdx idx lold tnew) eqn:Eq.
  - destruct p. injection H as h. subst.
    eapply IHlold. eauto.
  - inversion H.
Qed.

Definition apply_to_ReplaceAtIdx_result {A B} (f : A -> B) (opt_tpl : option (list A * A)) :=
  option_map (fun '(al, a) => (map f al, f a)) opt_tpl.

Lemma ReplaceAtIdx_map_provable : forall {A B} {f : A -> B} {idx} {lold : list A} {tnew},
    ReplaceAtIdx idx (map f lold) (f tnew)
    =
    apply_to_ReplaceAtIdx_result f (ReplaceAtIdx idx lold tnew).
Proof.
  induction idx; intros;destruct lold; simpl; auto.
  rewrite Nat.sub_0_r.
  rewrite IHidx.
  remember (ReplaceAtIdx idx lold tnew) as obj.
  destruct obj; simpl; auto.
  destruct_prs.
  simpl; auto.
Qed.

Lemma ReplaceAtIdx_map : forall {A B} {f : A -> B} {idx} {lold : list A} {tnew lnew told},
    ReplaceAtIdx idx lold tnew = Some (lnew, told) ->
    ReplaceAtIdx idx (map f lold) (f tnew)
    =
    Some (map f lnew, f told).
Proof.
  intros.
  rewrite ReplaceAtIdx_map_provable.
  rewrite H; simpl; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_update_linear_ctx : forall {F ks qc idx},
    InstFunctionCtxInd_under_ks
      (update_linear_ctx
         (Cons_p (QualConst qc) (linear F))
         F)
      ks idx
    =
    update_linear_ctx
      (Cons_p
         (QualConst qc)
         (linear (InstFunctionCtxInd_under_ks F ks idx)))
      (InstFunctionCtxInd_under_ks F ks idx).
Proof.
  destruct F; destruct idx; simpl; intros.
  all: unfold subst'_function_ctx.
  all: apply Function_Ctx_eq; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_update_label_ctx : forall {F taus L ks idx},
    InstFunctionCtxInd_under_ks
      (update_label_ctx ((taus, L) :: label F) F)
      ks idx
    =
    update_label_ctx
      ((subst'_types
          (under_ks'
             ks
             (subst'_of (subst_of_index idx)))
          taus,
        subst'_local_ctx
          (under_ks'
             ks
             (subst'_of (subst_of_index idx)))
          L)
         ::
       label (InstFunctionCtxInd_under_ks F ks idx))
      (InstFunctionCtxInd_under_ks F ks idx).
Proof.
  destruct F; destruct idx; simpl; intros.
  all: unfold subst'_function_ctx.
  all: apply Function_Ctx_eq; auto.
Qed.

Lemma nth_error_plist_pmap_provable : forall {T U} {i} {l : plist T} {f : T -> U},
    nth_error_plist (pmap f l) i = option_map f (nth_error_plist l i).
Proof.
  induction i; intros; destruct l; simpl; auto.
Qed.

Lemma nth_error_plist_pmap : forall {T U} {l : plist T} {x i} {f : T -> U},
    nth_error_plist l i = Some x ->
    nth_error_plist (pmap f l) i = Some (f x).
Proof.
  intros.
  rewrite nth_error_plist_pmap_provable.
  rewrite H; simpl; auto.
Qed.

Lemma pmap_set_hd : forall {A B} {f : A -> B} {pl el},
    pmap f (set_hd el pl) = set_hd (f el) (pmap f pl).
Proof.
  induction pl; intros; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_update_linear_ctx_set_hd : forall {F ks qc idx q},
    InstFunctionCtxInd_under_ks
      (update_linear_ctx
         (Cons_p (QualConst qc) (set_hd q (linear F)))
         F)
      ks idx
    =
    update_linear_ctx
      (Cons_p
         (QualConst qc)
         (set_hd
            (subst'_qual
               (under_ks' ks
                  (subst'_of (subst_of_index idx))) q)
            (linear (InstFunctionCtxInd_under_ks F ks idx))))
      (InstFunctionCtxInd_under_ks F ks idx).
Proof.
  destruct F; destruct idx; simpl; intros.
  all: unfold subst'_function_ctx.
  all: apply Function_Ctx_eq; auto.
  all: simpl.
  all: rewrite pmap_set_hd; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_update_linear_ctx_set_hd_only : forall {F ks idx q},
    InstFunctionCtxInd_under_ks
      (update_linear_ctx
         (set_hd q (linear F))
         F)
      ks idx
    =
    update_linear_ctx
      (set_hd
         (subst'_qual
            (under_ks' ks
               (subst'_of (subst_of_index idx))) q)
         (linear (InstFunctionCtxInd_under_ks F ks idx)))
      (InstFunctionCtxInd_under_ks F ks idx).
Proof.
  destruct F; destruct idx; simpl; intros.
  all: unfold subst'_function_ctx.
  all: apply Function_Ctx_eq; auto.
  all: simpl.
  all: rewrite pmap_set_hd; auto.
Qed.

Lemma location_update_label_ctx : forall {F lctx},
    location (update_label_ctx lctx F) = location F.
Proof.
  destruct F; subst; simpl in *; auto.
Qed.

Lemma linear_update_label_ctx : forall {F lctx},
    linear (update_label_ctx lctx F) = linear F.
Proof.
  destruct F; subst; simpl in *; auto.
Qed.

Lemma location_update_linear_ctx : forall {F lctx},
    location (update_linear_ctx lctx F) = location F.
Proof.
  destruct F; subst; simpl in *; auto.
Qed.

Lemma InstFunctionCtxInd_under_ks_linear_obligation : forall {F ks idx i},
    InstIndValid_at F ks idx ->
    (forall j, j <= i -> exists q, nth_error_plist (linear F) j = Some q /\ QualValid (qual F) q /\ QualLeq (qual F) q Unrestricted = Some true) ->
    forall j,
      j <= i ->
      exists q,
        nth_error_plist (linear (InstFunctionCtxInd_under_ks F ks idx)) j = Some q /\
        QualValid (qual (InstFunctionCtxInd_under_ks F ks idx)) q /\
        QualLeq (qual (InstFunctionCtxInd_under_ks F ks idx)) q Unrestricted = Some true.
Proof.
  intros.
  match goal with
  | [ H : forall _, _ <= _ -> _, H' : _ <= _ |- _ ] =>
    specialize (H _ H')
  end.
  destructAll.
  eexists.
  repeat split.
  3:{
    erewrite <-subst_qual_const.
    eapply QualLeq_subst_index; eauto.
    econstructor; eauto.
  }
  - destruct F; destruct idx; subst; simpl in *.
    all: apply nth_error_plist_pmap; auto.
  - eapply QualValid_subst_index; eauto.
Qed.

Lemma some_FunTyp_eq : forall {a b c a' b' c'},
    a = a' ->
    b = b' ->
    c = c' ->
    Some (FunT a (Arrow b c)) = Some (FunT a' (Arrow b' c')).
Proof.
  intros; subst; auto.
Qed.

Lemma under_ks_under_ks_comp : forall {ks su1 su2},
    (forall ks' ks'', under_ks' ks' (under_ks' ks'' su1) = under_ks' (plus ks'' ks') su1) ->
    under_ks' ks su1 ∘' under_ks' ks su2 =
    under_ks' ks (su1 ∘' su2).
Proof.
  intros.
  apply FunctionalExtensionality.functional_extensionality_dep.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  apply FunctionalExtensionality.functional_extensionality.
  intros.
  simpl.
  match goal with
  | [ X : Ind |- _ ] => destruct X
  end.
  all: simpl.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: unfold get_var'.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  2,4,6,8:
    match goal with
    | [ H : forall _ _, _ |- _ ] => rewrite H; auto
    end.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: rewrite under_ks'_unroll.
  all: handle_ineq.
  all: unfold var'.
  all: unfold var.
  all: simpl.
  all: unfold plus.
  all: unfold zero.
  all: rewrite Nat.add_0_r.
  all: rewrite minus_plus.
  all: auto.
Qed.

Lemma InstInd_subst : forall {chi idx chi' ks idx'},
    InstInd chi idx' = Some chi' ->
    InstInd
      (subst'_funtype
         (under_ks' ks (subst'_of (subst_of_index idx))) chi)
      (subst'_index
         (under_ks' ks (subst'_of (subst_of_index idx))) idx') =
      Some
        (subst'_funtype
           (under_ks' ks (subst'_of (subst_of_index idx))) chi').
Proof.
  intros.
  repeat match goal with
  | [ X : FunType |- _ ] => destruct X
  end.
  repeat match goal with
  | [ X : ArrowType |- _ ] => destruct X
  end.
  destruct idx'; simpl.
  all:
    match goal with
    | [ |- context[subst'_kindvars _ ?L] ] => destruct L; simpl in *
    end.
  all:
    try match goal with
      | [ H : None = Some _ |- _ ] => inv H
      end.
  all:
    match goal with
    | [ |- context[subst'_kindvar _ ?K] ] => destruct K; simpl in *
    end.
  all:
    match goal with
    | [ H : None = Some _ |- _ ] => inv H
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
  all: apply some_FunTyp_eq.
  
  1,4,7,10:
    repeat match goal with
      | [ |- context[subst'_kindvars ?SU ?A] ] =>
          replace (subst'_kindvars SU A) with (subst_ext' SU A) by auto
      end.
  1-4: repeat rewrite subst_ext'_assoc.
  1-4:
    match goal with
    | [ |- context[_ ∘' subst'_of (ext SLoc ?L ?ID)] ] =>
        replace (ext SLoc L ID) with (subst_of_index (LocI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SSize ?L ?ID)] ] =>
        replace (ext SSize L ID) with (subst_of_index (SizeI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SQual ?L ?ID)] ] =>
        replace (ext SQual L ID) with (subst_of_index (QualI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SPretype ?L ?ID)] ] =>
        replace (ext SPretype L ID) with (subst_of_index (PretypeI L)) by auto
    end.
  1-4: rewrite subst_of_index_commute_not_closed; simpl.
  1-4: unfold under_kindvar'.
  1-4: unfold under'.
  1-4: rewrite under_ks_under_ks_subst_of.
  1-4: simpl; auto.

  all: repeat rewrite map_map.
  all: apply map_ext.
  all: intros.
  all:
    repeat match goal with
      | [ |- context[subst'_type ?SU ?A] ] =>
          replace (subst'_type SU A) with (subst_ext' SU A) by auto
      end.
  all: repeat rewrite subst_ext'_assoc.
  all: repeat rewrite under_kindvars'_subst'_kindvars.
  all: repeat rewrite under_kindvars'_to_under_ks'.
  all: rewrite under_ks_under_ks_comp.
  
  2,4,6,8,10,12,14,16: intros.
  2-9: repeat rewrite under_ks_under_ks_subst_of.
  2-9: rewrite plus_assoc.
  2-9:
    match goal with
    | [ |- context[plus (plus ?A ?B) _] ] =>
        replace (plus A B) with (plus B A) by apply plus_comm; auto
    end.
    
  all: unfold under_kindvar'.
  all: unfold under'.
  all:
    match goal with
    | [ |- context[under_ks' ?KS1 (under_ks' ?KS2 (under_ks' ?KS3 ?SU))] ] =>
        replace (under_ks' KS1 (under_ks' KS2 (under_ks' KS3 SU))) with (under_ks' KS2 (under_ks' KS1 (under_ks' KS3 SU)))
    end.

  2,4,6,8,10,12,14,16: repeat rewrite under_ks_under_ks_subst_of.
  2-9: repeat rewrite plus_assoc.
  2-9:
    match goal with
    | [ |- context[plus (plus ?A ?B) _] ] =>
        replace (plus A B) with (plus B A) by apply plus_comm; auto
    end.
  
  all: rewrite under_ks_under_ks_comp.
  
  2,4,6,8,10,12,14,16: intros.
  2-9: repeat rewrite under_ks_under_ks_subst_of.
  2-9: rewrite plus_comm; auto.

  all:
    match goal with
    | [ |- context[_ ∘' subst'_of (ext SLoc ?L ?ID)] ] =>
        replace (ext SLoc L ID) with (subst_of_index (LocI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SSize ?L ?ID)] ] =>
        replace (ext SSize L ID) with (subst_of_index (SizeI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SQual ?L ?ID)] ] =>
        replace (ext SQual L ID) with (subst_of_index (QualI L)) by auto
    | [ |- context[_ ∘' subst'_of (ext SPretype ?L ?ID)] ] =>
        replace (ext SPretype L ID) with (subst_of_index (PretypeI L)) by auto
    end.
  all: rewrite subst_of_index_commute_not_closed; simpl.
  all: rewrite under_ks_under_ks_subst_of; auto.
Qed.

Lemma InstInd_subst_usable : forall {chi idx chi' ks idx' chinew idxnew resultnew},
    InstInd chi idx' = Some chi' ->
    chinew = subst'_funtype (under_ks' ks (subst'_of (subst_of_index idx))) chi ->
    idxnew = subst'_index (under_ks' ks (subst'_of (subst_of_index idx))) idx' ->
    resultnew = subst'_funtype (under_ks' ks (subst'_of (subst_of_index idx))) chi' ->
    InstInd
      chinew
      idxnew =
      Some resultnew.
Proof.
  intros; subst; eapply InstInd_subst; eauto.
Qed.

Lemma InstInds_subst : forall {is chi chi' ks idx},
    InstInds chi is = Some chi' ->
    InstInds
      (subst'_funtype
         (under_ks' ks (subst'_of (subst_of_index idx))) chi)
      (subst'_indices
         (under_ks' ks (subst'_of (subst_of_index idx))) is) =
      Some
        (subst'_funtype
           (under_ks' ks (subst'_of (subst_of_index idx))) chi').
Proof.
  induction is.
  1:{
    intros.
    unfold InstInds in *.
    simpl in *.
    match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    end.
    auto.
  }
  intros.
  repeat match goal with
  | [ X : FunType |- _ ] => destruct X
  end.
  repeat match goal with
  | [ X : ArrowType |- _ ] => destruct X
  end.
  
  match goal with
  | [ H : InstInds _ _ = _ |- _ ] =>
      specialize (InstInds_cons_inv H)
  end.
  intros; destructAll.
  
  simpl.
  eapply InstInds_compute_cons.
  - eapply InstInd_subst_usable; eauto.
    all: simpl; eauto.
  - do 2 match goal with
    | [ |- context[FunT (subst'_kindvars ?SU ?A) (Arrow (map ?F ?B) (map ?F ?C))] ] =>
        replace (FunT (subst'_kindvars SU A) (Arrow (map F B) (map F C))) with (subst'_funtype SU (FunT A (Arrow B C))) by auto
    end.
    match goal with
    | [ H : forall _ _, _ |- _ ] => eapply H; eauto
    end.
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
    eexists; split; eauto; repeat split.
    all: eauto.
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

Lemma LocalCtxValid_QualValid : forall {F L pt q sz},
    In (QualT pt q, sz) L ->
    LocalCtxValid F L ->
    QualValid (qual F) q.
Proof.
  intros.
  unfold LocalCtxValid in *.
  rewrite Forall_forall in *.
  match goal with
  | [ H : In _ _, H' : forall _, _ |- _ ] =>
      specialize (H' _ H); inv H'; auto
  end.
  match goal with
  | [ H : TypeValid _ _ |- _ ] => inv H; auto
  end.
Qed.

Lemma nth_error_combine_inv : forall {A B} {n} {l1 : list A} {l2 : list B} {el1 el2},
    nth_error l1 n = Some el1 ->
    nth_error l2 n = Some el2 ->
    nth_error (combine l1 l2) n = Some (el1, el2).
Proof.
  induction n.
  all: destruct l1; destruct l2; simpl.
  all: intros.
  all:
    repeat match goal with
      | [ H : None = Some _ |- _ ] => inv H
      | [ H : Some _ = Some _ |- _ ] => inv H
      end.
  all: auto.
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

Lemma InstIndValid_subst : forall {F chi idx' ks idx},
    InstIndValid F chi idx' ->
    InstIndValid_at F ks idx ->
    InstIndValid
      (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_funtype
         (under_ks' ks (subst'_of (subst_of_index idx))) chi)
      (subst'_index
         (under_ks' ks (subst'_of (subst_of_index idx))) idx').
Proof.
  intros.
  match goal with
  | [ H : InstIndValid _ _ _ |- _ ] => inv H
  end.
  - constructor 1.
    eapply LocValid_subst_index; eauto.
  - eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst_index; eauto.
    }
    intros; split; auto.
    destructAll.
    
    econstructor 2; eauto.
    -- eapply SizeValid_subst_index; eauto.
    -- eapply SizeLeq_Trans; eauto.
       eapply SizeLeq_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (subst'_pretype ?SU ?PT) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (subst'_pretype SU PT) (subst'_qual SU q)) with (subst'_type SU (QualT PT Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- intros.
       match goal with
       | [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H)
       end.
       eapply NoCapsPretype_subst_index; eauto.
  - constructor 3.
    -- eapply QualValid_subst_index; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : In _ (subst'_quals ?A ?B) |- _ ] =>
           replace (subst'_quals A B) with (map (subst'_qual A) B) in H by auto;
           apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
       end.
       destructAll.
       split.
       --- eapply QualValid_subst_index; eauto.
       --- eapply QualLeq_subst_index; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : In _ (subst'_quals ?A ?B) |- _ ] =>
           replace (subst'_quals A B) with (map (subst'_qual A) B) in H by auto;
           apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
       end.
       destructAll.
       split.
       --- eapply QualValid_subst_index; eauto.
       --- eapply QualLeq_subst_index; eauto.
  - constructor 4.
    -- eapply SizeValid_subst_index; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : In _ (subst'_sizes ?A ?B) |- _ ] =>
           replace (subst'_sizes A B) with (map (subst'_size A) B) in H by auto;
           apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
       end.
       destructAll.
       split.
       --- eapply SizeValid_subst_index; eauto.
       --- eapply SizeLeq_subst_index; eauto.
    -- prepare_Forall.
       match goal with
       | [ H : In _ (subst'_sizes ?A ?B) |- _ ] =>
           replace (subst'_sizes A B) with (map (subst'_size A) B) in H by auto;
           apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : Forall _ ?L, H' : In _ ?L |- _ ] =>
           rewrite Forall_forall in H; specialize (H _ H')
       end.
       destructAll.
       split.
       --- eapply SizeValid_subst_index; eauto.
       --- eapply SizeLeq_subst_index; eauto.
Qed.

Lemma InstIndsValid_subst : forall {is F chi ks idx},
    InstIndsValid F chi is ->
    InstIndValid_at F ks idx ->
    InstIndsValid
      (InstFunctionCtxInd_under_ks F ks idx)
      (subst'_funtype
         (under_ks' ks (subst'_of (subst_of_index idx))) chi)
      (subst'_indices
         (under_ks' ks (subst'_of (subst_of_index idx))) is).
Proof.
  induction is.
  1:{
    intros; simpl.
    constructor.
  }
  intros; simpl.
  match goal with
  | [ H : InstIndsValid _ _ _ |- _ ] => inv H
  end.
  econstructor.
  - eapply InstIndValid_subst; eauto.
  - eapply InstInd_subst; eauto.
  - eapply IHis; eauto.
Qed.

Lemma HasTypeInstruction_subst_index_provable :
  (forall S C F L1 es tau L2,
      HasTypeInstruction S C F L1 es tau L2 ->
      (forall tau1 tau2 ks idx F' L1' es' tau1' tau2' L2',
          tau = Arrow tau1 tau2 ->
          InstIndValid_at F ks idx ->
          F' = InstFunctionCtxInd_under_ks F ks idx ->
          L1' = subst_ext'
                  (under_ks' ks (subst'_of (subst_of_index idx))) L1 ->
          es' =
          map
            (subst_ext'
               (under_ks' ks (subst'_of (subst_of_index idx))))
            es ->
          L2' = subst_ext'
                  (under_ks' ks (subst'_of (subst_of_index idx))) L2 ->
          tau1' = subst_ext'
                    (under_ks' ks (subst'_of (subst_of_index idx))) tau1 ->
          tau2' = subst_ext'
                    (under_ks' ks (subst'_of (subst_of_index idx))) tau2 ->
          HasTypeInstruction
            S C F'
            L1'
            es'
            (Arrow tau1' tau2')
            L2')) /\
  (forall S cl chi,
      HasTypeClosure S cl chi ->
      HasTypeClosure S cl chi) /\
  (forall S C t ex chi,
      HasTypeFunc S C t ex chi ->
      HasTypeFunc S C t ex chi) /\
  (forall S maybe_ret i locvs locsz es taus,
      HasTypeConf S maybe_ret i locvs locsz es taus ->
      HasTypeConf S maybe_ret i locvs locsz es taus).
Proof.
  eapply HasType_Instruction_Closure_Func_Conf_mind; auto.
  all: intros.
  
  Ltac unfold_arrow :=
    match goal with
    | [ H : Arrow _ _ = _ |- _ ] => inv H
    end.
  Ltac apply_IH :=
    match goal with
    | [ H : forall _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
  Ltac simpl_subst := repeat ltac:(simpl; subst).
  60-62: econstructor; eauto.
  all: try unfold_arrow.

  - (* ValTyp *)
    unfold EmptyArrow in *.
    unfold_arrow.
    simpl.
    match goal with
    | [ |- context[Arrow [] [?A]] ] =>
      replace (Arrow [] [A]) with (EmptyArrow A) by auto
    end.
    eapply ValTyp; eauto.
    -- eapply HasTypeValue_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* UnreachableType *)
    rewrite subst_local_ctx_add_local_effects.
    eapply UnreachableType; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* NopTyp *)
    eapply NopTyp; eauto.
    eapply LocalCtxValid_subst_index; eauto.
    eapply QualValid_subst_index_usable; eauto.
    apply get_hd_linear_InstFunctionCtxInd.

  - (* DropTyp *)
    eapply DropTyp; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* SelectTyp *)
    eapply SelectTyp; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* BlockTyp *)
    unfold tf in *.
    unfold L' in *.
    unfold F1 in *.
    unfold F2 in *.
    unfold_arrow.

    eapply BlockTyp_usable; simpl; eauto.
    -- rewrite subst_local_ctx_add_local_effects; auto.
    -- fold subst'_instruction.
       apply_IH.
       --- eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
               replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
           rewrite linear_update_label_ctx; auto.
    -- eapply LCEffEqual_subst_index; eauto.
       eapply LocalCtxValid_Function_Ctx.
       1: eapply HasTypeInstruction_SecondLocalValid; eauto.
       all: destruct F; subst; simpl in *; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* LoopTyp *)
    unfold tf in *.
    unfold F1 in *.
    unfold F2 in *.
    unfold_arrow.
    eapply LoopTyp.
    fold subst'_instruction.
    apply_IH.
    -- eapply InstIndValid_at_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; subst; simpl in *; auto.
    -- match goal with
       | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
           replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
       end.
       2:{
         destruct F; subst; simpl in *; auto.
       }
       erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.
       erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
       rewrite linear_update_label_ctx; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.
      
  - (* ITETyp *)
    unfold tf in *.
    unfold L' in *.
    unfold F1 in *.
    unfold F2 in *.
    simpl_subst.
    rewrite subst_local_ctx_add_local_effects.
    rewrite subst_types_app.
    eapply ITETyp; simpl; eauto.
    -- apply_IH.
       --- eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
               replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
           rewrite linear_update_label_ctx; auto.
       --- rewrite subst_local_ctx_add_local_effects; auto.
    -- match goal with
       | [ H : context[_ = map _ ?ES]
           |- context[map (subst'_instruction _) ?ES] ] =>
         eapply H; eauto
       end.
       --- eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
               replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
           rewrite linear_update_label_ctx; auto.
       --- rewrite subst_local_ctx_add_local_effects; auto.
    -- rewrite <-subst_local_ctx_add_local_effects; auto.
       eapply LCEffEqual_subst_index; eauto.
       eapply LocalCtxValid_Function_Ctx.
       1: eapply HasTypeInstruction_SecondLocalValid; eauto.
       all: destruct F; subst; simpl in *; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* BrTyp *)
    rewrite subst_types_app.
    rewrite subst_local_ctx_add_local_effects; auto.
    eapply BrTyp; eauto.
    -- destruct F; destruct idx; subst; simpl in *.
       all: erewrite nth_error_map; eauto; simpl; auto.
    -- eapply TypQualLeq_subst_index; eauto.
       eapply proj1.
       eapply Forall_app; eauto.
    -- eapply InstFunctionCtxInd_under_ks_linear_obligation; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite <-subst_types_app.
       eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects; auto.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* Br_ifTyp *)
    rewrite subst_types_app.
    eapply Br_ifTyp; eauto.
    -- destruct F; destruct idx; subst; simpl in *.
       all: erewrite nth_error_map; eauto; simpl; auto.
    -- eapply InstFunctionCtxInd_under_ks_linear_obligation; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* Br_tableTyp *)
    repeat rewrite subst_types_app.
    match goal with
    | [ |- context[subst'_types ?SU [QualT ?PT ?Q]] ] =>
      replace (subst'_types SU [QualT PT Q]) with
          [QualT PT (subst'_qual SU Q)]
    end.
    2:{
      simpl.
      unfold uint32T.
      auto.
    }
    simpl_subst.
    rewrite subst_local_ctx_add_local_effects; auto.
    eapply Br_tableTyp; eauto.
    -- rewrite Forall_forall in *.
       intros.
       match goal with
       | [ H : forall _, In _ ?L -> _, H' : In _ ?L |- _ ] =>
           specialize (H _ H')
       end.
       destruct F; destruct idx; subst; simpl in *.
       all: erewrite nth_error_map; eauto; simpl; auto.
    -- eapply TypQualLeq_subst_index; eauto.
       eapply proj1.
       eapply Forall_app.
       eapply proj1.
       eapply Forall_app.
       rewrite <-app_assoc; eauto.
    -- eapply InstFunctionCtxInd_under_ks_linear_obligation; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- repeat rewrite Forall_app in *.
       destructAll.
       split; [ eapply TypeValids_subst_index; eauto | ].
       split; [ eapply TypeValids_subst_index; eauto | ].
       erewrite <-subst_pretype_uint32T.
       erewrite <-subst_type_QualT.
       rewrite <-subst_type_singleton.
       eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects; auto.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RetTyp *)
    repeat rewrite subst_types_app.
    simpl_subst.
    rewrite subst_local_ctx_add_local_effects; auto.
    eapply RetTyp; eauto.
    -- destruct F; destruct idx; subst; simpl in *; subst; simpl; auto.
    -- eapply QualLeq_local_ctx_subst_index; eauto.
    -- eapply TypQualLeq_subst_index; eauto.
       eapply proj1.
       eapply Forall_app; eauto.
    -- destruct idx; simpl.
       all: apply Forall_plist_pmap.
       all:
         match goal with
         | [ |- context[linear (?A ?B ?F)] ] =>
             replace (linear (A B F)) with (linear F); [ | destruct F; simpl; auto ]
         end.
       all: eapply Forall_plist_impl; eauto.
       all: intros; simpl in *.
       all: destructAll.
       all: split; [ eapply QualValid_subst_index_usable; eauto | ].
       all: eapply QualLeq_subst_index_usable.
       4,11,18,25: eauto.
       all: eauto.
       all: econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- repeat rewrite Forall_app in *.
       destructAll.
       split; [ eapply TypeValids_subst_index; eauto | ].
       eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects; auto.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* GetlocalTyp *)
    unfold EmptyArrow in *.
    unfold_arrow.
    simpl.
    rewrite set_localtype_subst.
    eapply GetlocalTyp; eauto.
    -- unfold subst'_local_ctx.
       erewrite map_nth_error; eauto.
       simpl; auto.
    -- intros.
       match goal with
       | [ H : _ = true -> QualLeq _ _ _ = _,
           H' : _ = true |- _ ] =>
         specialize (H H')
       end.
       erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- intros.
       match goal with
       | [ H : _ = false -> QualLeq _ _ _ = _,
           H' : _ = false |- _ ] =>
         specialize (H H')
       end.
       erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- intros.
       match goal with
       | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
       end.
       simpl_subst; auto.
    -- intros.
       match goal with
       | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
       end.
       simpl_subst; auto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* SetlocalTyp *)
    unfold EmptyRes in *.
    unfold_arrow.
    simpl.
    rewrite set_localtype_subst.

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfType_subst_index; eauto.
    }
    intros.
    split; auto.
    destructAll.
    
    eapply SetlocalTyp; eauto.
    -- unfold subst'_local_ctx.
       erewrite map_nth_error; eauto.
       simpl; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- eapply LocalCtxValid_QualValid; eauto.
           eapply nth_error_In; eauto.
       --- econstructor; eauto.
    -- eapply SizeLeq_Trans; eauto.
       eapply SizeLeq_subst_index; auto.
       eapply LocalCtxValid_SizeValid; eauto.
       eapply nth_error_In; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.
    
  - (* TeelocalTyp *)
    unfold tau in *.
    simpl_subst.
    rewrite set_localtype_subst.

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfType_subst_index; eauto.
    }
    intros.
    split; auto.
    destructAll.
    
    eapply TeelocalTyp; eauto.
    -- unfold subst'_local_ctx.
       erewrite map_nth_error; eauto.
       simpl; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- eapply LocalCtxValid_QualValid; eauto.
           eapply nth_error_In; eauto.
       --- econstructor; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply SizeLeq_Trans; eauto.
       eapply SizeLeq_subst_index; auto.
       eapply LocalCtxValid_SizeValid; eauto.
       eapply nth_error_In; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* GetglobalTyp *)
    unfold EmptyArrow in *.
    unfold_arrow.
    simpl_subst.
    eapply GetglobalTyp; eauto.
    -- erewrite TypeValid_empty_imp_value_closed; eauto.
       constructor; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       erewrite <-subst_type_QualT.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* SetglobalTyp *)
    unfold EmptyRes in *.
    unfold_arrow.
    simpl_subst.
    eapply SetglobalTyp; eauto.
    -- erewrite TypeValid_empty_imp_value_closed; eauto.
       constructor; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- apply QualValid_empty_ctx.
           replace [] with (qual empty_Function_Ctx) by auto.
           match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_type_QualT.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* CoderefTTyp *)
    unfold EmptyArrow in *.
    unfold_arrow.
    simpl_subst.
    eapply CoderefTTyp; eauto.
    -- erewrite FunTypeValid_empty_imp_value_closed; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           eauto.
       --- constructor; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_pretype_CoderefT.
       erewrite <-subst_qual_const.
       erewrite <-subst_type_QualT.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* InstITyp *)
    simpl.
    eapply InstITyp; eauto.
    -- eapply InstInds_subst; eauto.
    -- eapply InstIndsValid_subst; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_pretype_CoderefT.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_pretype_CoderefT.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* Call_indirectTyp *)
    simpl_subst.
    rewrite subst_types_app; simpl.
    eapply Call_indirectTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- match goal with
       | [ X : FunType |- context[CoderefT ?FT] ] =>
         match goal with
         | [ |- context[subst'_qual ?SU _] ] =>
           replace FT with (subst'_funtype SU X) by auto
         end
       end.
       erewrite <-subst_pretype_CoderefT.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* Call *)
    simpl_subst.
    eapply Call; eauto.
    -- match goal with
       | [ |- InstInds ?FT (subst'_indices ?SU _) = _ ] =>
           replace FT with (subst'_funtype SU FT)
       end.
       2:{
         erewrite FunTypeValid_empty_imp_value_closed; eauto.
         constructor; auto.
       }
       match goal with
       | [ |- _ = Some (FunT [] (Arrow (subst'_types ?SU ?TAU1) (subst'_types ?SU ?TAU2))) ] =>
	       replace (FunT [] (Arrow (subst'_types SU TAU1) (subst'_types SU TAU2))) with (subst'_funtype SU (FunT [] (Arrow TAU1 TAU2))) by auto
       end.
       eapply InstInds_subst; auto.
    -- match goal with
       | [ |- InstIndsValid _ ?FT (subst'_indices ?SU _) ] =>
           replace FT with (subst'_funtype SU FT)
       end.
       2:{
         erewrite FunTypeValid_empty_imp_value_closed; eauto.
         constructor; auto.
       }
       eapply InstIndsValid_subst; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RecFoldType *)
    unfold rec.
    unfold tau.
    match goal with
    | [ |- context[map (subst_ext' ?F) [RecFold ?A]] ] =>
      replace (map (subst_ext' F) [RecFold A]) with [RecFold (subst'_pretype F A)] by auto
    end.
    rewrite rec_pretype.
    rewrite rec_inner_type.
    rewrite rec_type.
    eapply RecFoldType; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite rec_type_inv.
       eapply TypeValid_subst_index; eauto.
    -- rewrite rec_inner_type_inv.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RecUnfoldType *)
    unfold rec.
    unfold tau.
    rewrite rec_type.
    rewrite rec_inner_type.
    eapply RecUnfoldType; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite rec_type_inv.
       eapply TypeValid_subst_index; eauto.
    -- rewrite rec_inner_type_inv.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* GroupType *)
    eapply GroupType; eauto.
    -- simpl.
       unfold subst'_types.
       rewrite map_length; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- TypeValid _ (QualT (ProdT (subst_ext' ?F ?TAU)) (subst'_qual ?F ?Q)) ] =>
         replace (QualT (ProdT (subst_ext' F TAU)) (subst'_qual F Q)) with (subst'_type F (QualT (ProdT TAU) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* UngroupTyp *)
    eapply UngroupTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- TypeValid _ (QualT (ProdT (subst_ext' ?F ?TAU)) (subst'_qual ?F ?Q)) ] =>
         replace (QualT (ProdT (subst_ext' F TAU)) (subst'_qual F Q)) with (subst'_type F (QualT (ProdT TAU) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* CapSplitTyp *)
    simpl.
    eapply CapSplitTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (CapT ?M (subst'_loc ?F ?L) (subst'_heaptype ?F ?HT)) ?Q] ] =>
         replace (QualT (CapT M (subst'_loc F L) (subst'_heaptype F HT)) Q) with (subst'_type F (QualT (CapT M L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (OwnR (subst'_loc ?F ?L)) ?Q] ] =>
         replace (QualT (OwnR (subst'_loc F L)) Q) with (subst'_type F (QualT (OwnR L) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* CapJoinTyp *)
    simpl.
    eapply CapJoinTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (CapT ?M (subst'_loc ?F ?L) (subst'_heaptype ?F ?HT)) ?Q] ] =>
         replace (QualT (CapT M (subst'_loc F L) (subst'_heaptype F HT)) Q) with (subst'_type F (QualT (CapT M L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (OwnR (subst'_loc ?F ?L)) ?Q] ] =>
         replace (QualT (OwnR (subst'_loc F L)) Q) with (subst'_type F (QualT (OwnR L) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RefDemoteTyp *)
    simpl.
    eapply RefDemoteTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (RefT ?M (subst'_loc ?F ?L) (subst'_heaptype ?F ?HT)) ?Q] ] =>
         replace (QualT (RefT M (subst'_loc F L) (subst'_heaptype F HT)) Q) with (subst'_type F (QualT (RefT M L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* MemPackTyp *)
    simpl.
    eapply MemPackTyp; eauto.
    -- simpl.
       rewrite <-subst_type_QualT.
       unfold tau in *.
       match goal with
       | [ H : _ = ?T |- _ = subst'_type _ ?T ] =>
           rewrite <-H
       end.
       simpl.
       repeat match goal with
              | [ |- context[ext SLoc ?A ?B] ] =>
                  replace (ext SLoc A B)
                  with (subst_of_index (LocI A)) by auto
              end.
       repeat match goal with
              | [ |- context[subst'_type ?SU ?T] ] =>
                  replace (subst'_type SU T)
                  with (subst_ext' SU T) by auto
              end.
       repeat rewrite subst_ext'_assoc.
       rewrite subst_of_index_commute_not_closed.
       simpl.
       unfold under'.
       rewrite under_ks_under_ks_subst_of.
       auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT
                        (ExLoc (subst'_type ?SU2 ?T))
                        (subst'_qual ?SU ?Q)] ] =>
           replace (QualT
                      (ExLoc (subst'_type SU2 T))
                      (subst'_qual SU Q))
           with
           (subst'_type SU (QualT (ExLoc T) Q))
           by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply LocValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* MemUnpackTyp *)
    subst; simpl.
    unfold L' in *.
    rewrite subst_local_ctx_add_local_effects.
    unfold tf' in *.
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
    end.
    rewrite subst_types_app.
    simpl.
    eapply MemUnpackTyp; eauto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- eapply InstIndValid_at_Function_Ctx_stronger.
           5:{
             eapply InstIndValid_at_subst_weak_loc; eauto.
           }
           all: destruct F; subst; simpl in *; auto.
       --- unfold F3.
           unfold F2.
           unfold F1.
           
           match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (subst_ext (weak SLoc) (update_location_ctx (location ?F + 1) ?FP)) _ _ ] =>
               replace (location F + 1) with (location FP + 1)
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_weak_loc; eauto.
           match goal with
           | [ |- subst_ext ?W ?F1 = subst_ext ?W ?F2 ] =>
               replace F2 with F1; auto
           end.

           match goal with
           | [ |- _ = _ _ (InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _) ] =>
               replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.

           rewrite location_update_linear_ctx.
           
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.

           repeat rewrite location_update_label_ctx.
           repeat rewrite linear_update_label_ctx.
           eauto.
       --- simpl.
           do 4 match goal with
           | [ |- context[subst'_local_ctx ?A ?B] ] =>
             replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
           end.
           do 2 rewrite subst_ext'_assoc.
           rewrite <-under_ks_under_ks_subst_of.
           match goal with
           | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
               replace (under_ks' (sing K 1) T) with (under' K T) by auto
           end.
           rewrite weak_subst_under_ks_comm; auto.
       --- rewrite <-under_ks_under_ks_subst_of.
           match goal with
           | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
               replace (under_ks' (sing K 1) T) with (under' K T) by auto
           end.
           auto.
       --- erewrite add_local_effects_apply_subst; [ | eauto ].
           match goal with
           | [ |- context[subst'_local_ctx ?A ?B] ] =>
               replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
           end.
           do 2 match goal with
                | [ |- context[subst_ext (weak SLoc) ?A] ] =>
                  replace (subst_ext (weak SLoc) A) with (subst_ext' (subst'_of (weak SLoc)) A) by auto
                end.
           do 2 rewrite subst_ext'_assoc.
           rewrite <-under_ks_under_ks_subst_of.
           match goal with
           | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
               replace (under_ks' (sing K 1) T) with (under' K T) by auto
           end.
           rewrite weak_subst_under_ks_comm; auto.
       --- simpl.
           unfold subst'_types.
           rewrite map_map.
           rewrite map_app.
           simpl.
           rewrite <-under_ks_under_ks_subst_of.
           match goal with
           | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
               replace (under_ks' (sing K 1) T) with (under' K T) by auto
           end.
           match goal with
           | [ |- ?A ++ _ = ?B ++ _ ] => replace B with A; auto
           end.
           rewrite map_map.
           match goal with
           | [ |- map ?A _ = map ?B _ ] => replace B with A; auto
           end.
           apply FunctionalExtensionality.functional_extensionality.
           intros.
           do 4 match goal with
                | [ |- context[subst'_type ?A ?B] ] =>
                  replace (subst'_type A B) with (subst_ext' A B) by auto
                end.
           do 2 rewrite subst_ext'_assoc.
           rewrite weak_subst_under_ks_comm; auto.
       --- match goal with
           | [ |- context[subst'_types ?A ?B] ] =>
             replace (subst'_types A B) with (subst_ext' A B) by auto
           end.
           do 2 match goal with
                | [ |- context[subst_ext (weak SLoc) ?A] ] =>
                  replace (subst_ext (weak SLoc) A) with (subst_ext' (subst'_of (weak SLoc)) A) by auto
             end.
           do 2 rewrite subst_ext'_assoc.
           rewrite <-under_ks_under_ks_subst_of.
           match goal with
           | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
               replace (under_ks' (sing K 1) T) with (under' K T) by auto
           end.
           rewrite weak_subst_under_ks_comm; auto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LCEffEqual_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT
                        (ExLoc (subst'_type ?SU2 ?T))
                        (subst'_qual ?SU ?Q)] ] =>
           replace (QualT
                      (ExLoc (subst'_type SU2 T))
                      (subst'_qual SU Q))
           with
           (subst'_type SU (QualT (ExLoc T) Q))
           by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* StructMallocTyp *)
    match goal with
    | [ |- context[Arrow _ (subst_ext' ?SU [?T])] ] =>
        replace (subst_ext' SU [T])
        with
        [subst_ext' SU T] by auto
    end.
    unfold psi.
    erewrite StructMalloc_typ_subst_index.

    eapply StructMallocTyp; eauto.
    -- apply forall2_nth_error_inv.
       2:{
         unfold subst_ext'.
         simpl.
         unfold subst'_types.
         unfold subst'_sizes.
         repeat rewrite map_length.
         eapply Forall2_length; eauto.
       }
       intros.
       unfold subst_ext' in *.
       simpl in *.
       unfold subst'_types in *.
       unfold subst'_sizes in *.
       do 2 match goal with
            | [ H : nth_error (map _ _) _ = Some _ |- _ ] =>
              apply nth_error_map_inv in H
         end.
       destructAll.
       match goal with
       | [ H : Forall2 _ ?L1 ?L2,
           H' : nth_error ?L1 _ = Some _,
           H'' : nth_error ?L2 _ = Some _ |-  _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
       end.
       intros.
       simpl in *.
       destructAll.

       eapply prove_using_unknown_lemma.
       {
         eapply sizeOfType_subst_index.
         1: eauto.
         2: eauto.
         - rewrite Forall_forall in *.
           match goal with
           | [ H : context[_ -> TypeValid _ _] |- _ ] =>
               apply H
           end.
           eapply nth_error_In; eauto.
         - auto.
       }
       intros.
       split; auto.
       destructAll.

       eexists; split; eauto.
       split; auto.
       eapply SizeLeq_Trans; eauto.
       eapply SizeLeq_subst_index; eauto.
       match goal with
       | [ H : Forall (SizeValid _) _ |- _ ] =>
           rewrite Forall_forall in H; apply H
       end.
       eapply nth_error_In; eauto.
    -- eapply SizeValids_subst_index; eauto.
    -- rewrite forallb_forall in *.
       intros.
       unfold subst_ext' in *.
       simpl in *.
       unfold subst'_types in *.
       match goal with
       | [ H : In _ (map _ _) |- _ ] =>
           apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
           specialize (H' _ H)
       end.
       eapply NoCapsTyp_subst_index; auto.
       rewrite Forall_forall in *.
       eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- match goal with
       | [ |- context[subst_ext (weak SLoc) ?TS] ] =>
           replace (subst_ext (weak SLoc) TS)
           with
           (subst_ext' (subst'_of (weak SLoc)) TS) by auto
       end.
       erewrite <-StructMalloc_typ_subst_index.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* StructFreeTyp *)
    simpl; subst.
    eapply StructFreeTyp; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ H : In _ (map _ _) |- _ ] =>
           apply in_map_inv in H
       end.
       destructAll.
       destruct_prs.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl; auto.
       rewrite Forall_forall in *.
       match goal with
       | [ H : In _ ?TS, H' : forall _, In _ ?TS -> _ |- _ ] =>
           specialize (H' _ H)
       end.
       simpl in *.
       erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H
           end.
           match goal with
           | [ H : HeapTypeValid _ _ |- _ ] => inv H
           end.
           rewrite Forall_forall in *.
           match goal with
           | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
               specialize (H' _ H); destructAll
           end.
           simpl in *.
           match goal with
           | [ H : TypeValid _ _ |- _ ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (RefT W
                               (subst'_loc ?SU ?L)
                               (StructType (?F ?TAUSZS)))
                            (subst'_qual ?SU ?Q)] ] =>
           replace
             (QualT
                (RefT W
                   (subst'_loc SU L)
                   (StructType (F TAUSZS)))
                (subst'_qual SU Q))
           with
           (subst'_type SU (QualT (RefT W L (StructType TAUSZS)) Q))
           by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  Ltac solve_struct_type_valid_obligation :=
    rewrite <-map_combine;
    match goal with
    | [ |- context[QualT (RefT ?CAP
                            (subst'_loc ?SU ?L)
                            (StructType (?F ?TAUSZS)))
                         (subst'_qual ?SU ?Q)] ] =>
        replace
          (QualT
             (RefT CAP
                (subst'_loc SU L)
                (StructType (F TAUSZS)))
             (subst'_qual SU Q))
        with
        (subst'_type SU (QualT (RefT CAP L (StructType TAUSZS)) Q))
        by auto
    end;
    eapply TypeValid_subst_index; eauto.

  - (* StructGetTyp *)
    simpl; subst.
    repeat rewrite map_combine.
    eapply StructGetTyp; eauto.
    -- repeat rewrite map_length; auto.
    -- rewrite <-subst_type_QualT.
       apply nth_error_map; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] => inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- solve_struct_type_valid_obligation.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* StructSetTyp *)
    simpl; subst.
    repeat rewrite map_combine.

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfType_subst_index.
      1: eauto.
      2: eauto.
      - auto.
      - auto.
    }
    intros.
    split; auto.
    destructAll.

    eapply StructSetTyp; auto.
    5: eauto.
    6:{
      eapply SizeLeq_Trans; [ eauto | ].
      eapply SizeLeq_subst_index.
      4: eauto.
      all: eauto.
      do 2 match goal with
      | [ H : TypeValid _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : HeapTypeValid _ _ |- _ ] => inv H
      end.
      eapply prove_using_unknown_lemma.
      {
        eapply Forall_combine_nth_error; eauto.
      }
      intros; split; auto.
      destructAll.
      auto.
    }
    -- repeat rewrite map_length; auto.
    -- erewrite ReplaceAtIdx_map; eauto; simpl; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- do 2 match goal with
             | [ H : TypeValid _ (QualT (RefT _ _ _) _) |- _ ] =>
                 inv H
             end.
           match goal with
           | [ H : HeapTypeValid _ ?X, H' : HeapTypeValid _ ?Y |- _ ] =>
               unfold X in *; unfold Y in *
           end.
           match goal with
           | [ H : HeapTypeValid _ (StructType (combine ?TAUS _)),
               H' : ReplaceAtIdx _ ?TAUS _ = Some _ |- _ ] =>
               inv H
           end.
           match goal with
           | [ H : ReplaceAtIdx ?IDX ?TAUS _ = Some (_, ?TAU),
               H' : nth_error ?SZS ?IDX = Some ?SZ,
               H'' : Forall _ (combine ?TAUS ?SZS) |- _ ] =>
               let H''' := fresh "H" in
               assert (H''' : nth_error (combine TAUS SZS) IDX = Some (TAU, SZ));
               [ | apply nth_error_In in H''';
	               rewrite Forall_forall in H'';
                   specialize (H'' _ H''') ]
           end.
           { apply nth_error_combine_inv; auto.
             eapply ReplaceAtIdx_old_nth_error; eauto. }
           destructAll.
           simpl in *.
           match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
               inv H; auto
           end.
       --- econstructor; eauto.
    -- erewrite nth_error_map; eauto.
    -- auto.
    -- eapply TypeValid_subst_index; eauto.
    -- eapply NoCapsTyp_subst_index; auto.
    -- match goal with
       | [ H : _ \/ _ |- _ ] => case H; intros; [ left | right ]
       end.
       --- erewrite <-subst_qual_const.
           eapply QualLeq_subst_index; eauto.
           ---- econstructor; eauto.
           ---- match goal with
                | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
                    inv H; auto
                end.
       --- subst; simpl; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- solve_struct_type_valid_obligation.
    -- solve_struct_type_valid_obligation.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* StructSwapTyp *)
    simpl; subst.
    repeat rewrite map_combine.

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfType_subst_index.
      1: eauto.
      2: eauto.
      - auto.
      - auto.
    }
    intros.
    split; auto.
    destructAll.
    
    eapply StructSwapTyp; auto.
    4: eauto.
    5:{
      eapply SizeLeq_Trans; [ eauto | ].
      eapply SizeLeq_subst_index.
      4: eauto.
      all: eauto.
      match goal with
      | [ H : TypeValid _ (QualT (RefT _ _ ?P) _),
          H' : TypeValid _ (QualT (RefT _ _ ?P2) _) |- _ ] =>
          unfold P in *; unfold P2 in *
      end.
      match goal with
      | [ H : TypeValid _ (QualT (RefT _ _ (StructType (combine ?TAUS _))) _),
          H' : ReplaceAtIdx _ ?TAUS _ = Some _ |- _ ] =>
          inv H
      end.
      match goal with
      | [ H : HeapTypeValid _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : ReplaceAtIdx ?IDX ?TAUS _ = Some (_, ?TAU),
          H' : nth_error ?SZS ?IDX = Some ?SZ,
          H'' : Forall _ (combine ?TAUS ?SZS) |- _ ] =>
          let H''' := fresh "H" in
          assert (H''' : nth_error (combine TAUS SZS) IDX = Some (TAU, SZ));
          [ | apply nth_error_In in H''';
              rewrite Forall_forall in H'';
              specialize (H'' _ H''') ]
      end.
      { apply nth_error_combine_inv; auto.
        eapply ReplaceAtIdx_old_nth_error; eauto. }
      destructAll.
      simpl in *; auto.
    }
    -- repeat rewrite map_length; auto.
    -- erewrite ReplaceAtIdx_map; eauto; simpl; eauto.
    -- erewrite nth_error_map; eauto.
    -- auto.
    -- eapply TypeValid_subst_index; eauto.
    -- eapply NoCapsTyp_subst_index; auto.
    -- match goal with
       | [ H : _ \/ _ |- _ ] => case H; intros; [ left | right ]
       end.
       --- erewrite <-subst_qual_const.
           eapply QualLeq_subst_index; eauto.
           ---- econstructor; eauto.
           ---- match goal with
                | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
                    inv H; auto
                end.
       --- subst; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- solve_struct_type_valid_obligation.
    -- solve_struct_type_valid_obligation.
    -- eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* VariantMallocTyp *)
    match goal with
    | [ |- context[Arrow _ (subst_ext' ?SU [?T])] ] =>
        replace (subst_ext' SU [T])
        with
        [subst_ext' SU T] by auto
    end.
    unfold psi.
    erewrite VariantMalloc_typ_subst_index.
    eapply VariantMallocTyp; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- unfold subst'_types.
       erewrite nth_error_map; eauto.
       unfold tau; simpl; auto.
    -- eapply QualLeq_subst_index; eauto.
       do 2 match goal with
       | [ H : TypeValid _ _ |- _ ] => inv H
         end.
       match goal with
       | [ H : HeapTypeValid _ _ |- _ ] => inv H
       end.
       unfold subst'_types in *.
       match goal with
       | [ H : nth_error ?L ?IDX = Some ?EL,
           H' : Forall _ (map ?F ?L) |- _ ] =>
           let H'' := fresh "H" in
           assert (In (F EL) (map F L));
           [ | rewrite Forall_forall in H'; specialize (H' _ H'');
               unfold EL in * ]
       end.
       { eapply nth_error_In.
         apply nth_error_map; eauto. }
       simpl in *.
       rewrite loc_weak_no_effect_on_qual in *.
       destruct F; subst; simpl in *.
       unfold subst'_function_ctx in *; simpl in *.
       match goal with
       | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
           rewrite add_non_qual_constraint_no_effect_on_qual in H; [ | solve_ineqs ];
	       inv H; auto
       end.
    -- unfold subst'_types.
       erewrite forallb_forall.
       intros.
       match goal with
       | [ H : In _ (map _ _) |- _ ] =>
           apply in_map_inv in H
       end.
       destructAll.
       eapply NoCapsTyp_subst_index; auto.
       --- rewrite Forall_forall in *.
           eauto.
       --- rewrite forallb_forall in *.
           match goal with
           | [ H : In _ ?TS, H' : forall _, In _ ?TS -> _ |- _ ] =>
               specialize (H' _ H); auto
           end.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[subst_ext (weak SLoc) ?TS] ] =>
           replace (subst_ext (weak SLoc) TS)
           with
           (subst_ext' (subst'_of (weak SLoc)) TS) by auto
       end.
       erewrite <-VariantMalloc_typ_subst_index.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* VariantCaseTypUnr *)
    simpl; subst.
    unfold L'.
    rewrite subst_local_ctx_add_local_effects.
    unfold subst'_types.
    rewrite map_app.
    simpl.
    match goal with
    | [ |- context[Arrow _ (QualT ?PT ?Q :: ?B)] ] =>
        replace (QualT PT Q :: B) with ([QualT PT Q] ++ B) by auto
    end.
    eapply VariantCaseTypUnr; eauto.
    -- eapply QualLeq_subst_index.
       4: eauto.
       all: auto.
    -- eapply QualLeq_first_linear_subst_index; eauto.
    -- apply forall2_nth_error_inv.
       2:{
         repeat rewrite map_length.
         eapply Forall2_length; eauto.
       }
       intros.
       do 2 match goal with
            | [ H : nth_error (map _ _) _ = _ |- _ ] =>
                apply nth_error_map_inv in H
            end.
       destructAll.
       match goal with
       | [ H : Forall2 _ ?L1 ?L2,
           H' : nth_error ?L1 _ = Some _,
           H'' : nth_error ?L2 _ = Some _ |- _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
       end.
       let H := fresh "H" in intro H; eapply H; eauto.
       --- eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- unfold F2.
           unfold F1.
           match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (set_hd ?Q (linear F))) ?FP) _ _ ] =>
               replace (Cons_p QC (set_hd Q (linear F))) with (Cons_p QC (set_hd Q (linear FP)))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx_set_hd; eauto.
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
           rewrite linear_update_label_ctx; auto.
       --- rewrite <-subst_local_ctx_add_local_effects; auto.
       --- simpl.
           unfold subst'_types.
           rewrite map_app.
           simpl; auto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ H : In _ _ |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl.
       erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : TypeValid _ (QualT (RefT _ _ (VariantType _)) _) |- _ ] => inv H
           end.
           match goal with
           | [ H : HeapTypeValid _ _ |- _ ] => inv H
           end.
           rewrite Forall_forall in *.
           match goal with
           | [ H : In _ ?L, H' : forall _, In _ ?L -> TypeValid _ _ |- _ ] =>
               specialize (H' _ H); inv H'; auto
           end.
       --- econstructor; eauto.
       --- match goal with
           | [ H : Forall _ ?TS, H' : In _ ?TS |- _ ] =>
               rewrite Forall_forall in H; specialize (H _ H')
           end.
           simpl in *; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LCEffEqual_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (RefT ?C (subst'_loc ?SU ?L) (VariantType (map ?SU2 ?TS))) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT C (subst'_loc SU L) (VariantType (map SU2 TS))) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT C L (VariantType TS)) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* VariantCaseTypLin *)
    simpl; subst.
    unfold L'.
    rewrite subst_local_ctx_add_local_effects.
    unfold subst'_types.
    rewrite map_app; simpl.
    eapply VariantCaseTypLin; eauto.
    -- eapply forall2_nth_error_inv; eauto.
       2:{
         repeat rewrite map_length.
         eapply Forall2_length; eauto.
       }
       intros.
       do 2 match goal with
            | [ H : nth_error (map _ _) _ = _ |- _ ] =>
                apply nth_error_map_inv in H; destructAll
            end.
       match goal with
       | [ H : Forall2 (fun _ _ => forall _, _) ?L1 ?L2,
           H' : nth_error ?L1 _ = Some _,
           H'' : nth_error ?L2 _ = Some _ |- _ ] =>
           specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
       end.
       let H := fresh "H" in intro H; simpl in *; eapply H.
       --- eauto.
       --- unfold F2.
           unfold F1.
           eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- unfold F2.
           unfold F1.
           
           match goal with
           | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
               replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
           end.
           2:{
             destruct F; subst; simpl in *; auto.
           }
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx.
           erewrite InstFunctionCtxInd_under_ks_update_label_ctx.
           rewrite linear_update_label_ctx.
           eauto.
       --- auto.
       --- auto.
       --- unfold L'.
           rewrite <-subst_local_ctx_add_local_effects; auto.
       --- unfold subst'_types.
           rewrite map_app.
           auto.
       --- auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LCEffEqual_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT (RefT ?C (subst'_loc ?SU ?L) (VariantType (map ?SU2 ?TS))) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT C (subst'_loc SU L) (VariantType (map SU2 TS))) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT C L (VariantType TS)) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ArrayMallocTyp *)
    match goal with
    | [ |- context[Arrow _ (subst_ext' ?SU [?T])] ] =>
        replace (subst_ext' SU [T])
        with
        [subst_ext' SU T] by auto
    end.
    unfold psi.
    erewrite ArrayMalloc_typ_subst_index.
    eapply ArrayMallocTyp; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply NoCapsTyp_subst_index; auto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- match goal with
           | [ H : NoCapsTyp _ ?T = _ |- _ ] => unfold T in *
           end.
           match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
               inv H; auto
           end.
       --- econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ |- context[subst_ext (weak SLoc) ?TS] ] =>
           replace (subst_ext (weak SLoc) TS)
           with
           (subst_ext' (subst'_of (weak SLoc)) TS) by auto
       end.
       rewrite <-subst_type_QualT.
       erewrite <-ArrayMalloc_typ_subst_index.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ArrayGetTyp *)
    simpl; subst.
    eapply ArrayGetTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       rewrite <-subst_type_QualT.
       match goal with
       | [ |- context[QualT (RefT ?C (subst'_loc ?SU ?L) (ArrayType (subst'_type ?SU ?TS))) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT C (subst'_loc SU L) (ArrayType (subst'_type SU TS))) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT C L (ArrayType TS)) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ArraySetTyp *)
    simpl; subst.
    eapply ArraySetTyp; eauto.
    -- erewrite <-subst_qual_const.
       rewrite <-subst_type_QualT.
       eapply NoCapsTyp_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       rewrite <-subst_type_QualT.
       match goal with
       | [ |- context[QualT (RefT ?C (subst'_loc ?SU ?L) (ArrayType (subst'_type ?SU ?TS))) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT C (subst'_loc SU L) (ArrayType (subst'_type SU TS))) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT C L (ArrayType TS)) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_pretype_uint32T.
       rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       erewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ArrayFreeTyp *)
    simpl; subst.
    eapply ArrayFreeTyp; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- erewrite <-subst_qual_const.
       rewrite <-subst_type_QualT.
       match goal with
       | [ |- context[QualT (RefT ?C (subst'_loc ?SU ?L) (ArrayType (subst'_type ?SU ?TS))) (subst'_qual ?SU ?Q)] ] =>
           replace (QualT (RefT C (subst'_loc SU L) (ArrayType (subst'_type SU TS))) (subst'_qual SU Q)) with (subst'_type SU (QualT (RefT C L (ArrayType TS)) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ExistPackTyp *)
    match goal with
    | [ |- context[Arrow _ (subst_ext' ?SU [?T])] ] =>
        replace (subst_ext' SU [T])
        with
        [subst_ext' SU T] by auto
    end.
    unfold psi.
    rewrite ExistPack_ExLoc_typ_subst_index.
    simpl.
    match goal with
    | [ |- context[QualT (subst'_pretype ?SU1 (subst'_pretype ?SU2 ?PT)) (subst'_qual ?SU1 (subst'_qual ?SU2 ?Q))] ] =>
        replace (QualT (subst'_pretype SU1 (subst'_pretype SU2 PT)) (subst'_qual SU1 (subst'_qual SU2 Q)))
        with
        (QualT (subst_ext' SU1 (subst_ext' SU2 PT)) (subst_ext' SU1 (subst_ext' SU2 Q)))
    end.
    do 2 rewrite subst_ext'_assoc.
    match goal with
    | [ |- context[subst'_of (ext SPretype ?PT id)] ] =>
        replace
          (subst'_of (ext SPretype PT id))
        with
        (subst'_of (subst_of_index (PretypeI PT)))
    end.
    rewrite subst_of_index_commute_not_closed.
    do 2 rewrite <-subst_ext'_assoc.
    simpl.
    match goal with
    | [ |- context[under_ks' (plus (sing SPretype 1) ?F2) ?SU] ] =>
        replace
          (under_ks' (plus (sing SPretype 1) F2) SU)
        with
        (under' SPretype (under_ks' F2 SU))
    end.
    2:{
      unfold under'.
      rewrite under_ks_under_ks_subst_of; auto.
    }

    eapply prove_using_unknown_lemma.
    {
      eapply sizeOfPretype_subst_index.
      1: eauto.
      2: eauto.
      - eauto.
      - auto.
    }
    intros.
    split; auto.
    destructAll.
    
    eapply ExistPackTyp; eauto.
    all: try now ltac:(simpl; auto).
    -- erewrite under_non_qual_no_effect_on_qual; eauto; [ | | solve_ineqs ].
       2:{
         eapply debruijn_subst_under_ks.
         eapply idx_debruijn_subst_ext_conds.
       }
       eapply QualLeq_subst_index; eauto.
       unfold tau in *.
       simpl in *.
       match goal with
       | [ H : context[subst'_qual (subst'_of (ext SPretype _ _))] |- _ ] =>
           erewrite qual_debruijn_subst_ext in H
       end.
       3:{
         eapply simpl_debruijn_subst_ext_conds; eauto.
       }
       2: solve_ineqs.
       match goal with
       | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
           inv H; auto
       end.
    -- eapply QualValid_subst_index; eauto.
    -- eapply SizeLeq_Trans; eauto.
       eapply SizeLeq_subst_index; eauto.
    -- eapply SizeValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- unfold under'.
       rewrite under_ks_under_ks_subst_of.
       match goal with
       | [ H : TypeValid (subst_ext ?SU ?F) _ |- TypeValid ?FP _ ] =>
           match goal with
           | [ |- context[InstFunctionCtxInd_under_ks ?FORIG ?KS ?IDX] ] =>
               replace FP with
               (InstFunctionCtxInd_under_ks
                  (subst_ext SU F)
                  (plus (sing SPretype 1) KS)
                  IDX)
           end
       end.
       1:{
         rewrite <-subst_type_QualT.
         eapply TypeValid_subst_index; eauto.
         eapply InstIndValid_at_subst_weak_pretype; eauto.
       }
       erewrite InstFunctionCtxInd_under_ks_weak_pretype; auto.
    -- eapply NoCapsPretype_subst_index; eauto.
    -- unfold heapable in *.
       rewrite type_update_type_ctx in *.
       unfold under'.
       rewrite under_ks_under_ks_subst_of.
       simpl in *.
       match goal with
       | [ H : TypeValid ?F (QualT ?HP _)
           |- NoCapsPretype ?TCTX (subst'_pretype (under_ks' ?KS (subst'_of (subst_of_index ?IDX))) ?HP) = true ] =>
           replace TCTX with (heapable (InstFunctionCtxInd_under_ks F KS IDX))
       end.
       2:{
         unfold heapable.
         destruct F; destruct idx; simpl.
         all: try rewrite remove_nth_map.
         all: repeat rewrite map_map.
         all:
           match goal with
           | [ |- _ :: map ?A _ = _ :: map ?B _ ] => replace B with A; auto
           end.
         all: apply FunctionalExtensionality.functional_extensionality.
         all: intros.
         all: destruct_prs; auto.
       }
       eapply NoCapsPretype_subst_index; eauto.
       --- eapply InstIndValid_at_subst_weak_pretype; auto.
       --- destruct F; subst; simpl in *.
           unfold heapable; simpl.
           rewrite map_map.
           match goal with
           | [ H : context[map ?F ?T] |- context[map ?F2 ?T] ] =>
               replace F2 with F; auto
           end.
           apply FunctionalExtensionality.functional_extensionality.
           intros.
           destruct_prs; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       match goal with
       | [ |- context[subst'_type ?SU ?T] ] =>
           replace (subst'_type SU T)
           with
           (subst_ext' SU T)
           by auto
       end.
       match goal with
       | [ |- context[subst_ext ?SU ?T] ] =>
           replace (subst_ext SU T)
           with
           (subst_ext' (subst'_of SU) T)
           by auto
       end.
       rewrite subst_ext'_assoc.
       match goal with
       | [ |- context[ext SPretype (subst'_pretype ?SU ?PT) id] ] =>
           replace (ext SPretype (subst'_pretype SU PT) id)
           with
           (subst_of_index (subst'_index SU (PretypeI PT)))
           by auto
       end.
       unfold under'.
       match goal with
       | [ |- context[PretypeI ?PT] ] =>
           replace (sing SPretype 1)
           with
           (sing (kind_of_index (PretypeI PT)) 1)
           by auto
       end.
       rewrite under_ks_under_ks_subst_of.
       rewrite <-subst_of_index_commute_not_closed.
       rewrite <-subst_ext'_assoc.
       do 2 match goal with
            | [ |- context[subst_ext' ?SU ?T] ] =>
                replace (subst_ext' SU T)
                with
                (subst'_type SU T)
                by auto
            end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ |- context[subst_ext (weak SLoc) ?TS] ] =>
           replace (subst_ext (weak SLoc) TS)
           with
           (subst_ext' (subst'_of (weak SLoc)) TS) by auto
       end.
       rewrite <-subst_type_QualT.
       rewrite <-ExistPack_ExLoc_typ_subst_index.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ExistUnpackTypUnr *)
    simpl; subst.
    unfold subst'_types.
    rewrite map_app.
    simpl.
    unfold L'.
    rewrite subst_local_ctx_add_local_effects.
    eapply ExistUnpackTypUnr; eauto.
    2:{
      erewrite under_non_qual_no_effect_on_qual; eauto; [ | | solve_ineqs ].
      2:{
        eapply debruijn_subst_under_ks.
        eapply idx_debruijn_subst_ext_conds.
      }
      erewrite <-subst_qual_const.
      eapply QualLeq_subst_index; eauto.
      - match goal with
        | [ H : TypeValid _ (QualT (RefT _ _ (Ex _ _ _)) _) |- _ ] =>
            inv H
        end.
        match goal with
        | [ H : HeapTypeValid _ _ |- _ ] => inv H
        end.
        destruct F; simpl in *.
        unfold subst'_function_ctx in *.
        match goal with
        | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
            rewrite add_non_qual_constraint_no_effect_on_qual in H;
            [ inv H; auto | solve_ineqs ]
        end.
      - econstructor; eauto.
    }
    2:{
      erewrite <-subst_qual_const.
      eapply QualLeq_subst_index; eauto.
      - econstructor; eauto.
    }
    4: eapply QualValid_subst_index; eauto.
    4: eapply QualValid_subst_index; eauto.
    2:{
      eapply QualLeq_subst_index.
      4: eauto.
      all: auto.
    }
    2:{
      eapply QualLeq_first_linear_subst_index; eauto.
    }
    2: eapply QualValid_subst_index; eauto.
    2:{
      eapply QualValid_subst_index_usable; eauto.
      apply get_hd_linear_InstFunctionCtxInd.
    }
    2:{
      rewrite <-subst_local_ctx_add_local_effects.
      eapply LCEffEqual_subst_index.
      3: eauto.
      all: auto.
    }
    2: eapply LocalCtxValid_subst_index; eauto.
    2: eapply LocalCtxValid_subst_index; eauto.
    2: eapply TypeValids_subst_index; eauto.
    2: eapply TypeValids_subst_index; eauto.
    2:{
      match goal with
      | [ H : TypeValid _ (QualT (RefT ?C ?L ?HT) ?Q)
          |- TypeValid _ ?T ] =>
          replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (RefT C L HT) Q)) by auto
      end.
      eapply TypeValid_subst_index; eauto.
    }
    2:{
      rewrite <-subst_local_ctx_add_local_effects.
      eapply LocalCtxValid_subst_index; eauto.
    }
    match goal with
    | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- unfold F3.
       unfold F2.
       unfold F1.
       eapply InstIndValid_at_subst_weak_pretype; eauto.
       eapply InstIndValid_at_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; subst; simpl in *; auto.
    -- unfold F3.
       unfold F2.
       unfold F1.
       erewrite InstFunctionCtxInd_under_ks_weak_pretype; eauto.
       match goal with
       | [ |- subst_ext _ ?A = subst_ext _ ?B ] =>
           replace B with A; auto
       end.

       match goal with
       | [ |- _ = _ _ (InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (set_hd ?Q (linear ?FORIG))) ?F) ?KS ?IDX) ] =>
           replace (Cons_p QC (set_hd Q (linear FORIG))) with (Cons_p QC (set_hd Q (linear F)))
       end.
       2:{
         destruct F; subst; simpl in *; auto.
       }

       erewrite InstFunctionCtxInd_under_ks_update_linear_ctx_set_hd; eauto.
       repeat rewrite type_update_linear_ctx.

       erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
       repeat rewrite type_update_label_ctx.
       repeat rewrite linear_update_label_ctx.
       auto.
    -- do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       match goal with
       | [ |- context[subst'_local_ctx ?A ?B] ] =>
         replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
       end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- simpl.
       unfold under'.
       rewrite under_ks_under_ks_subst_of; auto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       match goal with
       | [ |- context[subst'_local_ctx ?A ?B] ] =>
         replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
       end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- simpl.
       unfold subst'_types.
       repeat rewrite map_app.
       repeat rewrite map_map.
       simpl.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       match goal with
       | [ |- ?A ++ _ = ?B ++ _ ] => replace B with A; auto
       end.
       match goal with
       | [ |- map ?A _ = map ?B _ ] => replace B with A; auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       do 4 match goal with
            | [ |- context[subst'_type ?A ?B] ] =>
              replace (subst'_type A B) with (subst_ext' A B) by auto
            end.
       do 2 rewrite subst_ext'_assoc.
       rewrite weak_subst_under_ks_comm; auto.
    -- match goal with
       | [ |- context[map (subst'_type ?A) ?B] ] =>
         replace (map (subst'_type A) B) with (subst_ext' A B) by auto
       end.
       do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ExistUnpackTypLin *)
    simpl; subst.
    unfold subst'_types.
    rewrite map_app.
    simpl.
    unfold L'.
    rewrite subst_local_ctx_add_local_effects.
    eapply ExistUnpackTypLin; eauto.
    2:{
      erewrite <-subst_qual_const.
      eapply QualLeq_subst_index; eauto.
      econstructor; eauto.
    }
    2:{
      erewrite <-subst_qual_const.
      eapply QualLeq_subst_index; eauto.
      econstructor; eauto.
    }
    2: eapply QualValid_subst_index; eauto.
    2: eapply QualValid_subst_index; eauto.
    2:{
      rewrite <-subst_local_ctx_add_local_effects.
      eapply LCEffEqual_subst_index.
      3: eauto.
      all: auto.
    }
    2: eapply LocalCtxValid_subst_index; eauto.
    2: eapply LocalCtxValid_subst_index; eauto.
    2: eapply TypeValids_subst_index; eauto.
    2: eapply TypeValids_subst_index; eauto.
    2:{
      match goal with
      | [ H : TypeValid _ (QualT (RefT ?C ?L ?HT) ?Q)
          |- TypeValid _ ?T ] =>
          replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (RefT C L HT) Q)) by auto
      end.
      eapply TypeValid_subst_index; eauto.
    }
    2:{
      rewrite <-subst_local_ctx_add_local_effects.
      eapply LocalCtxValid_subst_index; eauto.
    }
    match goal with
    | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
    end.
    -- unfold F3.
       unfold F2.
       unfold F1.
       eapply InstIndValid_at_subst_weak_pretype; eauto.
       eapply InstIndValid_at_Function_Ctx_stronger.
       5: eauto.
       all: destruct F; subst; simpl in *; auto.
    -- unfold F3.
       unfold F2.
       unfold F1.
       erewrite InstFunctionCtxInd_under_ks_weak_pretype.
       match goal with
       | [ |- subst_ext _ ?A = subst_ext _ ?B ] =>
           replace B with A; auto
       end.

       match goal with
       | [ |- _ = _ _ (InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear ?FORIG)) ?F) ?KS ?IDX) ] =>
           replace (Cons_p QC (linear FORIG)) with (Cons_p QC (linear F))
       end.
       2:{
         destruct F; subst; simpl in *; auto.
       }

       erewrite InstFunctionCtxInd_under_ks_update_linear_ctx; eauto.
       repeat rewrite type_update_linear_ctx.

       erewrite InstFunctionCtxInd_under_ks_update_label_ctx; eauto.
       repeat rewrite type_update_label_ctx.
       repeat rewrite linear_update_label_ctx.
       auto.
    -- do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       match goal with
       | [ |- context[subst'_local_ctx ?A ?B] ] =>
         replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
       end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- simpl.
       unfold under'.
       rewrite under_ks_under_ks_subst_of; auto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       match goal with
       | [ |- context[subst'_local_ctx ?A ?B] ] =>
         replace (subst'_local_ctx A B) with (subst_ext' A B) by auto
       end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- simpl.
       unfold subst'_types.
       repeat rewrite map_app.
       repeat rewrite map_map.
       simpl.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       match goal with
       | [ |- ?A ++ _ = ?B ++ _ ] => replace B with A; auto
       end.
       match goal with
       | [ |- map ?A _ = map ?B _ ] => replace B with A; auto
       end.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       do 4 match goal with
            | [ |- context[subst'_type ?A ?B] ] =>
              replace (subst'_type A B) with (subst_ext' A B) by auto
            end.
       do 2 rewrite subst_ext'_assoc.
       rewrite weak_subst_under_ks_comm; auto.
    -- match goal with
       | [ |- context[map (subst'_type ?A) ?B] ] =>
         replace (map (subst'_type A) B) with (subst_ext' A B) by auto
       end.
       do 2 match goal with
            | [ |- context[subst_ext (weak SPretype) ?A] ] =>
              replace (subst_ext (weak SPretype) A) with (subst_ext' (subst'_of (weak SPretype)) A) by auto
            end.
       do 2 rewrite subst_ext'_assoc.
       rewrite <-under_ks_under_ks_subst_of.
       match goal with
       | [ |- context[under_ks' (sing ?K 1) ?T] ] =>
         replace (under_ks' (sing K 1) T) with (under' K T) by auto
       end.
       rewrite weak_subst_under_ks_comm; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RefSplitTyp *)
    simpl; subst.
    eapply RefSplitTyp; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       --- econstructor; eauto.
       --- match goal with
           | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
               inv H; auto
           end.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (RefT ?C ?L ?HT) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (RefT C L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (CapT ?C ?L ?HT) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (CapT C L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (PtrT ?L) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (PtrT L) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* RefJoinTyp *)
    simpl; subst.
    eapply RefJoinTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (RefT ?C ?L ?HT) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (RefT C L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (CapT ?C ?L ?HT) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (CapT C L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (PtrT ?L) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (PtrT L) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* QualifyTyp *)
    simpl; subst.
    eapply QualifyTyp; eauto.
    -- intros.
       repeat match goal with
              | [ H : context[_ <> _] |- _ ] => revert H
       end.
       case p; intros; simpl; try now solve_ineqs.
       --- match goal with
           | [ H : forall _, TVar ?X <> TVar _ |- _ ] =>
               specialize (H X); exfalso; apply H
           end.
           auto.
       --- match goal with
           | [ H : forall _ _ _, CapT ?A ?B ?C <> CapT _ _ _ |- _ ] =>
               specialize (H A B C); exfalso; apply H
           end.
           auto.
    -- intros.
       repeat match goal with
              | [ H : context[_ <> _] |- _ ] => revert H
       end.
       case p; intros; simpl; try now solve_ineqs.
       --- match goal with
           | [ H : forall _, TVar ?X <> TVar _ |- _ ] =>
               specialize (H X); exfalso; apply H
           end.
           auto.
       --- match goal with
           | [ H : forall _ _ _, RefT ?A ?B ?C <> RefT _ _ _ |- _ ] =>
               specialize (H A B C); exfalso; apply H
           end.
           auto.
    -- intros.
       repeat match goal with
              | [ H : context[_ <> _] |- _ ] => revert H
       end.
       case p; intros; simpl; try now solve_ineqs.
       match goal with
       | [ H : forall _, TVar ?X <> TVar _ |- _ ] =>
           specialize (H X); exfalso; apply H
       end.
       auto.
    -- eapply QualLeq_subst_index; eauto.
       match goal with
       | [ H : TypeValid _ (QualT _ ?Q) |- QualValid _ ?Q ] =>
           inv H; auto
       end.
    -- eapply QualValid_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- rewrite <-subst_type_QualT.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* TrapTyp *)
    simpl; subst.
    rewrite subst_local_ctx_add_local_effects.
    eapply TrapTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- rewrite <-subst_local_ctx_add_local_effects.
       eapply LocalCtxValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* CallAdmTyp *)
    simpl; subst.
    eapply CallAdmTyp; eauto.
    -- match goal with
       | [ |- InstInds ?FT (subst'_indices ?SU _) = _ ] =>
           replace FT with (subst'_funtype SU FT)
       end.
       2:{ erewrite HasTypeClosure_imp_funtype_closed; eauto. }
       match goal with
       | [ |- _ = Some (FunT [] (Arrow (subst'_types ?SU ?TAU1) (subst'_types ?SU ?TAU2))) ] =>
	       replace (FunT [] (Arrow (subst'_types SU TAU1) (subst'_types SU TAU2))) with (subst'_funtype SU (FunT [] (Arrow TAU1 TAU2))) by auto
       end.
       eapply InstInds_subst; auto.
    -- match goal with
       | [ |- InstIndsValid _ ?FT (subst'_indices ?SU _) ] =>
           replace FT with (subst'_funtype SU FT)
       end.
       2:{ erewrite HasTypeClosure_imp_funtype_closed; eauto. }
       eapply InstIndsValid_subst; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* LabelTyp *)
    subst; simpl.
    unfold tf in *.
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
    end.
    eapply LabelTyp.
    2:{
      match goal with
      | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
      end.
      --- eapply InstIndValid_at_Function_Ctx_stronger.
          5: eauto.
          all: destruct F; subst; simpl in *; auto.
      --- match goal with
          | [ |- _ = InstFunctionCtxInd_under_ks (update_linear_ctx (Cons_p ?QC (linear F)) ?FP) _ _ ] =>
              replace (Cons_p QC (linear F)) with (Cons_p QC (linear FP))
          end.
          2:{
            destruct F; subst; simpl in *; auto.
          }
          erewrite InstFunctionCtxInd_under_ks_update_linear_ctx.
          erewrite InstFunctionCtxInd_under_ks_update_label_ctx.
          rewrite linear_update_label_ctx.
          eauto.
    }
    -- unfold subst'_types; rewrite map_length; auto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* LocalTyp *)
    subst; simpl.
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
    end.
    eapply LocalTyp; eauto.
    -- unfold subst'_types.
       rewrite map_length; auto.
    -- match goal with
       | [ H : HasTypeConf _ _ _ _ _ _ _ |- _ ] => inversion H
       end.
       subst.
       econstructor; eauto.
       unfold F0 in *.
       match goal with
       | [ H : HasTypeInstruction _ _ _ _ _ _ _ |- _ ] =>
           specialize (HasTypeInstruction_TypeAndLocalValid_provable _ _ _ _ _ _ _ H _ _ eq_refl)
       end.
       intros; destructAll.
       unfold subst'_types.
       rewrite Forall_eq; auto.
       eapply Forall_impl; [ | eauto ].
       intros.
       eapply TypeValid_empty_imp_value_closed_type; eauto.
       simpl in *.
       unfold Function_Ctx_empty.
       auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply TypeValids_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* MallocTyp *)
    match goal with
    | [ |- context[Arrow _ (subst_ext' ?SU [?T])] ] =>
        replace (subst_ext' SU [T])
        with
        [subst_ext' SU T] by auto
    end.
    rewrite Malloc_typ_subst_index.
    simpl.
    match goal with
    | [ |- context[QualT ?PT (subst'_qual ?SU ?Q)] ] =>
        replace (subst'_qual SU Q) with Q
    end.
    2:{
      rewrite QualValid_empty_imp_value_closed; auto.
    }
    eapply MallocTyp; eauto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- eapply HasHeapType_HeapTypeValid; eauto.
       --- constructor; auto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- eapply HasHeapType_HeapTypeValid; eauto.
       --- constructor; auto.
    -- erewrite HeapTypeValid_empty_imp_value_closed; eauto.
       --- eapply HasHeapType_HeapTypeValid; eauto.
       --- constructor; auto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ |- context[QualT ?PT ?Q] ] =>
         match goal with
         | [ |- context[subst'_heaptype ?SU] ] =>
             replace Q with (subst'_qual SU Q)
         end
       end.
       2:{
         rewrite QualValid_empty_imp_value_closed; auto.
       }
       rewrite <-Malloc_typ_subst_index.
       erewrite TypeValid_empty_imp_value_closed_type; eauto.
       constructor; auto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* FreeTyp *)
    subst; simpl.
    unfold EmptyRes in *.
    match goal with
    | [ H : Arrow _ _ = Arrow _ _ |- _ ] => inv H
    end.
    simpl.
    match goal with
    | [ |- context[Arrow [?T] []] ] =>
        replace (Arrow [T] []) with (EmptyRes T) by auto
    end.
    eapply FreeTyp; eauto.
    -- erewrite <-subst_qual_const.
       eapply QualLeq_subst_index; eauto.
       econstructor; eauto.
    -- eapply QualValid_subst_index; eauto.
    -- eapply HeapTypeUnrestricted_subst_index; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- match goal with
       | [ H : TypeValid _ (QualT (RefT ?C ?L ?HT) ?Q)
           |- TypeValid _ ?T ] =>
           replace T with (subst'_type (under_ks' ks (subst'_of (subst_of_index idx))) (QualT (RefT C L HT) Q)) by auto
       end.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* EmptyTyp *)
    simpl.
    eapply EmptyTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- unfold subst'_types.
       apply Forall_comp_map.
       eapply Forall_impl; [ | eauto ].
       intros.
       eapply TypeValid_subst_index; eauto.
    -- eapply QualValid_subst_index_usable; eauto.
       apply get_hd_linear_InstFunctionCtxInd.

  - (* ConsTyp *)
    simpl; subst.
    rewrite map_app.
    simpl.
    eapply ConsTyp; eauto.

  - (* FrameTyp *)
    simpl; subst.
    unfold subst'_types.
    do 2 rewrite map_app.
    eapply FrameTyp; eauto.
    2: eapply QualLeq_first_linear_subst_index; eauto.
    -- rewrite Forall_forall.
       intros.
       match goal with
       | [ H : In _ _ |- _ ] => apply in_map_inv in H
       end.
       destructAll.
       match goal with
       | [ X : Typ |- _ ] => destruct X
       end.
       simpl in *.
       eapply QualLeq_subst_index; eauto.
       --- rewrite Forall_forall in *.
           match goal with
           | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
               specialize (H' _ H); inv H'; auto
           end.
       --- rewrite Forall_forall in *.
           repeat match goal with
           | [ H : In _ ?L, H' : forall _, In _ ?L -> _ |- _ ] =>
               specialize (H' _ H)
           end.
           simpl in *; destructAll; auto.
    -- match goal with
       | [ H : forall _ _ _ _ _, _ |- _ ] => eapply H; eauto
       end.
       --- unfold F'.
           eapply InstIndValid_at_Function_Ctx_stronger.
           5: eauto.
           all: destruct F; subst; simpl in *; auto.
       --- unfold F'.
           erewrite InstFunctionCtxInd_under_ks_update_linear_ctx_set_hd_only; eauto.
    -- eapply QualValid_subst_index_usable.
       4: apply get_hd_linear_InstFunctionCtxInd.
       all: eauto.
    -- eapply QualValid_subst_index_usable; eauto.
    -- eapply TypeValids_subst_index; eauto.

  - (* ChangeBegLocalTyp *)
    eapply ChangeBegLocalTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply LCEffEqual_subst_index; eauto.
       eapply HasTypeInstruction_FirstLocalValid; eauto.

  - (* ChangeEndLocalTyp *)
    eapply ChangeEndLocalTyp; eauto.
    -- eapply LocalCtxValid_subst_index; eauto.
    -- eapply LCEffEqual_subst_index; eauto.
       eapply HasTypeInstruction_SecondLocalValid; eauto.
Qed.

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
Proof.
  specialize HasTypeInstruction_subst_index_provable; intro H.
  destruct H as [H].
  intros.
  eapply H; eauto.
Qed.

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
