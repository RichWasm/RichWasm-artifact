(*

We want a function

  subst : (nat -> term) -> term -> term

such that (subst s e) applies the parallel substitution s at each free variable in e.

Each free variable in e can be decomposed into a sum of two nats n+k where
- the free variable points to the nth element in the environment/typing context
- the variable appears under k binders

Given

  subst' : (nat -> nat -> term) -> term -> term

such that (subst' s e) replaces each free variable n+k with the term (s n k),
we can define subst as

  subst s e = subst' (fun n k => shift' k (s n)) e
  where shift' m e = subst' (fun n k => var (m + n + k)) e

{subst, var} will satisfy the monad laws

  subst f (var n) = f n
  subst var e = e
  subst f (subst g e) = subst (fun n => subst f (g n)) e

so long as subst' satisfies

  subst' f (var n) = f n 0
  subst' (fun n k => var (n + k)) e = e

and its own associativity law. (Proof below.)

In our case, there are four different kinds of binders (loc, qual, size, type).
So we need a function that takes four different substitutions:

  subst : (nat -> loc) * (nat -> qual) * (nat -> size) * (nat -> pretype) -> term -> term

(where term ∈ {loc, qual, size, pretype, type, instruction, conf, ...})

So we'll generalize to a family of substitutions indexed by "kinds of binding"

   I : Type
   eq : ∀ i j : I, {i = j} + {i ≠ j}
   B : I -> Type
   subst I := ∀ i : I, nat -> B i
   var : subst I

Now we want

  subst : subst I -> term -> term

We also want combinators for constructing substitutions, and laws for reasoning about them:

  Experiment: lambda calculus

    (lam e1) e2 = e1[ext e2 id]
    (lam e)[s] = lam e[ext (var 0) (weak ∘ s)]
    
    (lam (lam e1)) e2 e3
    = ((lam e1)[ext e2 id]) e3
    = (lam e1[ext (var 0) (weak ∘ ext e2 id)]) e3
    = e1[ext (var 0) (weak ∘ ext e2 id)][ext e3 id]
    = e1[ext e3 id ∘ ext (var 0) (weak ∘ ext e2 id)]
    = ?
    = e1[ext e3 (ext e2 id)]
    
    (var 0)[ext e id] = e
    (var (S n))[ext _ s] = (var n)[s]
    
    So basically environments are represented as lists (ext e0 (ext e1 (ext ... id))).
    To fill in the step labelled (?), just need a way to "compose" two lists.

  Idea: "eta"
  
    s = ext (var 0)[s] (s ∘ weak)
  
  In this case we have
  
    ext e3 id ∘ ext (var 0) (weak ∘ ext e2 id)
  = ext (var 0)[ext e3 id ∘ ext (var 0) (weak ∘ ext e2 id)]
        (ext e3 id ∘ ext (var 0) (weak ∘ ext e2 id) ∘ weak)
  = ext (var 0)[ext e3 id] (ext e3 id ∘ weak ∘ ext e2 id)
  = ext e3 (id ∘ ext e2 id)
  = ext e3 (ext e2 id)
  
  Laws:
  
    s = ext (var 0)[s] (s ∘ weak)
  
    ext _ s ∘ weak = s
  
    (lam e1) e2 = e1[ext e2 id]
    (lam e)[s] = lam e[ext (var 0) (weak ∘ s)]
  
    (var 0)[ext e _] = e
    (var (S n))[ext _ s] = (var n)[s]
  
  Generalizing to multiple substitutions (assume throughout that i ≠ j):
  
    id ∘ s = s ∘ id = s
    (s ∘ t) ∘ u = s ∘ (t ∘ u)
  
    ext i _ s ∘ weak i = s
    ext i e s ∘ weak j = ext i e (s ∘ weak j)
  
    (lam i e1) e2 = e1[ext i e2 id]
    (lam i e)[s] = lam i e[ext i (var i 0) (weak i ∘ s)]
  
    (var i 0)[ext i e _] = e
    (var i (S n))[ext i _ s] = (var i n)[s]
  
    (var i n)[ext j _ s] = (var i n)[s]

  These laws should be provable generically.

Also want lemmas for performing simplification like

  subst s (C e ..) = C (subst s e) ..
  when e .. don't introduce any binders

  subst s (C e) = C (subst (ext i (var i 0) (weak i s)) e)
  when e is a binding site of kind i

These can't be done generically, but maybe can be solved by tactics.

For example, the following is useful for going under binders when constructing subst':

  under' s :=
    fun n k =>
    if n = 0
    then var (n + k)
    else s (n - 1) (k + 1)


( 3 , 4 )

(fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)




subst'
  (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)
  (\. (\. [3] + [2] + [1] + [0]))


subst'
  (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0))
  (\. [3] + [2] + [1] + [0])


subst'
  (under (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)))
  ([3] + [2] + [1] + [0])


(under (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0))) [0] [0]

var [0]

under (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)) [1] [0]

var [1]


(under (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0))) [2] [0]

(under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)) [1] [1]

(fun n k => if n = 0 then 3 else if n = 1 then 4 else 0) [0] [2]

3

(under (under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0))) [3] [0]

(under (fun n k => if n = 0 then 3 else if n = 1 then 4 else 0)) [2] [1]

(fun n k => if n = 0 then 3 else if n = 1 then 4 else 0) [1] [2]


fun n k => 


Define

  under i s = ext i (var i 0) (weak i ∘ s)

Want simplifiation lemmas to relate under' and under.
For example, in lambda calculus, want

  subst s (lam i e) = lam i (subst (under i s) e)

to be provable given

  subst' s (lam i e) = lam i (subst' (under' i s) e)

It suffices to show

  under' i (subst'_of s) = subst'_of (under i s)
  where subst'_of s = fun n k => shift' k (s n)

which turns out to be provable generically.

We also want it to be relatively easy to prove that a given definition for subst' 
satisfies the proper laws. This might be doable with tactics.

 *)

From Coq Require Import Logic.FunctionalExtensionality.

Notation fext := functional_extensionality_dep.
Ltac fext x := apply fext; intros x.

Require Import Lia List RWasm.list_util.
Import ListNotations.

Class Eq A := dec_eq : forall x y : A, {x = y} + {x <> y}.

Instance dec_eq_nat : Eq nat := ltac:(intros m n; decide equality).

Lemma hedberg : forall {A} `{Eq A} {x : A} (p : x = x), p = eq_refl.
Proof.
  intros.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Ltac hedberg :=
  match goal with
  | x : @eq ?A ?y ?y |- context [eq_rect ?y _ _ ?y _] =>
    (assert (x = eq_refl) by (eapply hedberg; typeclasses eauto));
    subst x; unfold eq_rect
  | x : @eq ?A ?y ?y |- context [match _ with eq_refl => _ end] =>
    (assert (x = eq_refl) by (eapply hedberg; typeclasses eauto));
    subst x; unfold eq_rect
  end.

(* To generalize to multiple kinds of substitutions, need a family of
   nesting depths (one for each kind of substitution).

   Can represent this with functions (I -> nat) *)

Section Depths.

Definition zero {A} : A -> nat := fun _ => 0.
Definition plus {A} (f g : A -> nat) : A -> nat := fun x => f x + g x.

Definition sing {I} `{Eq I} i (n : nat) : I -> nat :=
  fun j => if dec_eq i j then n else 0.

Definition plus_id {A} ks : @plus A zero ks = ks. Proof. reflexivity. Qed.

Definition plus_zero {A} ks : @plus A ks zero = ks.
Proof.
  unfold plus.
  unfold zero.
  apply FunctionalExtensionality.functional_extensionality.
  lia.
Qed.

Definition plus_comm {A} ks ls : @plus A ks ls = plus ls ks.
Proof. fext i; unfold plus; lia. Qed.

Definition plus_assoc {A} ks ls ms : @plus A ks (plus ls ms) = plus (plus ks ls) ms.
Proof. fext i; unfold plus; lia. Qed.

End Depths.

Global Hint Unfold zero plus sing : CrushDB.

Definition Subst' {I} (Kind : I -> Type) := forall i, nat -> (I -> nat) -> Kind i.

Class Var {I} (Kind : I -> Type) := var : forall i, nat -> Kind i.

Definition var' {I} {Kind : I -> Type} `{Var _ Kind} : forall i, nat -> (I -> nat) -> Kind i :=
  fun i n ks => var i (ks i + n).

Definition under_ks' {I} {Kind : I -> Type} `{Var _ Kind} : (I -> nat) -> Subst' Kind -> Subst' Kind :=
  fun ks s i' n' ks' =>
  if Nat.ltb n' (ks i')
  then var' i' n' ks'
  else s i' (n' - ks i') (plus ks ks').

(** All the things needed to support |I| binding constructs over types {Kind i}_{i ∈ I} *)

Class BindVar {I} (Kind : I -> Type) `{Var _ Kind} :=
  { subst' : forall i, Subst' Kind -> Kind i -> Kind i;
    subst'_s_var : forall i f n, subst' i f (var i n) = f i n zero }.

Definition comp' {I} {Kind : I -> Type} `{BindVar _ Kind} (f g : Subst' Kind) :=
  fun i n ks => subst' i (under_ks' ks f) (g i n ks).
Infix "∘'" := comp' (at level 60, right associativity).

Class Bind {I} (Kind : I -> Type) `{BindVar _ Kind} :=
  { subst'_var_e : forall i e, subst' i var' e = e;
    subst'_assoc : forall i f g e, subst' i f (subst' i g e) = subst' i (f ∘' g) e }.

(** A Bind instance can be used to construct a family of functions
      subst : ∀ i, Subst Kind -> Kind i -> Kind i
    but we also want functions of the form
      subst : Subst Kind -> A -> A
    for other A.
    (e.g. we want to substitute into configurations, instructions, function bodies, ...)

    These functions are specified by BindExt instances.
    They are basically Bind instances but without one of the laws about var. *)
Class BindExt {I} (Kind : I -> Type) `{Bind _ Kind} A :=
  { subst_ext' : Subst' Kind -> A -> A;
    subst_ext'_var_e : forall e, subst_ext' var' e = e;
    subst_ext'_assoc : forall f g e, subst_ext' f (subst_ext' g e) = subst_ext' (f ∘' g) e }.

Definition SubstAt A := nat -> A.
Definition Subst {I} (Kind : I -> Type) := forall i, SubstAt (Kind i).

(** Tactic [crush] for unfolding definitions, applying monad laws, and then doing
    casework and arithmetic. Uses hint database CrushDB. *)

Ltac feql := f_equal; repeat (apply fext; intros).

Hint Rewrite @subst'_assoc @subst'_s_var @subst'_var_e : CrushDB.
Hint Rewrite @subst_ext'_assoc @subst_ext'_assoc : CrushDB.

Global Hint Unfold var' comp' under_ks' : CrushDB.
  
Ltac ltb_false :=
  match goal with
  | |- context [if ?e then _ else _] =>
    replace e with false by (symmetry; apply PeanoNat.Nat.ltb_nlt; lia)
  end.

Ltac destruct_ltb :=
  match goal with
  | |- context [if Nat.ltb ?x ?y then _ else _] =>
    destruct (PeanoNat.Nat.ltb_spec x y)
  end.

Ltac destruct_dec_eq :=
  match goal with
  | |- context [if dec_eq ?x ?y then _ else _] =>
    destruct (dec_eq x y)
  | |- context [match dec_eq ?x ?y with left _ => _ | right _ => _ end] =>
    destruct (dec_eq x y)
  end.

Ltac destruct_dec_eq_refl :=
  match goal with
  | |- context [match dec_eq ?x ?x with left _ => _ | right _ => _ end] =>
    destruct (dec_eq x x); [hedberg|congruence]
  end.

Ltac crush n :=
  match n with
  | 0 => idtac
  | S ?n =>
    (progress (lia
              + congruence
              + (autorewrite with CrushDB; autounfold with CrushDB)
              + ltb_false
              + feql
              + destruct_ltb
              + (destruct_dec_eq; [subst; unfold eq_rect|])
              + destruct_dec_eq_refl
              + hedberg
             );
     crush n) || solve [rewrite <- subst'_var_e; crush n]
  end.

Section BindDerivedOperators.

  Context {I} `{Eq I} {Kind : I -> Type} `{bind : Bind _ Kind}.

  (** Shifting' *)

  Definition weaks' : (I -> nat) -> Subst' Kind :=
    fun ks i' n' ks' => var i' (ks i' + ks' i' + n').
  Hint Unfold weaks' : CrushDB.

  Definition shifts' : forall i, (I -> nat) -> Kind i -> Kind i :=
    fun i ks => subst' i (weaks' ks).

  Definition subst'_of (s : Subst Kind) : Subst' Kind :=
    fun i n ks => shifts' i ks (s i n).

  Lemma weaks'_zero : weaks' zero = var'.
  Proof. crush 3. Qed.

  (** Substitution *)
  
  Definition subst : forall i, Subst Kind -> Kind i -> Kind i :=
    fun i s => subst' i (subst'_of s).

  Hint Unfold subst shifts' subst'_of : CrushDB.
  
  (** Identity & composition *)

  Definition id : Subst Kind := var.
  Definition comp : Subst Kind -> Subst Kind -> Subst Kind :=
    fun s t i n => subst i s (t i n).
  Infix "∘" := comp (at level 60, right associativity).

  Hint Unfold id comp : CrushDB.

  Lemma comp_left_id s : id ∘ s = s. Proof. crush 7. Qed.
  Lemma comp_right_id s : s ∘ id = s. Proof. crush 4. Qed.
  Lemma comp_assoc s t u : (s ∘ t) ∘ u = s ∘ t ∘ u. Proof. crush 15. Qed.

  (** Monad laws *)

  Lemma subst_s_var i f n : subst i f (var i n) = f i n. Proof. crush 5. Qed.

  Lemma subst_var_e i e : subst i var e = e. Proof. crush 6. Qed.

  Lemma subst_assoc i f g e : subst i f (subst i g e) = subst i (f ∘ g) e.
  Proof. crush 17. Qed.

  (** Weakening / shifting *)

  Definition weaks : (I -> nat) -> Subst Kind := fun ks i n => var i (ks i + n).
  Definition weak : I -> Subst Kind := fun i => weaks (sing i 1).
  
  Definition shifts : forall i, (I -> nat) -> Kind i -> Kind i := fun i ks => subst i (weaks ks).
  Definition shift : forall i, I -> Kind i -> Kind i := fun i j => shifts i (sing j 1).

  Hint Unfold weaks shifts weak shift : CrushDB.

  Lemma shifts_shifts' : shifts' = shifts. Proof. crush 6. Qed.

  (** Extension *)
  
  Definition ext : forall i, Kind i -> Subst Kind -> Subst Kind :=
    fun i e s j n =>
    match dec_eq i j with
    | left p =>
      if dec_eq n 0
      then eq_rect i Kind e j p
      else s j (n - 1)
    | right _ => s j n
    end.
  
  (** Useful for going under a binder when defining subst' *)
  Definition under' : I -> Subst' Kind -> Subst' Kind :=
    fun i => under_ks' (sing i 1).
  
  (** Like subst/subst', the more well-behaved version of under' *)
  Definition under : I -> Subst Kind -> Subst Kind :=
    fun i s => ext i (var i 0) (weak i ∘ s).

  Hint Unfold ext under under' : CrushDB.
  
  Lemma under_under' i s : under' i (subst'_of s) = subst'_of (under i s).
  Proof.
    (* crush 12 solves this, but the proof goes faster if we help it along *)
    unfold subst'_of, under', under_ks'; fext j; fext n; fext ks.
    unfold under, ext, sing; destruct (dec_eq i j); [subst; unfold eq_rect|].
    - destruct (dec_eq n 0); [subst; unfold eq_rect|]; crush 8.
    - ltb_false; crush 7.
  Qed.

  (** Laws *)

  Lemma s_eta i s : s = ext i (subst i s (var i 0)) (s ∘ weak i).
  Proof. crush 9. Qed.

  Lemma ext_var_hd i e s : subst i (ext i e s) (var i 0) = e.
  Proof. crush 6. Qed.

  Lemma ext_var_tl i e s n : subst i (ext i e s) (var i (S n)) = subst i s (var i n).
  Proof. crush 6. Qed.

  (*
  Lemma ext_var_ne i j e s n : i <> j -> subst j (ext i e s) (var j n) = subst j s (var j n).
  Proof. crush 5. Qed.
  *)

  Lemma ext_weak i e s : ext i e s ∘ weak i = s.
  Proof. crush 7. Qed.

  (*
  Lemma ext_weak_ne i j e s : i <> j -> ext i e s ∘ weak j = ext i e (s ∘ weak j).
  Proof. intros. crush 8. Qed.
  *)
  
  Lemma under_comm i j s : under i (under j s) = under j (under i s).
  Proof. crush 15. Qed.

End BindDerivedOperators.

Infix "∘" := comp (at level 60, right associativity).
Global Hint Unfold
       subst subst'_of shifts' weaks'
       id comp weaks shifts weak shift ext under under'
  : CrushDB.

Hint Rewrite @under_under' @ext_var_hd @ext_var_tl @ext_weak : SubstDB.

Section BindExtDerivedOperators.

  Context {I} `{Eq I} {A} {Kind : I -> Type} `{bind_ext : BindExt _ Kind A}.
  
  Definition subst_ext : Subst Kind -> A -> A :=
    fun s => subst_ext' (subst'_of s).

  Hint Unfold subst subst_ext : CrushDB.

  Lemma subst_ext_assoc f g e : subst_ext f (subst_ext g e) = subst_ext (f ∘ g) e.
  Proof. crush 14. Qed.

End BindExtDerivedOperators.

Global Hint Unfold subst subst_ext : CrushDB.

(** Other operators useful for defining and verifying subst' *)
Section Subst'Helpers.

  Context {I} `{Eq I} {Kind : I -> Type}
          (** var_e and associativity are the proof obligations that will require induction,
              so we'll assume f_var has been proved already *)
          `{bindvar : BindVar _ Kind}.
  
  Definition get_var' : forall i, nat -> Subst' Kind -> Kind i :=
    fun i n s => s i n zero.
  Hint Unfold get_var' : CrushDB.

  Lemma get_var_get_var' `{bind : @Bind _ _ _ bindvar} i n s
    : get_var' i n (subst'_of s) = s i n.
  Proof. unfold get_var'; crush 3. Qed.
  
  Definition subst'_ok_at {A} (subst' : Subst' Kind -> A -> A) e :=
    (subst' var' e = e) /\
    (forall f g, subst' f (subst' g e) = subst' (f ∘' g) e).

  Definition subst'_ok {A} (subst' : Subst' Kind -> A -> A) :=
    forall e, subst'_ok_at subst' e.

  Definition mkBind (p : forall i, subst'_ok (subst' i)) : Bind Kind.
  Proof. constructor; abstract (unfold subst'_ok in *; firstorder). Defined.
  
  Definition mkBindExt {A} `{bind : @Bind _ _ _ bindvar}
             (subst_ext' : Subst' Kind -> A -> A)
             (p : subst'_ok subst_ext')
    : BindExt Kind A.
  Proof. refine {| subst_ext' := subst_ext' |}; abstract firstorder intuition. Defined.

  Lemma under_ks'_zero s : under_ks' zero s = s. Proof. crush 5. Qed.

  Lemma subst'_ok_map {A} (subst' : Subst' Kind -> A -> A) (es : list A)
    : Forall (subst'_ok_at subst') es ->
      subst'_ok_at (fun s => map (subst' s)) es.
  Proof.
    induction es as [|e es IHes].
    - intros _; split; reflexivity.
    - intros Hees; inversion Hees as [|e' es' [He_var He_assoc] Hes]; subst; clear Hees.
      destruct IHes as [Hvar Hassoc]; auto.
      split; cbn; [congruence|intros f g].
      now repeat multimatch goal with H : _ |- _ => rewrite !H end.
  Qed.

  Lemma subst'_ok_map_map {A}
        (subst_ext' : Subst' Kind -> A -> A)
        (ess : list (list A))
    : Forall (Forall (subst'_ok_at subst_ext')) ess ->
      subst'_ok_at (fun s => map (map (subst_ext' s))) ess.
  Proof.
    induction ess as [|es ess IHess]; [split; reflexivity|].
    intros Heess; inversion Heess as [|? ? Hes Hess]; subst; clear Heess.
    destruct IHess as [Hvar Hassoc]; auto.
    induction es as [|e es IHes]; split; cbn; intros; rewrite ?Hvar, ?Hassoc; auto;
      inversion Hes as [|? ? [Hvar' Hassoc'] Hes']; subst;
      apply IHes in Hes'; destruct Hes' as [Hvar'' Hassoc'']; cbn in *;
      rewrite ?Hvar', ?Hvar'', ?Hassoc', ?Hassoc'', ?Hassoc; [congruence|].
     specialize (Hassoc'' f g); congruence.
  Qed.
  
  Lemma under'_var' i : under' i var' = var'. Proof. crush 5. Qed.

  Lemma under'_comp' i f g : under' i (f ∘' g) = under' i f ∘' under' i g.
  Proof. crush 9. Qed.

End Subst'Helpers.

Hint Rewrite @under_ks'_zero @under'_var' @under'_comp' @get_var_get_var'
  : CrushDB SubstDB.

(** Lifting substitutions to commonly-used type constructors *)

Lemma map_subst'_ok {A} {I} (Kind : I -> Type) `{BindVar _ Kind}
      (subst' : Subst' Kind -> A -> A)
      (ok : subst'_ok subst')
  : subst'_ok (fun s => map (subst' s)).
Proof.
  intros es; split; intros; (induction es as [|e es IHes]; [easy|]);
  cbn; destruct (ok e) as [var_e assoc]; intuition congruence.
Qed.

Lemma map_prod_subst'_ok {A B} {I} (Kind : I -> Type) `{BindVar _ Kind}
      (subst_ext'1 : Subst' Kind -> A -> A)
      (subst_ext'2 : Subst' Kind -> B -> B)
      (ok1 : subst'_ok subst_ext'1)
      (ok2 : subst'_ok subst_ext'2)
  : subst'_ok (fun s => map (fun '(x, y) => (subst_ext'1 s x, subst_ext'2 s y))).
Proof.
  intros es; split; intros; (induction es as [|[e1 e2] es IHes]; [easy|]);
  cbn; destruct (ok1 e1) as [var_e1 assoc1]; destruct (ok2 e2) as [var_e2 assoc2]; intuition congruence.
Qed.

Lemma map_prod_subst'_ok_hc {A B} {I} (C : Type) (Kind : I -> Type) `{BindVar _ Kind}
      (subst_ext'1 : Subst' Kind -> A -> A)
      (subst_ext'2 : Subst' Kind -> B -> B)
      (ok1 : subst'_ok subst_ext'1)
      (ok2 : subst'_ok subst_ext'2)
  : subst'_ok (fun s => map ((fun '(x, y, z) => (subst_ext'1 s x, subst_ext'2 s y, z)) :
                               (A * B * C) -> (A * B * C))).
Proof.
  intros es; split; intros; (induction es as [|[[e1 e2] e3] es IHes]; [easy|]); cbn; destruct (ok1 e1) as [var_e1 assoc1]; destruct (ok2 e2) as [var_e2 assoc2]; intuition congruence.
Qed.

Lemma option_map_subst'_ok {A} {I} (Kind : I -> Type) `{BindVar _ Kind}
      (subst' : Subst' Kind -> A -> A)
      (ok : subst'_ok subst')
  : subst'_ok (fun s => option_map (subst' s)).
Proof.
  intros e; split; intros; cbn; (destruct e as [e|]; [|reflexivity]);
  cbn; destruct (ok e) as [var_e assoc]; now rewrite ?var_e, ?assoc.
Qed.

Lemma pmap_subst'_ok {A} {I} (Kind : I -> Type) `{BindVar _ Kind}
      (subst' : Subst' Kind -> A -> A)
      (ok : subst'_ok subst')
  : subst'_ok (fun s => pmap (subst' s)).
Proof.
  intros es; split; intros; (induction es as [e|e es IHes]);
  cbn; destruct (ok e) as [var_e assoc]; intuition congruence.
Qed.

Global Hint Resolve
       map_subst'_ok map_subst'_ok map_prod_subst'_ok map_prod_subst'_ok_hc
       option_map_subst'_ok pmap_subst'_ok
  : OKDB.

(** Tactic [simpl_ok] to help solve *_ok obligations.
    Uses hint database SubstDB. *)

Ltac intros_ok_at := split; intros.

Ltac elim_ok_at :=
  repeat match goal with
  | H : subst'_ok_at _ _ |- _ => destruct H as [? ?]
  end.

Ltac rewrites := repeat multimatch goal with H : _ |- _ => rewrite !H end.

Ltac saturate_subst_ok_map :=
  repeat multimatch goal with
  | H : subst'_ok ?sub' |- context [pmap (?sub' _) ?e] =>
    lazymatch goal with
    | _ : subst'_ok_at (fun _ => pmap (?sub _)) e |- _ => fail
    | _ =>
      let H' := fresh in
      pose proof (pmap_subst'_ok _ _ H) as H';
      specialize (H' e)
    end
  | H : subst'_ok ?sub' |- context [option_map (?sub' _) ?e] =>
    lazymatch goal with
    | _ : subst'_ok_at (fun _ => option_map (?sub _)) e |- _ => fail
    | _ =>
      let H' := fresh in
      pose proof (option_map_subst'_ok _ _ H) as H';
      specialize (H' e)
    end
  | H : subst'_ok ?sub' |- context [map (fun '(_, _) => (?sub' _ _, ?sub' _ _)) ?e] =>
    lazymatch goal with
    | _ : subst'_ok_at (fun _ => map (fun '(_, _) => (sub' _ _, sub' _ _))) e |- _ => fail
    | _ =>
      let H' := fresh in
      pose proof (map_prod_subst'_ok _ _ _ H H) as H';
      specialize (H' e)
    end
  | Ha : subst'_ok ?suba', Hb : subst'_ok ?subb'
    |- context [map (fun '(_, _) => (?suba' _ _, ?subb' _ _)) ?e] =>
    lazymatch goal with
    | _ : subst'_ok_at (fun _ => map (fun '(_, _) => (suba' _ _, subb' _ _))) e |- _ => fail
    | _ =>
      let H := fresh in
      pose proof (map_prod_subst'_ok _ _ _ Ha Hb) as H;
      specialize (H e)
    end
  end.

Ltac saturate_subst_ok_Forall :=
  repeat match goal with
         | H : Forall (Forall _) _ |- _ => apply subst'_ok_map_map in H
         | H : Forall _ _ |- _ => apply subst'_ok_map in H
         end.

Ltac saturate_ok_at :=
  repeat multimatch goal with
  | H : subst'_ok ?sub' |- context [?sub' _ ?e] =>
    lazymatch goal with
    | _ : subst'_ok_at sub' e |- _ => fail
    | _ => pose proof (H e)
    end
  end.

(** Mutable tactic to be extended as the user proves lemmas of the form (subst'_ok subst') *)
Tactic Notation "pose_ok_proofs'" := idtac.
Ltac pose_ok_proofs := pose_ok_proofs'.

Ltac simpl_ok :=
  pose_ok_proofs;
  autounfold with SubstDB; autorewrite with SubstDB;
  saturate_subst_ok_Forall;
  saturate_subst_ok_map;
  saturate_ok_at; elim_ok_at; rewrites.

Global Hint Unfold get_var' : CrushDB SubstDB.
