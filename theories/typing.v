From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive.
Require Import ExtLib.Structures.Monads.

Import Monads.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.

Module M := PositiveMap.

Require Import RWasm.EnsembleUtil (* TODO fix naming convention :) *). 
Require Import RWasm.tactics RWasm.term RWasm.memory RWasm.list_util RWasm.map_util
        RWasm.debruijn RWasm.subst.

(* Used in progress, preservation_GC *)
Axiom LEM : forall (P : Prop), P \/ ~ P.

Section Monads.

  Global Instance OptionMonad : Monad option :=
  { ret := @Some;
    bind :=
      fun t u m f =>
        match m with
        | Some x => f x
        | None => None
        end
  }.

Definition mret {m : Type -> Type} {Hm : Monad m} {t : Type} := 
  @Monad.ret m Hm t.

End Monads.

(* Conversion from [Size] to [nat] *)

Fixpoint size_closed (s : Size) : Prop :=
  match s with
  | SizeVar _ => False
  | SizePlus s1 s2 => size_closed s1 /\ size_closed s2
  | SizeConst i => True
  end.

Definition sizes_closed (ss : list Size) : Prop :=
  List.Forall size_closed ss.

Definition to_size (s : Size) (H : size_closed s) : nat.
  induction s.
  - inversion H.
  - inversion H. exact (IHs1 H0 + IHs2 H1).
  - exact n.
Defined.


Definition to_sizes (ss : list Size) (H : sizes_closed ss) : list nat.
  induction ss.
  + exact [].
  + assert (Hs : size_closed a).
    { inversion H. eassumption. } 
    assert (Hss : sizes_closed ss).
    { inversion H. eassumption. } 
    exact (to_size a Hs :: (IHss Hss)).
Defined.

Definition size_of_value (v : Value) : Size := SizeConst (size_val v).

Section TypeSize.

  Fixpoint size_to_nat (s : Size) : option nat :=
    match s with
    | SizeVar _ => None
    | SizePlus s1 s2 =>
      match size_to_nat s1 with
      | Some n1 =>
        match size_to_nat s2 with
        | Some n2 => Some (n1 + n2)
        | None => None
        end
      | None => None
      end
    | SizeConst i => Some i
    end.


  Definition fold_size (s : list (option Size)) : option Size :=
    fold_right
      (fun (o1 o2 : option Size) =>
         s1 <- o1;; s2 <- o2;; Monad.ret (SizePlus s1 s2)) (mret (SizeConst 0)) s.

  Fixpoint sizeOfPretype (T : list (Size * Qual * HeapableConstant)) (pt : Pretype) : option Size :=
    match pt with
    | Num nt =>
      match nt with
      | Int _ i32 | Float f32 => Some (SizeConst 32)
      | Int _ i64 | Float f64 => Some (SizeConst 64)
      end
    | TVar a => option_map (fun '(sz, _, _) => sz) (nth_error T a)
    | OwnR _
    | CapT _ _ _
    | Unit => Some (SizeConst 0)
    | ProdT ts => fold_size (map (sizeOfType T) ts)
    | PtrT _ | CoderefT _ | RefT _ _ _ => Some (SizeConst 64)
    | Rec q t =>
      let bogus := SizeConst 0 in
      sizeOfType ((bogus, q, Heapable) :: T) t
      (*
      if rec_var_under_ref_typ t 0
      then let bogus := SizeConst 0 in sizeOfType ((bogus, q) :: T) t
      else None
       *)
    | ExLoc t => sizeOfType T t
    end
  with sizeOfType T (t : Typ) : option Size :=
         match t with
         | QualT pt _ => sizeOfPretype T pt
         end.

  Fixpoint model_satisfies_context_from_idx 
           {A B}
           (leq : B -> B -> Prop)
           (lift_model : (nat -> B) -> (A -> B))
           (model : nat -> B)
           (ctx : list (list A * list A))
           (idx : nat) :=
    match ctx with
    | [] => True
    | (lst1, lst2) :: ctx' =>
      Forall
        (fun obj =>
           leq (lift_model model obj) (model idx))
        lst1 /\
      Forall
        (fun obj =>
           leq (model idx) (lift_model model obj))
        lst2 /\
      model_satisfies_context_from_idx
        leq
        lift_model
        model
        ctx'
        (Datatypes.S idx)
    end.

  Definition model_satisfies_context
             {A B}
             (leq : B -> B -> Prop)
             (lift_model : (nat -> B) -> (A -> B))
             (model : nat -> B)
             (ctx : list (list A * list A)) :=
    model_satisfies_context_from_idx leq lift_model model ctx 0.

  Inductive list_sub {T}: list T -> list T -> Prop :=
      | L_nil: forall L, list_sub [] L
      | L_cons: forall x L L',
          list_sub L L' ->
          list_sub (x::L) (x::L').

  Lemma list_sub_model_gen : forall {A B leq lift_model model ctx ctx' idx},
      @model_satisfies_context_from_idx A B leq lift_model model ctx' idx ->
      list_sub ctx ctx' ->
      model_satisfies_context_from_idx leq lift_model model ctx idx.
  Proof.
    induction ctx; [ constructor | ].
    intros.
    destruct_prs.
    match goal with
    | [ H : list_sub _ _ |- _ ] => inversion H; subst
    end.
    simpl in *.
    destructAll.
    do 2 ltac:(split; auto).
    eauto.
  Qed.

  Lemma list_sub_model : forall {A B leq lift_model model ctx ctx'},
      @model_satisfies_context A B leq lift_model model ctx' ->
      list_sub ctx ctx' ->
      model_satisfies_context leq lift_model model ctx.
  Proof.
    unfold model_satisfies_context.
    intros.
    eapply list_sub_model_gen; eauto.
  Qed.

  Definition ctx_imp_leq
             {A B}
             (leq : B -> B -> Prop)
             (lift_model : (nat -> B) -> (A -> B))
             (ctx : list (list A * list A))
             (obj1 : A)
             (obj2 : A) :=
    forall (model : nat -> B),
      model_satisfies_context leq lift_model model ctx ->
      leq (lift_model model obj1) (lift_model model obj2).

  Lemma list_sub_ctx_imp_leq : forall {A B leq lift_model ctx ctx' obj1 obj2},
      @ctx_imp_leq A B leq lift_model ctx obj1 obj2 ->
      list_sub ctx ctx' ->
      @ctx_imp_leq A B leq lift_model ctx' obj1 obj2.
  Proof.
    unfold ctx_imp_leq.
    intros.
    eapply H.
    eapply list_sub_model; eauto.
  Qed.
  
  Lemma ctx_imp_leq_refl : forall {A B} {leq : B -> B -> Prop} {lift_model ctx obj},
      (forall obj', leq obj' obj') ->
      @ctx_imp_leq A B leq lift_model ctx obj obj.
  Proof.
    unfold ctx_imp_leq.
    intros.
    eauto.
  Qed.

  Lemma ctx_imp_leq_trans : forall {A B} {leq : B -> B -> Prop} {lift_model ctx obj1 obj2 obj3},
      (forall obj1' obj2' obj3',
          leq obj1' obj2' ->
          leq obj2' obj3' ->
          leq obj1' obj3') ->
      @ctx_imp_leq A B leq lift_model ctx obj1 obj2 ->
      @ctx_imp_leq A B leq lift_model ctx obj2 obj3 ->
      @ctx_imp_leq A B leq lift_model ctx obj1 obj3.
  Proof.
    unfold ctx_imp_leq.
    intros.
    repeat match goal with
           | [ H : forall _, _ -> _,
               H' : model_satisfies_context _ _ _ _ |- _ ] =>
             specialize (H _ H')
           end.
    eauto.
  Qed.

  (* A solver is needed for that *)
  Axiom SizeLeq : list (list Size * list Size) -> Size -> Size -> option bool.

  Fixpoint interp_size (model : nat -> nat) (sz : Size) :=
    match sz with
    | SizeVar v => model v
    | SizeConst c => c
    | SizePlus sz1 sz2 =>
      (interp_size model sz1) + (interp_size model sz2)
    end.

  Axiom SizeLeq_desc : forall C q1 q2,
      SizeLeq C q1 q2 = Some true <->
      ctx_imp_leq Peano.le interp_size C q1 q2.
  
  Theorem SizeLeq_Refl : forall C s, SizeLeq C s s = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    eapply ctx_imp_leq_refl; eauto.
  Qed.

  Theorem SizeLeq_Trans :
    forall C q1 q2 q3,
      SizeLeq C q1 q2 = Some true ->
      SizeLeq C q2 q3 = Some true ->
      SizeLeq C q1 q3 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite SizeLeq_desc.
    eapply ctx_imp_leq_trans; eauto.
    exact Nat.le_trans.
  Qed.

  Lemma size_to_nat_interp_size : forall {sz c model},
      size_to_nat sz = Some c ->
      interp_size model sz = c.
  Proof.
    induction sz; intros; simpl in *.
    - inversion H.
    - destruct (size_to_nat sz1); destruct (size_to_nat sz2).
      all:
        match goal with
        | [ H : _ = Some _ |- _ ] => inversion H; subst
        end.
      eauto.
    - inversion H; subst; auto.
  Qed.

  Theorem SizeLeq_Const : forall sz1 sz2 c1 c2,
      size_to_nat sz1 = Some c1 ->
      size_to_nat sz2 = Some c2 ->
      SizeLeq [] sz1 sz2 = Some true ->
      c1 <= c2.
  Proof.
    do 4 intro.
    rewrite SizeLeq_desc.
    intros.
    unfold ctx_imp_leq in *.
    match goal with
    | [ H : forall _, _ -> _ |- _ ] =>
      specialize (H (fun _ => 0))
    end.
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { constructor. }
    match goal with
    | [ H : ?A <= _ |- ?B <= _ ] =>
      let H' := fresh "H" in
      assert (H' : A = B)
    end.
    { apply size_to_nat_interp_size; auto. }
    match goal with
    | [ H : _ <= ?A |- _ <= ?B ] =>
      let H' := fresh "H" in
      assert (H' : A = B)
    end.
    { apply size_to_nat_interp_size; auto. }
    subst; auto.
  Qed.

  Lemma size_to_nat_None_unbounded : forall {sz bound},
      size_to_nat sz = None ->
      exists model,
        interp_size model sz >= bound.
  Proof.
    induction sz.
    - intros.
      exists (fun _ => bound).
      simpl; auto.
    - intros.
      simpl in *.
      remember (size_to_nat sz1) as obj.
      generalize (eq_sym Heqobj).
      destruct obj.
      -- intros.
         remember (size_to_nat sz2) as obj2.
         generalize (eq_sym Heqobj2).
         destruct obj2.
         --- inversion H.
         --- intros.
             specialize (IHsz2 bound eq_refl).
             destructAll.
             match goal with
             | [ H : interp_size ?A _ >= _ |- _ ] =>
               exists A
             end.
             unfold Peano.ge.
             eapply Nat.le_trans; [ | apply le_plus_r ].
             auto.
      -- intros.
         specialize (IHsz1 bound eq_refl).
         destructAll.
         match goal with
         | [ H : interp_size ?A _ >= _ |- _ ] =>
           exists A
         end.
         unfold Peano.ge.
         eapply Nat.le_trans; [ | apply Nat.le_add_r ].
         auto.
    - intros; simpl in *.
      inversion H.
  Qed.

  Theorem SizeLeq_right_closed_imp_left_closed : forall sz1 sz2 c2,
      size_to_nat sz2 = Some c2 ->
      SizeLeq [] sz1 sz2 = Some true ->
      exists c1,
        size_to_nat sz1 = Some c1.
  Proof.
    do 3 intro.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    remember (size_to_nat sz1) as obj.
    generalize (eq_sym Heqobj); destruct obj; eauto.
    let H' := fresh "H" in
    intro H'; apply (size_to_nat_None_unbounded (bound:=Datatypes.S c2)) in H'.
    destructAll.
    match goal with
    | [ H : interp_size ?F _ >= _, H' : forall _, _ -> _ |- _ ] =>
      specialize (H' F)
    end.
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { constructor. }
    match goal with
    | [ H : size_to_nat ?SZ = Some _,
        H' : _ <= interp_size _ ?SZ |- _ ] =>
      erewrite (size_to_nat_interp_size (sz:=SZ)) in H'; eauto
    end.
    unfold Peano.ge in *.
    match goal with
    | [ H : _ <= ?A, H' : ?A <= _ |- _ ] =>
      specialize (Nat.le_trans _ _ _ H H')
    end.
    intros.
    exfalso; eapply Nat.nle_succ_diag_l; eauto.
  Qed.

  Theorem SizeLeq_Bottom : forall C s, SizeLeq C (SizeConst 0) s = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    simpl.
    apply Peano.le_0_n.
  Qed.

  Theorem SizeLeq_leq :
    forall s1 s2 n1 n2 s,
      size_to_nat s1 = Some n1 ->
      size_to_nat s2 = Some n2 ->
      n1 <= n2 ->
      SizeLeq s s1 s2 = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    erewrite size_to_nat_interp_size; [ | eauto ].
    erewrite size_to_nat_interp_size; [ | eauto ].
    auto.
  Qed.

  Theorem SizeLeq_Bigger_Ctx : forall C C' s1 s2,
      SizeLeq C s1 s2 = Some true ->
      list_sub C C' ->
      SizeLeq C' s1 s2 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite SizeLeq_desc.
    apply list_sub_ctx_imp_leq.
  Qed.

End TypeSize.


Record Module_Ctx :=
  { func   : list FunType;
    global : list GlobalType;
    table  : list FunType;
  }.

Definition Local_Ctx := list (Typ * Size).

Record Function_Ctx :=
  { label  : list (list Typ * Local_Ctx);
    ret    : option (list Typ);
    (* Type variables and their constraints *)
    qual   : list (list Qual * list Qual);
    size   : list (list Size * list Size);
    type   : list (Size * Qual * HeapableConstant);
    location : nat; (* The number of free location variables *)
    linear : plist Qual;
  }.

Definition heapable (f : Function_Ctx) :=
  map (fun '(_, _, hc) => hc) (type f).

(* Shifting in environments *)

Definition subst'_local_ctx (su : Subst' Kind) : Local_Ctx -> Local_Ctx :=
  map (fun '(t, s) => (subst'_type su t, subst'_size su s)).

(* TODO for some reason map_prod_subst'ok doesn't get applied automatically
   despite being in OKDB *)
Lemma subst'_local_ctx_ok : subst'_ok subst'_local_ctx.
Proof. unfold subst'_local_ctx; apply map_prod_subst'_ok; pose_ok_proofs; auto. Qed.
Global Hint Resolve subst'_local_ctx_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_local_ctx_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Instance BindExtLocalCtx : BindExt Kind Local_Ctx := ltac:(mkBindExt).

Definition subst'_function_ctx (su : Subst' Kind) (ctx : Function_Ctx) : Function_Ctx :=
  {| label :=
       map (fun '(ts, lctx) => (subst'_types su ts, subst'_local_ctx su lctx)) (label ctx);
     ret := option_map (subst'_types su) (ret ctx);
     qual := map (fun '(qs1, qs2) => (subst'_quals su qs1, subst'_quals su qs2)) (qual ctx);
     size := map (fun '(ss1, ss2) => (subst'_sizes su ss1, subst'_sizes su ss2)) (size ctx);
     type := map (fun '(s, q, hc) => (subst'_size su s, subst'_qual su q, hc)) (type ctx);
     location := location ctx;
     linear := pmap (subst'_qual su) (linear ctx) |}.


Lemma function_ctx_eq : forall {F F'},
    label F = label F' ->
    ret F = ret F' ->
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    linear F = linear F' ->
    F = F'.
Proof.
  intros.
  destruct F; destruct F'; subst; simpl in *.
  repeat match goal with
         | [ H : _ = _ |- _ ] => rewrite H; clear H
         end.
  auto.
Qed.

Lemma subst'_label_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(ts, lctx) =>
             (subst'_types su ts, subst'_local_ctx su lctx)))).
Proof.
  apply map_prod_subst'_ok.
  - apply subst'_types_ok.
  - apply subst'_local_ctx_ok.
Qed.

Lemma subst'_ret_function_ctx_ok :
  subst'_ok
    (fun su =>
       (option_map (subst'_types su))).
Proof.
  apply option_map_subst'_ok.
  apply subst'_types_ok.
Qed.

Lemma subst'_qual_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(qs0, qs1) =>
             (subst'_quals su qs0, subst'_quals su qs1)))).
Proof.
  apply map_prod_subst'_ok; apply subst'_quals_ok.
Qed.

Lemma subst'_size_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(szs0, szs1) =>
             (subst'_sizes su szs0, subst'_sizes su szs1)))).
Proof.
  apply map_prod_subst'_ok; apply subst'_sizes_ok.
Qed.

Lemma subst'_type_function_ctx_ok :
  subst'_ok
    (fun su =>
       (@map
          (Size * Qual * HeapableConstant)
          _
          (fun '(s, q, hc) =>
             (subst'_size su s, subst'_qual su q, hc)))).
Proof.
  apply map_prod_subst'_ok_hc.
  - apply subst'_size_ok.
  - apply subst'_qual_ok.
Qed.

Lemma subst'_linear_function_ctx_ok :
  subst'_ok (fun su => (pmap (subst'_qual su))).
Proof.
  apply pmap_subst'_ok.
  apply subst'_qual_ok.
Qed.

Lemma subst'_function_ctx_ok : subst'_ok subst'_function_ctx.
Proof.
  Ltac use_eq1 lem :=
    specialize lem;
    unfold subst'_ok;
    unfold subst'_ok_at;
    intros;
    match goal with
    | [ H : forall _, _ /\ _ |- _ = ?X ] =>
      specialize (H X); destruct H as [H]; rewrite H; auto
    end.
  Ltac use_eq2 lem :=
    specialize lem;
    unfold subst'_ok;
    unfold subst'_ok_at;
    intros;
    match goal with
    | [ H : forall _, _ /\ _ |- _ = _ _ ?X ] =>
      specialize (H X); destruct H as [_ H]; rewrite H; auto
    end.
  
  unfold subst'_ok.
  intros.
  unfold subst'_ok_at.
  split.
  - unfold subst'_function_ctx.
    apply function_ctx_eq; simpl in *; auto.
    -- use_eq1 subst'_label_function_ctx_ok.
    -- use_eq1 subst'_ret_function_ctx_ok.
    -- use_eq1 subst'_qual_function_ctx_ok.
    -- use_eq1 subst'_size_function_ctx_ok.
    -- use_eq1 subst'_type_function_ctx_ok.
    -- use_eq1 subst'_linear_function_ctx_ok.
  - intros.
    unfold subst'_function_ctx.
    apply function_ctx_eq; simpl in *; auto.
    -- use_eq2 subst'_label_function_ctx_ok.
    -- use_eq2 subst'_ret_function_ctx_ok.
    -- use_eq2 subst'_qual_function_ctx_ok.
    -- use_eq2 subst'_size_function_ctx_ok.
    -- use_eq2 subst'_type_function_ctx_ok.
    -- use_eq2 subst'_linear_function_ctx_ok.
Qed.

Global Hint Resolve subst'_function_ctx_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_function_ctx_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Instance BindExtFunctionCtx : BindExt Kind Function_Ctx := ltac:(mkBindExt).

(* Empty Ctxes *)
Definition empty_Module_Ctx : Module_Ctx := Build_Module_Ctx [] [] [].
Definition empty_Function_Ctx : Function_Ctx := Build_Function_Ctx [] None [] [] [] 0 (Single_p (QualConst Unrestricted)).

(* Setters for Ctx *)
Definition update_label_ctx (lab : list (list Typ * Local_Ctx)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx _ r q s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_ret_ctx (r : option (list Typ)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab _ q s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_qual_ctx (q : list (list Qual * list Qual)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r _ s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_size_ctx (s : list (list Size * list Size)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q _ t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_type_ctx (t : list (Size * Qual * HeapableConstant)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s _ l lin := C in
  Build_Function_Ctx lab r q s t l lin.

(* TODO check what this is for *)
Definition update_location_ctx (l : nat) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s t _ lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_linear_ctx (lin : plist Qual) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s t l _ := C in
  Build_Function_Ctx lab r q s t l lin.

Definition HeapTyping := M.t HeapType.

Definition SplitHeapTyping (H1 H2 H3 : HeapTyping) : Prop :=
  Dom_ht H1 :|: Dom_ht H2 <--> Dom_ht H3 /\
  (forall l t, get_heaptype l H3 = Some t ->
               (get_heaptype l H1 = Some t /\ get_heaptype l H2 = None) /\
               (get_heaptype l H1 = None /\ get_heaptype l H2 = Some t)).             

Inductive ExactlyInOne : bool -> Ptr -> HeapType -> list HeapTyping -> Prop :=
| FoundNil :
    forall l ht, 
      ExactlyInOne true l ht []
| InHead :
    forall l ht H Hs, 
      get_heaptype l H = Some ht ->
      ExactlyInOne true l ht Hs ->
      ExactlyInOne false l ht (H :: Hs)
| NotInHead :    
    forall b l ht H Hs, 
      get_heaptype l H = None ->
      ExactlyInOne b l ht Hs ->
      ExactlyInOne b l ht (H :: Hs).
     
Definition SplitHeapTypings (Hs : list HeapTyping) (H : HeapTyping) : Prop :=
  Union_list (map Dom_ht Hs) <--> Dom_ht H /\
  (forall l ht, get_heaptype l H = Some ht -> ExactlyInOne false l ht Hs). 


Definition Empty_HeapTyping (H : HeapTyping) : Prop :=
  Dom_ht H <--> Ensembles.Empty_set _. 
  
Fixpoint nth_upd {A} (l : list A) (i : nat) (a : A) :=
  match l with
  | nil => l
  | cons x l =>
    match i with
    | 0 => a :: l
    | Datatypes.S i => x :: nth_upd l i a
    end
  end.

Definition get_localtype (l : nat) (loc : Local_Ctx) :=
  nth_error loc l.

Definition set_localtype (l : nat) (tau : Typ) (sz : Size) (loc : Local_Ctx) : Local_Ctx :=
  nth_upd loc l (tau, sz).

Definition InstanceTyping := list Module_Ctx. 

Record StoreTyping :=
  { InstTyp : InstanceTyping;
    LinTyp  : HeapTyping;
    UnrTyp : HeapTyping
  }.

Definition SplitStoreTypings (Ss : list StoreTyping) (S : StoreTyping) : Prop :=
  Forall (fun S' => InstTyp S = InstTyp S' /\ UnrTyp S = UnrTyp S') Ss /\
  let Hs := map LinTyp Ss in
  SplitHeapTypings Hs (LinTyp S).

Definition EmptyLinHeapTyping (S : StoreTyping) : Prop :=
  Empty_HeapTyping (LinTyp S).

Section QualLt.

  (* Definition Leq (c1 c2 : QaulConstant) : bool := *)
  (*   match c1, c2 with *)
  (*   | Unrestricted, _ => true *)
  (*   | Affine, Affine => true *)
  (*   | Affine, Linear => true *)
  (*   | _, Linear => true *)
  (*   | _, _ => false *)
  (*   end. *)

  (* Definition find_qual (m : M.t UseConstant) (q : Use) : option UseConstant := *)
  (*   match q with *)
  (*   | UseVar x => M.find x m *)
  (*   | UseConst x => Some x *)
  (*   end. *)


  (* Definition QualLeq (m : M.t UseConstant) (q1 q2 : Use) : Prop := *)
  (*   match q1, q2 with *)
  (*   | UseConst c1, UseConst c2 => Leq c1 c2 = true *)
  (*   | UseVar x, UseConst c2 => *)
  (*     match M.find x m with *)
  (*     | Some c1 => Leq c1 c2 = true *)
  (*     | None => False *)
  (*     end *)
  (*   | _, UseVar _ => False                        *)
  (*   end. *)

  (* A solver is needed for that *) 

  (* Zoe: If more axioms are needed we could have a separate interface for that at some point *)

  Axiom QualLeq : list (list Qual * list Qual) -> Qual -> Qual -> option bool.

  Definition le_qualconst qc1 qc2 :=
    match qc1, qc2 with
    | Unrestricted, _ => True
    | _, Linear => True
    | _, _ => False
    end.

  Fixpoint interp_qual (model : nat -> QualConstant) (q : Qual) :=
    match q with
    | QualVar v => model v
    | QualConst c => c
    end.

  Axiom QualLeq_desc : forall C q1 q2,
      QualLeq C q1 q2 = Some true <->
      ctx_imp_leq le_qualconst interp_qual C q1 q2.

  Theorem QualLeq_Top : forall C q, QualLeq C q Linear = Some true.
  Proof.
    intros.
    rewrite QualLeq_desc.
    unfold ctx_imp_leq.
    intros.
    simpl; unfold le_qualconst.
    destruct (interp_qual model q); auto.
  Qed.

  Theorem QualLeq_Refl : forall C q, QualLeq C q q = Some true. 
  Proof.
    intros.
    rewrite QualLeq_desc.
    eapply ctx_imp_leq_refl; eauto.
    intros.
    destruct obj'; simpl; auto.
  Qed.

  Theorem QualLeq_Trans :
    forall C q1 q2 q3,
      QualLeq C q1 q2 = Some true ->
      QualLeq C q2 q3 = Some true ->
      QualLeq C q1 q3 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite QualLeq_desc.
    eapply ctx_imp_leq_trans; eauto.
    intros.
    destruct obj1'; destruct obj2'; destruct obj3'; simpl in *; auto.
  Qed.

  Theorem QualLeq_Bigger_Ctx : forall C C' q1 q2,
      QualLeq C q1 q2 = Some true ->
      list_sub C C' ->
      QualLeq C' q1 q2 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite QualLeq_desc.
    apply list_sub_ctx_imp_leq.
  Qed.

  Lemma eq_dec_nat : forall a b : nat,
      a = b \/ a <> b.
  Proof.
    intros.
    specialize (OrderedTypeEx.Nat_as_OT.eq_dec a b).
    intros.
    case H; eauto.
  Qed.

  Theorem QualLeq_Empty_Ctx : forall q1 q2,
      QualLeq [] q1 q2 = Some true ->
      q1 = q2 \/
      q1 = Unrestricted \/
      q2 = Linear.
  Proof.
    do 2 intro.
    rewrite QualLeq_desc.
    unfold ctx_imp_leq.
    intros.
    destruct q1; destruct q2; simpl.
    - left.
      assert (Heq : v = v0 \/ v <> v0) by apply eq_dec_nat.
      case Heq; auto.
      intros.
      specialize
        (H
           (fun v' =>
              if OrderedTypeEx.Nat_as_OT.eq_dec v v'
              then Linear
              else Unrestricted)).
      match goal with
      | [ H : ?A -> _ |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A); [ | specialize (H H') ]
      end.
      { constructor. }
      simpl in *.
      remember (OrderedTypeEx.Nat_as_OT.eq_dec v v) as obj.
      destruct obj; [ | exfalso; eauto ].
      remember (OrderedTypeEx.Nat_as_OT.eq_dec v v0) as obj2.
      destruct obj2; [ subst; exfalso; eauto | ].
      simpl in *.
      exfalso; auto.
    - destruct q; [ | right; right; auto ].
      specialize (H (fun _ => Linear)).
      match goal with
      | [ H : ?A -> _ |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A); [ | specialize (H H') ]
      end.
      { constructor. }
      simpl in *.
      exfalso; auto.
    - destruct q; [ right; left; auto | ].
      specialize (H (fun _ => Unrestricted)).
      match goal with
      | [ H : ?A -> _ |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A); [ | specialize (H H') ]
      end.
      { constructor. }
      simpl in *.
      exfalso; auto.
    - destruct q; [ right; left; auto | ].
      destruct q0; [ | right; right; auto ].
      specialize (H (fun _ => Unrestricted)).
      match goal with
      | [ H : ?A -> _ |- _ ] =>
        let H' := fresh "H" in
        assert (H' : A); [ | specialize (H H') ]
      end.
      { constructor. }
      simpl in *.
      exfalso; auto.
  Qed.

  Theorem QualLeq_Const_False : QualLeq [] Linear Unrestricted = Some true -> False.
  Proof.
    intros.
    apply QualLeq_Empty_Ctx in H.
    case H; [ | intro H'; case H' ]; intro H''; inversion H''.
  Qed.

  Theorem QualLeq_Top_Const : forall q, QualLeq [] Linear q = Some true -> q = Linear.
  Proof.
    intros.
    apply QualLeq_Empty_Ctx in H.
    case H; auto.
    intro H'; case H'; auto.
    intro H''; inversion H''.
  Qed.

  Theorem QualLeq_Bottom_Const : forall q, QualLeq [] q Unrestricted = Some true -> q = Unrestricted.
  Proof.
    intros.
    apply QualLeq_Empty_Ctx in H.
    case H; auto.
    intro H'; case H'; auto.
    intro H''; inversion H''.
  Qed.

End QualLt.


(*
  Inductive RecQualValidTyp : Qual -> term.var -> Typ -> Prop :=
   | RecQualValidQualT : forall q x pt qpt,
       RecQualValidPretype q qpt x pt ->
       RecQualValidTyp q x (QualT pt qpt)
   with RecQualValidPretype : Qual -> Qual -> term.var -> Pretype -> Prop :=
   | RecQualValidNum : forall q qpt x n,
       RecQualValidPretype q qpt x (Num n)
   | RecQualValidTVarSame : forall q qpt x xpt,
       x = xpt -> q = qpt ->
       RecQualValidPretype q qpt x (TVar xpt)
   | RecQualValidTVarOther : forall q qpt x xpt,
       x <> xpt ->
       RecQualValidPretype q qpt x (TVar xpt)
   | RecQualValidUnit : forall q qpt x,
       RecQualValidPretype q qpt x Unit
   | RecQualValidProdT : forall q qpt x taus,
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidPretype q qpt x (ProdT taus)
   | RecQualValidCoderefT : forall q qpt x chi,
       RecQualValidPretype q qpt x (CoderefT chi)
   | RecQualValidRec : forall qα q qpt x tau,
       RecQualValidTyp q (x + 1) tau ->
       RecQualValidPretype q qpt x (Rec qα tau)
   | RecQualValidPtr : forall q qpt x l,
       RecQualValidPretype q qpt x (PtrT l)
   | RecQualValidExLoc : forall q qpt x tau,
       RecQualValidTyp q x tau ->
       RecQualValidPretype q qpt x (ExLoc tau)
   | RecQualValidOwnR : forall q qpt x l,
       RecQualValidPretype q qpt x (OwnR l)
   | RecQualValidCapT : forall q qpt x c l ht,
       RecQualValidHeapType q x ht ->
       RecQualValidPretype q qpt x (CapT c l ht)
   | RecQualValidRefT : forall q qpt x c l ht,
       RecQualValidHeapType q x ht ->
       RecQualValidPretype q qpt x (RefT c l ht)
   with RecQualValidHeapType : Qual -> term.var -> HeapType -> Prop :=
   | RecQualValidVariant : forall q x taus,
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidHeapType q x (VariantType taus)
   | RecQualValidStruct : forall q x tauszs taus szs,
       split tauszs = (taus, szs) ->
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidHeapType q x (StructType tauszs)
   | RecQualValidArray : forall q x tau,
       RecQualValidTyp q x tau ->
       RecQualValidHeapType q x (ArrayType tau)
   | RecQualValidEx : forall qα q x sz tau,
       RecQualValidTyp q (x + 1) tau ->
       RecQualValidHeapType q x (Ex sz qα tau).
  *)

  Inductive RecVarUnderRefTyp : Typ -> term.var -> bool -> Prop :=
    | RecVarUnderRefT : forall pt q v b,
        RecVarUnderRefPretype pt v b ->
        RecVarUnderRefTyp (QualT pt q) v b
  with RecVarUnderRefPretype : Pretype -> term.var -> bool -> Prop :=
    | RecVarUnderRefRef : forall c l ht v,
        RecVarUnderRefPretype (RefT c l ht) v true
    | RecVarUnderRefCap : forall c l ht v,
        RecVarUnderRefPretype (CapT c l ht) v true
    | RecVarUnderRefVar : forall v1 v2,
        RecVarUnderRefPretype (TVar v1) v2 (negb (Nat.eqb v1 v2))
    | RecVarUnderRefNum : forall n v,
        RecVarUnderRefPretype (Num n) v true
    | RecVarUnderRefUnit : forall v,
        RecVarUnderRefPretype Unit v true
    | RecVarUnderRefProd : forall v taus,
        Forall (fun typ => RecVarUnderRefTyp typ v true) taus ->
        RecVarUnderRefPretype (ProdT taus) v true
    | RecVarUnderRefCoderef : forall ft v,
        RecVarUnderRefPretype (CoderefT ft) v true
    | RecVarUnderRefRec : forall qa v tau,
        RecVarUnderRefTyp tau (v + 1) true ->
        RecVarUnderRefPretype (Rec qa tau) v true
    | RecVarUnderRefPtr : forall l v,
        RecVarUnderRefPretype (PtrT l) v true
    | RecVarUnderRefExLoc : forall v tau,
        RecVarUnderRefTyp tau v true ->
        RecVarUnderRefPretype (ExLoc tau) v true
    | RecVarUnderRefOwn : forall l v,
        RecVarUnderRefPretype (OwnR l) v true.

  Lemma RecVarUnderRefPretypeProd_iff taus v :
    RecVarUnderRefPretype (ProdT taus) v true <->
    Forall (fun typ => RecVarUnderRefTyp typ v true) taus.
  Proof.
    induction taus; cbn; [split; inversion 1; subst; now constructor|].
    split; inversion 1; subst.
    - inv H1; constructor; auto.
    - constructor; auto.
  Qed.

  Lemma Forall_cons_iff {A} (P : A -> Prop) (x : A) xs :
    Forall P (x :: xs) <-> P x /\ Forall P xs.
  Proof. split; inversion 1; subst; constructor; auto. Qed.

  Fixpoint rec_var_under_ref_typ t v :=
    let 'QualT pt q := t in rec_var_under_ref_pretype pt v
  with rec_var_under_ref_pretype pt v :=
         match pt with
         | Num _ => true
         | TVar x => negb (Nat.eqb x v)
         | Unit => true
         | ProdT ts => forallb (fun t => rec_var_under_ref_typ t v) ts
         | CoderefT x => true
         | Rec _ t => rec_var_under_ref_typ t (v + 1)
         | PtrT _ => true
         | ExLoc t => rec_var_under_ref_typ t v
         | OwnR _ => true
         | CapT _ _ _ => true
         | RefT _ _ _ => true
         end.

  Fixpoint RecVarUnderRefTyp_spec t v {struct t} :
    RecVarUnderRefTyp t v true <-> rec_var_under_ref_typ t v = true
  with RecVarUnderRefPretype_spec pt v {struct pt} :
    RecVarUnderRefPretype pt v true <-> rec_var_under_ref_pretype pt v = true.
  Proof.
    - destruct t; cbn; rewrite <- RecVarUnderRefPretype_spec.
      split; [inversion 1; subst; assumption|constructor; assumption].
    - destruct pt; cbn; try (split; [reflexivity|intros[]]); try solve [constructor].
      + split; [inversion 1; subst; reflexivity|intros <-; constructor].
      + rewrite RecVarUnderRefPretypeProd_iff.
        induction l; [cbn; split; [reflexivity|constructor] |].
        cbn; rewrite Forall_cons_iff, Bool.andb_true_iff, IHl, RecVarUnderRefTyp_spec.
        reflexivity.
      + split; [inversion 1; subst|constructor]; apply RecVarUnderRefTyp_spec; assumption.
      + split; [inversion 1; subst|constructor]; apply RecVarUnderRefTyp_spec; assumption.
  Qed.


  (* adds variables and constraints and shifts appropriately *)
  Definition add_constraint (C : Function_Ctx) (quant : KindVar) : Function_Ctx :=
    match quant with
    | LOC => subst_ext (weak SLoc) (update_location_ctx (location C + 1) C)
    | QUAL qs qs' => subst_ext (weak SQual) (update_qual_ctx ((qs, qs') :: qual C) C)
    | SIZE sz sz' => subst_ext (weak SSize) (update_size_ctx ((sz, sz') :: size C) C)
    | TYPE sz q hc => subst_ext (weak SPretype) (update_type_ctx ((sz, q, hc) :: type C) C)
    end.

  Definition add_constraints (C : Function_Ctx) (quants : list KindVar) : Function_Ctx :=
    fold_left add_constraint quants C.
  
Section Validity.

  Inductive QualValid : list (list Qual * list Qual) -> Qual -> Prop :=
  | QualConstValid :
      forall C q const, q = QualConst const -> QualValid C q
  | QualVarValid :
      forall C q var constraint,
        q = QualVar var ->
        nth_error C var = Some constraint ->
        QualValid C q.

  Inductive LocValid : nat -> Loc -> Prop :=
  | LocPValid :
      forall C l ptr qual, l = LocP ptr qual -> LocValid C l
  | LocVValid :
      forall C l var,
        l = LocV var ->
        var < C ->
        LocValid C l.

  Inductive SizeValid : list (list Size * list Size) -> Size -> Prop :=
  | SizeConstValid :
      forall C sz n,
        sz = SizeConst n -> SizeValid C sz
  | SizePlusValid :
      forall C sz1 sz2 sz3,
        sz1 = SizePlus sz2 sz3 ->
        SizeValid C sz2 ->
        SizeValid C sz3 ->
        SizeValid C sz1
  | SizeVarValid :
      forall C sz var constraint,
        sz = SizeVar var ->
        nth_error C var = Some constraint ->
        SizeValid C sz.

  Definition KindVarValid C kv :=
    match kv with
    | LOC => True
    | QUAL qs1 qs2 => Forall (QualValid (qual C)) qs1 /\ Forall (QualValid (qual C)) qs2
    | SIZE ss1 ss2 => Forall (SizeValid (size C)) ss1 /\ Forall (SizeValid (size C)) ss2
    | TYPE s q hc => SizeValid (size C) s /\ QualValid (qual C) q
    end.
  
  Inductive KindVarsValid : Function_Ctx -> list KindVar -> Prop :=
  | KindVarsValidNil : forall C, KindVarsValid C []
  | KindVarsValidCons : forall C kv kvs, KindVarValid C kv ->
                                 KindVarsValid (add_constraint C kv) kvs ->
                                 KindVarsValid C (kv :: kvs).
  
  Inductive TypeValid: Function_Ctx -> Typ -> Prop :=
  | TNumValid :
      forall C q n,
        QualValid (qual C) q ->
        TypeValid C (QualT (Num n) q)
  | TVarValid :
      forall C q a qa sz hc,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        nth_error (type C) a = Some (sz, qa, hc) ->
        QualLeq (qual C) qa q = Some true ->
        TypeValid C (QualT (TVar a) q)
  | TRecValid :
      forall C qa q qp p sz,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        QualValid (qual C) qp ->
        QualLeq (qual C) qp q = Some true ->
        QualLeq (qual C) qp qa = Some true ->
        RecVarUnderRefPretype p 0 true ->
        sizeOfPretype (type C) (Rec qa (QualT p qp)) = Some sz ->
        SizeValid (size C) sz ->
        TypeValid (subst_ext (weak SPretype) (update_type_ctx ((sz, qa, Heapable) :: type C) C)) (QualT p qp) ->
        TypeValid C (QualT (Rec qa (QualT p qp)) q)
  | TUnitValid :
      forall C q,
        QualValid (qual C) q ->
        TypeValid C (QualT Unit q)
  | TProdValid :
      forall C taus q,
        QualValid (qual C) q ->
        Forall (fun '(QualT _ qi) => QualLeq (qual C) qi q = Some true) taus ->
        Forall (TypeValid C) taus ->
        TypeValid C (QualT (ProdT taus) q)
  | TCoderefValid :
      forall C ft q,
        QualValid (qual C) q ->
        FunTypeValid C ft ->
        TypeValid C (QualT (CoderefT ft) q)
  | TPtrValid :
      forall C q l,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        TypeValid C (QualT (PtrT l) q)
  | TCapValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid C psi ->
        TypeValid C (QualT (CapT c l psi) q)
  | TRefValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid C psi ->
        TypeValid C (QualT (RefT c l psi) q)
  | TExLocValid :
      forall C qp p q,
        QualValid (qual C) q ->
        QualLeq (qual C) qp q = Some true ->
        TypeValid (subst_ext (weak SLoc) (update_location_ctx (location C + 1) C)) (QualT p qp) ->
        TypeValid C (QualT (ExLoc (QualT p qp)) q)
  | TOwnValid :
      forall C l q,
        QualValid (qual C) q ->
        QualLeq (qual C) Linear q  = Some true ->
        LocValid (location C) l ->
        TypeValid C (QualT (OwnR l) q)
  with HeapTypeValid : Function_Ctx -> HeapType -> Prop :=
  | VariantValid :
      forall taus C,
        Forall (TypeValid C) taus ->
        HeapTypeValid C (VariantType taus)
  | StructValid :
      forall tausizes C,
        Forall (fun tausize => exists sz, sizeOfType (type C) (fst tausize) = Some sz /\
                                          SizeValid (size C) (snd tausize) /\
                                          SizeValid (size C) sz /\
                                          TypeValid C (fst tausize) /\
                                          SizeLeq (size C) sz (snd tausize) = Some true) tausizes ->
        HeapTypeValid C (StructType tausizes)
  | ArrayValid :
      forall qp p C,
        TypeValid C (QualT p qp) ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeValid C (ArrayType (QualT p qp))
  | ExValid :
      forall C qα sz tau,
         SizeValid (size C) sz ->
         QualValid (qual C) qα ->
        TypeValid (subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: type C) C)) tau ->
        HeapTypeValid C (Ex sz qα tau)
  with ArrowTypeValid : Function_Ctx -> ArrowType -> Prop :=
  | ArrowValid :
      forall C ts1 ts2,
        Forall (TypeValid C) ts1 ->
        Forall (TypeValid C) ts2 ->
        ArrowTypeValid C (Arrow ts1 ts2)
  with FunTypeValid : Function_Ctx -> FunType -> Prop :=
  | FunTValid :
      forall C quants arr,
        KindVarsValid C quants ->
        ArrowTypeValid (add_constraints C quants) arr ->
        FunTypeValid C (FunT quants arr).

  Inductive HeapTypeUnrestricted: Function_Ctx -> HeapType -> Prop :=
  | VariantUnrestricted :
      forall taus C,
        Forall (fun '(QualT _ q) => QualValid (qual C) q /\ QualLeq (qual C) q Unrestricted = Some true) taus ->
        HeapTypeUnrestricted C (VariantType taus)
  | StructUnrestricted :
      forall tausizes C,
        Forall (fun '(QualT _ q, _) => QualValid (qual C) q /\ QualLeq (qual C) q Unrestricted = Some true) tausizes ->
        HeapTypeUnrestricted C (StructType tausizes)
  | ArrayUnrestricted :
      forall qp p C,
        QualValid (qual C) qp ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeUnrestricted C (ArrayType (QualT p qp))
  | ExUnrestricted :
      forall C qα sz p q,
        QualValid (qual C) qα ->
        QualValid (qual C) q ->
        QualLeq (qual C) qα Unrestricted = Some true ->
        QualLeq (qual C) q Unrestricted = Some true ->
        HeapTypeUnrestricted C (Ex sz qα (QualT p q)).

  Section ValidInd.
    
  Context (TypeValid': Function_Ctx -> Typ -> Prop)
          (HeapTypeValid' : Function_Ctx -> HeapType -> Prop)
          (ArrowTypeValid' : Function_Ctx -> ArrowType -> Prop)
          (FunTypeValid' : Function_Ctx -> FunType -> Prop).

  Context
    (TNumValid :
      forall C q n,
        QualValid (qual C) q ->
        TypeValid' C (QualT (Num n) q))
    (TVarValid :
      forall C q a qa sz hc,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        nth_error (type C) a = Some (sz, qa, hc) ->
        QualLeq (qual C) qa q = Some true ->
        TypeValid' C (QualT (TVar a) q))
    (TRecValid :
      forall C qa q qp p sz,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        QualValid (qual C) qp ->
        QualLeq (qual C) qp q = Some true ->
        QualLeq (qual C) qp qa = Some true ->
        RecVarUnderRefPretype p 0 true ->
        sizeOfPretype (type C) (Rec qa (QualT p qp)) = Some sz ->
        SizeValid (size C) sz ->
        TypeValid' (subst_ext (weak SPretype) (update_type_ctx ((sz, qa, Heapable) :: type C) C)) (QualT p qp) ->
        TypeValid' C (QualT (Rec qa (QualT p qp)) q))
    (TUnitValid :
      forall C q,
        QualValid (qual C) q ->
        TypeValid' C (QualT Unit q))
    (TProdValid :
      forall C taus q,
        QualValid (qual C) q ->
        Forall (fun '(QualT _ qi) => QualLeq (qual C) qi q = Some true) taus ->
        Forall (TypeValid' C) taus ->
        TypeValid' C (QualT (ProdT taus) q))
    (TCoderefValid :
      forall C ft q,
        QualValid (qual C) q ->
        FunTypeValid' C ft ->
        TypeValid' C (QualT (CoderefT ft) q))
    (TPtrValid :
      forall C q l,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        TypeValid' C (QualT (PtrT l) q))
    (TCapValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid' C psi ->
        TypeValid' C (QualT (CapT c l psi) q))
    (TRefValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid' C psi ->
        TypeValid' C (QualT (RefT c l psi) q))
    (TExLocValid :
      forall C qp p q,
        QualValid (qual C) q ->
        QualLeq (qual C) qp q = Some true ->
        TypeValid' (subst_ext (weak SLoc) (update_location_ctx (location C + 1) C)) (QualT p qp) ->
        TypeValid' C (QualT (ExLoc (QualT p qp)) q))
    (TOwnValid :
      forall C l q,
        QualValid (qual C) q ->
        QualLeq (qual C) Linear q  = Some true ->
        LocValid (location C) l ->
        TypeValid' C (QualT (OwnR l) q))
    (VariantValid :
      forall taus C,
        Forall (TypeValid' C) taus ->
        HeapTypeValid' C (VariantType taus))
    (StructValid :
      forall tausizes C,
        Forall (fun tausize => exists sz, sizeOfType (type C) (fst tausize) = Some sz /\
                                          SizeValid (size C) (snd tausize) /\
                                          SizeValid (size C) sz /\
                                          TypeValid' C (fst tausize) /\
                                          SizeLeq (size C) sz (snd tausize) = Some true) tausizes ->
        HeapTypeValid' C (StructType tausizes))
    (ArrayValid :
      forall qp p C,
        TypeValid' C (QualT p qp) ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeValid' C (ArrayType (QualT p qp)))
    (ExValid :
       forall C qα sz tau,
         SizeValid (size C) sz ->
         QualValid (qual C) qα ->
        TypeValid' (subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: type C) C)) tau ->
        HeapTypeValid' C (Ex sz qα tau))
    (ArrowValid :
      forall C ts1 ts2,
        Forall (TypeValid' C) ts1 ->
        Forall (TypeValid' C) ts2 ->
        ArrowTypeValid' C (Arrow ts1 ts2))
    (FunTValid :
      forall C quants arr,
        KindVarsValid C quants ->
        ArrowTypeValid' (add_constraints C quants) arr ->
        FunTypeValid' C (FunT quants arr)).

  (* To temporarily hide IHs from eauto *)
  Inductive Trivial : Prop := MkTrivial.
  Definition sealed (P : Prop) : Prop := Trivial -> P.
  (* These proofs need to compute so termination checker can see unseal (seal IH_proof) = IH_proof *)
  Definition seal (P : Prop) : P -> sealed P := fun prf => fun _ => prf.
  Definition unseal (P : Prop) : sealed P -> P := fun prf => prf MkTrivial.
  (* Test hiding from eauto *)
  Goal False -> False. Proof. intros H; clear - H. apply seal in H. Fail solve [eauto]. Abort.
  (* Test unseal ∘ seal = id *)
  Goal forall (P : Prop) (prf : P), unseal P (seal P prf) = prf. Proof. intros. exact eq_refl. Abort.
  
  Fixpoint TypeValid_ind' F t (Hty : TypeValid F t) {struct Hty} : TypeValid' F t
  with HeapTypeValid_ind' F t (Hty : HeapTypeValid F t) {struct Hty} : HeapTypeValid' F t
  with ArrowTypeValid_ind' F t (Hty : ArrowTypeValid F t) {struct Hty} : ArrowTypeValid' F t
  with FunTypeValid_ind' F t (Hty : FunTypeValid F t) {struct Hty} : FunTypeValid' F t.
  Proof.
    all: destruct Hty;
        try (apply seal in TypeValid_ind';
             apply seal in HeapTypeValid_ind';
             apply seal in ArrowTypeValid_ind';
             apply seal in FunTypeValid_ind';
             multimatch goal with
             (* Somewhere in the context, there's a suitable assumption *)
             | H : forall _, _ |- _ =>
               solve [
                 (* Apply it and solve side conditions by using the stuff that was inside Hty *)
                 eapply H; eauto;
                 (* Now, it should be safe to apply induction hypothesis where needed *)
                 apply unseal in TypeValid_ind';
                 apply unseal in HeapTypeValid_ind';
                 apply unseal in ArrowTypeValid_ind';
                 apply unseal in FunTypeValid_ind';
                 eauto;
                 (* Some cases have recursive occurrences of
                    the typing judgment under Forall. Solve by nested induction *)
                 match goal with
                 | H : Forall _ ?taus |- Forall _ ?taus =>
                   clear - H TypeValid_ind' HeapTypeValid_ind'
                             ArrowTypeValid_ind' FunTypeValid_ind';
                   induction H; constructor; try solve [eauto|firstorder eauto]
                 end]
             end).
  Qed.
  
  Corollary TypesValid_ind' :
    (forall F t, TypeValid F t -> TypeValid' F t) /\
    (forall F t, HeapTypeValid F t -> HeapTypeValid' F t) /\
    (forall F t, ArrowTypeValid F t -> ArrowTypeValid' F t) /\
    (forall F t, FunTypeValid F t -> FunTypeValid' F t).
  Proof.
    repeat split; intros; [apply TypeValid_ind'|apply HeapTypeValid_ind'|apply ArrowTypeValid_ind'|apply FunTypeValid_ind']; auto.
  Qed.

  Scheme TypeValid_mind := Induction for TypeValid Sort Prop
    with HeapTypeValid_mind := Induction for HeapTypeValid Sort Prop
    with ArrowTypeValid_mind := Induction for ArrowTypeValid Sort Prop
    with FunTypeValid_mind := Induction for FunTypeValid Sort Prop.

  End ValidInd.
  
End Validity.


Definition EmptyArrow tau : ArrowType := Arrow [] [tau].

Definition EmptyRes tau : ArrowType := Arrow [tau] [].


Section Typing.

  Definition NumLen (n : NumType) :=
    match n with
    | Int _ i32 | Float f32 => 2 ^ 32
    | Int _ i64 | Float f64 => 2 ^ 64
    end.

  Definition TypQualLeq (C : Function_Ctx) (t : Typ) (q : Qual) :=
    match t with
    | QualT _ q' => QualLeq (qual C) q' q
    end.

  Fixpoint NoCapsTyp (F : list HeapableConstant) (tau : Typ) : bool :=
    match tau with
      | QualT p _ => NoCapsPretype F p
    end
  with NoCapsPretype (F : list HeapableConstant) (pt : Pretype) : bool :=
    match pt with
      | Num _
      | Unit
      | CoderefT _
      | PtrT _
      | OwnR _
      | RefT _ _ _ => true
      | TVar n =>
        (match List.nth_error F n with
         | None => false
         | Some Heapable => true
         | Some NotHeapable => false
        end)
      | ProdT taus => forallb (NoCapsTyp F) taus
      | Rec _ tau => NoCapsTyp (Heapable :: F) tau
      | ExLoc tau => NoCapsTyp F tau
      | CapT _ _ _ => false
    end.

  Definition NoCapsHeapType (F : list HeapableConstant) (ht : HeapType) : bool :=
    match ht with
    | VariantType taus => forallb (NoCapsTyp F) taus
    | StructType tis => forallb (NoCapsTyp F) (fst (split tis))
    | ArrayType tau => NoCapsTyp F tau
    | Ex s q tau => NoCapsTyp (Heapable :: F) tau
    end.
    
  Inductive InstIndValid : Function_Ctx -> FunType -> Index -> Prop :=
  | LocIndValid :
      forall l F rest tf,
        LocValid (location F) l ->
        InstIndValid F (FunT (LOC :: rest) tf) (LocI l)
  | TypeInstValid : 
      forall pt sz' sz q F rest tf hc,
        sizeOfPretype (type F) pt = Some sz' ->
        SizeValid (size F) sz' ->
        SizeValid (size F) sz ->
        SizeLeq (size F) sz' sz = Some true ->
        TypeValid F (QualT pt q) ->
        (hc = Heapable -> NoCapsPretype (heapable F) pt = true) ->
        InstIndValid F (FunT ((TYPE sz q hc) :: rest) tf) (PretypeI pt)
  | QualInstValid :
      forall q qs1 qs2 F rest tf,
        QualValid (qual F) q ->
        Forall (fun q' => QualValid (qual F) q' /\ QualLeq (qual F) q' q = Some true) qs1 ->
        Forall (fun q' => QualValid (qual F) q' /\ QualLeq (qual F) q q' = Some true) qs2 ->
        InstIndValid F (FunT ((QUAL qs1 qs2) :: rest) tf) (QualI q)
  | SizeInstValid :
      forall sz szs1 szs2 F rest tf,
        SizeValid (size F) sz ->
        Forall (fun sz' => SizeValid (size F) sz' /\ SizeLeq (size F) sz' sz = Some true) szs1 ->
        Forall (fun sz' => SizeValid (size F) sz' /\ SizeLeq (size F) sz sz' = Some true) szs2 ->
        InstIndValid F (FunT ((SIZE szs1 szs2) :: rest) tf) (SizeI sz).

  Definition InstInd (ft : FunType) (i : Index) : option FunType :=
    match ft, i with
    | FunT (LOC :: rest) tf, (LocI l) => Some (subst_ext (ext subst.SLoc l id) (FunT rest tf))
    | FunT ((QUAL q1s q2s) :: rest) tf, (QualI q) => Some (subst_ext (ext subst.SQual q id) (FunT rest tf))
    | FunT ((SIZE sz1s sz2s) :: rest) tf, (SizeI s) => Some (subst_ext (ext subst.SSize s id) (FunT rest tf))
    | FunT ((TYPE size q hc) :: rest) tf, (PretypeI p) => Some (subst_ext (ext subst.SPretype p id) (FunT rest tf))
    | _, _ => None
    end.

  Inductive InstIndsValid : Function_Ctx -> FunType -> list Index -> Prop :=
  | InstIndsValidNil :
      forall F chi,
        InstIndsValid F chi []
  | InstIndsValidCons :
      forall F chi chi' f r,
        InstIndValid F chi f ->
        InstInd chi f = Some chi' ->
        InstIndsValid F chi' r ->
        InstIndsValid F chi (f :: r).

  Definition InstInds (ft : FunType) (is : list Index) : option FunType :=
    fold_left (fun ft i =>
                 match ft with
                 | None => None
                 | Some ft => InstInd ft i
              end) is (Some ft).

  
  Fixpoint ReplaceAtIdx {A : Type} (i : nat) (l : list A) (new : A) : option (list A * A) :=
    match i, l with
      | 0, old :: rest => Some (new :: rest, old)
      | n, first :: rest =>
        bind (ReplaceAtIdx (i - 1) rest new) (fun '(rest, old) => Some (first :: rest, old))
      | _, _ => None
    end.

  
  Inductive HasTypeValue : StoreTyping -> Function_Ctx -> Value -> Typ -> Prop :=
  | NumConstTyp :
      forall S C nt i q,
        M.is_empty (LinTyp S) = true ->
        i <= NumLen nt ->
        TypeValid C (QualT (Num nt) q) ->
        HasTypeValue S C (NumConst nt i)  (QualT (Num nt) q)
  | UnitTyp :
      forall S C q,
        M.is_empty (LinTyp S) = true ->
        TypeValid C (QualT Unit q) ->
        HasTypeValue S C Tt  (QualT Unit q)
  | ProdTyp :
      forall S Ss C vs taus q,
        SplitStoreTypings Ss S ->
        Forall3 (fun S' v t => HasTypeValue S' C v t) Ss vs taus ->
        TypeValid C (QualT (ProdT taus) q) ->
        HasTypeValue S C (Prod vs) (QualT (ProdT taus) q)
  | PtrTyp :
      forall S C l q,
        M.is_empty (LinTyp S) = true ->
        TypeValid C (QualT (PtrT l) q) ->
        HasTypeValue S C (PtrV l)  (QualT (PtrT l) q)
  | RefTypUnr :
      forall S C rw l ht q,
        M.is_empty (LinTyp S) = true ->
        get_heaptype l (UnrTyp S) = Some ht ->
        (* Values which depend on S having LinTyp / UnrTyp can not be from surface instructions, so must be valid under empty function context *)
        QualLeq [] q Unrestricted = Some true ->
        TypeValid empty_Function_Ctx (QualT (RefT rw (LocP l Unrestricted) ht) q) ->
        HasTypeValue S C (Ref (LocP l Unrestricted)) (QualT (RefT rw (LocP l Unrestricted) ht) q)
  | RefTypLin :
      forall S C rw l ht q,
        map_util.eq_map (LinTyp S)
                        (M.add (N.succ_pos l) ht (M.empty HeapType)) ->
        (* Values which depend on S having LinTyp / UnrTyp can not be from surface instructions, so must be valid under empty function context *)
        QualLeq [] Linear q = Some true ->
        TypeValid empty_Function_Ctx (QualT (RefT rw (LocP l Linear) ht) q) ->
        HasTypeValue S C (Ref (LocP l Linear)) (QualT (RefT rw (LocP l Linear) ht) q)
  | CapTypLin :
      forall S C rw l ht q,
        map_util.eq_map (LinTyp S)
                        (M.add (N.succ_pos l) ht (M.empty HeapType)) ->
        (* Values which depend on S having LinTyp / UnrTyp can not be from surface instructions, so must be valid under empty function context *)
        QualLeq [] Linear q = Some true ->
        TypeValid empty_Function_Ctx (QualT (CapT rw (LocP l Linear) ht) q) ->
        HasTypeValue S C Cap (QualT (CapT rw (LocP l Linear) ht) q)
  | OwnTyp : forall S C l q,
        M.is_empty (LinTyp S) = true ->
        TypeValid C (QualT (OwnR l) q) ->
        HasTypeValue S C Own (QualT (OwnR l) q)
  | RecTyp :
      forall S C v qa q q' pt,
        let r := Rec qa (QualT pt q) in
        TypeValid C (QualT r q') ->
        HasTypeValue S C v (QualT (subst (Kind:=Kind) SPretype (ext SPretype r id) pt) q) ->
        HasTypeValue S C (Fold v) (QualT r q')
  | MempackTyp :
      forall S C l v t q,
        LocValid (location C) l ->
        TypeValid C (QualT (ExLoc t) q) ->
        HasTypeValue S C v (subst_ext (Kind:=Kind) (ext SLoc l id) t) ->
        HasTypeValue S C (Mempack l v)  (QualT (ExLoc t) q)
  | CoderefTyp :
      forall S C modi tabi is ft C' ftinst q,
        M.is_empty (LinTyp S) = true ->
        nth_error (InstTyp S) modi = Some C' ->
        nth_error (table C') tabi = Some ft ->
        InstInds ft is = Some ftinst ->
        (* Coderef values can not be from surface instructions, so must be valid under empty function context *)
        InstIndsValid empty_Function_Ctx ft is ->
        TypeValid empty_Function_Ctx (QualT (CoderefT ftinst) q) ->
        HasTypeValue S C (Coderef modi tabi is) (QualT (CoderefT ftinst) q).

  Section HasTypeValueInd.

    Context
      (P : StoreTyping -> Function_Ctx -> Value -> Typ -> Prop)
      (HNumConstTyp :
          forall S C nt i q,
            M.is_empty (LinTyp S) = true ->
            i <= NumLen nt ->
            TypeValid C (QualT (Num nt) q) ->
            P S C (NumConst nt i)  (QualT (Num nt) q))
      (HUnitTyp :
          forall S C q,
            M.is_empty (LinTyp S) = true ->
            TypeValid C (QualT Unit q) ->
            P S C Tt  (QualT Unit q))
      (HProdTyp :
          forall S Ss C vs taus q,
            SplitStoreTypings Ss S ->
            Forall3 (fun S' v t => P S' C v t)
                    Ss vs taus ->
            TypeValid C (QualT (ProdT taus) q) ->
            P S C (Prod vs) (QualT (ProdT taus) q))
      (HPtrTyp :
          forall S C l q,
            M.is_empty (LinTyp S) = true ->
            TypeValid C (QualT (PtrT l) q) ->
            P S C (PtrV l)  (QualT (PtrT l) q))
      (HRefTypUnr :
          forall S C rw l ht q,
            M.is_empty (LinTyp S) = true ->
            get_heaptype l (UnrTyp S) = Some ht ->
            QualLeq [] q Unrestricted = Some true ->
            TypeValid empty_Function_Ctx (QualT (RefT rw (LocP l Unrestricted) ht) q) ->
            P S C (Ref (LocP l Unrestricted)) (QualT (RefT rw (LocP l Unrestricted) ht) q))
      (HRefTypLin :
          forall S C rw l ht q,
            map_util.eq_map (LinTyp S)
                            (M.add (N.succ_pos l) ht (M.empty HeapType)) ->
            QualLeq [] Linear q = Some true ->
            TypeValid empty_Function_Ctx (QualT (RefT rw (LocP l Linear) ht) q) ->
            P S C (Ref (LocP l Linear)) (QualT (RefT rw (LocP l Linear) ht) q))
      (HCapTypLin :
          forall S C rw l ht q,
            map_util.eq_map (LinTyp S)
                            (M.add (N.succ_pos l) ht (M.empty HeapType)) ->
            QualLeq [] Linear q = Some true ->
            TypeValid empty_Function_Ctx (QualT (CapT rw (LocP l Linear) ht) q) ->
            P S C Cap (QualT (CapT rw (LocP l Linear) ht) q))
      (HOwnTyp : forall S C l q,
            M.is_empty (LinTyp S) = true ->
            TypeValid C (QualT (OwnR l) q) ->
            P S C Own (QualT (OwnR l) q))
      (HRecTyp :
         forall S C v qa q q' pt,
           let r := Rec qa (QualT pt q) in
           TypeValid C (QualT r q') ->
           P S C v (QualT (subst (Kind:=Kind) SPretype (ext SPretype r id) pt) q) ->
           P S C (Fold v) (QualT r q'))
      (HMempackTyp :
          forall S C l v t q,
            LocValid (location C) l ->
            TypeValid C (QualT (ExLoc t) q) ->
            P S C v (subst_ext (Kind:=Kind) (ext SLoc l id) t) ->
            P S C (Mempack l v)  (QualT (ExLoc t) q))
      (CoderefTyp :
          forall S C modi tabi is ft C' ftinst q,
            M.is_empty (LinTyp S) = true ->
            nth_error (InstTyp S) modi = Some C' ->
            nth_error (table C') tabi = Some ft ->
            InstInds ft is = Some ftinst ->
            InstIndsValid empty_Function_Ctx ft is ->
            TypeValid empty_Function_Ctx (QualT (CoderefT ftinst) q) ->
            P S C (Coderef modi tabi is) (QualT (CoderefT ftinst) q))
    .

    Fixpoint HasTypeValue_ind' S C v t (Hty : HasTypeValue S C v t) {struct Hty} :
      P S C v t.
    Proof.
      destruct Hty.
      - apply HNumConstTyp; assumption.
      - apply HUnitTyp; assumption.
      - eapply HProdTyp; try eassumption.
        clear - H0 HasTypeValue_ind'.
        induction H0; [constructor|constructor].
        + apply HasTypeValue_ind'; assumption.
        + apply IHForall3.
      - apply HPtrTyp; assumption.
      - apply HRefTypUnr; assumption.
      - apply HRefTypLin; assumption.
      - apply HCapTypLin; assumption.
      - apply HOwnTyp; assumption.
      - apply HRecTyp; try assumption. apply HasTypeValue_ind'. assumption.
      - apply HMempackTyp; try assumption. apply HasTypeValue_ind'; assumption.
      - eapply CoderefTyp; eassumption.
    Qed.

  End HasTypeValueInd.

  Inductive HasHeapType : StoreTyping -> Function_Ctx -> HeapValue -> HeapType -> Prop :=
  | VariantHT :
      forall S F taus i v tau,
        Forall (TypeValid F) taus ->
        nth_error taus i = Some tau ->
        HasTypeValue S F v tau  ->
        HasHeapType S F (Variant i v) (VariantType taus)
  | StructHT :
      forall S Ss F vs tauis taus is,
        SplitStoreTypings Ss S ->
        Forall3 (fun S' v t => HasTypeValue S' F v t) Ss vs taus ->
        (taus, is) = split tauis ->
        Forall (fun sz => SizeValid (size F) sz) is /\
        Forall2 (fun tau sz => exists sztau, sizeOfType (type F) tau  = Some sztau /\
                                             SizeValid (size F) sztau /\
                                             SizeLeq (size F) sztau sz = Some true) taus is ->
        HasHeapType S F (Struct vs) (StructType tauis)
  | ArrayHT :
      forall S Ss F i vs p q,
        TypeValid F (QualT p q)->
        QualLeq (qual F) q Unrestricted = Some true ->
        SplitStoreTypings Ss S ->
        length vs = i ->
        Forall2 (fun S v => HasTypeValue S F v (QualT p q)) Ss vs ->
        HasHeapType S F (Array i vs) (ArrayType (QualT p q))
  | ExHT :
      forall S F pt qα tau v i sz,
        sizeOfPretype (type F) pt = Some sz ->
        SizeLeq (size F) sz i = Some true ->
        SizeValid (size F) sz ->
        SizeValid (size F) i ->
        NoCapsPretype (heapable F) pt = true ->
        TypeValid F (QualT pt qα) ->
        TypeValid (subst_ext (weak subst.SPretype) (update_type_ctx ((i, qα, Heapable) :: (type F)) F)) tau ->
        HasTypeValue S F v (subst_ext (Kind:=Kind) (ext SPretype pt id) tau) ->
        HasHeapType S F (Pack pt v (Ex i qα tau)) (Ex i qα tau).


  Definition uint32T : Pretype := Num (Int U i32).
  Definition uint64T : Pretype := Num (Int U i64).
  Definition int32T : Pretype := Num (Int U i32).
  Definition int64T : Pretype := Num (Int U i64).
  Definition float32T : Pretype := Num (Float f32).
  Definition float64T : Pretype := Num (Float f64).

  (* Note: This is O(n^2) where n the lize of local_type. *)
  Fixpoint add_local_effects (L : Local_Ctx) (tl : LocalEffect) : Local_Ctx :=
    match tl with
    | [] => L
    | (i, tau) :: tl =>
      match get_localtype i L with
      | Some (_tau, size) => add_local_effects (set_localtype i tau size L) tl
      | None => add_local_effects L tl
      end
    end.

  Definition empty_LinTyp (s : StoreTyping) :=
    match s with
    | Build_StoreTyping i l u => Build_StoreTyping i (M.empty _) u
    end.


  (* This rule ignores sizes -- HasTypeConf ensures the L has the types passed in Local block *)
  Inductive HasTypeLocals : Function_Ctx -> list StoreTyping -> list Value -> list (Typ * Size) -> Prop :=
  | LocalCtxTyp :
      forall F Ss lvs L,
        Forall3 (fun S' v '(tau, sz) =>
                   HasTypeValue S' F v tau (* XXX this should imply that size val <= sizeOfType t *)
                   (* sizeOfType (type F) tau  Some st -- XXX maybe check size compat *))
                Ss lvs L ->
        HasTypeLocals F Ss lvs L.

  Inductive RoomForStrongUpdates : N -> HeapType -> Prop :=
  | NoUpdateTypeFits : forall l ht,
      match ht with
      | VariantType _ => True
      | ArrayType _ => True
      | Ex _ _ _ => True
      | StructType _ => False
      end ->
      RoomForStrongUpdates l ht
  | StructTypeFits : forall tauszs taus szs l,
      split tauszs = (taus, szs) ->
      ((fold_left (fun acc sz =>
                    match (size_to_nat sz) with
                    | None => acc
                    | Some n => acc + (N.of_nat n)
                    end) szs (N.of_nat 0)) <= l)%N ->
      RoomForStrongUpdates l (StructType tauszs).

  Definition LCEffEqual
             C (L : Local_Ctx) (L' : Local_Ctx) :=
    Forall2
      (fun '(t0, sz0) '(t1, sz1) =>
         t0 = t1 /\
         SizeLeq C sz0 sz1 = Some true /\
         SizeLeq C sz1 sz0 = Some true)
      L L'.

  Lemma LCEffEqual_refl : forall C L,
      LCEffEqual C L L.
  Proof.
    intros.
    unfold LCEffEqual.
    apply forall2_nth_error_inv; auto.
    intros.
    destruct_prs.
    match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inversion H'; subst
    end.
    split; auto.
    split; apply SizeLeq_Refl.
  Qed.

  Lemma LCEffEqual_sym : forall {C L L'},
      LCEffEqual C L L' ->
      LCEffEqual C L' L.
  Proof.
    unfold LCEffEqual.
    intros.
    apply forall2_nth_error_inv; [ | apply eq_sym; eapply Forall2_length; eauto ].
    intros.
    destruct_prs.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.
    intros; simpl in *; destructAll; eauto.
  Qed.

  Lemma LCEffEqual_trans : forall {C L1 L2 L3},
      LCEffEqual C L1 L2 ->
      LCEffEqual C L2 L3 ->
      LCEffEqual C L1 L3.
  Proof.
    unfold LCEffEqual.
    intros.
    apply forall2_nth_error_inv; [ | eapply eq_trans; eapply Forall2_length; eauto ].
    intros.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : exists v, nth_error L2 IDX = Some v);
      [ remember (nth_error L2 IDX) as obj | ]
    end.
    { generalize (eq_sym Heqobj); case obj; intros; eauto.
      rewrite nth_error_None in *.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : IDX < length L1);
        [ apply nth_error_Some; rewrite H';
          intro H''; inversion H'' | ];
        let H1 := fresh "H" in
        assert (H1 : length L1 = length L2);
        [ eapply Forall2_length; eauto | ];
        rewrite H1 in H0;
        let H2 := fresh "H" in
        assert (H2 : IDX < IDX);
        [ eapply Nat.lt_le_trans; eauto | ];
        apply Nat.lt_irrefl in H2; exfalso; auto
      end. }
    destructAll.
    destruct_prs.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H''' : Forall2 _ ?L2 ?L3,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _,
        H'''' : nth_error ?L3 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'');
      specialize (forall2_nth_error _ _ _ _ _ _ H''' H'' H'''')
    end.
    intros; simpl in *; destructAll; subst.
    split; auto.
    split; eapply SizeLeq_Trans; eauto.
  Qed.

  Definition LocalCtxValid (F : Function_Ctx) (L : Local_Ctx) :=
    Forall (fun '(tau, sz) => TypeValid F tau /\ SizeValid (size F) sz) L.

  Inductive HasTypeInstruction :
    StoreTyping -> Module_Ctx -> Function_Ctx ->
    Local_Ctx -> list Instruction -> ArrowType -> Local_Ctx -> Prop :=
  | ValTyp :
      forall S C F L v t,
        HasTypeValue S F v t ->
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Val v] (EmptyArrow t) L
  (* TODO: numerical instructions *)
  | UnreachableType :
      forall S C F L taus1 taus2 tl,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Unreachable] (Arrow taus1 taus2) (add_local_effects L tl)
  | NopTyp :
      forall S C F L,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Nop] (Arrow [] []) L
  | DropTyp :
      forall S C F L q pt,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) q Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Drop] (Arrow [QualT pt q] []) L
  | SelectTyp :
      forall S C F L q1 pt q2,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) q1 Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT pt q1) ->
        TypeValid F (QualT uint32T q2) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Select]
                           (Arrow [QualT pt q1; QualT pt q1; QualT uint32T q2] [QualT pt q1]) L
  | BlockTyp :
      forall S C F L tl taus1 taus2 es L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Block tf tl es] tf L'
  | LoopTyp :
      forall S C F L taus1 taus2 es,
        let tf := Arrow taus1 taus2 in
        (* let L' := add_local_effects L tl in *)
        let F1 := update_label_ctx ((taus1, L) :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es tf L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Loop tf es] tf L
  | ITETyp :
      forall S C F L tl taus1 taus2 es1 es2 q L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es1 tf L' ->
        HasTypeInstruction S C F2 L es2 tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        TypeValid F (QualT uint32T q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ITE tf tl es1 es2] (Arrow (taus1 ++ [QualT uint32T q]) taus2) L'
  | BrTyp :
      forall S C F L i taus1 taus1' taus2 tl,
        M.is_empty (LinTyp S) = true ->
        nth_error (label F) i = Some (taus1', L) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->                
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Br i] (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl)
  | Br_ifTyp :
      forall S C F L i taus q,
        M.is_empty (LinTyp S) = true ->
        nth_error (label F) i = Some (taus, L) ->
        (* Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus ->                 *)
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        TypeValid F (QualT uint32T q) ->
        Forall (TypeValid F) taus ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Br_if i] (Arrow (taus ++ [QualT uint32T q]) taus) L
  | Br_tableTyp :
      forall S C F L is taus1 taus1' taus2 tl q k,
        M.is_empty (LinTyp S) = true ->
        Forall (fun i => nth_error (label F) i = Some (taus1', L)) (is ++ [k]) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->
        let i := list_max (is ++ [k]) in
        (forall j, j <= i ->
                   exists q, nth_error_plist  (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1' ++ [QualT uint32T q]) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Br_table is k] (Arrow (taus1 ++ taus1' ++ [QualT uint32T q]) taus2) (add_local_effects L tl)
  | RetTyp :
      forall S C F L taus1 taus1' taus2 tl,
        M.is_empty (LinTyp S) = true ->
        ret F = Some taus1' ->

        Forall (fun '(QualT pt q, sz) => QualLeq (qual F) q Unrestricted = Some true) L ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->

        Forall_plist (fun q => QualValid (qual F) q /\ QualLeq (qual F) q Unrestricted = Some true) (linear F) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Ret] (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl)
  | GetlocalTyp :
      forall S C F L i q pt sz b taunew,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pt q, sz) ->
        (b = true -> QualLeq (qual F) q Unrestricted = Some true) ->
        (b = false -> QualLeq (qual F) Linear q = Some true) ->
        (b = true -> taunew = QualT pt q) ->
        (b = false -> taunew = QualT Unit Unrestricted) ->
        QualValid (qual F) q ->
        LocalCtxValid F L ->
        TypeValid F taunew ->
        TypeValid F (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Get_local i q] (EmptyArrow (QualT pt q)) (set_localtype i taunew sz L)
  | SetlocalTyp :
      forall S C F L i q pt sz tau tausz,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pt q, sz) ->
        QualLeq (qual F) q Unrestricted = Some true ->
        Some tausz = sizeOfType (type F) tau ->
        SizeValid (size F) tausz ->
        SizeLeq (size F) tausz sz = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Set_local i] (EmptyRes tau) (set_localtype i tau sz L)
  | TeelocalTyp :
      forall S C F L i qo qn pto ptn sz szn,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pto qo, sz) ->
        QualLeq (qual F) qo Unrestricted = Some true ->
        QualLeq (qual F) qn Unrestricted = Some true ->
        let tau := (QualT ptn qn) in
        Some szn = sizeOfType (type F) tau ->
        SizeValid (size F) szn ->
        SizeLeq (size F) szn sz = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Tee_local i] (Arrow [tau] [tau]) (set_localtype i tau sz L)
  | GetglobalTyp :
      forall S C F L i mut pt,
        M.is_empty (LinTyp S) = true ->
        nth_error (global C) i = Some (GT mut pt) ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx (QualT pt Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Get_global i] (EmptyArrow (QualT pt Unrestricted)) L
  | SetglobalTyp :
      forall S C F L i q pt,
        M.is_empty (LinTyp S) = true ->
        nth_error (global C) i = Some (GT true pt) ->
        QualLeq (qual F) q Unrestricted = Some true ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Set_global i] (EmptyRes (QualT pt q)) L
  | CoderefTTyp :
      forall S C F L i chi,
        M.is_empty (LinTyp S) = true ->
        nth_error (table C) i = Some chi ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx (QualT (CoderefT chi) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [CoderefI i] (EmptyArrow (QualT (CoderefT chi) Unrestricted)) L
  | InstITyp : (* typeset *)
      forall S C F L is chi chi' q,
        M.is_empty (LinTyp S) = true ->
        InstInds chi is = Some chi' ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CoderefT chi) q) ->
        TypeValid F (QualT (CoderefT chi') q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Inst is] (Arrow [QualT (CoderefT chi) q] [QualT (CoderefT chi') q]) L
  | Call_indirectTyp : (* typeset *)
      forall S C F L taus1 taus2 q,
        M.is_empty (LinTyp S) = true ->
        let chi := FunT [] (Arrow taus1 taus2) in
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (CoderefT chi) q) ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Call_indirect] (Arrow (taus1 ++ [QualT (CoderefT chi) q]) taus2) L
  | Call : (* typeset *)
      forall S C F L i is chi taus1 taus2,
        M.is_empty (LinTyp S) = true ->
        nth_error (func C) i = Some chi ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        FunTypeValid empty_Function_Ctx chi ->
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Call i is] (Arrow taus1 taus2) L
  | RecFoldType : (* typeset *)
      forall S C F L qa q pt,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT pt q in
        let rec := Rec qa tau in
        LocalCtxValid F L ->
        TypeValid F (QualT rec q) ->
        TypeValid F (subst_ext (Kind:=Kind) (ext SPretype rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [RecFold rec]
                           (Arrow [subst_ext (Kind:=Kind) (ext SPretype rec id) tau] [QualT rec q]) L
  | RecUnfoldType : (* typeset *)
      forall S C F L qa q pt,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT pt q in (* TODO fixme *)
        let rec := Rec qa tau in
        LocalCtxValid F L ->
        TypeValid F (QualT rec q) ->
        TypeValid F (subst_ext (Kind:=Kind) (ext SPretype rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [RecUnfold]
                           (Arrow [QualT rec q] [subst_ext (Kind:=Kind) (ext SPretype rec id) tau]) L
  | GroupType : (* typeset *)
      forall S C F L i taus qseq,
        M.is_empty (LinTyp S) = true ->
        length taus = i ->
        LocalCtxValid F L ->
        TypeValid F (QualT (ProdT taus) qseq) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Group i qseq]
                           (Arrow taus [QualT (ProdT taus) qseq]) L
  | UngroupTyp : (* typeset *)
      forall S C F L taus qseq,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (ProdT taus) qseq) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Ungroup] (Arrow [QualT (ProdT taus) qseq] taus) L
  | CapSplitTyp :
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CapT W l ht) Linear) ->
        TypeValid F (QualT (OwnR l) Linear) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [CapSplit]
                           (Arrow [QualT (CapT W l ht) Linear]
                                  [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear])
                           L
  | CapJoinTyp :
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CapT W l ht) Linear) ->
        TypeValid F (QualT (OwnR l) Linear) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [CapJoin]
                           (Arrow [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear]
                                  [QualT (CapT W l ht) Linear])
                           L
  | RefDemoteTyp : (* typeset *)
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l ht) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [RefDemote]
                           (Arrow [QualT (RefT W l ht) Unrestricted]
                                  [QualT (RefT R l ht) Unrestricted])
                           L
  | MemPackTyp :
      forall S C F L pt taurho q l,
        M.is_empty (LinTyp S) = true ->
        let tau := (QualT pt q) in
        (subst_ext (Kind:=Kind) (ext SLoc l id)taurho) = tau ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (QualT (ExLoc taurho) q) ->
        LocValid (location F) l ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [MemPack l]
                           (Arrow [tau]
                                  [QualT (ExLoc taurho) q])
                           L
  | MemUnpackTyp :
      forall S C F L taus1 taus2 qrho taurho es tl L'',
        let tf := Arrow taus1 taus2 in
        let tf' := Arrow (taus1 ++ [QualT (ExLoc taurho) qrho]) taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SLoc) (update_location_ctx (location F  + 1) F2) in
        HasTypeInstruction
          S C F3
          (subst_ext (weak SLoc) L)
          es
          (Arrow (subst_ext (weak SLoc) taus1 ++ [taurho]) (subst_ext (weak SLoc) taus2))
          (subst_ext (weak SLoc) L') ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (ExLoc taurho) qrho) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [MemUnpack tf tl es] tf' L'
  | StructMallocTyp : (* typeset *)
      forall S C F L szs q taus,
        M.is_empty (LinTyp S) = true ->
        Forall2 (fun tau sz => exists tausz, sizeOfType (type F) tau = Some tausz /\
                   SizeValid (size F) tausz /\
                   SizeLeq (size F) tausz sz = Some true) taus szs ->
        Forall (SizeValid (size F)) szs ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        QualValid (qual F) q ->
        let psi := StructType (combine (subst_ext (Kind:=Kind) (weak SLoc) taus) szs) in
        LocalCtxValid F L ->
        Forall (TypeValid F) taus ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [StructMalloc szs q]
                           (Arrow taus
                                  [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L
  | StructFreeTyp : (* typeset *)
      forall S C F L q tauszs l,
        M.is_empty (LinTyp S) = true ->
        QualValid (qual F) q ->
        QualLeq (qual F) Linear q = Some true ->
        Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) tauszs ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (StructType tauszs)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [StructFree] (Arrow [QualT (RefT W l (StructType tauszs)) q] []) L
  | StructGetTyp : 
      forall S C F L n taus szs tau q l cap pv qv,
        M.is_empty (LinTyp S) = true ->
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        nth_error taus n = Some tau ->
        tau = (QualT pv qv) ->
        QualLeq (qual F) qv Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l psi) q) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [StructGet n]
                           (Arrow [QualT (RefT cap l psi) q]
                                  [QualT (RefT cap l psi) q; tau])
                           L
  | StructSetTyp :
      forall S C F L taus szs tau q taus' l n q_old p_old sz tau_sz,
        M.is_empty (LinTyp S) = true ->
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau = Some (taus', (QualT p_old q_old)) ->
        QualLeq (qual F) q_old Unrestricted = Some true ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz = Some true ->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (QualLeq (qual F) Linear q = Some true \/
         tau = QualT p_old q_old) ->
        let psi' := StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l psi) q) ->
        TypeValid F (QualT (RefT W l psi') q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [StructSet n]
                           (Arrow [QualT (RefT W l psi) q; tau]
                                  [QualT (RefT W l psi') q])
                           L
  | StructSwapTyp :
      forall S C F L taus szs tau q taus' l n tau_old sz tau_sz,
        M.is_empty (LinTyp S) = true ->
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau = Some (taus', tau_old) ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz = Some true->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (QualLeq (qual F) Linear q = Some true \/
         tau = tau_old) ->
        let psi' := StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l psi) q) ->
        TypeValid F (QualT (RefT W l psi') q) ->
        TypeValid F tau_old ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [StructSwap n]
                           (Arrow [QualT (RefT W l psi) q; tau]
                                  [QualT (RefT W l psi') q; tau_old])
                           L
  | VariantMallocTyp : (* typeset *)
      forall S C F L n taus q p qp,
        M.is_empty (LinTyp S) = true ->
        Forall (TypeValid F) taus ->
        QualValid (qual F) q ->
        let tau := (QualT p qp) in
        nth_error taus n = Some tau ->
        QualLeq (qual F) qp q = Some true ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        let psi := VariantType (subst_ext (Kind:=Kind) (weak SLoc) taus) in
        LocalCtxValid F L ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [VariantMalloc n taus q]
                           (Arrow [tau]
                                  [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L
  | VariantCaseTypUnr : 
      forall S C F L taus1 taus2 tausv q' q qv cap l es tl L'',
        M.is_empty (LinTyp S) = true -> (* Because es are surface *)
        QualLeq (qual F) qv q' = Some true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->

        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        Forall2 (fun es tau => HasTypeInstruction S C F2 L es (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        Forall (fun '(QualT p q) => QualLeq (qual F) q Unrestricted = Some true) tausv ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT cap l (VariantType tausv)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [VariantCase q (VariantType tausv) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT cap l (VariantType tausv)) qv])
                                  ([QualT (RefT cap l (VariantType tausv)) qv] ++ taus2))
                           L'
  | VariantCaseTypLin : (* typeset *)
      forall S C F L taus1 taus2 tausv q qv l es tl L'',
        M.is_empty (LinTyp S) = true -> (* Because es are surface *)
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        Forall2 (fun es tau => HasTypeInstruction S C F2 L es (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (RefT W l (VariantType tausv)) qv) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [VariantCase q (VariantType tausv) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT W l (VariantType tausv)) qv]) taus2)
                           L'
  | ArrayMallocTyp : (* typeset *)
      forall S C F L p qp q qi,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT p qp in
        let psi := (ArrayType (subst_ext (Kind:=Kind) (weak SLoc) tau)) in
        QualValid (qual F) q ->
        NoCapsTyp (heapable F) tau = true ->
        QualLeq (qual F) qp Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ArrayMalloc q] (Arrow [tau; QualT uint32T qi]
                                                      [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L
  | ArrayGetTyp : (* typeset *)
      forall S C F L cap l p q qi,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l (ArrayType tau)) q) ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ArrayGet] (Arrow [QualT (RefT cap l (ArrayType tau)) q; QualT uint32T qi]
                                                 [QualT (RefT cap l (ArrayType tau)) q; tau])
                           L
  | ArraySetTyp : (* typeset *)
      forall S C F L l p q qi,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        NoCapsTyp (heapable F) tau = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (ArrayType tau)) q) ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ArraySet] (Arrow [QualT (RefT W l (ArrayType tau)) q; QualT uint32T qi; tau]
                                                 [QualT (RefT W l (ArrayType tau)) q])
                           L
  | ArrayFreeTyp : (* typeset *)
      forall S C F L q p l,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        QualValid (qual F) q ->
        QualLeq (qual F) Linear q = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (ArrayType tau)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ArrayFree] (Arrow [QualT (RefT W l (ArrayType tau)) q] []) L
  | ExistPackTyp : (* typeset *)
      forall S C F L hp hq p sz q szp,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) hq q = Some true ->
        QualValid (qual F) q ->
        sizeOfPretype (type F) p = Some szp ->
        SizeLeq (size F) szp sz = Some true ->
        SizeValid (size F) szp ->
        SizeValid (size F) sz ->
        TypeValid F (QualT p q) ->
        TypeValid (subst_ext (weak subst.SPretype) (update_type_ctx ((sz, q, Heapable) :: (type F)) F)) (QualT hp hq) ->
        NoCapsPretype (heapable F) p = true ->
        NoCapsTyp (heapable (update_type_ctx ((sz, q, Heapable) :: (type F)) F)) (QualT hp hq) = true ->
        let tau := subst_ext (Kind:=Kind) (ext SPretype p id) (QualT hp hq) in
        let psi := Ex sz q (subst_ext (Kind:=Kind) (weak SLoc) (QualT hp hq)) in
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ExistPack p (Ex sz q (QualT hp hq)) q]
                           (Arrow [tau] [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L
  | ExistUnpackTypUnr : (* typeset *)
      forall S C F L cap taus1 taus2 tau q' q qv l es tl sz qα q_ex p_ex L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        let F3 := subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstruction S C F3 (subst_ext (weak SPretype) L) es
                           (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                  (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') ->
        tau = QualT p_ex q_ex ->
        QualLeq (qual F) q_ex Unrestricted = Some true ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualLeq (qual F) qv q' = Some true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        M.is_empty (LinTyp S) = true ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT cap l (Ex sz qα tau)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ExistUnpack q (Ex sz qα tau) tf tl es] (* TODO fixme *)
                           (Arrow (taus1 ++ [QualT (RefT cap l (Ex sz qα tau)) qv])
                                  ([QualT (RefT cap l (Ex sz qα tau)) qv] ++ taus2 ))
                           L'
  | ExistUnpackTypLin : (* typeset *)
      forall S C F L taus1 taus2 tau q qv l es tl sz qα L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SPretype)  (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstruction S C F3 (subst_ext (weak SPretype) L) es
                           (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                  (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        M.is_empty (LinTyp S) = true ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT W l (Ex sz qα tau)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [ExistUnpack q (Ex sz qα tau) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT W l (Ex sz qα tau)) qv]) taus2)
                           L'
  | RefSplitTyp : (* typeset *)
      forall S C F L cap l ht q,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) Linear q = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l ht) q) ->
        TypeValid F (QualT (CapT cap l ht) q) ->
        TypeValid F (QualT (PtrT l) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [RefSplit] (Arrow [QualT (RefT cap l ht) q]
                                                 [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted]) L
  | RefJoinTyp : (* typeset *)
      forall S C F L cap l ht q,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l ht) q) ->
        TypeValid F (QualT (CapT cap l ht) q) ->
        TypeValid F (QualT (PtrT l) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [RefJoin] (Arrow [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted]
                                                [QualT (RefT cap l ht) q]) L
  | QualifyTyp :  (* typeset *)
      forall S C F L qold qnew p,
        M.is_empty (LinTyp S) = true ->
        (forall cap l ht, p <> CapT cap l ht) ->
        (forall cap l ht, p <> RefT cap l ht) ->
        (forall n, p <> TVar n) ->
        QualLeq (qual F) qold qnew = Some true ->
        QualValid (qual F) qnew ->
        LocalCtxValid F L ->
        TypeValid F (QualT p qold) ->
        TypeValid F (QualT p qnew) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Qualify qnew] (Arrow [QualT p qold] [QualT p qnew]) L
  (* Admin instrs *)
  | TrapTyp :  (* typeset *)
      forall S C F L tau1 tau2 tl,
        LocalCtxValid F L ->
        Forall (TypeValid F) tau1 ->
        Forall (TypeValid F) tau2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Trap] (Arrow tau1 tau2) (add_local_effects L tl)
  | CallAdmTyp :  (* typeset *)
      forall S C F L chi taus1 taus2 cl is,
        HasTypeClosure S cl chi ->
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [CallAdm cl is] (Arrow taus1 taus2) L
  | LabelTyp :  (* typeset *)
      forall S C F L L' i tau1 tau2 es1 es2,
        let tf := Arrow [] tau2 in
        length tau1 = i ->
        HasTypeInstruction S C (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) (update_label_ctx ((tau1, L') :: label F) F)) L es2 tf L' ->
        HasTypeInstruction (empty_LinTyp S) C F L' es1 (Arrow tau1 tau2) L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Label i tf es1 es2] tf L'
  | LocalTyp :  (* typeset *)
      forall S C F L reti modi vlocs slocs es tf taus,
      tf = Arrow [] taus ->
      length taus = reti ->
      HasTypeConf S (Some taus) modi vlocs (map SizeConst slocs) es taus ->
      LocalCtxValid F L ->
      Forall (TypeValid F) taus ->
      QualValid (qual F) (get_hd (linear F)) ->
      HasTypeInstruction S C F L [Local reti modi vlocs slocs es] tf L
  | MallocTyp :
      forall S C F L hv ht q sz (H : size_closed sz),
        (* This isn't a surface instruction, so it should always be well-typed under an empty function context *)
        HasHeapType S empty_Function_Ctx hv ht ->
        RoomForStrongUpdates (N.of_nat (to_size sz H)) ht ->
        QualValid [] q ->
        NoCapsHeapType [] ht = true ->
        LocalCtxValid F L ->
        TypeValid empty_Function_Ctx (QualT (ExLoc (QualT (RefT W (LocV 0) (subst_ext (Kind:=Kind) (weak SLoc) ht)) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Malloc sz hv q] (Arrow [] [QualT (ExLoc (QualT (RefT W (LocV 0) (subst_ext (Kind:=Kind) (weak SLoc) ht)) q)) q]) L
  | FreeTyp : 
      forall S C F L l ht q,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) Linear q = Some true ->
        QualValid (qual F) q ->
        HeapTypeUnrestricted F ht ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l ht) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [Free] (EmptyRes (QualT (RefT W l ht) q)) L
(* Connectives *)
  | EmptyTyp :  (* typeset *)
      forall S C F L ts,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        Forall (TypeValid F) ts ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstruction S C F L [] (Arrow ts ts) L
  | ConsTyp :  (* typeset *)
      forall S S1 S2 C F L1 L2 L3 es e tau1 tau2 tau3,
        SplitStoreTypings [S1; S2] S ->
        HasTypeInstruction S1 C F L1 es (Arrow tau1 tau2) L2 ->
        HasTypeInstruction S2 C F L2 [e] (Arrow tau2 tau3) L3 ->
        HasTypeInstruction S C F L1 (es ++ [e]) (Arrow tau1 tau3) L3
  | FrameTyp : 
      forall S C F L L' qf es taus taus1 taus2 Flin_hd,
        get_hd (linear F) = Flin_hd ->
        Forall (fun '(QualT pt q) => QualLeq (qual F) q qf = Some true) taus ->
        QualLeq (qual F) Flin_hd qf = Some true ->
        let F' := update_linear_ctx (set_hd qf (linear F)) F in
        HasTypeInstruction S C F' L es (Arrow taus1 taus2) L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        QualValid (qual F) qf ->
        Forall (TypeValid F) taus ->
        HasTypeInstruction S C F L es (Arrow (taus ++ taus1) (taus ++ taus2)) L'
  | ChangeBegLocalTyp :  (* typeset *)
      forall S C F L L1 es taus1 taus2 L',
        LocalCtxValid F L1 ->
        LCEffEqual (size F) L L1 ->
        HasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
        HasTypeInstruction S C F L1 es (Arrow taus1 taus2) L'
  | ChangeEndLocalTyp :  (* typeset *)
      forall S C F L es taus1 taus2 L' L1,
        LocalCtxValid F L1 ->
        LCEffEqual (size F) L' L1 ->
        HasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
        HasTypeInstruction S C F L es (Arrow taus1 taus2) L1
  with HasTypeClosure : StoreTyping -> Closure -> FunType -> Prop :=
  | CloTyp :
      forall S C i f ex chi,
        nth_error (InstTyp S) i = Some C ->
        HasTypeFunc S C f ex chi ->
        HasTypeClosure S (Clo i f) chi
  with HasTypeFunc : StoreTyping -> Module_Ctx -> Func -> list ex -> FunType -> Prop :=
  | FunTyp :
      forall S C L' taus1 taus2 sz1 sz cnstr tauszs es ex,
        let chi := FunT cnstr (Arrow taus1 taus2) in
        FunTypeValid empty_Function_Ctx chi ->
        length taus1 = length sz1 ->
        tauszs = combine taus1 sz1 ->
        let F_cnstr := add_constraints empty_Function_Ctx cnstr in
        Forall2 (fun tau sz => sizeOfType (type F_cnstr) tau = Some sz) taus1 sz1 ->
        let L := (tauszs ++ (map (fun s => (QualT Unit Unrestricted, s)) sz)) in
        let F := update_ret_ctx (Some taus2) F_cnstr in
        HasTypeInstruction S C F L es (Arrow [] taus2) L' ->
        Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) L' ->
        Forall (fun sz => SizeValid (size F) sz) sz ->
        HasTypeFunc S C (Fun ex chi sz es) ex chi
  with HasTypeConf : StoreTyping -> option (list Typ) ->
                     nat ->
                     list Value ->
                     list Size ->
                     list Instruction ->
                     list Typ -> Prop :=
  | ConfTypFull :
      forall S S_stack Ss taus i es C L L' locvs locsz maybe_ret,
        
        
        maybe_ret = Some taus \/ maybe_ret = None ->
        nth_error (InstTyp S) i = Some C ->

        SplitStoreTypings (S_stack (* store typing for instructions *) :: Ss (* store typings for stack *)) S ->

        HasTypeLocals empty_Function_Ctx Ss locvs L ->
        (let (taus, szs) := split L in szs = locsz) -> 

        let F := (update_ret_ctx maybe_ret empty_Function_Ctx) in
        
        HasTypeInstruction S_stack C F L es (Arrow [] taus) L' ->
        
        (* Everything local after typechecking the configurations must be unrestricted -- linear things must be consumed! *)
        Forall (fun '(QualT pt q, sz) => QualLeq (qual F) q Unrestricted = Some true) L' ->
        HasTypeConf S maybe_ret i locvs locsz es taus.

  (* These schemes aren't strong as can be because of recursive
     occurrences under Forall/Forall2/Forall3 *)
  Scheme HasTypeInstruction_mind := Induction for HasTypeInstruction Sort Prop
    with HasTypeClosure_mind := Induction for HasTypeClosure Sort Prop
    with HasTypeFunc_mind := Induction for HasTypeFunc Sort Prop
    with HasTypeConf_mind := Induction for HasTypeConf Sort Prop.
  
  Section HasType_Instruction_Closure_Func_Conf_mind'.

  Context
    (PHasTypeInstruction : StoreTyping -> Module_Ctx -> Function_Ctx -> Local_Ctx -> list Instruction -> ArrowType -> Local_Ctx -> Prop)
    (PHasTypeClosure : StoreTyping -> Closure -> FunType -> Prop)
    (PHasTypeFunc : StoreTyping -> Module_Ctx -> Func -> list ex -> FunType -> Prop)
    (PHasTypeConf : StoreTyping -> option (list Typ) ->
                    nat ->
                    list Value ->
                    list Size ->
                    list Instruction ->
                    list Typ -> Prop)
    (ValTyp :
      forall S C F L v t,
        HasTypeValue S F v t ->
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Val v] (EmptyArrow t) L)
    (UnreachableType :
      forall S C F L taus1 taus2 tl,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Unreachable] (Arrow taus1 taus2) (add_local_effects L tl))
    (NopTyp :
      forall S C F L,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Nop] (Arrow [] []) L)
    (DropTyp :
      forall S C F L q pt,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) q Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Drop] (Arrow [QualT pt q] []) L)
    (SelectTyp :
      forall S C F L q1 pt q2,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) q1 Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT pt q1) ->
        TypeValid F (QualT uint32T q2) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Select]
                           (Arrow [QualT pt q1; QualT pt q1; QualT uint32T q2] [QualT pt q1]) L)
    (BlockTyp :
      forall S C F L tl taus1 taus2 es L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es tf L' ->
        PHasTypeInstruction S C F2 L es tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Block tf tl es] tf L')
    (LoopTyp :
      forall S C F L taus1 taus2 es,
        let tf := Arrow taus1 taus2 in
        (* let L' := add_local_effects L tl in *)
        let F1 := update_label_ctx ((taus1, L) :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es tf L ->
        PHasTypeInstruction S C F2 L es tf L ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Loop tf es] tf L)
    (ITETyp :
      forall S C F L tl taus1 taus2 es1 es2 q L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstruction S C F2 L es1 tf L' ->
        PHasTypeInstruction S C F2 L es1 tf L' ->
        HasTypeInstruction S C F2 L es2 tf L' ->
        PHasTypeInstruction S C F2 L es2 tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        TypeValid F (QualT uint32T q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ITE tf tl es1 es2] (Arrow (taus1 ++ [QualT uint32T q]) taus2) L')
    (BrTyp :
      forall S C F L i taus1 taus1' taus2 tl,
        M.is_empty (LinTyp S) = true ->
        nth_error (label F) i = Some (taus1', L) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->                
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Br i] (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl))
    (Br_ifTyp :
      forall S C F L i taus q,
        M.is_empty (LinTyp S) = true ->
        nth_error (label F) i = Some (taus, L) ->
        (* Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus ->                 *)
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        TypeValid F (QualT uint32T q) ->
        Forall (TypeValid F) taus ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Br_if i] (Arrow (taus ++ [QualT uint32T q]) taus) L)
    (Br_tableTyp :
      forall S C F L is taus1 taus1' taus2 tl q k,
        M.is_empty (LinTyp S) = true ->
        Forall (fun i => nth_error (label F) i = Some (taus1', L)) (is ++ [k]) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->
        let i := list_max (is ++ [k]) in
        (forall j, j <= i ->
                   exists q, nth_error_plist  (linear F) j = Some q /\
                             QualValid (qual F) q /\
                             QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1' ++ [QualT uint32T q]) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Br_table is k] (Arrow (taus1 ++ taus1' ++ [QualT uint32T q]) taus2) (add_local_effects L tl))
    (RetTyp :
      forall S C F L taus1 taus1' taus2 tl,
        M.is_empty (LinTyp S) = true ->
        ret F = Some taus1' ->

        Forall (fun '(QualT pt q, sz) => QualLeq (qual F) q Unrestricted = Some true) L ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->

        Forall_plist (fun q => QualValid (qual F) q /\ QualLeq (qual F) q Unrestricted = Some true) (linear F) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Ret] (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl))
    (GetlocalTyp :
      forall S C F L i q b pt sz taunew,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pt q, sz) ->
        (b = true -> QualLeq (qual F) q Unrestricted = Some true) ->
        (b = false -> QualLeq (qual F) Linear q = Some true) ->
        (b = true -> taunew = QualT pt q) ->
        (b = false -> taunew = QualT Unit Unrestricted) ->
        (*
        match QualLeq (qual F) q Unrestricted, QualLeq (qual F) Unrestricted q with
        | None, _ | _, None | Some false, Some false => False
        | Some true, _ => taunew = QualT pt q
        | Some false, Some true => taunew = QualT Unit Unrestricted
        end -> *)
        QualValid (qual F) q ->
        LocalCtxValid F L ->
        TypeValid F taunew ->
        TypeValid F (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Get_local i q] (EmptyArrow (QualT pt q)) (set_localtype i taunew sz L))
    (SetlocalTyp :
      forall S C F L i q pt sz tau tausz,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pt q, sz) ->
        QualLeq (qual F) q Unrestricted = Some true ->
        Some tausz = sizeOfType (type F) tau ->
        SizeValid (size F) tausz ->
        SizeLeq (size F) tausz sz = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Set_local i] (EmptyRes tau) (set_localtype i tau sz L))
    (TeelocalTyp :
      forall S C F L i qo qn pto ptn sz szn,
        M.is_empty (LinTyp S) = true ->
        nth_error L i = Some (QualT pto qo, sz) ->
        QualLeq (qual F) qo Unrestricted = Some true ->
        QualLeq (qual F) qn Unrestricted = Some true ->
        let tau := (QualT ptn qn) in
        Some szn = sizeOfType (type F) tau ->
        SizeValid (size F) szn ->
        SizeLeq (size F) szn sz = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Tee_local i] (Arrow [tau] [tau]) (set_localtype i tau sz L))
    (GetglobalTyp :
      forall S C F L i mut pt,
        M.is_empty (LinTyp S) = true ->
        nth_error (global C) i = Some (GT mut pt) ->
        LocalCtxValid F L ->
        TypeValid empty_Function_Ctx (QualT pt Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Get_global i] (EmptyArrow (QualT pt Unrestricted)) L)
    (SetglobalTyp :
      forall S C F L i q pt,
        M.is_empty (LinTyp S) = true ->
        nth_error (global C) i = Some (GT true pt) ->
        QualLeq (qual F) q Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid empty_Function_Ctx (QualT pt q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Set_global i] (EmptyRes (QualT pt q)) L)
    (CoderefTTyp :
      forall S C F L i chi,
        M.is_empty (LinTyp S) = true ->
        nth_error (table C) i = Some chi ->
        LocalCtxValid F L ->
        TypeValid empty_Function_Ctx (QualT (CoderefT chi) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [CoderefI i] (EmptyArrow (QualT (CoderefT chi) Unrestricted)) L)
    (InstITyp :
      forall S C F L is chi chi' q,
        M.is_empty (LinTyp S) = true ->
        InstInds chi is = Some chi' ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CoderefT chi) q) ->
        TypeValid F (QualT (CoderefT chi') q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Inst is] (Arrow [QualT (CoderefT chi) q] [QualT (CoderefT chi') q]) L)
    (Call_indirectTyp :
      forall S C F L taus1 taus2 q,
        M.is_empty (LinTyp S) = true ->
        let chi := FunT [] (Arrow taus1 taus2) in
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (CoderefT chi) q) ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Call_indirect] (Arrow (taus1 ++ [QualT (CoderefT chi) q]) taus2) L)
    (Call :
      forall S C F L i is chi taus1 taus2,
        M.is_empty (LinTyp S) = true ->
        nth_error (func C) i = Some chi ->
        FunTypeValid empty_Function_Ctx chi ->
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [term.Call i is] (Arrow taus1 taus2) L)
    (RecFoldType :
      forall S C F L qa q pt,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT pt q in
        let rec := Rec qa tau in
        LocalCtxValid F L ->
        TypeValid F (QualT rec q) ->
        TypeValid F (subst_ext (Kind:=Kind) (ext SPretype rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [RecFold rec]
                            (Arrow [subst_ext (Kind:=Kind) (ext SPretype rec id) tau] [QualT rec q]) L)
    (RecUnfoldType :
      forall S C F L qa q pt,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT pt q in
        let rec := Rec qa tau in
        LocalCtxValid F L ->
        TypeValid F (QualT rec q) ->
        TypeValid F (subst_ext (Kind:=Kind) (ext SPretype rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [RecUnfold]
                           (Arrow [QualT rec q] [subst_ext (Kind:=Kind) (ext SPretype rec id)tau]) L)
    (GroupType :
      forall S C F L i taus qseq,
        M.is_empty (LinTyp S) = true ->
        length taus = i ->
        LocalCtxValid F L ->
        TypeValid F (QualT (ProdT taus) qseq) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Group i qseq]
                           (Arrow taus [QualT (ProdT taus) qseq]) L)
    (UngroupTyp :
      forall S C F L taus qseq,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (ProdT taus) qseq) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Ungroup] (Arrow [QualT (ProdT taus) qseq] taus) L)
    (CapSplitTyp :
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CapT W l ht) Linear) ->
        TypeValid F (QualT (OwnR l) Linear) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [CapSplit]
                           (Arrow [QualT (CapT W l ht) Linear]
                                  [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear])
                           L)
    (CapJoinTyp :
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (CapT W l ht) Linear) ->
        TypeValid F (QualT (OwnR l) Linear) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [CapJoin]
                           (Arrow [QualT (CapT R l ht) Linear; QualT (OwnR l) Linear]
                                  [QualT (CapT W l ht) Linear])
                           L)
    (RefDemoteTyp :
      forall S C F L l ht,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l ht) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [RefDemote]
                           (Arrow [QualT (RefT W l ht) Unrestricted]
                                  [QualT (RefT R l ht) Unrestricted])
                           L)
    (MemPackTyp :
      forall S C F L pt taurho q l,
        M.is_empty (LinTyp S) = true ->
        let tau := (QualT pt q) in
        (subst_ext (Kind:=Kind) (ext SLoc l id) taurho) = tau ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (QualT (ExLoc taurho) q) ->
        LocValid (location F) l ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [MemPack l]
                           (Arrow [tau]
                                  [QualT (ExLoc taurho) q])
                           L)
    (MemUnpackTyp :
      forall S C F L taus1 taus2 qrho taurho es tl L'',
        let tf := Arrow taus1 taus2 in
        let tf' := Arrow (taus1 ++ [QualT (ExLoc taurho) qrho]) taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SLoc) (update_location_ctx (location F + 1) F2) in
        HasTypeInstruction
          S C F3
          (subst_ext (weak SLoc) L)
          es
          (Arrow (subst_ext (weak SLoc) taus1 ++ [taurho]) (subst_ext (weak SLoc) taus2))
          (subst_ext (weak SLoc) L') ->
        PHasTypeInstruction
          S C F3
          (subst_ext (weak SLoc) L)
          es
          (Arrow (subst_ext (weak SLoc) taus1 ++ [taurho]) (subst_ext (weak SLoc) taus2))
          (subst_ext (weak SLoc) L') ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (ExLoc taurho) qrho) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [MemUnpack tf tl es] tf' L')
    
    (StructMallocTyp :
      forall S C F L szs q taus,
        M.is_empty (LinTyp S) = true ->
        Forall2 (fun tau sz => exists tausz, sizeOfType (type F) tau = Some tausz /\
                   SizeValid (size F) tausz /\
                   SizeLeq (size F) tausz sz = Some true) taus szs ->
        Forall (SizeValid (size F)) szs ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        QualValid (qual F) q ->
        let psi := StructType (combine (subst_ext (Kind:=Kind) (weak SLoc) taus) szs) in
        LocalCtxValid F L ->
        Forall (TypeValid F) taus ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [StructMalloc szs q]
                           (Arrow taus
                                  [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L)
    (StructFreeTyp :
      forall S C F L q tauszs l,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) Linear q = Some true ->
        QualValid (qual F) q ->
        Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) tauszs ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (StructType tauszs)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [StructFree] (Arrow [QualT (RefT W l (StructType tauszs)) q] []) L)
    (StructGetTyp :
      forall S C F L n taus szs tau q l cap pv qv,
        M.is_empty (LinTyp S) = true ->
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        nth_error taus n = Some tau ->
        tau = (QualT pv qv) ->
        QualLeq (qual F) qv Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l psi) q) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [StructGet n]
                           (Arrow [QualT (RefT cap l psi) q]
                                  [QualT (RefT cap l psi) q; tau])
                           L)
    (StructSetTyp :
      forall S C F L taus szs tau q taus' l n q_old p_old sz tau_sz,
        M.is_empty (LinTyp S) = true ->
        let psi :=
          StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau =
          Some (taus', QualT p_old q_old) ->
        QualLeq (qual F) q_old Unrestricted =
          Some true ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz = Some true ->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (QualLeq (qual F) Linear q = Some true \/
        tau = QualT p_old q_old) ->
        let psi' :=
            StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l psi) q) ->
        TypeValid F (QualT (RefT W l psi') q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [StructSet n]
                            (Arrow [QualT (RefT W l psi) q; tau]
                                   [QualT (RefT W l psi') q])
                           L)
    (StructSwapTyp :
      forall S C F L taus szs tau q taus' l n tau_old sz tau_sz,
        M.is_empty (LinTyp S) = true ->
        let psi :=
          StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau =
          Some (taus', tau_old) ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz =
          Some true ->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (QualLeq (qual F) Linear q = Some true \/
           tau = tau_old) ->
        let psi' :=
            StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l psi) q) ->
        TypeValid F (QualT (RefT W l psi') q) ->
        TypeValid F tau_old ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [StructSwap n]
                            (Arrow [QualT (RefT W l psi) q; tau]
                                   [QualT (RefT W l psi') q; tau_old])
                            L)
    (VariantMallocTyp :
      forall S C F L n taus q p qp,
        M.is_empty (LinTyp S) = true ->
        Forall (TypeValid F) taus ->
        QualValid (qual F) q ->
        let tau := (QualT p qp) in
        nth_error taus n = Some tau ->
        QualLeq (qual F) qp q = Some true ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        let psi := VariantType (subst_ext (Kind:=Kind) (weak SLoc) taus) in
        LocalCtxValid F L ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [VariantMalloc n taus q]
                           (Arrow [tau]
                                  [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L)
    (VariantCaseTypUnr :
      forall (S : StoreTyping) (C : Module_Ctx) (F : Function_Ctx) 
             (L : Local_Ctx) (taus1 taus2 tausv : list Typ) (q' q qv : Qual) 
             (cap : term.cap) (l : term.Loc) (es : list (list Instruction))
             (tl : LocalEffect) L'',
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->
        QualLeq (qual F) qv q' = Some true ->
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        Forall2
          (fun (es0 : list Instruction) (tau : Typ) =>
             HasTypeInstruction S C F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        Forall2
          (fun (es0 : list Instruction) (tau : Typ) =>
             PHasTypeInstruction S C F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        Forall (fun '(QualT _ q0) => QualLeq (qual F) q0 Unrestricted = Some true) tausv ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT cap l (VariantType tausv)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [VariantCase q (VariantType tausv) tf tl es]
                            (Arrow (taus1 ++ [QualT (RefT cap l (VariantType tausv)) qv])
                                   ([QualT (RefT cap l (VariantType tausv)) qv] ++ taus2))
                            L')
    (VariantCaseTypLin :
      forall S C F L taus1 taus2 tausv q qv l es tl L'',
        M.is_empty (LinTyp S) = true ->
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: label F) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        Forall2
          (fun (es0 : list Instruction) (tau : Typ) =>
             HasTypeInstruction S C F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        Forall2
          (fun (es0 : list Instruction) (tau : Typ) =>
             PHasTypeInstruction S C F2 L es0 (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (QualT (RefT W l (VariantType tausv)) qv) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [VariantCase q (VariantType tausv) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT W l (VariantType tausv)) qv]) taus2)
                           L')
    (ArrayMallocTyp :
      forall S C F L p qp q qi,
        M.is_empty (LinTyp S) = true ->
        let tau := QualT p qp in
        let psi := (ArrayType (subst_ext (Kind:=Kind) (weak SLoc) tau)) in
        QualValid (qual F) q ->
        NoCapsTyp (heapable F) tau = true ->
        QualLeq (qual F) qp Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ArrayMalloc q] (Arrow [tau; QualT uint32T qi]
                                                      [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L)
    (ArrayGetTyp :
      forall S C F L cap l p q qi,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l (ArrayType tau)) q) ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ArrayGet] (Arrow [QualT (RefT cap l (ArrayType tau)) q; QualT uint32T qi]
                                                 [QualT (RefT cap l (ArrayType tau)) q; tau])
                           L)
    (ArraySetTyp :
      forall S C F L l p q qi,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        NoCapsTyp (heapable F) tau = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (ArrayType tau)) q) ->
        TypeValid F (QualT uint32T qi) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ArraySet] (Arrow [QualT (RefT W l (ArrayType tau)) q; QualT uint32T qi; tau]
                                                 [QualT (RefT W l (ArrayType tau)) q])
                           L)
    (ArrayFreeTyp :
      forall S C F L q p l,
        let tau := QualT p Unrestricted in
        M.is_empty (LinTyp S) = true ->
        QualValid (qual F) q ->
        QualLeq (qual F) Linear q = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l (ArrayType tau)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ArrayFree] (Arrow [QualT (RefT W l (ArrayType tau)) q] []) L)
    (ExistPackTyp :
      forall S C F L hp hq p sz q szp,
       M.is_empty (LinTyp S) = true ->
       QualLeq (qual F) hq q = Some true ->
       QualValid (qual F) q ->
       sizeOfPretype (type F) p = Some szp ->
       SizeLeq (size F) szp sz = Some true ->
       SizeValid (size F) szp ->
       SizeValid (size F) sz ->
       TypeValid F (QualT p q) ->
       TypeValid (subst_ext (weak SPretype) (update_type_ctx ((sz, q, Heapable) :: type F) F)) (QualT hp hq) ->
       NoCapsPretype (heapable F) p = true ->
       NoCapsTyp (heapable (update_type_ctx ((sz, q, Heapable) :: (type F)) F)) (QualT hp hq) = true ->
       let tau :=
         debruijn.subst_ext (debruijn.ext subst.SPretype p debruijn.id) (QualT hp hq) in
       let psi := Ex sz q (debruijn.subst_ext (debruijn.weak subst.SLoc) (QualT hp hq)) in
       LocalCtxValid F L ->
       TypeValid F tau ->
       TypeValid F (QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q) ->
       QualValid (qual F) (get_hd (linear F)) ->
       PHasTypeInstruction S C F L [ExistPack p (Ex sz q (QualT hp hq)) q]
                           (Arrow [tau] [QualT (ExLoc (QualT (RefT W (LocV 0) psi) q)) q])
                           L)
    (ExistUnpackTypUnr :
      forall S C F L cap taus1 taus2 tau q' q qv l es tl sz qα q_ex p_ex L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        let F3 := subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstruction S C F3 (subst_ext (weak SPretype) L) es
                            (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                   (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') ->
        PHasTypeInstruction S C F3 (subst_ext (weak SPretype) L) es
                            (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                   (subst_ext (weak SPretype) taus2)) (subst_ext (weak SPretype) L') ->
        tau = QualT p_ex q_ex ->
        QualLeq (qual F) q_ex Unrestricted = Some true ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        QualLeq (qual F) qv q' = Some true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->
        M.is_empty (LinTyp S) = true ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT cap l (Ex sz qα tau)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ExistUnpack q (Ex sz qα tau) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT cap l (Ex sz qα tau)) qv])
                                  ([QualT (RefT cap l (Ex sz qα tau)) qv] ++ taus2))
                           L')
    (ExistUnpackTypLin :
      forall S C F L taus1 taus2 tau q qv l es tl sz qα L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SPretype) (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstruction S C F3 (subst_ext (weak SPretype) L)
                            es (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                      (subst_ext (weak SPretype) taus2))
                            (subst_ext (weak SPretype) L') ->
        PHasTypeInstruction S C F3 (subst_ext (weak SPretype) L)
                            es (Arrow (subst_ext (weak SPretype) taus1 ++ [tau])
                                      (subst_ext (weak SPretype) taus2))
                            (subst_ext (weak SPretype) L') ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        M.is_empty (LinTyp S) = true ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        TypeValid F (QualT (RefT W l (Ex sz qα tau)) qv) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [ExistUnpack q (Ex sz qα tau) tf tl es]
                           (Arrow (taus1 ++ [QualT (RefT W l (Ex sz qα tau)) qv]) taus2)
                           L')
    (RefSplitTyp :
      forall S C F L cap l ht q,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) Linear q = Some true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l ht) q) ->
        TypeValid F (QualT (CapT cap l ht) q) ->
        TypeValid F (QualT (PtrT l) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [RefSplit] (Arrow [QualT (RefT cap l ht) q]
                                                 [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted]) L)
    (RefJoinTyp :
      forall S C F L cap l ht q,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT cap l ht) q) ->
        TypeValid F (QualT (CapT cap l ht) q) ->
        TypeValid F (QualT (PtrT l) Unrestricted) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [RefJoin] (Arrow [QualT (CapT cap l ht) q; QualT (PtrT l) Unrestricted]
                                                [QualT (RefT cap l ht) q]) L)
    (QualifyTyp :
      forall S C F L qold qnew p,
        M.is_empty (LinTyp S) = true ->
        (forall cap l ht, p <> CapT cap l ht) ->
        (forall cap l ht, p <> RefT cap l ht) ->
        (forall n, p <> TVar n) ->
        QualLeq (qual F) qold qnew = Some true ->
        QualValid (qual F) qnew ->
        LocalCtxValid F L ->
        TypeValid F (QualT p qold) ->
        TypeValid F (QualT p qnew) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Qualify qnew] (Arrow [QualT p qold] [QualT p qnew]) L)
    (TrapTyp :
       forall S C F L tau1 tau2 tl,
         LocalCtxValid F L ->
         Forall (TypeValid F) tau1 ->
         Forall (TypeValid F) tau2 ->
         LocalCtxValid F (add_local_effects L tl) ->
         QualValid (qual F) (get_hd (linear F)) ->
         PHasTypeInstruction S C F L [Trap] (Arrow tau1 tau2) (add_local_effects L tl))
    (CallAdmTyp :
      forall S C F L chi taus1 taus2 cl is,
        HasTypeClosure S cl chi ->
        PHasTypeClosure S cl chi ->
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [CallAdm cl is] (Arrow taus1 taus2) L)
    (LabelTyp :
      forall S C F L L' i tau1 tau2 es1 es2,
        let tf := Arrow [] tau2 in
        length tau1 = i ->
        HasTypeInstruction S C (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) (update_label_ctx ((tau1, L') :: label F) F)) L es2 tf L' ->
        PHasTypeInstruction S C (update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) (update_label_ctx ((tau1, L') :: label F) F)) L es2 tf L' ->
        HasTypeInstruction (empty_LinTyp S) C F L' es1 (Arrow tau1 tau2) L' ->
        PHasTypeInstruction (empty_LinTyp S) C F L' es1 (Arrow tau1 tau2) L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Label i tf es1 es2] tf L')
    (LocalTyp :
      forall S C F L reti modi vlocs slocs es tf taus,
      tf = Arrow [] taus ->
      length taus = reti ->
      HasTypeConf S (Some taus) modi vlocs (map SizeConst slocs) es taus ->
      PHasTypeConf S (Some taus) modi vlocs (map SizeConst slocs) es taus ->
      LocalCtxValid F L ->
      Forall (TypeValid F) taus ->
      QualValid (qual F) (get_hd (linear F)) ->
      PHasTypeInstruction S C F L [Local reti modi vlocs slocs es] tf L)
    (MallocTyp :
      forall S C F L hv ht q sz H,
        HasHeapType S empty_Function_Ctx hv ht ->
        RoomForStrongUpdates (N.of_nat (to_size sz H)) ht ->
        QualValid [] q ->
        NoCapsHeapType [] ht = true ->
        LocalCtxValid F L ->
        TypeValid empty_Function_Ctx (QualT (ExLoc (QualT (RefT W (LocV 0) (subst_ext (Kind:=Kind) (weak SLoc) ht)) q)) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Malloc sz hv q] (Arrow [] [QualT (ExLoc (QualT (RefT W (LocV 0) (subst_ext (Kind:=Kind) (weak SLoc) ht)) q)) q]) L)
    (FreeTyp :
      forall S C F L l ht q,
        M.is_empty (LinTyp S) = true ->
        QualLeq (qual F) Linear q = Some true ->
        QualValid (qual F) q ->
        HeapTypeUnrestricted F ht ->
        LocalCtxValid F L ->
        TypeValid F (QualT (RefT W l ht) q) ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [Free] (EmptyRes (QualT (RefT W l ht) q)) L)
    (EmptyTyp :
      forall S C F L ts,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        Forall (TypeValid F) ts ->
        QualValid (qual F) (get_hd (linear F)) ->
        PHasTypeInstruction S C F L [] (Arrow ts ts) L)
    (ConsTyp :
      forall S S1 S2 C F L1 L2 L3 es e tau1 tau2 tau3,
        SplitStoreTypings [S1; S2] S ->
        HasTypeInstruction S1 C F L1 es (Arrow tau1 tau2) L2 ->
        PHasTypeInstruction S1 C F L1 es (Arrow tau1 tau2) L2 ->
        HasTypeInstruction S2 C F L2 [e] (Arrow tau2 tau3) L3 ->
        PHasTypeInstruction S2 C F L2 [e] (Arrow tau2 tau3) L3 ->
        PHasTypeInstruction S C F L1 (es ++ [e]) (Arrow tau1 tau3) L3)
    (FrameTyp :
      forall S C F L L' qf es taus taus1 taus2 Flin_hd,
        get_hd (linear F) = Flin_hd ->
        Forall (fun '(QualT pt q) => QualLeq (qual F) q qf = Some true) taus ->
        QualLeq (qual F) Flin_hd qf = Some true ->
        let F' := update_linear_ctx (set_hd qf (linear F)) F in
        HasTypeInstruction S C F' L es (Arrow taus1 taus2) L' ->
        PHasTypeInstruction S C F' L es (Arrow taus1 taus2) L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        QualValid (qual F) qf ->
        Forall (TypeValid F) taus ->
        PHasTypeInstruction S C F L es (Arrow (taus ++ taus1) (taus ++ taus2)) L')
    (ChangeBegLocalTyp :
       forall S C F L L1 es taus1 taus2 L',
         LocalCtxValid F L1 ->
         LCEffEqual (size F) L L1 ->
         HasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
         PHasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
         PHasTypeInstruction S C F L1 es (Arrow taus1 taus2) L')
    (ChangeEndLocalTyp :
       forall S C F L es taus1 taus2 L' L1,
         LocalCtxValid F L1 ->
         LCEffEqual (size F) L' L1 ->
         HasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
         PHasTypeInstruction S C F L es (Arrow taus1 taus2) L' ->
         PHasTypeInstruction S C F L es (Arrow taus1 taus2) L1)
    (CloTyp :
      forall S C i f ex chi,
        nth_error (InstTyp S) i = Some C ->
        HasTypeFunc S C f ex chi ->
        PHasTypeFunc S C f ex chi ->
        PHasTypeClosure S (Clo i f) chi)
    (FunTyp :
      forall S C L' taus1 taus2 sz1 sz cnstr tauszs es ex,
        let chi := FunT cnstr (Arrow taus1 taus2) in
        FunTypeValid empty_Function_Ctx chi ->
        length taus1 = length sz1 ->
        tauszs = combine taus1 sz1 ->
        let F_cnstr := add_constraints empty_Function_Ctx cnstr in
        Forall2 (fun tau sz => sizeOfType (type F_cnstr) tau = Some sz) taus1 sz1 ->
        let L := (tauszs ++ (map (fun s => (QualT Unit Unrestricted, s)) sz)) in
        let F := update_ret_ctx (Some taus2) F_cnstr in
        HasTypeInstruction S C F L es (Arrow [] taus2) L' ->
        PHasTypeInstruction S C F L es (Arrow [] taus2) L' ->
        Forall (fun '(QualT _ q, _) => QualLeq (qual F) q Unrestricted = Some true) L' ->
        Forall (fun sz => SizeValid (size F) sz) sz ->
        PHasTypeFunc S C (Fun ex chi sz es) ex chi)
    (ConfTypFull :
       forall S S_stack Ss taus i es C L L' locvs locsz maybe_ret,
        (maybe_ret = Some taus \/ maybe_ret = None) ->
        nth_error (InstTyp S) i = Some C ->

        SplitStoreTypings (S_stack (* store typing for instructions *) :: Ss (* store typings for stack *)) S ->
        HasTypeLocals empty_Function_Ctx Ss locvs L ->
        (let (_, szs) := split L in szs = locsz) ->
        
        let F := (update_ret_ctx maybe_ret empty_Function_Ctx) in

        HasTypeInstruction S_stack C F L es (Arrow [] taus) L' ->
        PHasTypeInstruction S_stack C F L es (Arrow [] taus) L' ->
        
        (* Everything local after typechecking the configurations must be unrestricted -- linear things must be consumed! *)
        Forall (fun '(QualT pt q, sz) => QualLeq (qual F) q Unrestricted = Some true) L' ->
        PHasTypeConf S maybe_ret i locvs locsz es taus).


  Fixpoint HasTypeInstruction_mind' S C F L es tau L'
           (Hty : HasTypeInstruction S C F L es tau L') {struct Hty} :
    PHasTypeInstruction S C F L es tau L'
  with HasTypeClosure_mind' S cl chi (Hty : HasTypeClosure S cl chi) {struct Hty} :
    PHasTypeClosure S cl chi
  with HasTypeFunc_mind' S C t ex chi (Hty : HasTypeFunc S C t ex chi) {struct Hty} :
    PHasTypeFunc S C t ex chi
  with HasTypeConf_mind' S maybe_ret i locvis locsz es taus
                         (Hty : HasTypeConf S maybe_ret i locvis locsz es taus)
                         {struct Hty} :
    PHasTypeConf S maybe_ret i locvis locsz es taus.
  Proof.
    all: destruct Hty;
        try (apply seal in HasTypeInstruction_mind';
             apply seal in HasTypeClosure_mind';
             apply seal in HasTypeFunc_mind';
             apply seal in HasTypeConf_mind';
             multimatch goal with
             (* Somewhere in the context, there's a suitable assumption *)
             | H : forall _, _ |- _ =>
               solve [
                 (* Apply it and solve side conditions by using the stuff that was inside Hty *)
                 eapply H; eauto;
                 (* Now, it should be safe to apply induction hypothesis where needed *)
                 apply unseal in HasTypeInstruction_mind';
                 apply unseal in HasTypeClosure_mind';
                 apply unseal in HasTypeFunc_mind';
                 apply unseal in HasTypeConf_mind';
                 eauto;
                 (* Some cases (e.g. VariantCaseTyp(Lin|Unr)) have recursive occurrences of
                    the typing judgment under Forall2. Solve by nested induction *)
                 match goal with
                 | H : Forall2 _ ?es ?tausv |- Forall2 _ ?es ?tausv =>
                   clear - H HasTypeInstruction_mind' HasTypeClosure_mind'
                             HasTypeFunc_mind' HasTypeConf_mind';
                   let e := fresh in
                   let tauv := fresh in
                   let es := fresh in
                   let tausv := fresh in
                   let Hetauv := fresh in
                   let Hestausv := fresh in
                   let IH := fresh in
                   induction H as [|e tauv es tausv Hetauv Hestausv IH]; constructor; eauto
                 end]
             end).
  Qed.

  Lemma HasType_Instruction_Closure_Func_Conf_mind :
    (forall S C F L es tau L', HasTypeInstruction S C F L es tau L' ->
      PHasTypeInstruction S C F L es tau L') /\
    (forall S cl chi, HasTypeClosure S cl chi ->
      PHasTypeClosure S cl chi) /\
    (forall S C t ex chi, HasTypeFunc S C t ex chi ->
      PHasTypeFunc S C t ex chi) /\
    (forall S maybe_ret i locvis locsz es taus, HasTypeConf S maybe_ret i locvis locsz es taus ->
      PHasTypeConf S maybe_ret i locvis locsz es taus).
  Proof.
    repeat split; intros;
      (apply HasTypeInstruction_mind'||
       apply HasTypeClosure_mind'||
       apply HasTypeFunc_mind'||
       eapply HasTypeConf_mind'); auto.
  Qed.

  End HasType_Instruction_Closure_Func_Conf_mind'.

  Inductive HasTypeGlob (S : StoreTyping) : Module_Ctx -> Glob -> GlobalType -> list ex -> Prop :=
  | GlobMutTyp :
      forall C pt es,
        HasTypeInstruction S C empty_Function_Ctx [] es (Arrow [] [QualT pt Unrestricted]) [] ->
        HasTypeGlob S C (GlobMut pt es) (GT true pt) []
  | GlobTyp :
      forall C ex pt es,
        HasTypeInstruction S C empty_Function_Ctx [] es (Arrow [] [QualT pt Unrestricted]) [] ->
        HasTypeGlob S C (GlobEx ex pt es) (GT false pt) ex
  | GlobIm :
      forall C ex pt im,
        HasTypeGlob S C (GlobIm ex pt im) (GT false pt) ex.


  Definition combine_i {A} (xs : list A) : list (A * nat) :=
    (fix aux (xs : list A) (i : nat) :=
         match xs with
         | nil => []
         | cons x xs => (x, i) :: aux xs (i + 1)
         end) xs 0.

  Definition glob_typ (g : Glob) :=
    match g with
    | GlobMut pt es => GT true pt
    | GlobEx ex pt es => GT false pt
    | term.GlobIm ex pt im => GT false pt
    end.

  Definition fun_typ (f : Func) : FunType :=
    match f with
    | Fun x_ ft _ _ => ft
    end.

  Definition table_types (tb : Table) (tfs : list FunType) :=
    (fix aux tb :=
       match tb with
       | nil => []
       | cons t tb =>
         let tf :=
             match nth_error tfs t with
             | None => FunT [] (Arrow [] []) (* perhaps needs some WF so that always exists *)
             | Some tf => tf
             end
         in tf :: aux tb
       end) tb.
  

  Definition EmptyStoreTyping (I : InstanceTyping) : StoreTyping :=
    Build_StoreTyping I (M.empty _) (M.empty _).
      
  (* Module Instances are typed in the empty store typing *)
  Inductive HasTypeInstance (I : InstanceTyping) : MInst -> Module_Ctx -> Prop :=
  | InstT :
      forall cls gs ts fts1 tgs fts2,
        Forall2 (fun c ft => HasTypeClosure (EmptyStoreTyping I) c ft) cls fts1 ->
        Forall2 (fun c ft => HasTypeClosure (EmptyStoreTyping I) c ft) ts fts2 ->
        
        Forall2 (fun '(mut, v) tg => exists pt, HasTypeValue (EmptyStoreTyping I)
                                                         empty_Function_Ctx v (QualT pt Unrestricted)
                                            /\ tg = GT mut pt) gs tgs ->
        let C := Build_Module_Ctx fts1 tgs fts2 in
        HasTypeInstance I (Build_MInst cls gs ts) C.
                 
End Typing.

Require Import RWasm.locations.

Module Type MemTyping (Mem : Memory).

  Module MemUtils := MemUtils Mem.

  Module L := Location Mem.

  Import Mem L MemUtils RWasm.EnsembleUtil.

  Inductive HasTypeMeminst : StoreTyping -> StoreTyping -> Mem.t -> Prop  :=
  | MeminstT :
      forall mem S_lin S_unr Sh Sprog,
        dom_lin mem <--> Dom_ht (LinTyp Sh) :|: Dom_ht (LinTyp Sprog) ->
        dom_unr mem <--> Dom_ht (UnrTyp Sh) :|: Dom_ht (UnrTyp Sprog) ->

        SplitStoreTypings (S_lin ++ S_unr) Sh ->
                
        Forall2 (fun S '(loc, hv, len) =>
                   exists ht,
                     NoCapsHeapType [] ht = true /\
                     (get_heaptype loc (LinTyp Sh) = Some ht \/
                      get_heaptype loc (LinTyp Sprog) = Some ht) /\
                     HasHeapType S empty_Function_Ctx hv ht /\
                     RoomForStrongUpdates len ht /\ (* XXX ask Michael *) 
                     HeapTypeValid empty_Function_Ctx ht)
                S_lin (* a list of stores, each one of them is used to type a heap value *)
                (to_list Linear mem) (* A list of all locations + their values in the linear memry *) ->

        Forall2 (fun S '(loc, hv, len) =>
                   exists ht,
                     NoCapsHeapType [] ht = true /\
                     get_heaptype loc (UnrTyp S) = Some ht /\
                     HasHeapType S empty_Function_Ctx hv ht /\
                     RoomForStrongUpdates len ht /\
                     HeapTypeValid empty_Function_Ctx ht) S_unr (to_list Unrestricted mem) ->
        
        HasTypeMeminst Sh Sprog mem.
  
  Definition addEmptyLinTyping (S : StoreTyping) :=
    let (it, _, unrt) := S in
    Build_StoreTyping it (M.empty _) unrt.

    Record Store :=
    { inst    : list MInst;
      meminst : Mem.t;
      out_set : list Mem.Loc (* TODO redundant *)
    }.

  Inductive HasTypeStore : Store -> StoreTyping -> StoreTyping -> Prop :=
  | StoreT :
      forall s Sh Sprog S,
        SplitStoreTypings [Sprog; Sh] S ->
        Forall2 (fun i C => HasTypeInstance (InstTyp S) i C) (inst s) (InstTyp Sprog) ->
        HasTypeMeminst Sh Sprog (meminst s) ->
        HasTypeStore s Sh Sprog.

                    
  Inductive HasTypeConfig (S : StoreTyping) (i : nat) :
    Store -> list Value -> list nat (* size of the correspoding local slots *) -> list Instruction -> list Typ -> Prop :=
  | ConfTyp :
      forall s vlocs slocs es taus Sprog Sh,
        SplitStoreTypings [Sprog; Sh] S ->
        HasTypeStore s Sh Sprog ->
        HasTypeConf Sprog None i vlocs (map SizeConst slocs) es taus ->
        HasTypeConfig S i s vlocs slocs es taus.

End MemTyping.
