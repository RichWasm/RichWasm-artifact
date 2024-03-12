From Coq Require Import Numbers.BinNums ZArith List Structures.Orders .

Require Import RWasm.term RWasm.functions RWasm.EnsembleUtil RWasm.list_util RWasm.tactics.

Open Scope N.

Module Type Memory.

  Parameter (t : Type).
  
  Definition Loc := N.
  Definition Len := N. (* The length of the mem block (Size is taken) *)
  Definition Mem := QualConstant.
  Definition Val := HeapValue.
    

  (* The empty memory *) 
  Parameter emp : t.
  
  (* Every pointer is associated to a heap-allocated value, a strategy, and the end of the range *)  
  (* If [get m l1 = Some (ms, v, l2)] then v is stored in [l1, l2] *)
  Parameter get : Loc -> Mem -> t -> option (Val * Len).
  
  Parameter set : Loc -> Mem -> t -> Val -> option t.

  Parameter to_list : Mem -> t -> list (Loc * Val * Len).
    
  Parameter get_empty :
    forall (l : Loc) (m : Mem), get l m emp = None.  

  (* Non-overlap spec *)
  Parameter get_range :
    forall (mem : t) (l : Loc) (m : Mem) (s : Len) (v : Val),
      get l m mem = Some (v, s) ->
      forall l'', l < l'' < l + s -> get l'' m mem = None. 
 
  (* Get after set spec *)
  Parameter get_set_same :
    forall (mem mem' : t) (l : Loc) (m : Mem) (v : Val),
      set l m mem v = Some mem' ->
      exists s, get l m mem' = Some (v, s) /\ N.of_nat (size v) <= s. 
  
  (* TODO: Discuss in Slack whether this axiom is correct *)
  Parameter get_set_same_size :
    forall (mem mem' : t) (l : Loc) (m : Mem) (vold v : Val) (s : Len),
      get l m mem = Some (vold, s) ->
      set l m mem v = Some mem' ->
      get l m mem' = Some (v, s).

  Parameter get_set_other_loc :
    forall (mem mem' : t) (l l' : Loc) (m : Mem) (v : Val),
      set l m mem v = Some mem' ->
      l <> l' ->
      get l' m mem = get l' m mem'.

  Parameter get_set_other_mem :
    forall (mem mem' : t) (l l' : Loc) (m m' : Mem) (v : Val),
      set l m mem v = Some mem' ->
      m <> m' ->
      get l' m' mem = get l' m' mem'.

  (* Get after set spec *)
  Parameter get_spec1 :
    forall (mem : t) (l : Loc) (m : Mem) (v : Val) (s : Len),
      get l m mem = Some (v, s) ->
      N.of_nat (size v) <= s.

  Parameter set_spec1 :
    forall (mem : t) (l : Loc) (m : Mem) (v v' : Val) (s : Len),
      get l m mem = Some (v, s)  ->  (* to update something is must 1.) be present in memory *)
      N.of_nat (size v') <= s -> (* 2.) It must fit in the range *)
      exists mem', set l m mem v' = Some mem'.
  
  Parameter alloc : t -> Mem -> Len -> Val -> option (t * Loc * Len).

  (* alloc always gives size requested *)
  (* TODO: Discuss in Slack whether this axiom is correct *)
  Parameter alloc_same_size :
    forall (mem mem' : t) (m : Mem) (l : Loc) (s s' : Len) (v : Val),
      alloc mem m s v = Some (mem', l, s') -> s = s'.

  (* alloc size spec *)
  Parameter alloc_size :
    forall (mem mem' : t) (m : Mem) (l : Loc) (s : Len) (v : Val),
      alloc mem m s v = Some (mem', l, s) -> N.of_nat (size v) < s.

  Parameter alloc_fresh :
    forall (mem mem' : t) (l : Loc) (m : Mem) (v : Val) (s : Len),
      alloc mem m s v = Some (mem', l, s) ->
      forall l', l <= l' < l + s  -> get l' m mem = None. 

  (* Get after alloc spec *)
  Parameter get_alloc_same :
    forall (mem mem' : t) (l : Loc) (m : Mem) (v : Val) (s : Len),
      alloc mem m s v = Some (mem', l, s) ->
      get l m mem' = Some (v, s).  
  
  Parameter get_alloc_other_loc :
    forall (mem mem' : t) (l l' : Loc) (m : Mem) (v : Val) (s : Len),
      alloc mem m s v = Some (mem', l, s) ->
      l' <> l ->
      get l' m mem' = get l' m mem.  

  Parameter get_alloc_other_mem :
    forall (mem mem' : t) (l l' : Loc) (m m' : Mem) (v : Val) (s : Len),
      alloc mem m s v = Some (mem', l, s) ->
      m' <> m ->
      get l' m' mem' = get l' m' mem.  

  (* Is the range exact ? Is it updated whenever something smaller gets stored in a location? *) 

  
  Parameter free : Loc -> Mem -> t -> option t.
  
  Parameter free_spec1 :
    forall (mem : t) (l : Loc) (m : Mem) (v : Val) (s : Len),
      get l m mem = Some (v, s)  ->  (* if something is present in memory *)
      exists mem', free l m mem = Some mem'.  (* free succeds *)
  

  Parameter free_spec2 :
    forall (mem : t) (l : Loc) (m : Mem),
      get l m mem = None -> free l m mem = None.

  Parameter get_free_s :
    forall (mem mem' : t) (m : Mem) (l : Loc),
      free l m mem = Some mem' -> get l m mem' = None. 

  Parameter get_free_o :
    forall (mem mem' : t) (m : Mem) (l l' : Loc),
      free l m mem = Some mem' ->
      l <> l' ->
      get l' m mem' = get l' m mem. 

  Parameter get_free_diff_mem :
    forall (mem mem' : t) (m m' : Mem) (l l' : Loc),
      free l m mem = Some mem' ->
      m <> m' ->
      get l' m' mem' = get l' m' mem. 

  Parameter get_implies_in_to_list :
    forall l1 l2 m mem v,
      get l1 m mem = Some (v, l2) ->
      exists i,
        nth_error (to_list m mem) i = Some (l1, v, l2).

  Parameter in_to_list_implies_get :
    forall l1 l2 m mem v i,
      nth_error (to_list m mem) i = Some (l1, v, l2) ->
      get l1 m mem = Some (v, l2).

  Parameter to_list_NoDup :
    forall m h, NoDup (to_list m h). 
      
End Memory.

Close Scope N.


Module MemUtils (M : Memory).

  Import M. 

  Definition dom (M : Mem) (m : M.t) :=
    [ set l | exists v, get l M m = Some v ].  

  Definition dom_lin := dom Linear. 

  Definition dom_unr := dom Unrestricted. 

  Definition sub_heap (m : Mem) (s1 s2 : M.t) :=
    forall x v m, M.get m x s1 = Some v ->
                  M.get m x s2 = Some v.

  
  Lemma to_list_sub_heap :
    forall h1 h2 m,
      sub_heap m h1 h2 ->
      exists l1 l2 l,
        Permutation.Permutation (to_list m h1) l1 /\
        Permutation.Permutation (to_list m h2) l2 /\
          l2 = l ++ l1.
  Proof.
    intros h1 h2 m Hsub. 
    assert (Hsubl : Subperm (to_list m h1) (to_list m h2)).
    { eapply incl_Subperm. eapply to_list_NoDup.
      intros [[l v] s] Hin1.
      
      eapply In_nth_error in Hin1. inv Hin1.
      eapply in_to_list_implies_get in H.
      eapply Hsub in H.
      eapply get_implies_in_to_list in H. inv H.
      eapply nth_error_In. eassumption.

    }

    eapply Subperm_permutation_app. eassumption.
  Qed.      
      
End MemUtils.
