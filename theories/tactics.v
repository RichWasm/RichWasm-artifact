(* General purpose tactics *)

Require Import Coq.Arith.Arith. 

Ltac inv H := inversion H; clear H; subst.

Ltac subst_exp :=
  match goal with
    | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e2 = ?e |- _ ] =>
      rewrite <- H1 in H2; inv H2
    | [H1 : ?e = ?e1, H2 : ?e2 = ?e |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e = ?e2 |- _ ] =>
      rewrite <- H1 in H2; inv H2
  end.

Ltac tci := eauto with typeclass_instances.

Ltac sets := eauto with Ensembles_DB functions_BD.

Ltac xsets := eauto 20 with Ensembles_DB functions_BD.

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.

Ltac solve_ineqs :=
  try match goal with
      | [ |- _ <> _ ] =>
        let H' := fresh "H" in
        intro H'; inversion H'
      end.

Ltac solve_impossibles :=
  try match goal with
      | [ H : ?A <> ?A |- _ ] =>
        exfalso; apply H; auto
      end.

Ltac destruct_prs :=
  repeat match goal with
         | [ X : _ * _ |- _ ] => destruct X
         end.
