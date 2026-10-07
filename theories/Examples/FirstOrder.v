(** First-order syntax and [N_L] examples. *)

From Stdlib Require Import String List.
From stdpp Require Import gmap.
From LogicCourse.FirstOrder Require Import Syntax NaturalDeduction.

Import ListNotations.

Open Scope string_scope.
Open Scope FOL_scope.

Definition x : term := Var "x".
Definition c : term := Func "c" [].
Definition Px : formula := Rel "P" [x].

Check (∀ₒ "x", Px)%FOL.
Check (∃ₒ "x", Px)%FOL.

Compute free_variables (∀ₒ "x", Px)%FOL.
Compute substitute "x" c Px.

Example NL_specialize :
  ({[Forall "x" Px]} : Context) ⊢ₙₗ substitute "x" c Px.
Proof.
  apply (NL_forallElim (x := "x") (A := Px) (t := c)).
  - nl_assumption.
  - reflexivity.
Qed.
