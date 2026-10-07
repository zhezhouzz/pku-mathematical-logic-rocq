(** Run the [Compute] commands sentence by sentence in the Rocq editor. *)

From Stdlib Require Import String.
From stdpp Require Import gmap.
From LogicCourse.Propositional Require Import Syntax Semantics.

Open Scope N_scope.
Open Scope string_scope.

Definition p : formula := Atom "p".
Definition q : formula := Atom "q".

Compute printTruthTable (p → p).
Compute printTruthTable ((p → q) ↔ (¬ q → ¬ p)).

Example identity_is_valid : isValid (p → p) = true.
Proof. reflexivity. Qed.

Example modus_ponens_is_a_consequence :
  (({[p; p → q]} : Context) ⊨ q) = true.
Proof. reflexivity. Qed.
