(** * System P exercises *)

From stdpp Require Import gmap.
From LogicCourse.Propositional Require Import Hilbert.

Open Scope P_scope.

Example exercise1 (Γ : PContext) (A B : pformula): Γ ⊢ₚ (A → (B → A)).
Proof.
  apply P_ax1.
Qed.

Example exercise2 (Γ : PContext) (A : pformula): Γ ⊢ₚ (A → A).
Proof.
Abort.
