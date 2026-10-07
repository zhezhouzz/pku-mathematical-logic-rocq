(** Small system-N proof trees built by applying inference rules directly. *)

From stdpp Require Import gmap.
From LogicCourse.Propositional Require Import Syntax NaturalDeduction.

Open Scope N_scope.

Example N_identity (A : formula) : (∅ : Context) ⊢ₙ (A → A).
Proof.
  apply N_impIntro.
  n_assumption.
Qed.

Example N_and_comm (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A ∧ B) -> Γ ⊢ₙ (B ∧ A).
Proof.
  intro hAB.
  apply N_conjIntro.
  - exact (N_conjElimRight hAB).
  - exact (N_conjElimLeft hAB).
Qed.

Example N_modus_ponens (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A → B) -> Γ ⊢ₙ A -> Γ ⊢ₙ B.
Proof. exact (@N_impElim Γ A B). Qed.
