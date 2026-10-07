(** * System N exercises

    Replace [Abort] by a proof.  Useful first commands are [apply], [exact],
    and [n_assumption]. *)

From stdpp Require Import gmap.
From LogicCourse Require Import Tactics.
From LogicCourse.Propositional Require Import Syntax NaturalDeduction.

Open Scope N_scope.

Example exercise1 (A B : formula): (∅ : Context) ⊢ₙ ((A ∧ B) → (B ∧ A)).
Proof.
  apply N_impIntro.
  apply N_conjIntro.
  - apply (N_conjElimRight (A := A)). n_assumption.
  - apply (N_conjElimLeft (B := B)). n_assumption.
Qed.

Example exercise1' (A B : formula): (∅ : Context) ⊢ₙ ((A ∧ B) → (B ∧ A)).
Proof.
  assert ({[A ∧ B]} ⊢ₙ (A ∧ B)) as line0 by n_assumption.
  assert ({[A ∧ B]} ⊢ₙ A) as line1 by apply (N_conjElimLeft line0).
  assert ({[A ∧ B]} ⊢ₙ B) as line2 by apply (N_conjElimRight line0).
  assert ({[A ∧ B]} ⊢ₙ (B ∧ A)) as line3 by apply (N_conjIntro line2 line1).
  apply N_impIntro. normalize_context. exact line3.
Qed.

Example exercise2 (A B : formula): (∅ : Context) ⊢ₙ (A → (A ∨ B)).
Proof.
  apply N_impIntro.
  apply N_disjIntroLeft.
  n_assumption.
Qed.

Example exercise2' (A B : formula): (∅ : Context) ⊢ₙ (A → (A ∨ B)).
Proof.
  assert ({[A]} ⊢ₙ A) as line0 by n_assumption.
  assert ({[A]} ⊢ₙ (A ∨ B)) as line1 by apply (N_disjIntroLeft line0).
  apply N_impIntro. normalize_context. exact line1.
Qed.

Example exercise3 (Γ : Context) (A B C : formula):
  {[(A → B); (B → C); A]} ⊢ₙ C.
Proof.
  apply (N_impElim (A := B)).
  - n_assumption.
  - apply (N_impElim (A := A)).
    + n_assumption.
    + n_assumption.
Qed.

Example exercise3' (Γ : Context) (A B C : formula):
  {[(A → B); (B → C); A]} ⊢ₙ C.
Proof.
  assert ({[(A → B); (B → C); A]} ⊢ₙ (A → B)) as line0 by n_assumption.
  assert ({[(A → B); (B → C); A]} ⊢ₙ (B → C)) as line1 by n_assumption.
  assert ({[(A → B); (B → C); A]} ⊢ₙ A) as line2 by n_assumption.
  assert ({[(A → B); (B → C); A]} ⊢ₙ B) as line3 by
    apply (N_impElim line0 line2).
  assert ({[(A → B); (B → C); A]} ⊢ₙ C) as line4 by
    apply (N_impElim line1 line3).
  exact line4.
Qed.
