(** * Frequently used derived rules in Section 2.5

    These are proved once from the primitive rules of N, so later classroom
    proofs can use the same abbreviations as the textbook. *)

From stdpp Require Import gmap sets tactics.
From LogicCourse.Propositional Require Import Syntax NaturalDeduction.

Open Scope N_scope.

Theorem N_identity (Γ : Context) (A : formula) : Γ ⊢ₙ (A → A).
Proof. apply N_impIntro. n_assumption. Qed.

(** Ex falso: from a contradiction, derive any formula. *)
Theorem N_explosion (Γ : Context) (A B : formula) :
  Γ ⊢ₙ A -> Γ ⊢ₙ (¬ A) -> Γ ⊢ₙ B.
Proof.
  intros dA dnA. apply (N_negElim (B := A)).
  - now apply N_add_premise.
  - now apply N_add_premise.
Qed.

Theorem N_double_neg_elim (Γ : Context) (A : formula) :
  Γ ⊢ₙ (¬ ¬ A) -> Γ ⊢ₙ A.
Proof.
  intro d. apply (N_negElim (B := ¬ A)).
  - n_assumption.
  - now apply N_add_premise.
Qed.

Theorem N_double_neg_intro (Γ : Context) (A : formula) :
  Γ ⊢ₙ A -> Γ ⊢ₙ (¬ ¬ A).
Proof.
  intro d. apply (N_negElim (B := A)).
  - now apply N_add_premise.
  - apply N_double_neg_elim. n_assumption.
Qed.

(** The derived reductio rule called [¬+] in the book. *)
Theorem N_reductio (Γ : Context) (A B : formula) :
  ({[A]} ∪ Γ) ⊢ₙ B ->
  ({[A]} ∪ Γ) ⊢ₙ (¬ B) ->
  Γ ⊢ₙ (¬ A).
Proof.
  intros dB dnB. apply (N_negElim (B := B)).
  - set (E := ({[¬ ¬ A]} ∪ Γ : Context)).
    apply (N_cut E A B).
    + apply N_double_neg_elim. n_assumption.
    + apply (N_weaken ({[A]} ∪ Γ) ({[A]} ∪ E) B).
      * unfold E. set_solver.
      * exact dB.
  - set (E := ({[¬ ¬ A]} ∪ Γ : Context)).
    apply (N_cut E A (¬ B)).
    + apply N_double_neg_elim. n_assumption.
    + apply (N_weaken ({[A]} ∪ Γ) ({[A]} ∪ E) (¬ B)).
      * unfold E. set_solver.
      * exact dnB.
Qed.

Theorem N_modus_tollens (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A → B) -> Γ ⊢ₙ (¬ B) -> Γ ⊢ₙ (¬ A).
Proof.
  intros dAB dnB. apply (N_reductio Γ A B).
  - apply (N_impElim (A := A)).
    + now apply N_add_premise.
    + n_assumption.
  - now apply N_add_premise.
Qed.

Theorem N_imp_trans (Γ : Context) (A B C : formula) :
  Γ ⊢ₙ (A → B) -> Γ ⊢ₙ (B → C) -> Γ ⊢ₙ (A → C).
Proof.
  intros dAB dBC. apply N_impIntro.
  apply (N_impElim (A := B)).
  - now apply N_add_premise.
  - apply (N_impElim (A := A)).
    + now apply N_add_premise.
    + n_assumption.
Qed.

Theorem N_and_comm (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A ∧ B) -> Γ ⊢ₙ (B ∧ A).
Proof.
  intro d. apply N_conjIntro.
  - exact (N_conjElimRight d).
  - exact (N_conjElimLeft d).
Qed.

Theorem N_or_comm (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A ∨ B) -> Γ ⊢ₙ (B ∨ A).
Proof.
  intro d. apply (N_disjElim (A := A) (B := B)).
  - exact d.
  - apply N_disjIntroRight. n_assumption.
  - apply N_disjIntroLeft. n_assumption.
Qed.

Theorem N_iff_refl (Γ : Context) (A : formula) : Γ ⊢ₙ (A ↔ A).
Proof. apply N_iffIntro; n_assumption. Qed.

Theorem N_iff_sym (Γ : Context) (A B : formula) :
  Γ ⊢ₙ (A ↔ B) -> Γ ⊢ₙ (B ↔ A).
Proof.
  intro d. apply N_iffIntro.
  - apply (N_iffElimRight (B := B)).
    + now apply N_add_premise.
    + n_assumption.
  - apply (N_iffElimLeft (A := A)).
    + now apply N_add_premise.
    + n_assumption.
Qed.
