(** * System N: classical natural deduction

    Each constructor is one inference rule.  An argument is implicit exactly
    when it can be reconstructed from the rule's conclusion.  For example,
    Formula and context indices are implicit whenever they can be recovered
    from the conclusion or from a derivation premise.  A user can still select
    an unresolved intermediate formula with a named argument such as
    [N_impElim (A := A)]. *)

From stdpp Require Import gmap sets tactics.
From LogicCourse.Propositional Require Import Syntax.

Open Scope N_scope.

Inductive NDerivation : Context -> formula -> Prop :=
| N_assumption {Γ : Context} {A : formula} :
    A ∈ Γ -> NDerivation Γ A
| N_negElim {Γ : Context} {A B : formula} :
    NDerivation ({[Neg A]} ∪ Γ) B ->
    NDerivation ({[Neg A]} ∪ Γ) (Neg B) ->
    NDerivation Γ A
| N_conjIntro {Γ : Context} {A B : formula} :
    NDerivation Γ A -> NDerivation Γ B -> NDerivation Γ (A ∧ B)
| N_conjElimLeft {Γ : Context} {A B : formula} :
    NDerivation Γ (A ∧ B) -> NDerivation Γ A
| N_conjElimRight {Γ : Context} {A B : formula} :
    NDerivation Γ (A ∧ B) -> NDerivation Γ B
| N_disjIntroLeft {Γ : Context} {A B : formula} :
    NDerivation Γ A -> NDerivation Γ (A ∨ B)
| N_disjIntroRight {Γ : Context} {A B : formula} :
    NDerivation Γ B -> NDerivation Γ (A ∨ B)
| N_disjElim {Γ : Context} {A B C : formula} :
    NDerivation Γ (A ∨ B) ->
    NDerivation ({[A]} ∪ Γ) C ->
    NDerivation ({[B]} ∪ Γ) C ->
    NDerivation Γ C
| N_impIntro {Γ : Context} {A B : formula} :
    NDerivation ({[A]} ∪ Γ) B -> NDerivation Γ (A → B)
| N_impElim {Γ : Context} {A B : formula} :
    NDerivation Γ (A → B) -> NDerivation Γ A -> NDerivation Γ B
| N_iffIntro {Γ : Context} {A B : formula} :
    NDerivation ({[A]} ∪ Γ) B ->
    NDerivation ({[B]} ∪ Γ) A ->
    NDerivation Γ (A ↔ B)
| N_iffElimLeft {Γ : Context} {A B : formula} :
    NDerivation Γ (A ↔ B) -> NDerivation Γ A -> NDerivation Γ B
| N_iffElimRight {Γ : Context} {A B : formula} :
    NDerivation Γ (A ↔ B) -> NDerivation Γ B -> NDerivation Γ A.

Notation "Γ ⊢ₙ A" := (NDerivation Γ A) (at level 74).

(** Familiar aliases. *)
Definition N_mp {Γ : Context} {A B : formula} :
  Γ ⊢ₙ (A → B) -> Γ ⊢ₙ A -> Γ ⊢ₙ B :=
  N_impElim (Γ := Γ) (A := A) (B := B).
Definition N_byContradiction {Γ : Context} {A B : formula} :
  ({[¬ A]} ∪ Γ) ⊢ₙ B -> ({[¬ A]} ∪ Γ) ⊢ₙ (¬ B) -> Γ ⊢ₙ A :=
  N_negElim (Γ := Γ) (A := A) (B := B).

(** Closes a goal whose conclusion is literally among the assumptions. *)
Ltac n_assumption := apply N_assumption; set_solver.

(** ** Metatheorems from Section 2.5 *)

Lemma N_extend_context (Γ Δ : Context) (X : formula) :
  Γ ⊆ Δ -> ({[X]} ∪ Γ) ⊆ ({[X]} ∪ Δ).
Proof. set_solver. Qed.

(** Theorem 2.5 (增加前提律).  The book states the one-premise form;
    the subset formulation is more convenient and immediately implies it. *)
Theorem N_weaken (Γ Δ : Context) (A : formula) :
  Γ ⊆ Δ -> Γ ⊢ₙ A -> Δ ⊢ₙ A.
Proof.
  intros Hsub d. revert Δ Hsub.
  induction d as
    [Γ A h
    |Γ A B dB IHB dNB IHNB
    |Γ A B dA IHA dB IHB
    |Γ A B dAB IHAB
    |Γ A B dAB IHAB
    |Γ A B dA IHA
    |Γ A B dB IHB
    |Γ A B C dAB IHAB dAC IHAC dBC IHBC
    |Γ A B dB IHB
    |Γ A B dAB IHAB dA IHA
    |Γ A B dAB IHAB dBA IHBA
    |Γ A B dIff IHIff dA IHA
    |Γ A B dIff IHIff dB IHB]; intros Δ Hsub.
  - apply N_assumption. set_solver.
  - apply (N_negElim (B := B)).
    + apply IHB. now apply N_extend_context.
    + apply IHNB. now apply N_extend_context.
  - apply N_conjIntro; [now apply IHA | now apply IHB].
  - apply (N_conjElimLeft (B := B)). now apply IHAB.
  - apply (N_conjElimRight (A := A)). now apply IHAB.
  - apply N_disjIntroLeft. now apply IHA.
  - apply N_disjIntroRight. now apply IHB.
  - apply (N_disjElim (A := A) (B := B)).
    + now apply IHAB.
    + apply IHAC. now apply N_extend_context.
    + apply IHBC. now apply N_extend_context.
  - apply N_impIntro. apply IHB. now apply N_extend_context.
  - apply (N_impElim (A := A)); [now apply IHAB | now apply IHA].
  - apply N_iffIntro.
    + apply IHAB. now apply N_extend_context.
    + apply IHBA. now apply N_extend_context.
  - apply (N_iffElimLeft (A := A)); [now apply IHIff | now apply IHA].
  - apply (N_iffElimRight (B := B)); [now apply IHIff | now apply IHB].
Qed.

Corollary N_add_premise (Γ : Context) (A B : formula) :
  Γ ⊢ₙ A -> ({[B]} ∪ Γ) ⊢ₙ A.
Proof. apply N_weaken. set_solver. Qed.

(** Theorem 2.6 (传递律), in a general substitution form.  Every open
    assumption of the second derivation is replaced by a derivation from Γ. *)
Theorem N_substitution (Γ Δ : Context) (A : formula) :
  (forall B, B ∈ Δ -> Γ ⊢ₙ B) -> Δ ⊢ₙ A -> Γ ⊢ₙ A.
Proof.
  intros Hprem d. revert Γ Hprem.
  induction d as
    [Δ A h
    |Δ A B dB IHB dNB IHNB
    |Δ A B dA IHA dB IHB
    |Δ A B dAB IHAB
    |Δ A B dAB IHAB
    |Δ A B dA IHA
    |Δ A B dB IHB
    |Δ A B C dAB IHAB dAC IHAC dBC IHBC
    |Δ A B dB IHB
    |Δ A B dAB IHAB dA IHA
    |Δ A B dAB IHAB dBA IHBA
    |Δ A B dIff IHIff dA IHA
    |Δ A B dIff IHIff dB IHB]; intros Γ Hprem.
  - now apply Hprem.
  - apply (N_negElim (B := B)).
    + apply IHB. intros C HC. destruct (decide (C = Neg A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHNB. intros C HC. destruct (decide (C = Neg A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply N_conjIntro; [now apply IHA | now apply IHB].
  - apply (N_conjElimLeft (B := B)). now apply IHAB.
  - apply (N_conjElimRight (A := A)). now apply IHAB.
  - apply N_disjIntroLeft. now apply IHA.
  - apply N_disjIntroRight. now apply IHB.
  - apply (N_disjElim (A := A) (B := B)).
    + now apply IHAB.
    + apply IHAC. intros D HD. destruct (decide (D = A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHBC. intros D HD. destruct (decide (D = B)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply N_impIntro. apply IHB.
    intros C HC. destruct (decide (C = A)) as [->|Hne].
    + n_assumption.
    + apply N_add_premise, Hprem. set_solver.
  - apply (N_impElim (A := A)); [now apply IHAB | now apply IHA].
  - apply N_iffIntro.
    + apply IHAB. intros C HC. destruct (decide (C = A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHBA. intros C HC. destruct (decide (C = B)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply (N_iffElimLeft (A := A)); [now apply IHIff | now apply IHA].
  - apply (N_iffElimRight (B := B)); [now apply IHIff | now apply IHB].
Qed.

Corollary N_cut (Γ : Context) (A B : formula) :
  Γ ⊢ₙ A -> ({[A]} ∪ Γ) ⊢ₙ B -> Γ ⊢ₙ B.
Proof.
  intros dA dB. eapply N_substitution; [|exact dB].
  intros C HC. destruct (decide (C = A)) as [->|Hne].
  - exact dA.
  - apply N_assumption. set_solver.
Qed.
