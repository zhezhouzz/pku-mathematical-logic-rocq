(** * First-Order Natural Deduction [N_L]

    Section 3.3 extends natural deduction with universal and existential
    rules.  The propositional rules have the same proof-tree reading as in N;
    the new work lies in substitution and freshness side conditions.

    ** Quantifier side conditions

    Universal elimination and existential introduction require [free_for] so
    that substitution cannot capture a variable.  Universal introduction and
    existential elimination require an eigenvariable that is absent from the
    open assumptions (and, for elimination, from the conclusion).  These are
    logical restrictions, not inconveniences introduced by Rocq. *)

From Stdlib Require Import String.
From stdpp Require Import gmap fin_sets sets tactics.
From LogicCourse.FirstOrder Require Import Syntax.

Open Scope FOL_scope.

(** Formula, term, variable, and context indices are implicit whenever a
    conclusion or a derivation premise can determine them.  If unification of
    a substitution is underconstrained, callers can still write named
    arguments such as [(x := x)] and [(t := t)]. *)
Inductive NLDerivation : Context -> formula -> Prop :=
| NL_assumption {Γ : Context} {A : formula} :
    A ∈ Γ -> NLDerivation Γ A
| NL_negElim {Γ : Context} {A B : formula} :
    NLDerivation ({[Neg A]} ∪ Γ) B ->
    NLDerivation ({[Neg A]} ∪ Γ) (Neg B) -> NLDerivation Γ A
| NL_impElim {Γ : Context} {A B : formula} :
    NLDerivation Γ (A → B) -> NLDerivation Γ A -> NLDerivation Γ B
| NL_impIntro {Γ : Context} {A B : formula} :
    NLDerivation ({[A]} ∪ Γ) B -> NLDerivation Γ (A → B)
| NL_disjElim {Γ : Context} {A B C : formula} :
    NLDerivation ({[A]} ∪ Γ) C ->
    NLDerivation ({[B]} ∪ Γ) C ->
    NLDerivation Γ (A ∨ B) -> NLDerivation Γ C
| NL_disjIntroLeft {Γ : Context} {A B : formula} :
    NLDerivation Γ A -> NLDerivation Γ (A ∨ B)
| NL_disjIntroRight {Γ : Context} {A B : formula} :
    NLDerivation Γ B -> NLDerivation Γ (A ∨ B)
| NL_conjElimLeft {Γ : Context} {A B : formula} :
    NLDerivation Γ (A ∧ B) -> NLDerivation Γ A
| NL_conjElimRight {Γ : Context} {A B : formula} :
    NLDerivation Γ (A ∧ B) -> NLDerivation Γ B
| NL_conjIntro {Γ : Context} {A B : formula} :
    NLDerivation Γ A -> NLDerivation Γ B -> NLDerivation Γ (A ∧ B)
| NL_iffElimLeft {Γ : Context} {A B : formula} :
    NLDerivation Γ (A ↔ B) -> NLDerivation Γ A -> NLDerivation Γ B
| NL_iffElimRight {Γ : Context} {A B : formula} :
    NLDerivation Γ (A ↔ B) -> NLDerivation Γ B -> NLDerivation Γ A
| NL_iffIntro {Γ : Context} {A B : formula} :
    NLDerivation ({[A]} ∪ Γ) B ->
    NLDerivation ({[B]} ∪ Γ) A -> NLDerivation Γ (A ↔ B)
| NL_addPremise {Γ : Context} {A B : formula} :
    NLDerivation Γ A -> NLDerivation ({[B]} ∪ Γ) A
| NL_forallElim {Γ : Context} {x : string} {A : formula} {t : term} :
    NLDerivation Γ (Forall x A) -> free_for t x A = true ->
    NLDerivation Γ (substitute x t A)
| NL_forallIntro {Γ : Context} {x : string} {A : formula} :
    NLDerivation Γ A ->
    (forall B, B ∈ Γ -> x ∉ free_variables B) ->
    NLDerivation Γ (Forall x A)
| NL_existsElim {Γ : Context} {x : string} {A B : formula} :
    NLDerivation ({[A]} ∪ Γ) B ->
    x ∉ free_variables B ->
    (forall C, C ∈ Γ -> x ∉ free_variables C) ->
    NLDerivation ({[Exists x A]} ∪ Γ) B
| NL_existsIntro {Γ : Context} {x : string} {A : formula} {t : term} :
    NLDerivation Γ (substitute x t A) -> free_for t x A = true ->
    NLDerivation Γ (Exists x A).

Notation "Γ ⊢ₙₗ A" := (NLDerivation Γ A) (at level 74).

Definition NL_mp {Γ : Context} {A B : formula} :
  Γ ⊢ₙₗ (A → B) -> Γ ⊢ₙₗ A -> Γ ⊢ₙₗ B :=
  NL_impElim (Γ := Γ) (A := A) (B := B).
Ltac nl_assumption := apply NL_assumption; set_solver.

(** ** Two first quantifier proofs *)

Example NL_specialization_walkthrough :
  ({[Forall "x" syntax_Px]} : Context) ⊢ₙₗ substitute "x" syntax_c syntax_Px.
Proof.
  apply (NL_forallElim (x := "x") (A := syntax_Px) (t := syntax_c)).
  - nl_assumption.
  - reflexivity.
Qed.

Example NL_existential_witness_walkthrough :
  ({[substitute "x" syntax_c syntax_Px]} : Context) ⊢ₙₗ
    Exists "x" syntax_Px.
Proof.
  apply (NL_existsIntro (t := syntax_c)).
  - nl_assumption.
  - reflexivity.
Qed.

(** ** Structural metatheorems from Section 3.3 *)

(** Rule 11 in the book adds one premise.  This lemma iterates that primitive
    rule over an arbitrary finite [gset]. *)
Lemma NL_add_context (Γ extra : Context) (A : formula) :
  Γ ⊢ₙₗ A -> (extra ∪ Γ) ⊢ₙₗ A.
Proof.
  intro d. induction extra as [|B extra Hfresh IH] using set_ind_L.
  - replace (∅ ∪ Γ) with Γ by set_solver. exact d.
  - replace (({[B]} ∪ extra) ∪ Γ) with ({[B]} ∪ (extra ∪ Γ)) by set_solver.
    now apply NL_addPremise.
Qed.

Theorem NL_weaken (Γ Δ : Context) (A : formula) :
  Γ ⊆ Δ -> Γ ⊢ₙₗ A -> Δ ⊢ₙₗ A.
Proof.
  intros Hsub d.
  replace Δ with ((Δ ∖ Γ) ∪ Γ).
  2:{ apply (proj2 (set_eq ((Δ ∖ Γ) ∪ Γ) Δ)). intros C.
      rewrite elem_of_union, elem_of_difference. split.
      - intros [[HC _]|HC]; [exact HC|now apply Hsub].
      - intro HC. destruct (decide (C ∈ Γ)) as [Hin|Hnot].
        + now right.
        + now left. }
  now apply NL_add_context.
Qed.

(** A one-formula form of Theorem 3.2(1) (传递性/cut).  The temporary
    assumption [A] is discharged by implication introduction and then used
    with modus ponens. *)
Theorem NL_cut (Γ : Context) (A B : formula) :
  Γ ⊢ₙₗ A -> ({[A]} ∪ Γ) ⊢ₙₗ B -> Γ ⊢ₙₗ B.
Proof.
  intros dA dB.
  apply (NL_impElim (A := A)).
  - now apply NL_impIntro.
  - exact dA.
Qed.

(** The form closest to the book: the second derivation uses [A] as its
    only premise.  Weakening first adds [Γ], after which [NL_cut] applies. *)
Corollary NL_transitivity (Γ : Context) (A B : formula) :
  Γ ⊢ₙₗ A -> ({[A]} : Context) ⊢ₙₗ B -> Γ ⊢ₙₗ B.
Proof.
  intros dA dB. apply (NL_cut Γ A B dA).
  apply (NL_weaken ({[A]} : Context) ({[A]} ∪ Γ) B); [set_solver|exact dB].
Qed.

(** ** Chapter summary

    N_L reuses ordinary natural deduction and makes quantifier hygiene
    explicit in constructor premises.  Weakening is iterated from the
    primitive add-premise rule; implication introduction and elimination give
    the one-formula form of 传递性/cut. *)
