(** * Selected Exercise Solutions

    These representative solutions demonstrate proof style without publishing
    answers to the complete worksheets.  Their names are distinct from the
    exercise templates, so students can fill a worksheet without collisions. *)

From Stdlib Require Import String.
From stdpp Require Import gmap.
From LogicCourse.Preliminaries Require Import RelationsFunctions.
From LogicCourse.Propositional Require Import
  Syntax NaturalDeduction Hilbert.
From LogicCourse.FirstOrder Require Import
  Syntax NaturalDeduction.

Open Scope N_scope.
Open Scope string_scope.

Theorem selected_composition_injective {A B C : Type}
    (f : A -> B) (g : B -> C) :
  injective f -> injective g -> injective (compose g f).
Proof.
  intros Hf Hg x y H.
  apply Hf, Hg, H.
Qed.

Theorem selected_N_identity (A : LogicCourse.Propositional.Syntax.formula) :
  (∅ : LogicCourse.Propositional.Syntax.Context) ⊢ₙ (A → A).
Proof.
  apply N_impIntro.
  n_assumption.
Qed.

Open Scope P_scope.

Theorem selected_P_identity (A : pformula) :
  (∅ : PContext) ⊢ₚ (A → A).
Proof. apply P_identity. Qed.

Open Scope FOL_scope.

Theorem selected_NL_specialization :
  ({[Forall "x" syntax_Px]} : LogicCourse.FirstOrder.Syntax.Context) ⊢ₙₗ
    substitute "x" syntax_c syntax_Px.
Proof.
  apply (NL_forallElim (x := "x") (A := syntax_Px) (t := syntax_c)).
  - nl_assumption.
  - reflexivity.
Qed.
