(** * Tarski Semantics for First-Order Formulas

    Section 3.6 interprets syntax inside a mathematical structure.  In
    contrast with propositional truth tables, the domain may be infinite and
    satisfaction is a Rocq proposition rather than a Boolean enumeration.

    A model interprets function and relation symbols; an assignment interprets
    variables.  Keeping these responsibilities separate is essential when a
    quantified formula changes one variable while preserving the model. *)

From Stdlib Require Import String List.
From stdpp Require Import gmap.
From LogicCourse.FirstOrder Require Import Syntax.

Import ListNotations.

Record model (D : Type) := {
  function_interp : string -> list D -> D;
  relation_interp : string -> list D -> Prop
}.

Definition assignment (D : Type) : Type := string -> D.

Definition update {D : Type} (ρ : assignment D) (x : string) (d : D) : assignment D :=
  fun y => if decide (y = x) then d else ρ y.

Fixpoint term_eval {D : Type} (M : model D) (ρ : assignment D) (t : term) : D :=
  match t with
  | Var x => ρ x
  | Func f args => function_interp D M f (map (term_eval M ρ) args)
  end.

Fixpoint satisfies {D : Type} (M : model D) (ρ : assignment D) (A : formula) : Prop :=
  match A with
  | Rel r args => relation_interp D M r (map (term_eval M ρ) args)
  | Neg B => ~ satisfies M ρ B
  | Conj B C => satisfies M ρ B /\ satisfies M ρ C
  | Disj B C => satisfies M ρ B \/ satisfies M ρ C
  | Imp B C => satisfies M ρ B -> satisfies M ρ C
  | Iff B C => satisfies M ρ B <-> satisfies M ρ C
  | Forall x B => forall d : D, satisfies M (update ρ x d) B
  | Exists x B => exists d : D, satisfies M (update ρ x d) B
  end.

Definition semantic_consequence (Γ : Context) (A : formula) : Prop :=
  forall (D : Type) (M : model D) (ρ : assignment D),
    (forall B, B ∈ Γ -> satisfies M ρ B) -> satisfies M ρ A.

Notation "Γ ⊨ A" := (semantic_consequence Γ A) (at level 74) : FOL_scope.

(** ** Propositional and first-order semantics compared

    A propositional valuation maps atom names directly to Booleans.  A
    first-order assignment maps variables to domain elements, while [model]
    supplies the meanings of nonlogical symbols.  Consequently [satisfies]
    returns [Prop], and [semantic_consequence] quantifies over every domain,
    model, and assignment.

    ** Chapter summary

    [term_eval] interprets terms, [satisfies] follows the structure of a
    formula, and [update] gives bound variables their quantified values.  The
    semantic judgment [Γ ⊨ A] remains distinct from both [Γ ⊢ₙₗ A] and
    [Γ ⊢ₖ A]. *)
