(** * Tarski semantics for first-order formulas *)

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
