(** * Propositional Syntax

    Formulas are ordinary Rocq data.  This is a deliberately small deep
    embedding intended for the first chapters of a mathematical logic course.
    All five textbook connectives are primitive in system N.

    ** Learning objectives

    The reader should be able to distinguish an object-language formula from
    a Rocq proposition, construct formulas with textbook notation, and compute
    their complexity, depth, and variable set. *)

From Stdlib Require Import String List Bool Arith.
From stdpp Require Import gmap strings.

Import ListNotations.
Open Scope string_scope.

Inductive formula : Type :=
| Atom : string -> formula
| Neg  : formula -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula
| Imp  : formula -> formula -> formula
| Iff  : formula -> formula -> formula.

(** [formula] is syntax, not truth.  For example, [Imp (Atom "p") (Atom
    "q")] is a tree that can later be evaluated under many valuations. *)

Declare Scope N_scope.
Delimit Scope N_scope with N.
Notation "¬ A" := (Neg A) (at level 75, right associativity) : N_scope.
Notation "A ∧ B" := (Conj A B) (at level 80, right associativity) : N_scope.
Notation "A ∨ B" := (Disj A B) (at level 85, right associativity) : N_scope.
Notation "A → B" := (Imp A B) (at level 99, right associativity) : N_scope.
Notation "A ↔ B" := (Iff A B) (at level 95, no associativity) : N_scope.

Open Scope N_scope.

Definition syntax_p : formula := Atom "p".
Definition syntax_q : formula := Atom "q".

Check (syntax_p → (¬ syntax_q)).

(** ** Structural measures *)

Fixpoint complexity (A : formula) : nat :=
  match A with
  | Atom _ => 0
  | Neg B => S (complexity B)
  | Conj B C | Disj B C | Imp B C | Iff B C =>
      S (complexity B + complexity C)
  end.

Fixpoint depth (A : formula) : nat :=
  match A with
  | Atom _ => 0
  | Neg B => S (depth B)
  | Conj B C | Disj B C | Imp B C | Iff B C =>
      S (Nat.max (depth B) (depth C))
  end.

Compute complexity (syntax_p → (¬ syntax_q)).
Compute depth (syntax_p → (¬ syntax_q)).

Fixpoint variable_set (A : formula) : gset string :=
  match A with
  | Atom p => {[ p ]}
  | Neg B => variable_set B
  | Conj B C | Disj B C | Imp B C | Iff B C =>
      variable_set B ∪ variable_set C
  end.

Fixpoint uses_only_neg_imp (A : formula) : bool :=
  match A with
  | Atom _ => true
  | Neg B => uses_only_neg_imp B
  | Imp B C => uses_only_neg_imp B && uses_only_neg_imp C
  | _ => false
  end.

(** Short names are convenient in examples. *)
Definition atom (name : string) : formula := Atom name.

Fixpoint formula_to_string (A : formula) : string :=
  match A with
  | Atom p => p
  | Neg B => "¬(" ++ formula_to_string B ++ ")"
  | Conj B C => "(" ++ formula_to_string B ++ " ∧ " ++ formula_to_string C ++ ")"
  | Disj B C => "(" ++ formula_to_string B ++ " ∨ " ++ formula_to_string C ++ ")"
  | Imp B C => "(" ++ formula_to_string B ++ " → " ++ formula_to_string C ++ ")"
  | Iff B C => "(" ++ formula_to_string B ++ " ↔ " ++ formula_to_string C ++ ")"
  end.

(** ** Optional implementation interlude: finite-set keys

    Readers interested only in logic may skip this section.  std++ implements
    [gset formula] with a finite map, so formulas need decidable equality and a
    countable encoding.  The encoding below is infrastructure: it does not add
    a logical axiom or change the meaning of a formula. *)

Global Instance formula_eq_dec : EqDecision formula.
Proof. solve_decision. Defined.

Fixpoint formula_to_tree (A : formula) : gen_tree string :=
  match A with
  | Atom p => GenLeaf p
  | Neg B => GenNode 0 [formula_to_tree B]
  | Conj B C => GenNode 1 [formula_to_tree B; formula_to_tree C]
  | Disj B C => GenNode 2 [formula_to_tree B; formula_to_tree C]
  | Imp B C => GenNode 3 [formula_to_tree B; formula_to_tree C]
  | Iff B C => GenNode 4 [formula_to_tree B; formula_to_tree C]
  end.

Fixpoint formula_of_tree (t : gen_tree string) : option formula :=
  match t with
  | GenLeaf p => Some (Atom p)
  | GenNode 0 [u] => option_map Neg (formula_of_tree u)
  | GenNode 1 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Conj B C) | _, _ => None end
  | GenNode 2 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Disj B C) | _, _ => None end
  | GenNode 3 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Imp B C) | _, _ => None end
  | GenNode 4 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Iff B C) | _, _ => None end
  | _ => None
  end.

Lemma formula_tree_round_trip A : formula_of_tree (formula_to_tree A) = Some A.
Proof.
  induction A; simpl;
    repeat match goal with H : formula_of_tree (formula_to_tree _) = _ |- _ => rewrite H end;
    reflexivity.
Qed.

Global Instance formula_countable : Countable formula :=
  inj_countable formula_to_tree formula_of_tree formula_tree_round_trip.

(** ** Finite contexts

    With the two infrastructure instances available, a context can be a finite
    set of formulas.  Sets deliberately forget order and duplicates, matching
    the structural treatment in the textbook. *)
Definition Context : Type := gset formula.

(** ** Chapter summary

    Formulas are inspectable syntax trees.  Structural recursion defines their
    measures and variables, while [Context] records a finite set of open
    assumptions.  Truth is intentionally absent from this chapter and is
    supplied by valuations in Section 2.2. *)
