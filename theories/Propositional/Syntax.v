(** * Propositional formulas

    Formulas are ordinary Rocq data.  This is a deliberately small deep
    embedding intended for the first chapters of a mathematical logic course.
    All five textbook connectives are primitive in system N. *)

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

(** A finite set of assumptions. *)
Definition Context : Type := gset formula.

Declare Scope N_scope.
Delimit Scope N_scope with N.
Notation "¬ A" := (Neg A) (at level 75, right associativity) : N_scope.
Notation "A ∧ B" := (Conj A B) (at level 80, right associativity) : N_scope.
Notation "A ∨ B" := (Disj A B) (at level 85, right associativity) : N_scope.
Notation "A → B" := (Imp A B) (at level 99, right associativity) : N_scope.
Notation "A ↔ B" := (Iff A B) (at level 95, no associativity) : N_scope.

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
