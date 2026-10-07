(** * Truth-table semantics *)

From Stdlib Require Import String List Bool.
From stdpp Require Import gmap fin_sets.
From LogicCourse.Propositional Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

Definition valuation : Type := string -> bool.

Fixpoint eval (v : valuation) (A : formula) : bool :=
  match A with
  | Atom p => v p
  | Neg B => negb (eval v B)
  | Conj B C => eval v B && eval v C
  | Disj B C => eval v B || eval v C
  | Imp B C => negb (eval v B) || eval v C
  | Iff B C => Bool.eqb (eval v B) (eval v C)
  end.

Definition valuation_of_true_variables (names : gset string) : valuation :=
  fun name => bool_decide (name ∈ names).

Fixpoint all_sublists {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: rest =>
      let rows := all_sublists rest in
      rows ++ map (cons x) rows
  end.

Record truth_table_row := {
  assignment : list (string * bool);
  result : bool
}.

Record truth_table := {
  table_variables : gset string;
  rows : list truth_table_row
}.

Definition truthTable (A : formula) : truth_table :=
  let names := variable_set A in
  let columns := elements names in
  {| table_variables := names;
     rows := map (fun true_names =>
       let v := valuation_of_true_variables (list_to_set true_names) in
       {| assignment := map (fun name => (name, v name)) columns;
          result := eval v A |}) (all_sublists columns) |}.

Definition isValid (A : formula) : bool :=
  forallb (fun row => result row) (rows (truthTable A)).

Definition isSatisfiable (A : formula) : bool :=
  existsb (fun row => result row) (rows (truthTable A)).

Definition isContradiction (A : formula) : bool := negb (isSatisfiable A).

Definition context_variables (Γ : Context) : gset string :=
  fold_right (fun A names => variable_set A ∪ names) ∅ (elements Γ).

(** [Γ ⊨ A] computes whether every valuation satisfying all formulas in [Γ]
    also satisfies [A]. *)
Definition semantic_consequence (Γ : Context) (A : formula) : bool :=
  let names := variable_set A ∪ context_variables Γ in
  forallb (fun true_names =>
    let v := valuation_of_true_variables (list_to_set true_names) in
    negb (forallb (eval v) (elements Γ)) || eval v A)
    (all_sublists (elements names)).

Notation "Γ ⊨ A" := (semantic_consequence Γ A) (at level 74) : N_scope.

Definition show_value (b : bool) : string := if b then "T" else "F".

Definition print_assignment (row : truth_table_row) : string :=
  String.concat " | " (map (fun nv => show_value (snd nv)) (assignment row)).

(** Rocq computations are pure, so this "printer" returns the lines to show.
    Use [Compute printTruthTable A.] in a lesson or exercise. *)
Definition printTruthTable (A : formula) : list string :=
  let table := truthTable A in
  let header := String.concat " | " (elements (table_variables table)) ++
                " || " ++ formula_to_string A in
  header :: map (fun row => print_assignment row ++ " || " ++ show_value (result row))
                (rows table).
