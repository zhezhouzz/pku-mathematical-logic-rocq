(** * First-order syntax

    Names are strings and function/relation arguments are ordinary lists.  This
    keeps the first encounter with first-order syntax close to blackboard
    notation; arity checking can be added later as an optional refinement. *)

From Stdlib Require Import String List Bool.
From stdpp Require Import gmap strings.

Import ListNotations.

Inductive term : Type :=
| Var : string -> term
| Func : string -> list term -> term.

Inductive formula : Type :=
| Rel : string -> list term -> formula
| Neg : formula -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula
| Imp : formula -> formula -> formula
| Iff : formula -> formula -> formula
| Forall : string -> formula -> formula
| Exists : string -> formula -> formula.

Fixpoint term_to_tree (t : term) : gen_tree string :=
  match t with
  | Var x => GenNode 0 [GenLeaf x]
  | Func f args =>
      GenNode 1 (GenLeaf f ::
        (fix args_to_trees (xs : list term) : list (gen_tree string) :=
           match xs with
           | [] => []
           | u :: us => term_to_tree u :: args_to_trees us
           end) args)
  end.

Fixpoint term_of_tree (t : gen_tree string) : option term :=
  match t with
  | GenNode 0 [GenLeaf x] => Some (Var x)
  | GenNode 1 (GenLeaf f :: trees) =>
      match (fix trees_to_args (xs : list (gen_tree string)) : option (list term) :=
               match xs with
               | [] => Some []
               | u :: us =>
                   match term_of_tree u, trees_to_args us with
                   | Some t, Some ts => Some (t :: ts)
                   | _, _ => None
                   end
               end) trees with
      | Some args => Some (Func f args)
      | None => None
      end
  | _ => None
  end.

Lemma term_tree_round_trip : forall t, term_of_tree (term_to_tree t) = Some t.
Proof.
  fix IH 1. intros [x|f args]; simpl; [reflexivity|].
  assert (Hargs :
    (fix trees_to_args (xs : list (gen_tree string)) : option (list term) :=
       match xs with
       | [] => Some []
       | u :: us =>
           match term_of_tree u, trees_to_args us with
           | Some t, Some ts => Some (t :: ts)
           | _, _ => None
           end
       end)
      ((fix args_to_trees (xs : list term) : list (gen_tree string) :=
          match xs with
          | [] => []
          | u :: us => term_to_tree u :: args_to_trees us
          end) args) = Some args).
  { induction args as [|u us IHus]; simpl; [reflexivity|].
    rewrite IH, IHus; reflexivity. }
  now rewrite Hargs.
Qed.

Global Instance term_eq_dec : EqDecision term.
Proof.
  intros t u. destruct (decide (term_to_tree t = term_to_tree u)) as [H|H].
  - left. apply (f_equal term_of_tree) in H.
    now rewrite !term_tree_round_trip in H; inversion H.
  - right. intros ->. apply H. reflexivity.
Defined.

Global Instance term_countable : Countable term :=
  inj_countable term_to_tree term_of_tree term_tree_round_trip.

Fixpoint formula_to_tree (A : formula) : gen_tree string :=
  match A with
  | Rel r args => GenNode 0 (GenLeaf r :: map term_to_tree args)
  | Neg B => GenNode 1 [formula_to_tree B]
  | Conj B C => GenNode 2 [formula_to_tree B; formula_to_tree C]
  | Disj B C => GenNode 3 [formula_to_tree B; formula_to_tree C]
  | Imp B C => GenNode 4 [formula_to_tree B; formula_to_tree C]
  | Iff B C => GenNode 5 [formula_to_tree B; formula_to_tree C]
  | Forall x B => GenNode 6 [GenLeaf x; formula_to_tree B]
  | Exists x B => GenNode 7 [GenLeaf x; formula_to_tree B]
  end.

Definition decode_terms (trees : list (gen_tree string)) : option (list term) :=
  fold_right (fun u acc =>
    match term_of_tree u, acc with
    | Some t, Some ts => Some (t :: ts)
    | _, _ => None
    end) (Some []) trees.

Fixpoint formula_of_tree (t : gen_tree string) : option formula :=
  match t with
  | GenNode 0 (GenLeaf r :: trees) =>
      match decode_terms trees with Some args => Some (Rel r args) | None => None end
  | GenNode 1 [u] => option_map Neg (formula_of_tree u)
  | GenNode 2 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Conj B C) | _, _ => None end
  | GenNode 3 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Disj B C) | _, _ => None end
  | GenNode 4 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Imp B C) | _, _ => None end
  | GenNode 5 [u; v] =>
      match formula_of_tree u, formula_of_tree v with
      | Some B, Some C => Some (Iff B C) | _, _ => None end
  | GenNode 6 [GenLeaf x; u] => option_map (Forall x) (formula_of_tree u)
  | GenNode 7 [GenLeaf x; u] => option_map (Exists x) (formula_of_tree u)
  | _ => None
  end.

Lemma decode_terms_map_round_trip args :
  decode_terms (map term_to_tree args) = Some args.
Proof.
  induction args as [|t ts IH]; simpl; [reflexivity|].
  rewrite term_tree_round_trip, IH; reflexivity.
Qed.

Lemma formula_tree_round_trip A : formula_of_tree (formula_to_tree A) = Some A.
Proof.
  induction A; simpl;
    try rewrite decode_terms_map_round_trip;
    repeat match goal with H : formula_of_tree (formula_to_tree _) = _ |- _ => rewrite H end;
    reflexivity.
Qed.

Global Instance formula_eq_dec : EqDecision formula.
Proof.
  intros A B. destruct (decide (formula_to_tree A = formula_to_tree B)) as [H|H].
  - left. apply (f_equal formula_of_tree) in H.
    now rewrite !formula_tree_round_trip in H; inversion H.
  - right. intros ->. apply H. reflexivity.
Defined.

Global Instance formula_countable : Countable formula :=
  inj_countable formula_to_tree formula_of_tree formula_tree_round_trip.

Definition Context : Type := gset formula.

Declare Scope FOL_scope.
Delimit Scope FOL_scope with FOL.
Notation "¬ A" := (Neg A) (at level 75, right associativity) : FOL_scope.
Notation "A ∧ B" := (Conj A B) (at level 80, right associativity) : FOL_scope.
Notation "A ∨ B" := (Disj A B) (at level 85, right associativity) : FOL_scope.
Notation "A → B" := (Imp A B) (at level 99, right associativity) : FOL_scope.
Notation "A ↔ B" := (Iff A B) (at level 95, no associativity) : FOL_scope.
Notation "∀ₒ x , A" := (Forall x A) (at level 200, x constr, right associativity) : FOL_scope.
Notation "∃ₒ x , A" := (Exists x A) (at level 200, x constr, right associativity) : FOL_scope.

Fixpoint term_free_variables (t : term) : gset string :=
  match t with
  | Var x => {[x]}
  | Func _ args =>
      fold_right (fun u xs => term_free_variables u ∪ xs) ∅ args
  end.

Fixpoint free_variables (A : formula) : gset string :=
  match A with
  | Rel _ args => fold_right (fun t xs => term_free_variables t ∪ xs) ∅ args
  | Neg B => free_variables B
  | Conj B C | Disj B C | Imp B C | Iff B C =>
      free_variables B ∪ free_variables C
  | Forall x B | Exists x B => free_variables B ∖ {[x]}
  end.

Definition is_sentence (A : formula) : bool := bool_decide (free_variables A = ∅).

Fixpoint substitute_term (x : string) (replacement : term) (t : term) : term :=
  match t with
  | Var y => if decide (y = x) then replacement else Var y
  | Func f args => Func f (map (substitute_term x replacement) args)
  end.

Fixpoint substitute (x : string) (t : term) (A : formula) : formula :=
  match A with
  | Rel r args => Rel r (map (substitute_term x t) args)
  | Neg B => Neg (substitute x t B)
  | Conj B C => Conj (substitute x t B) (substitute x t C)
  | Disj B C => Disj (substitute x t B) (substitute x t C)
  | Imp B C => Imp (substitute x t B) (substitute x t C)
  | Iff B C => Iff (substitute x t B) (substitute x t C)
  | Forall y B => if decide (y = x) then Forall y B else Forall y (substitute x t B)
  | Exists y B => if decide (y = x) then Exists y B else Exists y (substitute x t B)
  end.

(** Whether [t] is free for [x] in [A]. *)
Fixpoint free_for (t : term) (x : string) (A : formula) : bool :=
  match A with
  | Rel _ _ => true
  | Neg B => free_for t x B
  | Conj B C | Disj B C | Imp B C | Iff B C =>
      free_for t x B && free_for t x C
  | Forall y B | Exists y B =>
      if decide (y = x) then true
      else (bool_decide (x ∉ free_variables B) ||
            bool_decide (y ∉ term_free_variables t)) && free_for t x B
  end.
