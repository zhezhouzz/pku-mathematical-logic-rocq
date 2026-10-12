(** * Formal Systems

    Section 1.4 supplies the conceptual bridge from ordinary mathematics to
    the deep embeddings used in the rest of this book.  A formal system fixes
    a language, formation rules, axioms or assumptions, and inference rules.
    Rocq lets us represent each ingredient as data or as an inductive family.

    ** A tiny language *)

From Stdlib Require Import List Arith.
Import ListNotations.

Inductive toy_formula : Type :=
| ToyAtom : nat -> toy_formula
| ToyImp : toy_formula -> toy_formula -> toy_formula.

Fixpoint toy_complexity (A : toy_formula) : nat :=
  match A with
  | ToyAtom _ => 0
  | ToyImp B C => S (toy_complexity B + toy_complexity C)
  end.

Compute toy_complexity (ToyImp (ToyAtom 0) (ToyAtom 1)).

(** Because [toy_formula] is inductive, definitions and proofs may follow its
    formation rules exactly.  This is structural recursion and structural
    induction in executable form.

    ** A tiny derivation system

    The judgment [toy_derivation Γ A] says that [A] has a derivation from the
    finite list of assumptions [Γ].  Its constructors are inference rules. *)

Inductive toy_derivation : list toy_formula -> toy_formula -> Prop :=
| ToyAssumption {Γ A} : In A Γ -> toy_derivation Γ A
| ToyImpIntro {Γ A B} :
    toy_derivation (A :: Γ) B -> toy_derivation Γ (ToyImp A B)
| ToyImpElim {Γ A B} :
    toy_derivation Γ (ToyImp A B) ->
    toy_derivation Γ A ->
    toy_derivation Γ B.

Example toy_identity (A : toy_formula) : toy_derivation [] (ToyImp A A).
Proof.
  apply ToyImpIntro.
  apply ToyAssumption.
  now left.
Qed.

(** The proof term built above is literally a tree whose nodes are labelled by
    inference rules.  Chapters 2 and 3 replace this toy language with the
    textbook's formulas and replace lists with finite sets, but the central
    representation is unchanged.

    ** Deep and shallow embeddings

    [toy_formula] is a _deep embedding_: implication is represented by the
    constructor [ToyImp], so programs can inspect and transform formulas.  A
    shallow embedding would translate implication directly to Rocq's own
    function type and would lose the syntax tree.  Truth tables, substitution,
    and formal proof systems require the deep representation.

    ** Chapter summary

    A formal language becomes an inductive datatype; recursive definitions
    follow formation rules; and an inductive proposition records precisely the
    permitted inference trees. *)
