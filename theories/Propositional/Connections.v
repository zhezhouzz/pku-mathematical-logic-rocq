(** * Syntax, Semantics, N, and P

    Sections 2.7--2.9 ask how the two calculi relate to each other and to truth
    tables.  This chapter is a roadmap rather than a large metatheory library.

    [[
        Γ ⊢ₙ A  -------- soundness -------->  Γ ⊨ A
           ^                                  |
           |                                  | completeness
           |          N / P translation       |
           +-----------  Γ ⊢ₚ A  <------------+
    ]]

    ** What is implemented

    System N and system P have explicit derivation trees.  Propositional
    semantics computes truth tables and semantic consequence.  [p_to_n]
    translates the primitive language of P into N's richer formula type. *)

From LogicCourse.Propositional Require Import
  Syntax Semantics NaturalDeduction DerivedRules Hilbert.

Check p_to_n.
Check NDerivation.
Check PDerivation.
Check semantic_consequence.

(** ** What is deliberately postponed

    The repository does not yet contain total translations between arbitrary
    N and P derivations, nor proofs of soundness and completeness.  Those
    results require substantial induction and canonical-model machinery.  In
    this course version they remain paper theorems and future extension points
    rather than automation that would obscure the proof systems themselves.

    Students should nevertheless keep the three levels separate:

    - a [formula] is syntax;
    - [Γ ⊨ A] is a semantic statement checked through valuations;
    - [Γ ⊢ₙ A] or [Γ ⊢ₚ A] asks for a syntactic derivation.

    ** Reading the textbook

    The equivalence and metatheoretic results in the textbook explain why the
    calculi capture the same classical logic.  Nothing in the Rocq definitions
    assumes those results: their eventual proofs must be explicit theorems. *)
