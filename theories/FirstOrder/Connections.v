(** * The Relationship between [N_L] and [K_L]

    Section 3.5 compares two presentations of first-order classical logic.
    [N_L] exposes introduction and elimination rules close to paper reasoning;
    [K_L] concentrates logical power in axiom schemata and modus ponens.

    [[
          natural-deduction tree       Hilbert derivation
                Γ ⊢ₙₗ A       <---->       Γ ⊢ₖ A
    ]]

    This repository defines both endpoints and proves their local structural
    properties.  A complete translation in either direction is intentionally
    left outside the first teaching version: it is a sizeable induction and
    should appear as a theorem, never as an assumption hidden in the API. *)

From LogicCourse.FirstOrder Require Import Syntax NaturalDeduction Hilbert.

Check NLDerivation.
Check KDerivation.
Check NL_cut.
Check K_deduction.

(** The common syntax is important.  Unlike propositional P, [K_L] does not
    introduce a second formula datatype, so an equivalence theorem can compare
    the two judgments at exactly the same [Context] and [formula].

    ** Study question

    For each primitive N_L rule, identify the K_L theorem that would be needed
    to translate it.  Conversely, ask which N_L derived rule validates each of
    K1--K7.  This exercise exposes the architecture of the equivalence proof
    without requiring students to implement all of it at once. *)
