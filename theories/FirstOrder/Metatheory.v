(** * First-Order Metatheory Roadmap

    Sections 3.7 and 3.8 state soundness, harmony, and completeness results.
    They connect the syntactic systems studied earlier with Tarski semantics.
    This chapter records the intended interfaces without postulating any of
    the results as axioms.

    ** Soundness (可靠性)

    Soundness has the direction

    [[
        Γ ⊢ₙₗ A  ->  Γ ⊨ A        and        Γ ⊢ₖ A  ->  Γ ⊨ A.
    ]]

    Its proof proceeds by induction on a derivation and validates every rule or
    axiom under an arbitrary model and assignment.

    ** Completeness (完备性)

    Completeness reverses the implication.  A proof normally constructs a
    syntactic or canonical model and is substantially larger than the rule
    exercises that are the focus of this course repository. *)

From LogicCourse.FirstOrder Require Import
  Syntax NaturalDeduction Hilbert Semantics.

Check NLDerivation.
Check KDerivation.
Check semantic_consequence.

(** ** Future theorem statements

    When the metatheory is added, it should introduce named theorems such as
    [NL_sound] and [K_sound] in a separate advanced module.  Core syntax,
    inference rules, and student exercises must not depend on them.  This
    dependency direction keeps the elementary chapters usable on their own.

    ** Chapter summary

    Derivability and semantic consequence are intentionally independent
    definitions.  Reliability and completeness are theorems connecting them,
    not definitional equalities and not trusted assumptions. *)
