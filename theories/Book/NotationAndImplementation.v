(** * Notation and Implementation Reference

    This appendix collects conventions that are useful while reading several
    chapters but are not themselves logical rules.

    ** Judgment notation

    [[
      Γ ⊨ A     semantic consequence
      Γ ⊢ₙ A    derivability in propositional natural deduction N
      Γ ⊢ₚ A    derivability in propositional Hilbert system P
      Γ ⊢ₙₗ A   derivability in first-order natural deduction N_L
      Γ ⊢ₖ A    derivability in first-order Hilbert system K_L
    ]]

    These symbols live in [N_scope], [P_scope], and [FOL_scope].  Open exactly
    the scope required by the current object language.

    ** Rule names and implicit arguments

    Constructors begin with the system name: [N_], [P_], [NL_], or [K_].
    Formula and context arguments are implicit when a conclusion or derivation
    premise determines them.  Supply a named argument such as [(A := A)] only
    when the intermediate formula remains ambiguous. *)

From LogicCourse.Propositional Require Import
  Syntax Semantics NaturalDeduction Hilbert.
From LogicCourse.FirstOrder Require Import
  Syntax NaturalDeduction Hilbert Semantics.

Check N_impElim.
Check P_mp.
Check NL_forallElim.
Check K_mp.

(** ** std++ finite sets

    Contexts use [gset], so order and repeated assumptions are ignored.  The
    [EqDecision] and [Countable] instances in syntax chapters are engineering
    support for finite-map keys; they are constructive encodings, not logical
    postulates.  [set_solver] and [normalize_context] solve only finite-set
    bookkeeping.

    ** English--Chinese glossary

    - assumption / premise -- 前提
    - derivation -- 推演
    - semantic consequence -- 语义后承
    - weakening / adding premises -- 增加前提律
    - transitivity / cut -- 传递性 / 切割
    - free variable -- 自由变元
    - bound variable -- 约束变元
    - soundness -- 可靠性
    - consistency / harmony -- 和谐性
    - completeness -- 完备性

    ** API index

    Use the generated definition and theorem index for links to every public
    identifier.  Existing module names and theorem names are kept stable so
    classroom files can import the library across textbook revisions. *)
