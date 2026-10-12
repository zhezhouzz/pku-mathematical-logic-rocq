(** * System N: classical natural deduction

    Each constructor is one inference rule.  An argument is implicit exactly
    when it can be reconstructed from the rule's conclusion.  For example,
    Formula and context indices are implicit whenever they can be recovered
    from the conclusion or from a derivation premise.  A user can still select
    an unresolved intermediate formula with a named argument such as
    [N_impElim (A := A)].

    This chapter covers Sections 2.4 and 2.5.  Its central idea is that a proof
    is data: an inhabitant of [NDerivation Γ A] records a complete inference
    tree concluding [A] from assumptions [Γ].

    ** Reading the rules

    Each constructor below is one horizontal rule from the textbook.  Its
    derivation arguments are the premises above the line and its result is the
    conclusion below the line.  Introduction rules build a connective;
    elimination rules consume it. *)

From stdpp Require Import gmap sets tactics.
From LogicCourse.Propositional Require Import Syntax.

Open Scope N_scope.

Inductive NDerivation : Context -> formula -> Prop :=
| N_assumption {Γ : Context} {A : formula} :
    A ∈ Γ -> NDerivation Γ A

| N_negElim {Γ : Context} {A B : formula} :
    NDerivation ({[Neg A]} ∪ Γ) B ->
    NDerivation ({[Neg A]} ∪ Γ) (Neg B) ->
    NDerivation Γ A

| N_conjIntro {Γ : Context} {A B : formula} :
    NDerivation Γ A -> NDerivation Γ B -> NDerivation Γ (A ∧ B)

| N_conjElimLeft {Γ : Context} {A B : formula} :
    NDerivation Γ (A ∧ B) -> NDerivation Γ A

| N_conjElimRight {Γ : Context} {A B : formula} :
    NDerivation Γ (A ∧ B) -> NDerivation Γ B

| N_disjIntroLeft {Γ : Context} {A B : formula} :
    NDerivation Γ A -> NDerivation Γ (A ∨ B)

| N_disjIntroRight {Γ : Context} {A B : formula} :
    NDerivation Γ B -> NDerivation Γ (A ∨ B)

| N_disjElim {Γ : Context} {A B C : formula} :
    NDerivation Γ (A ∨ B) ->
    NDerivation ({[A]} ∪ Γ) C ->
    NDerivation ({[B]} ∪ Γ) C ->
    NDerivation Γ C

| N_impIntro {Γ : Context} {A B : formula} :
    NDerivation ({[A]} ∪ Γ) B -> NDerivation Γ (A → B)

| N_impElim {Γ : Context} {A B : formula} :
    NDerivation Γ (A → B) -> NDerivation Γ A -> NDerivation Γ B

| N_iffIntro {Γ : Context} {A B : formula} :
    NDerivation ({[A]} ∪ Γ) B ->
    NDerivation ({[B]} ∪ Γ) A ->
    NDerivation Γ (A ↔ B)

| N_iffElimLeft {Γ : Context} {A B : formula} :
    NDerivation Γ (A ↔ B) -> NDerivation Γ A -> NDerivation Γ B

| N_iffElimRight {Γ : Context} {A B : formula} :
    NDerivation Γ (A ↔ B) -> NDerivation Γ B -> NDerivation Γ A.

Notation "Γ ⊢ₙ A" := (NDerivation Γ A) (at level 74).

(** ** Rule atlas: paper trees and Rocq constructors

    A rule is read top-down when checking a finished derivation: derivations
    of every premise above the bar justify the conclusion below it.  While
    constructing a proof, read it bottom-up: match the desired conclusion,
    apply the named constructor, and Rocq turns the premises into new goals.

    The book writes contexts as [Γ ∪ {A}].  The implementation writes
    [{[A]} ∪ Γ], using std++ singleton and union notation.  Because [Context]
    is a finite set, the order is immaterial.

    *** Assumptions -- Rule 1

    An available assumption may be used immediately.  The premise [A ∈ Γ] is
    finite-set bookkeeping rather than another logical derivation.

[[[
A ∈ Γ
---------------- assumption / N_assumption
Γ ⊢ₙ A
]]]

    In Rocq, [apply N_assumption] leaves the membership goal [A ∈ Γ].  The
    teaching tactic [n_assumption] performs both steps.

    *** Classical contradiction -- Rule 2

    Temporarily assume [¬ A].  If that enlarged context derives both some
    formula [B] and its negation, the temporary assumption is impossible, so
    conclude [A].  The witness [B] is arbitrary; this is the system's
    classical reductio rule, not ordinary negation elimination.

[[[
{¬ A} ∪ Γ ⊢ₙ B     {¬ A} ∪ Γ ⊢ₙ ¬ B
------------------------------- ¬E / N_negElim
Γ ⊢ₙ A
]]]

    Since [B] does not occur in the conclusion, it may not be inferable when
    applying the constructor.  Write, for example,
    [apply (N_negElim (B := B))].

    *** Conjunction -- Rules 7 and 8

    Introduction combines two derivations with the same open assumptions.
    The two elimination rules project either component of a conjunction.

[[[
Γ ⊢ₙ A     Γ ⊢ₙ B
----------------- ∧I / N_conjIntro
Γ ⊢ₙ A ∧ B

Γ ⊢ₙ A ∧ B
------------- ∧E-left / N_conjElimLeft
Γ ⊢ₙ A

Γ ⊢ₙ A ∧ B
------------- ∧E-right / N_conjElimRight
Γ ⊢ₙ B
]]]

    Thus a goal [Γ ⊢ₙ A ∧ B] suggests [apply N_conjIntro], whereas an
    available derivation of [A ∧ B] can be consumed by one of the projections.

    *** Disjunction -- Rules 5 and 6

    Either disjunct is enough to introduce a disjunction.  Elimination is
    proof by cases: derive the same [C] once under temporary assumption [A]
    and once under temporary assumption [B].

[[[
Γ ⊢ₙ A
------------- ∨I-left / N_disjIntroLeft
Γ ⊢ₙ A ∨ B

Γ ⊢ₙ B
------------- ∨I-right / N_disjIntroRight
Γ ⊢ₙ A ∨ B

Γ ⊢ₙ A ∨ B     {A} ∪ Γ ⊢ₙ C     {B} ∪ Γ ⊢ₙ C
------------------------------------------- ∨E / N_disjElim
Γ ⊢ₙ C
]]]

    Notice that [C] must be identical in the two branches.  Applying
    [N_disjElim] therefore creates a major-premise goal and two case goals.

    *** Implication -- Rules 3 and 4

    Implication introduction is conditional proof: assume [A], derive [B],
    then discharge that temporary assumption.  Implication elimination is
    modus ponens.

[[[
{A} ∪ Γ ⊢ₙ B
------------- →I / N_impIntro
Γ ⊢ₙ A → B

Γ ⊢ₙ A → B     Γ ⊢ₙ A
--------------------- →E / N_impElim
Γ ⊢ₙ B
]]]

    In the first tree, [A] occurs above but not below the bar: that change of
    context is how discharge is represented.  In the second, the intermediate
    antecedent [A] sometimes needs to be supplied explicitly as
    [(A := A)].

    *** Biconditional -- Rules 9 and 10

    To introduce [A ↔ B], prove both directions by conditional reasoning.
    Elimination uses the biconditional in either direction.

[[[
{A} ∪ Γ ⊢ₙ B     {B} ∪ Γ ⊢ₙ A
----------------------------- ↔I / N_iffIntro
Γ ⊢ₙ A ↔ B

Γ ⊢ₙ A ↔ B     Γ ⊢ₙ A
--------------------- ↔E-left / N_iffElimLeft
Γ ⊢ₙ B

Γ ⊢ₙ A ↔ B     Γ ⊢ₙ B
--------------------- ↔E-right / N_iffElimRight
Γ ⊢ₙ A
]]]

    The constructor names say which input is used: "left" consumes [A] to
    obtain [B], and "right" consumes [B] to obtain [A].

    These ten textbook rule schemes become thirteen constructors because
    disjunction introduction, conjunction elimination, and biconditional
    elimination each have left and right forms. *)

(** Familiar aliases. *)
Definition N_mp {Γ : Context} {A B : formula} :
  Γ ⊢ₙ (A → B) -> Γ ⊢ₙ A -> Γ ⊢ₙ B :=
  N_impElim (Γ := Γ) (A := A) (B := B).
Definition N_byContradiction {Γ : Context} {A B : formula} :
  ({[¬ A]} ∪ Γ) ⊢ₙ B -> ({[¬ A]} ∪ Γ) ⊢ₙ (¬ B) -> Γ ⊢ₙ A :=
  N_negElim (Γ := Γ) (A := A) (B := B).

(** Closes a goal whose conclusion is literally among the assumptions. *)
Ltac n_assumption := apply N_assumption; set_solver.

(** ** From a paper proof to Rocq

    The paper derivation

    [[
          A ⊢ A
        -------- →I
          ⊢ A → A
    ]]

    becomes one application of implication introduction followed by the
    assumption rule. *)

Example N_identity_walkthrough (A : formula) : (∅ : Context) ⊢ₙ (A → A).
Proof.
  apply N_impIntro.
  n_assumption.
Qed.

(** If an elimination rule contains an intermediate formula that is not fixed
    by the goal, name it explicitly, for example
    [apply (N_impElim (A := A))].  [About N_impElim.] displays the full rule in
    the editor. *)

(** ** Metatheorems from Section 2.5 *)

Lemma N_extend_context (Γ Δ : Context) (X : formula) :
  Γ ⊆ Δ -> ({[X]} ∪ Γ) ⊆ ({[X]} ∪ Δ).
Proof. set_solver. Qed.

(** Theorem 2.5 (增加前提律).  The book states the one-premise form;
    the subset formulation is more convenient and immediately implies it. *)
Theorem N_weaken (Γ Δ : Context) (A : formula) :
  Γ ⊆ Δ -> Γ ⊢ₙ A -> Δ ⊢ₙ A.
Proof.
  intros Hsub d. revert Δ Hsub.
  induction d as
    [Γ A h
    |Γ A B dB IHB dNB IHNB
    |Γ A B dA IHA dB IHB
    |Γ A B dAB IHAB
    |Γ A B dAB IHAB
    |Γ A B dA IHA
    |Γ A B dB IHB
    |Γ A B C dAB IHAB dAC IHAC dBC IHBC
    |Γ A B dB IHB
    |Γ A B dAB IHAB dA IHA
    |Γ A B dAB IHAB dBA IHBA
    |Γ A B dIff IHIff dA IHA
    |Γ A B dIff IHIff dB IHB]; intros Δ Hsub.
  - apply N_assumption. set_solver.
  - apply (N_negElim (B := B)).
    + apply IHB. now apply N_extend_context.
    + apply IHNB. now apply N_extend_context.
  - apply N_conjIntro; [now apply IHA | now apply IHB].
  - apply (N_conjElimLeft (B := B)). now apply IHAB.
  - apply (N_conjElimRight (A := A)). now apply IHAB.
  - apply N_disjIntroLeft. now apply IHA.
  - apply N_disjIntroRight. now apply IHB.
  - apply (N_disjElim (A := A) (B := B)).
    + now apply IHAB.
    + apply IHAC. now apply N_extend_context.
    + apply IHBC. now apply N_extend_context.
  - apply N_impIntro. apply IHB. now apply N_extend_context.
  - apply (N_impElim (A := A)); [now apply IHAB | now apply IHA].
  - apply N_iffIntro.
    + apply IHAB. now apply N_extend_context.
    + apply IHBA. now apply N_extend_context.
  - apply (N_iffElimLeft (A := A)); [now apply IHIff | now apply IHA].
  - apply (N_iffElimRight (B := B)); [now apply IHIff | now apply IHB].
Qed.

Corollary N_add_premise (Γ : Context) (A B : formula) :
  Γ ⊢ₙ A -> ({[B]} ∪ Γ) ⊢ₙ A.
Proof. apply N_weaken. set_solver. Qed.

(** Theorem 2.6 (传递律), in a general substitution form.  Every open
    assumption of the second derivation is replaced by a derivation from Γ. *)
Theorem N_substitution (Γ Δ : Context) (A : formula) :
  (forall B, B ∈ Δ -> Γ ⊢ₙ B) -> Δ ⊢ₙ A -> Γ ⊢ₙ A.
Proof.
  intros Hprem d. revert Γ Hprem.
  induction d as
    [Δ A h
    |Δ A B dB IHB dNB IHNB
    |Δ A B dA IHA dB IHB
    |Δ A B dAB IHAB
    |Δ A B dAB IHAB
    |Δ A B dA IHA
    |Δ A B dB IHB
    |Δ A B C dAB IHAB dAC IHAC dBC IHBC
    |Δ A B dB IHB
    |Δ A B dAB IHAB dA IHA
    |Δ A B dAB IHAB dBA IHBA
    |Δ A B dIff IHIff dA IHA
    |Δ A B dIff IHIff dB IHB]; intros Γ Hprem.
  - now apply Hprem.
  - apply (N_negElim (B := B)).
    + apply IHB. intros C HC. destruct (decide (C = Neg A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHNB. intros C HC. destruct (decide (C = Neg A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply N_conjIntro; [now apply IHA | now apply IHB].
  - apply (N_conjElimLeft (B := B)). now apply IHAB.
  - apply (N_conjElimRight (A := A)). now apply IHAB.
  - apply N_disjIntroLeft. now apply IHA.
  - apply N_disjIntroRight. now apply IHB.
  - apply (N_disjElim (A := A) (B := B)).
    + now apply IHAB.
    + apply IHAC. intros D HD. destruct (decide (D = A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHBC. intros D HD. destruct (decide (D = B)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply N_impIntro. apply IHB.
    intros C HC. destruct (decide (C = A)) as [->|Hne].
    + n_assumption.
    + apply N_add_premise, Hprem. set_solver.
  - apply (N_impElim (A := A)); [now apply IHAB | now apply IHA].
  - apply N_iffIntro.
    + apply IHAB. intros C HC. destruct (decide (C = A)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
    + apply IHBA. intros C HC. destruct (decide (C = B)) as [->|Hne].
      * n_assumption.
      * apply N_add_premise, Hprem. set_solver.
  - apply (N_iffElimLeft (A := A)); [now apply IHIff | now apply IHA].
  - apply (N_iffElimRight (B := B)); [now apply IHIff | now apply IHB].
Qed.

Corollary N_cut (Γ : Context) (A B : formula) :
  Γ ⊢ₙ A -> ({[A]} ∪ Γ) ⊢ₙ B -> Γ ⊢ₙ B.
Proof.
  intros dA dB. eapply N_substitution; [|exact dB].
  intros C HC. destruct (decide (C = A)) as [->|Hne].
  - exact dA.
  - apply N_assumption. set_solver.
Qed.

(** ** Chapter summary

    Primitive constructors are the inference rules students should use in
    first proofs.  [N_weaken] formalizes 增加前提律, while [N_substitution] and
    [N_cut] formalize replacement of open assumptions by derivations.  The next
    chapter packages frequently repeated proof trees as derived rules. *)
