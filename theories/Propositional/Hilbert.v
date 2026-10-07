(** * System P: Hilbert-style propositional calculus *)

From Stdlib Require Import String List.
From stdpp Require Import gmap strings sets tactics.
From LogicCourse.Propositional Require Import Syntax.

Import ListNotations.

Inductive pformula : Type :=
| PAtom : string -> pformula
| PNeg : pformula -> pformula
| PImp : pformula -> pformula -> pformula.

Global Instance pformula_eq_dec : EqDecision pformula.
Proof. solve_decision. Defined.

Fixpoint pformula_to_tree (A : pformula) : gen_tree string :=
  match A with
  | PAtom p => GenLeaf p
  | PNeg B => GenNode 0 [pformula_to_tree B]
  | PImp B C => GenNode 1 [pformula_to_tree B; pformula_to_tree C]
  end.

Fixpoint pformula_of_tree (t : gen_tree string) : option pformula :=
  match t with
  | GenLeaf p => Some (PAtom p)
  | GenNode 0 [u] => option_map PNeg (pformula_of_tree u)
  | GenNode 1 [u; v] =>
      match pformula_of_tree u, pformula_of_tree v with
      | Some B, Some C => Some (PImp B C) | _, _ => None end
  | _ => None
  end.

Lemma pformula_tree_round_trip A :
  pformula_of_tree (pformula_to_tree A) = Some A.
Proof.
  induction A; simpl;
    repeat match goal with H : pformula_of_tree (pformula_to_tree _) = _ |- _ => rewrite H end;
    reflexivity.
Qed.

Global Instance pformula_countable : Countable pformula :=
  inj_countable pformula_to_tree pformula_of_tree pformula_tree_round_trip.

Definition PContext : Type := gset pformula.

Declare Scope P_scope.
Delimit Scope P_scope with P.
Notation "¬ A" := (PNeg A) (at level 75, right associativity) : P_scope.
Notation "A → B" := (PImp A B) (at level 99, right associativity) : P_scope.

(** Section 2.6 treats the remaining connectives as metalinguistic
    abbreviations in P. *)
Definition PDisj (A B : pformula) : pformula := PImp (PNeg A) B.
Definition PConj (A B : pformula) : pformula := PNeg (PImp A (PNeg B)).
Definition PIff (A B : pformula) : pformula :=
  PConj (PImp A B) (PImp B A).

Notation "A ∨ B" := (PDisj A B) (at level 85, right associativity) : P_scope.
Notation "A ∧ B" := (PConj A B) (at level 80, right associativity) : P_scope.
Notation "A ↔ B" := (PIff A B) (at level 95, no associativity) : P_scope.

Fixpoint p_to_n (A : pformula) : formula :=
  match A with
  | PAtom p => Atom p
  | PNeg B => Neg (p_to_n B)
  | PImp B C => Imp (p_to_n B) (p_to_n C)
  end.

Open Scope P_scope.

(** Formula and context indices are implicit whenever the conclusion or the
    derivation premises determine them.  Named arguments remain available for
    the occasional underconstrained use of modus ponens. *)
Inductive PDerivation : PContext -> pformula -> Prop :=
| P_premise {Γ : PContext} {A : pformula} :
    A ∈ Γ -> PDerivation Γ A
| P_ax1 {Γ : PContext} {A B : pformula} :
    PDerivation Γ (A → (B → A))
| P_ax2 {Γ : PContext} {A B C : pformula} :
    PDerivation Γ ((A → (B → C)) → ((A → B) → (A → C)))
| P_ax3 {Γ : PContext} {A B : pformula} :
    PDerivation Γ ((¬ A → ¬ B) → (B → A))
| P_mp {Γ : PContext} {A B : pformula} :
    PDerivation Γ A -> PDerivation Γ (A → B) -> PDerivation Γ B.

Notation "Γ ⊢ₚ A" := (PDerivation Γ A) (at level 74).

Ltac p_premise := apply P_premise; set_solver.

(** The standard derivation of [A → A].  Under Curry--Howard this is the
    identity combinator [I]; the proof below is the typed version of
    [I = S K K], with A1 playing [K] and A2 playing [S]. *)
Theorem P_identity (Γ : PContext) (A : pformula) : Γ ⊢ₚ (A → A).
Proof.
  pose proof (P_ax1 (Γ := Γ) (A := A) (B := A → A)) as line1.
  pose proof (P_ax1 (Γ := Γ) (A := A) (B := A)) as line2.
  pose proof (P_ax2 (Γ := Γ) (A := A) (B := A → A) (C := A)) as line3.
  pose proof (P_mp line1 line3) as line4.
  exact (P_mp line2 line4).
Qed.

(** ** Metatheorems from Section 2.6 *)

Theorem P_weaken (Γ Δ : PContext) (A : pformula) :
  Γ ⊆ Δ -> Γ ⊢ₚ A -> Δ ⊢ₚ A.
Proof.
  intros Hsub d. induction d.
  - apply P_premise. set_solver.
  - apply P_ax1.
  - apply P_ax2.
  - apply P_ax3.
  - eapply P_mp; eauto.
Qed.

(** Theorem 2.10, the deduction theorem.

    There is a useful computational reading of this proof.  Regard a
    derivation from the distinguished assumption [A] as a typed combinatory
    term with one free variable [a : A].  The induction below removes that
    variable, producing a term of type [A → B].  It is exactly the usual
    bracket-abstraction algorithm from lambda calculus to SKI:

    - [[A] A = I]: the distinguished premise becomes [P_identity];
    - [[A] C = K C] when [C] does not depend on [A]: A1 lifts a premise or
      axiom to [A → C];
    - [[A] (f x) = S ([A] f) ([A] x)]: the MP case combines its two induction
      hypotheses with A2.

    Thus the apparently technical induction is a proof compiler: it turns a
    proof using the distinguished open assumption [A] into an SKI expression
    in which that assumption has been abstracted (the background [Γ] remains).
    A3 is merely another closed constant and is therefore handled by [K], in
    exactly the same way as A1 and A2. *)
Lemma P_deduction_aux (Δ : PContext) (B : pformula) (d : Δ ⊢ₚ B) :
  forall (Γ : PContext) (A : pformula),
    Δ = ({[A]} ∪ Γ) -> Γ ⊢ₚ (A → B).
Proof.
  induction d as
    [Δ C HC
    |Δ C D
    |Δ C D E
    |Δ C D
    |Δ C D dC IHC dCD IHCD]; intros Γ A Heq; subst Δ.
  - (** Premise: the distinguished premise becomes [I]; every other premise
        is constant with respect to [A] and is lifted by [K]. *)
    destruct (decide (C = A)) as [->|Hne].
    + apply P_identity.
    + apply (P_mp (A := C)).
      * apply P_premise. set_solver.
      * apply P_ax1.
  - (** A1, A2 and A3 are closed constants, so bracket abstraction uses [K]. *)
    eapply (P_mp (A := C → (D → C))); [apply P_ax1 | apply P_ax1].
  - eapply (P_mp (A := (C → (D → E)) → ((C → D) → (C → E))));
      [apply P_ax2 | apply P_ax1].
  - eapply (P_mp (A := (¬ C → ¬ D) → (D → C)));
      [apply P_ax3 | apply P_ax1].
  - (** MP is application.  A2 is [S], distributing the abstracted argument
        [A] to both the function proof and its input proof. *)
    apply (P_mp (A := A → C)).
    + apply IHC. reflexivity.
    + apply (P_mp (A := A → (C → D))).
      * apply IHCD. reflexivity.
      * apply P_ax2.
Qed.

Theorem P_deduction (Γ : PContext) (A B : pformula) :
  ({[A]} ∪ Γ) ⊢ₚ B -> Γ ⊢ₚ (A → B).
Proof. intro d. eapply P_deduction_aux; [exact d|reflexivity]. Qed.

(** Theorem 2.11, the converse of the deduction theorem. *)
Theorem P_deduction_inverse (Γ : PContext) (A B : pformula) :
  Γ ⊢ₚ (A → B) -> ({[A]} ∪ Γ) ⊢ₚ B.
Proof.
  intro d.
  apply (P_mp (A := A)).
  - apply P_premise. set_solver.
  - apply (P_weaken Γ ({[A]} ∪ Γ) (A → B)).
    + set_solver.
    + exact d.
Qed.

Theorem P_substitution (Γ Δ : PContext) (A : pformula) :
  (forall B, B ∈ Δ -> Γ ⊢ₚ B) -> Δ ⊢ₚ A -> Γ ⊢ₚ A.
Proof.
  intros Hprem d. induction d.
  - now apply Hprem.
  - apply P_ax1.
  - apply P_ax2.
  - apply P_ax3.
  - eapply P_mp; eauto.
Qed.

(** Theorem 2.12, specialized to one temporary premise. *)
Corollary P_cut (Γ : PContext) (A B : pformula) :
  Γ ⊢ₚ A -> ({[A]} ∪ Γ) ⊢ₚ B -> Γ ⊢ₚ B.
Proof.
  intros dA dB. eapply P_substitution; [|exact dB].
  intros C HC. destruct (decide (C = A)) as [->|Hne].
  - exact dA.
  - apply P_premise. set_solver.
Qed.
