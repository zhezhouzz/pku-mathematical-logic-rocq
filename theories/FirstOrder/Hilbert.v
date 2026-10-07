(** * First-order Hilbert system [K_L] *)

From Stdlib Require Import String.
From stdpp Require Import gmap sets tactics.
From LogicCourse.FirstOrder Require Import Syntax.

Open Scope FOL_scope.

(** All schematic indices are implicit: they are determined by the displayed
    axiom together with its side-condition proof.  Named arguments can be used
    when a substitution is not sufficiently constrained for unification. *)
Inductive KAxiom : formula -> Prop :=
| K_ax1 {A B : formula} : KAxiom (A → (B → A))
| K_ax2 {A B C : formula} :
    KAxiom ((A → (B → C)) → ((A → B) → (A → C)))
| K_ax3 {A B : formula} : KAxiom ((Neg A → Neg B) → (B → A))
| K_ax4 {x : string} {A : formula} {t : term} :
    free_for t x A = true -> KAxiom (Forall x A → substitute x t A)
| K_ax5 {x : string} {A : formula} :
    x ∉ free_variables A -> KAxiom (A → Forall x A)
| K_ax6 {x : string} {A B : formula} :
    KAxiom (Forall x (A → B) → (Forall x A → Forall x B))
| K_ax7 {x : string} {A : formula} :
    KAxiom A -> KAxiom (Forall x A).

(** As in P, all formula and context indices are implicit; an unresolved
    intermediate antecedent can still be selected with [(A := ...)]. *)
Inductive KDerivation : Context -> formula -> Prop :=
| K_premise {Γ : Context} {A : formula} :
    A ∈ Γ -> KDerivation Γ A
| K_axiom {Γ : Context} {A : formula} :
    KAxiom A -> KDerivation Γ A
| K_mp {Γ : Context} {A B : formula} :
    KDerivation Γ A -> KDerivation Γ (A → B) -> KDerivation Γ B.

Notation "Γ ⊢ₖ A" := (KDerivation Γ A) (at level 74).

Ltac k_premise := apply K_premise; set_solver.

Definition K1 (Γ : Context) (A B : formula) : Γ ⊢ₖ (A → (B → A)) :=
  K_axiom (K_ax1 (A := A) (B := B)).
Definition K2 (Γ : Context) (A B C : formula) :
    Γ ⊢ₖ ((A → (B → C)) → ((A → B) → (A → C))) :=
  K_axiom (K_ax2 (A := A) (B := B) (C := C)).
Definition K3 (Γ : Context) (A B : formula) :
    Γ ⊢ₖ ((Neg A → Neg B) → (B → A)) :=
  K_axiom (K_ax3 (A := A) (B := B)).

Definition K4 (Γ : Context) (x : string) (A : formula) (t : term)
    (Hfree : free_for t x A = true) :
    Γ ⊢ₖ (Forall x A → substitute x t A) :=
  K_axiom (K_ax4 (x := x) (A := A) (t := t) Hfree).

Definition K5 (Γ : Context) (x : string) (A : formula)
    (Hfresh : x ∉ free_variables A) : Γ ⊢ₖ (A → Forall x A) :=
  K_axiom (K_ax5 (x := x) (A := A) Hfresh).

Definition K6 (Γ : Context) (x : string) (A B : formula) :
    Γ ⊢ₖ (Forall x (A → B) → (Forall x A → Forall x B)) :=
  K_axiom (K_ax6 (x := x) (A := A) (B := B)).

Definition K7 (Γ : Context) (x : string) (A : formula) (Hax : KAxiom A) :
    Γ ⊢ₖ Forall x A := K_axiom (K_ax7 (x := x) (A := A) Hax).

Theorem K_identity (Γ : Context) (A : formula) : Γ ⊢ₖ (A → A).
Proof.
  pose proof (K1 Γ A (A → A)) as line1.
  pose proof (K1 Γ A A) as line2.
  pose proof (K2 Γ A (A → A) A) as line3.
  pose proof (K_mp line1 line3) as line4.
  exact (K_mp line2 line4).
Qed.

Theorem K_weaken (Γ Δ : Context) (A : formula) :
  Γ ⊆ Δ -> Γ ⊢ₖ A -> Δ ⊢ₖ A.
Proof.
  intros Hsub d. induction d.
  - apply K_premise. set_solver.
  - now apply K_axiom.
  - eapply K_mp; eauto.
Qed.

(** Theorem 3.7 / Property (4): generalization. *)
Theorem K_generalize (Γ : Context) (x : string) (A : formula) :
  (forall B, B ∈ Γ -> x ∉ free_variables B) ->
  Γ ⊢ₖ A -> Γ ⊢ₖ Forall x A.
Proof.
  intros Hfresh d. induction d as
    [Γ B HB
    |Γ B Hax
    |Γ B C dB IHB dBC IHBC].
  - apply (K_mp (A := B)).
    + now apply K_premise.
    + apply K5. now apply Hfresh.
  - apply K_axiom. now apply K_ax7.
  - apply (K_mp (A := Forall x B)).
    + now apply IHB.
    + apply (K_mp (A := Forall x (B → C))).
      * now apply IHBC.
      * apply K6.
Qed.

(** This is the same bracket-abstraction/SKI transformation as
    [P_deduction_aux].  A first-order axiom is treated as a closed constant
    (the [K] case), and MP is transformed by [S]. *)
Lemma K_deduction_aux (Δ : Context) (B : formula) (d : Δ ⊢ₖ B) :
  forall (Γ : Context) (A : formula),
    Δ = ({[A]} ∪ Γ) -> Γ ⊢ₖ (A → B).
Proof.
  induction d as
    [Δ C HC
    |Δ C Hax
    |Δ C D dC IHC dCD IHCD]; intros Γ A Heq; subst Δ.
  - destruct (decide (C = A)) as [->|Hne].
    + apply K_identity.
    + apply (K_mp (A := C)).
      * apply K_premise.
        rewrite elem_of_union, elem_of_singleton in HC.
        destruct HC as [HC|HC]; [contradiction|exact HC].
      * apply K1.
  - apply (K_mp (A := C)).
    + now apply K_axiom.
    + apply K1.
  - apply (K_mp (A := A → C)).
    + apply IHC. reflexivity.
    + apply (K_mp (A := A → (C → D))).
      * apply IHCD. reflexivity.
      * apply K2.
Qed.

(** Theorem 3.8, the deduction theorem for [K_L]. *)
Theorem K_deduction (Γ : Context) (A B : formula) :
  ({[A]} ∪ Γ) ⊢ₖ B -> Γ ⊢ₖ (A → B).
Proof. intro d. eapply K_deduction_aux; [exact d|reflexivity]. Qed.

Theorem K_deduction_inverse (Γ : Context) (A B : formula) :
  Γ ⊢ₖ (A → B) -> ({[A]} ∪ Γ) ⊢ₖ B.
Proof.
  intro d. apply (K_mp (A := A)).
  - apply K_premise. rewrite elem_of_union, elem_of_singleton. now left.
  - apply (K_weaken Γ ({[A]} ∪ Γ) (A → B)).
    + intros C HC. rewrite elem_of_union. now right.
    + exact d.
Qed.

Theorem K_substitution (Γ Δ : Context) (A : formula) :
  (forall B, B ∈ Δ -> Γ ⊢ₖ B) -> Δ ⊢ₖ A -> Γ ⊢ₖ A.
Proof.
  intros Hprem d. induction d.
  - now apply Hprem.
  - now apply K_axiom.
  - eapply K_mp; eauto.
Qed.

Corollary K_cut (Γ : Context) (A B : formula) :
  Γ ⊢ₖ A -> ({[A]} ∪ Γ) ⊢ₖ B -> Γ ⊢ₖ B.
Proof.
  intros dA dB. eapply K_substitution; [|exact dB].
  intros C HC. destruct (decide (C = A)) as [->|Hne].
  - exact dA.
  - apply K_premise. set_solver.
Qed.
