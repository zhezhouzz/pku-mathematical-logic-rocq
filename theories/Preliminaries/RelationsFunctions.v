(** * Relations and Functions

    This chapter accompanies Section 1.2.  Rocq functions are total by
    construction: applying [f : A -> B] to an element of [A] always returns an
    element of [B].  A binary relation is instead a proposition depending on
    two arguments.

    ** Relations *)

From Stdlib Require Import Arith.

Definition relation (A B : Type) : Type := A -> B -> Prop.

Definition reflexive {A : Type} (R : relation A A) : Prop :=
  forall x, R x x.

Definition symmetric {A : Type} (R : relation A A) : Prop :=
  forall x y, R x y -> R y x.

Definition transitive {A : Type} (R : relation A A) : Prop :=
  forall x y z, R x y -> R y z -> R x z.

Definition equivalent_mod_two : relation nat nat :=
  fun x y => x mod 2 = y mod 2.

Example equivalent_mod_two_reflexive : reflexive equivalent_mod_two.
Proof. intros x. reflexivity. Qed.

Example zero_related_to_two : equivalent_mod_two 0 2.
Proof. reflexivity. Qed.

(** ** Functions and composition *)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall y, exists x, f x = y.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Example successor_is_injective : injective S.
Proof. intros x y H. now injection H. Qed.

Example identity_is_bijective {A : Type} : bijective (fun x : A => x).
Proof.
  split.
  - intros x y H. exact H.
  - intros y. now exists y.
Qed.

(** A bijection is the comparison map used when two sets have the same
    cardinality.  For this course we need the idea, but not a general theory of
    infinite cardinals.

    ** Chapter summary

    Later semantics uses functions for valuations and assignments, and uses
    relations to interpret predicate symbols.  Soundness statements are also
    relations between syntactic derivations and semantic truth. *)
