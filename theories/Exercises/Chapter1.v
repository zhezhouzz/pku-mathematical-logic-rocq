(** * Chapter 1 Exercises

    These exercises accompany the preliminary material.  Replace [Admitted]
    with a proof while keeping each exercise name unchanged. *)

From Stdlib Require Import Arith.
From stdpp Require Import gmap sets tactics.
From LogicCourse.Preliminaries Require Import
  Sets RelationsFunctions FormalSystems.

(** **** Exercise: 1 star, standard (chapter1_union_membership)

    Prove the displayed membership statement with finite-set reasoning. *)
Example chapter1_union_membership :
  11 ∈ ({[11]} ∪ small_primes : gset nat).
Proof. Admitted.

(** **** Exercise: 2 stars, standard (chapter1_composition_injective)

    Show that a composition of injective functions is injective. *)
Theorem chapter1_composition_injective {A B C : Type}
    (f : A -> B) (g : B -> C) :
  injective f -> injective g -> injective (compose g f).
Proof. Admitted.

(** **** Exercise: 1 star, standard (chapter1_toy_identity)

    Reconstruct the derivation of [A -> A] using the three constructors of the
    tiny formal system. *)
Example chapter1_toy_identity (A : toy_formula) :
  toy_derivation [] (ToyImp A A).
Proof. Admitted.

(** **** Exercise: 2 stars, standard, paper (chapter1_deep_embedding)

    Explain why a truth-table program needs access to an explicit syntax tree
    and therefore cannot use a purely shallow embedding. *)
