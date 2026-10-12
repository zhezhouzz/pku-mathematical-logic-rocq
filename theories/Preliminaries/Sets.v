(** * Sets and Finite Cardinality

    This chapter is a lightweight executable companion to Sections 1.1 and
    1.3.  It recalls only the set operations used later for contexts and free
    variables.  The textbook discusses arbitrary and infinite sets as
    mathematical objects; the executable examples below deliberately use
    finite sets.

    ** Learning objectives

    After this chapter, a reader should be able to read membership and subset
    statements, calculate with union and difference, and explain why a
    context is represented by a finite set rather than a list. *)

From Stdlib Require Import Arith.
From stdpp Require Import gmap fin_sets sets tactics.

(** A [gset A] is a finite set whose elements have decidable equality and a
    countable encoding.  Natural numbers already have both instances. *)

Definition small_primes : gset nat := {[2; 3; 5; 7]}.
Definition small_odds : gset nat := {[1; 3; 5; 7]}.

Example five_is_a_small_prime : 5 ∈ small_primes.
Proof. set_solver. Qed.

Example nine_is_not_a_small_prime : 9 ∉ small_primes.
Proof. set_solver. Qed.

(** Union collects the elements belonging to either set.  Intersection keeps
    the elements belonging to both, and difference removes the second set
    from the first. *)

Example common_small_odd_primes : small_primes ∩ small_odds = {[3; 5; 7]}.
Proof. set_solver. Qed.

Example removing_three : small_primes ∖ {[3]} = {[2; 5; 7]}.
Proof. set_solver. Qed.

(** Subset reasoning is the form used by weakening lemmas later: every
    assumption in the old context must also occur in the new context. *)

Example adding_an_element : small_primes ⊆ {[11]} ∪ small_primes.
Proof. set_solver. Qed.

(** ** Finite cardinality

    The generic [size] operation counts elements of a finite container.
    Duplicate insertions do not change a set, which is exactly the behaviour
    desired for logical assumptions. *)

Compute size small_primes.

Example duplicate_does_not_change_the_set :
  ({[2; 2; 3]} : gset nat) = {[2; 3]}.
Proof. set_solver. Qed.

(** The textbook continues with equipotence and infinite cardinality.  Those
    notions are important mathematics but are not prerequisites for Chapters
    2 and 3, so this executable companion does not build a cardinal-arithmetic
    library.  Bijections are introduced in the next chapter and provide the
    conceptual bridge.

    ** Chapter summary

    Later [Context] and variable-set definitions use the same operations shown
    here.  [set_solver] handles routine rearrangement; it never proves a
    logical inference rule for us. *)
