(** * A Minimal Rocq Primer

    This chapter introduces only the fragment of Rocq needed in the logic
    course.  It is not a general programming-language tutorial.

    ** Data, constructors, and computation

    An [Inductive] declaration introduces data by listing all ways to build a
    value.  Pattern matching then defines functions by cases. *)

From Stdlib Require Import Bool Arith.
From stdpp Require Import gmap sets tactics.

Inductive traffic_light : Type := red | amber | green.

Definition may_go (light : traffic_light) : bool :=
  match light with green => true | _ => false end.

Compute may_go green.

(** A Boolean is executable data.  A proposition is a statement that may have
    a proof.  The distinction will reappear when propositional semantics uses
    [bool], while derivability judgments live in [Prop]. *)

Example green_means_go : may_go green = true.
Proof. reflexivity. Qed.

(** ** Reading a proof script

    [Goal] states the proposition to prove.  [intros] moves universally
    quantified variables and implications into the context.  [exact] supplies
    a proof term, while [apply] works backwards from a theorem or constructor.
    [Qed] checks and records the completed proof. *)

Goal forall P : Prop, P -> P.
Proof.
  intros P proof_of_P.
  exact proof_of_P.
Qed.

(** ** Finite contexts

    The course represents a finite set of assumptions by std++'s [gset].
    Singleton notation, union, membership, and subset are the operations used
    most often in derivation rules. *)

Example finite_set_warmup : (2 : nat) ∈ ({[1; 2]} : gset nat).
Proof. set_solver. Qed.

(** ** Implicit arguments

    Braces in a declaration mark arguments that Rocq should reconstruct from
    the goal or from explicit proof arguments.  Use [About name.] in VSRocq to
    display the complete type when elaboration is surprising. *)

Definition keep_proof {P : Prop} (p : P) : P := p.

Check keep_proof.

(** ** Scopes and object-language symbols

    Later chapters reuse familiar symbols such as [¬], [∧], and [→] for
    several deep embeddings.  Separate scopes ensure that the same printed
    symbol can denote different constructors without ambiguity.  Always open
    the scope belonging to the system used in the current chapter.

    ** Chapter summary

    Students should now be able to run a computation, read a small goal, apply
    a constructor, recognize an implicit argument, and manipulate a finite
    context.  These are the only Rocq prerequisites assumed below. *)
