(** * Small tactics shared by the course files *)

From stdpp Require Import sets tactics.

(** Normalize finite-set expressions without changing their meaning.

    The tactic removes empty unions and adjacent duplicates, and associates
    nested unions to the left.  It rewrites both the goal and hypotheses, so
    it also transports derivations whose context differs only by these set
    identities.  We deliberately do not rewrite by commutativity: orienting
    commutativity as a rewrite rule would loop rather than normalize. *)
Ltac normalize_sets :=
  repeat progress (
    rewrite ?(left_id_L ∅ (∪)) in *;
    rewrite ?(right_id_L ∅ (∪)) in *;
    rewrite ?(idemp_L (∪)) in *;
    rewrite ?(assoc_L (∪)) in *
  ).

(** Course-facing name for the common use case: simplifying a proof context. *)
Ltac normalize_context := normalize_sets.

(** When commutativity is involved there is no useful orientation for a plain
    rewrite rule.  Supply the desired presentation explicitly; [set_solver]
    proves that the old and new contexts are extensionally equal, and
    [replace] transports the judgment.  Example:

      [normalize_context_to ({[A; B]} : Context).] *)
Ltac normalize_context_to normalized :=
  lazymatch goal with
  | |- ?judgment ?current ?conclusion =>
      replace current with normalized by set_solver
  | _ => fail "the goal is not a two-index judgment with a context"
  end.
