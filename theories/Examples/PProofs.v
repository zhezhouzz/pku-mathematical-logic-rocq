(** System-P examples. *)

From Stdlib Require Import String.
From stdpp Require Import gmap.
From LogicCourse.Propositional Require Import Hilbert.

Open Scope string_scope.
Open Scope P_scope.

Definition Pp : pformula := PAtom "p".

Example P_identity_again (Γ : PContext) : Γ ⊢ₚ (Pp → Pp).
Proof. apply P_identity. Qed.

Example P_use_premise : ({[Pp]} : PContext) ⊢ₚ Pp.
Proof. p_premise. Qed.
