(** Interface checks for Chapter 3. *)
From LogicCourse.FirstOrder Require Import
  Syntax NaturalDeduction Hilbert Connections Semantics Metatheory.
From LogicCourse.Solutions Require Import Selected.

Check free_for.
Check NL_weaken.
Check NL_cut.
Check K_generalize.
Check K_deduction.
Check semantic_consequence.
Check selected_NL_specialization.
Print Assumptions selected_NL_specialization.
