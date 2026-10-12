(** Interface checks for Chapter 2. *)
From LogicCourse.Propositional Require Import
  Syntax Semantics NaturalDeduction DerivedRules Hilbert Connections.
From LogicCourse.Solutions Require Import Selected.

Check truthTable.
Check semantic_consequence.
Check N_weaken.
Check N_cut.
Check P_deduction.
Check selected_N_identity.
Check selected_P_identity.
Print Assumptions selected_N_identity.
Print Assumptions selected_P_identity.
