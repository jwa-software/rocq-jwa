(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Base.All.

Definition data_base_all_delivers_bool
  : Bool
  := true.

Definition data_base_all_delivers_comparison
  : Comparison
  := Comparison.Eq.

Definition data_base_all_delivers_unit
  : Unit
  := Unit_introduction.

Definition data_base_all_delivers_empty
  : forall (A : Type) . Empty -> A
  := fun (A : Type) . Empty.elimination A.
