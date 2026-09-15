(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [discriminate] looks both of these up by registered name and reports
   [not found in table: core.True.type] without them. *)

Inductive True : Prop :=
  | I : True.

Register True as core.True.type.
Register I as core.True.I.
