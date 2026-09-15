(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [discriminate] looks this up by registered name and reports
   [not found in table: core.False.type] without it. *)

Inductive False : Prop := .

Register False as core.False.type.
