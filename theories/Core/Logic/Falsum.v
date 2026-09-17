(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Falsum is the false proposition: no constructor, so no proof.
   [discriminate] looks this up by registered name and reports
   [not found in table: core.False.type] without it. *)

Inductive Falsum : Prop := .

Register Falsum as core.False.type.
