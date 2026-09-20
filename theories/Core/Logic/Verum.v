(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Verum is the true proposition, with [I] its one proof. [discriminate]
 * looks both of these up by registered name and reports
 * [not found in table: core.True.type] without them.
 *)

Inductive Verum : Prop :=
  | I : Verum.

Register Verum as core.True.type.
Register I as core.True.I.
