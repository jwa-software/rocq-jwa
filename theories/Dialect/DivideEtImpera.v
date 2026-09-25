(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Control Std.

(* divide et impera    turns a goal whose type has one constructor into one
 *                     goal per premise of it, as Rocq's [split] does
 *
 * Latin for "divide and rule": the goal is divided here, and each part is
 * proved after. [A /\ B] leaves [A] and [B]; [P <-> Q] leaves [P -> Q] and
 * [Q -> P]. A tactic notation, not a term notation, so [divide], [et] and
 * [impera] stay free as names.
 *)
Ltac2 Notation "divide" "et" "impera" :=
  Control.enter (fun () => Std.split false Std.NoBindings).
