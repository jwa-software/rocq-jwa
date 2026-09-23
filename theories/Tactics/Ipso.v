(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* ipso <H>    closes the goal with <H>, exactly as [exact <H>] does
 *
 * Latin for "by itself": the proof given is the whole of it. The preferred
 * use names the closing proof [facto], so the step reads [ipso facto], "by
 * the fact itself". A tactic notation, not a term notation, so [ipso] stays
 * free as a name.
 *)
Tactic Notation "ipso" uconstr(H) :=
  exact H.
