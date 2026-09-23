(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* The tactic language is Ltac2, a compiled plugin rather than Rocq syntax.
 * [Ltac2.Init] loads it and makes Ltac2 the proof mode of every file that
 * imports this one; [Export] is what carries both that far.
 *
 * Only the core is loaded. The syntax of Rocq's own tactics -- [intros],
 * [exact] and the rest -- lives in [Ltac2.Notations], which is not imported,
 * so a tactic is written here only once this library has declared it.
 *)
From Ltac2 Require Export Init.
