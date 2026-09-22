(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Core.Logic]: re-exports every connective, so a client
 * imports them all with [From jwa Require Import Core.Logic.All].
 *)

(* [Require Export], not a plain [Require]: a notation reaches a client only
 * through [Import].
 *)
From jwa Require Export Core.Logic.Abjunction.
From jwa Require Export Core.Logic.Biconditional.
From jwa Require Export Core.Logic.Conditional.
From jwa Require Export Core.Logic.Conjunction.
From jwa Require Export Core.Logic.Disjunction.
From jwa Require Export Core.Logic.Exists.
From jwa Require Export Core.Logic.Falsum.
From jwa Require Export Core.Logic.Negation.
From jwa Require Export Core.Logic.Sejunction.
From jwa Require Export Core.Logic.Syllogism.
From jwa Require Export Core.Logic.Verum.

(* Each connective only [Import]s [Core.Notations], so the open scope reaches
 * a client of this umbrella only from here.
 *)
From jwa Require Export Core.Notations.
