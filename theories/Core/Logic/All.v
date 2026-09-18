(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Core.Logic]: re-exports every connective, so a client
   imports them all with [From jwa Require Import Core.Logic.All]. *)

(* Each connective only [Import]s [Core.Notations], so the open scope reaches
   a client of this umbrella only from here. *)
From jwa Require Export Core.Notations.

(* [Require Export], not a plain [Require]: a notation reaches a client only
   through [Import]. *)
From jwa Require Export Core.Logic.Verum.
From jwa Require Export Core.Logic.Falsum.
From jwa Require Export Core.Logic.Conjunction.
From jwa Require Export Core.Logic.Disjunction.
From jwa Require Export Core.Logic.Sejunction.
From jwa Require Export Core.Logic.Negation.
From jwa Require Export Core.Logic.Subjunction.
From jwa Require Export Core.Logic.Bijunction.
From jwa Require Export Core.Logic.Abjunction.
From jwa Require Export Core.Logic.Exists.
