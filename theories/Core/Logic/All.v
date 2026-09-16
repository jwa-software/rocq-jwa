(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Core.Logic]: re-exports every connective, so a client
   imports them all with [From jwa Require Import Core.Logic.All]. *)

(* Each connective only [Import]s [Core.Notations], so the open scope reaches
   a client of this umbrella only from here. *)
From jwa Require Export Core.Notations.

(* [Require Export], not a plain [Require]: a notation reaches a client only
   through [Import]. *)
From jwa Require Export Core.Logic.True.
From jwa Require Export Core.Logic.False.
From jwa Require Export Core.Logic.And.
From jwa Require Export Core.Logic.Or.
From jwa Require Export Core.Logic.Not.
From jwa Require Export Core.Logic.Conditional.
From jwa Require Export Core.Logic.Biconditional.
From jwa Require Export Core.Logic.Exists.
