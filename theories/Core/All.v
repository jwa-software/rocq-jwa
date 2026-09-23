(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Core]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Core.All].
 *)

(* [Require Export], not a plain [Require]: a notation and an open scope reach
 * a client only through [Import], so qualified access would deliver nothing.
 *
 * [Dialect.All] is exported too, though it is a layer of its own: a file that
 * takes [Core] writes its proofs, and without the dialect it would fall back
 * to Rocq's default proof mode, where every built-in tactic is open again.
 *)
From jwa Require Export Core.Class.
From jwa Require Export Core.Identity.
From jwa Require Export Core.Logic.All.
From jwa Require Export Core.Notations.
From jwa Require Export Dialect.All.
