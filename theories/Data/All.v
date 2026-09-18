(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Data.All].
 *)

(* Without [Core.All] a client of this umbrella has no [->]. *)
From jwa Require Export Core.All.
From jwa Require Export Relation.All.
From jwa Require Export Structures.All.

(* [Export] so a client writes [Option A], not [Option.Option A]. *)
From jwa Require Export Data.Bool.
From jwa Require Export Data.Comparison.
From jwa Require Export Data.Empty.
From jwa Require Export Data.Integer.
From jwa Require Export Data.List.
From jwa Require Export Data.Nat.
From jwa Require Export Data.NatWithZero.
From jwa Require Export Data.Option.
From jwa Require Export Data.Pair.
From jwa Require Export Data.Sum.
From jwa Require Export Data.Unit.
