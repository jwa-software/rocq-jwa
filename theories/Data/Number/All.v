(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Number]: re-exports the three number types, so a
 * client imports them with [From jwa Require Import Data.Number.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Data.Number.Integer.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.NatWithZero.
