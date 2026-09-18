(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Relations]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Relations.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Relations.Antisymmetric.
From jwa Require Export Relations.Equivalence.
From jwa Require Export Relations.Irreflexive.
From jwa Require Export Relations.PartialOrder.
From jwa Require Export Relations.Reflexive.
From jwa Require Export Relations.StrictOrder.
From jwa Require Export Relations.Symmetric.
From jwa Require Export Relations.Total.
From jwa Require Export Relations.TotalOrder.
From jwa Require Export Relations.Transitive.
