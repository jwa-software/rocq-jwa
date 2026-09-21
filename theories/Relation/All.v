(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Relation]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Relation.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Relation.Accessible.
From jwa Require Export Relation.Antisymmetric.
From jwa Require Export Relation.Equivalence.
From jwa Require Export Relation.Irreflexive.
From jwa Require Export Relation.Order.All.
From jwa Require Export Relation.Reflexive.
From jwa Require Export Relation.Symmetric.
From jwa Require Export Relation.Total.
From jwa Require Export Relation.Transitive.
From jwa Require Export Relation.Trichotomous.
From jwa Require Export Relation.WellFounded.
