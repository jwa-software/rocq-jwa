(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Relation.Order]: re-exports the four order classes, and
 * the six classes their fields hold, so a client imports them with
 * [From jwa Require Import Relation.Order.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Relation.Order.PartialOrder.
From jwa Require Export Relation.Order.StrictPartialOrder.
From jwa Require Export Relation.Order.StrictTotalOrder.
From jwa Require Export Relation.Order.TotalOrder.

From jwa Require Export Relation.Antisymmetric.
From jwa Require Export Relation.Irreflexive.
From jwa Require Export Relation.Reflexive.
From jwa Require Export Relation.Total.
From jwa Require Export Relation.Transitive.
From jwa Require Export Relation.Trichotomous.
