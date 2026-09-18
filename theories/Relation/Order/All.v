(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Relation.Order]: re-exports the three order classes, so
 * a client imports them with [From jwa Require Import Relation.Order.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Relation.Order.PartialOrder.
From jwa Require Export Relation.Order.StrictOrder.
From jwa Require Export Relation.Order.TotalOrder.
