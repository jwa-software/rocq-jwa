(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Algebra]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Algebra.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Algebra.AbelianGroup.
From jwa Require Export Algebra.Cancellative.
From jwa Require Export Algebra.Commutative.
From jwa Require Export Algebra.Group.
From jwa Require Export Algebra.Monoid.
From jwa Require Export Algebra.Ring.
From jwa Require Export Algebra.Semigroup.
From jwa Require Export Algebra.Semiring.
