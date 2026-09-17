(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Structures]: re-exports every module of the layer, so a
   client imports the whole layer with [From jwa Require Import Structures.All]. *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
   client of this umbrella only from here. *)
From jwa Require Export Core.All.

From jwa Require Export Structures.Class.
From jwa Require Export Structures.Semigroup.
From jwa Require Export Structures.Monoid.
From jwa Require Export Structures.Commutative.
From jwa Require Export Structures.Cancellative.
From jwa Require Export Structures.Functor.
