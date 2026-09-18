(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

Class Transitive {A : Type} (R : A -> A -> Prop) : Prop :=
  { transitivity
    : forall (x : A) (y : A) (z : A), R x y -> R y z -> R x z }.
