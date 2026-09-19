(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Trichotomous {A : Type} (R : A -> A -> Prop) : Prop :=
  { trichotomy
    : forall (x : A) (y : A), R x y \/ x = y \/ R y x }.
