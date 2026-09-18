(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Total {A : Type} (R : A -> A -> Prop) : Prop :=
  { totality
    : forall (x : A) (y : A), R x y \/ R y x }.
