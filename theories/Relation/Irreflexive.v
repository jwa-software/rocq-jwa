(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

Class Irreflexive {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity
    : forall (x : A), ~ R x x }.
