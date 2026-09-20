(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Semigroup {A : Type} (op : A -> A -> A) : Prop :=
  { associativity
    : forall (x : A) (y : A) (z : A) .
      op (op x y) z = op x (op y z) }.
