(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Semigroup. (* Semigroup *)

Class T {A : Type} (op : A -> A -> A) : Prop :=
  { associativity
    : forall (x : A) (y : A) (z : A) . op (op x y) z = op x (op y z) }.

Abbreviation Semigroup := T.

End Semigroup. (* Semigroup *)

Abbreviation Semigroup := Semigroup.T.
