(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Commutative. (* Commutative *)

Class T {A : Type} (op : A -> A -> A) : Prop :=
  { commutativity
    : forall (x : A) (y : A) . op x y = op y x }.

Abbreviation Commutative := T.

End Commutative. (* Commutative *)

Abbreviation Commutative := Commutative.T.
