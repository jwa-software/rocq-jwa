(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Transitive. (* Transitive *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { transitivity
    : forall (x : A) (y : A) (z : A) . R x y -> R y z -> R x z }.

Abbreviation Transitive := T.

End Transitive. (* Transitive *)

Abbreviation Transitive := Transitive.T.
