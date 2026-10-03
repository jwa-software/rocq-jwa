(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Symmetric. (* Symmetric *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { symmetry
    : forall (x : A) (y : A) . R x y -> R y x }.

Abbreviation Symmetric := T.

End Symmetric. (* Symmetric *)

Abbreviation Symmetric := Symmetric.T.
