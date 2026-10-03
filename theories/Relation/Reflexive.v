(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Reflexive. (* Reflexive *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity
    : forall (x : A) . R x x }.

Abbreviation Reflexive := T.

End Reflexive. (* Reflexive *)

Abbreviation Reflexive := Reflexive.T.
