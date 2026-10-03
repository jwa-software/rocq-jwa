(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Irreflexive. (* Irreflexive *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity
    : forall (x : A) . ~ R x x }.

Abbreviation Irreflexive := T.

End Irreflexive. (* Irreflexive *)

Abbreviation Irreflexive := Irreflexive.T.
