(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Relations.Irreflexive.
From jwa Require Import Relations.Transitive.
From jwa Require Import Structures.Class.

Class StrictOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity :: Irreflexive R
  ; transitivity  :: Transitive  R}.
