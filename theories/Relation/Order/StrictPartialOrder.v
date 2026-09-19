(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Transitive.

Class StrictPartialOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity :: Irreflexive R
  ; transitivity  :: Transitive  R }.
