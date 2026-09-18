(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Transitive.

Class PartialOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive     R
  ; antisymmetry :: Antisymmetric R
  ; transitivity :: Transitive    R }.
