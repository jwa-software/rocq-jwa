(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Relations.Antisymmetric.
From jwa Require Import Relations.Reflexive.
From jwa Require Import Relations.Transitive.
From jwa Require Import Structures.Class.

Class PartialOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive     R
  ; antisymmetry :: Antisymmetric R
  ; transitivity :: Transitive    R }.
