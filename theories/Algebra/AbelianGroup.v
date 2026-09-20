(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class AbelianGroup {A : Type} (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
  { group       :: Group op identity inverse
  ; commutative :: Commutative op }.
