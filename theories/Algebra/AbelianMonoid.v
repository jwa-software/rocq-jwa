(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class AbelianMonoid {A : Type} (op : A -> A -> A) (identity : A) : Prop :=
  { monoid
    :: Monoid op identity
  ; commutative
    :: Commutative op }.
