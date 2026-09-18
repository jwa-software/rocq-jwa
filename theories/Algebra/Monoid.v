(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Monoid {A : Type} (op : A -> A -> A) (identity : A) : Prop :=
  { semigroup
    :: Semigroup op
  ; identity
    : forall (x : A),
      op identity x = x /\ op x identity = x }.
