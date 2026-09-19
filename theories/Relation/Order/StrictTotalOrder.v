(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Order.StrictPartialOrder.
From jwa Require Import Relation.Trichotomous.

Class StrictTotalOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { strict_partial_order :: StrictPartialOrder R
  ; trichotomy           :: Trichotomous       R }.
