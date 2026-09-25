(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Total.

Class TotalOrder {A : Type} (R : A -> A -> Prop) : Prop :=
  { partial_order :: PartialOrder R
  ; totality      :: Total        R }.
