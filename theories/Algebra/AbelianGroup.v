(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module AbelianGroup. (* AbelianGroup *)

Class T {A : Type} (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
  { group
    :: Group op identity inverse
  ; commutative
    :: Commutative op }.

Abbreviation AbelianGroup := T.

End AbelianGroup. (* AbelianGroup *)

Abbreviation AbelianGroup := AbelianGroup.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance AbelianGroup.group.
#[export] Existing Instance AbelianGroup.commutative.
