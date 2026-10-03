(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module AbelianMonoid. (* AbelianMonoid *)

Class T {A : Type} (op : A -> A -> A) (identity : A) : Prop :=
  { monoid
    :: Monoid op identity
  ; commutative
    :: Commutative op }.

Abbreviation AbelianMonoid := T.

End AbelianMonoid. (* AbelianMonoid *)

Abbreviation AbelianMonoid := AbelianMonoid.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance AbelianMonoid.monoid.
#[export] Existing Instance AbelianMonoid.commutative.
