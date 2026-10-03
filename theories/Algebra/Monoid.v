(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Monoid. (* Monoid *)

Class T {A : Type} (op : A -> A -> A) (identity : A) : Prop :=
  { semigroup
    :: Semigroup op
  ; identity
    : forall (x : A) . op identity x = x /\ op x identity = x }.

Abbreviation Monoid := T.

End Monoid. (* Monoid *)

Abbreviation Monoid := Monoid.T.

(* A [::] field is an instance only where its module is imported;
 * this line makes it one wherever this file is.
 *)
#[export] Existing Instance Monoid.semigroup.
