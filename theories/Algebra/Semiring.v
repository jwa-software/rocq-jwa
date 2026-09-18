(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Semiring.
  Class T (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
    : Prop :=
    { add_monoid      :: Monoid add zero
    ; add_commutative :: Commutative.T A add
    ; mul_monoid      :: Monoid mul one
    ; left_distributivity
        : forall (x : A) (y : A) (z : A), mul x (add y z) = add (mul x y) (mul x z)
    ; right_distributivity
        : forall (x : A) (y : A) (z : A), mul (add y z) x = add (mul y x) (mul z x)
    ; left_absorption  : forall (x : A), mul zero x = zero
    ; right_absorption : forall (x : A), mul x zero = zero }.
End Semiring.

(* The instance hints that [::] declares are scoped to the module; this
 * lets them out while the names stay qualified.
 *)
Export (hints) Semiring.
