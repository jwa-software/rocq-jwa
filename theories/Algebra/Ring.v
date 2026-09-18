(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Ring.
  Class T (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
          (mul : A -> A -> A) (one : A)
    : Prop :=
    { add_group  :: AbelianGroup.T A add zero negate
    ; mul_monoid :: Monoid mul one
    ; left_distributivity
        : forall (x : A) (y : A) (z : A), mul x (add y z) = add (mul x y) (mul x z)
    ; right_distributivity
        : forall (x : A) (y : A) (z : A), mul (add y z) x = add (mul y x) (mul z x) }.
End Ring.

(* The instance hints that [::] declares are scoped to the module; this
 * lets them out while the names stay qualified.
 *)
Export (hints) Ring.
