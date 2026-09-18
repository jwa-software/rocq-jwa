(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Algebra.All] would be circular from inside [Algebra]; [Core.All]
 * carries [->] and [=], [Core.Class] the hint database, and
 * [Algebra.AbelianGroup] and [Algebra.Monoid] the classes the two
 * operations satisfy on their own.
 *)
From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

(* The module is the prefix: the class reads [Ring.T] and its fields
 * [Ring.add_group], [Ring.mul_monoid], [Ring.left_distributivity] and
 * [Ring.right_distributivity].
 *)
Module Ring.
  (* Two operations on one type: [add] an abelian group with [zero] and
   * [negate], [mul] a monoid with [one], [mul] distributing over [add] on
   * both sides. Absorption is not stated: with inverses for [add] it
   * follows from distributivity. The [::] on the two class fields declares
   * each an instance as well as a projection.
   *)
  Class T (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
          (mul : A -> A -> A) (one : A)
    : Prop :=
    { add_group  :: AbelianGroup.T A add zero negate
    ; mul_monoid :: Monoid.T A mul one
    ; left_distributivity
        : forall (x : A) (y : A) (z : A), mul x (add y z) = add (mul x y) (mul x z)
    ; right_distributivity
        : forall (x : A) (y : A) (z : A), mul (add y z) x = add (mul y x) (mul z x) }.
End Ring.

(* The instance hints that [::] declares are scoped to the module; this
 * lets them out while the names stay qualified.
 *)
Export (hints) Ring.
