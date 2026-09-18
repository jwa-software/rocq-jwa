(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
 * carries [->] and [=], [Structures.Class] the hint database, and
 * [Structures.Commutative] and [Structures.Monoid] the classes the two
 * operations satisfy on their own.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Monoid.

(* The module is the prefix: the class reads [Semiring.T] and its fields
 * [Semiring.add_monoid], [Semiring.left_distributivity] and so on.
 *)
Module Semiring.
  (* Two operations on one type: [add] a commutative monoid with [zero],
   * [mul] a monoid with [one], [mul] distributing over [add] on both sides
   * and [zero] absorbing under [mul] on both sides. Absorption is stated,
   * not derived: without inverses for [add] it does not follow from the
   * rest. The [::] on the three class fields declares each an instance as
   * well as a projection; the two monoids are told apart by their
   * operation.
   *)
  Class T (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
    : Prop :=
    { add_monoid      :: Monoid.T A add zero
    ; add_commutative :: Commutative.T A add
    ; mul_monoid      :: Monoid.T A mul one
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
