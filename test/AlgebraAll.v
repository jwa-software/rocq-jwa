(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.All.

Definition algebra_all_delivers
  : forall (A : Type) (op : A -> A -> A) (e : A),
      Semigroup.T A op -> Monoid.T A op e -> Commutative.T A op
      -> Cancellative.T A op -> ~ Falsum -> Verum
  := fun (A : Type) (op : A -> A -> A) (e : A)
         (_ : Semigroup.T A op) (_ : Monoid.T A op e) (_ : Commutative.T A op)
         (_ : Cancellative.T A op) (_ : ~ Falsum) => I.

Definition algebra_all_delivers_projections
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e) (x : A),
      op e x = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e) (x : A) =>
       Monoid.left_identity x.

Definition algebra_all_delivers_groups_and_rings
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A),
      Group.T A add zero negate -> AbelianGroup.T A add zero negate
      -> Semiring.T A add zero mul one -> Ring.T A add zero negate mul one -> Verum
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A)
         (_ : Group.T A add zero negate) (_ : AbelianGroup.T A add zero negate)
         (_ : Semiring.T A add zero mul one) (_ : Ring.T A add zero negate mul one) => I.

Definition algebra_all_delivers_ring_projection
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A) (r : Ring.T A add zero negate mul one)
           (x : A) (y : A) (z : A),
      mul x (add y z) = add (mul x y) (mul x z)
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A) (r : Ring.T A add zero negate mul one)
         (x : A) (y : A) (z : A) =>
       Ring.left_distributivity x y z.
