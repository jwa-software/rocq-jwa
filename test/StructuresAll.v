(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Structures.All], imported alone. It forwards [Core.All] as well as
   the five modules, so names from both appear below. *)
From jwa Require Import Structures.All.

Definition structures_all_delivers
  : forall (A : Type) (op : A -> A -> A) (e : A),
      forall (F : Type -> Type),
      Semigroup.T A op -> Monoid.T A op e -> Commutative.T A op
      -> Cancellative.T A op -> Functor.T F -> ~ Falsum -> Verum
  := fun (A : Type) (op : A -> A -> A) (e : A) (F : Type -> Type)
         (_ : Semigroup.T A op) (_ : Monoid.T A op e) (_ : Commutative.T A op)
         (_ : Cancellative.T A op) (_ : Functor.T F) (_ : ~ Falsum) => I.

(* The projections are constants of their modules, so the umbrella has to
   forward them too. *)
Definition structures_all_delivers_projections
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e)
           (x : A),
      op e x = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e)
         (x : A) =>
       Monoid.left_identity x.

(* The four algebraic classes, and one projection of the last. *)
Definition structures_all_delivers_algebra
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A),
      Group.T A add zero negate -> AbelianGroup.T A add zero negate
      -> Semiring.T A add zero mul one -> Ring.T A add zero negate mul one -> Verum
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A)
         (_ : Group.T A add zero negate) (_ : AbelianGroup.T A add zero negate)
         (_ : Semiring.T A add zero mul one) (_ : Ring.T A add zero negate mul one) => I.

Definition structures_all_delivers_ring_projection
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A) (r : Ring.T A add zero negate mul one)
           (x : A) (y : A) (z : A),
      mul x (add y z) = add (mul x y) (mul x z)
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A) (r : Ring.T A add zero negate mul one)
         (x : A) (y : A) (z : A) =>
       Ring.left_distributivity x y z.
