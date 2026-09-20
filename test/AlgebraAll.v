(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.All.

Definition algebra_all_delivers
  : forall (A : Type) (op : A -> A -> A) (e : A) .
      Semigroup op -> Monoid op e -> Commutative op -> AbelianMonoid op e
      -> Cancellative op -> ~ Falsum -> Verum
  := fun (A : Type) (op : A -> A -> A) (e : A)
         (_ : Semigroup op) (_ : Monoid op e) (_ : Commutative op) (_ : AbelianMonoid op e)
         (_ : Cancellative op) (_ : ~ Falsum) . I.

Definition algebra_all_delivers_projections
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid op e) (x : A) .
      op e x = x /\ op x e = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid op e) (x : A) .
       Monoid.identity x.

Definition algebra_all_delivers_groups_and_rings
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A) .
      Group add zero negate -> AbelianGroup add zero negate
      -> Semiring add zero mul one -> Ring add zero negate mul one -> Verum
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A)
         (_ : Group add zero negate) (_ : AbelianGroup add zero negate)
         (_ : Semiring add zero mul one) (_ : Ring add zero negate mul one) . I.

Definition algebra_all_delivers_ring_projection
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one)
           (x : A) (y : A) (z : A) .
      mul x (add y z) = add (mul x y) (mul x z) /\ mul (add y z) x = add (mul y x) (mul z x)
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
         (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one)
         (x : A) (y : A) (z : A) .
       Ring.distributivity x y z.
