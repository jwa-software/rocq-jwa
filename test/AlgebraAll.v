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

Definition algebra_all_delivers_monoid_associativity
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid op e) (x : A) (y : A) (z : A) .
      op (op x y) z = op x (op y z)
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid op e) . Semigroup.associativity.

Definition algebra_all_delivers_group_identity
  : forall (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : Group op e i) (x : A) .
      op e x = x /\ op x e = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : Group op e i) . Monoid.identity.

Definition algebra_all_delivers_abelian_monoid_identity
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : AbelianMonoid op e) (x : A) .
      op e x = x /\ op x e = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : AbelianMonoid op e) . Monoid.identity.

Definition algebra_all_delivers_abelian_monoid_commutativity
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : AbelianMonoid op e) (x : A) (y : A) .
      op x y = op y x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : AbelianMonoid op e) .
      Commutative.commutativity.

Definition algebra_all_delivers_abelian_group_inverse
  : forall (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : AbelianGroup op e i) (x : A) .
      op (i x) x = e /\ op x (i x) = e
  := fun (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : AbelianGroup op e i) .
      Group.inverse.

Definition algebra_all_delivers_abelian_group_commutativity
  : forall (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : AbelianGroup op e i)
        (x : A) (y : A) .
      op x y = op y x
  := fun (A : Type) (op : A -> A -> A) (e : A) (i : A -> A) (g : AbelianGroup op e i) .
      Commutative.commutativity.

Definition algebra_all_delivers_ring_commutativity
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
        (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one) (x : A) (y : A) .
      add x y = add y x
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
        (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one) .
      Commutative.commutativity.

Definition algebra_all_delivers_ring_identity
  : forall (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
        (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one) (x : A) .
      mul one x = x /\ mul x one = x
  := fun (A : Type) (add : A -> A -> A) (zero : A) (negate : A -> A)
        (mul : A -> A -> A) (one : A) (r : Ring add zero negate mul one) .
      Monoid.identity.

Definition algebra_all_delivers_semiring_commutativity
  : forall (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) (x : A) (y : A) .
      add x y = add y x
  := fun (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) .
      Commutative.commutativity.

Definition algebra_all_delivers_semiring_identity
  : forall (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) (x : A) .
      mul one x = x /\ mul x one = x
  := fun (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) .
      Monoid.identity.

Definition algebra_all_delivers_semiring_distributivity
  : forall (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) (x : A) (y : A) (z : A) .
      mul x (add y z) = add (mul x y) (mul x z) /\ mul (add y z) x = add (mul y x) (mul z x)
  := fun (A : Type) (add : A -> A -> A) (zero : A) (mul : A -> A -> A) (one : A)
        (s : Semiring add zero mul one) .
      Semiring.distributivity.
