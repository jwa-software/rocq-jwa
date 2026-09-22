(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Number.All.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.

Definition data_number_all_delivers
  : Nat -> NatWithZero -> Integer -> ~ Falsum -> Verum
  := fun (_ : Nat) (_ : NatWithZero) (_ : Integer) (_ : ~ Falsum) . I.

Definition data_number_all_delivers_operations
  : Integer
  := (Integer.Zero + Integer.Negative Nat.One * Integer.Positive Nat.One)%integer.

Definition data_number_all_delivers_well_founded
  : forall (m : Nat) (n : NatWithZero) (x : Integer) .
      Accessible Nat.LessThan m
  := fun (m : Nat) (n : NatWithZero) (x : Integer) . accessibility m.

Definition data_number_all_delivers_well_founded_with_zero
  : forall (n : NatWithZero) . Accessible NatWithZero.LessThan n
  := fun (n : NatWithZero) . accessibility n.

Definition data_number_all_delivers_nat_equality_decidability
  : forall (m : Nat) (n : Nat) . m = n \/ ~ (m = n)
  := Nat.equality.decidability.

Definition data_number_all_delivers_nat_equality_uniqueness
  : forall (m : Nat) (n : Nat) (p : m = n) (q : m = n) . p = q
  := Nat.equality.uniqueness.

Definition data_number_all_delivers_gcd_zero
  : forall (a : NatWithZero) . NatWithZero.gcd a NatWithZero.Zero = a
  := NatWithZero.gcd.zero.

Definition data_number_all_delivers_gcd_recurrence
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.gcd a (NatWithZero.Positive q)
      = NatWithZero.gcd (NatWithZero.Positive q) (NatWithZero.modulo a q)
  := NatWithZero.gcd.recurrence.

Definition data_number_all_delivers_gcd_divisibility
  : forall (b : NatWithZero) (a : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := NatWithZero.gcd.divisibility.

Definition data_number_all_delivers_gcd_left_right_divisibility
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := fun (a : NatWithZero) (b : NatWithZero) .
       Conjunction_introduction
         (NatWithZero.gcd.left.divisibility a b) (NatWithZero.gcd.right.divisibility a b).

Definition data_number_all_delivers_gcd_universality
  : forall (b : NatWithZero) (a : NatWithZero) (d : NatWithZero) .
      NatWithZero.Divides d a ->
      NatWithZero.Divides d b -> NatWithZero.Divides d (NatWithZero.gcd a b)
  := NatWithZero.gcd.universality.

Definition data_number_all_delivers_gcd_nat
  : forall (q : Nat) (a : NatWithZero) .
      NatWithZero.gcd a (NatWithZero.Positive q)
      = NatWithZero.Positive (NatWithZero.gcd.nat a q)
  := NatWithZero.gcd.nat.specification.

Definition data_number_all_delivers_integer_divide
  : forall (x : Integer) (d : Nat) .
      Integer.abs (Integer.divide x d) = NatWithZero.divide (Integer.abs x) d
  := Integer.division.magnitude.

Definition data_number_all_delivers_well_founded_magnitude
  : forall (x : Integer) .
      Accessible (Induced NatWithZero.LessThan Integer.abs) x
  := fun (x : Integer) . accessibility x.

Definition data_number_all_delivers_divide_nat_safe
  : forall (d : Nat) (g : Nat)
      (h : NatWithZero.Divides (NatWithZero.Positive g) (NatWithZero.Positive d)) .
      NatWithZero.Positive (NatWithZero.divide.nat.safe d g h)
      = NatWithZero.divide (NatWithZero.Positive d) g
  := NatWithZero.divide.nat.safe.specification.

Definition data_number_all_delivers_gcd_nat_left_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides (NatWithZero.Positive (NatWithZero.gcd.nat a q)) a
  := NatWithZero.gcd.nat.left.divisibility.

Definition data_number_all_delivers_gcd_nat_right_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides
        (NatWithZero.Positive (NatWithZero.gcd.nat a q)) (NatWithZero.Positive q)
  := NatWithZero.gcd.nat.right.divisibility.

Definition data_number_all_delivers_gcd_nat_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides (NatWithZero.Positive (NatWithZero.gcd.nat a q)) a
      /\ NatWithZero.Divides
           (NatWithZero.Positive (NatWithZero.gcd.nat a q)) (NatWithZero.Positive q)
  := NatWithZero.gcd.nat.divisibility.

Definition data_number_all_delivers_multiplication_right_order_extensivity
  : forall (k : Nat) (n : NatWithZero) .
      NatWithZero.LessOrEqual n (NatWithZero.mul (NatWithZero.Positive k) n)
  := NatWithZero.multiplication.right.order.extensivity.

Definition data_number_all_delivers_division_uniqueness
  : forall (n : NatWithZero) (d : Nat) (m : NatWithZero) (r : NatWithZero) .
      (NatWithZero.add (NatWithZero.mul m (NatWithZero.Positive d)) r = n
       /\ NatWithZero.LessThan r (NatWithZero.Positive d))
      -> NatWithZero.divide n d = m /\ NatWithZero.modulo n d = r
  := NatWithZero.division.uniqueness.

Definition data_number_all_delivers_division_invariance
  : forall (n : NatWithZero) (d : Nat) (k : Nat) .
      NatWithZero.divide
        (NatWithZero.mul (NatWithZero.Positive k) n) (Nat.mul k d)
      = NatWithZero.divide n d
  := NatWithZero.division.invariance.

Definition data_number_all_delivers_modulo_homogeneity
  : forall (n : NatWithZero) (d : Nat) (k : Nat) .
      NatWithZero.modulo
        (NatWithZero.mul (NatWithZero.Positive k) n) (Nat.mul k d)
      = NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.modulo n d)
  := NatWithZero.modulo.homogeneity.

Definition data_number_all_delivers_gcd_left_distributivity_of_multiplication
  : forall (k : Nat) (b : NatWithZero) (a : NatWithZero) .
      NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.gcd a b)
      = NatWithZero.gcd
          (NatWithZero.mul (NatWithZero.Positive k) a)
          (NatWithZero.mul (NatWithZero.Positive k) b)
  := NatWithZero.gcd.left.distributivity.of.multiplication.

Definition data_number_all_delivers_gcd_nat_left_distributivity_of_multiplication
  : forall (k : Nat) (q : Nat) (a : NatWithZero) .
      Nat.mul k (NatWithZero.gcd.nat a q)
      = NatWithZero.gcd.nat
          (NatWithZero.mul (NatWithZero.Positive k) a) (Nat.mul k q)
  := NatWithZero.gcd.nat.left.distributivity.of.multiplication.

Definition data_number_all_delivers_divide_nat_safe_congruence
  : forall (d1 : Nat) (g1 : Nat)
      (h1 : NatWithZero.Divides
              (NatWithZero.Positive g1) (NatWithZero.Positive d1))
      (d2 : Nat) (g2 : Nat)
      (h2 : NatWithZero.Divides
              (NatWithZero.Positive g2) (NatWithZero.Positive d2)) .
      NatWithZero.divide (NatWithZero.Positive d1) g1
      = NatWithZero.divide (NatWithZero.Positive d2) g2
      -> NatWithZero.divide.nat.safe d1 g1 h1
         = NatWithZero.divide.nat.safe d2 g2 h2
  := NatWithZero.divide.nat.safe.congruence.

Definition data_number_all_delivers_division_exactness
  : forall (n : NatWithZero) (d : Nat) .
      NatWithZero.Divides (NatWithZero.Positive d) n
      -> NatWithZero.mul (NatWithZero.divide n d) (NatWithZero.Positive d) = n
  := NatWithZero.division.exactness.

Definition data_number_all_delivers_gcd_nat_exhaustiveness
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.gcd.nat
        (NatWithZero.divide a (NatWithZero.gcd.nat a q))
        (NatWithZero.divide.nat.safe q (NatWithZero.gcd.nat a q)
           (NatWithZero.gcd.nat.right.divisibility a q))
      = Nat.One
  := NatWithZero.gcd.nat.exhaustiveness.

Definition data_number_all_delivers_gcd_multiplication_cancellation
  : forall (p : NatWithZero) (q : NatWithZero) (r : NatWithZero) .
      NatWithZero.Divides p (NatWithZero.mul q r)
      -> NatWithZero.gcd p q = NatWithZero.Positive Nat.One
      -> NatWithZero.Divides p r
  := NatWithZero.gcd.multiplication.cancellation.

Definition data_number_all_delivers_gcd_commutativity
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.gcd a b = NatWithZero.gcd b a
  := NatWithZero.gcd.commutativity.

Definition data_number_all_delivers_integer_multiplication_magnitude
  : forall (m : Integer) (n : Integer) .
      Integer.abs (Integer.mul m n)
      = NatWithZero.mul (Integer.abs m) (Integer.abs n)
  := Integer.multiplication.magnitude.

Definition data_number_all_delivers_integer_division_invariance
  : forall (x : Integer) (d : Nat) (k : Nat) .
      Integer.divide (Integer.mul (Integer.Positive k) x) (Nat.mul k d)
      = Integer.divide x d
  := Integer.division.invariance.

Definition data_number_all_delivers_integer_division_exactness
  : forall (x : Integer) (d : Nat) .
      NatWithZero.Divides (NatWithZero.Positive d) (Integer.abs x)
      -> Integer.mul (Integer.divide x d) (Integer.Positive d) = x
  := Integer.division.exactness.

Definition data_number_all_delivers_integer_division_exhaustiveness
  : forall (x : Integer) (d : Nat) .
      NatWithZero.gcd.nat
        (Integer.abs
           (Integer.divide x (NatWithZero.gcd.nat (Integer.abs x) d)))
        (NatWithZero.divide.nat.safe d
           (NatWithZero.gcd.nat (Integer.abs x) d)
           (NatWithZero.gcd.nat.right.divisibility (Integer.abs x) d))
      = Nat.One
  := Integer.division.exhaustiveness.

Definition data_number_all_delivers_integer_multiplication_cancellation
  : forall (k : Integer) (m : Integer) (n : Integer) .
      ~ (k = Integer.Zero)
      -> Integer.mul k m = Integer.mul k n
      -> m = n
  := Integer.multiplication.cancellation.

Definition data_number_all_delivers_integer_multiplication_interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      Integer.mul (Integer.mul a b) (Integer.mul c d)
      = Integer.mul (Integer.mul a c) (Integer.mul b d)
  := Integer.multiplication.interchange.

Definition data_number_all_delivers_rational_numerator
  : Rational -> Integer
  := Rational.numerator.

Definition data_number_all_delivers_rational_denominator
  : Rational -> Nat
  := Rational.denominator.

Definition data_number_all_delivers_rational_make
  : Integer -> Nat -> Rational
  := Rational.make.

Definition data_number_all_delivers_rational_negate
  : Rational -> Rational
  := Rational.negate.

Definition data_number_all_delivers_rational_add
  : Rational -> Rational -> Rational
  := Rational.add.

Definition data_number_all_delivers_rational_sub
  : Rational -> Rational -> Rational
  := Rational.sub.

Definition data_number_all_delivers_rational_mul
  : Rational -> Rational -> Rational
  := Rational.mul.

Definition data_number_all_delivers_rational_inverse
  : Rational -> Option Rational
  := Rational.inverse.

Definition data_number_all_delivers_rational_make_invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      Rational.make (Integer.mul (Integer.Positive k) n) (Nat.mul k d)
      = Rational.make n d
  := Rational.make.invariance.

Definition data_number_all_delivers_rational_make_proportionality
  : forall (a : Integer) (b : Nat) .
      Integer.mul (Rational.numerator (Rational.make a b)) (Integer.from_nat b)
      = Integer.mul a
          (Integer.from_nat (Rational.denominator (Rational.make a b)))
  := Rational.make.proportionality.

Definition data_number_all_delivers_rational_irreducibility
  : forall (x : Rational) .
      NatWithZero.gcd.nat
        (Integer.abs (Rational.numerator x))
        (Rational.denominator x)
      = Nat.One
  := Rational.irreducibility.

Definition data_number_all_delivers_rational_extensionality
  : forall (x : Rational) (y : Rational) .
      Rational.numerator x = Rational.numerator y
      -> Rational.denominator x = Rational.denominator y
      -> x = y
  := Rational.extensionality.

Definition data_number_all_delivers_rational_make_characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      Rational.make a b = Rational.make c d
      <-> Integer.mul a (Integer.from_nat d)
          = Integer.mul c (Integer.from_nat b)
  := Rational.make.characterisation.
