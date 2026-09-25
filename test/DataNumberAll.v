(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Base.Comparison.
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
       conjoin
         (NatWithZero.gcd.left.divisibility a b), (NatWithZero.gcd.right.divisibility a b).

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

Definition data_number_all_delivers_integer_multiplication_positive_homomorphism
  : forall (m : Nat) (n : Nat) .
      Integer.mul (Integer.Positive m) (Integer.Positive n)
      = Integer.Positive (Nat.mul m n)
  := Integer.multiplication.positive.homomorphism.

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

Definition data_number_all_delivers_rational_zero
  : Rational
  := Rational.Zero.

Definition data_number_all_delivers_rational_one
  : Rational
  := Rational.One.

Definition data_number_all_delivers_rational_make_retraction
  : forall (x : Rational) .
      Rational.make (Rational.numerator x) (Rational.denominator x) = x
  := Rational.make.retraction.

Definition data_number_all_delivers_rational_make_annihilation
  : forall (b : Nat) . Rational.make Integer.Zero b = Rational.Zero
  := Rational.make.annihilation.

Definition data_number_all_delivers_rational_make_addition_homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      Rational.add (Rational.make a b) (Rational.make c d)
      = Rational.make
          (Integer.add (Integer.mul a (Integer.from_nat d))
                       (Integer.mul c (Integer.from_nat b)))
          (Nat.mul b d)
  := Rational.make.addition.homomorphism.

Definition data_number_all_delivers_rational_make_multiplication_homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      Rational.mul (Rational.make a b) (Rational.make c d)
      = Rational.make (Integer.mul a c) (Nat.mul b d)
  := Rational.make.multiplication.homomorphism.

Definition data_number_all_delivers_rational_make_negation_homomorphism
  : forall (a : Integer) (b : Nat) .
      Rational.negate (Rational.make a b)
      = Rational.make (Integer.negate a) b
  := Rational.make.negation.homomorphism.

Definition data_number_all_delivers_rational_addition_associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      Rational.add (Rational.add x y) z = Rational.add x (Rational.add y z)
  := Rational.addition.associativity.

Definition data_number_all_delivers_rational_addition_commutativity
  : forall (x : Rational) (y : Rational) .
      Rational.add x y = Rational.add y x
  := Rational.addition.commutativity.

Definition data_number_all_delivers_rational_addition_identity
  : forall (x : Rational) .
      (Rational.add Rational.Zero x = x) /\ (Rational.add x Rational.Zero = x)
  := Rational.addition.identity.

Definition data_number_all_delivers_rational_addition_inverse
  : forall (x : Rational) .
      (Rational.add (Rational.negate x) x = Rational.Zero)
      /\ (Rational.add x (Rational.negate x) = Rational.Zero)
  := Rational.addition.inverse.

Definition data_number_all_delivers_rational_addition_cancellation
  : forall (m : Rational) (n : Rational) (k : Rational) .
      (Rational.add m n = Rational.add m k -> n = k)
      /\ (Rational.add m n = Rational.add k n -> m = k)
  := Rational.addition.cancellation.

Definition data_number_all_delivers_rational_multiplication_associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      Rational.mul (Rational.mul x y) z = Rational.mul x (Rational.mul y z)
  := Rational.multiplication.associativity.

Definition data_number_all_delivers_rational_multiplication_commutativity
  : forall (x : Rational) (y : Rational) .
      Rational.mul x y = Rational.mul y x
  := Rational.multiplication.commutativity.

Definition data_number_all_delivers_rational_multiplication_identity
  : forall (x : Rational) .
      (Rational.mul Rational.One x = x) /\ (Rational.mul x Rational.One = x)
  := Rational.multiplication.identity.

Definition data_number_all_delivers_rational_multiplication_left_annihilation
  : forall (x : Rational) . Rational.mul Rational.Zero x = Rational.Zero
  := Rational.multiplication.left.annihilation.

Definition data_number_all_delivers_rational_multiplication_right_annihilation
  : forall (x : Rational) . Rational.mul x Rational.Zero = Rational.Zero
  := Rational.multiplication.right.annihilation.

Definition data_number_all_delivers_rational_multiplication_distributivity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (Rational.mul x (Rational.add y z)
       = Rational.add (Rational.mul x y) (Rational.mul x z))
      /\ (Rational.mul (Rational.add y z) x
          = Rational.add (Rational.mul y x) (Rational.mul z x))
  := Rational.multiplication.distributivity.over.addition.

Definition data_number_all_delivers_rational_inverse_specification
  : forall (x : Rational) (y : Rational) .
      Rational.inverse x = Some y -> Rational.mul x y = Rational.One
  := Rational.inverse.specification.

Definition data_number_all_delivers_rational_less_or_equal
  : Rational -> Rational -> Prop
  := Rational.LessOrEqual.

Definition data_number_all_delivers_rational_characterisation
  : forall (x : Rational) (y : Rational) .
      x = y
      <-> Integer.mul (Rational.numerator x)
                      (Integer.from_nat (Rational.denominator y))
          = Integer.mul (Rational.numerator y)
                        (Integer.from_nat (Rational.denominator x))
  := Rational.characterisation.

Definition data_number_all_delivers_rational_order_strict_transitivity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      Rational.LessThan x y
      -> Rational.LessThan y z
      -> Rational.LessThan x z
  := Rational.order.strict.transitivity.

Definition data_number_all_delivers_rational_make_order_strict_characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      Rational.LessThan (Rational.make a b) (Rational.make c d)
      <-> Integer.LessThan (Integer.mul a (Integer.from_nat d))
                           (Integer.mul c (Integer.from_nat b))
  := Rational.make.order.strict.characterisation.

Definition data_number_all_delivers_rational_addition_order_strict_monotonicity
  : forall (z : Rational) (x : Rational) (y : Rational) .
      Rational.LessThan x y
      -> Rational.LessThan (Rational.add z x) (Rational.add z y)
  := Rational.addition.order.strict.monotonicity.

Definition data_number_all_delivers_rational_multiplication_left_order_strict_monotonicity
  : forall (z : Rational) (x : Rational) (y : Rational) .
      Rational.LessThan Rational.Zero z
      -> Rational.LessThan x y
      -> Rational.LessThan (Rational.mul z x) (Rational.mul z y)
  := Rational.multiplication.left.order.strict.monotonicity.

Definition data_number_all_delivers_rational_comparison_specification
  : forall (x : Rational) (y : Rational) .
      (Rational.compare x y = Comparison.Lt <-> Rational.LessThan x y)
      /\ (Rational.compare x y = Comparison.Eq <-> x = y)
  := Rational.comparison.specification.

Definition data_number_all_delivers_rational_comparison_antisymmetry
  : forall (x : Rational) (y : Rational) .
      Rational.compare x y = Comparison.transpose (Rational.compare y x)
  := Rational.comparison.antisymmetry.

Definition data_number_all_delivers_rational_embedding_injectivity
  : forall (m : Integer) (n : Integer) .
      Rational.from_integer m = Rational.from_integer n -> m = n
  := fun (m : Integer) (n : Integer) . @Rational.embedding.injectivity m n.

Definition data_number_all_delivers_rational_embedding_addition
  : forall (m : Integer) (n : Integer) .
      Rational.from_integer (Integer.add m n)
      = Rational.add (Rational.from_integer m) (Rational.from_integer n)
  := Rational.embedding.addition.

Definition data_number_all_delivers_rational_embedding_multiplication
  : forall (m : Integer) (n : Integer) .
      Rational.from_integer (Integer.mul m n)
      = Rational.mul (Rational.from_integer m) (Rational.from_integer n)
  := Rational.embedding.multiplication.

Definition data_number_all_delivers_rational_embedding_order
  : forall (m : Integer) (n : Integer) .
      Integer.LessThan m n
      <-> Rational.LessThan (Rational.from_integer m)
                            (Rational.from_integer n)
  := Rational.embedding.order.

Definition data_number_all_delivers_gcd_nat_right_annihilation
  : forall (a : NatWithZero) . NatWithZero.gcd.nat a Nat.One = Nat.One
  := NatWithZero.gcd.nat.right.annihilation.

Definition data_number_all_delivers_nat_with_zero_narrowing_nat_retraction
  : forall (p : Nat) . NatWithZero.to_nat p = Some p
  := NatWithZero.narrowing.nat.retraction.

Definition data_number_all_delivers_nat_with_zero_narrowing_nat_specification
  : forall (n : NatWithZero) (p : Nat) . NatWithZero.to_nat n = Some p <-> n = p
  := NatWithZero.narrowing.nat.specification.

Definition data_number_all_delivers_nat_with_zero_narrowing_nat_failure
  : forall (n : NatWithZero) . NatWithZero.to_nat n = None <-> n = NatWithZero.Zero
  := NatWithZero.narrowing.nat.failure.

Definition data_number_all_delivers_integer_narrowing_nat_with_zero_retraction
  : forall (n : NatWithZero) . Integer.to_nat_with_zero n = Some n
  := Integer.narrowing.nat_with_zero.retraction.

Definition data_number_all_delivers_integer_narrowing_nat_with_zero_specification
  : forall (x : Integer) (n : NatWithZero) . Integer.to_nat_with_zero x = Some n <-> x = n
  := Integer.narrowing.nat_with_zero.specification.

Definition data_number_all_delivers_integer_narrowing_nat_with_zero_failure
  : forall (x : Integer) . Integer.to_nat_with_zero x = None <-> (x < Integer.Zero)%integer
  := Integer.narrowing.nat_with_zero.failure.

Definition data_number_all_delivers_integer_narrowing_nat_retraction
  : forall (p : Nat) . Integer.to_nat p = Some p
  := Integer.narrowing.nat.retraction.

Definition data_number_all_delivers_integer_narrowing_nat_specification
  : forall (x : Integer) (p : Nat) . Integer.to_nat x = Some p <-> x = p
  := Integer.narrowing.nat.specification.

Definition data_number_all_delivers_integer_narrowing_nat_failure
  : forall (x : Integer) . Integer.to_nat x = None <-> (x <= Integer.Zero)%integer
  := Integer.narrowing.nat.failure.

Definition data_number_all_delivers_rational_narrowing_integer_retraction
  : forall (n : Integer) . Rational.to_integer n = Some n
  := Rational.narrowing.integer.retraction.

Definition data_number_all_delivers_rational_narrowing_integer_specification
  : forall (x : Rational) (n : Integer) . Rational.to_integer x = Some n <-> x = n
  := Rational.narrowing.integer.specification.

Definition data_number_all_delivers_rational_narrowing_integer_failure
  : forall (x : Rational) .
      Rational.to_integer x = None <-> ~ (Rational.denominator x = Nat.One)
  := Rational.narrowing.integer.failure.

Definition data_number_all_delivers_rational_narrowing_nat_with_zero_retraction
  : forall (n : NatWithZero) . Rational.to_nat_with_zero n = Some n
  := Rational.narrowing.nat_with_zero.retraction.

Definition data_number_all_delivers_rational_narrowing_nat_with_zero_specification
  : forall (x : Rational) (n : NatWithZero) . Rational.to_nat_with_zero x = Some n <-> x = n
  := Rational.narrowing.nat_with_zero.specification.

Definition data_number_all_delivers_rational_narrowing_nat_retraction
  : forall (p : Nat) . Rational.to_nat p = Some p
  := Rational.narrowing.nat.retraction.

Definition data_number_all_delivers_rational_narrowing_nat_specification
  : forall (x : Rational) (p : Nat) . Rational.to_nat x = Some p <-> x = p
  := Rational.narrowing.nat.specification.

Theorem data_number_all_delivers_coercion_nat_to_nat_with_zero
  : forall (n : Nat) .
      NatWithZero.add n n = NatWithZero.add (NatWithZero.Positive n) (NatWithZero.Positive n).
Proof.
  intro n.
  quod idem est.
Qed.

Theorem data_number_all_delivers_coercion_nat_to_integer
  : forall (n : Nat) . Integer.negate n = Integer.negate (Integer.Positive n).
Proof.
  intro n.
  quod idem est.
Qed.

Theorem data_number_all_delivers_coercion_nat_with_zero_to_integer
  : forall (w : NatWithZero) . Integer.negate w = Integer.negate (Integer.from_nat_with_zero w).
Proof.
  intro w.
  quod idem est.
Qed.

Theorem data_number_all_delivers_coercion_integer_to_rational
  : forall (z : Integer) . Rational.negate z = Rational.negate (Rational.from_integer z).
Proof.
  intro z.
  quod idem est.
Qed.

Theorem data_number_all_delivers_coercion_nat_to_rational
  : forall (n : Nat) .
      Rational.negate n = Rational.negate (Rational.from_integer (Integer.Positive n)).
Proof.
  intro n.
  quod idem est.
Qed.

Theorem data_number_all_delivers_coercion_nat_with_zero_to_rational
  : forall (w : NatWithZero) .
      Rational.negate w = Rational.negate (Rational.from_integer (Integer.from_nat_with_zero w)).
Proof.
  intro w.
  quod idem est.
Qed.
