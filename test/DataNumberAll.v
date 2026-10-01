(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* The umbrella under guard, and nothing else that it owes a client. The one
 * other import is a tactic language, not a type: some guards below are proved
 * rather than stated, and [Tactics.Equation] is what writes them. A type this
 * file can name only because it imported it would defeat the guard.
 *)
From jwa Require Import Data.Number.All.
From jwa Require Import Tactics.Equation.

Definition data_number_all_delivers
  : Nat -> Nat0 -> Integer -> ~ Falsum -> Verum
  := fun (_ : Nat) (_ : Nat0) (_ : Integer) (_ : ~ Falsum) . I.

Definition data_number_all_delivers_operations
  : Integer
  := (Integer.Zero + Integer.Negative Nat.One * Integer.Positive Nat.One)%z.

Definition data_number_all_delivers_well_founded
  : forall (m : Nat) (n : Nat0) (x : Integer) .
      Accessible Nat.LessThan m
  := fun (m : Nat) (n : Nat0) (x : Integer) . accessibility m.

Definition data_number_all_delivers_well_founded_with_zero
  : forall (n : Nat0) . Accessible Nat0.LessThan n
  := fun (n : Nat0) . accessibility n.

Definition data_number_all_delivers_nat_equality_decidability
  : forall (m : Nat) (n : Nat) . m = n \/ ~ (m = n)
  := Nat.equality.decidability.

Definition data_number_all_delivers_nat_equality_uniqueness
  : forall (m : Nat) (n : Nat) (p : m = n) (q : m = n) . p = q
  := Nat.equality.uniqueness.

Definition data_number_all_delivers_gcd_zero
  : forall (a : Nat0) . Nat0.gcd a Nat0.Zero = a
  := Nat0.gcd.zero.

Definition data_number_all_delivers_gcd_recurrence
  : forall (a : Nat0) (q : Nat) .
      Nat0.gcd a (Nat0.Positive q)
      = Nat0.gcd (Nat0.Positive q) (Nat0.modulo a q)
  := Nat0.gcd.recurrence.

Definition data_number_all_delivers_gcd_divisibility
  : forall (b : Nat0) (a : Nat0) .
      Nat0.Divides (Nat0.gcd a b) a
      /\ Nat0.Divides (Nat0.gcd a b) b
  := Nat0.gcd.divisibility.

Definition data_number_all_delivers_gcd_left_right_divisibility
  : forall (a : Nat0) (b : Nat0) .
      Nat0.Divides (Nat0.gcd a b) a
      /\ Nat0.Divides (Nat0.gcd a b) b
  := fun (a : Nat0) (b : Nat0) .
       conjoin
         (Nat0.gcd.left.divisibility a b), (Nat0.gcd.right.divisibility a b).

Definition data_number_all_delivers_gcd_universality
  : forall (b : Nat0) (a : Nat0) (d : Nat0) .
      Nat0.Divides d a ->
      Nat0.Divides d b -> Nat0.Divides d (Nat0.gcd a b)
  := Nat0.gcd.universality.

Definition data_number_all_delivers_gcd_nat
  : forall (q : Nat) (a : Nat0) .
      Nat0.gcd a (Nat0.Positive q)
      = Nat0.Positive (Nat0.gcd.nat a q)
  := Nat0.gcd.nat.specification.

Definition data_number_all_delivers_integer_divide
  : forall (x : Integer) (d : Nat) .
      Integer.abs (Integer.divide x d) = Nat0.divide (Integer.abs x) d
  := Integer.division.magnitude.

Definition data_number_all_delivers_well_founded_magnitude
  : forall (x : Integer) .
      Accessible (Induced Nat0.LessThan Integer.abs) x
  := fun (x : Integer) . accessibility x.

Definition data_number_all_delivers_divide_nat_safe
  : forall (d : Nat) (g : Nat)
      (h : Nat0.Divides (Nat0.Positive g) (Nat0.Positive d)) .
      Nat0.Positive (Nat0.divide.nat.safe d g h)
      = Nat0.divide (Nat0.Positive d) g
  := Nat0.divide.nat.safe.specification.

Definition data_number_all_delivers_gcd_nat_left_divisibility
  : forall (a : Nat0) (q : Nat) .
      Nat0.Divides (Nat0.Positive (Nat0.gcd.nat a q)) a
  := Nat0.gcd.nat.left.divisibility.

Definition data_number_all_delivers_gcd_nat_right_divisibility
  : forall (a : Nat0) (q : Nat) .
      Nat0.Divides
        (Nat0.Positive (Nat0.gcd.nat a q)) (Nat0.Positive q)
  := Nat0.gcd.nat.right.divisibility.

Definition data_number_all_delivers_gcd_nat_divisibility
  : forall (a : Nat0) (q : Nat) .
      Nat0.Divides (Nat0.Positive (Nat0.gcd.nat a q)) a
      /\ Nat0.Divides
           (Nat0.Positive (Nat0.gcd.nat a q)) (Nat0.Positive q)
  := Nat0.gcd.nat.divisibility.

Definition data_number_all_delivers_multiplication_right_order_extensivity
  : forall (k : Nat) (n : Nat0) .
      Nat0.LessOrEqual n (Nat0.mul (Nat0.Positive k) n)
  := Nat0.multiplication.right.order.extensivity.

Definition data_number_all_delivers_division_uniqueness
  : forall (n : Nat0) (d : Nat) (m : Nat0) (r : Nat0) .
      (Nat0.add (Nat0.mul m (Nat0.Positive d)) r = n
       /\ Nat0.LessThan r (Nat0.Positive d))
      -> Nat0.divide n d = m /\ Nat0.modulo n d = r
  := Nat0.division.uniqueness.

Definition data_number_all_delivers_division_invariance
  : forall (n : Nat0) (d : Nat) (k : Nat) .
      Nat0.divide
        (Nat0.mul (Nat0.Positive k) n) (Nat.mul k d)
      = Nat0.divide n d
  := Nat0.division.invariance.

Definition data_number_all_delivers_modulo_homogeneity
  : forall (n : Nat0) (d : Nat) (k : Nat) .
      Nat0.modulo
        (Nat0.mul (Nat0.Positive k) n) (Nat.mul k d)
      = Nat0.mul (Nat0.Positive k) (Nat0.modulo n d)
  := Nat0.modulo.homogeneity.

Definition data_number_all_delivers_gcd_left_distributivity_of_multiplication
  : forall (k : Nat) (b : Nat0) (a : Nat0) .
      Nat0.mul (Nat0.Positive k) (Nat0.gcd a b)
      = Nat0.gcd
          (Nat0.mul (Nat0.Positive k) a)
          (Nat0.mul (Nat0.Positive k) b)
  := Nat0.gcd.left.distributivity.of.multiplication.

Definition data_number_all_delivers_gcd_nat_left_distributivity_of_multiplication
  : forall (k : Nat) (q : Nat) (a : Nat0) .
      Nat.mul k (Nat0.gcd.nat a q)
      = Nat0.gcd.nat
          (Nat0.mul (Nat0.Positive k) a) (Nat.mul k q)
  := Nat0.gcd.nat.left.distributivity.of.multiplication.

Definition data_number_all_delivers_divide_nat_safe_congruence
  : forall (d1 : Nat) (g1 : Nat)
      (h1 : Nat0.Divides
              (Nat0.Positive g1) (Nat0.Positive d1))
      (d2 : Nat) (g2 : Nat)
      (h2 : Nat0.Divides
              (Nat0.Positive g2) (Nat0.Positive d2)) .
      Nat0.divide (Nat0.Positive d1) g1
      = Nat0.divide (Nat0.Positive d2) g2
      -> Nat0.divide.nat.safe d1 g1 h1
         = Nat0.divide.nat.safe d2 g2 h2
  := Nat0.divide.nat.safe.congruence.

Definition data_number_all_delivers_division_exactness
  : forall (n : Nat0) (d : Nat) .
      Nat0.Divides (Nat0.Positive d) n
      -> Nat0.mul (Nat0.divide n d) (Nat0.Positive d) = n
  := Nat0.division.exactness.

Definition data_number_all_delivers_gcd_nat_exhaustiveness
  : forall (a : Nat0) (q : Nat) .
      Nat0.gcd.nat
        (Nat0.divide a (Nat0.gcd.nat a q))
        (Nat0.divide.nat.safe q (Nat0.gcd.nat a q)
           (Nat0.gcd.nat.right.divisibility a q))
      = Nat.One
  := Nat0.gcd.nat.exhaustiveness.

Definition data_number_all_delivers_gcd_multiplication_cancellation
  : forall (p : Nat0) (q : Nat0) (r : Nat0) .
      Nat0.Divides p (Nat0.mul q r)
      -> Nat0.gcd p q = Nat0.Positive Nat.One
      -> Nat0.Divides p r
  := Nat0.gcd.multiplication.cancellation.

Definition data_number_all_delivers_gcd_commutativity
  : forall (a : Nat0) (b : Nat0) .
      Nat0.gcd a b = Nat0.gcd b a
  := Nat0.gcd.commutativity.

Definition data_number_all_delivers_integer_multiplication_magnitude
  : forall (m : Integer) (n : Integer) .
      Integer.abs (Integer.mul m n)
      = Nat0.mul (Integer.abs m) (Integer.abs n)
  := Integer.multiplication.magnitude.

Definition data_number_all_delivers_integer_division_invariance
  : forall (x : Integer) (d : Nat) (k : Nat) .
      Integer.divide (Integer.mul (Integer.Positive k) x) (Nat.mul k d)
      = Integer.divide x d
  := Integer.division.invariance.

Definition data_number_all_delivers_integer_division_exactness
  : forall (x : Integer) (d : Nat) .
      Nat0.Divides (Nat0.Positive d) (Integer.abs x)
      -> Integer.mul (Integer.divide x d) (Integer.Positive d) = x
  := Integer.division.exactness.

Definition data_number_all_delivers_integer_division_exhaustiveness
  : forall (x : Integer) (d : Nat) .
      Nat0.gcd.nat
        (Integer.abs
           (Integer.divide x (Nat0.gcd.nat (Integer.abs x) d)))
        (Nat0.divide.nat.safe d
           (Nat0.gcd.nat (Integer.abs x) d)
           (Nat0.gcd.nat.right.divisibility (Integer.abs x) d))
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
      Nat0.gcd.nat
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
  : forall (a : Nat0) . Nat0.gcd.nat a Nat.One = Nat.One
  := Nat0.gcd.nat.right.annihilation.

Definition data_number_all_delivers_nat0_narrowing_nat_retraction
  : forall (p : Nat) . Nat0.to_nat p = Some p
  := Nat0.narrowing.nat.retraction.

Definition data_number_all_delivers_nat0_narrowing_nat_specification
  : forall (n : Nat0) (p : Nat) . Nat0.to_nat n = Some p <-> n = p
  := Nat0.narrowing.nat.specification.

Definition data_number_all_delivers_nat0_narrowing_nat_failure
  : forall (n : Nat0) . Nat0.to_nat n = None <-> n = Nat0.Zero
  := Nat0.narrowing.nat.failure.

Definition data_number_all_delivers_integer_narrowing_nat0_retraction
  : forall (n : Nat0) . Integer.to_nat0 n = Some n
  := Integer.narrowing.nat0.retraction.

Definition data_number_all_delivers_integer_narrowing_nat0_specification
  : forall (x : Integer) (n : Nat0) . Integer.to_nat0 x = Some n <-> x = n
  := Integer.narrowing.nat0.specification.

Definition data_number_all_delivers_integer_narrowing_nat0_failure
  : forall (x : Integer) . Integer.to_nat0 x = None <-> (x < Integer.Zero)%z
  := Integer.narrowing.nat0.failure.

Definition data_number_all_delivers_integer_narrowing_nat_retraction
  : forall (p : Nat) . Integer.to_nat p = Some p
  := Integer.narrowing.nat.retraction.

Definition data_number_all_delivers_integer_narrowing_nat_specification
  : forall (x : Integer) (p : Nat) . Integer.to_nat x = Some p <-> x = p
  := Integer.narrowing.nat.specification.

Definition data_number_all_delivers_integer_narrowing_nat_failure
  : forall (x : Integer) . Integer.to_nat x = None <-> (x <= Integer.Zero)%z
  := Integer.narrowing.nat.failure.

Definition data_number_all_delivers_nat_literal
  : 3%n = Nat.Successor (Nat.Successor Nat.One)
  := Identity.reflexivity _.

Definition data_number_all_delivers_nat_literal_hexadecimal
  : 0x1F%n = 31%n
  := Identity.reflexivity _.

Fail Definition data_number_all_refuses_nat_literal_zero
  : Nat
  := 0%n.

Definition data_number_all_delivers_nat0_literal
  : 3%n0 = Nat0.Positive 3%n
  := Identity.reflexivity _.

Definition data_number_all_delivers_nat0_literal_zero
  : 0%n0 = Nat0.Zero
  := Identity.reflexivity _.

#[warnings="-abstract-large-number"]
Definition data_number_all_delivers_nat0_literal_large
  : Nat0
  := 100000%n0.

Definition data_number_all_delivers_integer_literal_negative
  : (-5)%z = Integer.Negative 5%n
  := Identity.reflexivity _.

Definition data_number_all_delivers_integer_literal_hexadecimal
  : (-0x10)%z = (-16)%z
  := Identity.reflexivity _.

Definition data_number_all_delivers_integer_literal_zero
  : (-0)%z = Integer.Zero
  := Identity.reflexivity _.

#[warnings="-abstract-large-number"]
Definition data_number_all_delivers_integer_literal_large
  : Integer
  := (-100000)%z.

Definition data_number_all_delivers_bare_numeral
  := 3.

Definition data_number_all_delivers_bare_numeral_integer
  : data_number_all_delivers_bare_numeral = Integer.Positive 3%n
  := Identity.reflexivity _.

Definition data_number_all_delivers_numeral_expected_type
  : Nat0.add 3 4 = 7%n0
  := Identity.reflexivity _.

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

Definition data_number_all_delivers_rational_narrowing_nat0_retraction
  : forall (n : Nat0) . Rational.to_nat0 n = Some n
  := Rational.narrowing.nat0.retraction.

Definition data_number_all_delivers_rational_narrowing_nat0_specification
  : forall (x : Rational) (n : Nat0) . Rational.to_nat0 x = Some n <-> x = n
  := Rational.narrowing.nat0.specification.

Definition data_number_all_delivers_rational_narrowing_nat0_failure
  : forall (x : Rational) .
      Rational.to_nat0 x = None
      <-> ~ (Rational.denominator x = Nat.One)
          \/ (Rational.numerator x < Integer.Zero)%z
  := Rational.narrowing.nat0.failure.

Definition data_number_all_delivers_rational_narrowing_nat_retraction
  : forall (p : Nat) . Rational.to_nat p = Some p
  := Rational.narrowing.nat.retraction.

Definition data_number_all_delivers_rational_narrowing_nat_specification
  : forall (x : Rational) (p : Nat) . Rational.to_nat x = Some p <-> x = p
  := Rational.narrowing.nat.specification.

Definition data_number_all_delivers_rational_narrowing_nat_failure
  : forall (x : Rational) .
      Rational.to_nat x = None
      <-> ~ (Rational.denominator x = Nat.One)
          \/ (Rational.numerator x <= Integer.Zero)%z
  := Rational.narrowing.nat.failure.

Theorem data_number_all_delivers_unwrap_of_a_narrowing
  : forall (n : Integer) (h : ~ (Rational.to_integer n = None)) .
      Option.unwrap (Rational.to_integer n) h = n.
Proof.
  intros n h.
  let proof r := Option.unwrapping.restoration (Rational.to_integer n) h.
  ipso (Option.some.injectivity (trans r, (Rational.narrowing.integer.retraction n))).
Qed.

Theorem data_number_all_delivers_coercion_nat_to_nat0
  : forall (n : Nat) .
      Nat0.add n n = Nat0.add (Nat0.Positive n) (Nat0.Positive n).
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

Theorem data_number_all_delivers_coercion_nat0_to_integer
  : forall (w : Nat0) . Integer.negate w = Integer.negate (Integer.from_nat0 w).
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

Theorem data_number_all_delivers_coercion_nat0_to_rational
  : forall (w : Nat0) .
      Rational.negate w = Rational.negate (Rational.from_integer (Integer.from_nat0 w)).
Proof.
  intro w.
  quod idem est.
Qed.

Definition data_number_all_delivers_bin_base_retraction
  : forall (n : Nat) . BinBase.to_nat (BinBase.from_nat n) = n
  := BinBase.conversion.retraction.

Definition data_number_all_delivers_bin_base_section
  : forall (b : BinBase) . BinBase.from_nat (BinBase.to_nat b) = b
  := BinBase.conversion.section.

Definition data_number_all_delivers_bin_base_successor
  : forall (b : BinBase) . BinBase.to_nat (++ b)%bin_base = Nat.Successor (BinBase.to_nat b)
  := BinBase.conversion.successor.

Definition data_number_all_delivers_bin_base_addition
  : forall (a : BinBase) (b : BinBase) .
      BinBase.to_nat (a + b)%bin_base = (BinBase.to_nat a + BinBase.to_nat b)%n
  := BinBase.conversion.addition.

Definition data_number_all_delivers_bin_base_multiplication
  : forall (a : BinBase) (b : BinBase) .
      BinBase.to_nat (a * b)%bin_base = (BinBase.to_nat a * BinBase.to_nat b)%n
  := BinBase.conversion.multiplication.

Definition data_number_all_delivers_bin_base_power
  : forall (a : BinBase) (n : BinBase) .
      BinBase.to_nat (a ^ n)%bin_base = (BinBase.to_nat a ^ BinBase.to_nat n)%n
  := BinBase.conversion.power.

Definition data_number_all_delivers_bin_base_comparison
  : forall (a : BinBase) (b : BinBase) .
      BinBase.compare a b = Nat.compare (BinBase.to_nat a) (BinBase.to_nat b)
  := BinBase.conversion.comparison.

Definition data_number_all_delivers_bin_base_subtraction
  : forall (a : BinBase) (b : BinBase) .
      Option.map BinBase.to_nat (BinBase.sub a b) = Nat.sub (BinBase.to_nat a) (BinBase.to_nat b)
  := BinBase.conversion.subtraction.

Definition data_number_all_delivers_bin_base_saturating_subtraction
  : forall (a : BinBase) (b : BinBase) .
      BinBase.to_nat (BinBase.saturating_sub a b)
      = Nat.saturating_sub (BinBase.to_nat a) (BinBase.to_nat b)
  := BinBase.conversion.subtraction.saturating.

Definition data_number_all_delivers_bin_base_multiplication_computes
  : (BinBase.b1 BinBase.One * BinBase.b0 (BinBase.b1 BinBase.One))%bin_base
    = BinBase.b0 (BinBase.b1 (BinBase.b0 (BinBase.b0 BinBase.One)))
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_base_comparison_computes
  : BinBase.compare (BinBase.b1 BinBase.One)
                   (BinBase.b0 (BinBase.b1 BinBase.One))
    = Comparison.Lt
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_retraction
  : forall (n : Nat0) .
      BinWithZero.to_nat0 (BinWithZero.from_nat0 n) = n
  := BinWithZero.conversion.retraction.

Definition data_number_all_delivers_bin_with_zero_addition
  : forall (m : BinWithZero) (n : BinWithZero) .
      BinWithZero.to_nat0 (m + n)%bin_with_zero
      = (BinWithZero.to_nat0 m + BinWithZero.to_nat0 n)%n0
  := BinWithZero.conversion.addition.

Definition data_number_all_delivers_bin_with_zero_subtraction
  : forall (m : BinWithZero) (n : BinWithZero) .
      Option.map BinWithZero.to_nat0 (BinWithZero.sub m n)
      = Nat0.sub (BinWithZero.to_nat0 m) (BinWithZero.to_nat0 n)
  := BinWithZero.conversion.subtraction.

Definition data_number_all_delivers_bin_with_zero_subtraction_computes
  : BinWithZero.sub (BinBase.b0 BinBase.One) (BinBase.b0 BinBase.One)
    = Some BinWithZero.Zero
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_conjunction_commutativity
  : forall (m : BinWithZero) (n : BinWithZero) .
      (m && n)%bin_with_zero = (n && m)%bin_with_zero
  := BinWithZero.conjunction.commutativity.

Definition data_number_all_delivers_bin_with_zero_sejunction_irreflexivity
  : forall (n : BinWithZero) . (n ^^ n)%bin_with_zero = BinWithZero.Zero
  := BinWithZero.sejunction.irreflexivity.

Definition data_number_all_delivers_bin_with_zero_shift_retraction
  : forall (n : BinWithZero) (k : Nat0) .
      BinWithZero.shift_right (BinWithZero.shift_left n k) k = n
  := BinWithZero.shift.retraction.

Definition data_number_all_delivers_bin_with_zero_left_shift
  : forall (n : BinWithZero) (k : Nat0) .
      BinWithZero.to_nat0 (BinWithZero.shift_left n k)
      = (BinWithZero.to_nat0 n
         * Nat0.Positive (Nat.Successor Nat.One) ^ k)%n0
  := BinWithZero.conversion.left.shift.

Definition data_number_all_delivers_bin_with_zero_conjunction_computes
  : (BinBase.b0 (BinBase.b0 (BinBase.b1 BinBase.One))
     && BinBase.b0 (BinBase.b1 (BinBase.b0 BinBase.One)))%bin_with_zero
    = BinBase.b0 (BinBase.b0 (BinBase.b0 BinBase.One))
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_disjunction_computes
  : (BinBase.b0 (BinBase.b0 (BinBase.b1 BinBase.One))
     || BinBase.b0 (BinBase.b1 (BinBase.b0 BinBase.One)))%bin_with_zero
    = BinBase.b0 (BinBase.b1 (BinBase.b1 BinBase.One))
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_sejunction_computes
  : (BinBase.b0 (BinBase.b0 (BinBase.b1 BinBase.One))
     ^^ BinBase.b0 (BinBase.b1 (BinBase.b0 BinBase.One)))%bin_with_zero
    = BinBase.b0 (BinBase.b1 BinBase.One)
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_shift_computes
  : BinWithZero.shift_left (BinBase.b1 BinBase.One) (Nat.Successor Nat.One)
    = BinBase.b0 (BinBase.b0 (BinBase.b1 BinBase.One))
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_bit_computes
  : BinWithZero.test_bit (BinBase.b0 (BinBase.b1 (BinBase.b0 BinBase.One)))
                            Nat.One
    = true
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_base_addition_commutativity
  : forall (a : BinBase) (b : BinBase) . (a + b)%bin_base = (b + a)%bin_base
  := BinBase.addition.commutativity.

Definition data_number_all_delivers_bin_base_order
  : forall (a : BinBase) (b : BinBase) .
      (a < b)%bin_base <-> (BinBase.to_nat a < BinBase.to_nat b)%n
  := BinBase.conversion.order.

Definition data_number_all_delivers_bin_base_well_founded
  : forall (b : BinBase) . Accessible BinBase.LessThan b
  := fun (b : BinBase) . accessibility b.

Definition data_number_all_delivers_bin_base_maximum_computes
  : BinBase.max (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One)
    = BinBase.b1 BinBase.One
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_distributivity
  : forall (x : BinWithZero) (y : BinWithZero) (z : BinWithZero) .
      ((x * (y + z)) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%bin_with_zero
  := BinWithZero.multiplication.distributivity.over.addition.

Definition data_number_all_delivers_bin_with_zero_well_founded
  : forall (n : BinWithZero) . Accessible BinWithZero.LessThan n
  := fun (n : BinWithZero) . accessibility n.

Definition data_number_all_delivers_bin_with_zero_narrowing_base_specification
  : forall (n : BinWithZero) (p : BinBase) . BinWithZero.to_bin_base n = Some p <-> n = p
  := BinWithZero.narrowing.base.specification.

Definition data_number_all_delivers_bin_with_zero_narrowing_base_failure
  : forall (n : BinWithZero) .
      BinWithZero.to_bin_base n = None <-> n = BinWithZero.Zero
  := BinWithZero.narrowing.base.failure.

Definition data_number_all_delivers_bin_with_zero_literal
  : (1011 + 1)%bin_with_zero = 1100%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_literal_zero
  : 0%bin_with_zero = BinWithZero.Zero
  := Identity.reflexivity _.

Fail Definition data_number_all_refuses_bin_with_zero_literal_digit
  : BinWithZero
  := 1021%bin_with_zero.

Definition data_number_all_delivers_bin_with_zero_large_power
  : (10 ^ 11001000)%bin_with_zero = (100 ^ 1100100)%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_with_zero_large_product
  : (1111111111111111 * 1111111111111111)%bin_with_zero
    = 11111111111111100000000000000001%bin_with_zero
  := Identity.reflexivity _.

Theorem data_number_all_delivers_coercion_bin_base_to_bin_with_zero
  : forall (b : BinBase) . BinWithZero.inc b = BinWithZero.inc (BinWithZero.Positive b).
Proof.
  intro b.
  quod idem est.
Qed.

Definition data_number_all_delivers_bin
  : Bin -> Verum
  := fun (_ : Bin) . I.

Definition data_number_all_delivers_bin_addition
  : forall (x : Bin) (y : Bin) .
      Bin.to_integer (x + y)%b
      = (Bin.to_integer x + Bin.to_integer y)%z
  := Bin.conversion.addition.

Definition data_number_all_delivers_bin_difference
  : forall (p : BinBase) (q : BinBase) .
      Bin.to_integer (Bin.bin_base_difference p q)
      = Integer.nat_difference (BinBase.to_nat p) (BinBase.to_nat q)
  := Bin.conversion.difference.

Definition data_number_all_delivers_bin_order
  : forall (x : Bin) (y : Bin) .
      (x < y)%b <-> (Bin.to_integer x < Bin.to_integer y)%z
  := Bin.conversion.order.

Definition data_number_all_delivers_bin_associativity
  : forall (x : Bin) (y : Bin) (z : Bin) .
      ((x + y) + z = x + (y + z))%b
  := Bin.addition.associativity.

Definition data_number_all_delivers_bin_inverse
  : forall (x : Bin) .
      ((Bin.negate x + x = Bin.Zero)
       /\ (x + Bin.negate x = Bin.Zero))%b
  := Bin.addition.inverse.

Definition data_number_all_delivers_bin_involution
  : forall (x : Bin) .
      Bin.negate (Bin.negate x) = x
  := Bin.negation.involution.

Definition data_number_all_delivers_bin_comparison
  : forall (x : Bin) (y : Bin) .
      (Bin.compare x y = Comparison.Lt <-> (x < y)%b)
      /\ (Bin.compare x y = Comparison.Eq <-> x = y)
  := Bin.comparison.specification.

Definition data_number_all_delivers_bin_literal
  : (1011 + 1)%b = 1100%b
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_literal_negative
  : ((-1011) + 1011)%b = 0%b
  := Identity.reflexivity _.

Definition data_number_all_delivers_bin_literal_zero
  : (-0)%b = Bin.Zero
  := Identity.reflexivity _.

Fail Definition data_number_all_refuses_bin_literal_digit
  : Bin
  := 1021%b.

Definition data_number_all_delivers_bin_well_founded_magnitude
  : forall (x : Bin) .
      Accessible (Induced BinWithZero.LessThan Bin.abs) x
  := fun (x : Bin) . accessibility x.

Definition data_number_all_delivers_bin_maximum_computes
  : Bin.max 1011%b (-1011)%b = 1011%b
  := Identity.reflexivity _.

Theorem data_number_all_delivers_coercion_bin_base_to_bin
  : forall (b : BinBase) .
      Bin.negate b = Bin.negate (Bin.Positive b).
Proof.
  intro b.
  quod idem est.
Qed.

(* The types the operations above return, named rather than merely produced. A
 * client who cannot write [Comparison] cannot state anything about [compare],
 * and every guard here would still have passed while that was true.
 *)
Definition data_number_all_delivers_comparison
  : Comparison
  := BinBase.compare BinBase.One BinBase.One.

Definition data_number_all_delivers_bool
  : Bool
  := BinBase.eq BinBase.One BinBase.One.

Definition data_number_all_delivers_option
  : Option BinBase
  := BinBase.sub (BinBase.b0 BinBase.One) BinBase.One.

Definition data_number_all_delivers_numeral
  : Numeral.Unsigned
  := BinWithZero.to_numeral 1011%bin_with_zero.
