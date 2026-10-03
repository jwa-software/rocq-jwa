(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [jwa.Data.Number.Binary.All] by importing that umbrella and nothing
 * else, so anything it fails to re-export is a build failure here. What
 * [Data.Number.All] forwards from it is guarded separately in
 * [DataNumberAll.v].
 *)
From jwa Require Import Data.Number.Binary.All.

Definition data_number_binary_all_delivers_types
  : BinBase -> BinWithZero -> Bin -> Verum
  := fun (_ : BinBase) (_ : BinWithZero) (_ : Bin) . I.

Definition data_number_binary_all_delivers_bin_base_notation
  : forall (a : BinBase) (b : BinBase) . (a + b)%bin_base = (b + a)%bin_base
  := BinBase.addition.commutativity.

Definition data_number_binary_all_delivers_bin_with_zero_notation
  : forall (m : BinWithZero) (n : BinWithZero) .
      (m && n)%bin_with_zero = (n && m)%bin_with_zero
  := BinWithZero.conjunction.commutativity.

Definition data_number_binary_all_delivers_bin_notation
  : forall (x : Bin) (y : Bin) (z : Bin) .
      ((x + y) + z = x + (y + z))%b
  := Bin.addition.associativity.

Definition data_number_binary_all_delivers_bin_involution
  : forall (x : Bin) .
      Bin.negate (Bin.negate x) = x
  := Bin.negation.involution.

Definition data_number_binary_all_delivers_bin_distributivity
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%b
  := Bin.multiplication.distributivity.over.addition.

Definition data_number_binary_all_delivers_bin_with_zero_division_specification
  : forall (n : BinWithZero) (d : BinBase) .
      ((n /. d) * d + (n %. d) = n /\ (n %. d) < d)%bin_with_zero
  := BinWithZero.division.specification.

Definition data_number_binary_all_delivers_bin_with_zero_gcd_commutativity
  : forall (a : BinWithZero) (b : BinWithZero) . BinWithZero.gcd a b = BinWithZero.gcd b a
  := BinWithZero.gcd.commutativity.

Definition data_number_binary_all_delivers_bin_with_zero_shift_quotient
  : forall (n : BinWithZero) (k : BinBase) .
      BinWithZero.shift_right n (BinBase.to_nat k) = (n /. (10 ^ k)%bin_base)%bin_with_zero
  := BinWithZero.shift.right.quotient.

Definition data_number_binary_all_delivers_bin_division_magnitude
  : forall (x : Bin) (d : BinBase) .
      Bin.abs (x /. d)%b = (Bin.abs x /. d)%bin_with_zero
  := Bin.division.magnitude.

Definition data_number_binary_all_delivers_bin_base_literal
  : (1011 + 1)%bin_base = 1100%bin_base
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_literal
  : (1011 + 1)%bin_with_zero = 1100%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_literal
  : (1011 + 1)%b = 1100%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_literal_negative
  : ((-1011) + 1011)%b = 0%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_multiplication_computes
  : ((-11) * 101)%b = (-1111)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_division_computes
  : (1011 /. 11%bin_base)%bin_with_zero = 11%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_modulo_computes
  : (1011 %. 11%bin_base)%bin_with_zero = 10%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_zero_gcd_computes
  : BinWithZero.gcd 1100%bin_with_zero 10010%bin_with_zero = 110%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_division_computes
  : ((-1011) /. 11%bin_base)%b = (-11)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_division_computes
  : (1111111111111111111111111111111111111111111111111111111111111111
      /. 100000000000000000000000000000001%bin_base)%bin_with_zero
    = 11111111111111111111111111111111%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_large_gcd_computes
  : BinWithZero.gcd
      1111111111111111111111111111111111111111111111111111111111111111%bin_with_zero
      100000000000000000000000000000001%bin_with_zero
    = 100000000000000000000000000000001%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_comparison
  : BinBase.compare (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = Comparison.Gt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_comparison
  : Bin.compare (-1011)%b 1011%b = Comparison.Lt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_base_maximum_computes
  : BinBase.max (BinBase.b1 BinBase.One) (BinBase.b0 BinBase.One) = BinBase.b1 BinBase.One
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_maximum_computes
  : Bin.max (-1011)%b 1011%b = 1011%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_minimum_computes
  : Bin.min (-1011)%b 1011%b = (-1011)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_modulo_identity
  : forall (n : BinWithZero) (d : BinBase) .
      (n < BinWithZero.Positive d -> n %. d = n)%bin_with_zero
  := BinWithZero.modulo.identity.

Definition data_number_binary_all_delivers_modulo_sum_absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (((a %. d) + b) %. d = (a + b) %. d)%bin_with_zero
  := BinWithZero.modulo.sum.left.absorption.

Definition data_number_binary_all_delivers_modulo_product_absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (((a %. d) * b) %. d = (a * b) %. d)%bin_with_zero
  := BinWithZero.modulo.product.left.absorption.

Definition data_number_binary_all_delivers_shift_left_multiplication
  : forall (n : BinWithZero) (k : Nat0) .
      BinWithZero.shift_left n k = (n * BinWithZero.shift_left 1 k)%bin_with_zero
  := BinWithZero.shift.left.multiplication.

Definition data_number_binary_all_delivers_decimal_reading_computes
  : BinWithZero.from_decimal 0%bin_with_zero
      (Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End)))
    = 11111111%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_decimal_printing_computes
  : BinWithZero.to_decimal 11111111%bin_with_zero
    = Numeral.Decimal.Digits.Two
        (Numeral.Decimal.Digits.Five
          (Numeral.Decimal.Digits.Five Numeral.Decimal.Digits.End))
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_difference_additivity
  : forall (a : BinWithZero) (b : BinWithZero) (c : BinWithZero) (d : BinWithZero) .
      (Bin.bin_with_zero_difference a b + Bin.bin_with_zero_difference c d
        = Bin.bin_with_zero_difference (a + c)%bin_with_zero (b + d)%bin_with_zero)%b
  := Bin.difference.additivity.

Definition data_number_binary_all_delivers_difference_invariance
  : forall (a : BinWithZero) (b : BinWithZero) (c : BinWithZero) (d : BinWithZero) .
      (a + d = c + b)%bin_with_zero ->
      Bin.bin_with_zero_difference a b = Bin.bin_with_zero_difference c d
  := @Bin.difference.invariance.

(* The types the operations above take and return, named rather than merely
 * produced: a client who cannot write them cannot state anything about them.
 *)
Definition data_number_binary_all_delivers_bool
  : Bool
  := BinBase.eq BinBase.One BinBase.One.

Definition data_number_binary_all_delivers_option
  : Option BinBase
  := BinBase.sub (BinBase.b0 BinBase.One) BinBase.One.

Definition data_number_binary_all_delivers_product
  : Product BinWithZero BinWithZero
  := BinWithZero.div 1011%bin_with_zero 11%bin_base.

Definition data_number_binary_all_delivers_nat
  : Nat
  := BinBase.to_nat BinBase.One.

Definition data_number_binary_all_delivers_nat0
  : Nat0
  := BinWithZero.to_nat0 1011%bin_with_zero.

Definition data_number_binary_all_delivers_integer
  : Integer
  := Bin.to_integer (-1011)%b.

Definition data_number_binary_all_delivers_numeral
  : Numeral.Signed
  := Bin.to_numeral (-1011)%b.

Definition data_number_binary_all_delivers_well_founded
  : forall (x : Bin) . Accessible (Induced (<)%bin_with_zero Bin.abs) x
  := fun (x : Bin) . WellFounded.accessibility x.
