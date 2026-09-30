(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [jwa.Data.Number.Binary.All] by importing that umbrella and nothing
 * else, so anything it fails to re-export is a build failure here. What
 * [Data.Number.All] forwards from it is guarded separately in
 * [DataNumberAll.v].
 *)
From jwa Require Import Data.Number.Binary.All.

Definition data_number_binary_all_delivers_types
  : Bin -> BinWithZero -> BinWithSign -> Verum
  := fun (_ : Bin) (_ : BinWithZero) (_ : BinWithSign) . I.

Definition data_number_binary_all_delivers_bin_notation
  : forall (a : Bin) (b : Bin) . (a + b)%bin = (b + a)%bin
  := Bin.addition.commutativity.

Definition data_number_binary_all_delivers_bin_with_zero_notation
  : forall (m : BinWithZero) (n : BinWithZero) .
      (m && n)%bin_with_zero = (n && m)%bin_with_zero
  := BinWithZero.conjunction.commutativity.

Definition data_number_binary_all_delivers_bin_with_sign_notation
  : forall (x : BinWithSign) (y : BinWithSign) (z : BinWithSign) .
      ((x + y) + z = x + (y + z))%b
  := BinWithSign.addition.associativity.

Definition data_number_binary_all_delivers_bin_with_sign_involution
  : forall (x : BinWithSign) .
      BinWithSign.negate (BinWithSign.negate x) = x
  := BinWithSign.negation.involution.

Definition data_number_binary_all_delivers_bin_with_sign_distributivity
  : forall (x : BinWithSign) (y : BinWithSign) (z : BinWithSign) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%b
  := BinWithSign.multiplication.distributivity.over.addition.

Definition data_number_binary_all_delivers_bin_with_zero_literal
  : (1011 + 1)%bin_with_zero = 1100%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_literal
  : (1011 + 1)%b = 1100%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_literal_negative
  : ((-1011) + 1011)%b = 0%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_multiplication_computes
  : ((-11) * 101)%b = (-1111)%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_comparison
  : Bin.compare (Bin.b1 Bin.One) (Bin.b0 Bin.One) = Comparison.Gt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_comparison
  : BinWithSign.compare (-1011)%b 1011%b = Comparison.Lt
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_maximum_computes
  : Bin.max (Bin.b1 Bin.One) (Bin.b0 Bin.One) = Bin.b1 Bin.One
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_maximum_computes
  : BinWithSign.max (-1011)%b 1011%b = 1011%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_minimum_computes
  : BinWithSign.min (-1011)%b 1011%b = (-1011)%b
  := Identity.reflexivity _.

(* The types the operations above take and return, named rather than merely
 * produced: a client who cannot write them cannot state anything about them.
 *)
Definition data_number_binary_all_delivers_bool
  : Bool
  := Bin.eq Bin.One Bin.One.

Definition data_number_binary_all_delivers_option
  : Option Bin
  := Bin.sub (Bin.b0 Bin.One) Bin.One.

Definition data_number_binary_all_delivers_nat
  : Nat
  := Bin.to_nat Bin.One.

Definition data_number_binary_all_delivers_nat_with_zero
  : NatWithZero
  := BinWithZero.to_nat_with_zero 1011%bin_with_zero.

Definition data_number_binary_all_delivers_integer
  : Integer
  := BinWithSign.to_integer (-1011)%b.

Definition data_number_binary_all_delivers_numeral
  : Numeral.Signed
  := BinWithSign.to_numeral (-1011)%b.

Definition data_number_binary_all_delivers_well_founded
  : forall (x : BinWithSign) . Accessible (Induced (<)%bin_with_zero BinWithSign.abs) x
  := fun (x : BinWithSign) . accessibility x.
