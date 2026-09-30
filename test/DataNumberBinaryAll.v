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

Definition data_number_binary_all_delivers_bin_with_zero_literal
  : (1011 + 1)%bin_with_zero = 1100%bin_with_zero
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_literal
  : (1011 + 1)%b = 1100%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_literal_negative
  : ((-1011) + 1011)%b = 0%b
  := Identity.reflexivity _.

(* [compare]'s result type is not nameable here: neither this umbrella nor
 * [Data.Number.All] re-exports [Data.Base.Comparison]. The orderings are
 * exercised through [min] and [max], which answer in the types themselves.
 *)
Definition data_number_binary_all_delivers_bin_maximum_computes
  : Bin.max (Bin.b1 Bin.One) (Bin.b0 Bin.One) = Bin.b1 Bin.One
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_maximum_computes
  : BinWithSign.max (-1011)%b 1011%b = 1011%b
  := Identity.reflexivity _.

Definition data_number_binary_all_delivers_bin_with_sign_minimum_computes
  : BinWithSign.min (-1011)%b 1011%b = (-1011)%b
  := Identity.reflexivity _.
