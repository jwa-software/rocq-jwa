(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Machine.DWord.
From jwa Require Import Data.Machine.Endian.
From jwa Require Import Data.Number.Binary.Bin.
From jwa Require Import Data.Number.Binary.BinBase.
From jwa Require Import Data.Number.Binary.BinWithZero.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A signed integer of sixty-four bits: eight [Byte]s read in two's complement,
 * from -9223372036854775808 (-2^63) to 9223372036854775807 (2^63 - 1), its
 * arithmetic wrapping modulo 18446744073709551616 (2^64). In this file
 * [10000000000000000000000000000000000000000000000000000000000000000] is 2^64,
 * [1000000000000000000000000000000000000000000000000000000000000000] is 2^63
 * and [111111111111111111111111111111111111111111111111111111111111111] is
 * 2^63 - 1, written in binary digits.
 *)

Module Int64. (* Int64 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> T.

Abbreviation Int64 := T.

(* The number of values, 18446744073709551616 (2^64), the arithmetic wrapping
 * modulo it.
 *)
(* [BinBase] *)
Definition modulus := 10000000000000000000000000000000000000000000000000000000000000000%bin_base.

(* [x] laid out as a [DWord] in the order [e] names. *)
(* [Endian -> Int64 -> DWord] *)
Definition to_dword := fun (e : Endian) (x : Int64) .
  match x with
  | Int64.introduction b7 b6 b5 b4 b3 b2 b1 b0 => DWord.make e b0 b1 b2 b3 b4 b5 b6 b7
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [DWord -> Int64] *)
Definition from_dword := fun (w : DWord) .
  Int64.introduction
    (DWord.byte7 w) (DWord.byte6 w) (DWord.byte5 w) (DWord.byte4 w)
    (DWord.byte3 w) (DWord.byte2 w) (DWord.byte1 w) (DWord.byte0 w).

(* The bits read as a number in base two, the most significant first, from 0 to
 * 18446744073709551615: the value of the bit pattern, through which the
 * arithmetic is proved and from which [to_bin] takes the signed value; [10] is
 * two in binary digits.
 *)
(* [Int64 -> BinWithZero] *)
Definition unsigned_value := fun (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * (10 * (10 * Bit.to_bin_with_zero x63 + Bit.to_bin_with_zero x62)
        + Bit.to_bin_with_zero x61) + Bit.to_bin_with_zero x60) + Bit.to_bin_with_zero x59)
        + Bit.to_bin_with_zero x58) + Bit.to_bin_with_zero x57) + Bit.to_bin_with_zero x56)
        + Bit.to_bin_with_zero x55) + Bit.to_bin_with_zero x54) + Bit.to_bin_with_zero x53)
        + Bit.to_bin_with_zero x52) + Bit.to_bin_with_zero x51) + Bit.to_bin_with_zero x50)
        + Bit.to_bin_with_zero x49) + Bit.to_bin_with_zero x48) + Bit.to_bin_with_zero x47)
        + Bit.to_bin_with_zero x46) + Bit.to_bin_with_zero x45) + Bit.to_bin_with_zero x44)
        + Bit.to_bin_with_zero x43) + Bit.to_bin_with_zero x42) + Bit.to_bin_with_zero x41)
        + Bit.to_bin_with_zero x40) + Bit.to_bin_with_zero x39) + Bit.to_bin_with_zero x38)
        + Bit.to_bin_with_zero x37) + Bit.to_bin_with_zero x36) + Bit.to_bin_with_zero x35)
        + Bit.to_bin_with_zero x34) + Bit.to_bin_with_zero x33) + Bit.to_bin_with_zero x32)
        + Bit.to_bin_with_zero x31) + Bit.to_bin_with_zero x30) + Bit.to_bin_with_zero x29)
        + Bit.to_bin_with_zero x28) + Bit.to_bin_with_zero x27) + Bit.to_bin_with_zero x26)
        + Bit.to_bin_with_zero x25) + Bit.to_bin_with_zero x24) + Bit.to_bin_with_zero x23)
        + Bit.to_bin_with_zero x22) + Bit.to_bin_with_zero x21) + Bit.to_bin_with_zero x20)
        + Bit.to_bin_with_zero x19) + Bit.to_bin_with_zero x18) + Bit.to_bin_with_zero x17)
        + Bit.to_bin_with_zero x16) + Bit.to_bin_with_zero x15) + Bit.to_bin_with_zero x14)
        + Bit.to_bin_with_zero x13) + Bit.to_bin_with_zero x12) + Bit.to_bin_with_zero x11)
        + Bit.to_bin_with_zero x10) + Bit.to_bin_with_zero x9) + Bit.to_bin_with_zero x8)
        + Bit.to_bin_with_zero x7) + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5)
        + Bit.to_bin_with_zero x4) + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2)
        + Bit.to_bin_with_zero x1) + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* The top bit, [1] for a negative value. *)
(* [Int64 -> Bit] *)
Definition sign_bit := fun (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 _ _ _ _ _ _ _) _ _ _ _ _ _ _ => x63
  end.

(* The value in two's complement: the unsigned value, less 18446744073709551616
 * when the sign bit is set.
 *)
(* [Int64 -> Bin] *)
Definition to_bin := fun (x : Int64) .
  Bin.bin_with_zero_difference
    (unsigned_value x) (modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.

(* From here to the end of the module an [Int64] stands where a [Bin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_bin : T >-> Bin.
Add Printing Coercion to_bin.

(* The value in [Integer], through [to_bin]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_bin].
 *)
(* [Int64 -> Integer] *)
Definition to_integer := fun (x : Int64) . Bin.to_integer (to_bin x).

(* [Int64] *)
Definition Zero := Int64.introduction Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero
  Byte.Zero Byte.Zero.

(* [Int64] *)
Definition One :=
  Int64.introduction
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [Int64 -> Nat -> Int64] *)
Fixpoint shift_left_nat (x : Int64) (k : Nat) : Int64 :=
  let y :=
    match x with
    | Int64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [Int64 -> Nat0 -> Int64] *)
Definition shift_left := fun (x : Int64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int64 -> Nat -> Int64] *)
Fixpoint shift_right_nat (x : Int64) (k : Nat) : Int64 :=
  let y :=
    match x with
    | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int64.introduction (Byte.introduction x63 x63 x62 x61 x60 x59 x58 x57)
          (Byte.introduction x56 x55 x54 x53 x52 x51 x50 x49)
          (Byte.introduction x48 x47 x46 x45 x44 x43 x42 x41)
          (Byte.introduction x40 x39 x38 x37 x36 x35 x34 x33)
          (Byte.introduction x32 x31 x30 x29 x28 x27 x26 x25)
          (Byte.introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int64 -> Nat0 -> Int64] *)
Definition shift_right := fun (x : Int64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int64 -> Int64] *)
Definition append_bit := fun (b : Bit) (x : Int64) .
  match x with
  | Int64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      Int64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
        (Byte.introduction x54 x53 x52 x51 x50 x49 x48 x47)
        (Byte.introduction x46 x45 x44 x43 x42 x41 x40 x39)
        (Byte.introduction x38 x37 x36 x35 x34 x33 x32 x31)
        (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
        (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
        (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int64 -> Int64 -> Product Bit Int64] *)
Definition add_with_carry := fun (carry : Bit) (x : Int64) (y : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
          (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
          (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
          (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
          (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
          (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
          (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          let r8 := Bit.add_with_carry (pi_1 r7) x8 y8 in
          let r9 := Bit.add_with_carry (pi_1 r8) x9 y9 in
          let r10 := Bit.add_with_carry (pi_1 r9) x10 y10 in
          let r11 := Bit.add_with_carry (pi_1 r10) x11 y11 in
          let r12 := Bit.add_with_carry (pi_1 r11) x12 y12 in
          let r13 := Bit.add_with_carry (pi_1 r12) x13 y13 in
          let r14 := Bit.add_with_carry (pi_1 r13) x14 y14 in
          let r15 := Bit.add_with_carry (pi_1 r14) x15 y15 in
          let r16 := Bit.add_with_carry (pi_1 r15) x16 y16 in
          let r17 := Bit.add_with_carry (pi_1 r16) x17 y17 in
          let r18 := Bit.add_with_carry (pi_1 r17) x18 y18 in
          let r19 := Bit.add_with_carry (pi_1 r18) x19 y19 in
          let r20 := Bit.add_with_carry (pi_1 r19) x20 y20 in
          let r21 := Bit.add_with_carry (pi_1 r20) x21 y21 in
          let r22 := Bit.add_with_carry (pi_1 r21) x22 y22 in
          let r23 := Bit.add_with_carry (pi_1 r22) x23 y23 in
          let r24 := Bit.add_with_carry (pi_1 r23) x24 y24 in
          let r25 := Bit.add_with_carry (pi_1 r24) x25 y25 in
          let r26 := Bit.add_with_carry (pi_1 r25) x26 y26 in
          let r27 := Bit.add_with_carry (pi_1 r26) x27 y27 in
          let r28 := Bit.add_with_carry (pi_1 r27) x28 y28 in
          let r29 := Bit.add_with_carry (pi_1 r28) x29 y29 in
          let r30 := Bit.add_with_carry (pi_1 r29) x30 y30 in
          let r31 := Bit.add_with_carry (pi_1 r30) x31 y31 in
          let r32 := Bit.add_with_carry (pi_1 r31) x32 y32 in
          let r33 := Bit.add_with_carry (pi_1 r32) x33 y33 in
          let r34 := Bit.add_with_carry (pi_1 r33) x34 y34 in
          let r35 := Bit.add_with_carry (pi_1 r34) x35 y35 in
          let r36 := Bit.add_with_carry (pi_1 r35) x36 y36 in
          let r37 := Bit.add_with_carry (pi_1 r36) x37 y37 in
          let r38 := Bit.add_with_carry (pi_1 r37) x38 y38 in
          let r39 := Bit.add_with_carry (pi_1 r38) x39 y39 in
          let r40 := Bit.add_with_carry (pi_1 r39) x40 y40 in
          let r41 := Bit.add_with_carry (pi_1 r40) x41 y41 in
          let r42 := Bit.add_with_carry (pi_1 r41) x42 y42 in
          let r43 := Bit.add_with_carry (pi_1 r42) x43 y43 in
          let r44 := Bit.add_with_carry (pi_1 r43) x44 y44 in
          let r45 := Bit.add_with_carry (pi_1 r44) x45 y45 in
          let r46 := Bit.add_with_carry (pi_1 r45) x46 y46 in
          let r47 := Bit.add_with_carry (pi_1 r46) x47 y47 in
          let r48 := Bit.add_with_carry (pi_1 r47) x48 y48 in
          let r49 := Bit.add_with_carry (pi_1 r48) x49 y49 in
          let r50 := Bit.add_with_carry (pi_1 r49) x50 y50 in
          let r51 := Bit.add_with_carry (pi_1 r50) x51 y51 in
          let r52 := Bit.add_with_carry (pi_1 r51) x52 y52 in
          let r53 := Bit.add_with_carry (pi_1 r52) x53 y53 in
          let r54 := Bit.add_with_carry (pi_1 r53) x54 y54 in
          let r55 := Bit.add_with_carry (pi_1 r54) x55 y55 in
          let r56 := Bit.add_with_carry (pi_1 r55) x56 y56 in
          let r57 := Bit.add_with_carry (pi_1 r56) x57 y57 in
          let r58 := Bit.add_with_carry (pi_1 r57) x58 y58 in
          let r59 := Bit.add_with_carry (pi_1 r58) x59 y59 in
          let r60 := Bit.add_with_carry (pi_1 r59) x60 y60 in
          let r61 := Bit.add_with_carry (pi_1 r60) x61 y61 in
          let r62 := Bit.add_with_carry (pi_1 r61) x62 y62 in
          let r63 := Bit.add_with_carry (pi_1 r62) x63 y63 in
          (pi_1 r63,
            Int64.introduction
              (Byte.introduction
                (pi_2 r63) (pi_2 r62) (pi_2 r61) (pi_2 r60)
                (pi_2 r59) (pi_2 r58) (pi_2 r57) (pi_2 r56))
              (Byte.introduction
                (pi_2 r55) (pi_2 r54) (pi_2 r53) (pi_2 r52)
                (pi_2 r51) (pi_2 r50) (pi_2 r49) (pi_2 r48))
              (Byte.introduction
                (pi_2 r47) (pi_2 r46) (pi_2 r45) (pi_2 r44)
                (pi_2 r43) (pi_2 r42) (pi_2 r41) (pi_2 r40))
              (Byte.introduction
                (pi_2 r39) (pi_2 r38) (pi_2 r37) (pi_2 r36)
                (pi_2 r35) (pi_2 r34) (pi_2 r33) (pi_2 r32))
              (Byte.introduction
                (pi_2 r31) (pi_2 r30) (pi_2 r29) (pi_2 r28)
                (pi_2 r27) (pi_2 r26) (pi_2 r25) (pi_2 r24))
              (Byte.introduction
                (pi_2 r23) (pi_2 r22) (pi_2 r21) (pi_2 r20)
                (pi_2 r19) (pi_2 r18) (pi_2 r17) (pi_2 r16))
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int64 -> Int64 -> Int64] *)
Definition add := fun (x : Int64) (y : Int64) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_int64_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int64 -> Int64 -> Product Bit Int64] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int64) (y : Int64) .
  match x with
  | Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
          (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
          (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
          (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
          (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
          (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
          (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          let r8 := Bit.sub_with_borrow (pi_1 r7) x8 y8 in
          let r9 := Bit.sub_with_borrow (pi_1 r8) x9 y9 in
          let r10 := Bit.sub_with_borrow (pi_1 r9) x10 y10 in
          let r11 := Bit.sub_with_borrow (pi_1 r10) x11 y11 in
          let r12 := Bit.sub_with_borrow (pi_1 r11) x12 y12 in
          let r13 := Bit.sub_with_borrow (pi_1 r12) x13 y13 in
          let r14 := Bit.sub_with_borrow (pi_1 r13) x14 y14 in
          let r15 := Bit.sub_with_borrow (pi_1 r14) x15 y15 in
          let r16 := Bit.sub_with_borrow (pi_1 r15) x16 y16 in
          let r17 := Bit.sub_with_borrow (pi_1 r16) x17 y17 in
          let r18 := Bit.sub_with_borrow (pi_1 r17) x18 y18 in
          let r19 := Bit.sub_with_borrow (pi_1 r18) x19 y19 in
          let r20 := Bit.sub_with_borrow (pi_1 r19) x20 y20 in
          let r21 := Bit.sub_with_borrow (pi_1 r20) x21 y21 in
          let r22 := Bit.sub_with_borrow (pi_1 r21) x22 y22 in
          let r23 := Bit.sub_with_borrow (pi_1 r22) x23 y23 in
          let r24 := Bit.sub_with_borrow (pi_1 r23) x24 y24 in
          let r25 := Bit.sub_with_borrow (pi_1 r24) x25 y25 in
          let r26 := Bit.sub_with_borrow (pi_1 r25) x26 y26 in
          let r27 := Bit.sub_with_borrow (pi_1 r26) x27 y27 in
          let r28 := Bit.sub_with_borrow (pi_1 r27) x28 y28 in
          let r29 := Bit.sub_with_borrow (pi_1 r28) x29 y29 in
          let r30 := Bit.sub_with_borrow (pi_1 r29) x30 y30 in
          let r31 := Bit.sub_with_borrow (pi_1 r30) x31 y31 in
          let r32 := Bit.sub_with_borrow (pi_1 r31) x32 y32 in
          let r33 := Bit.sub_with_borrow (pi_1 r32) x33 y33 in
          let r34 := Bit.sub_with_borrow (pi_1 r33) x34 y34 in
          let r35 := Bit.sub_with_borrow (pi_1 r34) x35 y35 in
          let r36 := Bit.sub_with_borrow (pi_1 r35) x36 y36 in
          let r37 := Bit.sub_with_borrow (pi_1 r36) x37 y37 in
          let r38 := Bit.sub_with_borrow (pi_1 r37) x38 y38 in
          let r39 := Bit.sub_with_borrow (pi_1 r38) x39 y39 in
          let r40 := Bit.sub_with_borrow (pi_1 r39) x40 y40 in
          let r41 := Bit.sub_with_borrow (pi_1 r40) x41 y41 in
          let r42 := Bit.sub_with_borrow (pi_1 r41) x42 y42 in
          let r43 := Bit.sub_with_borrow (pi_1 r42) x43 y43 in
          let r44 := Bit.sub_with_borrow (pi_1 r43) x44 y44 in
          let r45 := Bit.sub_with_borrow (pi_1 r44) x45 y45 in
          let r46 := Bit.sub_with_borrow (pi_1 r45) x46 y46 in
          let r47 := Bit.sub_with_borrow (pi_1 r46) x47 y47 in
          let r48 := Bit.sub_with_borrow (pi_1 r47) x48 y48 in
          let r49 := Bit.sub_with_borrow (pi_1 r48) x49 y49 in
          let r50 := Bit.sub_with_borrow (pi_1 r49) x50 y50 in
          let r51 := Bit.sub_with_borrow (pi_1 r50) x51 y51 in
          let r52 := Bit.sub_with_borrow (pi_1 r51) x52 y52 in
          let r53 := Bit.sub_with_borrow (pi_1 r52) x53 y53 in
          let r54 := Bit.sub_with_borrow (pi_1 r53) x54 y54 in
          let r55 := Bit.sub_with_borrow (pi_1 r54) x55 y55 in
          let r56 := Bit.sub_with_borrow (pi_1 r55) x56 y56 in
          let r57 := Bit.sub_with_borrow (pi_1 r56) x57 y57 in
          let r58 := Bit.sub_with_borrow (pi_1 r57) x58 y58 in
          let r59 := Bit.sub_with_borrow (pi_1 r58) x59 y59 in
          let r60 := Bit.sub_with_borrow (pi_1 r59) x60 y60 in
          let r61 := Bit.sub_with_borrow (pi_1 r60) x61 y61 in
          let r62 := Bit.sub_with_borrow (pi_1 r61) x62 y62 in
          let r63 := Bit.sub_with_borrow (pi_1 r62) x63 y63 in
          (pi_1 r63,
            Int64.introduction
              (Byte.introduction
                (pi_2 r63) (pi_2 r62) (pi_2 r61) (pi_2 r60)
                (pi_2 r59) (pi_2 r58) (pi_2 r57) (pi_2 r56))
              (Byte.introduction
                (pi_2 r55) (pi_2 r54) (pi_2 r53) (pi_2 r52)
                (pi_2 r51) (pi_2 r50) (pi_2 r49) (pi_2 r48))
              (Byte.introduction
                (pi_2 r47) (pi_2 r46) (pi_2 r45) (pi_2 r44)
                (pi_2 r43) (pi_2 r42) (pi_2 r41) (pi_2 r40))
              (Byte.introduction
                (pi_2 r39) (pi_2 r38) (pi_2 r37) (pi_2 r36)
                (pi_2 r35) (pi_2 r34) (pi_2 r33) (pi_2 r32))
              (Byte.introduction
                (pi_2 r31) (pi_2 r30) (pi_2 r29) (pi_2 r28)
                (pi_2 r27) (pi_2 r26) (pi_2 r25) (pi_2 r24))
              (Byte.introduction
                (pi_2 r23) (pi_2 r22) (pi_2 r21) (pi_2 r20)
                (pi_2 r19) (pi_2 r18) (pi_2 r17) (pi_2 r16))
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int64 -> Int64 -> Int64] *)
Definition sub := fun (x : Int64) (y : Int64) . (pi_2 (sub_with_borrow 0 x y))%product.

(* [x] taken from [Zero], wrapping. *)
(* [Int64 -> Int64] *)
Definition negate := fun (x : Int64) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_int64_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 18446744073709551616.
 *)
(* [Int64 -> Int64 -> Int64] *)
Definition mul := fun (x : Int64) (y : Int64) .
  let step := fun (p : Int64) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
      (Byte.introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        (step (step (step Zero y63) y62) y61) y60) y59) y58) y57) y56) y55) y54) y53) y52) y51) y50)
        y49) y48) y47) y46) y45) y44) y43) y42) y41) y40) y39) y38) y37) y36) y35) y34) y33) y32)
        y31) y30) y29) y28) y27) y26) y25) y24) y23) y22) y21) y20) y19) y18) y17) y16) y15) y14)
        y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_int64_scope.

(* The bit pattern of [p] modulo 18446744073709551616, its bits appended from
 * the most significant.
 *)
(* [BinBase -> Int64] *)
Fixpoint from_bin_base (p : BinBase) : Int64 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [BinWithZero -> Int64] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> Int64] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> Int64] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [z] modulo 18446744073709551616 into the range -9223372036854775808 to
 * 9223372036854775807: its positive part less its negative part, wrapping.
 *)
(* [Bin -> Int64] *)
Definition from_bin := fun (z : Bin) .
  add (from_bin_with_zero (Bin.ramp z)) (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).

(* The quotient through [Bin], toward zero, [None] when [y] is zero. [Bin.divide]
 * takes a positive divisor, so the divisor's sign is matched here;
 * -9223372036854775808 (-2^63) over -1 wraps to itself.
 *)
(* [Int64 -> Int64 -> Option Int64] *)
Definition divide := fun (x : Int64) (y : Int64) .
  match to_bin y with
  | Bin.Negative d => Some (from_bin (Bin.negate (x /. d)%b))
  | Bin.Zero       => None
  | Bin.Positive d => Some (from_bin (x /. d)%b)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jwa_int64_scope.

(* [x] modulo 18446744073709551616 into the range -9223372036854775808 to
 * 9223372036854775807.
 *)
(* [Integer -> Int64] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past
 * -9223372036854775808 or 9223372036854775807.
 *)
(* [Int64 -> Int64 -> Product Bit Int64] *)
Definition add_with_overflow := fun (x : Int64) (y : Int64) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* [Int64 -> Int64 -> Prop] *)
Definition LessThan := fun (x : Int64) (y : Int64) . (to_bin x < to_bin y)%b.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_int64_scope.

(* [Int64 -> Int64 -> Prop] *)
Definition LessOrEqual := fun (x : Int64) (y : Int64) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_int64_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_int64_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_int64_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_int64_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_int64_scope.

(* [Int64 -> Int64 -> Comparison] *)
Definition compare := fun (x : Int64) (y : Int64) . Bin.compare (to_bin x) (to_bin y).

(* [Int64 -> Int64 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int64 -> Int64 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int64 -> Int64 -> Int64] *)
Abbreviation min := (Comparable.min compare).

(* [Int64 -> Int64 -> Int64] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -9223372036854775808 to 9223372036854775807, in decimal or
 * hexadecimal, read in binary; any wider is refused.
 *)
(* [Numeral.Signed -> Option Int64] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : BinWithZero) .
    match BinWithZero.compare v
      111111111111111111111111111111111111111111111111111111111111111%bin_with_zero with
    | Comparison.Lt => Some (from_bin_with_zero v)
    | Comparison.Eq => Some (from_bin_with_zero v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : BinWithZero) .
    match BinWithZero.compare v
      1000000000000000000000000000000000000000000000000000000000000000%bin_with_zero with
    | Comparison.Lt => Some (negate (from_bin_with_zero v))
    | Comparison.Eq => Some (negate (from_bin_with_zero v))
    | Comparison.Gt => None
    end in
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      positive (BinWithZero.from_decimal 0%bin_with_zero d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      negative (BinWithZero.from_decimal 0%bin_with_zero d)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Positive h) =>
      positive (BinWithZero.from_hexadecimal 0%bin_with_zero h)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Negative h) =>
      negative (BinWithZero.from_hexadecimal 0%bin_with_zero h)
  end.

(* [x] as a literal, in decimal; zero prints as [0], not [-0]. *)
(* [Int64 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int64) .
  match to_bin x with
  | Bin.Negative p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative (BinWithZero.to_decimal (BinWithZero.Positive p)))
  | Bin.Zero =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | Bin.Positive p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive (BinWithZero.to_decimal (BinWithZero.Positive p)))
  end.

Local Open Scope jwa_int64_scope.

Module valuation. (* valuation *)

(* valuation.zero *)
Theorem zero : unsigned_value Zero = 0%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* valuation.one *)
Theorem one : unsigned_value One = 1%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* valuation.boundedness *)
Theorem boundedness : forall (x : Int64) . (unsigned_value x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl unsigned_value in |- *.
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness &x63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* valuation.injectivity *)
Theorem injectivity
  : forall {x : Int64} {y : Int64} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value in &e.
  match (Bit.conversion.binary.halving.injectivity &e) with | e1 b0 end.
  match (Bit.conversion.binary.halving.injectivity &e1) with | e2 b1 end.
  match (Bit.conversion.binary.halving.injectivity &e2) with | e3 b2 end.
  match (Bit.conversion.binary.halving.injectivity &e3) with | e4 b3 end.
  match (Bit.conversion.binary.halving.injectivity &e4) with | e5 b4 end.
  match (Bit.conversion.binary.halving.injectivity &e5) with | e6 b5 end.
  match (Bit.conversion.binary.halving.injectivity &e6) with | e7 b6 end.
  match (Bit.conversion.binary.halving.injectivity &e7) with | e8 b7 end.
  match (Bit.conversion.binary.halving.injectivity &e8) with | e9 b8 end.
  match (Bit.conversion.binary.halving.injectivity &e9) with | e10 b9 end.
  match (Bit.conversion.binary.halving.injectivity &e10) with | e11 b10 end.
  match (Bit.conversion.binary.halving.injectivity &e11) with | e12 b11 end.
  match (Bit.conversion.binary.halving.injectivity &e12) with | e13 b12 end.
  match (Bit.conversion.binary.halving.injectivity &e13) with | e14 b13 end.
  match (Bit.conversion.binary.halving.injectivity &e14) with | e15 b14 end.
  match (Bit.conversion.binary.halving.injectivity &e15) with | e16 b15 end.
  match (Bit.conversion.binary.halving.injectivity &e16) with | e17 b16 end.
  match (Bit.conversion.binary.halving.injectivity &e17) with | e18 b17 end.
  match (Bit.conversion.binary.halving.injectivity &e18) with | e19 b18 end.
  match (Bit.conversion.binary.halving.injectivity &e19) with | e20 b19 end.
  match (Bit.conversion.binary.halving.injectivity &e20) with | e21 b20 end.
  match (Bit.conversion.binary.halving.injectivity &e21) with | e22 b21 end.
  match (Bit.conversion.binary.halving.injectivity &e22) with | e23 b22 end.
  match (Bit.conversion.binary.halving.injectivity &e23) with | e24 b23 end.
  match (Bit.conversion.binary.halving.injectivity &e24) with | e25 b24 end.
  match (Bit.conversion.binary.halving.injectivity &e25) with | e26 b25 end.
  match (Bit.conversion.binary.halving.injectivity &e26) with | e27 b26 end.
  match (Bit.conversion.binary.halving.injectivity &e27) with | e28 b27 end.
  match (Bit.conversion.binary.halving.injectivity &e28) with | e29 b28 end.
  match (Bit.conversion.binary.halving.injectivity &e29) with | e30 b29 end.
  match (Bit.conversion.binary.halving.injectivity &e30) with | e31 b30 end.
  match (Bit.conversion.binary.halving.injectivity &e31) with | e32 b31 end.
  match (Bit.conversion.binary.halving.injectivity &e32) with | e33 b32 end.
  match (Bit.conversion.binary.halving.injectivity &e33) with | e34 b33 end.
  match (Bit.conversion.binary.halving.injectivity &e34) with | e35 b34 end.
  match (Bit.conversion.binary.halving.injectivity &e35) with | e36 b35 end.
  match (Bit.conversion.binary.halving.injectivity &e36) with | e37 b36 end.
  match (Bit.conversion.binary.halving.injectivity &e37) with | e38 b37 end.
  match (Bit.conversion.binary.halving.injectivity &e38) with | e39 b38 end.
  match (Bit.conversion.binary.halving.injectivity &e39) with | e40 b39 end.
  match (Bit.conversion.binary.halving.injectivity &e40) with | e41 b40 end.
  match (Bit.conversion.binary.halving.injectivity &e41) with | e42 b41 end.
  match (Bit.conversion.binary.halving.injectivity &e42) with | e43 b42 end.
  match (Bit.conversion.binary.halving.injectivity &e43) with | e44 b43 end.
  match (Bit.conversion.binary.halving.injectivity &e44) with | e45 b44 end.
  match (Bit.conversion.binary.halving.injectivity &e45) with | e46 b45 end.
  match (Bit.conversion.binary.halving.injectivity &e46) with | e47 b46 end.
  match (Bit.conversion.binary.halving.injectivity &e47) with | e48 b47 end.
  match (Bit.conversion.binary.halving.injectivity &e48) with | e49 b48 end.
  match (Bit.conversion.binary.halving.injectivity &e49) with | e50 b49 end.
  match (Bit.conversion.binary.halving.injectivity &e50) with | e51 b50 end.
  match (Bit.conversion.binary.halving.injectivity &e51) with | e52 b51 end.
  match (Bit.conversion.binary.halving.injectivity &e52) with | e53 b52 end.
  match (Bit.conversion.binary.halving.injectivity &e53) with | e54 b53 end.
  match (Bit.conversion.binary.halving.injectivity &e54) with | e55 b54 end.
  match (Bit.conversion.binary.halving.injectivity &e55) with | e56 b55 end.
  match (Bit.conversion.binary.halving.injectivity &e56) with | e57 b56 end.
  match (Bit.conversion.binary.halving.injectivity &e57) with | e58 b57 end.
  match (Bit.conversion.binary.halving.injectivity &e58) with | e59 b58 end.
  match (Bit.conversion.binary.halving.injectivity &e59) with | e60 b59 end.
  match (Bit.conversion.binary.halving.injectivity &e60) with | e61 b60 end.
  match (Bit.conversion.binary.halving.injectivity &e61) with | e62 b61 end.
  match (Bit.conversion.binary.halving.injectivity &e62) with | e63 b62 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, &b7, &b8, &b9, &b10, &b11, &b12, &b13, &b14, &b15, &b16,
    &b17, &b18, &b19, &b20, &b21, &b22, &b23, &b24, &b25, &b26, &b27, &b28, &b29, &b30, &b31, &b32,
    &b33, &b34, &b35, &b36, &b37, &b38, &b39, &b40, &b41, &b42, &b43, &b44, &b45, &b46, &b47, &b48,
    &b49, &b50, &b51, &b52, &b53, &b54, &b55, &b56, &b57, &b58, &b59, &b60, &b61, &b62,
    (Bit.conversion.binary.injectivity &e63)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* valuation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int64) (y : Int64) .
      (Bit.to_bin_with_zero carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, add_with_carry in |- *.
  ipso
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.carry _ &x63 &y63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* valuation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int64) (y : Int64) .
      (unsigned_value x
        + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_bin_with_zero borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, sub_with_borrow in |- *.
  ipso
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
    (Bit.conversion.binary.borrow _ &x63 &y63)
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* valuation.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) .
      (unsigned_value (x + y)%int64
        = (unsigned_value x + unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int64
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int64 < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          modulus),
        <- (valuation.carry 0 &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (valuation.boundedness (&x + &y)).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value &x + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          (unsigned_value (&x + &y)%int64)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* valuation.subtraction *)
Theorem subtraction
  : forall (x : Int64) (y : Int64) .
      ((unsigned_value (sub x y) + unsigned_value y) %. modulus
        = unsigned_value x)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product * modulus
        + unsigned_value &x
        = unsigned_value (sub &x &y) + unsigned_value &y
      /\ unsigned_value &x < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)
          modulus),
        (BinWithZero.addition.commutativity
          (modulus
            * Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)%bin_with_zero
          (unsigned_value &x)),
        (valuation.borrow 0 &x &y),
        (BinWithZero.addition.commutativity
          (unsigned_value &y) (Bit.to_bin_with_zero 0))
        in |- *.
      simpl in |- *.
      leibniz
        (BinWithZero.addition.commutativity
          (unsigned_value &y)
          (unsigned_value (pi_2 (sub_with_borrow 0 &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (valuation.boundedness &x).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value (sub &x &y) + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)
          (unsigned_value &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* valuation.negation *)
Theorem negation
  : forall (x : Int64) .
      ((unsigned_value (- x)%int64 + unsigned_value x) %. modulus
        = 0)%bin_with_zero.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (valuation.subtraction Zero &x), valuation.zero in |- *.
  quod idem est.
Qed.

(* The bits of [x] and then [b] read from the most significant: [b] goes in
 * below and the highest bit falls out, one
 * [Bit.conversion.binary.appending.propagation] per place.
 *)
(* valuation.appending *)
Theorem appending
  : forall (b : Bit) (x : Int64) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x63 * modulus
        + unsigned_value
            (append_bit &b
              (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                  (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                  (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                  (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                  (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ unsigned_value
          (append_bit &b
            (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%bin_with_zero.
  {
    divide et impera.
    - lemma top
        : (Bit.to_bin_with_zero &x63 = Bit.to_bin_with_zero &x63 * 1 + 0)%bin_with_zero.
      {
        match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x63 * 1)%bin_with_zero)
        with | _ sum end.
        match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x63))
        with | _ product end.
        leibniz &sum, &product in |- *.
        quod idem est.
      }
      simpl unsigned_value, append_bit in |- *.
      ipso
        (symm
          (Bit.conversion.binary.appending.propagation _ _ _ _ &b
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x0
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x1
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x2
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x3
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x4
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x5
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x6
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x7
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x8
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x9
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x10
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x11
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x12
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x13
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x14
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x15
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x16
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x17
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x18
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x19
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x20
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x21
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x22
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x23
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x24
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x25
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x26
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x27
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x28
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x29
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x30
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x31
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x32
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x33
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x34
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x35
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x36
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x37
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x38
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x39
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x40
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x41
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x42
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x43
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x44
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x45
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x46
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x47
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x48
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x49
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x50
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x51
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x52
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x53
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x54
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x55
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x56
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x57
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x58
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x59
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x60
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x61
          (Bit.conversion.binary.appending.propagation _ _ _ _ &x62
          &top))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
    - ipso
        (valuation.boundedness
          (append_bit &b
            (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * unsigned_value
                  (Int64.introduction
                    (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                    (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                    (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                    (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                    (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                    (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                    (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x63)
          (unsigned_value
            (append_bit &b
              (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* valuation.reduction *)
Theorem reduction
  : forall (n : BinWithZero) .
      unsigned_value (from_bin_with_zero n) = (n %. modulus)%bin_with_zero.
Proof.
  intros n.
  match &n with | Zero | Positive p end.
  - simpl from_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second in |- *.
    simpl in |- *.
    quod idem est.
  - simpl from_bin_with_zero in |- *.
    match p with | One | b0 (p' by IH) | b1 (p' by IH) end per BinBase.induction.
    + simpl BinWithZero.modulo, BinWithZero.div in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_bin_base (BinBase.b0 &p') = append_bit 0 (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (valuation.appending 0 (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero 0) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero 0) modulus)
        in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_bin_base (BinBase.b1 &p') = append_bit 1 (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (valuation.appending 1 (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero 1) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero 1) modulus)
        in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
Qed.

Module reduction. (* valuation.reduction *)

(* valuation.reduction.additivity *)
Theorem additivity
  : forall (m : BinWithZero) (n : BinWithZero) .
      from_bin_with_zero (m + n)%bin_with_zero = from_bin_with_zero m + from_bin_with_zero n.
Proof.
  intros m n.
  lemma facto
    : unsigned_value (from_bin_with_zero (&m + &n)%bin_with_zero)
      = unsigned_value (from_bin_with_zero &m + from_bin_with_zero &n).
  {
    leibniz
      (valuation.reduction (&m + &n)%bin_with_zero),
      (valuation.addition (from_bin_with_zero &m) (from_bin_with_zero &n)),
      (valuation.reduction &m),
      (valuation.reduction &n),
      (BinWithZero.modulo.sum.left.absorption
        &m (&n %. modulus)%bin_with_zero modulus),
      (BinWithZero.modulo.sum.right.absorption &m &n modulus)
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

End reduction. (* valuation.reduction *)

(* valuation.section *)
Theorem section : forall (x : Int64) . from_bin_with_zero (unsigned_value x) = x.
Proof.
  intros x.
  lemma facto
    : unsigned_value (from_bin_with_zero (unsigned_value &x)) = unsigned_value &x.
  {
    leibniz
      (valuation.reduction (unsigned_value &x)),
      (BinWithZero.modulo.identity
        (unsigned_value &x) modulus (valuation.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

Module left. (* valuation.left *)

(* valuation.left.doubling *)
Lemma doubling
  : forall (x : Int64) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
    match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
    match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
    match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
    match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
    match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
    match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
    match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
    match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  }
  match (BinWithZero.addition.identity (10 * unsigned_value &x)%bin_with_zero)
  with | _ sum end.
  leibniz &appended, (valuation.appending 0 &x) in |- *.
  simpl Bit.to_bin_with_zero in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

End left. (* valuation.left *)

Module multiplication. (* valuation.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* valuation.multiplication.step *)
Lemma step
  : forall (x : Int64) (p : Int64) (h : BinWithZero) (b : Bit) .
      (unsigned_value p = (unsigned_value x * h) %. modulus)%bin_with_zero ->
      unsigned_value
        (add (shift_left p 1%n0)
          match b with
          | 0%bit => Zero
          | 1%bit => x
          end)
      = ((unsigned_value x * (10 * h + Bit.to_bin_with_zero b))
          %. modulus)%bin_with_zero.
Proof.
  intros x p h b e.
  lemma doubled
    : ((10 * unsigned_value &p) %. modulus
        = (10 * (unsigned_value &x * &h)) %. modulus)%bin_with_zero.
  {
    leibniz
      &e,
      (BinWithZero.modulo.product.right.absorption
        10%bin_with_zero (unsigned_value &x * &h)%bin_with_zero modulus)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (unsigned_value &x * (10 * &h) = 10 * (unsigned_value &x * &h))%bin_with_zero.
  {
    leibniz
      <- (BinWithZero.multiplication.associativity (unsigned_value &x) 10%bin_with_zero &h),
      (BinWithZero.multiplication.commutativity (unsigned_value &x) 10%bin_with_zero),
      (BinWithZero.multiplication.associativity 10%bin_with_zero (unsigned_value &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) Zero)
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero 0))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (10 * unsigned_value &p)%bin_with_zero)
      with | _ right end.
      match (BinWithZero.addition.identity (10 * &h)%bin_with_zero) with | _ right' end.
      leibniz
        (valuation.addition (shift_left &p 1%n0) Zero),
        (valuation.left.doubling &p),
        valuation.zero,
        (BinWithZero.modulo.sum.left.absorption
          (10 * unsigned_value &p)%bin_with_zero 0%bin_with_zero modulus),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) &x)
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero 1))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.multiplication.identity (unsigned_value &x)) with | _ right end.
      match (BinWithZero.multiplication.distributivity.over.addition
              (unsigned_value &x) (10 * &h)%bin_with_zero 1%bin_with_zero)
      with | spread _ end.
      leibniz
        (valuation.addition (shift_left &p 1%n0) &x),
        (valuation.left.doubling &p),
        &doubled,
        (BinWithZero.modulo.sum.left.absorption
          (10 * (unsigned_value &x * &h))%bin_with_zero (unsigned_value &x)
          modulus)
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &spread, &right, &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* valuation.multiplication *)

(* valuation.multiplication *)
Theorem multiplication
  : forall (x : Int64) (y : Int64) .
      (unsigned_value (x * y)%int64
        = (unsigned_value x * unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma base
    : (unsigned_value Zero
        = (unsigned_value &x * 0) %. modulus)%bin_with_zero.
  {
    match (BinWithZero.multiplication.annihilation (unsigned_value &x)) with | _ right end.
    leibniz &right, valuation.zero in |- *.
    simpl BinWithZero.modulo, BinWithZero.div, Product.second in |- *.
    quod idem est.
  }
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _
    (valuation.multiplication.step _ _ _ _ &base
    )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

Module sign. (* valuation.sign *)

(* valuation.sign.clear *)
Theorem clear
  : forall (x : Int64) .
      sign_bit x = 0%bit
      -> (unsigned_value x
          < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (Bit.to_bin_with_zero 0 < 1)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists BinBase.One.
    simpl in |- *.
    quod idem est.
  }
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    (Bit.conversion.binary.boundedness.propagation _ _ _
    &base
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* valuation.sign.set *)
Theorem set
  : forall (x : Int64) .
      sign_bit x = 1%bit
      -> (1000000000000000000000000000000000000000000000000000000000000000
          <= unsigned_value x)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl sign_bit in &e.
  simpl unsigned_value in |- *.
  leibniz &e in |- *.
  lemma base : (1 <= Bit.to_bin_with_zero 1)%bin_with_zero.
  {
    simpl BinWithZero.LessOrEqual, Bit.to_bin_with_zero in |- *.
    ipso (disjoin (Identity.reflexivity 1%bin_with_zero), _).
  }
  ipso
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    (Bit.conversion.binary.boundedness.lower.propagation _ _ _
    &base
    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

End sign. (* valuation.sign *)

End valuation. (* valuation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Int64) (y : Int64) (z : Int64) . (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma facto : unsigned_value ((&x + &y) + &z) = unsigned_value (&x + (&y + &z)).
  {
    leibniz
      (valuation.addition (&x + &y) &z),
      (valuation.addition &x &y),
      (BinWithZero.modulo.sum.left.absorption
        (unsigned_value &x + unsigned_value &y)%bin_with_zero (unsigned_value &z)
        modulus),
      (valuation.addition &x (&y + &z)),
      (valuation.addition &y &z),
      (BinWithZero.modulo.sum.right.absorption
        (unsigned_value &x) (unsigned_value &y + unsigned_value &z)%bin_with_zero
        modulus),
      (BinWithZero.addition.associativity
        (unsigned_value &x) (unsigned_value &y) (unsigned_value &z))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (x : Int64) (y : Int64) . x + y = y + x.
Proof.
  intros x y.
  lemma facto : unsigned_value (&x + &y) = unsigned_value (&y + &x).
  {
    leibniz
      (valuation.addition &x &y),
      (valuation.addition &y &x),
      (BinWithZero.addition.commutativity (unsigned_value &x) (unsigned_value &y))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

(* addition.identity *)
Theorem identity : forall (x : Int64) . (Zero + x = x) /\ (x + Zero = x).
Proof.
  intros x.
  lemma left : Zero + &x = &x.
  {
    lemma facto : unsigned_value (Zero + &x) = unsigned_value &x.
    {
      match (BinWithZero.addition.identity (unsigned_value &x)) with | left _ end.
      leibniz
        (valuation.addition Zero &x),
        valuation.zero,
        &left,
        (BinWithZero.modulo.identity
          (unsigned_value &x) modulus (valuation.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (valuation.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (addition.commutativity &x Zero) in |- *.
    ipso &left.
Qed.

(* addition.inverse *)
Theorem inverse : forall (x : Int64) . (- x + x = Zero) /\ (x + - x = Zero).
Proof.
  intros x.
  lemma left : - &x + &x = Zero.
  {
    lemma facto : unsigned_value (- &x + &x) = unsigned_value Zero.
    {
      leibniz
        (valuation.addition (- &x) &x),
        (valuation.negation &x),
        valuation.zero
        in |- *.
      quod idem est.
    }
    ipso (valuation.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (addition.commutativity &x (- &x)) in |- *.
    ipso &left.
Qed.

End addition. (* addition *)

Module multiplication. (* multiplication *)

(* multiplication.associativity *)
Theorem associativity
  : forall (x : Int64) (y : Int64) (z : Int64) . (x * y) * z = x * (y * z).
Proof.
  intros x y z.
  lemma facto : unsigned_value ((&x * &y) * &z) = unsigned_value (&x * (&y * &z)).
  {
    leibniz
      (valuation.multiplication (&x * &y) &z),
      (valuation.multiplication &x &y),
      (BinWithZero.modulo.product.left.absorption
        (unsigned_value &x * unsigned_value &y)%bin_with_zero (unsigned_value &z)
        modulus),
      (valuation.multiplication &x (&y * &z)),
      (valuation.multiplication &y &z),
      (BinWithZero.modulo.product.right.absorption
        (unsigned_value &x) (unsigned_value &y * unsigned_value &z)%bin_with_zero
        modulus),
      (BinWithZero.multiplication.associativity
        (unsigned_value &x) (unsigned_value &y) (unsigned_value &z))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

(* multiplication.commutativity *)
Theorem commutativity : forall (x : Int64) (y : Int64) . x * y = y * x.
Proof.
  intros x y.
  lemma facto : unsigned_value (&x * &y) = unsigned_value (&y * &x).
  {
    leibniz
      (valuation.multiplication &x &y),
      (valuation.multiplication &y &x),
      (BinWithZero.multiplication.commutativity (unsigned_value &x) (unsigned_value &y))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

(* multiplication.identity *)
Theorem identity : forall (x : Int64) . (One * x = x) /\ (x * One = x).
Proof.
  intros x.
  lemma left : One * &x = &x.
  {
    lemma facto : unsigned_value (One * &x) = unsigned_value &x.
    {
      match (BinWithZero.multiplication.identity (unsigned_value &x)) with | left _ end.
      leibniz
        (valuation.multiplication One &x),
        valuation.one,
        &left,
        (BinWithZero.modulo.identity
          (unsigned_value &x) modulus (valuation.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (valuation.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (multiplication.commutativity &x One) in |- *.
    ipso &left.
Qed.

Module left. (* multiplication.left *)

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) (z : Int64) . x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  lemma facto : unsigned_value (&x * (&y + &z)) = unsigned_value ((&x * &y) + (&x * &z)).
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            (unsigned_value &x) (unsigned_value &y) (unsigned_value &z))
    with | spread _ end.
    leibniz
      (valuation.multiplication &x (&y + &z)),
      (valuation.addition &y &z),
      (BinWithZero.modulo.product.right.absorption
        (unsigned_value &x) (unsigned_value &y + unsigned_value &z)%bin_with_zero
        modulus),
      &spread,
      (valuation.addition (&x * &y) (&x * &z)),
      (valuation.multiplication &x &y),
      (valuation.multiplication &x &z),
      (BinWithZero.modulo.sum.left.absorption
        (unsigned_value &x * unsigned_value &y)%bin_with_zero
        ((unsigned_value &x * unsigned_value &z) %. modulus)%bin_with_zero
        modulus),
      (BinWithZero.modulo.sum.right.absorption
        (unsigned_value &x * unsigned_value &y)%bin_with_zero
        (unsigned_value &x * unsigned_value &z)%bin_with_zero modulus)
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) (z : Int64) . (y + z) * x = (y * x) + (z * x).
Proof.
  intros x y z.
  leibniz
    (multiplication.commutativity (&y + &z) &x),
    (multiplication.commutativity &y &x),
    (multiplication.commutativity &z &x)
    in |- *.
  ipso (multiplication.left.distributivity.over.addition &x &y &z).
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) (z : Int64) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (multiplication.left.distributivity.over.addition  &x &y &z).
  - ipso (multiplication.right.distributivity.over.addition &x &y &z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module conversion. (* conversion *)

(* The bit pattern of [a - b] is that of [a] less that of [b]. *)
(* conversion.difference *)
Lemma difference
  : forall (a : BinWithZero) (b : BinWithZero) .
      from_bin (Bin.bin_with_zero_difference a b)
      = from_bin_with_zero a + - from_bin_with_zero b.
Proof.
  intros a b.
  let proof e := congru from_bin_with_zero, (Bin.difference.specification &a &b).
  leibniz
    (valuation.reduction.additivity (Bin.ramp (Bin.bin_with_zero_difference &a &b)) &b),
    (valuation.reduction.additivity
      (Bin.ramp (Bin.negate (Bin.bin_with_zero_difference &a &b))) &a)
    in &e.
  simpl from_bin in |- *.
  let p := from_bin_with_zero (Bin.ramp (Bin.bin_with_zero_difference &a &b)) in &e |- *.
  let q :=
    from_bin_with_zero (Bin.ramp (Bin.negate (Bin.bin_with_zero_difference &a &b)))
    in &e |- *.
  lemma rewritten : &p = (&q + from_bin_with_zero &a) + - from_bin_with_zero &b.
  {
    match (addition.inverse (from_bin_with_zero &b)) with | _ cancel end.
    match (addition.identity &p) with | _ unit end.
    leibniz
      <- &e,
      (addition.associativity &p (from_bin_with_zero &b) (- from_bin_with_zero &b)),
      &cancel,
      &unit
      in |- *.
    quod idem est.
  }
  match (addition.inverse &q) with | _ cancel end.
  match (addition.identity (- from_bin_with_zero &b)) with | _ unit end.
  leibniz
    &rewritten,
    (addition.commutativity &q (from_bin_with_zero &a)),
    (addition.associativity (from_bin_with_zero &a) &q (- from_bin_with_zero &b)),
    (addition.commutativity &q (- from_bin_with_zero &b)),
    (addition.associativity (from_bin_with_zero &a) (- from_bin_with_zero &b + &q) (- &q)),
    (addition.associativity (- from_bin_with_zero &b) &q (- &q)),
    &cancel,
    &unit
    in |- *.
  quod idem est.
Qed.

(* conversion.section *)
Theorem section : forall (x : Int64) . from_bin (to_bin x) = x.
Proof.
  intros x.
  lemma vanishing
    : from_bin_with_zero (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero = Zero.
  {
    lemma facto
      : unsigned_value
          (from_bin_with_zero (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero)
        = unsigned_value Zero.
    {
      leibniz
        (valuation.reduction (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero),
        valuation.zero
        in |- *.
      match (sign_bit &x) with | Zero | One end.
      - simpl Bit.to_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second
          in |- *.
        simpl in |- *.
        quod idem est.
      - simpl Bit.to_bin_with_zero, BinWithZero.modulo, BinWithZero.div, Product.second
          in |- *.
        simpl in |- *.
        quod idem est.
    }
    ipso (valuation.injectivity &facto).
  }
  lemma unsigned : - Zero = Zero.
  {
    match (addition.inverse Zero) with | _ right end.
    match (addition.identity (- Zero)) with | left _ end.
    ipso (trans (symm &left), &right).
  }
  match (addition.identity &x) with | _ right end.
  simpl to_bin in |- *.
  leibniz
    (conversion.difference
      (unsigned_value &x) (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero),
    (valuation.section &x),
    &vanishing,
    &unsigned,
    &right
    in |- *.
  quod idem est.
Qed.

(* conversion.injectivity *)
Theorem injectivity : forall {x : Int64} {y : Int64} . to_bin x = to_bin y -> x = y.
Proof.
  intros x y e.
  leibniz <- (conversion.section &x), <- (conversion.section &y), &e in |- *.
  quod idem est.
Qed.

(* Without an overflow, the sign bits of [x] and [y] sum to the carry out of
 * [x + y] and its sign bit.
 *)
(* conversion.sign *)
Lemma sign
  : forall (x : Int64) (y : Int64) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_bin_with_zero (sign_bit x) + Bit.to_bin_with_zero (sign_bit y)
        = Bit.to_bin_with_zero (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_bin_with_zero (sign_bit (x + y)%int64))%bin_with_zero.
Proof.
  intros x y o.
  match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
  match &xb7 with | introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
  match &xb6 with | introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
  match &xb5 with | introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
  match &xb4 with | introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
  match &xb3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
  match &xb2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb7 yb6 yb5 yb4 yb3 yb2 yb1 yb0 end.
  match &yb7 with | introduction y63 y62 y61 y60 y59 y58 y57 y56 end.
  match &yb6 with | introduction y55 y54 y53 y52 y51 y50 y49 y48 end.
  match &yb5 with | introduction y47 y46 y45 y44 y43 y42 y41 y40 end.
  match &yb4 with | introduction y39 y38 y37 y36 y35 y34 y33 y32 end.
  match &yb3 with | introduction y31 y30 y29 y28 y27 y26 y25 y24 end.
  match &yb2 with | introduction y23 y22 y21 y20 y19 y18 y17 y16 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x63 &y63 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int64) (y : Int64) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_bin (x + y) = (x + y)%b.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int64)%bin_with_zero
    := valuation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int64
        + (modulus * Bit.to_bin_with_zero (sign_bit &x)
          + modulus * Bit.to_bin_with_zero (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int64))%bin_with_zero.
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (sign_bit &x)) (Bit.to_bin_with_zero (sign_bit &y)))
    with | signs _ end.
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_bin_with_zero (sign_bit (&x + &y)%int64)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (BinWithZero.addition.associativity
        (unsigned_value (&x + &y)%int64)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)%bin_with_zero
        (modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int64))%bin_with_zero),
      (BinWithZero.addition.commutativity
        (unsigned_value (&x + &y)%int64)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)%bin_with_zero),
      &a
      in |- *.
    quod idem est.
  }
  simpl to_bin in |- *.
  leibniz
    (Bin.difference.additivity
      (unsigned_value &x) (modulus * Bit.to_bin_with_zero (sign_bit &x))%bin_with_zero
      (unsigned_value &y) (modulus * Bit.to_bin_with_zero (sign_bit &y))%bin_with_zero)
    in |- *.
  ipso (Bin.difference.invariance &balance).
Qed.

Module right. (* conversion.right *)

(* A shift to the right by one place halves the value, rounding down: the
 * lowest bit is what it drops, and the sign bit copied in keeps the sign.
 *)
(* conversion.right.halving *)
Theorem halving
  : forall (x63 : Bit) (x62 : Bit) (x61 : Bit) (x60 : Bit)
      (x59 : Bit) (x58 : Bit) (x57 : Bit) (x56 : Bit)
      (x55 : Bit) (x54 : Bit) (x53 : Bit) (x52 : Bit)
      (x51 : Bit) (x50 : Bit) (x49 : Bit) (x48 : Bit)
      (x47 : Bit) (x46 : Bit) (x45 : Bit) (x44 : Bit)
      (x43 : Bit) (x42 : Bit) (x41 : Bit) (x40 : Bit)
      (x39 : Bit) (x38 : Bit) (x37 : Bit) (x36 : Bit)
      (x35 : Bit) (x34 : Bit) (x33 : Bit) (x32 : Bit)
      (x31 : Bit) (x30 : Bit) (x29 : Bit) (x28 : Bit)
      (x27 : Bit) (x26 : Bit) (x25 : Bit) (x24 : Bit)
      (x23 : Bit) (x22 : Bit) (x21 : Bit) (x20 : Bit)
      (x19 : Bit) (x18 : Bit) (x17 : Bit) (x16 : Bit)
      (x15 : Bit) (x14 : Bit) (x13 : Bit) (x12 : Bit)
      (x11 : Bit) (x10 : Bit) (x9 : Bit) (x8 : Bit)
      (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_bin (Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
                (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
                (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
                (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
                (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
                (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
                (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
                (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right
            (Int64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
              (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
              (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
              (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
              (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
              (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
              (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
              (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_bin_with_zero x0)%b.
Proof.
  intros x63 x62 x61 x60 x59 x58 x57 x56 x55 x54 x53 x52 x51 x50 x49 x48 x47 x46 x45 x44 x43 x42 x41
    x40 x39 x38 x37 x36 x35 x34 x33 x32 x31 x30 x29 x28 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x17
    x16 x15 x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
          (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
          (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
          (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
          (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
        (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
        (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
        (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
        (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
        (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
        (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
        (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_bin_with_zero &x0
        = Bit.to_bin_with_zero &x63 * modulus
          + unsigned_value
              (Int64.introduction
                (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                  (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                  (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                  (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                  (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%bin_with_zero.
  {
    lemma top
      : (Bit.to_bin_with_zero &x63 = Bit.to_bin_with_zero &x63 * 1 + 0)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x63 * 1)%bin_with_zero)
      with | _ sum end.
      match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x63))
      with | _ product end.
      leibniz &sum, &product in |- *.
      quod idem est.
    }
    simpl unsigned_value in |- *.
    ipso
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x0
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x1
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x2
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x3
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x4
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x5
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x6
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x7
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x8
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x9
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x10
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x11
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x12
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x13
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x14
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x15
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x16
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x17
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x18
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x19
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x20
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x21
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x22
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x23
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x24
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x25
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x26
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x27
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x28
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x29
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x30
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x31
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x32
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x33
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x34
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x35
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x36
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x37
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x38
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x39
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x40
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x41
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x42
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x43
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x44
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x45
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x46
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x47
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x48
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x49
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x50
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x51
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x52
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x53
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x54
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x55
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x56
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x57
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x58
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x59
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x60
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x61
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x62
      (Bit.conversion.binary.appending.propagation _ _ _ _ &x63
      &top)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
  }
  lemma twice : forall (z : Bin) . (10 * z = z + z)%b.
  {
    intros z.
    lemma ten : (10 = 1 + 1)%b.
    {
      simpl Bin.add in |- *.
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (Bin.multiplication.distributivity.over.addition &z 1%b 1%b) with | _ spread end.
    match (Bin.multiplication.identity &z) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma doubled
    : forall (n : BinWithZero) . (n + n = 10 * n)%bin_with_zero.
  {
    intros n.
    lemma ten : (10 = 1 + 1)%bin_with_zero.
    {
      simpl in |- *.
      simpl BinBase.add in |- *.
      simpl in |- *.
      quod idem est.
    }
    match (BinWithZero.multiplication.distributivity.over.addition &n 1%bin_with_zero
            1%bin_with_zero)
    with | _ spread end.
    match (BinWithZero.multiplication.identity &n) with | unit _ end.
    leibniz &ten, &spread, &unit in |- *.
    quod idem est.
  }
  lemma embedding
    : forall (n : BinWithZero) .
        Bin.from_bin_with_zero n = Bin.bin_with_zero_difference n 0%bin_with_zero.
  {
    intros n.
    match &n with | Zero | Positive p end; simpl in |- *; quod idem est.
  }
  lemma balance
    : (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
          (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
          (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
          (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
          (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
          (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
          (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_bin_with_zero &x63 + modulus * Bit.to_bin_with_zero &x63 + 0)
        = (unsigned_value
            (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
              (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
              (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
              (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
              (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
              (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
              (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
              (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_bin_with_zero &x0)
          + modulus * Bit.to_bin_with_zero &x63)%bin_with_zero.
  {
    match (BinWithZero.addition.identity
            (modulus * Bit.to_bin_with_zero &x63
              + modulus * Bit.to_bin_with_zero &x63)%bin_with_zero)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
            (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
            (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
            (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
            (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (BinWithZero.multiplication.commutativity
        (Bit.to_bin_with_zero &x63) modulus),
      (BinWithZero.addition.commutativity
        (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
            (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
            (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
            (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
            (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (BinWithZero.addition.associativity
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
            (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
            (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
            (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
            (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
            (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
            (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero
        (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_bin, sign_bit in |- *.
  leibniz
    (&twice
      (Bin.bin_with_zero_difference
        (unsigned_value
          (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
            (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
            (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
            (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
            (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
            (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
            (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero)),
    (Bin.difference.additivity
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x63)%bin_with_zero),
    (&embedding (Bit.to_bin_with_zero &x0)),
    (Bin.difference.additivity
      (unsigned_value
        (Int64.introduction (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
          (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
          (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
          (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
          (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
          (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
          (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int64.introduction
              (Byte.introduction &x63 &x63 &x62 &x61 &x60 &x59 &x58 &x57)
                (Byte.introduction &x56 &x55 &x54 &x53 &x52 &x51 &x50 &x49)
                (Byte.introduction &x48 &x47 &x46 &x45 &x44 &x43 &x42 &x41)
                (Byte.introduction &x40 &x39 &x38 &x37 &x36 &x35 &x34 &x33)
                (Byte.introduction &x32 &x31 &x30 &x29 &x28 &x27 &x26 &x25)
                (Byte.introduction &x24 &x23 &x22 &x21 &x20 &x19 &x18 &x17)
                (Byte.introduction &x16 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%bin_with_zero
      (modulus * Bit.to_bin_with_zero &x63
        + modulus * Bit.to_bin_with_zero &x63)%bin_with_zero
      (Bit.to_bin_with_zero &x0) 0%bin_with_zero)
    in |- *.
  ipso (Bin.difference.invariance &balance).
Qed.

End right. (* conversion.right *)

Module bin. (* conversion.bin *)

(* conversion.bin.nonnegative *)
Lemma nonnegative
  : forall (n : BinWithZero) . from_bin (Bin.from_bin_with_zero n) = from_bin_with_zero n.
Proof.
  intros n.
  lemma nothing : - from_bin_with_zero BinWithZero.Zero = Zero.
  {
    simpl from_bin_with_zero in |- *.
    match (addition.inverse Zero) with | _ right end.
    match (addition.identity (- Zero)) with | left _ end.
    ipso (trans (symm &left), &right).
  }
  match &n with | Zero | Positive p end.
  - simpl Bin.from_bin_with_zero, from_bin in |- *.
    simpl Bin.ramp, Bin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_bin_with_zero BinWithZero.Zero)) with | _ right end.
    ipso &right.
  - simpl Bin.from_bin_with_zero, from_bin in |- *.
    simpl Bin.ramp, Bin.negate in |- *.
    leibniz &nothing in |- *.
    match (addition.identity (from_bin_with_zero (BinWithZero.Positive &p))) with
    | _ right end.
    ipso &right.
Qed.

(* conversion.bin.negative *)
Lemma negative : forall (p : BinBase) . from_bin (Bin.Negative p) = - from_bin_base p.
Proof.
  intros p.
  simpl from_bin in |- *.
  simpl Bin.ramp, Bin.negate in |- *.
  lemma nothing : from_bin_with_zero BinWithZero.Zero = Zero.
  {
    simpl from_bin_with_zero in |- *.
    quod idem est.
  }
  lemma unfolded : from_bin_with_zero (BinWithZero.Positive &p) = from_bin_base &p.
  {
    simpl from_bin_with_zero in |- *.
    quod idem est.
  }
  leibniz &nothing, &unfolded in |- *.
  match (addition.identity (- from_bin_base &p)) with | left _ end.
  ipso &left.
Qed.

End bin. (* conversion.bin *)

Module boundedness. (* conversion.boundedness *)

(* conversion.boundedness.positive *)
Theorem positive
  : forall (x : Int64) (p : BinBase) .
      to_bin x = Bin.Positive p
      -> (p < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
Proof.
  intros x p e.
  simpl to_bin in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_bin_with_zero 0 = 0)%bin_with_zero.
    {
      simpl modulus, Bit.to_bin_with_zero in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    let proof small := valuation.sign.clear &x &s.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
    + simpl Bin.bin_with_zero_difference in &e.
      let proof g := congru Bin.ramp, &e.
      simpl Bin.ramp in &g.
      leibniz &g in &small.
      ipso &small.
  - lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof sp := Bin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl Bin.ramp, Bin.negate in &sp.
    match (BinWithZero.addition.identity (unsigned_value &x)) with | left _ end.
    leibniz &left in &sp.
    let proof bound := valuation.boundedness &x.
    leibniz <- &sp in &bound.
    ex
      (BinWithZero.order.strict.irreflexivity _
        (BinWithZero.order.mixed.transitivity
          (BinWithZero.addition.right.order.extensivity p modulus) &bound))
      quodlibet.
Qed.

(* conversion.boundedness.negative *)
Theorem negative
  : forall (x : Int64) (p : BinBase) .
      to_bin x = Bin.Negative p
      -> (p <= 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
Proof.
  intros x p e.
  simpl to_bin in &e.
  match (sign_bit &x) with | Zero | One end |- s.
  - lemma scaled : (modulus * Bit.to_bin_with_zero 0 = 0)%bin_with_zero.
    {
      simpl modulus, Bit.to_bin_with_zero in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &scaled in &e.
    match (unsigned_value &x) with | Zero | Positive q end |- f.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
    + simpl Bin.bin_with_zero_difference in &e.
      ex &e quodlibet.
  - lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
    {
      simpl modulus in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &whole in &e.
    let proof big := valuation.sign.set &x &s.
    let proof sp := Bin.difference.specification (unsigned_value &x) modulus.
    leibniz &e in &sp.
    simpl Bin.ramp, Bin.negate in &sp.
    match (BinWithZero.addition.identity modulus) with | left _ end.
    leibniz &left in &sp.
    match
      (Comparable.order.strict.trichotomy
        (BinWithZero.Positive p)
        1000000000000000000000000000000000000000000000000000000000000000%bin_with_zero)
    with
    | below | rest end.
    + simpl BinWithZero.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl BinWithZero.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double
          : (1000000000000000000000000000000000000000000000000000000000000000
              + 1000000000000000000000000000000000000000000000000000000000000000
              = modulus)%bin_with_zero.
        {
          simpl modulus, BinWithZero.add in |- *.
          simpl BinBase.add in |- *.
          simpl in |- *.
          quod idem est.
        }
        let proof total := BinWithZero.addition.order.strict.monotonicity _ _ _ _ &big &above.
        leibniz
          &double,
          (BinWithZero.addition.commutativity (unsigned_value &x) p),
          <- &sp
          in &total.
        ex (BinWithZero.order.strict.irreflexivity _ &total) quodlibet.
Qed.

End boundedness. (* conversion.boundedness *)

Module retraction. (* conversion.retraction *)

(* conversion.retraction.nonnegative *)
Theorem nonnegative
  : forall (n : BinWithZero) .
      (n < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero
      -> to_bin (from_bin (Bin.from_bin_with_zero n)) = Bin.from_bin_with_zero n.
Proof.
  intros n h.
  lemma half
    : (1000000000000000000000000000000000000000000000000000000000000000
        < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 1000000000000000000000000000000000000000000000000000000000000000%bin_base.
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma value : unsigned_value (from_bin_with_zero &n) = &n.
  {
    leibniz
      (valuation.reduction &n),
      (BinWithZero.modulo.identity &n modulus (BinWithZero.order.strict.transitivity &h &half))
      in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_bin_with_zero &n) = 0%bit.
  {
    match (sign_bit (from_bin_with_zero &n)) with | Zero | One end |- s.
    - quod idem est.
    - let proof big := valuation.sign.set _ &s.
      leibniz &value in &big.
      ex
        (BinWithZero.order.strict.irreflexivity _
          (BinWithZero.order.mixed.transitivity &big &h))
        quodlibet.
  }
  leibniz (conversion.bin.nonnegative &n) in |- *.
  simpl to_bin in |- *.
  leibniz &value, &sign in |- *.
  match &n with | Zero | Positive p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

(* conversion.retraction.negative *)
Theorem negative
  : forall (p : BinBase) .
      (p <= 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero
      -> to_bin (from_bin (Bin.Negative p)) = Bin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.bin.negative &p) in |- *.
  lemma half
    : (1000000000000000000000000000000000000000000000000000000000000000
        < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 1000000000000000000000000000000000000000000000000000000000000000%bin_base.
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma below : (p < modulus)%bin_with_zero.
  {
    match &h with | same | smaller end.
    - leibniz &same in |- *.
      ipso &half.
    - ipso (BinWithZero.order.strict.transitivity &smaller &half).
  }
  let proof pbelow := &below.
  match &below with | k ek end.
  lemma kbelow : (k < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists &p.
    leibniz (BinWithZero.addition.commutativity k p) in |- *.
    ipso &ek.
  }
  lemma valuek : unsigned_value (from_bin_base &k) = k.
  {
    lemma through : from_bin_base &k = from_bin_with_zero k.
    {
      simpl from_bin_with_zero in |- *.
      quod idem est.
    }
    leibniz
      &through, (valuation.reduction k), (BinWithZero.modulo.identity k modulus &kbelow)
      in |- *.
    quod idem est.
  }
  lemma valuep : unsigned_value (from_bin_base &p) = p.
  {
    lemma through : from_bin_base &p = from_bin_with_zero p.
    {
      simpl from_bin_with_zero in |- *.
      quod idem est.
    }
    leibniz
      &through, (valuation.reduction p), (BinWithZero.modulo.identity p modulus &pbelow)
      in |- *.
    quod idem est.
  }
  lemma sum : from_bin_base &k + from_bin_base &p = Zero.
  {
    lemma facto : unsigned_value (from_bin_base &k + from_bin_base &p) = unsigned_value Zero.
    {
      leibniz
        (valuation.addition (from_bin_base &k) (from_bin_base &p)),
        &valuek, &valuep, valuation.zero,
        (BinWithZero.addition.commutativity k p),
        &ek
        in |- *.
      simpl modulus in |- *.
      simpl BinWithZero.modulo, BinWithZero.div in |- *.
      simpl in |- *.
      quod idem est.
    }
    ipso (valuation.injectivity &facto).
  }
  lemma complement : - from_bin_base &p = from_bin_base &k.
  {
    match (addition.identity (- from_bin_base &p)) with | left _ end.
    match (addition.inverse (from_bin_base &p)) with | _ right end.
    match (addition.identity (from_bin_base &k)) with | _ right' end.
    leibniz
      <- &left,
      <- &sum,
      (addition.associativity (from_bin_base &k) (from_bin_base &p) (- from_bin_base &p)),
      &right,
      &right'
      in |- *.
    quod idem est.
  }
  leibniz &complement in |- *.
  lemma double
    : (1000000000000000000000000000000000000000000000000000000000000000
        + 1000000000000000000000000000000000000000000000000000000000000000
        = modulus)%bin_with_zero.
  {
    simpl modulus, BinWithZero.add in |- *.
    simpl BinBase.add in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma sign : sign_bit (from_bin_base &k) = 1%bit.
  {
    match (sign_bit (from_bin_base &k)) with | Zero | One end |- s.
    - let proof small := valuation.sign.clear _ &s.
      leibniz &valuek in &small.
      let proof total := BinWithZero.addition.order.strict.monotonicity _ _ _ _ &h &small.
      leibniz &ek, &double in &total.
      ex (BinWithZero.order.strict.irreflexivity _ &total) quodlibet.
    - quod idem est.
  }
  lemma whole : (modulus * Bit.to_bin_with_zero 1 = modulus)%bin_with_zero.
  {
    simpl modulus in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma swap : (k + p = 0 + modulus)%bin_with_zero.
  {
    match (BinWithZero.addition.identity modulus) with | left _ end.
    leibniz (BinWithZero.addition.commutativity k p), &ek, &left in |- *.
    quod idem est.
  }
  simpl to_bin in |- *.
  leibniz &valuek, &sign, &whole, (Bin.difference.invariance &swap) in |- *.
  simpl Bin.bin_with_zero_difference in |- *.
  quod idem est.
Qed.

End retraction. (* conversion.retraction *)

Module division. (* conversion.division *)

(* conversion.division.positive *)
Theorem positive
  : forall (x : Int64) (y : Int64) (d : BinBase) .
      to_bin y = Bin.Positive d -> Option.map to_bin (x /. y)%int64 = Some (x /. d)%b.
Proof.
  intros x y d e.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing
      : (0 < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 1000000000000000000000000000000000000000000000000000000000000000%bin_base.
      simpl BinWithZero.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%bin_with_zero &nothing.
    simpl Bin.from_bin_with_zero in &r.
    ipso &r.
  }
  lemma fits : to_bin (from_bin (x /. &d)%b) = (x /. &d)%b.
  {
    match (to_bin &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      match ((p /. &d)%bin_with_zero) with | Zero | Positive q end |- f.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        ipso &origin.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        lemma bounded
          : (q <= 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
        {
          match &r with | same | smaller end.
          - leibniz &same in &b.
            ipso &b.
          - simpl BinWithZero.LessOrEqual in |- *.
            ipso (disjoin _, (BinWithZero.order.mixed.transitivity &b &smaller)).
        }
        ipso (conversion.retraction.negative &q &bounded).
    - simpl Bin.divide in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      ipso
        (conversion.retraction.nonnegative (p /. &d)%bin_with_zero
          (BinWithZero.order.mixed.transitivity &b &r)).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz &fits in |- *.
  quod idem est.
Qed.

(* conversion.division.negative *)
Theorem negative
  : forall (x : Int64) (y : Int64) (d : BinBase) .
      to_bin y = Bin.Negative d
      -> ~ (to_bin x = (-1000000000000000000000000000000000000000000000000000000000000000)%b
            /\ d = BinBase.One)
      -> Option.map to_bin (x /. y)%int64 = Some (Bin.negate (x /. d)%b).
Proof.
  intros x y d e h.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing
      : (0 < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 1000000000000000000000000000000000000000000000000000000000000000%bin_base.
      simpl BinWithZero.add in |- *.
      quod idem est.
    }
    let proof r := conversion.retraction.nonnegative 0%bin_with_zero &nothing.
    simpl Bin.from_bin_with_zero in &r.
    ipso &r.
  }
  lemma fits : to_bin (from_bin (Bin.negate (x /. &d)%b)) = Bin.negate (x /. &d)%b.
  {
    match (to_bin &x) with | Negative p | Zero | Positive p end |- t.
    - let proof r := conversion.boundedness.negative &x &p &t.
      lemma below
        : ((p /. &d)
            < 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
      {
        match &r with | same | smaller end.
        - match &d with | One | b0 d' | b1 d' end.
          + let proof g := congru BinWithZero.to_bin_base, &same.
            simpl BinWithZero.to_bin_base in &g.
            let proof k := Option.some.injectivity &g.
            leibniz &k in &h.
            ex
              (&h
                (conjoin
                  (Identity.reflexivity
                    (-1000000000000000000000000000000000000000000000000000000000000000)%b),
                  (Identity.reflexivity BinBase.One)))
              quodlibet.
          + lemma differ : ~ (BinBase.b0 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (BinWithZero.division.quotient.strict.boundedness &p (BinBase.b0 &d') &differ).
          + lemma differ : ~ (BinBase.b1 &d' = BinBase.One).
            {
              intro k.
              ex &k quodlibet.
            }
            leibniz <- &same in |- *.
            ipso (BinWithZero.division.quotient.strict.boundedness &p (BinBase.b1 &d') &differ).
        - ipso
            (BinWithZero.order.mixed.transitivity
              (BinWithZero.division.quotient.boundedness p &d) &smaller).
      }
      simpl Bin.divide in |- *.
      leibniz (Bin.negation.involution (Bin.from_bin_with_zero (p /. &d)%bin_with_zero)) in |- *.
      ipso (conversion.retraction.nonnegative (p /. &d)%bin_with_zero &below).
    - simpl Bin.divide, Bin.negate in |- *.
      ipso &origin.
    - let proof r := conversion.boundedness.positive &x &p &t.
      let proof b := BinWithZero.division.quotient.boundedness p &d.
      simpl Bin.divide in |- *.
      match ((p /. &d)%bin_with_zero) with | Zero | Positive q end |- f.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        ipso &origin.
      + simpl Bin.from_bin_with_zero, Bin.negate in |- *.
        lemma bounded
          : (q <= 1000000000000000000000000000000000000000000000000000000000000000)%bin_with_zero.
        {
          simpl BinWithZero.LessOrEqual in |- *.
          ipso (disjoin _, (BinWithZero.order.mixed.transitivity &b &r)).
        }
        ipso (conversion.retraction.negative &q &bounded).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz &fits in |- *.
  quod idem est.
Qed.

End division. (* conversion.division *)

Module dword. (* conversion.dword *)

(* conversion.dword.retraction *)
Theorem retraction : forall (w : DWord) . to_dword (DWord.endian w) (from_dword w) = w.
Proof.
  intros w.
  match &w with | introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
  match &e with | Little | Big end;
    simpl from_dword, to_dword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.dword.section *)
Theorem section : forall (e : Endian) (x : Int64) . from_dword (to_dword e x) = x.
Proof.
  intros e x.
  match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &e with | Little | Big end;
    simpl from_dword, to_dword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End dword. (* conversion.dword *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Int64} {y : Int64} {z : Int64} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (Bin.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : Int64) (y : Int64) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  simpl compare, LessThan in |- *.
  let proof s := Bin.comparison.specification (to_bin &x) (to_bin &y).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_bin, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : Int64) (y : Int64) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (Bin.comparison.antisymmetry (to_bin &x) (to_bin &y)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Int64. (* Int64 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Int64], not [Int64.T].
 *)
Abbreviation Int64 := Int64.T.

(* Makes the notations declared in [Module Int64] usable in every file that
 * imports this one, as [(x + y)%int64] or under an opened [jwa_int64_scope].
 *)
Export (notations) Int64.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int64], [(-100)%int64] or [0x7F%int64], and a closed one prints
 * in decimal.
 *)
Number Notation Int64.T Int64.from_numeral Int64.to_numeral
  : jwa_int64_scope.

(* Where an [Int64] is expected, a literal or a notation reads in this scope
 * without its [%int64].
 *)
Bind Scope jwa_int64_scope with Int64.T.

(* An [Int64] stands wherever a [Bin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int64.to_bin : Int64 >-> Bin.
Add Printing Coercion Int64.to_bin.
Coercion Int64.to_integer : Int64 >-> Integer.
Add Printing Coercion Int64.to_integer.

(* Declared inside [Module Int64]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int64.comparable.

Instance Int64_add_monoid
  : Monoid Int64.add Int64.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int64.addition.associativity |}
  ; Monoid.identity := Int64.addition.identity |}.

Instance Int64_mul_monoid
  : Monoid Int64.mul Int64.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int64.multiplication.associativity |}
  ; Monoid.identity := Int64.multiplication.identity |}.

Instance Int64_add_commutative
  : Commutative Int64.add :=
  {| Commutative.commutativity := Int64.addition.commutativity |}.

Instance Int64_mul_commutative
  : Commutative Int64.mul :=
  {| Commutative.commutativity := Int64.multiplication.commutativity |}.

Instance Int64_add_group
  : Group Int64.add Int64.Zero Int64.negate :=
  {| Group.monoid := Int64_add_monoid
  ; Group.inverse := Int64.addition.inverse |}.

Instance Int64_add_abelian_group
  : AbelianGroup Int64.add Int64.Zero Int64.negate :=
  {| AbelianGroup.group := Int64_add_group
  ; AbelianGroup.commutative := Int64_add_commutative |}.

Instance Int64_ring
  : Ring Int64.add Int64.Zero Int64.negate Int64.mul Int64.One :=
  {| Ring.abelian_group := Int64_add_abelian_group
  ; Ring.monoid := Int64_mul_monoid
  ; Ring.distributivity := Int64.multiplication.distributivity.over.addition |}.
