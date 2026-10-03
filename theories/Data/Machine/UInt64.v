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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* An unsigned integer of sixty-four bits: eight [Byte]s read as a number from 0
 * to 18446744073709551615 (2^64 - 1), its arithmetic wrapping modulo
 * 18446744073709551616 (2^64). In this file
 * [10000000000000000000000000000000000000000000000000000000000000000] is 2^64,
 * written in binary digits.
 *)

Module UInt64. (* UInt64 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> T.

Abbreviation UInt64 := T.

(* The number of values, 18446744073709551616 (2^64), the arithmetic wrapping
 * modulo it.
 *)
(* [BinBase] *)
Definition modulus := 10000000000000000000000000000000000000000000000000000000000000000%bin_base.

(* [x] laid out as a [DWord] in the order [e] names. *)
(* [Endian -> UInt64 -> DWord] *)
Definition to_dword := fun (e : Endian) (x : UInt64) .
  match x with
  | UInt64.introduction b7 b6 b5 b4 b3 b2 b1 b0 => DWord.make e b0 b1 b2 b3 b4 b5 b6 b7
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [DWord -> UInt64] *)
Definition from_dword := fun (w : DWord) .
  UInt64.introduction
    (DWord.byte7 w) (DWord.byte6 w) (DWord.byte5 w) (DWord.byte4 w)
    (DWord.byte3 w) (DWord.byte2 w) (DWord.byte1 w) (DWord.byte0 w).

(* The bits read as a number in base two, the most significant first; [10]
 * is two in binary digits.
 *)
(* [UInt64 -> BinWithZero] *)
Definition to_bin_with_zero := fun (x : UInt64) .
  match x with
  | UInt64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
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

(* From here to the end of the module a [UInt64] stands where a [BinWithZero] is
 * expected, read as its value; the conversion is printed.
 *)
Local Coercion to_bin_with_zero : T >-> BinWithZero.
Add Printing Coercion to_bin_with_zero.

(* The value as a [Bin], through [to_bin_with_zero]. *)
(* [UInt64 -> Bin] *)
Definition to_bin := fun (x : UInt64) . Bin.from_bin_with_zero (to_bin_with_zero x).

(* The value in [Nat0], through [to_bin_with_zero]; [Nat0] is unary, so it is
 * for stating and proving, and computing goes through [to_bin_with_zero].
 *)
(* [UInt64 -> Nat0] *)
Definition to_nat0 := fun (x : UInt64) . BinWithZero.to_nat0 (to_bin_with_zero x).

(* [UInt64] *)
Definition Zero := UInt64.introduction Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero
  Byte.Zero Byte.Zero.

(* [UInt64] *)
Definition One :=
  UInt64.introduction
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
(* [UInt64 -> Nat -> UInt64] *)
Fixpoint shift_left_nat (x : UInt64) (k : Nat) : UInt64 :=
  let y :=
    match x with
    | UInt64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        UInt64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
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

(* [UInt64 -> Nat0 -> UInt64] *)
Definition shift_left := fun (x : UInt64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [UInt64 -> Nat -> UInt64] *)
Fixpoint shift_right_nat (x : UInt64) (k : Nat) : UInt64 :=
  let y :=
    match x with
    | UInt64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 _) =>
        UInt64.introduction (Byte.introduction 0 x63 x62 x61 x60 x59 x58 x57)
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

(* [UInt64 -> Nat0 -> UInt64] *)
Definition shift_right := fun (x : UInt64) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> UInt64 -> UInt64] *)
Definition append_bit := fun (b : Bit) (x : UInt64) .
  match x with
  | UInt64.introduction (Byte.introduction _ x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      UInt64.introduction (Byte.introduction x62 x61 x60 x59 x58 x57 x56 x55)
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
(* [Bit -> UInt64 -> UInt64 -> Product Bit UInt64] *)
Definition add_with_carry := fun (carry : Bit) (x : UInt64) (y : UInt64) .
  match x with
  | UInt64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
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
            UInt64.introduction
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

(* [UInt64 -> UInt64 -> UInt64] *)
Definition add := fun (x : UInt64) (y : UInt64) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_uint64_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> UInt64 -> UInt64 -> Product Bit UInt64] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : UInt64) (y : UInt64) .
  match x with
  | UInt64.introduction (Byte.introduction x63 x62 x61 x60 x59 x58 x57 x56)
      (Byte.introduction x55 x54 x53 x52 x51 x50 x49 x48)
      (Byte.introduction x47 x46 x45 x44 x43 x42 x41 x40)
      (Byte.introduction x39 x38 x37 x36 x35 x34 x33 x32)
      (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
      (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
      (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
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
            UInt64.introduction
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

(* [UInt64 -> UInt64 -> UInt64] *)
Definition sub := fun (x : UInt64) (y : UInt64) . (pi_2 (sub_with_borrow 0 x y))%product.

(* The two's complement: [x] taken from [Zero], wrapping. *)
(* [UInt64 -> UInt64] *)
Definition negate := fun (x : UInt64) . sub Zero x.

Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_uint64_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 18446744073709551616.
 *)
(* [UInt64 -> UInt64 -> UInt64] *)
Definition mul := fun (x : UInt64) (y : UInt64) .
  let step := fun (p : UInt64) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | UInt64.introduction (Byte.introduction y63 y62 y61 y60 y59 y58 y57 y56)
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
  : jwa_uint64_scope.

(* [p] modulo 18446744073709551616, its bits appended from the most significant. *)
(* [BinBase -> UInt64] *)
Fixpoint from_bin_base (p : BinBase) : UInt64 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [BinWithZero -> UInt64] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> UInt64] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> UInt64] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [z] modulo 18446744073709551616 (2^64), a negative [z] counted down from
 * 18446744073709551616.
 *)
(* [Bin -> UInt64] *)
Definition from_bin := fun (z : Bin) .
  match z with
  | Bin.Negative p => negate (from_bin_base p)
  | Bin.Zero       => Zero
  | Bin.Positive p => from_bin_base p
  end.

(* The quotient through [BinWithZero], [None] when [y] is zero. It is at most
 * [x], so it always fits.
 *)
(* [UInt64 -> UInt64 -> Option UInt64] *)
Definition divide := fun (x : UInt64) (y : UInt64) .
  match to_bin_with_zero y with
  | BinWithZero.Zero       => None
  | BinWithZero.Positive d => Some (from_bin_with_zero (x /. d)%bin_with_zero)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jwa_uint64_scope.

(* The remainder through [BinWithZero], [None] when [y] is zero. *)
(* [UInt64 -> UInt64 -> Option UInt64] *)
Definition modulo := fun (x : UInt64) (y : UInt64) .
  match to_bin_with_zero y with
  | BinWithZero.Zero       => None
  | BinWithZero.Positive d => Some (from_bin_with_zero (x %. d)%bin_with_zero)
  end.

Notation "x %. y" := (modulo x y) (only parsing)
  : jwa_uint64_scope.

(* [UInt64 -> UInt64 -> Prop] *)
Definition LessThan := fun (x : UInt64) (y : UInt64) .
  (to_bin_with_zero x < to_bin_with_zero y)%bin_with_zero.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_uint64_scope.

(* [UInt64 -> UInt64 -> Prop] *)
Definition LessOrEqual := fun (x : UInt64) (y : UInt64) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_uint64_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_uint64_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_uint64_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_uint64_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_uint64_scope.

(* [UInt64 -> UInt64 -> Comparison] *)
Definition compare := fun (x : UInt64) (y : UInt64) .
  BinWithZero.compare (to_bin_with_zero x) (to_bin_with_zero y).

(* [UInt64 -> UInt64 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [UInt64 -> UInt64 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [UInt64 -> UInt64 -> UInt64] *)
Abbreviation min := (Comparable.min compare).

(* [UInt64 -> UInt64 -> UInt64] *)
Abbreviation max := (Comparable.max compare).

(* A literal of 0 to 18446744073709551615, in decimal or hexadecimal, read in
 * binary; any larger is refused.
 *)
(* [Numeral.Unsigned -> Option UInt64] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  let value :=
    match u with
    | Numeral.Unsigned.Decimal d     => BinWithZero.from_decimal 0%bin_with_zero d
    | Numeral.Unsigned.Hexadecimal h => BinWithZero.from_hexadecimal 0%bin_with_zero h
    end in
  match BinWithZero.compare value modulus with
  | Comparison.Lt => Some (from_bin_with_zero value)
  | Comparison.Eq => None
  | Comparison.Gt => None
  end.

(* [x] as a literal, in decimal. *)
(* [UInt64 -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : UInt64) .
  Numeral.Unsigned.Decimal (BinWithZero.to_decimal (to_bin_with_zero x)).

Local Open Scope jwa_uint64_scope.

Module conversion. (* conversion *)

(* conversion.zero *)
Theorem zero : to_bin_with_zero Zero = 0%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.one *)
Theorem one : to_bin_with_zero One = 1%bin_with_zero.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.boundedness *)
Theorem boundedness : forall (x : UInt64) . (x < modulus)%bin_with_zero.
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
  simpl to_bin_with_zero in |- *.
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

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : UInt64} {y : UInt64} . to_bin_with_zero x = to_bin_with_zero y -> x = y.
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
  simpl to_bin_with_zero in &e.
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
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : UInt64) (y : UInt64) .
      (Bit.to_bin_with_zero carry + x + y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
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
  simpl to_bin_with_zero, add_with_carry in |- *.
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

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : UInt64) (y : UInt64) .
      (x + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = y + Bit.to_bin_with_zero borrow
          + (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
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
  simpl to_bin_with_zero, sub_with_borrow in |- *.
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

(* conversion.addition *)
Theorem addition
  : forall (x : UInt64) (y : UInt64) .
      (to_bin_with_zero (x + y)%uint64 = (x + y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + to_bin_with_zero (&x + &y)%uint64
        = to_bin_with_zero &x + to_bin_with_zero &y
      /\ to_bin_with_zero (&x + &y)%uint64 < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          modulus),
        <- (conversion.carry 0 &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (conversion.boundedness (&x + &y)).
  }
  match (BinWithZero.division.uniqueness
          (to_bin_with_zero &x + to_bin_with_zero &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
          (to_bin_with_zero (&x + &y)%uint64)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : UInt64) (y : UInt64) .
      ((sub x y + y) %. modulus = x)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product * modulus
        + to_bin_with_zero &x
        = to_bin_with_zero (sub &x &y) + to_bin_with_zero &y
      /\ to_bin_with_zero &x < modulus)%bin_with_zero.
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
          (to_bin_with_zero &x)),
        (conversion.borrow 0 &x &y),
        (BinWithZero.addition.commutativity
          (to_bin_with_zero &y) (Bit.to_bin_with_zero 0))
        in |- *.
      simpl in |- *.
      leibniz
        (BinWithZero.addition.commutativity
          (to_bin_with_zero &y)
          (to_bin_with_zero (pi_2 (sub_with_borrow 0 &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (conversion.boundedness &x).
  }
  match (BinWithZero.division.uniqueness
          (to_bin_with_zero (sub &x &y) + to_bin_with_zero &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow 0 &x &y))%product)
          (to_bin_with_zero &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : UInt64) .
      (((- x)%uint64 + x) %. modulus = 0)%bin_with_zero.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (conversion.subtraction Zero &x), conversion.zero in |- *.
  quod idem est.
Qed.

(* The bits of [x] and then [b] read from the most significant: [b] goes in
 * below and the highest bit falls out, one
 * [Bit.conversion.binary.appending.propagation] per place.
 *)
(* conversion.appending *)
Theorem appending
  : forall (b : Bit) (x : UInt64) .
      (to_bin_with_zero (append_bit b x)
        = (10 * x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
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
        + to_bin_with_zero
            (append_bit &b
              (UInt64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * to_bin_with_zero
                (UInt64.introduction
                  (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
                  (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
                  (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
                  (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
                  (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
                  (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
                  (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ to_bin_with_zero
          (append_bit &b
            (UInt64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
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
      simpl to_bin_with_zero, append_bit in |- *.
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
        (conversion.boundedness
          (append_bit &b
            (UInt64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * to_bin_with_zero
                  (UInt64.introduction
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
          (to_bin_with_zero
            (append_bit &b
              (UInt64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
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

(* conversion.reduction *)
Theorem reduction
  : forall (n : BinWithZero) .
      to_bin_with_zero (from_bin_with_zero n) = (n %. modulus)%bin_with_zero.
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
        (conversion.appending 0 (from_bin_base &p')),
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
        (conversion.appending 1 (from_bin_base &p')),
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

(* conversion.section *)
Theorem section : forall (x : UInt64) . from_bin_with_zero (to_bin_with_zero x) = x.
Proof.
  intros x.
  lemma facto
    : to_bin_with_zero (from_bin_with_zero (to_bin_with_zero &x)) = to_bin_with_zero &x.
  {
    leibniz
      (conversion.reduction (to_bin_with_zero &x)),
      (BinWithZero.modulo.identity
        (to_bin_with_zero &x) modulus (conversion.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

Module left. (* conversion.left *)

(* conversion.left.doubling *)
Lemma doubling
  : forall (x : UInt64) .
      (to_bin_with_zero (shift_left x 1%n0) = (10 * x) %. modulus)%bin_with_zero.
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
  match (BinWithZero.addition.identity (10 * to_bin_with_zero &x)%bin_with_zero)
  with | _ sum end.
  leibniz &appended, (conversion.appending 0 &x) in |- *.
  simpl Bit.to_bin_with_zero in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

(* conversion.left.shift *)
Theorem shift
  : forall (x : UInt64) (k : Nat0) .
      (to_bin_with_zero (shift_left x k) = BinWithZero.shift_left x k %. modulus)%bin_with_zero.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_left &x 0%n0 = &x.
    {
      match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
      simpl in |- *.
      quod idem est.
    }
    leibniz &unchanged in |- *.
    simpl BinWithZero.shift_left in |- *.
    leibniz
      (BinWithZero.modulo.identity
        (to_bin_with_zero &x) modulus (conversion.boundedness &x))
      in |- *.
    quod idem est.
  - extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      leibniz
        (conversion.left.doubling &x),
        (BinWithZero.shift.left.doubling (to_bin_with_zero &x))
        in |- *.
      quod idem est.
    + intros x.
      lemma unfolding
        : shift_left &x (Nat0.Positive (Nat.Successor &n'))
          = shift_left (shift_left &x 1%n0) (Nat0.Positive &n').
      {
        match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (&IH (shift_left &x 1%n0)),
        (conversion.left.doubling &x),
        (BinWithZero.shift.left.multiplication
          ((10 * to_bin_with_zero &x) %. modulus)%bin_with_zero
          (Nat0.Positive &n')),
        (BinWithZero.modulo.product.left.absorption
          (10 * to_bin_with_zero &x)%bin_with_zero
          (BinWithZero.shift_left 1%bin_with_zero (Nat0.Positive &n'))
          modulus),
        <- (BinWithZero.shift.left.multiplication
          (10 * to_bin_with_zero &x)%bin_with_zero (Nat0.Positive &n')),
        <- (BinWithZero.shift.left.successor (to_bin_with_zero &x) &n')
        in |- *.
      quod idem est.
Qed.

End left. (* conversion.left *)

Module right. (* conversion.right *)

(* conversion.right.halving *)
Lemma halving
  : forall (x : UInt64) .
      to_bin_with_zero (shift_right x 1%n0) = BinWithZero.halve x.
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
  ipso
    (symm
      (Bit.conversion.binary.halving
        (to_bin_with_zero
          (shift_right
            (UInt64.introduction (Byte.introduction &x63 &x62 &x61 &x60 &x59 &x58 &x57 &x56)
              (Byte.introduction &x55 &x54 &x53 &x52 &x51 &x50 &x49 &x48)
              (Byte.introduction &x47 &x46 &x45 &x44 &x43 &x42 &x41 &x40)
              (Byte.introduction &x39 &x38 &x37 &x36 &x35 &x34 &x33 &x32)
              (Byte.introduction &x31 &x30 &x29 &x28 &x27 &x26 &x25 &x24)
              (Byte.introduction &x23 &x22 &x21 &x20 &x19 &x18 &x17 &x16)
              (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            1%n0))
        &x0)).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : UInt64) (k : Nat0) .
      to_bin_with_zero (shift_right x k) = BinWithZero.shift_right x k.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_right &x 0%n0 = &x.
    {
      match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
      simpl in |- *.
      quod idem est.
    }
    leibniz &unchanged in |- *.
    simpl BinWithZero.shift_right in |- *.
    quod idem est.
  - extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      leibniz (conversion.right.halving &x) in |- *.
      simpl BinWithZero.shift_right in |- *.
      simpl BinWithZero.shift_right_nat in |- *.
      quod idem est.
    + intros x.
      lemma unfolding
        : shift_right &x (Nat0.Positive (Nat.Successor &n'))
          = shift_right (shift_right &x 1%n0) (Nat0.Positive &n').
      {
        match &x with | introduction xb7 xb6 xb5 xb4 xb3 xb2 xb1 xb0 end.
        simpl in |- *.
        quod idem est.
      }
      lemma step
        : BinWithZero.shift_right (to_bin_with_zero &x) (Nat0.Positive (Nat.Successor &n'))
          = BinWithZero.shift_right
              (BinWithZero.halve (to_bin_with_zero &x)) (Nat0.Positive &n').
      {
        ipso (BinWithZero.shift.right.successor (to_bin_with_zero &x) (Nat0.Positive &n')).
      }
      leibniz
        &unfolding,
        (&IH (shift_right &x 1%n0)),
        (conversion.right.halving &x),
        &step
        in |- *.
      quod idem est.
Qed.

End right. (* conversion.right *)

Module multiplication. (* conversion.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* conversion.multiplication.step *)
Lemma step
  : forall (x : UInt64) (p : UInt64) (h : BinWithZero) (b : Bit) .
      (to_bin_with_zero p = (x * h) %. modulus)%bin_with_zero ->
      to_bin_with_zero
        (add (shift_left p 1%n0)
          match b with
          | 0%bit => Zero
          | 1%bit => x
          end)
      = ((x * (10 * h + Bit.to_bin_with_zero b)) %. modulus)%bin_with_zero.
Proof.
  intros x p h b e.
  lemma doubled
    : ((10 * to_bin_with_zero &p) %. modulus
        = (10 * (to_bin_with_zero &x * &h)) %. modulus)%bin_with_zero.
  {
    leibniz
      &e,
      (BinWithZero.modulo.product.right.absorption
        10%bin_with_zero (to_bin_with_zero &x * &h)%bin_with_zero modulus)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (to_bin_with_zero &x * (10 * &h) = 10 * (to_bin_with_zero &x * &h))%bin_with_zero.
  {
    leibniz
      <- (BinWithZero.multiplication.associativity (to_bin_with_zero &x) 10%bin_with_zero &h),
      (BinWithZero.multiplication.commutativity (to_bin_with_zero &x) 10%bin_with_zero),
      (BinWithZero.multiplication.associativity 10%bin_with_zero (to_bin_with_zero &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : to_bin_with_zero (add (shift_left &p 1%n0) Zero)
        = ((to_bin_with_zero &x * (10 * &h + Bit.to_bin_with_zero 0))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (10 * to_bin_with_zero &p)%bin_with_zero)
      with | _ right end.
      match (BinWithZero.addition.identity (10 * &h)%bin_with_zero) with | _ right' end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) Zero),
        (conversion.left.doubling &p),
        conversion.zero,
        (BinWithZero.modulo.sum.left.absorption
          (10 * to_bin_with_zero &p)%bin_with_zero 0%bin_with_zero modulus),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : to_bin_with_zero (add (shift_left &p 1%n0) &x)
        = ((to_bin_with_zero &x * (10 * &h + Bit.to_bin_with_zero 1))
            %. modulus)%bin_with_zero.
    {
      match (BinWithZero.multiplication.identity (to_bin_with_zero &x)) with | _ right end.
      match (BinWithZero.multiplication.distributivity.over.addition
              (to_bin_with_zero &x) (10 * &h)%bin_with_zero 1%bin_with_zero)
      with | spread _ end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) &x),
        (conversion.left.doubling &p),
        &doubled,
        (BinWithZero.modulo.sum.left.absorption
          (10 * (to_bin_with_zero &x * &h))%bin_with_zero (to_bin_with_zero &x)
          modulus)
        in |- *.
      simpl Bit.to_bin_with_zero in |- *.
      leibniz &spread, &right, &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* conversion.multiplication *)

(* conversion.multiplication *)
Theorem multiplication
  : forall (x : UInt64) (y : UInt64) .
      (to_bin_with_zero (x * y)%uint64 = (x * y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma base
    : (to_bin_with_zero Zero
        = (to_bin_with_zero &x * 0) %. modulus)%bin_with_zero.
  {
    match (BinWithZero.multiplication.annihilation (to_bin_with_zero &x)) with | _ right end.
    leibniz &right, conversion.zero in |- *.
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
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _
    (conversion.multiplication.step _ _ _ _ &base
    )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

(* conversion.division *)
Theorem division
  : forall (x : UInt64) (y : UInt64) (d : BinBase) .
      to_bin_with_zero y = BinWithZero.Positive d
      -> Option.map to_bin_with_zero (x /. y)%uint64 = Some (x /. d)%bin_with_zero.
Proof.
  intros x y d e.
  lemma below : ((x /. &d) < modulus)%bin_with_zero.
  {
    match (BinWithZero.division.quotient.boundedness x &d) with | same | smaller end.
    - leibniz &same in |- *.
      ipso (conversion.boundedness &x).
    - ipso (BinWithZero.order.strict.transitivity &smaller (conversion.boundedness &x)).
  }
  simpl divide in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz
    (conversion.reduction (x /. &d)%bin_with_zero),
    (BinWithZero.modulo.identity (x /. &d)%bin_with_zero modulus &below)
    in |- *.
  quod idem est.
Qed.

(* conversion.modulo *)
Theorem modulo
  : forall (x : UInt64) (y : UInt64) (d : BinBase) .
      to_bin_with_zero y = BinWithZero.Positive d
      -> Option.map to_bin_with_zero (x %. y)%uint64 = Some (x %. d)%bin_with_zero.
Proof.
  intros x y d e.
  lemma below : ((x %. &d) < modulus)%bin_with_zero.
  {
    match (BinWithZero.division.specification x &d) with | _ smaller end.
    let proof bound := conversion.boundedness &y.
    leibniz &e in &bound.
    ipso (BinWithZero.order.strict.transitivity &smaller &bound).
  }
  simpl modulo in |- *.
  leibniz &e in |- *.
  simpl Option.map in |- *.
  leibniz
    (conversion.reduction (x %. &d)%bin_with_zero),
    (BinWithZero.modulo.identity (x %. &d)%bin_with_zero modulus &below)
    in |- *.
  quod idem est.
Qed.

Module bin. (* conversion.bin *)

(* conversion.bin.section *)
Theorem section : forall (x : UInt64) . from_bin (to_bin x) = x.
Proof.
  intros x.
  lemma through
    : forall (n : BinWithZero) . from_bin (Bin.from_bin_with_zero n) = from_bin_with_zero n.
  {
    intros n.
    match &n with | Zero | Positive p end.
    - simpl Bin.from_bin_with_zero, from_bin, from_bin_with_zero in |- *.
      quod idem est.
    - simpl Bin.from_bin_with_zero, from_bin, from_bin_with_zero in |- *.
      quod idem est.
  }
  simpl to_bin in |- *.
  leibniz (&through (to_bin_with_zero &x)), (conversion.section &x) in |- *.
  quod idem est.
Qed.

End bin. (* conversion.bin *)

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
Theorem section : forall (e : Endian) (x : UInt64) . from_dword (to_dword e x) = x.
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

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : UInt64) (y : UInt64) (z : UInt64) . (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma facto : to_bin_with_zero ((&x + &y) + &z) = to_bin_with_zero (&x + (&y + &z)).
  {
    leibniz
      (conversion.addition (&x + &y) &z),
      (conversion.addition &x &y),
      (BinWithZero.modulo.sum.left.absorption
        (to_bin_with_zero &x + to_bin_with_zero &y)%bin_with_zero (to_bin_with_zero &z)
        modulus),
      (conversion.addition &x (&y + &z)),
      (conversion.addition &y &z),
      (BinWithZero.modulo.sum.right.absorption
        (to_bin_with_zero &x) (to_bin_with_zero &y + to_bin_with_zero &z)%bin_with_zero
        modulus),
      (BinWithZero.addition.associativity
        (to_bin_with_zero &x) (to_bin_with_zero &y) (to_bin_with_zero &z))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (x : UInt64) (y : UInt64) . x + y = y + x.
Proof.
  intros x y.
  lemma facto : to_bin_with_zero (&x + &y) = to_bin_with_zero (&y + &x).
  {
    leibniz
      (conversion.addition &x &y),
      (conversion.addition &y &x),
      (BinWithZero.addition.commutativity (to_bin_with_zero &x) (to_bin_with_zero &y))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* addition.identity *)
Theorem identity : forall (x : UInt64) . (Zero + x = x) /\ (x + Zero = x).
Proof.
  intros x.
  lemma left : Zero + &x = &x.
  {
    lemma facto : to_bin_with_zero (Zero + &x) = to_bin_with_zero &x.
    {
      match (BinWithZero.addition.identity (to_bin_with_zero &x)) with | left _ end.
      leibniz
        (conversion.addition Zero &x),
        conversion.zero,
        &left,
        (BinWithZero.modulo.identity
          (to_bin_with_zero &x) modulus (conversion.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (conversion.injectivity &facto).
  }
  divide et impera.
  - ipso &left.
  - leibniz (addition.commutativity &x Zero) in |- *.
    ipso &left.
Qed.

(* addition.inverse *)
Theorem inverse : forall (x : UInt64) . (- x + x = Zero) /\ (x + - x = Zero).
Proof.
  intros x.
  lemma left : - &x + &x = Zero.
  {
    lemma facto : to_bin_with_zero (- &x + &x) = to_bin_with_zero Zero.
    {
      leibniz
        (conversion.addition (- &x) &x),
        (conversion.negation &x),
        conversion.zero
        in |- *.
      quod idem est.
    }
    ipso (conversion.injectivity &facto).
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
  : forall (x : UInt64) (y : UInt64) (z : UInt64) . (x * y) * z = x * (y * z).
Proof.
  intros x y z.
  lemma facto : to_bin_with_zero ((&x * &y) * &z) = to_bin_with_zero (&x * (&y * &z)).
  {
    leibniz
      (conversion.multiplication (&x * &y) &z),
      (conversion.multiplication &x &y),
      (BinWithZero.modulo.product.left.absorption
        (to_bin_with_zero &x * to_bin_with_zero &y)%bin_with_zero (to_bin_with_zero &z)
        modulus),
      (conversion.multiplication &x (&y * &z)),
      (conversion.multiplication &y &z),
      (BinWithZero.modulo.product.right.absorption
        (to_bin_with_zero &x) (to_bin_with_zero &y * to_bin_with_zero &z)%bin_with_zero
        modulus),
      (BinWithZero.multiplication.associativity
        (to_bin_with_zero &x) (to_bin_with_zero &y) (to_bin_with_zero &z))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* multiplication.commutativity *)
Theorem commutativity : forall (x : UInt64) (y : UInt64) . x * y = y * x.
Proof.
  intros x y.
  lemma facto : to_bin_with_zero (&x * &y) = to_bin_with_zero (&y * &x).
  {
    leibniz
      (conversion.multiplication &x &y),
      (conversion.multiplication &y &x),
      (BinWithZero.multiplication.commutativity (to_bin_with_zero &x) (to_bin_with_zero &y))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* multiplication.identity *)
Theorem identity : forall (x : UInt64) . (One * x = x) /\ (x * One = x).
Proof.
  intros x.
  lemma left : One * &x = &x.
  {
    lemma facto : to_bin_with_zero (One * &x) = to_bin_with_zero &x.
    {
      match (BinWithZero.multiplication.identity (to_bin_with_zero &x)) with | left _ end.
      leibniz
        (conversion.multiplication One &x),
        conversion.one,
        &left,
        (BinWithZero.modulo.identity
          (to_bin_with_zero &x) modulus (conversion.boundedness &x))
        in |- *.
      quod idem est.
    }
    ipso (conversion.injectivity &facto).
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
  : forall (x : UInt64) (y : UInt64) (z : UInt64) . x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  lemma facto
    : to_bin_with_zero (&x * (&y + &z)) = to_bin_with_zero ((&x * &y) + (&x * &z)).
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            (to_bin_with_zero &x) (to_bin_with_zero &y) (to_bin_with_zero &z))
    with | spread _ end.
    leibniz
      (conversion.multiplication &x (&y + &z)),
      (conversion.addition &y &z),
      (BinWithZero.modulo.product.right.absorption
        (to_bin_with_zero &x) (to_bin_with_zero &y + to_bin_with_zero &z)%bin_with_zero
        modulus),
      &spread,
      (conversion.addition (&x * &y) (&x * &z)),
      (conversion.multiplication &x &y),
      (conversion.multiplication &x &z),
      (BinWithZero.modulo.sum.left.absorption
        (to_bin_with_zero &x * to_bin_with_zero &y)%bin_with_zero
        ((to_bin_with_zero &x * to_bin_with_zero &z) %. modulus)%bin_with_zero
        modulus),
      (BinWithZero.modulo.sum.right.absorption
        (to_bin_with_zero &x * to_bin_with_zero &y)%bin_with_zero
        (to_bin_with_zero &x * to_bin_with_zero &z)%bin_with_zero modulus)
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (x : UInt64) (y : UInt64) (z : UInt64) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : UInt64) (y : UInt64) (z : UInt64) .
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

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : UInt64} {y : UInt64} {z : UInt64} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (BinWithZero.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : UInt64) (y : UInt64) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  simpl compare, LessThan in |- *.
  let proof s :=
    BinWithZero.comparison.specification (to_bin_with_zero &x) (to_bin_with_zero &y).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_bin_with_zero, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : UInt64) (y : UInt64) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (BinWithZero.comparison.antisymmetry (to_bin_with_zero &x) (to_bin_with_zero &y)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End UInt64. (* UInt64 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [UInt64], not [UInt64.T].
 *)
Abbreviation UInt64 := UInt64.T.

(* Makes the notations declared in [Module UInt64] usable in every file that
 * imports this one, as [(x + y)%uint64] or under an opened [jwa_uint64_scope].
 *)
Export (notations) UInt64.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [200%uint64] or [0xFF%uint64], and a closed one prints in decimal.
 *)
Number Notation UInt64.T UInt64.from_numeral UInt64.to_numeral
  : jwa_uint64_scope.

(* Where a [UInt64] is expected, a literal or a notation reads in this scope
 * without its [%uint64].
 *)
Bind Scope jwa_uint64_scope with UInt64.T.

(* A [UInt64] stands wherever a [BinWithZero] is expected, read as its value,
 * and wherever a [Nat0] is, through that value; each conversion is printed
 * where it happened.
 *)
Coercion UInt64.to_bin_with_zero : UInt64 >-> BinWithZero.
Add Printing Coercion UInt64.to_bin_with_zero.
Coercion UInt64.to_nat0 : UInt64 >-> Nat0.
Add Printing Coercion UInt64.to_nat0.

(* Declared inside [Module UInt64]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance UInt64.comparable.

Instance UInt64_add_monoid
  : Monoid UInt64.add UInt64.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt64.addition.associativity |}
  ; Monoid.identity := UInt64.addition.identity |}.

Instance UInt64_mul_monoid
  : Monoid UInt64.mul UInt64.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt64.multiplication.associativity |}
  ; Monoid.identity := UInt64.multiplication.identity |}.

Instance UInt64_add_commutative
  : Commutative UInt64.add :=
  {| Commutative.commutativity := UInt64.addition.commutativity |}.

Instance UInt64_mul_commutative
  : Commutative UInt64.mul :=
  {| Commutative.commutativity := UInt64.multiplication.commutativity |}.

Instance UInt64_add_group
  : Group UInt64.add UInt64.Zero UInt64.negate :=
  {| Group.monoid := UInt64_add_monoid
  ; Group.inverse := UInt64.addition.inverse |}.

Instance UInt64_add_abelian_group
  : AbelianGroup UInt64.add UInt64.Zero UInt64.negate :=
  {| AbelianGroup.group := UInt64_add_group
  ; AbelianGroup.commutative := UInt64_add_commutative |}.

Instance UInt64_ring
  : Ring UInt64.add UInt64.Zero UInt64.negate UInt64.mul UInt64.One :=
  {| Ring.abelian_group := UInt64_add_abelian_group
  ; Ring.monoid := UInt64_mul_monoid
  ; Ring.distributivity := UInt64.multiplication.distributivity.over.addition |}.
