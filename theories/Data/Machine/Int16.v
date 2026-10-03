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
From jwa Require Import Data.Machine.Endian.
From jwa Require Import Data.Machine.HWord.
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

(* A signed integer of sixteen bits: two [Byte]s read in two's complement, from
 * -32768 (-2^15) to 32767 (2^15 - 1), its arithmetic wrapping modulo 65536
 * (2^16). In this file [10000000000000000] is 2^16, [1000000000000000] is 2^15
 * and [111111111111111] is 2^15 - 1, written in binary digits.
 *)

Module Int16. (* Int16 *)

Inductive T : Type :=
  | introduction : Byte -> Byte -> T.

Abbreviation Int16 := T.

(* The number of values, 65536 (2^16), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 10000000000000000%bin_base.

(* [x] laid out as a [HWord] in the order [e] names. *)
(* [Endian -> Int16 -> HWord] *)
Definition to_hword := fun (e : Endian) (x : Int16) .
  match x with
  | Int16.introduction b1 b0 => HWord.make e b0 b1
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [HWord -> Int16] *)
Definition from_hword := fun (w : HWord) . Int16.introduction (HWord.high w) (HWord.low w).

(* The bits read as a number in base two, the most significant first, from 0 to
 * 65535: the value of the bit pattern, through which the arithmetic is proved
 * and from which [to_bin] takes the signed value; [10] is two in binary digits.
 *)
(* [Int16 -> BinWithZero] *)
Definition unsigned_value := fun (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * Bit.to_bin_with_zero x15 + Bit.to_bin_with_zero x14) + Bit.to_bin_with_zero x13)
        + Bit.to_bin_with_zero x12) + Bit.to_bin_with_zero x11) + Bit.to_bin_with_zero x10)
        + Bit.to_bin_with_zero x9) + Bit.to_bin_with_zero x8) + Bit.to_bin_with_zero x7)
        + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5) + Bit.to_bin_with_zero x4)
        + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2) + Bit.to_bin_with_zero x1)
        + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* The top bit, [1] for a negative value. *)
(* [Int16 -> Bit] *)
Definition sign_bit := fun (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 _ _ _ _ _ _ _) _ => x15
  end.

(* The value in two's complement: the unsigned value, less 65536 when the sign
 * bit is set.
 *)
(* [Int16 -> Bin] *)
Definition to_bin := fun (x : Int16) .
  Bin.bin_with_zero_difference
    (unsigned_value x) (modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.

(* From here to the end of the module an [Int16] stands where a [Bin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_bin : T >-> Bin.
Add Printing Coercion to_bin.

(* The value in [Integer], through [to_bin]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_bin].
 *)
(* [Int16 -> Integer] *)
Definition to_integer := fun (x : Int16) . Bin.to_integer (to_bin x).

(* [Int16] *)
Definition Zero := Int16.introduction Byte.Zero Byte.Zero.

(* [Int16] *)
Definition One :=
  Int16.introduction
    Byte.Zero
    (Byte.introduction
      0 0 0 0 0 0 0 1).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [Int16 -> Nat -> Int16] *)
Fixpoint shift_left_nat (x : Int16) (k : Nat) : Int16 :=
  let y :=
    match x with
    | Int16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [Int16 -> Nat0 -> Int16] *)
Definition shift_left := fun (x : Int16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int16 -> Nat -> Int16] *)
Fixpoint shift_right_nat (x : Int16) (k : Nat) : Int16 :=
  let y :=
    match x with
    | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int16.introduction (Byte.introduction x15 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int16 -> Nat0 -> Int16] *)
Definition shift_right := fun (x : Int16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int16 -> Int16] *)
Definition append_bit := fun (b : Bit) (x : Int16) .
  match x with
  | Int16.introduction (Byte.introduction _ x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      Int16.introduction (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int16 -> Int16 -> Product Bit Int16] *)
Definition add_with_carry := fun (carry : Bit) (x : Int16) (y : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
          (pi_1 r15,
            Int16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int16 -> Int16 -> Int16] *)
Definition add := fun (x : Int16) (y : Int16) . (pi_2 (add_with_carry 0 x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_int16_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int16 -> Int16 -> Product Bit Int16] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int16) (y : Int16) .
  match x with
  | Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
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
          (pi_1 r15,
            Int16.introduction
              (Byte.introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int16 -> Int16 -> Int16] *)
Definition sub := fun (x : Int16) (y : Int16) . (pi_2 (sub_with_borrow 0 x y))%product.

(* [x] taken from [Zero], wrapping. *)
(* [Int16 -> Int16] *)
Definition negate := fun (x : Int16) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_int16_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 65536.
 *)
(* [Int16 -> Int16 -> Int16] *)
Definition mul := fun (x : Int16) (y : Int16) .
  let step := fun (p : Int16) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | 0%bit => Zero
      | 1%bit => x
      end in
  match y with
  | Int16.introduction (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        Zero y15) y14) y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_int16_scope.

(* The bit pattern of [p] modulo 65536, its bits appended from the most
 * significant.
 *)
(* [BinBase -> Int16] *)
Fixpoint from_bin_base (p : BinBase) : Int16 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit 0 (from_bin_base p')
  | BinBase.b1 p' => append_bit 1 (from_bin_base p')
  end.

(* [BinWithZero -> Int16] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> Int16] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> Int16] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [z] modulo 65536 into the range -32768 to 32767: its positive part less its
 * negative part, wrapping.
 *)
(* [Bin -> Int16] *)
Definition from_bin := fun (z : Bin) .
  add (from_bin_with_zero (Bin.ramp z)) (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).

(* The quotient through [Bin], toward zero, [None] when [y] is zero. [Bin.divide]
 * takes a positive divisor, so the divisor's sign is matched here; -32768
 * (-2^15) over -1 wraps to itself.
 *)
(* [Int16 -> Int16 -> Option Int16] *)
Definition divide := fun (x : Int16) (y : Int16) .
  match to_bin y with
  | Bin.Negative d => Some (from_bin (Bin.negate (x /. d)%b))
  | Bin.Zero       => None
  | Bin.Positive d => Some (from_bin (x /. d)%b)
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jwa_int16_scope.

(* [x] modulo 65536 into the range -32768 to 32767. *)
(* [Integer -> Int16] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past -32768 or
 * 32767.
 *)
(* [Int16 -> Int16 -> Product Bit Int16] *)
Definition add_with_overflow := fun (x : Int16) (y : Int16) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* [Int16 -> Int16 -> Prop] *)
Definition LessThan := fun (x : Int16) (y : Int16) . (to_bin x < to_bin y)%b.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_int16_scope.

(* [Int16 -> Int16 -> Prop] *)
Definition LessOrEqual := fun (x : Int16) (y : Int16) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_int16_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_int16_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_int16_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_int16_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_int16_scope.

(* [Int16 -> Int16 -> Comparison] *)
Definition compare := fun (x : Int16) (y : Int16) . Bin.compare (to_bin x) (to_bin y).

(* [Int16 -> Int16 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int16 -> Int16 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int16 -> Int16 -> Int16] *)
Abbreviation min := (Comparable.min compare).

(* [Int16 -> Int16 -> Int16] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -32768 to 32767, in decimal or hexadecimal, read in binary; any
 * wider is refused.
 *)
(* [Numeral.Signed -> Option Int16] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : BinWithZero) .
    match BinWithZero.compare v 111111111111111%bin_with_zero with
    | Comparison.Lt => Some (from_bin_with_zero v)
    | Comparison.Eq => Some (from_bin_with_zero v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : BinWithZero) .
    match BinWithZero.compare v 1000000000000000%bin_with_zero with
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
(* [Int16 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int16) .
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

Local Open Scope jwa_int16_scope.

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
Theorem boundedness : forall (x : Int16) . (unsigned_value x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | introduction xb1 xb0 end.
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
    (Bit.conversion.binary.boundedness &x15)))))))))))))))).
Qed.

(* valuation.injectivity *)
Theorem injectivity
  : forall {x : Int16} {y : Int16} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
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
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, &b7, &b8, &b9, &b10, &b11, &b12, &b13, &b14,
    (Bit.conversion.binary.injectivity &e15)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* valuation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int16) (y : Int16) .
      (Bit.to_bin_with_zero carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
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
    (Bit.conversion.binary.carry _ &x15 &y15)))))))))))))))).
Qed.

(* valuation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int16) (y : Int16) .
      (unsigned_value x
        + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_bin_with_zero borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
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
    (Bit.conversion.binary.borrow _ &x15 &y15)))))))))))))))).
Qed.

(* valuation.addition *)
Theorem addition
  : forall (x : Int16) (y : Int16) .
      (unsigned_value (x + y)%int16
        = (unsigned_value x + unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product * modulus
        + unsigned_value (&x + &y)%int16
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int16 < modulus)%bin_with_zero.
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
          (unsigned_value (&x + &y)%int16)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* valuation.subtraction *)
Theorem subtraction
  : forall (x : Int16) (y : Int16) .
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
  : forall (x : Int16) .
      ((unsigned_value (- x)%int16 + unsigned_value x) %. modulus
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
  : forall (b : Bit) (x : Int16) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x15 * modulus
        + unsigned_value
            (append_bit &b
              (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ unsigned_value
          (append_bit &b
            (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%bin_with_zero.
  {
    divide et impera.
    - lemma top
        : (Bit.to_bin_with_zero &x15 = Bit.to_bin_with_zero &x15 * 1 + 0)%bin_with_zero.
      {
        match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x15 * 1)%bin_with_zero)
        with | _ sum end.
        match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x15))
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
          &top))))))))))))))))).
    - ipso
        (valuation.boundedness
          (append_bit &b
            (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * unsigned_value
                  (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x15)
          (unsigned_value
            (append_bit &b
              (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
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
Theorem section : forall (x : Int16) . from_bin_with_zero (unsigned_value x) = x.
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
  : forall (x : Int16) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit 0 &x.
  {
    match &x with | introduction xb1 xb0 end.
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
  : forall (x : Int16) (p : Int16) (h : BinWithZero) (b : Bit) .
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
  : forall (x : Int16) (y : Int16) .
      (unsigned_value (x * y)%int16
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
  match &y with | introduction yb1 yb0 end.
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
    (valuation.multiplication.step _ _ _ _ &base)))))))))))))))).
Qed.

Module sign. (* valuation.sign *)

(* valuation.sign.clear *)
Theorem clear
  : forall (x : Int16) .
      sign_bit x = 0%bit -> (unsigned_value x < 1000000000000000)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb1 xb0 end.
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
    &base))))))))))))))).
Qed.

(* valuation.sign.set *)
Theorem set
  : forall (x : Int16) .
      sign_bit x = 1%bit -> (1000000000000000 <= unsigned_value x)%bin_with_zero.
Proof.
  intros x e.
  match &x with | introduction xb1 xb0 end.
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
    &base))))))))))))))).
Qed.

End sign. (* valuation.sign *)

End valuation. (* valuation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Int16) (y : Int16) (z : Int16) . (x + y) + z = x + (y + z).
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
Theorem commutativity : forall (x : Int16) (y : Int16) . x + y = y + x.
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
Theorem identity : forall (x : Int16) . (Zero + x = x) /\ (x + Zero = x).
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
Theorem inverse : forall (x : Int16) . (- x + x = Zero) /\ (x + - x = Zero).
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
  : forall (x : Int16) (y : Int16) (z : Int16) . (x * y) * z = x * (y * z).
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
Theorem commutativity : forall (x : Int16) (y : Int16) . x * y = y * x.
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
Theorem identity : forall (x : Int16) . (One * x = x) /\ (x * One = x).
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
  : forall (x : Int16) (y : Int16) (z : Int16) . x * (y + z) = (x * y) + (x * z).
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
  : forall (x : Int16) (y : Int16) (z : Int16) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : Int16) (y : Int16) (z : Int16) .
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
Theorem section : forall (x : Int16) . from_bin (to_bin x) = x.
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
Theorem injectivity : forall {x : Int16} {y : Int16} . to_bin x = to_bin y -> x = y.
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
  : forall (x : Int16) (y : Int16) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      (Bit.to_bin_with_zero (sign_bit x) + Bit.to_bin_with_zero (sign_bit y)
        = Bit.to_bin_with_zero (pi_1 (add_with_carry 0 x y))%product
          + Bit.to_bin_with_zero (sign_bit (x + y)%int16))%bin_with_zero.
Proof.
  intros x y o.
  match &x with | introduction xb1 xb0 end.
  match &xb1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | introduction yb1 yb0 end.
  match &yb1 with | introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x15 &y15 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int16) (y : Int16) .
      (pi_1 (add_with_overflow x y))%product = 0%bit ->
      to_bin (x + y) = (x + y)%b.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product
          + unsigned_value (&x + &y)%int16)%bin_with_zero
    := valuation.carry 0 &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int16
        + (modulus * Bit.to_bin_with_zero (sign_bit &x)
          + modulus * Bit.to_bin_with_zero (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int16))%bin_with_zero.
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (sign_bit &x)) (Bit.to_bin_with_zero (sign_bit &y)))
    with | signs _ end.
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)
            (Bit.to_bin_with_zero (sign_bit (&x + &y)%int16)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (BinWithZero.addition.associativity
        (unsigned_value (&x + &y)%int16)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry 0 &x &y))%product)%bin_with_zero
        (modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int16))%bin_with_zero),
      (BinWithZero.addition.commutativity
        (unsigned_value (&x + &y)%int16)
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
  : forall (x15 : Bit) (x14 : Bit) (x13 : Bit) (x12 : Bit)
      (x11 : Bit) (x10 : Bit) (x9 : Bit) (x8 : Bit)
      (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_bin (Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
                (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right
            (Int16.introduction (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
              (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_bin_with_zero x0)%b.
Proof.
  intros x15 x14 x13 x12 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
        (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_bin_with_zero &x0
        = Bit.to_bin_with_zero &x15 * modulus
          + unsigned_value
              (Int16.introduction
                (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%bin_with_zero.
  {
    lemma top
      : (Bit.to_bin_with_zero &x15 = Bit.to_bin_with_zero &x15 * 1 + 0)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x15 * 1)%bin_with_zero)
      with | _ sum end.
      match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x15))
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
      &top)))))))))))))))).
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
        (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
          (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_bin_with_zero &x15 + modulus * Bit.to_bin_with_zero &x15 + 0)
        = (unsigned_value
            (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
              (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_bin_with_zero &x0)
          + modulus * Bit.to_bin_with_zero &x15)%bin_with_zero.
  {
    match (BinWithZero.addition.identity
            (modulus * Bit.to_bin_with_zero &x15
              + modulus * Bit.to_bin_with_zero &x15)%bin_with_zero)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (BinWithZero.multiplication.commutativity
        (Bit.to_bin_with_zero &x15) modulus),
      (BinWithZero.addition.commutativity
        (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (BinWithZero.addition.associativity
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
            (Byte.introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero
        (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_bin, sign_bit in |- *.
  leibniz
    (&twice
      (Bin.bin_with_zero_difference
        (unsigned_value
          (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
            (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero)),
    (Bin.difference.additivity
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x15)%bin_with_zero),
    (&embedding (Bit.to_bin_with_zero &x0)),
    (Bin.difference.additivity
      (unsigned_value
        (Int16.introduction (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
          (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int16.introduction
              (Byte.introduction &x15 &x15 &x14 &x13 &x12 &x11 &x10 &x9)
                (Byte.introduction &x8 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%bin_with_zero
      (modulus * Bit.to_bin_with_zero &x15
        + modulus * Bit.to_bin_with_zero &x15)%bin_with_zero
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
  : forall (x : Int16) (p : BinBase) .
      to_bin x = Bin.Positive p -> (p < 1000000000000000)%bin_with_zero.
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
  : forall (x : Int16) (p : BinBase) .
      to_bin x = Bin.Negative p -> (p <= 1000000000000000)%bin_with_zero.
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
        (BinWithZero.Positive p) 1000000000000000%bin_with_zero)
    with
    | below | rest end.
    + simpl BinWithZero.LessOrEqual in |- *.
      ipso (disjoin _, &below).
    + match &rest with | same | above end.
      * simpl BinWithZero.LessOrEqual in |- *.
        ipso (disjoin &same, _).
      * lemma double : (1000000000000000 + 1000000000000000 = modulus)%bin_with_zero.
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
      (n < 1000000000000000)%bin_with_zero
      -> to_bin (from_bin (Bin.from_bin_with_zero n)) = Bin.from_bin_with_zero n.
Proof.
  intros n h.
  lemma half : (1000000000000000 < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 1000000000000000%bin_base.
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
      (p <= 1000000000000000)%bin_with_zero
      -> to_bin (from_bin (Bin.Negative p)) = Bin.Negative p.
Proof.
  intros p h.
  leibniz (conversion.bin.negative &p) in |- *.
  lemma half : (1000000000000000 < modulus)%bin_with_zero.
  {
    simpl BinWithZero.LessThan in |- *.
    exists 1000000000000000%bin_base.
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
  lemma double : (1000000000000000 + 1000000000000000 = modulus)%bin_with_zero.
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
  : forall (x : Int16) (y : Int16) (d : BinBase) .
      to_bin y = Bin.Positive d -> Option.map to_bin (x /. y)%int16 = Some (x /. d)%b.
Proof.
  intros x y d e.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing : (0 < 1000000000000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 1000000000000000%bin_base.
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
        lemma bounded : (q <= 1000000000000000)%bin_with_zero.
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
  : forall (x : Int16) (y : Int16) (d : BinBase) .
      to_bin y = Bin.Negative d
      -> ~ (to_bin x = (-1000000000000000)%b /\ d = BinBase.One)
      -> Option.map to_bin (x /. y)%int16 = Some (Bin.negate (x /. d)%b).
Proof.
  intros x y d e h.
  lemma origin : to_bin (from_bin 0%b) = 0%b.
  {
    lemma nothing : (0 < 1000000000000000)%bin_with_zero.
    {
      simpl BinWithZero.LessThan in |- *.
      exists 1000000000000000%bin_base.
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
      lemma below : ((p /. &d) < 1000000000000000)%bin_with_zero.
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
                  (Identity.reflexivity (-1000000000000000)%b),
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
        lemma bounded : (q <= 1000000000000000)%bin_with_zero.
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

Module hword. (* conversion.hword *)

(* conversion.hword.retraction *)
Theorem retraction : forall (w : HWord) . to_hword (HWord.endian w) (from_hword w) = w.
Proof.
  intros w.
  match &w with | introduction e b0 b1 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.hword.section *)
Theorem section : forall (e : Endian) (x : Int16) . from_hword (to_hword e x) = x.
Proof.
  intros e x.
  match &x with | introduction b1 b0 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End hword. (* conversion.hword *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Int16} {y : Int16} {z : Int16} . x < y -> y < z -> x < z.
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
  : forall (x : Int16) (y : Int16) .
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
  : forall (x : Int16) (y : Int16) . compare x y = Comparison.transpose (compare y x).
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

End Int16. (* Int16 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Int16], not [Int16.T].
 *)
Abbreviation Int16 := Int16.T.

(* Makes the notations declared in [Module Int16] usable in every file that
 * imports this one, as [(x + y)%int16] or under an opened [jwa_int16_scope].
 *)
Export (notations) Int16.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int16], [(-100)%int16] or [0x7F%int16], and a closed one prints
 * in decimal.
 *)
Number Notation Int16.T Int16.from_numeral Int16.to_numeral
  : jwa_int16_scope.

(* Where an [Int16] is expected, a literal or a notation reads in this scope
 * without its [%int16].
 *)
Bind Scope jwa_int16_scope with Int16.T.

(* An [Int16] stands wherever a [Bin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int16.to_bin : Int16 >-> Bin.
Add Printing Coercion Int16.to_bin.
Coercion Int16.to_integer : Int16 >-> Integer.
Add Printing Coercion Int16.to_integer.

(* Declared inside [Module Int16]; an instance declared there is dropped at
 * the module's [End], so it is announced again here.
 *)
Existing Instance Int16.comparable.

Instance Int16_add_monoid
  : Monoid Int16.add Int16.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int16.addition.associativity |}
  ; Monoid.identity := Int16.addition.identity |}.

Instance Int16_mul_monoid
  : Monoid Int16.mul Int16.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int16.multiplication.associativity |}
  ; Monoid.identity := Int16.multiplication.identity |}.

Instance Int16_add_commutative
  : Commutative Int16.add :=
  {| Commutative.commutativity := Int16.addition.commutativity |}.

Instance Int16_mul_commutative
  : Commutative Int16.mul :=
  {| Commutative.commutativity := Int16.multiplication.commutativity |}.

Instance Int16_add_group
  : Group Int16.add Int16.Zero Int16.negate :=
  {| Group.monoid := Int16_add_monoid
  ; Group.inverse := Int16.addition.inverse |}.

Instance Int16_add_abelian_group
  : AbelianGroup Int16.add Int16.Zero Int16.negate :=
  {| AbelianGroup.group := Int16_add_group
  ; AbelianGroup.commutative := Int16_add_commutative |}.

Instance Int16_ring
  : Ring Int16.add Int16.Zero Int16.negate Int16.mul Int16.One :=
  {| Ring.abelian_group := Int16_add_abelian_group
  ; Ring.monoid := Int16_mul_monoid
  ; Ring.distributivity := Int16.multiplication.distributivity.over.addition |}.
