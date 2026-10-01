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

(* A signed integer of eight bits: a [Byte] read in two's complement, from
 * -128 (-2^7) to 127 (2^7 - 1), its arithmetic wrapping modulo 256 (2^8). In
 * this file [100000000] is 2^8, [10000000] is 2^7 and [1111111] is 2^7 - 1,
 * written in binary digits.
 *)

Module Int8. (* Int8 *)

Inductive T : Type :=
  | Int8_introduction : Byte -> T.

Abbreviation Int8 := T.

(* The number of values, 256 (2^8), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 100000000%bin_base.

(* [Int8 -> Byte] *)
Definition to_byte := fun (x : Int8) .
  match x with
  | Int8_introduction b => b
  end.

(* [Byte -> Int8] *)
Definition from_byte := fun (b : Byte) . Int8_introduction b.

(* The bits read as a number in base two, the most significant first, from 0
 * to 255: the value of the bit pattern, through which the arithmetic is
 * proved and from which [to_bin] takes the signed value; [10] is two in
 * binary digits.
 *)
(* [Int8 -> BinWithZero] *)
Definition unsigned_value := fun (x : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * Bit.to_bin_with_zero x7
        + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5) + Bit.to_bin_with_zero x4)
        + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2) + Bit.to_bin_with_zero x1)
        + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* The top bit, [Bit.One] for a negative value. *)
(* [Int8 -> Bit] *)
Definition sign_bit := fun (x : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction x7 _ _ _ _ _ _ _) => x7
  end.

(* The value in two's complement: the unsigned value, less 256 when the sign
 * bit is set.
 *)
(* [Int8 -> Bin] *)
Definition to_bin := fun (x : Int8) .
  Bin.bin_with_zero_difference
    (unsigned_value x) (modulus * Bit.to_bin_with_zero (sign_bit x))%bin_with_zero.

(* From here to the end of the module an [Int8] stands where a [Bin] is expected,
 * read as its value; the conversion is printed.
 *)
Local Coercion to_bin : T >-> Bin.
Add Printing Coercion to_bin.

(* The value in [Integer], through [to_bin]; [Integer] is unary, so it is for
 * stating and proving, and computing goes through [to_bin].
 *)
(* [Int8 -> Integer] *)
Definition to_integer := fun (x : Int8) . Bin.to_integer (to_bin x).

(* [Int8] *)
Definition Zero := Int8_introduction Byte.Zero.

(* [Int8] *)
Definition One :=
  Int8_introduction
    (Byte.Byte_introduction
      Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One).

(* [Int8 -> Nat0 -> Int8] *)
Definition shift_left := fun (x : Int8) (k : Nat0) .
  match x with
  | Int8_introduction b => Int8_introduction (Byte.shift_left b k)
  end.

(* [k] places toward the least significant end, the sign bit copied in at
 * the other; one place first, then [k - 1].
 *)
(* [Int8 -> Nat -> Int8] *)
Fixpoint shift_right_nat (x : Int8) (k : Nat) : Int8 :=
  let y :=
    match x with
    | Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Int8_introduction (Byte.Byte_introduction x7 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Int8 -> Nat0 -> Int8] *)
Definition shift_right := fun (x : Int8) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> Int8 -> Int8] *)
Definition append_bit := fun (b : Bit) (x : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction _ x6 x5 x4 x3 x2 x1 x0) =>
      Int8_introduction (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> Int8 -> Int8 -> Product Bit Int8] *)
Definition add_with_carry := fun (carry : Bit) (x : Int8) (y : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Int8_introduction
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int8 -> Int8 -> Int8] *)
Definition add := fun (x : Int8) (y : Int8) . (pi_2 (add_with_carry Bit.Zero x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_int8_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Int8 -> Int8 -> Product Bit Int8] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Int8) (y : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | Int8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Int8_introduction
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [Int8 -> Int8 -> Int8] *)
Definition sub := fun (x : Int8) (y : Int8) . (pi_2 (sub_with_borrow Bit.Zero x y))%product.

(* [x] taken from [Zero], wrapping. *)
(* [Int8 -> Int8] *)
Definition negate := fun (x : Int8) . sub Zero x.

(* Also what makes the minus of a negative literal parse: [Numeral.Signed]
 * lets [from_numeral] receive a sign but puts none in the grammar.
 *)
Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_int8_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 256.
 *)
(* [Int8 -> Int8 -> Int8] *)
Definition mul := fun (x : Int8) (y : Int8) .
  let step := fun (p : Int8) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | Bit.Zero => Zero
      | Bit.One  => x
      end in
  match y with
  | Int8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step Zero y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_int8_scope.

(* The bit pattern of [p] modulo 256, its bits appended from the most
 * significant.
 *)
(* [BinBase -> Int8] *)
Fixpoint from_bin_base (p : BinBase) : Int8 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit Bit.Zero (from_bin_base p')
  | BinBase.b1 p' => append_bit Bit.One (from_bin_base p')
  end.

(* [BinWithZero -> Int8] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> Int8] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> Int8] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [z] modulo 256 into the range -128 to 127: its positive part less its
 * negative part, wrapping.
 *)
(* [Bin -> Int8] *)
Definition from_bin := fun (z : Bin) .
  add (from_bin_with_zero (Bin.ramp z)) (negate (from_bin_with_zero (Bin.ramp (Bin.negate z)))).

(* [x] modulo 256 into the range -128 to 127. *)
(* [Integer -> Int8] *)
Definition from_integer := fun (x : Integer) .
  match x with
  | Integer.Negative p => negate (from_nat p)
  | Integer.Zero       => Zero
  | Integer.Positive p => from_nat p
  end.

(* The overflow flag and the sum of [x + y]: the flag is set when [x] and [y]
 * have the same sign and the sum the other, the true sum lying past -128 or
 * 127.
 *)
(* [Int8 -> Int8 -> Product Bit Int8] *)
Definition add_with_overflow := fun (x : Int8) (y : Int8) .
  let flag :=
    Bit.and
      (Bit.flip (Bit.xor (sign_bit x) (sign_bit y)))
      (Bit.xor (sign_bit (add x y)) (sign_bit x)) in
  (flag, add x y)%product.

(* [Int8 -> Int8 -> Prop] *)
Definition LessThan := fun (x : Int8) (y : Int8) . (to_bin x < to_bin y)%b.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_int8_scope.

(* [Int8 -> Int8 -> Prop] *)
Definition LessOrEqual := fun (x : Int8) (y : Int8) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_int8_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_int8_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_int8_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_int8_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_int8_scope.

(* [Int8 -> Int8 -> Comparison] *)
Definition compare := fun (x : Int8) (y : Int8) . Bin.compare (to_bin x) (to_bin y).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation min := (Comparable.min compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation max := (Comparable.max compare).

(* A literal of -128 to 127, in decimal or hexadecimal, read in binary; any
 * wider is refused.
 *)
(* [Numeral.Signed -> Option Int8] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : BinWithZero) .
    match BinWithZero.compare v 1111111%bin_with_zero with
    | Comparison.Lt => Some (from_bin_with_zero v)
    | Comparison.Eq => Some (from_bin_with_zero v)
    | Comparison.Gt => None
    end in
  let negative := fun (v : BinWithZero) .
    match BinWithZero.compare v 10000000%bin_with_zero with
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
(* [Int8 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int8) .
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

Local Open Scope jwa_int8_scope.

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
Theorem boundedness : forall (x : Int8) . (unsigned_value x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl unsigned_value in |- *.
  ipso
    (Bit.conversion.binary.boundedness.propagation _ _ _
      (Bit.conversion.binary.boundedness.propagation _ _ _
        (Bit.conversion.binary.boundedness.propagation _ _ _
          (Bit.conversion.binary.boundedness.propagation _ _ _
            (Bit.conversion.binary.boundedness.propagation _ _ _
              (Bit.conversion.binary.boundedness.propagation _ _ _
                (Bit.conversion.binary.boundedness.propagation _ _ _
                  (Bit.conversion.binary.boundedness &x7)))))))).
Qed.

(* valuation.injectivity *)
Theorem injectivity
  : forall {x : Int8} {y : Int8} . unsigned_value x = unsigned_value y -> x = y.
Proof.
  intros x y e.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value in &e.
  match (Bit.conversion.binary.halving.injectivity &e) with | e1 b0 end.
  match (Bit.conversion.binary.halving.injectivity &e1) with | e2 b1 end.
  match (Bit.conversion.binary.halving.injectivity &e2) with | e3 b2 end.
  match (Bit.conversion.binary.halving.injectivity &e3) with | e4 b3 end.
  match (Bit.conversion.binary.halving.injectivity &e4) with | e5 b4 end.
  match (Bit.conversion.binary.halving.injectivity &e5) with | e6 b5 end.
  match (Bit.conversion.binary.halving.injectivity &e6) with | e7 b6 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, (Bit.conversion.binary.injectivity &e7)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.binary.carry.propagation] around the places
 * above it.
 *)
(* valuation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int8) (y : Int8) .
      (Bit.to_bin_with_zero carry + unsigned_value x + unsigned_value y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, add_with_carry in |- *.
  ipso
    (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.binary.carry.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.binary.carry _ &x7 &y7)))))))).
Qed.

(* valuation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int8) (y : Int8) .
      (unsigned_value x
        + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_bin_with_zero borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, sub_with_borrow in |- *.
  ipso
    (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.binary.borrow.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.binary.borrow _ &x7 &y7)))))))).
Qed.

(* valuation.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      (unsigned_value (x + y)%int8
        = (unsigned_value x + unsigned_value y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product * modulus
        + unsigned_value (&x + &y)%int8
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int8 < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          modulus),
        <- (valuation.carry Bit.Zero &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (valuation.boundedness (&x + &y)).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value &x + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          (unsigned_value (&x + &y)%int8)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* valuation.subtraction *)
Theorem subtraction
  : forall (x : Int8) (y : Int8) .
      ((unsigned_value (sub x y) + unsigned_value y) %. modulus
        = unsigned_value x)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product * modulus
        + unsigned_value &x
        = unsigned_value (sub &x &y) + unsigned_value &y
      /\ unsigned_value &x < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)
          modulus),
        (BinWithZero.addition.commutativity
          (modulus
            * Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)%bin_with_zero
          (unsigned_value &x)),
        (valuation.borrow Bit.Zero &x &y),
        (BinWithZero.addition.commutativity
          (unsigned_value &y) (Bit.to_bin_with_zero Bit.Zero))
        in |- *.
      simpl in |- *.
      leibniz
        (BinWithZero.addition.commutativity
          (unsigned_value &y)
          (unsigned_value (pi_2 (sub_with_borrow Bit.Zero &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (valuation.boundedness &x).
  }
  match (BinWithZero.division.uniqueness
          (unsigned_value (sub &x &y) + unsigned_value &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)
          (unsigned_value &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* valuation.negation *)
Theorem negation
  : forall (x : Int8) .
      ((unsigned_value (- x)%int8 + unsigned_value x) %. modulus
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
  : forall (b : Bit) (x : Int8) .
      (unsigned_value (append_bit b x)
        = (10 * unsigned_value x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x7 * modulus
        + unsigned_value
            (append_bit &b
              (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * unsigned_value
                (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ unsigned_value
          (append_bit &b
            (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        < modulus)%bin_with_zero.
  {
    divide et impera.
    - lemma top
        : (Bit.to_bin_with_zero &x7 = Bit.to_bin_with_zero &x7 * 1 + 0)%bin_with_zero.
      {
        match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x7 * 1)%bin_with_zero)
        with | _ sum end.
        match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x7))
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
                          &top))))))))).
    - ipso
        (valuation.boundedness
          (append_bit &b
            (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * unsigned_value
                  (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x7)
          (unsigned_value
            (append_bit &b
              (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
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
        : from_bin_base (BinBase.b0 &p') = append_bit Bit.Zero (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (valuation.appending Bit.Zero (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero Bit.Zero) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero Bit.Zero) modulus)
        in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding
        : from_bin_base (BinBase.b1 &p') = append_bit Bit.One (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (valuation.appending Bit.One (from_bin_base &p')),
        &IH,
        <- (BinWithZero.modulo.sum.left.absorption
          (10 * (BinWithZero.Positive &p' %. modulus))%bin_with_zero
          (Bit.to_bin_with_zero Bit.One) modulus),
        (BinWithZero.modulo.product.right.absorption
          10%bin_with_zero (BinWithZero.Positive &p') modulus),
        (BinWithZero.modulo.sum.left.absorption
          (10 * BinWithZero.Positive &p')%bin_with_zero
          (Bit.to_bin_with_zero Bit.One) modulus)
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
Theorem section : forall (x : Int8) . from_bin_with_zero (unsigned_value x) = x.
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
  : forall (x : Int8) .
      (unsigned_value (shift_left x 1%n0)
        = (10 * unsigned_value x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit Bit.Zero &x.
  {
    match &x with | Int8_introduction xb end.
    match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  }
  match (BinWithZero.addition.identity (10 * unsigned_value &x)%bin_with_zero)
  with | _ sum end.
  leibniz &appended, (valuation.appending Bit.Zero &x) in |- *.
  simpl Bit.to_bin_with_zero in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

End left. (* valuation.left *)

Module multiplication. (* valuation.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* valuation.multiplication.step *)
Lemma step
  : forall (x : Int8) (p : Int8) (h : BinWithZero) (b : Bit) .
      (unsigned_value p = (unsigned_value x * h) %. modulus)%bin_with_zero ->
      unsigned_value
        (add (shift_left p 1%n0)
          match b with
          | Bit.Zero => Zero
          | Bit.One  => x
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
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero Bit.Zero))
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
        = ((unsigned_value &x * (10 * &h + Bit.to_bin_with_zero Bit.One))
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
  : forall (x : Int8) (y : Int8) .
      (unsigned_value (x * y)%int8
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
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (valuation.multiplication.step _ _ _ _
      (valuation.multiplication.step _ _ _ _
        (valuation.multiplication.step _ _ _ _
          (valuation.multiplication.step _ _ _ _
            (valuation.multiplication.step _ _ _ _
              (valuation.multiplication.step _ _ _ _
                (valuation.multiplication.step _ _ _ _
                  (valuation.multiplication.step _ _ _ _ &base)))))))).
Qed.

End valuation. (* valuation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Int8) (y : Int8) (z : Int8) . (x + y) + z = x + (y + z).
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
Theorem commutativity : forall (x : Int8) (y : Int8) . x + y = y + x.
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
Theorem identity : forall (x : Int8) . (Zero + x = x) /\ (x + Zero = x).
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
Theorem inverse : forall (x : Int8) . (- x + x = Zero) /\ (x + - x = Zero).
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
  : forall (x : Int8) (y : Int8) (z : Int8) . (x * y) * z = x * (y * z).
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
Theorem commutativity : forall (x : Int8) (y : Int8) . x * y = y * x.
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
Theorem identity : forall (x : Int8) . (One * x = x) /\ (x * One = x).
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
  : forall (x : Int8) (y : Int8) (z : Int8) . x * (y + z) = (x * y) + (x * z).
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
  : forall (x : Int8) (y : Int8) (z : Int8) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : Int8) (y : Int8) (z : Int8) .
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
Theorem section : forall (x : Int8) . from_bin (to_bin x) = x.
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
Theorem injectivity : forall {x : Int8} {y : Int8} . to_bin x = to_bin y -> x = y.
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
  : forall (x : Int8) (y : Int8) .
      (pi_1 (add_with_overflow x y))%product = Bit.Zero ->
      (Bit.to_bin_with_zero (sign_bit x) + Bit.to_bin_with_zero (sign_bit y)
        = Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero x y))%product
          + Bit.to_bin_with_zero (sign_bit (x + y)%int8))%bin_with_zero.
Proof.
  intros x y o.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.binary.carry.conservation _ &x7 &y7 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      (pi_1 (add_with_overflow x y))%product = Bit.Zero ->
      to_bin (x + y) = (x + y)%b.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product
          + unsigned_value (&x + &y)%int8)%bin_with_zero
    := valuation.carry Bit.Zero &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int8
        + (modulus * Bit.to_bin_with_zero (sign_bit &x)
          + modulus * Bit.to_bin_with_zero (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int8))%bin_with_zero.
  {
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (sign_bit &x)) (Bit.to_bin_with_zero (sign_bit &y)))
    with | signs _ end.
    match (BinWithZero.multiplication.distributivity.over.addition
            modulus
            (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)
            (Bit.to_bin_with_zero (sign_bit (&x + &y)%int8)))
    with | carries _ end.
    leibniz
      <- &signs,
      &t,
      &carries,
      <- (BinWithZero.addition.associativity
        (unsigned_value (&x + &y)%int8)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)%bin_with_zero
        (modulus * Bit.to_bin_with_zero (sign_bit (&x + &y)%int8))%bin_with_zero),
      (BinWithZero.addition.commutativity
        (unsigned_value (&x + &y)%int8)
        (modulus
          * Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)%bin_with_zero),
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
  : forall (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_bin (Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (10
          * shift_right (Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)) 1%n0
          + Bit.to_bin_with_zero x0)%b.
Proof.
  intros x7 x6 x5 x4 x3 x2 x1 x0.
  lemma shifted
    : shift_right
        (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)) 1%n0
      = Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma split
    : (10 * unsigned_value
              (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + Bit.to_bin_with_zero &x0
        = Bit.to_bin_with_zero &x7 * modulus
          + unsigned_value
              (Int8_introduction
                (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))%bin_with_zero.
  {
    lemma top
      : (Bit.to_bin_with_zero &x7 = Bit.to_bin_with_zero &x7 * 1 + 0)%bin_with_zero.
    {
      match (BinWithZero.addition.identity (Bit.to_bin_with_zero &x7 * 1)%bin_with_zero)
      with | _ sum end.
      match (BinWithZero.multiplication.identity (Bit.to_bin_with_zero &x7))
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
                      &top)))))))).
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
    : (unsigned_value (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
        + (modulus * Bit.to_bin_with_zero &x7 + modulus * Bit.to_bin_with_zero &x7 + 0)
        = (unsigned_value
            (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + unsigned_value
              (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
          + Bit.to_bin_with_zero &x0)
          + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero.
  {
    match (BinWithZero.addition.identity
            (modulus * Bit.to_bin_with_zero &x7
              + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)
    with | _ unit end.
    leibniz
      &unit,
      (&doubled
        (unsigned_value
          (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))),
      &split,
      (BinWithZero.multiplication.commutativity
        (Bit.to_bin_with_zero &x7) modulus),
      (BinWithZero.addition.commutativity
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
        (unsigned_value
          (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))),
      (BinWithZero.addition.associativity
        (unsigned_value
          (Int8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)
      in |- *.
    quod idem est.
  }
  leibniz &shifted in |- *.
  simpl to_bin, sign_bit in |- *.
  leibniz
    (&twice
      (Bin.bin_with_zero_difference
        (unsigned_value
          (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
        (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero)),
    (Bin.difference.additivity
      (unsigned_value
        (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
      (unsigned_value
        (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))
      (modulus * Bit.to_bin_with_zero &x7)%bin_with_zero),
    (&embedding (Bit.to_bin_with_zero &x0)),
    (Bin.difference.additivity
      (unsigned_value
        (Int8_introduction (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1))
        + unsigned_value
            (Int8_introduction
              (Byte.Byte_introduction &x7 &x7 &x6 &x5 &x4 &x3 &x2 &x1)))%bin_with_zero
      (modulus * Bit.to_bin_with_zero &x7
        + modulus * Bit.to_bin_with_zero &x7)%bin_with_zero
      (Bit.to_bin_with_zero &x0) 0%bin_with_zero)
    in |- *.
  ipso (Bin.difference.invariance &balance).
Qed.

End right. (* conversion.right *)

Module byte. (* conversion.byte *)

(* conversion.byte.retraction *)
Theorem retraction : forall (b : Byte) . to_byte (from_byte b) = b.
Proof.
  intros b.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

(* conversion.byte.section *)
Theorem section : forall (x : Int8) . from_byte (to_byte x) = x.
Proof.
  intros x.
  match &x with | Int8_introduction b end.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

End byte. (* conversion.byte *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Int8} {y : Int8} {z : Int8} . x < y -> y < z -> x < z.
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
  : forall (x : Int8) (y : Int8) .
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
  : forall (x : Int8) (y : Int8) . compare x y = Comparison.transpose (compare y x).
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

End Int8. (* Int8 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Int8], not [Int8.T].
 *)
Abbreviation Int8 := Int8.T.

(* Makes the notations declared in [Module Int8] usable in every file that
 * imports this one, as [(x + y)%int8] or under an opened [jwa_int8_scope].
 *)
Export (notations) Int8.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [100%int8], [(-100)%int8] or [0x7F%int8], and a closed one prints
 * in decimal.
 *)
Number Notation Int8.T Int8.from_numeral Int8.to_numeral
  : jwa_int8_scope.

(* Where an [Int8] is expected, a literal or a notation reads in this scope
 * without its [%int8].
 *)
Bind Scope jwa_int8_scope with Int8.T.

(* An [Int8] stands wherever a [Bin] is expected, read as its value in two's
 * complement, and wherever an [Integer] is, through that value; each
 * conversion is printed where it happened.
 *)
Coercion Int8.to_bin : Int8 >-> Bin.
Add Printing Coercion Int8.to_bin.
Coercion Int8.to_integer : Int8 >-> Integer.
Add Printing Coercion Int8.to_integer.

Instance Int8_add_monoid
  : Monoid Int8.add Int8.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int8.addition.associativity |}
  ; Monoid.identity := Int8.addition.identity |}.

Instance Int8_mul_monoid
  : Monoid Int8.mul Int8.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Int8.multiplication.associativity |}
  ; Monoid.identity := Int8.multiplication.identity |}.

Instance Int8_add_commutative
  : Commutative Int8.add :=
  {| Commutative.commutativity := Int8.addition.commutativity |}.

Instance Int8_mul_commutative
  : Commutative Int8.mul :=
  {| Commutative.commutativity := Int8.multiplication.commutativity |}.

Instance Int8_add_group
  : Group Int8.add Int8.Zero Int8.negate :=
  {| Group.monoid := Int8_add_monoid
  ; Group.inverse := Int8.addition.inverse |}.

Instance Int8_add_abelian_group
  : AbelianGroup Int8.add Int8.Zero Int8.negate :=
  {| AbelianGroup.group := Int8_add_group
  ; AbelianGroup.commutative := Int8_add_commutative |}.

Instance Int8_ring
  : Ring Int8.add Int8.Zero Int8.negate Int8.mul Int8.One :=
  {| Ring.abelian_group := Int8_add_abelian_group
  ; Ring.monoid := Int8_mul_monoid
  ; Ring.distributivity := Int8.multiplication.distributivity.over.addition |}.
