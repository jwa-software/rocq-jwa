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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* An unsigned integer of sixteen bits: two [Byte]s read as a number from 0 to
 * 65535 (2^16 - 1), its arithmetic wrapping modulo 65536 (2^16). In this file
 * [10000000000000000] is 2^16, written in binary digits.
 *)

Module UInt16. (* UInt16 *)

Inductive T : Type :=
  | UInt16_introduction : Byte -> Byte -> T.

Abbreviation UInt16 := T.

(* The number of values, the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 10000000000000000%bin_base.

(* [x] laid out as a [HWord] in the order [e] names. *)
(* [Endian -> UInt16 -> HWord] *)
Definition to_hword := fun (e : Endian) (x : UInt16) .
  match x with
  | UInt16_introduction b1 b0 => HWord.make e b0 b1
  end.

(* The value of the bytes of [w], whatever the order they are laid out in. *)
(* [HWord -> UInt16] *)
Definition from_hword := fun (w : HWord) . UInt16_introduction (HWord.high w) (HWord.low w).

(* The bits read as a number in base two, the most significant first; [10]
 * is two in binary digits.
 *)
(* [UInt16 -> BinWithZero] *)
Definition to_bin_with_zero := fun (x : UInt16) .
  match x with
  | UInt16_introduction (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (10 * (
        10 * Bit.to_bin_with_zero x15 + Bit.to_bin_with_zero x14) + Bit.to_bin_with_zero x13)
        + Bit.to_bin_with_zero x12) + Bit.to_bin_with_zero x11) + Bit.to_bin_with_zero x10)
        + Bit.to_bin_with_zero x9) + Bit.to_bin_with_zero x8) + Bit.to_bin_with_zero x7)
        + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5) + Bit.to_bin_with_zero x4)
        + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2) + Bit.to_bin_with_zero x1)
        + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* From here to the end of the module a [UInt16] stands where a [BinWithZero] is
 * expected, read as its value; the conversion is printed.
 *)
Local Coercion to_bin_with_zero : T >-> BinWithZero.
Add Printing Coercion to_bin_with_zero.

(* The value as a [Bin], through [to_bin_with_zero]. *)
(* [UInt16 -> Bin] *)
Definition to_bin := fun (x : UInt16) . Bin.from_bin_with_zero (to_bin_with_zero x).

(* The value in [Nat0], through [to_bin_with_zero]; [Nat0] is unary, so it is
 * for stating and proving, and computing goes through [to_bin_with_zero].
 *)
(* [UInt16 -> Nat0] *)
Definition to_nat0 := fun (x : UInt16) . BinWithZero.to_nat0 (to_bin_with_zero x).

(* [UInt16] *)
Definition Zero := UInt16_introduction Byte.Zero Byte.Zero.

(* [UInt16] *)
Definition One :=
  UInt16_introduction
    Byte.Zero
    (Byte.Byte_introduction
      Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One).

(* [k] places toward the most significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [UInt16 -> Nat -> UInt16] *)
Fixpoint shift_left_nat (x : UInt16) (k : Nat) : UInt16 :=
  let y :=
    match x with
    | UInt16_introduction (Byte.Byte_introduction _ x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        UInt16_introduction (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [UInt16 -> Nat0 -> UInt16] *)
Definition shift_left := fun (x : UInt16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [k] places toward the least significant end, a 0 coming in at the
 * other; one place first, then [k - 1].
 *)
(* [UInt16 -> Nat -> UInt16] *)
Fixpoint shift_right_nat (x : UInt16) (k : Nat) : UInt16 :=
  let y :=
    match x with
    | UInt16_introduction (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 _) =>
        UInt16_introduction (Byte.Byte_introduction Bit.Zero x15 x14 x13 x12 x11 x10 x9)
          (Byte.Byte_introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [UInt16 -> Nat0 -> UInt16] *)
Definition shift_right := fun (x : UInt16) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> UInt16 -> UInt16] *)
Definition append_bit := fun (b : Bit) (x : UInt16) .
  match x with
  | UInt16_introduction (Byte.Byte_introduction _ x14 x13 x12 x11 x10 x9 x8)
      (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      UInt16_introduction (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
        (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> UInt16 -> UInt16 -> Product Bit UInt16] *)
Definition add_with_carry := fun (carry : Bit) (x : UInt16) (y : UInt16) .
  match x with
  | UInt16_introduction (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt16_introduction (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
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
            UInt16_introduction
              (Byte.Byte_introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt16 -> UInt16 -> UInt16] *)
Definition add := fun (x : UInt16) (y : UInt16) . (pi_2 (add_with_carry Bit.Zero x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_uint16_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> UInt16 -> UInt16 -> Product Bit UInt16] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : UInt16) (y : UInt16) .
  match x with
  | UInt16_introduction (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
      (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt16_introduction (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
          (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
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
            UInt16_introduction
              (Byte.Byte_introduction
                (pi_2 r15) (pi_2 r14) (pi_2 r13) (pi_2 r12)
                (pi_2 r11) (pi_2 r10) (pi_2 r9) (pi_2 r8))
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt16 -> UInt16 -> UInt16] *)
Definition sub := fun (x : UInt16) (y : UInt16) . (pi_2 (sub_with_borrow Bit.Zero x y))%product.

(* The two's complement: [x] taken from [Zero], wrapping. *)
(* [UInt16 -> UInt16] *)
Definition negate := fun (x : UInt16) . sub Zero x.

Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_uint16_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 65536.
 *)
(* [UInt16 -> UInt16 -> UInt16] *)
Definition mul := fun (x : UInt16) (y : UInt16) .
  let step := fun (p : UInt16) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | Bit.Zero => Zero
      | Bit.One  => x
      end in
  match y with
  | UInt16_introduction (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step (step (step (step (step (step (step (step (step
        Zero y15) y14) y13) y12) y11) y10) y9) y8) y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_uint16_scope.

(* [p] modulo 65536, its bits appended from the most significant. *)
(* [BinBase -> UInt16] *)
Fixpoint from_bin_base (p : BinBase) : UInt16 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit Bit.Zero (from_bin_base p')
  | BinBase.b1 p' => append_bit Bit.One (from_bin_base p')
  end.

(* [BinWithZero -> UInt16] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> UInt16] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> UInt16] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [UInt16 -> UInt16 -> Prop] *)
Definition LessThan := fun (x : UInt16) (y : UInt16) .
  (to_bin_with_zero x < to_bin_with_zero y)%bin_with_zero.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_uint16_scope.

(* [UInt16 -> UInt16 -> Prop] *)
Definition LessOrEqual := fun (x : UInt16) (y : UInt16) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_uint16_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_uint16_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_uint16_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_uint16_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_uint16_scope.

(* [UInt16 -> UInt16 -> Comparison] *)
Definition compare := fun (x : UInt16) (y : UInt16) .
  BinWithZero.compare (to_bin_with_zero x) (to_bin_with_zero y).

(* [UInt16 -> UInt16 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [UInt16 -> UInt16 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [UInt16 -> UInt16 -> UInt16] *)
Abbreviation min := (Comparable.min compare).

(* [UInt16 -> UInt16 -> UInt16] *)
Abbreviation max := (Comparable.max compare).

(* A literal of 0 to 65535, in decimal or hexadecimal, read in binary; any
 * larger is refused.
 *)
(* [Numeral.Unsigned -> Option UInt16] *)
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
(* [UInt16 -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : UInt16) .
  Numeral.Unsigned.Decimal (BinWithZero.to_decimal (to_bin_with_zero x)).

Local Open Scope jwa_uint16_scope.

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
Theorem boundedness : forall (x : UInt16) . (x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
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
    (Bit.conversion.binary.boundedness &x15)))))))))))))))).
Qed.

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : UInt16} {y : UInt16} . to_bin_with_zero x = to_bin_with_zero y -> x = y.
Proof.
  intros x y e.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt16_introduction yb1 yb0 end.
  match &yb1 with | Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : UInt16) (y : UInt16) .
      (Bit.to_bin_with_zero carry + x + y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt16_introduction yb1 yb0 end.
  match &yb1 with | Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
    (Bit.conversion.binary.carry _ &x15 &y15)))))))))))))))).
Qed.

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : UInt16) (y : UInt16) .
      (x + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = y + Bit.to_bin_with_zero borrow
          + (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt16_introduction yb1 yb0 end.
  match &yb1 with | Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
    (Bit.conversion.binary.borrow _ &x15 &y15)))))))))))))))).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : UInt16) (y : UInt16) .
      (to_bin_with_zero (x + y)%uint16 = (x + y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product * modulus
        + to_bin_with_zero (&x + &y)%uint16
        = to_bin_with_zero &x + to_bin_with_zero &y
      /\ to_bin_with_zero (&x + &y)%uint16 < modulus)%bin_with_zero.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (BinWithZero.multiplication.commutativity
          (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          modulus),
        <- (conversion.carry Bit.Zero &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (conversion.boundedness (&x + &y)).
  }
  match (BinWithZero.division.uniqueness
          (to_bin_with_zero &x + to_bin_with_zero &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          (to_bin_with_zero (&x + &y)%uint16)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : UInt16) (y : UInt16) .
      ((sub x y + y) %. modulus = x)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product * modulus
        + to_bin_with_zero &x
        = to_bin_with_zero (sub &x &y) + to_bin_with_zero &y
      /\ to_bin_with_zero &x < modulus)%bin_with_zero.
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
          (to_bin_with_zero &x)),
        (conversion.borrow Bit.Zero &x &y),
        (BinWithZero.addition.commutativity
          (to_bin_with_zero &y) (Bit.to_bin_with_zero Bit.Zero))
        in |- *.
      simpl in |- *.
      leibniz
        (BinWithZero.addition.commutativity
          (to_bin_with_zero &y)
          (to_bin_with_zero (pi_2 (sub_with_borrow Bit.Zero &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (conversion.boundedness &x).
  }
  match (BinWithZero.division.uniqueness
          (to_bin_with_zero (sub &x &y) + to_bin_with_zero &y)%bin_with_zero modulus
          (Bit.to_bin_with_zero (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)
          (to_bin_with_zero &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : UInt16) .
      (((- x)%uint16 + x) %. modulus = 0)%bin_with_zero.
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
  : forall (b : Bit) (x : UInt16) .
      (to_bin_with_zero (append_bit b x)
        = (10 * x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x15 * modulus
        + to_bin_with_zero
            (append_bit &b
              (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * to_bin_with_zero
                (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                  (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ to_bin_with_zero
          (append_bit &b
            (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
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
          &top))))))))))))))))).
    - ipso
        (conversion.boundedness
          (append_bit &b
            (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * to_bin_with_zero
                  (UInt16_introduction
                    (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                    (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x15)
          (to_bin_with_zero
            (append_bit &b
              (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
                (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
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
        : from_bin_base (BinBase.b0 &p') = append_bit Bit.Zero (from_bin_base &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (conversion.appending Bit.Zero (from_bin_base &p')),
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
        (conversion.appending Bit.One (from_bin_base &p')),
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

(* conversion.section *)
Theorem section : forall (x : UInt16) . from_bin_with_zero (to_bin_with_zero x) = x.
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
  : forall (x : UInt16) .
      (to_bin_with_zero (shift_left x 1%n0) = (10 * x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit Bit.Zero &x.
  {
    match &x with | UInt16_introduction xb1 xb0 end.
    match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
    match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  }
  match (BinWithZero.addition.identity (10 * to_bin_with_zero &x)%bin_with_zero)
  with | _ sum end.
  leibniz &appended, (conversion.appending Bit.Zero &x) in |- *.
  simpl Bit.to_bin_with_zero in |- *.
  leibniz &sum in |- *.
  quod idem est.
Qed.

(* conversion.left.shift *)
Theorem shift
  : forall (x : UInt16) (k : Nat0) .
      (to_bin_with_zero (shift_left x k) = BinWithZero.shift_left x k %. modulus)%bin_with_zero.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_left &x 0%n0 = &x.
    {
      match &x with | UInt16_introduction xb1 xb0 end.
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
        match &x with | UInt16_introduction xb1 xb0 end.
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
  : forall (x : UInt16) .
      to_bin_with_zero (shift_right x 1%n0) = BinWithZero.halve x.
Proof.
  intros x.
  match &x with | UInt16_introduction xb1 xb0 end.
  match &xb1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
  match &xb0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  ipso
    (symm
      (Bit.conversion.binary.halving
        (to_bin_with_zero
          (shift_right
            (UInt16_introduction (Byte.Byte_introduction &x15 &x14 &x13 &x12 &x11 &x10 &x9 &x8)
              (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            1%n0))
        &x0)).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : UInt16) (k : Nat0) .
      to_bin_with_zero (shift_right x k) = BinWithZero.shift_right x k.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_right &x 0%n0 = &x.
    {
      match &x with | UInt16_introduction xb1 xb0 end.
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
        match &x with | UInt16_introduction xb1 xb0 end.
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
  : forall (x : UInt16) (p : UInt16) (h : BinWithZero) (b : Bit) .
      (to_bin_with_zero p = (x * h) %. modulus)%bin_with_zero ->
      to_bin_with_zero
        (add (shift_left p 1%n0)
          match b with
          | Bit.Zero => Zero
          | Bit.One  => x
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
        = ((to_bin_with_zero &x * (10 * &h + Bit.to_bin_with_zero Bit.Zero))
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
        = ((to_bin_with_zero &x * (10 * &h + Bit.to_bin_with_zero Bit.One))
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
  : forall (x : UInt16) (y : UInt16) .
      (to_bin_with_zero (x * y)%uint16 = (x * y) %. modulus)%bin_with_zero.
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
  match &y with | UInt16_introduction yb1 yb0 end.
  match &yb1 with | Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8 end.
  match &yb0 with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
    (conversion.multiplication.step _ _ _ _ &base)))))))))))))))).
Qed.

Module hword. (* conversion.hword *)

(* conversion.hword.retraction *)
Theorem retraction : forall (e : Endian) (x : UInt16) . from_hword (to_hword e x) = x.
Proof.
  intros e x.
  match &x with | UInt16_introduction b1 b0 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.hword.section *)
Theorem section : forall (w : HWord) . to_hword (HWord.endian w) (from_hword w) = w.
Proof.
  intros w.
  match &w with | HWord_introduction e b0 b1 end.
  match &e with | Little | Big end;
    simpl from_hword, to_hword in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End hword. (* conversion.hword *)

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : UInt16) (y : UInt16) (z : UInt16) . (x + y) + z = x + (y + z).
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
Theorem commutativity : forall (x : UInt16) (y : UInt16) . x + y = y + x.
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
Theorem identity : forall (x : UInt16) . (Zero + x = x) /\ (x + Zero = x).
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
Theorem inverse : forall (x : UInt16) . (- x + x = Zero) /\ (x + - x = Zero).
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
  : forall (x : UInt16) (y : UInt16) (z : UInt16) . (x * y) * z = x * (y * z).
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
Theorem commutativity : forall (x : UInt16) (y : UInt16) . x * y = y * x.
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
Theorem identity : forall (x : UInt16) . (One * x = x) /\ (x * One = x).
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
  : forall (x : UInt16) (y : UInt16) (z : UInt16) . x * (y + z) = (x * y) + (x * z).
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
  : forall (x : UInt16) (y : UInt16) (z : UInt16) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : UInt16) (y : UInt16) (z : UInt16) .
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
  : forall {x : UInt16} {y : UInt16} {z : UInt16} . x < y -> y < z -> x < z.
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
  : forall (x : UInt16) (y : UInt16) .
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
  : forall (x : UInt16) (y : UInt16) . compare x y = Comparison.transpose (compare y x).
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

End UInt16. (* UInt16 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [UInt16], not [UInt16.T].
 *)
Abbreviation UInt16 := UInt16.T.

(* Makes the notations declared in [Module UInt16] usable in every file that
 * imports this one, as [(x + y)%uint16] or under an opened [jwa_uint16_scope].
 *)
Export (notations) UInt16.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [200%uint16] or [0xFF%uint16], and a closed one prints in decimal.
 *)
Number Notation UInt16.T UInt16.from_numeral UInt16.to_numeral
  : jwa_uint16_scope.

(* Where a [UInt16] is expected, a literal or a notation reads in this scope
 * without its [%uint16].
 *)
Bind Scope jwa_uint16_scope with UInt16.T.

(* A [UInt16] stands wherever a [BinWithZero] is expected, read as its value,
 * and wherever a [Nat0] is, through that value; each conversion is printed
 * where it happened.
 *)
Coercion UInt16.to_bin_with_zero : UInt16 >-> BinWithZero.
Add Printing Coercion UInt16.to_bin_with_zero.
Coercion UInt16.to_nat0 : UInt16 >-> Nat0.
Add Printing Coercion UInt16.to_nat0.

Instance UInt16_add_monoid
  : Monoid UInt16.add UInt16.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt16.addition.associativity |}
  ; Monoid.identity := UInt16.addition.identity |}.

Instance UInt16_mul_monoid
  : Monoid UInt16.mul UInt16.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt16.multiplication.associativity |}
  ; Monoid.identity := UInt16.multiplication.identity |}.

Instance UInt16_add_commutative
  : Commutative UInt16.add :=
  {| Commutative.commutativity := UInt16.addition.commutativity |}.

Instance UInt16_mul_commutative
  : Commutative UInt16.mul :=
  {| Commutative.commutativity := UInt16.multiplication.commutativity |}.

Instance UInt16_add_group
  : Group UInt16.add UInt16.Zero UInt16.negate :=
  {| Group.monoid := UInt16_add_monoid
  ; Group.inverse := UInt16.addition.inverse |}.

Instance UInt16_add_abelian_group
  : AbelianGroup UInt16.add UInt16.Zero UInt16.negate :=
  {| AbelianGroup.group := UInt16_add_group
  ; AbelianGroup.commutative := UInt16_add_commutative |}.

Instance UInt16_ring
  : Ring UInt16.add UInt16.Zero UInt16.negate UInt16.mul UInt16.One :=
  {| Ring.abelian_group := UInt16_add_abelian_group
  ; Ring.monoid := UInt16_mul_monoid
  ; Ring.distributivity := UInt16.multiplication.distributivity.over.addition |}.
