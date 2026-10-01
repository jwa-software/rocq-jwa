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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* An unsigned integer of eight bits: a [Byte] read as a number from 0 to
 * 255 (2^8 - 1), its arithmetic wrapping modulo 256 (2^8). In this file
 * [100000000] is 2^8, written in binary digits.
 *)

Module UInt8. (* UInt8 *)

Inductive T : Type :=
  | UInt8_introduction : Byte -> T.

Abbreviation UInt8 := T.

(* The number of values, 256 (2^8), the arithmetic wrapping modulo it. *)
(* [BinBase] *)
Definition modulus := 100000000%bin_base.

(* [UInt8 -> Byte] *)
Definition to_byte := fun (x : UInt8) .
  match x with
  | UInt8_introduction b => b
  end.

(* [Byte -> UInt8] *)
Definition from_byte := fun (b : Byte) . UInt8_introduction b.

(* The bits read as a number in base two, the most significant first; [10]
 * is two in binary digits.
 *)
(* [UInt8 -> BinWithZero] *)
Definition to_bin_with_zero := fun (x : UInt8) .
  match x with
  | UInt8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (10 * (10 * (10 * (10 * (10 * (10 * (10 * Bit.to_bin_with_zero x7
        + Bit.to_bin_with_zero x6) + Bit.to_bin_with_zero x5) + Bit.to_bin_with_zero x4)
        + Bit.to_bin_with_zero x3) + Bit.to_bin_with_zero x2) + Bit.to_bin_with_zero x1)
        + Bit.to_bin_with_zero x0)%bin_with_zero
  end.

(* From here to the end of the module a [UInt8] stands where a [BinWithZero] is
 * expected, read as its value; the conversion is printed.
 *)
Local Coercion to_bin_with_zero : T >-> BinWithZero.
Add Printing Coercion to_bin_with_zero.

(* The value as a [Bin], through [to_bin_with_zero]. *)
(* [UInt8 -> Bin] *)
Definition to_bin := fun (x : UInt8) . Bin.from_bin_with_zero (to_bin_with_zero x).

(* The value in [Nat0], through [to_bin_with_zero]; [Nat0] is unary, so it is
 * for stating and proving, and computing goes through [to_bin_with_zero].
 *)
(* [UInt8 -> Nat0] *)
Definition to_nat0 := fun (x : UInt8) . BinWithZero.to_nat0 (to_bin_with_zero x).

(* [UInt8] *)
Definition Zero := UInt8_introduction Byte.Zero.

(* [UInt8] *)
Definition One :=
  UInt8_introduction
    (Byte.Byte_introduction
      Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One).

(* [UInt8 -> Nat0 -> UInt8] *)
Definition shift_left := fun (x : UInt8) (k : Nat0) .
  match x with
  | UInt8_introduction b => UInt8_introduction (Byte.shift_left b k)
  end.

(* [UInt8 -> Nat0 -> UInt8] *)
Definition shift_right := fun (x : UInt8) (k : Nat0) .
  match x with
  | UInt8_introduction b => UInt8_introduction (Byte.shift_right b k)
  end.

(* [x] with [b] written after its lowest bit, the highest bit dropped. *)
(* [Bit -> UInt8 -> UInt8] *)
Definition append_bit := fun (b : Bit) (x : UInt8) .
  match x with
  | UInt8_introduction (Byte.Byte_introduction _ x6 x5 x4 x3 x2 x1 x0) =>
      UInt8_introduction (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 b)
  end.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place.
 *)
(* [Bit -> UInt8 -> UInt8 -> Product Bit UInt8] *)
Definition add_with_carry := fun (carry : Bit) (x : UInt8) (y : UInt8) .
  match x with
  | UInt8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          (pi_1 r7,
            UInt8_introduction
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt8 -> UInt8 -> UInt8] *)
Definition add := fun (x : UInt8) (y : UInt8) . (pi_2 (add_with_carry Bit.Zero x y))%product.

(* [only parsing] keeps goals printing the operations by name. *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_uint8_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> UInt8 -> UInt8 -> Product Bit UInt8] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : UInt8) (y : UInt8) .
  match x with
  | UInt8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      match y with
      | UInt8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          (pi_1 r7,
            UInt8_introduction
              (Byte.Byte_introduction
                (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
                (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0)))
      end
  end%product.

(* [UInt8 -> UInt8 -> UInt8] *)
Definition sub := fun (x : UInt8) (y : UInt8) . (pi_2 (sub_with_borrow Bit.Zero x y))%product.

(* The two's complement: [x] taken from [Zero], wrapping. *)
(* [UInt8 -> UInt8] *)
Definition negate := fun (x : UInt8) . sub Zero x.

Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_uint8_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 256.
 *)
(* [UInt8 -> UInt8 -> UInt8] *)
Definition mul := fun (x : UInt8) (y : UInt8) .
  let step := fun (p : UInt8) (b : Bit) .
    add (shift_left p 1%n0)
      match b with
      | Bit.Zero => Zero
      | Bit.One  => x
      end in
  match y with
  | UInt8_introduction (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      step (step (step (step (step (step (step (step Zero y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_uint8_scope.

(* [p] modulo 256, its bits appended from the most significant. *)
(* [BinBase -> UInt8] *)
Fixpoint from_bin_base (p : BinBase) : UInt8 :=
  match p with
  | BinBase.One   => One
  | BinBase.b0 p' => append_bit Bit.Zero (from_bin_base p')
  | BinBase.b1 p' => append_bit Bit.One (from_bin_base p')
  end.

(* [BinWithZero -> UInt8] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n with
  | BinWithZero.Zero       => Zero
  | BinWithZero.Positive p => from_bin_base p
  end.

(* [Nat -> UInt8] *)
Definition from_nat := fun (n : Nat) . from_bin_base (BinBase.from_nat n).

(* [Nat0 -> UInt8] *)
Definition from_nat0 := fun (n : Nat0) . from_bin_with_zero (BinWithZero.from_nat0 n).

(* [UInt8 -> UInt8 -> Prop] *)
Definition LessThan := fun (x : UInt8) (y : UInt8) .
  (to_bin_with_zero x < to_bin_with_zero y)%bin_with_zero.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_uint8_scope.

(* [UInt8 -> UInt8 -> Prop] *)
Definition LessOrEqual := fun (x : UInt8) (y : UInt8) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_uint8_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_uint8_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_uint8_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_uint8_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_uint8_scope.

(* [UInt8 -> UInt8 -> Comparison] *)
Definition compare := fun (x : UInt8) (y : UInt8) .
  BinWithZero.compare (to_bin_with_zero x) (to_bin_with_zero y).

(* [UInt8 -> UInt8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [UInt8 -> UInt8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [UInt8 -> UInt8 -> UInt8] *)
Abbreviation min := (Comparable.min compare).

(* [UInt8 -> UInt8 -> UInt8] *)
Abbreviation max := (Comparable.max compare).

(* A literal of 0 to 255, in decimal or hexadecimal, read in binary; any
 * larger is refused.
 *)
(* [Numeral.Unsigned -> Option UInt8] *)
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
(* [UInt8 -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : UInt8) .
  Numeral.Unsigned.Decimal (BinWithZero.to_decimal (to_bin_with_zero x)).

Local Open Scope jwa_uint8_scope.

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
Theorem boundedness : forall (x : UInt8) . (x < modulus)%bin_with_zero.
Proof.
  intros x.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl to_bin_with_zero in |- *.
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

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : UInt8} {y : UInt8} . to_bin_with_zero x = to_bin_with_zero y -> x = y.
Proof.
  intros x y e.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_bin_with_zero in &e.
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
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : UInt8) (y : UInt8) .
      (Bit.to_bin_with_zero carry + x + y
        = modulus * Bit.to_bin_with_zero (pi_1 (add_with_carry carry x y))%product
          + (pi_2 (add_with_carry carry x y))%product)%bin_with_zero.
Proof.
  intros carry x y.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_bin_with_zero, add_with_carry in |- *.
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

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : UInt8) (y : UInt8) .
      (x + modulus * Bit.to_bin_with_zero (pi_1 (sub_with_borrow borrow x y))%product
        = y + Bit.to_bin_with_zero borrow
          + (pi_2 (sub_with_borrow borrow x y))%product)%bin_with_zero.
Proof.
  intros borrow x y.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_bin_with_zero, sub_with_borrow in |- *.
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

(* conversion.addition *)
Theorem addition
  : forall (x : UInt8) (y : UInt8) .
      (to_bin_with_zero (x + y)%uint8 = (x + y) %. modulus)%bin_with_zero.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_bin_with_zero (pi_1 (add_with_carry Bit.Zero &x &y))%product * modulus
        + to_bin_with_zero (&x + &y)%uint8
        = to_bin_with_zero &x + to_bin_with_zero &y
      /\ to_bin_with_zero (&x + &y)%uint8 < modulus)%bin_with_zero.
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
          (to_bin_with_zero (&x + &y)%uint8)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : UInt8) (y : UInt8) .
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
  : forall (x : UInt8) .
      (((- x)%uint8 + x) %. modulus = 0)%bin_with_zero.
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
  : forall (b : Bit) (x : UInt8) .
      (to_bin_with_zero (append_bit b x)
        = (10 * x + Bit.to_bin_with_zero b) %. modulus)%bin_with_zero.
Proof.
  intros b x.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  lemma witness
    : (Bit.to_bin_with_zero &x7 * modulus
        + to_bin_with_zero
            (append_bit &b
              (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
        = 10
            * to_bin_with_zero
                (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
          + Bit.to_bin_with_zero &b
      /\ to_bin_with_zero
          (append_bit &b
            (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))
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
                          &top))))))))).
    - ipso
        (conversion.boundedness
          (append_bit &b
            (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0)))).
  }
  match (BinWithZero.division.uniqueness
          (10 * to_bin_with_zero
                  (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            + Bit.to_bin_with_zero &b)%bin_with_zero
          modulus
          (Bit.to_bin_with_zero &x7)
          (to_bin_with_zero
            (append_bit &b
              (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))))
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
Theorem section : forall (x : UInt8) . from_bin_with_zero (to_bin_with_zero x) = x.
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
  : forall (x : UInt8) .
      (to_bin_with_zero (shift_left x 1%n0) = (10 * x) %. modulus)%bin_with_zero.
Proof.
  intros x.
  lemma appended : shift_left &x 1%n0 = append_bit Bit.Zero &x.
  {
    match &x with | UInt8_introduction xb end.
    match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
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
  : forall (x : UInt8) (k : Nat0) .
      (to_bin_with_zero (shift_left x k) = BinWithZero.shift_left x k %. modulus)%bin_with_zero.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_left &x 0%n0 = &x.
    {
      match &x with | UInt8_introduction xb end.
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
        match &x with | UInt8_introduction xb end.
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
  : forall (x : UInt8) .
      to_bin_with_zero (shift_right x 1%n0) = BinWithZero.halve x.
Proof.
  intros x.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  ipso
    (symm
      (Bit.conversion.binary.halving
        (to_bin_with_zero
          (shift_right
            (UInt8_introduction (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
            1%n0))
        &x0)).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : UInt8) (k : Nat0) .
      to_bin_with_zero (shift_right x k) = BinWithZero.shift_right x k.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - lemma unchanged : shift_right &x 0%n0 = &x.
    {
      match &x with | UInt8_introduction xb end.
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
        match &x with | UInt8_introduction xb end.
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
  : forall (x : UInt8) (p : UInt8) (h : BinWithZero) (b : Bit) .
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
  : forall (x : UInt8) (y : UInt8) .
      (to_bin_with_zero (x * y)%uint8 = (x * y) %. modulus)%bin_with_zero.
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
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl mul in |- *.
  ipso
    (conversion.multiplication.step _ _ _ _
      (conversion.multiplication.step _ _ _ _
        (conversion.multiplication.step _ _ _ _
          (conversion.multiplication.step _ _ _ _
            (conversion.multiplication.step _ _ _ _
              (conversion.multiplication.step _ _ _ _
                (conversion.multiplication.step _ _ _ _
                  (conversion.multiplication.step _ _ _ _ &base)))))))).
Qed.

Module byte. (* conversion.byte *)

(* conversion.byte.retraction *)
Theorem retraction : forall (b : Byte) . to_byte (from_byte b) = b.
Proof.
  intros b.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

(* conversion.byte.section *)
Theorem section : forall (x : UInt8) . from_byte (to_byte x) = x.
Proof.
  intros x.
  match &x with | UInt8_introduction b end.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

End byte. (* conversion.byte *)

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : UInt8) (y : UInt8) (z : UInt8) . (x + y) + z = x + (y + z).
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
Theorem commutativity : forall (x : UInt8) (y : UInt8) . x + y = y + x.
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
Theorem identity : forall (x : UInt8) . (Zero + x = x) /\ (x + Zero = x).
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
Theorem inverse : forall (x : UInt8) . (- x + x = Zero) /\ (x + - x = Zero).
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
  : forall (x : UInt8) (y : UInt8) (z : UInt8) . (x * y) * z = x * (y * z).
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
Theorem commutativity : forall (x : UInt8) (y : UInt8) . x * y = y * x.
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
Theorem identity : forall (x : UInt8) . (One * x = x) /\ (x * One = x).
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
  : forall (x : UInt8) (y : UInt8) (z : UInt8) . x * (y + z) = (x * y) + (x * z).
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
  : forall (x : UInt8) (y : UInt8) (z : UInt8) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : UInt8) (y : UInt8) (z : UInt8) .
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
  : forall {x : UInt8} {y : UInt8} {z : UInt8} . x < y -> y < z -> x < z.
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
  : forall (x : UInt8) (y : UInt8) .
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
  : forall (x : UInt8) (y : UInt8) . compare x y = Comparison.transpose (compare y x).
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

End UInt8. (* UInt8 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [UInt8], not [UInt8.T].
 *)
Abbreviation UInt8 := UInt8.T.

(* Makes the notations declared in [Module UInt8] usable in every file that
 * imports this one, as [(x + y)%uint8] or under an opened [jwa_uint8_scope].
 *)
Export (notations) UInt8.

(* A number of the type is written in decimal or hexadecimal under its
 * scope, [200%uint8] or [0xFF%uint8], and a closed one prints in decimal.
 *)
Number Notation UInt8.T UInt8.from_numeral UInt8.to_numeral
  : jwa_uint8_scope.

(* Where a [UInt8] is expected, a literal or a notation reads in this scope
 * without its [%uint8].
 *)
Bind Scope jwa_uint8_scope with UInt8.T.

(* A [UInt8] stands wherever a [BinWithZero] is expected, read as its value,
 * and wherever a [Nat0] is, through that value; each conversion is printed
 * where it happened.
 *)
Coercion UInt8.to_bin_with_zero : UInt8 >-> BinWithZero.
Add Printing Coercion UInt8.to_bin_with_zero.
Coercion UInt8.to_nat0 : UInt8 >-> Nat0.
Add Printing Coercion UInt8.to_nat0.

Instance UInt8_add_monoid
  : Monoid UInt8.add UInt8.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt8.addition.associativity |}
  ; Monoid.identity := UInt8.addition.identity |}.

Instance UInt8_mul_monoid
  : Monoid UInt8.mul UInt8.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := UInt8.multiplication.associativity |}
  ; Monoid.identity := UInt8.multiplication.identity |}.

Instance UInt8_add_commutative
  : Commutative UInt8.add :=
  {| Commutative.commutativity := UInt8.addition.commutativity |}.

Instance UInt8_mul_commutative
  : Commutative UInt8.mul :=
  {| Commutative.commutativity := UInt8.multiplication.commutativity |}.

Instance UInt8_add_group
  : Group UInt8.add UInt8.Zero UInt8.negate :=
  {| Group.monoid := UInt8_add_monoid
  ; Group.inverse := UInt8.addition.inverse |}.

Instance UInt8_add_abelian_group
  : AbelianGroup UInt8.add UInt8.Zero UInt8.negate :=
  {| AbelianGroup.group := UInt8_add_group
  ; AbelianGroup.commutative := UInt8_add_commutative |}.

Instance UInt8_ring
  : Ring UInt8.add UInt8.Zero UInt8.negate UInt8.mul UInt8.One :=
  {| Ring.abelian_group := UInt8_add_abelian_group
  ; Ring.monoid := UInt8_mul_monoid
  ; Ring.distributivity := UInt8.multiplication.distributivity.over.addition |}.
