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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* An unsigned integer of eight bits: a [Byte] read as a number from 0 to
 * 255, its arithmetic wrapping modulo 256.
 *)

Module UInt8. (* UInt8 *)

Inductive T : Type :=
  | UInt8_introduction : Byte -> T.

Abbreviation UInt8 := T.

(* The bits read as a number in base two, the most significant first. *)
(* [UInt8 -> Nat0] *)
Definition to_nat0 := fun (x : UInt8) .
  match x with
  | UInt8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (2 * (2 * (2 * (2 * (2 * (2 * (2 * Bit.to_nat0 x7 + Bit.to_nat0 x6)
        + Bit.to_nat0 x5) + Bit.to_nat0 x4) + Bit.to_nat0 x3) + Bit.to_nat0 x2)
        + Bit.to_nat0 x1) + Bit.to_nat0 x0)%n0
  end.

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

(* [n] modulo 256, counted up from [One]. *)
(* [Nat -> UInt8] *)
Fixpoint from_nat (n : Nat) : UInt8 :=
  match n with
  | Nat.One          => One
  | Nat.Successor n' => add (from_nat n') One
  end.

(* [Nat0 -> UInt8] *)
Definition from_nat0 := fun (n : Nat0) .
  match n with
  | Nat0.Zero       => Zero
  | Nat0.Positive p => from_nat p
  end.

(* [UInt8 -> UInt8 -> Prop] *)
Definition LessThan := fun (x : UInt8) (y : UInt8) . (to_nat0 x < to_nat0 y)%n0.

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
Definition compare := fun (x : UInt8) (y : UInt8) . Nat0.compare (to_nat0 x) (to_nat0 y).

(* [UInt8 -> UInt8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [UInt8 -> UInt8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [UInt8 -> UInt8 -> UInt8] *)
Abbreviation min := (Comparable.min compare).

(* [UInt8 -> UInt8 -> UInt8] *)
Abbreviation max := (Comparable.max compare).

(* [n] followed by the digit [d] in base [base], [None] once the value
 * passes 255 and from then on, so that a literal of any length is refused
 * without its value being built.
 *)
(* [Nat0 -> Option Nat0 -> Option Nat -> Option Nat0] *)
Definition append_digit := fun (base : Nat0) (n : Option Nat0) (d : Option Nat) .
  match n with
  | None   => None
  | Some m =>
      let v :=
        (m * base
          + match d with
            | Some k => Nat0.Positive k
            | None   => 0
            end)%n0 in
      match Nat0.compare v 256%n0 with
      | Comparison.Lt => Some v
      | Comparison.Eq => None
      | Comparison.Gt => None
      end
  end.

(* [n] with the decimal digits [d] appended, most significant first. *)
(* [Option Nat0 -> Numeral.Decimal.Digits -> Option Nat0] *)
Fixpoint from_decimal (n : Option Nat0) (d : Numeral.Decimal.Digits) : Option Nat0 :=
  match d with
  | Numeral.Decimal.Digits.End      => n
  | Numeral.Decimal.Digits.Zero d'  => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.One d'   => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Two d'   => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Three d' => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Four d'  => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Five d'  => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Six d'   => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Seven d' => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Eight d' => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Nine d'  => from_decimal (append_digit 10%n0 n (Nat.decimal_value d)) d'
  end.

(* [n] with the hexadecimal digits [h] appended, most significant first. *)
(* [Option Nat0 -> Numeral.Hexadecimal.Digits -> Option Nat0] *)
Fixpoint from_hexadecimal (n : Option Nat0) (h : Numeral.Hexadecimal.Digits) : Option Nat0 :=
  match h with
  | Numeral.Hexadecimal.Digits.End         => n
  | Numeral.Hexadecimal.Digits.Zero h'     =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.One h'      =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Two h'      =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Three h'    =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Four h'     =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Five h'     =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Six h'      =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Seven h'    =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Eight h'    =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Nine h'     =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Ten h'      =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Eleven h'   =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Twelve h'   =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Thirteen h' =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Fourteen h' =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Fifteen h'  =>
      from_hexadecimal (append_digit 16%n0 n (Nat.hexadecimal_value h)) h'
  end.

(* A literal of 0 to 255, in decimal or hexadecimal; any larger is refused. *)
(* [Numeral.Unsigned -> Option UInt8] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  let value :=
    match u with
    | Numeral.Unsigned.Decimal d     => from_decimal (Some 0%n0) d
    | Numeral.Unsigned.Hexadecimal h => from_hexadecimal (Some 0%n0) h
    end in
  match value with
  | Some v => Some (from_nat0 v)
  | None   => None
  end.

(* [x] as a literal, in decimal. *)
(* [UInt8 -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : UInt8) . Nat0.to_numeral (to_nat0 x).

Local Open Scope jwa_uint8_scope.

Module conversion. (* conversion *)

(* conversion.zero *)
Theorem zero : to_nat0 Zero = 0%n0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.one *)
Theorem one : to_nat0 One = 1%n0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.boundedness *)
Theorem boundedness : forall (x : UInt8) . (to_nat0 x < 256)%n0.
Proof.
  intros x.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl to_nat0 in |- *.
  ipso
    (Bit.conversion.boundedness.propagation _ _ _
      (Bit.conversion.boundedness.propagation _ _ _
        (Bit.conversion.boundedness.propagation _ _ _
          (Bit.conversion.boundedness.propagation _ _ _
            (Bit.conversion.boundedness.propagation _ _ _
              (Bit.conversion.boundedness.propagation _ _ _
                (Bit.conversion.boundedness.propagation _ _ _
                  (Bit.conversion.boundedness &x7)))))))).
Qed.

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : UInt8} {y : UInt8} . to_nat0 x = to_nat0 y -> x = y.
Proof.
  intros x y e.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_nat0 in &e.
  match (Bit.conversion.halving.injectivity &e) with | e1 b0 end.
  match (Bit.conversion.halving.injectivity &e1) with | e2 b1 end.
  match (Bit.conversion.halving.injectivity &e2) with | e3 b2 end.
  match (Bit.conversion.halving.injectivity &e3) with | e4 b3 end.
  match (Bit.conversion.halving.injectivity &e4) with | e5 b4 end.
  match (Bit.conversion.halving.injectivity &e5) with | e6 b5 end.
  match (Bit.conversion.halving.injectivity &e6) with | e7 b6 end.
  leibniz
    &b0, &b1, &b2, &b3, &b4, &b5, &b6, (Bit.conversion.injectivity &e7)
    in |- *.
  quod idem est.
Qed.

(* The numbers are added place by place from the most significant, each
 * place one [Bit.conversion.carry.propagation] around the places above it.
 *)
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : UInt8) (y : UInt8) .
      (Bit.to_nat0 carry + to_nat0 x + to_nat0 y
        = 256 * Bit.to_nat0 (pi_1 (add_with_carry carry x y))%product
          + to_nat0 (pi_2 (add_with_carry carry x y))%product)%n0.
Proof.
  intros carry x y.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_nat0, add_with_carry in |- *.
  ipso
    (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.carry.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.carry _ &x7 &y7)))))))).
Qed.

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : UInt8) (y : UInt8) .
      (to_nat0 x + 256 * Bit.to_nat0 (pi_1 (sub_with_borrow borrow x y))%product
        = to_nat0 y + Bit.to_nat0 borrow
          + to_nat0 (pi_2 (sub_with_borrow borrow x y))%product)%n0.
Proof.
  intros borrow x y.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | UInt8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl to_nat0, sub_with_borrow in |- *.
  ipso
    (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
      (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
        (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
          (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
            (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
              (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
                (Bit.conversion.borrow.propagation _ _ _ _ _ _ _ _
                  (Bit.conversion.borrow _ &x7 &y7)))))))).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : UInt8) (y : UInt8) .
      to_nat0 (x + y) = ((to_nat0 x + to_nat0 y) %. 256)%n0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product * 256
        + to_nat0 (&x + &y)%uint8
        = to_nat0 &x + to_nat0 &y
      /\ to_nat0 (&x + &y)%uint8 < 256)%n0.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (Nat0.multiplication.commutativity
          (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product) 256%n0),
        <- (conversion.carry Bit.Zero &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (conversion.boundedness (&x + &y)).
  }
  match (Nat0.division.uniqueness
          (to_nat0 &x + to_nat0 &y)%n0 256%n
          (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          (to_nat0 (&x + &y)%uint8)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : UInt8) (y : UInt8) .
      ((to_nat0 (sub x y) + to_nat0 y) %. 256 = to_nat0 x)%n0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product * 256 + to_nat0 &x
        = to_nat0 (sub &x &y) + to_nat0 &y
      /\ to_nat0 &x < 256)%n0.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (Nat0.multiplication.commutativity
          (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product) 256%n0),
        (Nat0.addition.commutativity
          (256 * Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)%n0
          (to_nat0 &x)),
        (conversion.borrow Bit.Zero &x &y),
        (Nat0.addition.commutativity (to_nat0 &y) (Bit.to_nat0 Bit.Zero))
        in |- *.
      simpl in |- *.
      leibniz
        (Nat0.addition.commutativity
          (to_nat0 &y) (to_nat0 (pi_2 (sub_with_borrow Bit.Zero &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (conversion.boundedness &x).
  }
  match (Nat0.division.uniqueness
          (to_nat0 (sub &x &y) + to_nat0 &y)%n0 256%n
          (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)
          (to_nat0 &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : UInt8) . ((to_nat0 (- x)%uint8 + to_nat0 x) %. 256 = 0)%n0.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (conversion.subtraction Zero &x), conversion.zero in |- *.
  quod idem est.
Qed.

(* conversion.reduction *)
Theorem reduction
  : forall (n : Nat0) . to_nat0 (from_nat0 n) = (n %. 256)%n0.
Proof.
  intros n.
  match &n with | Zero | Positive p end.
  - simpl Nat0.modulo, Nat0.div, Product.second in |- *.
    simpl in |- *.
    quod idem est.
  - simpl from_nat0 in |- *.
    match p with | One | Successor (p' by IH) end per Nat.induction.
    + simpl Nat0.modulo, Nat0.div, Product.second in |- *.
      simpl in |- *.
      quod idem est.
    + lemma unfolding : from_nat (Nat.Successor &p') = add (from_nat &p') One.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding in |- *.
      lemma successor
        : (Nat0.Positive &p' + to_nat0 One = Nat0.Positive (Nat.Successor &p'))%n0.
      {
        leibniz (Nat0.addition.commutativity (Nat0.Positive &p') (to_nat0 One)) in |- *.
        simpl in |- *.
        quod idem est.
      }
      leibniz
        (conversion.addition (from_nat &p') One),
        &IH,
        (Nat0.modulo.sum.left.absorption (Nat0.Positive &p') (to_nat0 One) 256%n),
        &successor
        in |- *.
      quod idem est.
Qed.

(* conversion.section *)
Theorem section : forall (x : UInt8) . from_nat0 (to_nat0 x) = x.
Proof.
  intros x.
  lemma facto : to_nat0 (from_nat0 (to_nat0 &x)) = to_nat0 &x.
  {
    leibniz
      (conversion.reduction (to_nat0 &x)),
      (Nat0.modulo.identity (to_nat0 &x) 256%n (conversion.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

Module left. (* conversion.left *)

(* conversion.left.doubling *)
Lemma doubling
  : forall (x : UInt8) .
      to_nat0 (shift_left x 1%n0) = ((2 * to_nat0 x) %. 256)%n0.
Proof.
  intros x.
  lemma sum : shift_left &x 1%n0 = &x + &x.
  {
    match &x with | UInt8_introduction xb end.
    match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &x7 with | Zero | One end;
      match &x6 with | Zero | One end;
      match &x5 with | Zero | One end;
      match &x4 with | Zero | One end;
      match &x3 with | Zero | One end;
      match &x2 with | Zero | One end;
      match &x1 with | Zero | One end;
      match &x0 with | Zero | One end;
      simpl add in |- *;
      simpl in |- *;
      quod idem est.
  }
  lemma twice : (2 * to_nat0 &x = to_nat0 &x + to_nat0 &x)%n0.
  {
    match (to_nat0 &x) with | Zero | Positive q end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  leibniz &sum, (conversion.addition &x &x), &twice in |- *.
  quod idem est.
Qed.

(* conversion.left.shift *)
Theorem shift
  : forall (x : UInt8) (k : Nat0) .
      to_nat0 (shift_left x k) = ((to_nat0 x * 2 ^ k) %. 256)%n0.
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
    simpl Nat0.power in |- *.
    match (Nat0.multiplication.identity (to_nat0 &x)) with | _ identity end.
    leibniz
      &identity,
      (Nat0.modulo.identity (to_nat0 &x) 256%n (conversion.boundedness &x))
      in |- *.
    quod idem est.
  - extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      lemma power : (2 ^ Nat0.Positive Nat.One = 2)%n0.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        (conversion.left.doubling &x),
        &power,
        (Nat0.multiplication.commutativity (to_nat0 &x) 2%n0)
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
      lemma power
        : (2 ^ Nat0.Positive (Nat.Successor &n') = 2 * 2 ^ Nat0.Positive &n')%n0.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (&IH (shift_left &x 1%n0)),
        (conversion.left.doubling &x),
        (Nat0.modulo.product.left.absorption
          (2 * to_nat0 &x)%n0 (2 ^ Nat0.Positive &n')%n0 256%n),
        &power,
        (Nat0.multiplication.commutativity 2%n0 (to_nat0 &x)),
        (Nat0.multiplication.associativity (to_nat0 &x) 2%n0 (2 ^ Nat0.Positive &n')%n0)
        in |- *.
      quod idem est.
Qed.

End left. (* conversion.left *)

Module right. (* conversion.right *)

(* conversion.right.halving *)
Lemma halving
  : forall (x : UInt8) . to_nat0 (shift_right x 1%n0) = (to_nat0 x /. 2)%n0.
Proof.
  intros x.
  match &x with | UInt8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match (Bit.conversion.halving
          (to_nat0
            (shift_right
              (UInt8_introduction
                (Byte.Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0))
              1%n0))
          &x0)
  with | quotient _ end.
  ipso (symm &quotient).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : UInt8) (k : Nat) .
      to_nat0 (shift_right x k) = (to_nat0 x /. (2 ^ k)%n)%n0.
Proof.
  intros x k.
  extro &x.
  match k with | One | Successor (k' by IH) end per Nat.induction.
  - intros x.
    lemma power : ((2 ^ Nat.One)%n = 2%n).
    {
      simpl in |- *.
      quod idem est.
    }
    leibniz (conversion.right.halving &x), &power in |- *.
    quod idem est.
  - intros x.
    lemma unfolding
      : shift_right &x (Nat0.Positive (Nat.Successor &k'))
        = shift_right (shift_right &x 1%n0) (Nat0.Positive &k').
    {
      match &x with | UInt8_introduction xb end.
      simpl in |- *.
      quod idem est.
    }
    lemma power : ((2 ^ Nat.Successor &k')%n = (2 * 2 ^ &k')%n).
    {
      simpl in |- *.
      quod idem est.
    }
    leibniz
      &unfolding,
      (&IH (shift_right &x 1%n0)),
      (conversion.right.halving &x),
      (Nat0.division.iteration (to_nat0 &x) 2%n (2 ^ &k')%n),
      &power
      in |- *.
    quod idem est.
Qed.

End right. (* conversion.right *)

Module multiplication. (* conversion.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* conversion.multiplication.step *)
Lemma step
  : forall (x : UInt8) (p : UInt8) (h : Nat0) (b : Bit) .
      to_nat0 p = ((to_nat0 x * h) %. 256)%n0 ->
      to_nat0
        (add (shift_left p 1%n0)
          match b with
          | Bit.Zero => Zero
          | Bit.One  => x
          end)
      = ((to_nat0 x * (2 * h + Bit.to_nat0 b)) %. 256)%n0.
Proof.
  intros x p h b e.
  lemma doubled
    : ((2 * to_nat0 &p) %. 256 = (2 * (to_nat0 &x * &h)) %. 256)%n0.
  {
    leibniz
      &e,
      (Nat0.modulo.product.right.absorption 2%n0 (to_nat0 &x * &h)%n0 256%n)
      in |- *.
    quod idem est.
  }
  lemma regrouped : (to_nat0 &x * (2 * &h) = 2 * (to_nat0 &x * &h))%n0.
  {
    leibniz
      <- (Nat0.multiplication.associativity (to_nat0 &x) 2%n0 &h),
      (Nat0.multiplication.commutativity (to_nat0 &x) 2%n0),
      (Nat0.multiplication.associativity 2%n0 (to_nat0 &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : to_nat0 (add (shift_left &p 1%n0) Zero)
        = ((to_nat0 &x * (2 * &h + Bit.to_nat0 Bit.Zero)) %. 256)%n0.
    {
      match (Nat0.addition.identity (2 * to_nat0 &p)%n0) with | _ right end.
      match (Nat0.addition.identity (2 * &h)%n0) with | _ right' end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) Zero),
        (conversion.left.doubling &p),
        conversion.zero,
        (Nat0.modulo.sum.left.absorption (2 * to_nat0 &p)%n0 0%n0 256%n),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_nat0 in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : to_nat0 (add (shift_left &p 1%n0) &x)
        = ((to_nat0 &x * (2 * &h + Bit.to_nat0 Bit.One)) %. 256)%n0.
    {
      match (Nat0.multiplication.identity (to_nat0 &x)) with | _ right end.
      leibniz
        (conversion.addition (shift_left &p 1%n0) &x),
        (conversion.left.doubling &p),
        &doubled,
        (Nat0.modulo.sum.left.absorption (2 * (to_nat0 &x * &h))%n0 (to_nat0 &x) 256%n)
        in |- *.
      simpl Bit.to_nat0 in |- *.
      leibniz
        (Nat0.multiplication.left.distributivity.over.addition
          (to_nat0 &x) (2 * &h)%n0 1%n0),
        &right,
        &regrouped
        in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* conversion.multiplication *)

(* conversion.multiplication *)
Theorem multiplication
  : forall (x : UInt8) (y : UInt8) .
      to_nat0 (x * y) = ((to_nat0 x * to_nat0 y) %. 256)%n0.
Proof.
  intros x y.
  lemma base : to_nat0 Zero = ((to_nat0 &x * 0) %. 256)%n0.
  {
    match (Nat0.multiplication.annihilation (to_nat0 &x)) with | _ right end.
    leibniz &right, conversion.zero in |- *.
    simpl Nat0.modulo, Nat0.div, Product.second in |- *.
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

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : UInt8) (y : UInt8) (z : UInt8) . (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma facto : to_nat0 ((&x + &y) + &z) = to_nat0 (&x + (&y + &z)).
  {
    leibniz
      (conversion.addition (&x + &y) &z),
      (conversion.addition &x &y),
      (Nat0.modulo.sum.left.absorption
        (to_nat0 &x + to_nat0 &y)%n0 (to_nat0 &z) 256%n),
      (conversion.addition &x (&y + &z)),
      (conversion.addition &y &z),
      (Nat0.modulo.sum.right.absorption
        (to_nat0 &x) (to_nat0 &y + to_nat0 &z)%n0 256%n),
      (Nat0.addition.associativity (to_nat0 &x) (to_nat0 &y) (to_nat0 &z))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (x : UInt8) (y : UInt8) . x + y = y + x.
Proof.
  intros x y.
  lemma facto : to_nat0 (&x + &y) = to_nat0 (&y + &x).
  {
    leibniz
      (conversion.addition &x &y),
      (conversion.addition &y &x),
      (Nat0.addition.commutativity (to_nat0 &x) (to_nat0 &y))
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
    lemma facto : to_nat0 (Zero + &x) = to_nat0 &x.
    {
      match (Nat0.addition.identity (to_nat0 &x)) with | left _ end.
      leibniz
        (conversion.addition Zero &x),
        conversion.zero,
        &left,
        (Nat0.modulo.identity (to_nat0 &x) 256%n (conversion.boundedness &x))
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
    lemma facto : to_nat0 (- &x + &x) = to_nat0 Zero.
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
  lemma facto : to_nat0 ((&x * &y) * &z) = to_nat0 (&x * (&y * &z)).
  {
    leibniz
      (conversion.multiplication (&x * &y) &z),
      (conversion.multiplication &x &y),
      (Nat0.modulo.product.left.absorption
        (to_nat0 &x * to_nat0 &y)%n0 (to_nat0 &z) 256%n),
      (conversion.multiplication &x (&y * &z)),
      (conversion.multiplication &y &z),
      (Nat0.modulo.product.right.absorption
        (to_nat0 &x) (to_nat0 &y * to_nat0 &z)%n0 256%n),
      (Nat0.multiplication.associativity (to_nat0 &x) (to_nat0 &y) (to_nat0 &z))
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

(* multiplication.commutativity *)
Theorem commutativity : forall (x : UInt8) (y : UInt8) . x * y = y * x.
Proof.
  intros x y.
  lemma facto : to_nat0 (&x * &y) = to_nat0 (&y * &x).
  {
    leibniz
      (conversion.multiplication &x &y),
      (conversion.multiplication &y &x),
      (Nat0.multiplication.commutativity (to_nat0 &x) (to_nat0 &y))
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
    lemma facto : to_nat0 (One * &x) = to_nat0 &x.
    {
      match (Nat0.multiplication.identity (to_nat0 &x)) with | left _ end.
      leibniz
        (conversion.multiplication One &x),
        conversion.one,
        &left,
        (Nat0.modulo.identity (to_nat0 &x) 256%n (conversion.boundedness &x))
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
  lemma facto : to_nat0 (&x * (&y + &z)) = to_nat0 ((&x * &y) + (&x * &z)).
  {
    leibniz
      (conversion.multiplication &x (&y + &z)),
      (conversion.addition &y &z),
      (Nat0.modulo.product.right.absorption
        (to_nat0 &x) (to_nat0 &y + to_nat0 &z)%n0 256%n),
      (Nat0.multiplication.left.distributivity.over.addition
        (to_nat0 &x) (to_nat0 &y) (to_nat0 &z)),
      (conversion.addition (&x * &y) (&x * &z)),
      (conversion.multiplication &x &y),
      (conversion.multiplication &x &z),
      (Nat0.modulo.sum.left.absorption
        (to_nat0 &x * to_nat0 &y)%n0 ((to_nat0 &x * to_nat0 &z) %. 256)%n0 256%n),
      (Nat0.modulo.sum.right.absorption
        (to_nat0 &x * to_nat0 &y)%n0 (to_nat0 &x * to_nat0 &z)%n0 256%n)
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
  ipso (Nat0.order.strict.transitivity &h1 &h2).
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
  let proof s := Nat0.comparison.specification (to_nat0 &x) (to_nat0 &y).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_nat0, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : UInt8) (y : UInt8) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (Nat0.comparison.antisymmetry (to_nat0 &x) (to_nat0 &y)).
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
