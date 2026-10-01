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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

Module Byte. (* Byte *)

(* Eight bits, the MSB first, as a binary number is written. *)
Inductive T : Type :=
  | Byte_introduction : Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> T.

Abbreviation Byte := T.

(* [Byte] *)
Definition Zero :=
  Byte_introduction
    Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero.

(* [Byte -> Byte] *)
Definition flip := fun (x : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      Byte_introduction
        (Bit.flip x7) (Bit.flip x6) (Bit.flip x5) (Bit.flip x4)
        (Bit.flip x3) (Bit.flip x2) (Bit.flip x1) (Bit.flip x0)
  end.

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition and := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.and x7 y7) (Bit.and x6 y6) (Bit.and x5 y5) (Bit.and x4 y4)
            (Bit.and x3 y3) (Bit.and x2 y2) (Bit.and x1 y1) (Bit.and x0 y0)
      end
  end.

Notation "x &. y" := (and x y) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition or := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.or x7 y7) (Bit.or x6 y6) (Bit.or x5 y5) (Bit.or x4 y4)
            (Bit.or x3 y3) (Bit.or x2 y2) (Bit.or x1 y1) (Bit.or x0 y0)
      end
  end.

Notation "x |. y" := (or x y) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition xor := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.xor x7 y7) (Bit.xor x6 y6) (Bit.xor x5 y5) (Bit.xor x4 y4)
            (Bit.xor x3 y3) (Bit.xor x2 y2) (Bit.xor x1 y1) (Bit.xor x0 y0)
      end
  end.

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_byte_scope.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1].
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint rotate_left_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match x with
    | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
        Byte_introduction x6 x5 x4 x3 x2 x1 x0 x7
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint rotate_right_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
      Byte_introduction y0 y7 y6 y5 y4 y3 y2 y1
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition rotate_left := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition rotate_right := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [Bit.Zero] coming in at the
 * other, in the order of [rotate_left_nat].
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint shift_left_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match x with
    | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
        Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [k] places toward the least significant end, a [Bit.Zero] coming in at
 * the other; one place first, then [k - 1], so that a step of the count
 * reduces to a step of the argument ([conversion.right.shift]).
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint shift_right_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match x with
    | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
        Byte_introduction Bit.Zero x7 x6 x5 x4 x3 x2 x1
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition shift_left := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition shift_right := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* The bits read as a number in base two, the most significant first. *)
(* [Byte -> Nat0] *)
Definition to_nat0 := fun (x : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      (2 * (2 * (2 * (2 * (2 * (2 * (2 * Bit.to_nat0 x7 + Bit.to_nat0 x6)
        + Bit.to_nat0 x5) + Bit.to_nat0 x4) + Bit.to_nat0 x3) + Bit.to_nat0 x2)
        + Bit.to_nat0 x1) + Bit.to_nat0 x0)%n0
  end.

(* [Byte] *)
Definition One :=
  Byte_introduction
    Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One.

(* The carry out and the sum of [carry + x + y], the carry rippling up from
 * the least significant place; the carry out goes into the next byte of a
 * wider number.
 *)
(* [Bit -> Byte -> Byte -> Product Bit Byte] *)
Definition add_with_carry := fun (carry : Bit) (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          let r0 := Bit.add_with_carry carry x0 y0 in
          let r1 := Bit.add_with_carry (pi_1 r0) x1 y1 in
          let r2 := Bit.add_with_carry (pi_1 r1) x2 y2 in
          let r3 := Bit.add_with_carry (pi_1 r2) x3 y3 in
          let r4 := Bit.add_with_carry (pi_1 r3) x4 y4 in
          let r5 := Bit.add_with_carry (pi_1 r4) x5 y5 in
          let r6 := Bit.add_with_carry (pi_1 r5) x6 y6 in
          let r7 := Bit.add_with_carry (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Byte_introduction
              (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
              (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0))
      end
  end%product.

(* [Byte -> Byte -> Byte] *)
Definition add := fun (x : Byte) (y : Byte) . (pi_2 (add_with_carry Bit.Zero x y))%product.

Notation "x + y" := (add x y) (only parsing)
  : jwa_byte_scope.

(* The borrow out and the difference of [x - y - borrow], the borrow
 * rippling up as the carry does in [add_with_carry].
 *)
(* [Bit -> Byte -> Byte -> Product Bit Byte] *)
Definition sub_with_borrow := fun (borrow : Bit) (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          let r0 := Bit.sub_with_borrow borrow x0 y0 in
          let r1 := Bit.sub_with_borrow (pi_1 r0) x1 y1 in
          let r2 := Bit.sub_with_borrow (pi_1 r1) x2 y2 in
          let r3 := Bit.sub_with_borrow (pi_1 r2) x3 y3 in
          let r4 := Bit.sub_with_borrow (pi_1 r3) x4 y4 in
          let r5 := Bit.sub_with_borrow (pi_1 r4) x5 y5 in
          let r6 := Bit.sub_with_borrow (pi_1 r5) x6 y6 in
          let r7 := Bit.sub_with_borrow (pi_1 r6) x7 y7 in
          (pi_1 r7,
            Byte_introduction
              (pi_2 r7) (pi_2 r6) (pi_2 r5) (pi_2 r4)
              (pi_2 r3) (pi_2 r2) (pi_2 r1) (pi_2 r0))
      end
  end%product.

(* [Byte -> Byte -> Byte] *)
Definition sub := fun (x : Byte) (y : Byte) . (pi_2 (sub_with_borrow Bit.Zero x y))%product.

(* The two's complement: [x] taken from [Zero], wrapping. *)
(* [Byte -> Byte] *)
Definition negate := fun (x : Byte) . sub Zero x.

Notation "- x" := (negate x)
  (at level 35, right associativity, only parsing)
  : jwa_byte_scope.

(* [y]'s bits from the most significant, each step doubling the product so
 * far and adding [x] for a 1, all modulo 256.
 *)
(* [Byte -> Byte -> Byte] *)
Definition mul := fun (x : Byte) (y : Byte) .
  let step := fun (p : Byte) (b : Bit) .
    add (shift_left_nat p Nat.One)
      match b with
      | Bit.Zero => Zero
      | Bit.One  => x
      end in
  match y with
  | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
      step (step (step (step (step (step (step (step Zero y7) y6) y5) y4) y3) y2) y1) y0
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_byte_scope.

(* [n] modulo 256, counted up from [One]. *)
(* [Nat -> Byte] *)
Fixpoint from_nat (n : Nat) : Byte :=
  match n with
  | Nat.One          => One
  | Nat.Successor n' => add (from_nat n') One
  end.

(* [Nat0 -> Byte] *)
Definition from_nat0 := fun (n : Nat0) .
  match n with
  | Nat0.Zero       => Zero
  | Nat0.Positive p => from_nat p
  end.

(* [Byte -> Byte -> Prop] *)
Definition LessThan := fun (x : Byte) (y : Byte) . (to_nat0 x < to_nat0 y)%n0.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Prop] *)
Definition LessOrEqual := fun (x : Byte) (y : Byte) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_byte_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_byte_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_byte_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_byte_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Comparison] *)
Definition compare := fun (x : Byte) (y : Byte) . Nat0.compare (to_nat0 x) (to_nat0 y).

(* [Byte -> Byte -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Byte -> Byte -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Byte -> Byte -> Byte] *)
Abbreviation min := (Comparable.min compare).

(* [Byte -> Byte -> Byte] *)
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
(* [Numeral.Unsigned -> Option Byte] *)
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
(* [Byte -> Numeral.Unsigned] *)
Definition to_numeral := fun (x : Byte) . Nat0.to_numeral (to_nat0 x).

Local Open Scope jwa_byte_scope.

(* Eight equal fields make equal bytes; each law below is its [Bit]
 * counterpart taken field by field through this.
 *)
(* congruence *)
Lemma congruence
  : forall {a7 : Bit} {a6 : Bit} {a5 : Bit} {a4 : Bit}
      {a3 : Bit} {a2 : Bit} {a1 : Bit} {a0 : Bit}
      {b7 : Bit} {b6 : Bit} {b5 : Bit} {b4 : Bit}
      {b3 : Bit} {b2 : Bit} {b1 : Bit} {b0 : Bit} .
      a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 ->
      a3 = b3 -> a2 = b2 -> a1 = b1 -> a0 = b0 ->
      Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0
        = Byte_introduction b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
  intros e7 e6 e5 e4 e3 e2 e1 e0.
  leibniz &e7, &e6, &e5, &e4, &e3, &e2, &e1, &e0 in |- *.
  quod idem est.
Qed.

Module flipping. (* flipping *)

(* flipping.involution *)
Theorem involution : forall (x : Byte) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.flipping.involution &x7) (Bit.flipping.involution &x6)
      (Bit.flipping.involution &x5) (Bit.flipping.involution &x4)
      (Bit.flipping.involution &x3) (Bit.flipping.involution &x2)
      (Bit.flipping.involution &x1) (Bit.flipping.involution &x0)).
Qed.

End flipping. (* flipping *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.associativity &x7 &y7 &z7)
      (Bit.conjunction.associativity &x6 &y6 &z6)
      (Bit.conjunction.associativity &x5 &y5 &z5)
      (Bit.conjunction.associativity &x4 &y4 &z4)
      (Bit.conjunction.associativity &x3 &y3 &z3)
      (Bit.conjunction.associativity &x2 &y2 &z2)
      (Bit.conjunction.associativity &x1 &y1 &z1)
      (Bit.conjunction.associativity &x0 &y0 &z0)).
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x &. y = y &. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.commutativity &x7 &y7)
      (Bit.conjunction.commutativity &x6 &y6)
      (Bit.conjunction.commutativity &x5 &y5)
      (Bit.conjunction.commutativity &x4 &y4)
      (Bit.conjunction.commutativity &x3 &y3)
      (Bit.conjunction.commutativity &x2 &y2)
      (Bit.conjunction.commutativity &x1 &y1)
      (Bit.conjunction.commutativity &x0 &y0)).
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (x : Byte) . (~. Zero &. x = x) /\ (x &. ~. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (conjunction.commutativity &x (~. Zero)) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.left.distributivity.over.sejunction &x7 &y7 &z7)
      (Bit.conjunction.left.distributivity.over.sejunction &x6 &y6 &z6)
      (Bit.conjunction.left.distributivity.over.sejunction &x5 &y5 &z5)
      (Bit.conjunction.left.distributivity.over.sejunction &x4 &y4 &z4)
      (Bit.conjunction.left.distributivity.over.sejunction &x3 &y3 &z3)
      (Bit.conjunction.left.distributivity.over.sejunction &x2 &y2 &z2)
      (Bit.conjunction.left.distributivity.over.sejunction &x1 &y1 &z1)
      (Bit.conjunction.left.distributivity.over.sejunction &x0 &y0 &z0)).
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.right.distributivity.over.sejunction &x7 &y7 &z7)
      (Bit.conjunction.right.distributivity.over.sejunction &x6 &y6 &z6)
      (Bit.conjunction.right.distributivity.over.sejunction &x5 &y5 &z5)
      (Bit.conjunction.right.distributivity.over.sejunction &x4 &y4 &z4)
      (Bit.conjunction.right.distributivity.over.sejunction &x3 &y3 &z3)
      (Bit.conjunction.right.distributivity.over.sejunction &x2 &y2 &z2)
      (Bit.conjunction.right.distributivity.over.sejunction &x1 &y1 &z1)
      (Bit.conjunction.right.distributivity.over.sejunction &x0 &y0 &z0)).
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x &. (y ^. z) = (x &. y) ^. (x &. z))
    /\ ((y ^. z) &. x = (y &. x) ^. (z &. x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (conjunction.left.distributivity.over.sejunction  &x &y &z).
  - ipso (conjunction.right.distributivity.over.sejunction &x &y &z).
Qed.

End over. (* conjunction.distributivity.over *)

End distributivity. (* conjunction.distributivity *)

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.associativity *)
Theorem associativity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.disjunction.associativity &x7 &y7 &z7)
      (Bit.disjunction.associativity &x6 &y6 &z6)
      (Bit.disjunction.associativity &x5 &y5 &z5)
      (Bit.disjunction.associativity &x4 &y4 &z4)
      (Bit.disjunction.associativity &x3 &y3 &z3)
      (Bit.disjunction.associativity &x2 &y2 &z2)
      (Bit.disjunction.associativity &x1 &y1 &z1)
      (Bit.disjunction.associativity &x0 &y0 &z0)).
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x |. y = y |. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.disjunction.commutativity &x7 &y7)
      (Bit.disjunction.commutativity &x6 &y6)
      (Bit.disjunction.commutativity &x5 &y5)
      (Bit.disjunction.commutativity &x4 &y4)
      (Bit.disjunction.commutativity &x3 &y3)
      (Bit.disjunction.commutativity &x2 &y2)
      (Bit.disjunction.commutativity &x1 &y1)
      (Bit.disjunction.commutativity &x0 &y0)).
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (x : Byte) . (Zero |. x = x) /\ (x |. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (disjunction.commutativity &x Zero) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.associativity *)
Theorem associativity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.associativity &x7 &y7 &z7)
      (Bit.sejunction.associativity &x6 &y6 &z6)
      (Bit.sejunction.associativity &x5 &y5 &z5)
      (Bit.sejunction.associativity &x4 &y4 &z4)
      (Bit.sejunction.associativity &x3 &y3 &z3)
      (Bit.sejunction.associativity &x2 &y2 &z2)
      (Bit.sejunction.associativity &x1 &y1 &z1)
      (Bit.sejunction.associativity &x0 &y0 &z0)).
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x ^. y = y ^. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.commutativity &x7 &y7)
      (Bit.sejunction.commutativity &x6 &y6)
      (Bit.sejunction.commutativity &x5 &y5)
      (Bit.sejunction.commutativity &x4 &y4)
      (Bit.sejunction.commutativity &x3 &y3)
      (Bit.sejunction.commutativity &x2 &y2)
      (Bit.sejunction.commutativity &x1 &y1)
      (Bit.sejunction.commutativity &x0 &y0)).
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (x : Byte) . (Zero ^. x = x) /\ (x ^. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (sejunction.commutativity &x Zero) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : Byte) . x ^. x = Zero.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl Zero in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.irreflexivity &x7) (Bit.sejunction.irreflexivity &x6)
      (Bit.sejunction.irreflexivity &x5) (Bit.sejunction.irreflexivity &x4)
      (Bit.sejunction.irreflexivity &x3) (Bit.sejunction.irreflexivity &x2)
      (Bit.sejunction.irreflexivity &x1) (Bit.sejunction.irreflexivity &x0)).
Qed.

(* sejunction.inverse *)
Theorem inverse
  : forall (x : Byte) . (x ^. x = Zero) /\ (x ^. x = Zero).
Proof.
  intros x.
  divide et impera; ipso (sejunction.irreflexivity &x).
Qed.

End sejunction. (* sejunction *)

Module rotation. (* rotation *)

Module left. (* rotation.left *)

(* rotation.left.period *)
Theorem period : forall (x : Byte) . rotate_left x 8%n0 = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : Byte) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      quod idem est.
    + intros x.
      match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      leibniz (&IH (Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x7)) in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : Byte) . rotate_right x 8%n0 = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : Byte) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0
      end.
      ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

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
Theorem boundedness : forall (x : Byte) . (to_nat0 x < 256)%n0.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
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
  : forall {x : Byte} {y : Byte} . to_nat0 x = to_nat0 y -> x = y.
Proof.
  intros x y e.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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

(* The bytes are added place by place from the most significant, each
 * place one [Bit.conversion.carry.propagation] around the places above it.
 *)
(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (x : Byte) (y : Byte) .
      (Bit.to_nat0 carry + to_nat0 x + to_nat0 y
        = 256 * Bit.to_nat0 (pi_1 (add_with_carry carry x y))%product
          + to_nat0 (pi_2 (add_with_carry carry x y))%product)%n0.
Proof.
  intros carry x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
  : forall (borrow : Bit) (x : Byte) (y : Byte) .
      (to_nat0 x + 256 * Bit.to_nat0 (pi_1 (sub_with_borrow borrow x y))%product
        = to_nat0 y + Bit.to_nat0 borrow
          + to_nat0 (pi_2 (sub_with_borrow borrow x y))%product)%n0.
Proof.
  intros borrow x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
  : forall (x : Byte) (y : Byte) .
      to_nat0 (x + y) = ((to_nat0 x + to_nat0 y) %. 256)%n0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product * 256
        + to_nat0 (&x + &y)%byte
        = to_nat0 &x + to_nat0 &y
      /\ to_nat0 (&x + &y)%byte < 256)%n0.
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
          (to_nat0 (&x + &y)%byte)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (x : Byte) (y : Byte) .
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
  : forall (x : Byte) . ((to_nat0 (- x)%byte + to_nat0 x) %. 256 = 0)%n0.
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
Theorem section : forall (x : Byte) . from_nat0 (to_nat0 x) = x.
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
  : forall (x : Byte) .
      to_nat0 (shift_left_nat x Nat.One) = ((2 * to_nat0 x) %. 256)%n0.
Proof.
  intros x.
  lemma sum : shift_left_nat &x Nat.One = &x + &x.
  {
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
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
  : forall (x : Byte) (k : Nat0) .
      to_nat0 (shift_left x k) = ((to_nat0 x * 2 ^ k) %. 256)%n0.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl shift_left, Nat0.power in |- *.
    match (Nat0.multiplication.identity (to_nat0 &x)) with | _ identity end.
    leibniz
      &identity,
      (Nat0.modulo.identity (to_nat0 &x) 256%n (conversion.boundedness &x))
      in |- *.
    quod idem est.
  - simpl shift_left in |- *.
    extro &x.
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
        : shift_left_nat &x (Nat.Successor &n')
          = shift_left_nat (shift_left_nat &x Nat.One) &n'.
      {
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
        (&IH (shift_left_nat &x Nat.One)),
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
  : forall (x : Byte) . to_nat0 (shift_right_nat x Nat.One) = (to_nat0 x /. 2)%n0.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match (Bit.conversion.halving
          (to_nat0
            (shift_right_nat
              (Byte_introduction &x7 &x6 &x5 &x4 &x3 &x2 &x1 &x0) Nat.One))
          &x0)
  with | quotient _ end.
  ipso (symm &quotient).
Qed.

(* conversion.right.shift *)
Theorem shift
  : forall (x : Byte) (k : Nat) .
      to_nat0 (shift_right x k) = (to_nat0 x /. (2 ^ k)%n)%n0.
Proof.
  intros x k.
  simpl shift_right in |- *.
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
      : shift_right_nat &x (Nat.Successor &k')
        = shift_right_nat (shift_right_nat &x Nat.One) &k'.
    {
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
      (&IH (shift_right_nat &x Nat.One)),
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
  : forall (x : Byte) (p : Byte) (h : Nat0) (b : Bit) .
      to_nat0 p = ((to_nat0 x * h) %. 256)%n0 ->
      to_nat0
        (add (shift_left_nat p Nat.One)
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
      : to_nat0 (add (shift_left_nat &p Nat.One) Zero)
        = ((to_nat0 &x * (2 * &h + Bit.to_nat0 Bit.Zero)) %. 256)%n0.
    {
      match (Nat0.addition.identity (2 * to_nat0 &p)%n0) with | _ right end.
      match (Nat0.addition.identity (2 * &h)%n0) with | _ right' end.
      leibniz
        (conversion.addition (shift_left_nat &p Nat.One) Zero),
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
      : to_nat0 (add (shift_left_nat &p Nat.One) &x)
        = ((to_nat0 &x * (2 * &h + Bit.to_nat0 Bit.One)) %. 256)%n0.
    {
      match (Nat0.multiplication.identity (to_nat0 &x)) with | _ right end.
      leibniz
        (conversion.addition (shift_left_nat &p Nat.One) &x),
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
  : forall (x : Byte) (y : Byte) .
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
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
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
  : forall (x : Byte) (y : Byte) (z : Byte) . (x + y) + z = x + (y + z).
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
Theorem commutativity : forall (x : Byte) (y : Byte) . x + y = y + x.
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
Theorem identity : forall (x : Byte) . (Zero + x = x) /\ (x + Zero = x).
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
Theorem inverse : forall (x : Byte) . (- x + x = Zero) /\ (x + - x = Zero).
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
  : forall (x : Byte) (y : Byte) (z : Byte) . (x * y) * z = x * (y * z).
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
Theorem commutativity : forall (x : Byte) (y : Byte) . x * y = y * x.
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
Theorem identity : forall (x : Byte) . (One * x = x) /\ (x * One = x).
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
  : forall (x : Byte) (y : Byte) (z : Byte) . x * (y + z) = (x * y) + (x * z).
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
  : forall (x : Byte) (y : Byte) (z : Byte) . (y + z) * x = (y * x) + (z * x).
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
  : forall (x : Byte) (y : Byte) (z : Byte) .
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
  : forall {x : Byte} {y : Byte} {z : Byte} . x < y -> y < z -> x < z.
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
  : forall (x : Byte) (y : Byte) .
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
  : forall (x : Byte) (y : Byte) . compare x y = Comparison.transpose (compare y x).
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

End Byte. (* Byte *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Byte], not [Byte.T].
 *)
Abbreviation Byte := Byte.T.

(* Makes the notations declared in [Module Byte] usable in every file that
 * imports this one, as [(x &. y)%byte] or under an opened [jwa_byte_scope].
 *)
Export (notations) Byte.

(* A byte is written in decimal or hexadecimal under its scope, [200%byte]
 * or [0xFF%byte], and a closed one prints in decimal.
 *)
Number Notation Byte.T Byte.from_numeral Byte.to_numeral
  : jwa_byte_scope.

(* Where a [Byte] is expected, a literal or a notation reads in this scope
 * without its [%byte].
 *)
Bind Scope jwa_byte_scope with Byte.T.

Instance Byte_and_monoid
  : Monoid Byte.and (Byte.flip Byte.Zero) :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.conjunction.associativity |}
  ; Monoid.identity := Byte.conjunction.identity |}.

Instance Byte_or_monoid
  : Monoid Byte.or Byte.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.disjunction.associativity |}
  ; Monoid.identity := Byte.disjunction.identity |}.

Instance Byte_xor_monoid
  : Monoid Byte.xor Byte.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.sejunction.associativity |}
  ; Monoid.identity := Byte.sejunction.identity |}.

Instance Byte_and_commutative
  : Commutative Byte.and :=
  {| Commutative.commutativity := Byte.conjunction.commutativity |}.

Instance Byte_or_commutative
  : Commutative Byte.or :=
  {| Commutative.commutativity := Byte.disjunction.commutativity |}.

Instance Byte_xor_commutative
  : Commutative Byte.xor :=
  {| Commutative.commutativity := Byte.sejunction.commutativity |}.

Instance Byte_xor_group
  : Group Byte.xor Byte.Zero (fun (x : Byte) . x) :=
  {| Group.monoid := Byte_xor_monoid
  ; Group.inverse := Byte.sejunction.inverse |}.

Instance Byte_xor_abelian_group
  : AbelianGroup Byte.xor Byte.Zero (fun (x : Byte) . x) :=
  {| AbelianGroup.group := Byte_xor_group
  ; AbelianGroup.commutative := Byte_xor_commutative |}.

Instance Byte_ring
  : Ring Byte.xor Byte.Zero (fun (x : Byte) . x) Byte.and (Byte.flip Byte.Zero) :=
  {| Ring.abelian_group := Byte_xor_abelian_group
  ; Ring.monoid := Byte_and_monoid
  ; Ring.distributivity := Byte.conjunction.distributivity.over.sejunction |}.

Instance Byte_add_monoid
  : Monoid Byte.add Byte.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.addition.associativity |}
  ; Monoid.identity := Byte.addition.identity |}.

Instance Byte_mul_monoid
  : Monoid Byte.mul Byte.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.multiplication.associativity |}
  ; Monoid.identity := Byte.multiplication.identity |}.

Instance Byte_add_commutative
  : Commutative Byte.add :=
  {| Commutative.commutativity := Byte.addition.commutativity |}.

Instance Byte_mul_commutative
  : Commutative Byte.mul :=
  {| Commutative.commutativity := Byte.multiplication.commutativity |}.

Instance Byte_add_group
  : Group Byte.add Byte.Zero Byte.negate :=
  {| Group.monoid := Byte_add_monoid
  ; Group.inverse := Byte.addition.inverse |}.

Instance Byte_add_abelian_group
  : AbelianGroup Byte.add Byte.Zero Byte.negate :=
  {| AbelianGroup.group := Byte_add_group
  ; AbelianGroup.commutative := Byte_add_commutative |}.

Instance Byte_add_mul_ring
  : Ring Byte.add Byte.Zero Byte.negate Byte.mul Byte.One :=
  {| Ring.abelian_group := Byte_add_abelian_group
  ; Ring.monoid := Byte_mul_monoid
  ; Ring.distributivity := Byte.multiplication.distributivity.over.addition |}.
