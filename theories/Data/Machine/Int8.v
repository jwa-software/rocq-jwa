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
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* A signed integer of eight bits: a [Byte] read in two's complement, from
 * -128 to 127, its arithmetic wrapping modulo 256.
 *)

Module Int8. (* Int8 *)

Inductive T : Type :=
  | Int8_introduction : Byte -> T.

Abbreviation Int8 := T.

(* The bits read as a number in base two, the most significant first, from 0
 * to 255: the value of the bit pattern, through which the arithmetic is
 * proved and from which [to_integer] takes the signed value.
 *)
(* [Int8 -> Nat0] *)
Definition unsigned_value := fun (x : Int8) .
  match x with
  | Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
      (2 * (2 * (2 * (2 * (2 * (2 * (2 * Bit.to_nat0 x7 + Bit.to_nat0 x6)
        + Bit.to_nat0 x5) + Bit.to_nat0 x4) + Bit.to_nat0 x3) + Bit.to_nat0 x2)
        + Bit.to_nat0 x1) + Bit.to_nat0 x0)%n0
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
(* [Int8 -> Integer] *)
Definition to_integer := fun (x : Int8) .
  Integer.nat0_difference (unsigned_value x) (256 * Bit.to_nat0 (sign_bit x))%n0.

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

(* The bit pattern of [n] modulo 256, counted up from [One]. *)
(* [Nat -> Int8] *)
Fixpoint from_nat (n : Nat) : Int8 :=
  match n with
  | Nat.One          => One
  | Nat.Successor n' => add (from_nat n') One
  end.

(* [Nat0 -> Int8] *)
Definition from_nat0 := fun (n : Nat0) .
  match n with
  | Nat0.Zero       => Zero
  | Nat0.Positive p => from_nat p
  end.

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
Definition LessThan := fun (x : Int8) (y : Int8) . (to_integer x < to_integer y)%z.

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
Definition compare := fun (x : Int8) (y : Int8) . Integer.compare (to_integer x) (to_integer y).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Int8 -> Int8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation min := (Comparable.min compare).

(* [Int8 -> Int8 -> Int8] *)
Abbreviation max := (Comparable.max compare).

(* [n] followed by the digit [d] in base [base], [None] once the value
 * passes [limit] and from then on, so that a literal of any length is
 * refused without its value being built.
 *)
(* [Nat0 -> Nat0 -> Option Nat0 -> Option Nat -> Option Nat0] *)
Definition append_digit :=
  fun (limit : Nat0) (base : Nat0) (n : Option Nat0) (d : Option Nat) .
    match n with
    | None   => None
    | Some m =>
        let v :=
          (m * base
            + match d with
              | Some k => Nat0.Positive k
              | None   => 0
              end)%n0 in
        match Nat0.compare v limit with
        | Comparison.Lt => Some v
        | Comparison.Eq => Some v
        | Comparison.Gt => None
        end
    end.

(* [n] with the decimal digits [d] appended, most significant first. *)
(* [Nat0 -> Option Nat0 -> Numeral.Decimal.Digits -> Option Nat0] *)
Fixpoint from_decimal
  (limit : Nat0) (n : Option Nat0) (d : Numeral.Decimal.Digits) : Option Nat0 :=
  match d with
  | Numeral.Decimal.Digits.End      => n
  | Numeral.Decimal.Digits.Zero d'  =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.One d'   =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Two d'   =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Three d' =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Four d'  =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Five d'  =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Six d'   =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Seven d' =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Eight d' =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  | Numeral.Decimal.Digits.Nine d'  =>
      from_decimal limit (append_digit limit 10%n0 n (Nat.decimal_value d)) d'
  end.

(* [n] with the hexadecimal digits [h] appended, most significant first. *)
(* [Nat0 -> Option Nat0 -> Numeral.Hexadecimal.Digits -> Option Nat0] *)
Fixpoint from_hexadecimal
  (limit : Nat0) (n : Option Nat0) (h : Numeral.Hexadecimal.Digits) : Option Nat0 :=
  match h with
  | Numeral.Hexadecimal.Digits.End         => n
  | Numeral.Hexadecimal.Digits.Zero h'     =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.One h'      =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Two h'      =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Three h'    =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Four h'     =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Five h'     =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Six h'      =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Seven h'    =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Eight h'    =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Nine h'     =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Ten h'      =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Eleven h'   =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Twelve h'   =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Thirteen h' =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Fourteen h' =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  | Numeral.Hexadecimal.Digits.Fifteen h'  =>
      from_hexadecimal limit (append_digit limit 16%n0 n (Nat.hexadecimal_value h)) h'
  end.

(* A literal of -128 to 127, in decimal or hexadecimal; any wider is
 * refused.
 *)
(* [Numeral.Signed -> Option Int8] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  let positive := fun (v : Option Nat0) .
    match v with
    | Some n => Some (from_nat0 n)
    | None   => None
    end in
  let negative := fun (v : Option Nat0) .
    match v with
    | Some n => Some (negate (from_nat0 n))
    | None   => None
    end in
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      positive (from_decimal 127%n0 (Some 0%n0) d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      negative (from_decimal 128%n0 (Some 0%n0) d)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Positive h) =>
      positive (from_hexadecimal 127%n0 (Some 0%n0) h)
  | Numeral.Signed.Hexadecimal (Numeral.Hexadecimal.Signed.Negative h) =>
      negative (from_hexadecimal 128%n0 (Some 0%n0) h)
  end.

(* [x] as a literal, in decimal. *)
(* [Int8 -> Numeral.Signed] *)
Definition to_numeral := fun (x : Int8) . Integer.to_numeral (to_integer x).

Local Open Scope jwa_int8_scope.

Module valuation. (* valuation *)

(* valuation.zero *)
Theorem zero : unsigned_value Zero = 0%n0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* valuation.one *)
Theorem one : unsigned_value One = 1%n0.
Proof.
  simpl in |- *.
  quod idem est.
Qed.

(* valuation.boundedness *)
Theorem boundedness : forall (x : Int8) . (unsigned_value x < 256)%n0.
Proof.
  intros x.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl unsigned_value in |- *.
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
(* valuation.carry *)
Theorem carry
  : forall (carry : Bit) (x : Int8) (y : Int8) .
      (Bit.to_nat0 carry + unsigned_value x + unsigned_value y
        = 256 * Bit.to_nat0 (pi_1 (add_with_carry carry x y))%product
          + unsigned_value (pi_2 (add_with_carry carry x y))%product)%n0.
Proof.
  intros carry x y.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, add_with_carry in |- *.
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

(* valuation.borrow *)
Theorem borrow
  : forall (borrow : Bit) (x : Int8) (y : Int8) .
      (unsigned_value x + 256 * Bit.to_nat0 (pi_1 (sub_with_borrow borrow x y))%product
        = unsigned_value y + Bit.to_nat0 borrow
          + unsigned_value (pi_2 (sub_with_borrow borrow x y))%product)%n0.
Proof.
  intros borrow x y.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl unsigned_value, sub_with_borrow in |- *.
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

(* valuation.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      unsigned_value (x + y) = ((unsigned_value x + unsigned_value y) %. 256)%n0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product * 256
        + unsigned_value (&x + &y)%int8
        = unsigned_value &x + unsigned_value &y
      /\ unsigned_value (&x + &y)%int8 < 256)%n0.
  {
    divide et impera.
    - simpl add in |- *.
      leibniz
        (Nat0.multiplication.commutativity
          (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product) 256%n0),
        <- (valuation.carry Bit.Zero &x &y)
        in |- *.
      simpl in |- *.
      quod idem est.
    - ipso (valuation.boundedness (&x + &y)).
  }
  match (Nat0.division.uniqueness
          (unsigned_value &x + unsigned_value &y)%n0 256%n
          (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product)
          (unsigned_value (&x + &y)%int8)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

(* valuation.subtraction *)
Theorem subtraction
  : forall (x : Int8) (y : Int8) .
      ((unsigned_value (sub x y) + unsigned_value y) %. 256 = unsigned_value x)%n0.
Proof.
  intros x y.
  lemma witness
    : (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product * 256 + unsigned_value &x
        = unsigned_value (sub &x &y) + unsigned_value &y
      /\ unsigned_value &x < 256)%n0.
  {
    divide et impera.
    - simpl sub in |- *.
      leibniz
        (Nat0.multiplication.commutativity
          (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product) 256%n0),
        (Nat0.addition.commutativity
          (256 * Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)%n0
          (unsigned_value &x)),
        (valuation.borrow Bit.Zero &x &y),
        (Nat0.addition.commutativity (unsigned_value &y) (Bit.to_nat0 Bit.Zero))
        in |- *.
      simpl in |- *.
      leibniz
        (Nat0.addition.commutativity
          (unsigned_value &y)
          (unsigned_value (pi_2 (sub_with_borrow Bit.Zero &x &y))%product))
        in |- *.
      quod idem est.
    - ipso (valuation.boundedness &x).
  }
  match (Nat0.division.uniqueness
          (unsigned_value (sub &x &y) + unsigned_value &y)%n0 256%n
          (Bit.to_nat0 (pi_1 (sub_with_borrow Bit.Zero &x &y))%product)
          (unsigned_value &x)
          &witness)
  with | _ facto end.
  ipso facto.
Qed.

(* valuation.negation *)
Theorem negation
  : forall (x : Int8) . ((unsigned_value (- x)%int8 + unsigned_value x) %. 256 = 0)%n0.
Proof.
  intros x.
  simpl negate in |- *.
  leibniz (valuation.subtraction Zero &x), valuation.zero in |- *.
  quod idem est.
Qed.

(* valuation.reduction *)
Theorem reduction
  : forall (n : Nat0) . unsigned_value (from_nat0 n) = (n %. 256)%n0.
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
        : (Nat0.Positive &p' + unsigned_value One = Nat0.Positive (Nat.Successor &p'))%n0.
      {
        leibniz
          (Nat0.addition.commutativity (Nat0.Positive &p') (unsigned_value One))
          in |- *.
        simpl in |- *.
        quod idem est.
      }
      leibniz
        (valuation.addition (from_nat &p') One),
        &IH,
        (Nat0.modulo.sum.left.absorption (Nat0.Positive &p') (unsigned_value One) 256%n),
        &successor
        in |- *.
      quod idem est.
Qed.

(* valuation.section *)
Theorem section : forall (x : Int8) . from_nat0 (unsigned_value x) = x.
Proof.
  intros x.
  lemma facto : unsigned_value (from_nat0 (unsigned_value &x)) = unsigned_value &x.
  {
    leibniz
      (valuation.reduction (unsigned_value &x)),
      (Nat0.modulo.identity (unsigned_value &x) 256%n (valuation.boundedness &x))
      in |- *.
    quod idem est.
  }
  ipso (valuation.injectivity &facto).
Qed.

Module left. (* valuation.left *)

(* valuation.left.doubling *)
Lemma doubling
  : forall (x : Int8) .
      unsigned_value (shift_left x 1%n0) = ((2 * unsigned_value x) %. 256)%n0.
Proof.
  intros x.
  lemma sum : shift_left &x 1%n0 = &x + &x.
  {
    match &x with | Int8_introduction xb end.
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
  lemma twice : (2 * unsigned_value &x = unsigned_value &x + unsigned_value &x)%n0.
  {
    match (unsigned_value &x) with | Zero | Positive q end.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  leibniz &sum, (valuation.addition &x &x), &twice in |- *.
  quod idem est.
Qed.

End left. (* valuation.left *)

Module multiplication. (* valuation.multiplication *)

(* One step of [mul]: the product so far doubled, plus [x] for a 1. *)
(* valuation.multiplication.step *)
Lemma step
  : forall (x : Int8) (p : Int8) (h : Nat0) (b : Bit) .
      unsigned_value p = ((unsigned_value x * h) %. 256)%n0 ->
      unsigned_value
        (add (shift_left p 1%n0)
          match b with
          | Bit.Zero => Zero
          | Bit.One  => x
          end)
      = ((unsigned_value x * (2 * h + Bit.to_nat0 b)) %. 256)%n0.
Proof.
  intros x p h b e.
  lemma doubled
    : ((2 * unsigned_value &p) %. 256 = (2 * (unsigned_value &x * &h)) %. 256)%n0.
  {
    leibniz
      &e,
      (Nat0.modulo.product.right.absorption 2%n0 (unsigned_value &x * &h)%n0 256%n)
      in |- *.
    quod idem est.
  }
  lemma regrouped
    : (unsigned_value &x * (2 * &h) = 2 * (unsigned_value &x * &h))%n0.
  {
    leibniz
      <- (Nat0.multiplication.associativity (unsigned_value &x) 2%n0 &h),
      (Nat0.multiplication.commutativity (unsigned_value &x) 2%n0),
      (Nat0.multiplication.associativity 2%n0 (unsigned_value &x) &h)
      in |- *.
    quod idem est.
  }
  match &b with | Zero | One end.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) Zero)
        = ((unsigned_value &x * (2 * &h + Bit.to_nat0 Bit.Zero)) %. 256)%n0.
    {
      match (Nat0.addition.identity (2 * unsigned_value &p)%n0) with | _ right end.
      match (Nat0.addition.identity (2 * &h)%n0) with | _ right' end.
      leibniz
        (valuation.addition (shift_left &p 1%n0) Zero),
        (valuation.left.doubling &p),
        valuation.zero,
        (Nat0.modulo.sum.left.absorption (2 * unsigned_value &p)%n0 0%n0 256%n),
        &right,
        &doubled
        in |- *.
      simpl Bit.to_nat0 in |- *.
      leibniz &right', &regrouped in |- *.
      quod idem est.
    }
    ipso facto.
  - lemma facto
      : unsigned_value (add (shift_left &p 1%n0) &x)
        = ((unsigned_value &x * (2 * &h + Bit.to_nat0 Bit.One)) %. 256)%n0.
    {
      match (Nat0.multiplication.identity (unsigned_value &x)) with | _ right end.
      leibniz
        (valuation.addition (shift_left &p 1%n0) &x),
        (valuation.left.doubling &p),
        &doubled,
        (Nat0.modulo.sum.left.absorption
          (2 * (unsigned_value &x * &h))%n0 (unsigned_value &x) 256%n)
        in |- *.
      simpl Bit.to_nat0 in |- *.
      leibniz
        (Nat0.multiplication.left.distributivity.over.addition
          (unsigned_value &x) (2 * &h)%n0 1%n0),
        &right,
        &regrouped
        in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End multiplication. (* valuation.multiplication *)

(* valuation.multiplication *)
Theorem multiplication
  : forall (x : Int8) (y : Int8) .
      unsigned_value (x * y) = ((unsigned_value x * unsigned_value y) %. 256)%n0.
Proof.
  intros x y.
  lemma base : unsigned_value Zero = ((unsigned_value &x * 0) %. 256)%n0.
  {
    match (Nat0.multiplication.annihilation (unsigned_value &x)) with | _ right end.
    leibniz &right, valuation.zero in |- *.
    simpl Nat0.modulo, Nat0.div, Product.second in |- *.
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
      (Nat0.modulo.sum.left.absorption
        (unsigned_value &x + unsigned_value &y)%n0 (unsigned_value &z) 256%n),
      (valuation.addition &x (&y + &z)),
      (valuation.addition &y &z),
      (Nat0.modulo.sum.right.absorption
        (unsigned_value &x) (unsigned_value &y + unsigned_value &z)%n0 256%n),
      (Nat0.addition.associativity
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
      (Nat0.addition.commutativity (unsigned_value &x) (unsigned_value &y))
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
      match (Nat0.addition.identity (unsigned_value &x)) with | left _ end.
      leibniz
        (valuation.addition Zero &x),
        valuation.zero,
        &left,
        (Nat0.modulo.identity (unsigned_value &x) 256%n (valuation.boundedness &x))
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
      (Nat0.modulo.product.left.absorption
        (unsigned_value &x * unsigned_value &y)%n0 (unsigned_value &z) 256%n),
      (valuation.multiplication &x (&y * &z)),
      (valuation.multiplication &y &z),
      (Nat0.modulo.product.right.absorption
        (unsigned_value &x) (unsigned_value &y * unsigned_value &z)%n0 256%n),
      (Nat0.multiplication.associativity
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
      (Nat0.multiplication.commutativity (unsigned_value &x) (unsigned_value &y))
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
      match (Nat0.multiplication.identity (unsigned_value &x)) with | left _ end.
      leibniz
        (valuation.multiplication One &x),
        valuation.one,
        &left,
        (Nat0.modulo.identity (unsigned_value &x) 256%n (valuation.boundedness &x))
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
    leibniz
      (valuation.multiplication &x (&y + &z)),
      (valuation.addition &y &z),
      (Nat0.modulo.product.right.absorption
        (unsigned_value &x) (unsigned_value &y + unsigned_value &z)%n0 256%n),
      (Nat0.multiplication.left.distributivity.over.addition
        (unsigned_value &x) (unsigned_value &y) (unsigned_value &z)),
      (valuation.addition (&x * &y) (&x * &z)),
      (valuation.multiplication &x &y),
      (valuation.multiplication &x &z),
      (Nat0.modulo.sum.left.absorption
        (unsigned_value &x * unsigned_value &y)%n0
        ((unsigned_value &x * unsigned_value &z) %. 256)%n0 256%n),
      (Nat0.modulo.sum.right.absorption
        (unsigned_value &x * unsigned_value &y)%n0
        (unsigned_value &x * unsigned_value &z)%n0 256%n)
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

(* Checked byte by byte, the two sides computing to the same bits. *)
(* conversion.section *)
Theorem section : forall (x : Int8) . from_integer (to_integer x) = x.
Proof.
  intros x.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &x7 with | Zero | One end;
    match &x6 with | Zero | One end;
    match &x5 with | Zero | One end;
    match &x4 with | Zero | One end;
    match &x3 with | Zero | One end;
    match &x2 with | Zero | One end;
    match &x1 with | Zero | One end;
    match &x0 with | Zero | One end;
    ipso (Identity.reflexivity _).
Qed.

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : Int8} {y : Int8} . to_integer x = to_integer y -> x = y.
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
      (Bit.to_nat0 (sign_bit x) + Bit.to_nat0 (sign_bit y)
        = Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero x y))%product
          + Bit.to_nat0 (sign_bit (x + y)%int8))%n0.
Proof.
  intros x y o.
  match &x with | Int8_introduction xb end.
  match &xb with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Int8_introduction yb end.
  match &yb with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in &o |- *.
  ipso (Bit.conversion.carry.conservation _ &x7 &y7 &o).
Qed.

(* conversion.addition *)
Theorem addition
  : forall (x : Int8) (y : Int8) .
      (pi_1 (add_with_overflow x y))%product = Bit.Zero ->
      to_integer (x + y) = (to_integer x + to_integer y)%z.
Proof.
  intros x y o.
  let proof t := conversion.sign &x &y &o.
  let proof a
    : (unsigned_value &x + unsigned_value &y
        = 256 * Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product
          + unsigned_value (&x + &y)%int8)%n0
    := valuation.carry Bit.Zero &x &y.
  lemma balance
    : (unsigned_value (&x + &y)%int8
        + (256 * Bit.to_nat0 (sign_bit &x) + 256 * Bit.to_nat0 (sign_bit &y))
        = (unsigned_value &x + unsigned_value &y)
          + 256 * Bit.to_nat0 (sign_bit (&x + &y)%int8))%n0.
  {
    leibniz
      <- (Nat0.multiplication.left.distributivity.over.addition
        256%n0 (Bit.to_nat0 (sign_bit &x)) (Bit.to_nat0 (sign_bit &y))),
      &t,
      (Nat0.multiplication.left.distributivity.over.addition
        256%n0
        (Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product)
        (Bit.to_nat0 (sign_bit (&x + &y)%int8))),
      <- (Nat0.addition.associativity
        (unsigned_value (&x + &y)%int8)
        (256 * Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product)%n0
        (256 * Bit.to_nat0 (sign_bit (&x + &y)%int8))%n0),
      (Nat0.addition.commutativity
        (unsigned_value (&x + &y)%int8)
        (256 * Bit.to_nat0 (pi_1 (add_with_carry Bit.Zero &x &y))%product)%n0),
      &a
      in |- *.
    quod idem est.
  }
  simpl to_integer in |- *.
  leibniz
    (Integer.difference.nat0.additivity
      (unsigned_value &x) (256 * Bit.to_nat0 (sign_bit &x))%n0
      (unsigned_value &y) (256 * Bit.to_nat0 (sign_bit &y))%n0)
    in |- *.
  ipso (Integer.difference.nat0.well_definedness &balance).
Qed.

Module right. (* conversion.right *)

(* A shift to the right by one place halves the value, rounding down: the
 * lowest bit is what it drops.
 *)
(* conversion.right.halving *)
Theorem halving
  : forall (x7 : Bit) (x6 : Bit) (x5 : Bit) (x4 : Bit)
      (x3 : Bit) (x2 : Bit) (x1 : Bit) (x0 : Bit) .
      to_integer (Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0))
      = (2
          * to_integer
              (shift_right
                (Int8_introduction (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0))
                1%n0)
          + Integer.from_nat0 (Bit.to_nat0 x0))%z.
Proof.
  intros x7 x6 x5 x4 x3 x2 x1 x0.
  match &x7 with | Zero | One end;
    match &x6 with | Zero | One end;
    match &x5 with | Zero | One end;
    match &x4 with | Zero | One end;
    match &x3 with | Zero | One end;
    match &x2 with | Zero | One end;
    match &x1 with | Zero | One end;
    match &x0 with | Zero | One end;
    ipso (Identity.reflexivity _).
Qed.

End right. (* conversion.right *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Int8} {y : Int8} {z : Int8} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (Integer.order.strict.transitivity &h1 &h2).
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
  let proof s := Integer.comparison.specification (to_integer &x) (to_integer &y).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru to_integer, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : Int8) (y : Int8) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (Integer.comparison.antisymmetry (to_integer &x) (to_integer &y)).
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
