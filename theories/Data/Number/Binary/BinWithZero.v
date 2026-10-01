(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianMonoid.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Algebra.Semiring.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Binary.BinBase.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Descent.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [BinWithZero.add].
 * The type and its ctors are declared inside it: [Nat0] and [Integer]
 * declare [Zero] and [Positive] too, and across files a duplicate ctor name
 * rebinds the bare one silently and with no warning.
 *)
Module BinWithZero. (* BinWithZero *)

(* [Positive] wraps a [BinBase], so addition, multiplication, powers, comparison
 * and subtraction here reduce to the [BinBase] operation plus the [Zero] cases,
 * as [Nat0] does over [Nat].
 *)
Inductive T : Type :=
  | Zero     : T
  | Positive : BinBase -> T.

(* The carrier is named [T] so that the type itself reads [BinWithZero] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End BinWithZero].
 *)
Abbreviation BinWithZero := T.

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] is a prefix, apart from the infix [+].
 *)
Local Notation "0" := Zero (only parsing).
Local Notation "+ p" := (Positive p)
  (at level 35, right associativity, only parsing).

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition add := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => + (p + q)%bin_base
      end
  end.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition mul := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => + (p * q)%bin_base
      end
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End BinWithZero] a client writes [(m + n)%bin_with_zero].
 * [only parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_bin_with_zero_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_bin_with_zero_scope.

Local Open Scope jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero] *)
Definition inc := fun (n : BinWithZero) .
  match n with
  | 0   => + BinBase.One
  | + p => + (BinBase.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition power := fun (m : BinWithZero) (n : BinWithZero) .
  match n with
  | 0   => + BinBase.One
  | + q =>
      match m with
      | 0   => 0
      | + p => + (p ^ q)%bin_base
      end
  end.

Notation "m ^ n" := (power m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> Prop] *)
Definition LessThan := fun (m : BinWithZero) (n : BinWithZero) .
  forsome (k : BinBase) . m + (+ k) = n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> Prop] *)
Definition LessOrEqual := fun (m : BinWithZero) (n : BinWithZero) .
  m = n \/ m < n.

Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_bin_with_zero_scope.

Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_bin_with_zero_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_bin_with_zero_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_bin_with_zero_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> Comparison] *)
Definition compare := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match n with
      | 0   => Comparison.Gt
      | + q => BinBase.compare p q
      end
  end.

(* [BinWithZero -> BinWithZero -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [BinWithZero -> BinWithZero -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Abbreviation min := (Comparable.min compare).

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Abbreviation max := (Comparable.max compare).

(* [m - n], [None] when [n] is the greater, as [Nat0.sub] is. *)
(* [BinWithZero -> BinWithZero -> Option BinWithZero] *)
Definition sub := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Some 0
      | + _ => None
      end
  | + p =>
      match n with
      | 0   => Some (+ p)
      | + q =>
          match BinBase.diff p q with
          | BinBase.Lt   => None
          | BinBase.Eq   => Some 0
          | BinBase.Gt d => Some (+ d)
          end
      end
  end.

(* [m - n], and [0] where [sub] has nothing. *)
(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition saturating_sub := fun (m : BinWithZero) (n : BinWithZero) .
  match sub m n with
  | Some k => k
  | None   => 0
  end.

(* [BinWithZero -> Option BinBase] *)
Definition to_bin_base := fun (n : BinWithZero) .
  match n with
  | 0   => None
  | + p => Some p
  end.

(* [n] with [bit] written after its lowest bit: [2n], or [2n + 1] when [bit]
 * is [true].
 *)
(* [Bool -> BinWithZero -> BinWithZero] *)
Definition append_bit := fun (bit : Bool) (n : BinWithZero) .
  match n with
  | 0 =>
      match bit with
      | true  => + BinBase.One
      | false => 0
      end
  | + p =>
      match bit with
      | true  => + BinBase.b1 p
      | false => + BinBase.b0 p
      end
  end.

(* Every number is [0] or a number with a bit appended, so a law holds of
 * every number once it holds of [0] and survives the appending.
 *)
Definition induction
  : forall (P : BinWithZero -> Prop) .
      P 0 ->
      (forall (bit : Bool) (n : BinWithZero) . P n -> P (append_bit bit n)) ->
      forall (n : BinWithZero) . P n
  := fun (P : BinWithZero -> Prop)
         (zero : P 0)
         (step : forall (bit : Bool) (n : BinWithZero) . P n -> P (append_bit bit n))
         (n : BinWithZero) .
       match n with
       | 0   => zero
       | + p =>
           BinBase.induction (fun (q : BinBase) . P (+ q))
             (step true 0 zero)
             (fun (q : BinBase) (h : P (+ q)) . step false (+ q) h)
             (fun (q : BinBase) (h : P (+ q)) . step true (+ q) h)
             p
       end.

(* [n] with its lowest bit dropped. *)
(* [BinWithZero -> BinWithZero] *)
Definition halve := fun (n : BinWithZero) .
  match n with
  | 0              => 0
  | + BinBase.One  => 0
  | + BinBase.b0 p => + p
  | + BinBase.b1 p => + p
  end.

Local Open Scope jwa_product_scope.

(* One step of long division: [bit] is written after the remainder, and the
 * divisor [d] is taken away from the result when it fits, the quotient
 * gaining a 1 in that case and a 0 otherwise.
 *)
(* [Bool -> Product BinWithZero BinWithZero -> BinBase -> Product BinWithZero BinWithZero] *)
Definition bring_down := fun (bit : Bool) (x : Product BinWithZero BinWithZero) (d : BinBase) .
  match x with
  | (quotient, remainder) =>
      match sub (append_bit bit remainder) (+ d) with
      | Some remainder' => (append_bit true quotient, remainder')
      | None            => (append_bit false quotient, append_bit bit remainder)
      end
  end.

(* Long division of [p] by [d], the bits of [p] brought down from the
 * leading one.
 *)
(* [BinBase -> BinBase -> Product BinWithZero BinWithZero] *)
Fixpoint div_positive (p : BinBase) (d : BinBase) : Product BinWithZero BinWithZero :=
  match p with
  | BinBase.One   => bring_down true (0, 0) d
  | BinBase.b0 p' => bring_down false (div_positive p' d) d
  | BinBase.b1 p' => bring_down true (div_positive p' d) d
  end.

(* The quotient and the remainder of [n] by [d]. The divisor is a [BinBase], so
 * it is never zero.
 *)
(* [BinWithZero -> BinBase -> Product BinWithZero BinWithZero] *)
Definition div := fun (n : BinWithZero) (d : BinBase) .
  match n with
  | 0   => (0, 0)
  | + p => div_positive p d
  end.

(* [BinWithZero -> BinBase -> BinWithZero] *)
Definition divide := fun (n : BinWithZero) (d : BinBase) . pi_1 (div n d).

(* [BinWithZero -> BinBase -> BinWithZero] *)
Definition modulo := fun (n : BinWithZero) (d : BinBase) . pi_2 (div n d).

Notation "m /. n" := (divide m n) (only parsing)
  : jwa_bin_with_zero_scope.
Notation "m %. n" := (modulo m n) (only parsing)
  : jwa_bin_with_zero_scope.

Local Close Scope jwa_product_scope.

(* [d] divides [n] when some multiple of [d] is [n]. *)
(* [BinWithZero -> BinWithZero -> Prop] *)
Definition Divides := fun (d : BinWithZero) (n : BinWithZero) .
  forsome (k : BinWithZero) . d * k = n.

(* Euclid's algorithm on [a] and [b], two steps for each bit of [fuel] below
 * its leading one. Two steps at least halve [b], so while [b] is at most
 * [fuel] the steps never run out: at [BinBase.One], [b] is [0] or [1], and [1]
 * divides [a].
 *)
(* [BinBase -> BinWithZero -> BinWithZero -> BinWithZero] *)
Fixpoint gcd_with_fuel (fuel : BinBase) (a : BinWithZero) (b : BinWithZero) : BinWithZero :=
  match b with
  | 0   => a
  | + q =>
      match fuel with
      | BinBase.One                 => + q
      | BinBase.b0 f | BinBase.b1 f =>
          match a %. q with
          | 0   => + q
          | + r => gcd_with_fuel f (+ r) ((+ q) %. r)
          end
      end
  end.

(* The greatest common divisor, [b] itself serving as the fuel. *)
(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition gcd := fun (a : BinWithZero) (b : BinWithZero) .
  match b with
  | 0   => a
  | + q => gcd_with_fuel q a (+ q)
  end.

(* Bit by bit from the least significant end, a number reading as 0s past
 * its leading 1; the bits of the result may all be 0.
 *)
(* [BinBase -> BinBase -> BinWithZero] *)
Fixpoint and_positive (p : BinBase) (q : BinBase) : BinWithZero :=
  match p, q with
  | BinBase.One, BinBase.One     => + BinBase.One
  | BinBase.One, BinBase.b0 _    => 0
  | BinBase.One, BinBase.b1 _    => + BinBase.One
  | BinBase.b0 _, BinBase.One    => 0
  | BinBase.b0 p', BinBase.b0 q' => append_bit false (and_positive p' q')
  | BinBase.b0 p', BinBase.b1 q' => append_bit false (and_positive p' q')
  | BinBase.b1 _, BinBase.One    => + BinBase.One
  | BinBase.b1 p', BinBase.b0 q' => append_bit false (and_positive p' q')
  | BinBase.b1 p', BinBase.b1 q' => append_bit true (and_positive p' q')
  end.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition and := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => and_positive p q
      end
  end.

Notation "m && n" := (and m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* As [and_positive], each bit the disjunction of the two. *)
(* [BinBase -> BinBase -> BinWithZero] *)
Fixpoint or_positive (p : BinBase) (q : BinBase) : BinWithZero :=
  match p, q with
  | BinBase.One, BinBase.One     => + BinBase.One
  | BinBase.One, BinBase.b0 q'   => + BinBase.b1 q'
  | BinBase.One, BinBase.b1 q'   => + BinBase.b1 q'
  | BinBase.b0 p', BinBase.One   => + BinBase.b1 p'
  | BinBase.b0 p', BinBase.b0 q' => append_bit false (or_positive p' q')
  | BinBase.b0 p', BinBase.b1 q' => append_bit true (or_positive p' q')
  | BinBase.b1 p', BinBase.One   => + BinBase.b1 p'
  | BinBase.b1 p', BinBase.b0 q' => append_bit true (or_positive p' q')
  | BinBase.b1 p', BinBase.b1 q' => append_bit true (or_positive p' q')
  end.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition or := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => or_positive p q
      end
  end.

Notation "m || n" := (or m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* As [and_positive], each bit the exclusive disjunction of the two. *)
(* [BinBase -> BinBase -> BinWithZero] *)
Fixpoint xor_positive (p : BinBase) (q : BinBase) : BinWithZero :=
  match p, q with
  | BinBase.One, BinBase.One     => 0
  | BinBase.One, BinBase.b0 q'   => + BinBase.b1 q'
  | BinBase.One, BinBase.b1 q'   => + BinBase.b0 q'
  | BinBase.b0 p', BinBase.One   => + BinBase.b1 p'
  | BinBase.b0 p', BinBase.b0 q' => append_bit false (xor_positive p' q')
  | BinBase.b0 p', BinBase.b1 q' => append_bit true (xor_positive p' q')
  | BinBase.b1 p', BinBase.One   => + BinBase.b0 p'
  | BinBase.b1 p', BinBase.b0 q' => append_bit true (xor_positive p' q')
  | BinBase.b1 p', BinBase.b1 q' => append_bit false (xor_positive p' q')
  end.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition xor := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => xor_positive p q
      end
  end.

Notation "m ^^ n" := (xor m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> Nat -> BinWithZero] *)
Fixpoint shift_left_nat (n : BinWithZero) (k : Nat) : BinWithZero :=
  match k with
  | Nat.One          => append_bit false n
  | Nat.Successor k' => append_bit false (shift_left_nat n k')
  end.

(* [n] with [k] 0s appended, [n * 2 ^ k]. *)
(* [BinWithZero -> Nat0 -> BinWithZero] *)
Definition shift_left := fun (n : BinWithZero) (k : Nat0) .
  match k with
  | Nat0.Zero        => n
  | Nat0.Positive k' => shift_left_nat n k'
  end.

(* [BinWithZero -> Nat -> BinWithZero] *)
Fixpoint shift_right_nat (n : BinWithZero) (k : Nat) : BinWithZero :=
  match k with
  | Nat.One          => halve n
  | Nat.Successor k' => shift_right_nat (halve n) k'
  end.

(* [n] with its [k] lowest bits dropped. *)
(* [BinWithZero -> Nat0 -> BinWithZero] *)
Definition shift_right := fun (n : BinWithZero) (k : Nat0) .
  match k with
  | Nat0.Zero        => n
  | Nat0.Positive k' => shift_right_nat n k'
  end.

(* Bit [i] of [n], [true] for 1, counted from 0 at the lowest bit. *)
(* [BinWithZero -> Nat0 -> Bool] *)
Definition test_bit := fun (n : BinWithZero) (i : Nat0) .
  match shift_right n i with
  | 0              => false
  | + BinBase.One  => true
  | + BinBase.b0 _ => false
  | + BinBase.b1 _ => true
  end.

(* [n] with the digits [d] appended, [None] once a digit is neither 0 nor 1. *)
(* [BinWithZero -> Numeral.Decimal.Digits -> Option BinWithZero] *)
Fixpoint from_digits (n : BinWithZero) (d : Numeral.Decimal.Digits)
  : Option BinWithZero :=
  match d with
  | Numeral.Decimal.Digits.End     => Some n
  | Numeral.Decimal.Digits.Zero d' => from_digits (append_bit false n) d'
  | Numeral.Decimal.Digits.One d'  => from_digits (append_bit true  n) d'
  | _                              => None
  end.

(* The number a literal's digits spell in binary. *)
(* [Numeral.Unsigned -> Option BinWithZero] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal d     => from_digits 0 d
  | Numeral.Unsigned.Hexadecimal _ => None
  end.

(* [BinWithZero -> Numeral.Unsigned] *)
Definition to_numeral := fun (n : BinWithZero) .
  match n with
  | 0   => Numeral.Unsigned.Decimal (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End)
  | + p => BinBase.to_numeral p
  end.

(* [n] with the decimal digits [d] appended, the most significant first, each
 * step [n * 1010 + d] in binary digits.
 *)
(* [BinWithZero -> Numeral.Decimal.Digits -> BinWithZero] *)
Fixpoint from_decimal (n : BinWithZero) (d : Numeral.Decimal.Digits) : BinWithZero :=
  match d with
  | Numeral.Decimal.Digits.End      => n
  | Numeral.Decimal.Digits.Zero d'  => from_decimal (n * (+ 1010%bin_base)) d'
  | Numeral.Decimal.Digits.One d'   => from_decimal (n * (+ 1010%bin_base) + (+ 1%bin_base)) d'
  | Numeral.Decimal.Digits.Two d'   => from_decimal (n * (+ 1010%bin_base) + (+ 10%bin_base)) d'
  | Numeral.Decimal.Digits.Three d' => from_decimal (n * (+ 1010%bin_base) + (+ 11%bin_base)) d'
  | Numeral.Decimal.Digits.Four d'  =>
      from_decimal (n * (+ 1010%bin_base) + (+ 100%bin_base)) d'
  | Numeral.Decimal.Digits.Five d'  =>
      from_decimal (n * (+ 1010%bin_base) + (+ 101%bin_base)) d'
  | Numeral.Decimal.Digits.Six d'   =>
      from_decimal (n * (+ 1010%bin_base) + (+ 110%bin_base)) d'
  | Numeral.Decimal.Digits.Seven d' =>
      from_decimal (n * (+ 1010%bin_base) + (+ 111%bin_base)) d'
  | Numeral.Decimal.Digits.Eight d' =>
      from_decimal (n * (+ 1010%bin_base) + (+ 1000%bin_base)) d'
  | Numeral.Decimal.Digits.Nine d'  =>
      from_decimal (n * (+ 1010%bin_base) + (+ 1001%bin_base)) d'
  end.

(* [n] with the hexadecimal digits [h] appended, the most significant first,
 * each step [n * 10000 + h] in binary digits.
 *)
(* [BinWithZero -> Numeral.Hexadecimal.Digits -> BinWithZero] *)
Fixpoint from_hexadecimal (n : BinWithZero) (h : Numeral.Hexadecimal.Digits) : BinWithZero :=
  match h with
  | Numeral.Hexadecimal.Digits.End         => n
  | Numeral.Hexadecimal.Digits.Zero h'     =>
      from_hexadecimal (n * (+ 10000%bin_base)) h'
  | Numeral.Hexadecimal.Digits.One h'      =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Two h'      =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 10%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Three h'    =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 11%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Four h'     =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 100%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Five h'     =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 101%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Six h'      =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 110%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Seven h'    =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 111%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Eight h'    =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1000%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Nine h'     =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1001%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Ten h'      =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1010%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Eleven h'   =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1011%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Twelve h'   =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1100%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Thirteen h' =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1101%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Fourteen h' =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1110%bin_base)) h'
  | Numeral.Hexadecimal.Digits.Fifteen h'  =>
      from_hexadecimal (n * (+ 10000%bin_base) + (+ 1111%bin_base)) h'
  end.

(* The digit [high] before [rest] when [carry] is set, [low] otherwise. *)
(* [Bool -> (Numeral.Decimal.Digits -> Numeral.Decimal.Digits)
 *   -> (Numeral.Decimal.Digits -> Numeral.Decimal.Digits)
 *   -> Numeral.Decimal.Digits -> Numeral.Decimal.Digits]
 *)
Definition select_digit :=
  fun (carry : Bool)
      (low : Numeral.Decimal.Digits -> Numeral.Decimal.Digits)
      (high : Numeral.Decimal.Digits -> Numeral.Decimal.Digits)
      (rest : Numeral.Decimal.Digits) .
    match carry with
    | true  => high rest
    | false => low rest
    end.

(* The carry out and the digits of twice [d] plus [carry], [d] the most
 * significant digit first: [carry] goes in at the lowest digit and each
 * digit passes its own carry up.
 *)
(* [Bool -> Numeral.Decimal.Digits -> Product Bool Numeral.Decimal.Digits] *)
Fixpoint double_decimal (carry : Bool) (d : Numeral.Decimal.Digits)
  : Product Bool Numeral.Decimal.Digits :=
  match d with
  | Numeral.Decimal.Digits.End      => (carry, Numeral.Decimal.Digits.End)
  | Numeral.Decimal.Digits.Zero d'  =>
      let r := double_decimal carry d' in
      (false,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.One (pi_2 r))
  | Numeral.Decimal.Digits.One d'   =>
      let r := double_decimal carry d' in
      (false,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Two Numeral.Decimal.Digits.Three (pi_2 r))
  | Numeral.Decimal.Digits.Two d'   =>
      let r := double_decimal carry d' in
      (false,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Four Numeral.Decimal.Digits.Five (pi_2 r))
  | Numeral.Decimal.Digits.Three d' =>
      let r := double_decimal carry d' in
      (false,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Six Numeral.Decimal.Digits.Seven (pi_2 r))
  | Numeral.Decimal.Digits.Four d'  =>
      let r := double_decimal carry d' in
      (false,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Eight Numeral.Decimal.Digits.Nine (pi_2 r))
  | Numeral.Decimal.Digits.Five d'  =>
      let r := double_decimal carry d' in
      (true,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.One (pi_2 r))
  | Numeral.Decimal.Digits.Six d'   =>
      let r := double_decimal carry d' in
      (true,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Two Numeral.Decimal.Digits.Three (pi_2 r))
  | Numeral.Decimal.Digits.Seven d' =>
      let r := double_decimal carry d' in
      (true,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Four Numeral.Decimal.Digits.Five (pi_2 r))
  | Numeral.Decimal.Digits.Eight d' =>
      let r := double_decimal carry d' in
      (true,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Six Numeral.Decimal.Digits.Seven (pi_2 r))
  | Numeral.Decimal.Digits.Nine d'  =>
      let r := double_decimal carry d' in
      (true,
        select_digit (pi_1 r) Numeral.Decimal.Digits.Eight Numeral.Decimal.Digits.Nine (pi_2 r))
  end%product.

(* The decimal digits of [p], built bit by bit from the most significant: each
 * bit doubles the digits so far and adds itself, so no division is needed.
 *)
(* [BinBase -> Numeral.Decimal.Digits] *)
Fixpoint to_decimal_positive (p : BinBase) : Numeral.Decimal.Digits :=
  let grow := fun (r : Product Bool Numeral.Decimal.Digits) .
    (select_digit (pi_1 r) (fun (rest : Numeral.Decimal.Digits) . rest)
      Numeral.Decimal.Digits.One (pi_2 r))%product in
  match p with
  | BinBase.One   => Numeral.Decimal.Digits.One Numeral.Decimal.Digits.End
  | BinBase.b0 p' => grow (double_decimal false (to_decimal_positive p'))
  | BinBase.b1 p' => grow (double_decimal true (to_decimal_positive p'))
  end.

(* [n] in decimal digits, the most significant first. *)
(* [BinWithZero -> Numeral.Decimal.Digits] *)
Definition to_decimal := fun (n : BinWithZero) .
  match n with
  | 0   => Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End
  | + p => to_decimal_positive p
  end.

(* The conversions to and from [Nat0], used to state the laws: they
 * go through [Nat], which is unary, so they are for proofs, not for
 * computing.
 *)
(* [BinWithZero -> Nat0] *)
Definition to_nat0 := fun (n : BinWithZero) .
  match n with
  | 0   => Nat0.Zero
  | + p => Nat0.Positive (BinBase.to_nat p)
  end.

(* [Nat0 -> BinWithZero] *)
Definition from_nat0 := fun (n : Nat0) .
  match n with
  | Nat0.Zero       => 0
  | Nat0.Positive p => + BinBase.from_nat p
  end.

Module conversion. (* conversion *)

(* conversion.successor *)
Theorem successor
  : forall (n : BinWithZero) .
      to_nat0 (++ n) = Nat0.inc (to_nat0 n).
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (BinBase.conversion.successor &p) in |- *.
    simpl Nat.inc in |- *.
    quod idem est.
Qed.

(* conversion.retraction *)
Theorem retraction
  : forall (n : Nat0) . to_nat0 (from_nat0 n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (BinBase.conversion.retraction &p) in |- *.
    quod idem est.
Qed.

(* conversion.section *)
Theorem section
  : forall (n : BinWithZero) . from_nat0 (to_nat0 n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (BinBase.conversion.section &p) in |- *.
    quod idem est.
Qed.

(* conversion.addition *)
Theorem addition
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat0 (m + n)
      = (to_nat0 m + to_nat0 n)%n0.
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    let proof e := BinBase.conversion.addition &p &q.
    simpl in |- *.
    leibniz &e in |- *.
    quod idem est.
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat0 (m * n)
      = (to_nat0 m * to_nat0 n)%n0.
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (BinBase.conversion.multiplication &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.power *)
Theorem power
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat0 (m ^ n)
      = (to_nat0 m ^ to_nat0 n)%n0.
Proof.
  intros m n.
  match n with | | q end; match m with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (BinBase.conversion.power &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (m : BinWithZero) (n : BinWithZero) .
      compare m n = Nat0.compare (to_nat0 m) (to_nat0 n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    ipso (BinBase.conversion.comparison &p &q).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (m : BinWithZero) (n : BinWithZero) .
      Option.map to_nat0 (sub m n)
      = Nat0.sub (to_nat0 m) (to_nat0 n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    lemma sum
      : (Nat0.Zero + Nat0.Zero)%n0 = Nat0.Zero.
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (Nat0.subtraction.specification
         Nat0.Zero Nat0.Zero Nat0.Zero),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma below
      : (Nat0.Zero < Nat0.Positive (BinBase.to_nat &q))%n0.
    {
      simpl Nat0.LessThan in |- *.
      exists (BinBase.to_nat &q).
      simpl in |- *.
      quod idem est.
    }
    leibniz (Nat0.subtraction.truncation &below) in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma sum
      : (Nat0.Zero + Nat0.Positive (BinBase.to_nat &p))%n0
        = Nat0.Positive (BinBase.to_nat &p).
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (Nat0.subtraction.specification
         (Nat0.Positive (BinBase.to_nat &p)) Nat0.Zero
         (Nat0.Positive (BinBase.to_nat &p))),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    let proof h := BinBase.conversion.difference &p &q.
    extro &h.
    match (BinBase.diff &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      lemma below
        : (Nat0.Positive (BinBase.to_nat &p)
           < Nat0.Positive (BinBase.to_nat &q))%n0.
      {
        simpl Nat0.LessThan in |- *.
        simpl Nat.LessThan in &h.
        match &h with | k e end.
        exists &k.
        simpl in |- *.
        leibniz &e in |- *.
        quod idem est.
      }
      leibniz (Nat0.subtraction.truncation &below) in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (Nat0.Positive (BinBase.to_nat &q) + Nat0.Zero)%n0
          = Nat0.Positive (BinBase.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (Nat0.subtraction.specification
           (Nat0.Positive (BinBase.to_nat &p))
           (Nat0.Positive (BinBase.to_nat &q)) Nat0.Zero),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (Nat0.Positive (BinBase.to_nat &q)
           + Nat0.Positive (BinBase.to_nat &d))%n0
          = Nat0.Positive (BinBase.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (Nat0.subtraction.specification
           (Nat0.Positive (BinBase.to_nat &p))
           (Nat0.Positive (BinBase.to_nat &q))
           (Nat0.Positive (BinBase.to_nat &d))),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
Qed.

Module subtraction. (* conversion.subtraction *)

(* conversion.subtraction.saturating *)
Theorem saturating
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat0 (saturating_sub m n)
      = Nat0.saturating_sub (to_nat0 m) (to_nat0 n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    simpl saturating_sub, sub in |- *.
    let proof h := BinBase.conversion.difference &p &q.
    extro &h.
    match (BinBase.diff &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      let proof le : (BinBase.to_nat &p <= BinBase.to_nat &q)%n := disjoin _, &h.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      let proof le : (BinBase.to_nat &p <= BinBase.to_nat &q)%n := disjoin &h, _.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      leibniz <- &h in |- *.
      leibniz (Nat.addition.commutativity (BinBase.to_nat &q) (BinBase.to_nat &d)) in |- *.
      leibniz (Nat.subtraction.inversion.of.addition (BinBase.to_nat &d) (BinBase.to_nat &q))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End subtraction. (* conversion.subtraction *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {m : BinWithZero} {n : BinWithZero} .
      to_nat0 m = to_nat0 n -> m = n.
Proof.
  intros m n e.
  leibniz <- (conversion.section &m), <- (conversion.section &n) in |- *.
  leibniz &e in |- *.
  quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (m : BinWithZero) (n : BinWithZero) .
      m < n <-> (to_nat0 m < to_nat0 n)%n0.
Proof.
  intros m n.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Nat0.LessThan in |- *.
    exists (BinBase.to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &m (+ &k)) in |- *.
    simpl in |- *.
    quod idem est.
  -
    intro h.
    simpl Nat0.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (BinBase.from_nat &j).
    lemma f : to_nat0 (&m + (+ BinBase.from_nat &j)) = to_nat0 &n.
    {
      leibniz (conversion.addition &m (+ BinBase.from_nat &j)) in |- *.
      simpl in |- *.
      leibniz (BinBase.conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

(* conversion.appending *)
Theorem appending
  : forall (bit : Bool) (n : BinWithZero) .
      to_nat0 (append_bit bit n)
      = match bit with
        | true  => Nat0.inc (to_nat0 n + to_nat0 n)%n0
        | false => (to_nat0 n + to_nat0 n)%n0
        end.
Proof.
  intros bit n.
  match n with | | p end.
  -
    match bit with | | end.
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
  -
    match bit with | | end.
    +
      simpl in |- *.
      simpl Nat.inc in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
Qed.

(* conversion.halving *)
Theorem halving
  : forall (n : BinWithZero) .
      to_nat0 (halve n) = (to_nat0 n /. Nat.Successor Nat.One)%n0.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl Nat0.divide, Nat0.div in |- *.
    simpl in |- *.
    quod idem est.
  -
    match p with | | p' | p' end.
    +
      simpl Nat0.divide, Nat0.div in |- *.
      simpl in |- *.
      quod idem est.
    +
      lemma witness
        : ((to_nat0 (+ &p') * Nat.Successor Nat.One) + Nat0.Zero
            = to_nat0 (+ BinBase.b0 &p'))%n0
          /\ (Nat0.Zero < Nat.Successor Nat.One)%n0.
      {
        divide et impera.
        -
          simpl in |- *.
          leibniz (Nat.multiplication.commutativity (BinBase.to_nat &p') (Nat.Successor Nat.One))
            in |- *.
          simpl in |- *.
          quod idem est.
        -
          simpl Nat0.LessThan in |- *.
          exists (Nat.Successor Nat.One).
          simpl in |- *.
          quod idem est.
      }
      match (Nat0.division.uniqueness
          (to_nat0 (+ BinBase.b0 &p')) (Nat.Successor Nat.One)
          (to_nat0 (+ &p')) Nat0.Zero &witness)
        with | quotient _ end.
      simpl halve in |- *.
      ipso (symm &quotient).
    +
      lemma witness
        : ((to_nat0 (+ &p') * Nat.Successor Nat.One) + Nat.One
            = to_nat0 (+ BinBase.b1 &p'))%n0
          /\ (Nat.One < Nat.Successor Nat.One)%n0.
      {
        divide et impera.
        -
          simpl in |- *.
          leibniz (Nat.multiplication.commutativity (BinBase.to_nat &p') (Nat.Successor Nat.One)),
            (Nat.addition.commutativity (Nat.Successor Nat.One * BinBase.to_nat &p')%n Nat.One)
            in |- *.
          simpl in |- *.
          quod idem est.
        -
          simpl Nat0.LessThan in |- *.
          exists Nat.One.
          simpl in |- *.
          quod idem est.
      }
      match (Nat0.division.uniqueness
          (to_nat0 (+ BinBase.b1 &p')) (Nat.Successor Nat.One)
          (to_nat0 (+ &p')) Nat.One &witness)
        with | quotient _ end.
      simpl halve in |- *.
      ipso (symm &quotient).
Qed.

Module left. (* conversion.left *)

(* conversion.left.shift *)
Theorem shift
  : forall (n : BinWithZero) (k : Nat0) .
      to_nat0 (shift_left n k)
      = (to_nat0 n
         * Nat0.Positive (Nat.Successor Nat.One) ^ k)%n0.
Proof.
  intros n k.
  match k with | | k' end.
  -
    simpl shift_left, Nat0.power in |- *.
    let proof i := Nat0.multiplication.identity (to_nat0 &n).
    match &i with | l r end.
    leibniz &r in |- *.
    quod idem est.
  -
    simpl shift_left in |- *.
    match n with | | p end.
    +
      match k' with | | k'' by IH end per Nat.induction.
      *
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl in &IH.
        leibniz (conversion.appending false (shift_left_nat 0 &k'')) in |- *.
        simpl in |- *.
        leibniz &IH in |- *.
        simpl in |- *.
        quod idem est.
    +
      match k' with | | k'' by IH end per Nat.induction.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.commutativity
                   (BinBase.to_nat &p) (Nat.Successor Nat.One)) in |- *.
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl in &IH.
        leibniz (conversion.appending false (shift_left_nat (+ &p) &k'')) in |- *.
        simpl in |- *.
        leibniz &IH in |- *.
        simpl in |- *.
        leibniz (Nat.multiplication.left.distributivity.over.addition
                   (BinBase.to_nat &p)
                   (Nat.power (Nat.Successor Nat.One) &k'')
                   (Nat.power (Nat.Successor Nat.One) &k'')) in |- *.
        quod idem est.
Qed.

End left. (* conversion.left *)

Module right. (* conversion.right *)

(* conversion.right.shift *)
Theorem shift
  : forall (n : BinWithZero) (k : Nat) .
      to_nat0 (shift_right n k)
      = (to_nat0 n /. (Nat.Successor Nat.One ^ k)%n)%n0.
Proof.
  intros n k.
  extro &n.
  match k with | | k' by IH end per Nat.induction.
  -
    intro n.
    simpl shift_right, shift_right_nat, Nat.power in |- *.
    ipso (conversion.halving &n).
  -
    intro n.
    lemma unfolding : shift_right &n (Nat.Successor &k') = shift_right (halve &n) k'.
    {
      simpl in |- *.
      quod idem est.
    }
    lemma power
      : (Nat.Successor Nat.One ^ Nat.Successor &k')%n
        = (Nat.Successor Nat.One * Nat.Successor Nat.One ^ &k')%n.
    {
      simpl in |- *.
      quod idem est.
    }
    leibniz &unfolding, (&IH (halve &n)), (conversion.halving &n), &power in |- *.
    ipso (Nat0.division.iteration
      (to_nat0 &n) (Nat.Successor Nat.One) (Nat.Successor Nat.One ^ &k')%n).
Qed.

End right. (* conversion.right *)

Local Open Scope jwa_product_scope.

Module division. (* conversion.division *)

(* conversion.division.step *)
Lemma step
  : forall (bit : Bool) (x : Product BinWithZero BinWithZero) (d : BinBase) (n : BinWithZero) .
      ((to_nat0 (pi_1 x) * BinBase.to_nat d) + to_nat0 (pi_2 x)
        = to_nat0 n)%n0
      /\ (to_nat0 (pi_2 x) < BinBase.to_nat d)%n0 ->
      ((to_nat0 (pi_1 (bring_down bit x d)) * BinBase.to_nat d)
        + to_nat0 (pi_2 (bring_down bit x d))
        = to_nat0 (append_bit bit n))%n0
      /\ (to_nat0 (pi_2 (bring_down bit x d)) < BinBase.to_nat d)%n0.
Proof.
  intros bit x d n h.
  match x with | q r end.
  simpl Product.first, Product.second in &h.
  match &h with | e below end.
  lemma doubling
    : (((to_nat0 &q + to_nat0 &q) * BinBase.to_nat &d)
        + (to_nat0 &r + to_nat0 &r)
        = to_nat0 &n + to_nat0 &n)%n0.
  {
    leibniz (Nat0.multiplication.right.distributivity.over.addition
      (BinBase.to_nat &d) (to_nat0 &q) (to_nat0 &q)) in |- *.
    leibniz (Nat0.addition.interchange
      (to_nat0 &q * BinBase.to_nat &d)%n0 (to_nat0 &q * BinBase.to_nat &d)%n0
      (to_nat0 &r) (to_nat0 &r)) in |- *.
    leibniz &e in |- *.
    quod idem est.
  }
  lemma sum
    : (((to_nat0 &q + to_nat0 &q) * BinBase.to_nat &d)
        + to_nat0 (append_bit &bit &r)
        = to_nat0 (append_bit &bit &n))%n0.
  {
    leibniz (conversion.appending &bit &r), (conversion.appending &bit &n) in |- *.
    match bit with | | end.
    -
      leibniz (Nat0.increment.specification
          (to_nat0 &r + to_nat0 &r)%n0),
        (Nat0.increment.specification
          (to_nat0 &n + to_nat0 &n)%n0) in |- *.
      leibniz (Nat0.addition.left.commutativity
        ((to_nat0 &q + to_nat0 &q) * BinBase.to_nat &d)%n0 Nat.One
        (to_nat0 &r + to_nat0 &r)%n0) in |- *.
      leibniz &doubling in |- *.
      quod idem est.
    -
      ipso &doubling.
  }
  lemma bound
    : (to_nat0 (append_bit &bit &r) < BinBase.to_nat &d + BinBase.to_nat &d)%n0.
  {
    simpl Nat0.LessThan in &below.
    match &below with | k ek end.
    leibniz <- &ek in |- *.
    leibniz (Nat0.addition.interchange (to_nat0 &r) k (to_nat0 &r) k)
      in |- *.
    leibniz (conversion.appending &bit &r) in |- *.
    match bit with | | end.
    -
      leibniz (Nat0.increment.specification
          (to_nat0 &r + to_nat0 &r)%n0),
        (Nat0.addition.commutativity Nat.One
          (to_nat0 &r + to_nat0 &r)%n0) in |- *.
      lemma one : (Nat.One < k + k)%n0.
      {
        simpl Nat0.LessThan in |- *.
        match k with | | k' end.
        +
          exists Nat.One.
          quod idem est.
        +
          exists (&k' + Nat.Successor &k')%n.
          simpl in |- *.
          quod idem est.
      }
      ipso (Nat0.addition.order.strict.monotonicity
        (to_nat0 &r + to_nat0 &r)%n0 Nat.One (k + k)%n0 &one).
    -
      simpl Nat0.LessThan in |- *.
      exists (&k + &k)%n.
      simpl in |- *.
      quod idem est.
  }
  simpl bring_down in |- *.
  let proof s := conversion.subtraction (append_bit &bit &r) (+ &d).
  extro &s.
  match (sub (append_bit &bit &r) (+ &d)) with | | r' end.
  -
    intro s.
    let proof s
      : None = Nat0.sub (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d)
      := &s.
    simpl Product.first, Product.second in |- *.
    let proof a
      : to_nat0 (append_bit false &q) = (to_nat0 &q + to_nat0 &q)%n0
      := conversion.appending false &q.
    leibniz &a in |- *.
    divide et impera.
    +
      ipso &sum.
    +
      match (Comparable.order.strict.trichotomy
          (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d))
        with | less | rest end.
      *
        ipso &less.
      *
        match &rest with | same | greater end.
        {
          lemma plus
            : (BinBase.to_nat &d + Nat0.Zero = to_nat0 (append_bit &bit &r))%n0.
          {
            leibniz &same in |- *.
            simpl in |- *.
            quod idem est.
          }
          modus aequans
            (Nat0.subtraction.specification
              (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d) Nat0.Zero),
            &plus
          |- f.
          leibniz &f in &s.
          ex &s quodlibet.
        }
        {
          simpl Nat0.LessThan in &greater.
          match &greater with | k ek end.
          modus aequans
            (Nat0.subtraction.specification
              (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d) k),
            &ek
          |- f.
          leibniz &f in &s.
          ex &s quodlibet.
        }
  -
    intro s.
    let proof s
      : Nat0.sub (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d)
        = Some (to_nat0 &r')
      := symm &s.
    modus aequans
      (Nat0.subtraction.specification
        (to_nat0 (append_bit &bit &r)) (BinBase.to_nat &d) (to_nat0 &r')),
      &s
    |- f.
    simpl Product.first, Product.second in |- *.
    let proof a
      : to_nat0 (append_bit true &q)
        = Nat0.inc (to_nat0 &q + to_nat0 &q)%n0
      := conversion.appending true &q.
    leibniz &a in |- *.
    divide et impera.
    +
      leibniz (Nat0.increment.specification
        (to_nat0 &q + to_nat0 &q)%n0) in |- *.
      leibniz (Nat0.multiplication.right.distributivity.over.addition
        (BinBase.to_nat &d) Nat.One (to_nat0 &q + to_nat0 &q)%n0) in |- *.
      leibniz (Nat0.multiplication.left.identity (BinBase.to_nat &d)) in |- *.
      leibniz (Nat0.addition.commutativity
        (BinBase.to_nat &d) ((to_nat0 &q + to_nat0 &q) * BinBase.to_nat &d)%n0)
        in |- *.
      leibniz (Nat0.addition.associativity
        ((to_nat0 &q + to_nat0 &q) * BinBase.to_nat &d)%n0
        (BinBase.to_nat &d) (to_nat0 &r')) in |- *.
      leibniz &f in |- *.
      ipso &sum.
    +
      leibniz <- &f in &bound.
      ipso (Nat0.addition.order.strict.cancellation
        (BinBase.to_nat &d) (to_nat0 &r') (BinBase.to_nat &d) &bound).
Qed.

(* conversion.division.specification *)
Lemma specification
  : forall (n : BinWithZero) (d : BinBase) .
      ((to_nat0 (n /. d)%bin_with_zero * BinBase.to_nat d)
        + to_nat0 (n %. d)%bin_with_zero
        = to_nat0 n)%n0
      /\ (to_nat0 (n %. d)%bin_with_zero < BinBase.to_nat d)%n0.
Proof.
  intros n d.
  lemma base
    : ((to_nat0 (pi_1 (Zero, Zero)) * BinBase.to_nat &d) + to_nat0 (pi_2 (Zero, Zero))
        = to_nat0 Zero)%n0
      /\ (to_nat0 (pi_2 (Zero, Zero)) < BinBase.to_nat &d)%n0.
  {
    simpl in |- *.
    divide et impera.
    -
      quod idem est.
    -
      simpl Nat0.LessThan in |- *.
      exists (BinBase.to_nat &d).
      simpl in |- *.
      quod idem est.
  }
  match n with | | p end.
  -
    simpl divide, modulo, div in |- *.
    ipso &base.
  -
    simpl divide, modulo, div in |- *.
    match p with | | p' by IH | p' by IH end per BinBase.induction.
    +
      lemma unfolding : div_positive BinBase.One &d = bring_down true (0, 0) &d.
      {
        simpl in |- *.
        quod idem est.
      }
      lemma appended : + BinBase.One = append_bit true 0.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding, &appended in |- *.
      ipso (conversion.division.step true (0, 0) &d 0 &base).
    +
      lemma unfolding
        : div_positive (BinBase.b0 &p') &d = bring_down false (div_positive &p' &d) &d.
      {
        simpl in |- *.
        quod idem est.
      }
      lemma appended : + BinBase.b0 &p' = append_bit false (+ &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding, &appended in |- *.
      ipso (conversion.division.step false (div_positive &p' &d) &d (+ &p') &IH).
    +
      lemma unfolding
        : div_positive (BinBase.b1 &p') &d = bring_down true (div_positive &p' &d) &d.
      {
        simpl in |- *.
        quod idem est.
      }
      lemma appended : + BinBase.b1 &p' = append_bit true (+ &p').
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding, &appended in |- *.
      ipso (conversion.division.step true (div_positive &p' &d) &d (+ &p') &IH).
Qed.

End division. (* conversion.division *)

Local Close Scope jwa_product_scope.

(* conversion.division *)
Theorem division
  : forall (n : BinWithZero) (d : BinBase) .
      to_nat0 (n /. d) = (to_nat0 n /. BinBase.to_nat d)%n0.
Proof.
  intros n d.
  let proof u := Nat0.division.uniqueness
    (to_nat0 &n) (BinBase.to_nat &d)
    (to_nat0 (&n /. &d)) (to_nat0 (&n %. &d))
    (conversion.division.specification &n &d).
  match &u with | quotient _ end.
  ipso (symm &quotient).
Qed.

(* conversion.modulo *)
Theorem modulo
  : forall (n : BinWithZero) (d : BinBase) .
      to_nat0 (n %. d) = (to_nat0 n %. BinBase.to_nat d)%n0.
Proof.
  intros n d.
  let proof u := Nat0.division.uniqueness
    (to_nat0 &n) (BinBase.to_nat &d)
    (to_nat0 (&n /. &d)) (to_nat0 (&n %. &d))
    (conversion.division.specification &n &d).
  match &u with | _ remainder end.
  ipso (symm &remainder).
Qed.

(* conversion.divisibility *)
Theorem divisibility
  : forall (d : BinWithZero) (n : BinWithZero) .
      Divides d n <-> Nat0.Divides (to_nat0 d) (to_nat0 n).
Proof.
  intros d n.
  divide et impera.
  -
    intro h.
    simpl Divides in &h.
    match &h with | k e end.
    simpl Nat0.Divides in |- *.
    exists (to_nat0 &k).
    leibniz <- (conversion.multiplication &d &k), &e in |- *.
    quod idem est.
  -
    intro h.
    simpl Nat0.Divides in &h.
    match &h with | k e end.
    simpl Divides in |- *.
    exists (from_nat0 &k).
    lemma f : to_nat0 (&d * from_nat0 &k) = to_nat0 &n.
    {
      leibniz (conversion.multiplication &d (from_nat0 &k)), (conversion.retraction &k)
        in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

Module gcd. (* conversion.gcd *)

(* conversion.gcd.sufficiency *)
Lemma sufficiency
  : forall (fuel : BinBase) (a : BinWithZero) (b : BinWithZero) .
      (to_nat0 b <= BinBase.to_nat fuel)%n0 ->
      to_nat0 (gcd_with_fuel fuel a b)
      = Nat0.gcd (to_nat0 a) (to_nat0 b).
Proof.
  intro fuel.
  lemma nothing : to_nat0 0 = Nat0.Zero.
  {
    simpl in |- *.
    quod idem est.
  }
  lemma magnitude : forall (p : BinBase) . to_nat0 (+ p) = BinBase.to_nat p.
  {
    intro p.
    simpl in |- *.
    quod idem est.
  }
  lemma odd
    : forall (f : BinBase) .
        (forall (a : BinWithZero) (b : BinWithZero) .
          (to_nat0 b <= BinBase.to_nat f)%n0 ->
          to_nat0 (gcd_with_fuel f a b)
          = Nat0.gcd (to_nat0 a) (to_nat0 b)) ->
        forall (a : BinWithZero) (b : BinWithZero) .
          (to_nat0 b <= BinBase.to_nat (BinBase.b1 f))%n0 ->
          to_nat0 (gcd_with_fuel (BinBase.b1 f) a b)
          = Nat0.gcd (to_nat0 a) (to_nat0 b).
  {
    intros f IH a b h.
    match b with | | q end.
    -
      lemma facto : to_nat0 (gcd_with_fuel (BinBase.b1 &f) &a 0) = to_nat0 &a.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &facto, &nothing in |- *.
      ipso (symm (Nat0.gcd.zero (to_nat0 &a))).
    -
      leibniz (&magnitude &q) in &h.
      lemma unfolding
        : gcd_with_fuel (BinBase.b1 &f) &a (+ &q)
          = match &a %. &q with
            | 0   => + &q
            | + r => gcd_with_fuel &f (+ r) ((+ &q) %. r)
            end.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding in |- *.
      let proof rec
        : Nat0.gcd (to_nat0 &a) (to_nat0 (+ &q))
          = Nat0.gcd (to_nat0 (+ &q)) (to_nat0 &a %. BinBase.to_nat &q)%n0
        := Nat0.gcd.recurrence (to_nat0 &a) (BinBase.to_nat &q).
      leibniz <- (conversion.modulo &a &q) in &rec.
      leibniz &rec in |- *.
      let proof s
        := Nat0.division.remainder.boundedness (to_nat0 &a) (BinBase.to_nat &q).
      leibniz <- (conversion.modulo &a &q) in &s.
      extro &s.
      match (&a %. &q) with | | r end.
      +
        intro s.
        leibniz &nothing in |- *.
        ipso (symm (Nat0.gcd.zero (to_nat0 (+ &q)))).
      +
        intro s.
        leibniz (&magnitude &r) in &s.
        let proof m
          : to_nat0 ((+ &q) %. &r) = (BinBase.to_nat &q %. BinBase.to_nat &r)%n0
          := conversion.modulo (+ &q) &r.
        lemma halving
          : ((BinBase.to_nat &q %. BinBase.to_nat &r) + (BinBase.to_nat &q %. BinBase.to_nat &r)
              < BinBase.to_nat &q)%n0.
        {
          match (Nat0.division.specification (BinBase.to_nat &q) (BinBase.to_nat &r))
            with | e t end.
          extro &e.
          match (BinBase.to_nat &q /. BinBase.to_nat &r)%n0 with | | k end.
          *
            intro e.
            let proof e
              : (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 = Nat0.Positive (BinBase.to_nat &q)
              := &e.
            let proof c := Nat0.order.strict.transitivity &t &s.
            leibniz &e in &c.
            ex (Nat0.order.strict.irreflexivity (BinBase.to_nat &q) &c) quodlibet.
          *
            intro e.
            let proof one := Nat0.addition.order.strict.monotonicity
              (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &q %. BinBase.to_nat &r)%n0
              (BinBase.to_nat &r) &t.
            leibniz (Nat0.addition.commutativity
              (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &r)) in &one.
            let proof extension
              := Nat0.multiplication.right.order.extensivity &k (BinBase.to_nat &r).
            simpl Nat0.LessOrEqual in &extension.
            match &extension with | same | larger end.
            {
              leibniz <- &same in &e.
              leibniz &e in &one.
              ipso &one.
            }
            {
              let proof two := Nat0.addition.order.strict.monotonicity
                (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &r) (k * BinBase.to_nat &r)%n0
                &larger.
              leibniz (Nat0.addition.commutativity
                  (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &r)),
                (Nat0.addition.commutativity
                  (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (k * BinBase.to_nat &r)%n0) in &two.
              leibniz &e in &two.
              ipso (Nat0.order.strict.transitivity &one &two).
            }
        }
        lemma bound : ((BinBase.to_nat &q %. BinBase.to_nat &r) <= BinBase.to_nat &f)%n0.
        {
          lemma below
            : ((BinBase.to_nat &q %. BinBase.to_nat &r) + (BinBase.to_nat &q %. BinBase.to_nat &r)
                < BinBase.to_nat (BinBase.b1 &f))%n0.
          {
            simpl Nat0.LessOrEqual in &h.
            match &h with | same | less end.
            -
              leibniz <- &same in |- *.
              ipso &halving.
            -
              ipso (Nat0.order.strict.transitivity &halving &less).
          }
          lemma twice
            : Nat0.Positive (BinBase.to_nat (BinBase.b1 &f))
              = ((BinBase.to_nat &f + BinBase.to_nat &f) + Nat.One)%n0.
          {
            simpl in |- *.
            leibniz (Nat.addition.commutativity (BinBase.to_nat &f + BinBase.to_nat &f)%n Nat.One)
              in |- *.
            simpl in |- *.
            quod idem est.
          }
          leibniz &twice in &below.
          modus aequans
            (Nat0.order.discreteness
              ((BinBase.to_nat &q %. BinBase.to_nat &r) + (BinBase.to_nat &q %. BinBase.to_nat &r))%n0
              (BinBase.to_nat &f + BinBase.to_nat &f)%n0),
            &below
          |- doubled.
          simpl Nat0.LessOrEqual in |- *.
          match (Comparable.order.strict.trichotomy
              (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &f))
            with | less | rest end.
          -
            ipso (disjoin _, &less).
          -
            match &rest with | same | greater end.
            {
              ipso (disjoin &same, _).
            }
            {
              let proof one := Nat0.addition.order.strict.monotonicity
                (BinBase.to_nat &f) (BinBase.to_nat &f) (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 &greater.
              let proof two := Nat0.addition.order.strict.monotonicity
                (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &f)
                (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 &greater.
              leibniz (Nat0.addition.commutativity
                (BinBase.to_nat &q %. BinBase.to_nat &r)%n0 (BinBase.to_nat &f)) in &two.
              let proof three := Nat0.order.strict.transitivity &one &two.
              simpl Nat0.LessOrEqual in &doubled.
              match &doubled with | equal | smaller end.
              -
                leibniz &equal in &three.
                ex (Nat0.order.strict.irreflexivity _ &three) quodlibet.
              -
                ex (Nat0.order.strict.irreflexivity _
                  (Nat0.order.strict.transitivity &three &smaller)) quodlibet.
            }
        }
        leibniz <- &m in &bound.
        leibniz (&IH (+ &r) ((+ &q) %. &r) &bound) in |- *.
        let proof rec
          : Nat0.gcd (to_nat0 (+ &q)) (to_nat0 (+ &r))
            = Nat0.gcd (to_nat0 (+ &r)) (BinBase.to_nat &q %. BinBase.to_nat &r)%n0
          := Nat0.gcd.recurrence (to_nat0 (+ &q)) (BinBase.to_nat &r).
        leibniz <- &m in &rec.
        ipso (symm &rec).
  }
  match fuel with | | f by IH | f by IH end per BinBase.induction.
  -
    intros a b h.
    match b with | | q end.
    +
      lemma facto : to_nat0 (gcd_with_fuel BinBase.One &a 0) = to_nat0 &a.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &facto, &nothing in |- *.
      ipso (symm (Nat0.gcd.zero (to_nat0 &a))).
    +
      lemma unfolding : gcd_with_fuel BinBase.One &a (+ &q) = + &q.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz &unfolding in |- *.
      let proof s
        := Nat0.division.remainder.boundedness (to_nat0 &a) (BinBase.to_nat &q).
      lemma unit : BinBase.to_nat BinBase.One = Nat.One.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz (&magnitude &q), &unit in &h.
      lemma one : ((to_nat0 &a %. BinBase.to_nat &q) < Nat.One)%n0.
      {
        simpl Nat0.LessOrEqual in &h.
        match &h with | same | less end.
        -
          leibniz &same in &s.
          ipso &s.
        -
          ipso (Nat0.order.strict.transitivity &s &less).
      }
      lemma vanishing : (to_nat0 &a %. BinBase.to_nat &q)%n0 = Nat0.Zero.
      {
        simpl Nat0.LessThan in &one.
        match &one with | k e end.
        extro &e.
        match (to_nat0 &a %. BinBase.to_nat &q)%n0 with | | x end.
        -
          intro e.
          quod idem est.
        -
          intro e.
          let proof e : Nat0.Positive (&x + &k)%n = Nat0.Positive Nat.One := &e.
          let proof e := Nat0.positive.injectivity &e.
          match x with | | x' end.
          +
            simpl in &e.
            ex &e quodlibet.
          +
            simpl in &e.
            ex &e quodlibet.
      }
      let proof rec
        : Nat0.gcd (to_nat0 &a) (to_nat0 (+ &q))
          = Nat0.gcd (to_nat0 (+ &q)) (to_nat0 &a %. BinBase.to_nat &q)%n0
        := Nat0.gcd.recurrence (to_nat0 &a) (BinBase.to_nat &q).
      leibniz &rec, &vanishing in |- *.
      ipso (symm (Nat0.gcd.zero (to_nat0 (+ &q)))).
  -
    intros a b h.
    lemma step : (BinBase.to_nat (BinBase.b0 &f) < BinBase.to_nat (BinBase.b1 &f))%n0.
    {
      simpl Nat0.LessThan in |- *.
      exists Nat.One.
      simpl in |- *.
      leibniz (Nat.addition.commutativity (BinBase.to_nat &f + BinBase.to_nat &f)%n Nat.One) in |- *.
      simpl in |- *.
      quod idem est.
    }
    lemma weaker : (to_nat0 &b <= BinBase.to_nat (BinBase.b1 &f))%n0.
    {
      simpl Nat0.LessOrEqual in &h |- *.
      match &h with | same | less end.
      -
        leibniz &same in |- *.
        ipso (disjoin _, &step).
      -
        ipso (disjoin _, (Nat0.order.strict.transitivity &less &step)).
    }
    lemma same : gcd_with_fuel (BinBase.b0 &f) &a &b = gcd_with_fuel (BinBase.b1 &f) &a &b.
    {
      match b with | | q end.
      -
        simpl in |- *.
        quod idem est.
      -
        simpl in |- *.
        quod idem est.
    }
    leibniz &same in |- *.
    ipso (&odd &f &IH &a &b &weaker).
  -
    ipso (&odd &f &IH).
Qed.

End gcd. (* conversion.gcd *)

(* conversion.gcd *)
Theorem gcd
  : forall (a : BinWithZero) (b : BinWithZero) .
      to_nat0 (gcd a b) = Nat0.gcd (to_nat0 a) (to_nat0 b).
Proof.
  intros a b.
  match b with | | q end.
  -
    lemma facto : to_nat0 (gcd &a 0) = to_nat0 &a.
    {
      simpl gcd in |- *.
      quod idem est.
    }
    lemma nothing : to_nat0 0 = Nat0.Zero.
    {
      simpl in |- *.
      quod idem est.
    }
    leibniz &facto, &nothing in |- *.
    ipso (symm (Nat0.gcd.zero (to_nat0 &a))).
  -
    lemma enough : (to_nat0 (+ &q) <= BinBase.to_nat &q)%n0.
    {
      simpl Nat0.LessOrEqual in |- *.
      lemma same : to_nat0 (+ &q) = BinBase.to_nat &q.
      {
        simpl in |- *.
        quod idem est.
      }
      ipso (disjoin &same, _).
    }
    simpl gcd in |- *.
    ipso (conversion.gcd.sufficiency &q &a (+ &q) &enough).
Qed.

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : BinWithZero) (m : BinWithZero) (n : BinWithZero) .
      (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  lemma f : to_nat0 ((&l + &m) + &n) = to_nat0 (&l + (&m + &n)).
  {
    leibniz (conversion.addition (&l + &m) &n), (conversion.addition &l &m),
            (conversion.addition &l (&m + &n)), (conversion.addition &m &n) in |- *.
    ipso (Nat0.addition.associativity
            (to_nat0 &l) (to_nat0 &m) (to_nat0 &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m + n = n + m.
Proof.
  intros m n.
  lemma f : to_nat0 (&m + &n) = to_nat0 (&n + &m).
  {
    leibniz (conversion.addition &m &n), (conversion.addition &n &m) in |- *.
    ipso (Nat0.addition.commutativity (to_nat0 &m) (to_nat0 &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.identity *)
Theorem identity
  : forall (n : BinWithZero) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (m : BinWithZero) (n : BinWithZero) (k : BinWithZero) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  let proof c := Nat0.addition.cancellation
                   (to_nat0 &m) (to_nat0 &n) (to_nat0 &k).
  match &c with | l r end.
  divide et impera.
  -
    intro e.
    let proof f := congru to_nat0, &e.
    leibniz (conversion.addition &m &n), (conversion.addition &m &k) in &f.
    ipso (conversion.injectivity (&l &f)).
  -
    intro e.
    let proof f := congru to_nat0, &e.
    leibniz (conversion.addition &m &n), (conversion.addition &k &n) in &f.
    ipso (conversion.injectivity (&r &f)).
Qed.

End addition. (* addition *)

Module multiplication. (* multiplication *)

(* multiplication.associativity *)
Theorem associativity
  : forall (l : BinWithZero) (m : BinWithZero) (n : BinWithZero) .
      (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  lemma f : to_nat0 ((&l * &m) * &n) = to_nat0 (&l * (&m * &n)).
  {
    leibniz (conversion.multiplication (&l * &m) &n), (conversion.multiplication &l &m),
            (conversion.multiplication &l (&m * &n)), (conversion.multiplication &m &n)
      in |- *.
    ipso (Nat0.multiplication.associativity
            (to_nat0 &l) (to_nat0 &m) (to_nat0 &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m * n = n * m.
Proof.
  intros m n.
  lemma f : to_nat0 (&m * &n) = to_nat0 (&n * &m).
  {
    leibniz (conversion.multiplication &m &n), (conversion.multiplication &n &m) in |- *.
    ipso (Nat0.multiplication.commutativity
            (to_nat0 &m) (to_nat0 &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (n : BinWithZero) . ((+ BinBase.One) * n = n) /\ (n * (+ BinBase.One) = n).
Proof.
  intro n.
  divide et impera.
  -
    match n with | | p end; simpl in |- *; quod idem est.
  -
    match n with | | p end.
    +
      simpl in |- *.
      quod idem est.
    +
      let proof i := BinBase.multiplication.identity &p.
      match &i with | l r end.
      simpl in |- *.
      leibniz &r in |- *.
      quod idem est.
Qed.

(* multiplication.annihilation *)
Theorem annihilation
  : forall (n : BinWithZero) . (0 * n = 0) /\ (n * 0 = 0).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : BinWithZero) (y : BinWithZero) (z : BinWithZero) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  let proof d := Nat0.multiplication.distributivity.over.addition
                   (to_nat0 &x) (to_nat0 &y) (to_nat0 &z).
  match &d with | l r end.
  divide et impera.
  -
    lemma f : to_nat0 (&x * (&y + &z)) = to_nat0 ((&x * &y) + (&x * &z)).
    {
      leibniz (conversion.multiplication &x (&y + &z)), (conversion.addition &y &z),
              (conversion.addition (&x * &y) (&x * &z)),
              (conversion.multiplication &x &y), (conversion.multiplication &x &z) in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_nat0 ((&y + &z) * &x) = to_nat0 ((&y * &x) + (&z * &x)).
    {
      leibniz (conversion.multiplication (&y + &z) &x), (conversion.addition &y &z),
              (conversion.addition (&y * &x) (&z * &x)),
              (conversion.multiplication &y &x), (conversion.multiplication &z &x) in |- *.
      ipso &r.
    }
    ipso (conversion.injectivity &f).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : BinWithZero) . ~ (n < n).
Proof.
  intros n h.
  ipso (Nat0.order.strict.irreflexivity (to_nat0 &n)
          (modus aequans (conversion.order &n &n), &h)).
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : BinWithZero} {m : BinWithZero} {n : BinWithZero} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  let proof k := Nat0.order.strict.transitivity
                   (modus aequans (conversion.order &l &m), &h1)
                   (modus aequans (conversion.order &m &n), &h2).
  ipso (modus aequans (conversion.order &l &n), &k).
Qed.

(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (n : BinWithZero) . Accessible (<) n.
Proof.
  intro n.
  lemma descent
    : Descent.Step (Induced Nat0.LessThan to_nat0)
        (fun (x : BinWithZero) . Accessible (<) x).
  {
    intros x recurse.
    ipso (Accessible_introduction
            (fun (y : BinWithZero) (h : y < &x) .
               &recurse y (Induced.introduction (modus aequans (conversion.order y &x), h)))).
  }
  ipso (Accessible.recursion &descent &n
          (@accessibility _ _ (WellFounded.induced Nat0.LessThan to_nat0 _) &n)).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (m : BinWithZero) (n : BinWithZero) .
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
Proof.
  intros m n.
  leibniz (conversion.comparison &m &n) in |- *.
  let proof s := Nat0.comparison.specification
                   (to_nat0 &m) (to_nat0 &n).
  match &s with | strict equality end.
  divide et impera.
  -
    divide et impera.
    +
      intro c.
      ipso (modus aequans (conversion.order &m &n), (modus aequans &strict, &c)).
    +
      intro h.
      ipso (modus aequans &strict, (modus aequans (conversion.order &m &n), &h)).
  -
    divide et impera.
    +
      intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    +
      intro e.
      ipso (modus aequans &equality, (congru to_nat0, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : BinWithZero) (n : BinWithZero) .
      compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  leibniz (conversion.comparison &m &n), (conversion.comparison &n &m) in |- *.
  ipso (Nat0.comparison.antisymmetry (to_nat0 &m) (to_nat0 &n)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity  := @order.strict.transitivity
   ; Comparable.specification := comparison.specification
   ; Comparable.antisymmetry  := comparison.antisymmetry |}.

Module maximum. (* maximum *)

(* maximum.identity *)
Theorem identity
  : forall (n : BinWithZero) . (max 0 n = n) /\ (max n 0 = n).
Proof.
  intro n.
  simpl Comparable.max in |- *.
  divide et impera.
  -
    match n with | | p end; simpl in |- *; quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

End maximum. (* maximum *)

Module division. (* division *)

(* division.specification *)
Theorem specification
  : forall (n : BinWithZero) (d : BinBase) .
      (((n /. d) * (+ d)) + (n %. d) = n) /\ (n %. d) < + d.
Proof.
  intros n d.
  lemma divisor : to_nat0 (+ &d) = BinBase.to_nat &d.
  {
    simpl in |- *.
    quod idem est.
  }
  let proof s := Nat0.division.specification (to_nat0 &n) (BinBase.to_nat &d).
  match &s with | e below end.
  divide et impera.
  -
    lemma f : to_nat0 (((&n /. &d) * (+ &d)) + (&n %. &d)) = to_nat0 &n.
    {
      leibniz (conversion.addition ((&n /. &d) * (+ &d)) (&n %. &d)),
        (conversion.multiplication (&n /. &d) (+ &d)),
        (conversion.division &n &d), (conversion.modulo &n &d), &divisor in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
  -
    leibniz <- (conversion.modulo &n &d), <- &divisor in &below.
    ipso (modus aequans (conversion.order (&n %. &d) (+ &d)), &below).
Qed.

(* division.uniqueness *)
Theorem uniqueness
  : forall (n : BinWithZero) (d : BinBase) (m : BinWithZero) (r : BinWithZero) .
      ((m * (+ d)) + r = n /\ r < (+ d)) -> ((n /. d) = m) /\ ((n %. d) = r).
Proof.
  intros n d m r h.
  lemma divisor : to_nat0 (+ &d) = BinBase.to_nat &d.
  {
    simpl in |- *.
    quod idem est.
  }
  match &h with | e below end.
  let proof f := congru to_nat0, &e.
  leibniz (conversion.addition (&m * (+ &d)) &r), (conversion.multiplication &m (+ &d)),
    &divisor in &f.
  let proof bound := modus aequans (conversion.order &r (+ &d)), &below.
  leibniz &divisor in &bound.
  let proof u := Nat0.division.uniqueness
    (to_nat0 &n) (BinBase.to_nat &d) (to_nat0 &m) (to_nat0 &r)
    (conjoin &f, &bound).
  match &u with | quotient remainder end.
  leibniz <- (conversion.division &n &d) in &quotient.
  leibniz <- (conversion.modulo &n &d) in &remainder.
  divide et impera.
  -
    ipso (conversion.injectivity &quotient).
  -
    ipso (conversion.injectivity &remainder).
Qed.

End division. (* division *)

Module modulo. (* modulo *)

(* modulo.identity *)
Theorem identity : forall (n : BinWithZero) (d : BinBase) . n < + d -> n %. d = n.
Proof.
  intros n d h.
  let proof g := modus aequans (conversion.order &n (+ &d)), &h.
  lemma facto : to_nat0 (&n %. &d) = to_nat0 &n.
  {
    leibniz (conversion.modulo &n &d) in |- *.
    ipso (Nat0.modulo.identity (to_nat0 &n) (BinBase.to_nat &d) &g).
  }
  ipso (conversion.injectivity &facto).
Qed.

Module sum. (* modulo.sum *)

Module left. (* modulo.sum.left *)

(* modulo.sum.left.absorption *)
Theorem absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      ((a %. d) + b) %. d = (a + b) %. d.
Proof.
  intros a b d.
  lemma facto : to_nat0 ((&a %. &d + &b) %. &d) = to_nat0 ((&a + &b) %. &d).
  {
    leibniz
      (conversion.modulo (&a %. &d + &b) &d),
      (conversion.addition (&a %. &d) &b),
      (conversion.modulo &a &d),
      (conversion.modulo (&a + &b) &d),
      (conversion.addition &a &b)
      in |- *.
    ipso (Nat0.modulo.sum.left.absorption (to_nat0 &a) (to_nat0 &b) (BinBase.to_nat &d)).
  }
  ipso (conversion.injectivity &facto).
Qed.

End left. (* modulo.sum.left *)

Module right. (* modulo.sum.right *)

(* modulo.sum.right.absorption *)
Theorem absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (a + (b %. d)) %. d = (a + b) %. d.
Proof.
  intros a b d.
  leibniz
    (addition.commutativity &a (&b %. &d)),
    (modulo.sum.left.absorption &b &a &d),
    (addition.commutativity &b &a)
    in |- *.
  quod idem est.
Qed.

End right. (* modulo.sum.right *)

End sum. (* modulo.sum *)

Module product. (* modulo.product *)

Module left. (* modulo.product.left *)

(* modulo.product.left.absorption *)
Theorem absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      ((a %. d) * b) %. d = (a * b) %. d.
Proof.
  intros a b d.
  lemma facto : to_nat0 ((&a %. &d * &b) %. &d) = to_nat0 ((&a * &b) %. &d).
  {
    leibniz
      (conversion.modulo (&a %. &d * &b) &d),
      (conversion.multiplication (&a %. &d) &b),
      (conversion.modulo &a &d),
      (conversion.modulo (&a * &b) &d),
      (conversion.multiplication &a &b)
      in |- *.
    ipso
      (Nat0.modulo.product.left.absorption (to_nat0 &a) (to_nat0 &b) (BinBase.to_nat &d)).
  }
  ipso (conversion.injectivity &facto).
Qed.

End left. (* modulo.product.left *)

Module right. (* modulo.product.right *)

(* modulo.product.right.absorption *)
Theorem absorption
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinBase) .
      (a * (b %. d)) %. d = (a * b) %. d.
Proof.
  intros a b d.
  leibniz
    (multiplication.commutativity &a (&b %. &d)),
    (modulo.product.left.absorption &b &a &d),
    (multiplication.commutativity &b &a)
    in |- *.
  quod idem est.
Qed.

End right. (* modulo.product.right *)

End product. (* modulo.product *)

End modulo. (* modulo *)

Module gcd. (* gcd *)

(* gcd.zero *)
Theorem zero : forall (a : BinWithZero) . gcd a 0 = a.
Proof.
  intro a.
  simpl gcd in |- *.
  quod idem est.
Qed.

(* gcd.recurrence *)
Theorem recurrence
  : forall (a : BinWithZero) (q : BinBase) . gcd a (+ q) = gcd (+ q) (a %. q).
Proof.
  intros a q.
  lemma f : to_nat0 (gcd &a (+ &q)) = to_nat0 (gcd (+ &q) (&a %. &q)).
  {
    let proof rec
      : Nat0.gcd (to_nat0 &a) (to_nat0 (+ &q))
        = Nat0.gcd (to_nat0 (+ &q)) (to_nat0 &a %. BinBase.to_nat &q)%n0
      := Nat0.gcd.recurrence (to_nat0 &a) (BinBase.to_nat &q).
    leibniz (conversion.gcd &a (+ &q)), (conversion.gcd (+ &q) (&a %. &q)),
      (conversion.modulo &a &q) in |- *.
    ipso &rec.
  }
  ipso (conversion.injectivity &f).
Qed.

(* gcd.divisibility *)
Theorem divisibility
  : forall (a : BinWithZero) (b : BinWithZero) . Divides (gcd a b) a /\ Divides (gcd a b) b.
Proof.
  intros a b.
  let proof s := Nat0.gcd.divisibility (to_nat0 &b) (to_nat0 &a).
  leibniz <- (conversion.gcd &a &b) in &s.
  match &s with | of_a of_b end.
  divide et impera.
  -
    ipso (modus aequans (conversion.divisibility (gcd &a &b) &a), &of_a).
  -
    ipso (modus aequans (conversion.divisibility (gcd &a &b) &b), &of_b).
Qed.

(* gcd.universality *)
Theorem universality
  : forall (a : BinWithZero) (b : BinWithZero) (d : BinWithZero) .
      Divides d a -> Divides d b -> Divides d (gcd a b).
Proof.
  intros a b d ha hb.
  let proof u := Nat0.gcd.universality
    (to_nat0 &b) (to_nat0 &a) (to_nat0 &d)
    (modus aequans (conversion.divisibility &d &a), &ha)
    (modus aequans (conversion.divisibility &d &b), &hb).
  leibniz <- (conversion.gcd &a &b) in &u.
  ipso (modus aequans (conversion.divisibility &d (gcd &a &b)), &u).
Qed.

(* gcd.commutativity *)
Theorem commutativity
  : forall (a : BinWithZero) (b : BinWithZero) . gcd a b = gcd b a.
Proof.
  intros a b.
  lemma f : to_nat0 (gcd &a &b) = to_nat0 (gcd &b &a).
  {
    leibniz (conversion.gcd &a &b), (conversion.gcd &b &a) in |- *.
    ipso (Nat0.gcd.commutativity (to_nat0 &a) (to_nat0 &b)).
  }
  ipso (conversion.injectivity &f).
Qed.

End gcd. (* gcd *)

Module narrowing. (* narrowing *)

Module base. (* narrowing.base *)

(* narrowing.base.retraction *)
Theorem retraction
  : forall (p : BinBase) . to_bin_base (+ p) = Some p.
Proof.
  intro p.
  simpl to_bin_base in |- *.
  quod idem est.
Qed.

(* narrowing.base.specification *)
Theorem specification
  : forall (n : BinWithZero) (p : BinBase) . to_bin_base n = Some p <-> n = + p.
Proof.
  intros n p.
  divide et impera.
  -
    intro e.
    match n with | | q end.
    +
      simpl to_bin_base in &e.
      ex &e quodlibet.
    +
      simpl to_bin_base in &e.
      let proof f := Option.some.injectivity &e.
      leibniz &f in |- *.
      quod idem est.
  -
    intro e.
    leibniz &e in |- *.
    ipso (narrowing.base.retraction &p).
Qed.

(* narrowing.base.failure *)
Theorem failure
  : forall (n : BinWithZero) . to_bin_base n = None <-> n = 0.
Proof.
  intro n.
  divide et impera.
  -
    intro e.
    match n with | | q end.
    +
      quod idem est.
    +
      simpl to_bin_base in &e.
      ex &e quodlibet.
  -
    intro e.
    leibniz &e in |- *.
    simpl to_bin_base in |- *.
    quod idem est.
Qed.

End base. (* narrowing.base *)

End narrowing. (* narrowing *)

Module halving. (* halving *)

(* halving.retraction *)
Theorem retraction
  : forall (bit : Bool) (n : BinWithZero) . halve (append_bit bit n) = n.
Proof.
  intros bit n.
  match n with | | p end; match bit with | | end; simpl in |- *; quod idem est.
Qed.

End halving. (* halving *)

Module appending. (* appending *)

Module distributivity. (* appending.distributivity *)

Module over. (* appending.distributivity.over *)

(* appending.distributivity.over.conjunction *)
Theorem conjunction
  : forall (b : Bool) (c : Bool) (m : BinWithZero) (n : BinWithZero) .
      append_bit (b && c)%bool (m && n) = append_bit b m && append_bit c n.
Proof.
  intros b c m n.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

(* appending.distributivity.over.disjunction *)
Theorem disjunction
  : forall (b : Bool) (c : Bool) (m : BinWithZero) (n : BinWithZero) .
      append_bit (b || c)%bool (m || n) = append_bit b m || append_bit c n.
Proof.
  intros b c m n.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

(* appending.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b : Bool) (c : Bool) (m : BinWithZero) (n : BinWithZero) .
      append_bit (b ^^ c)%bool (m ^^ n) = append_bit b m ^^ append_bit c n.
Proof.
  intros b c m n.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

End over. (* appending.distributivity.over *)

End distributivity. (* appending.distributivity *)

End appending. (* appending *)

Module conjunction. (* conjunction *)

(* conjunction.annihilation *)
Theorem annihilation
  : forall (n : BinWithZero) . (0 && n = 0) /\ (n && 0 = 0).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m && n = n && m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof a := conjunction.annihilation (append_bit &b &m').
      match &a with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.conjunction &b &c &m' &n'),
              <- (appending.distributivity.over.conjunction &c &b &n' &m') in |- *.
      leibniz (&IH &n'), (Bool.conjunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* conjunction.associativity *)
Theorem associativity
  : forall (m : BinWithZero) (n : BinWithZero) (o : BinWithZero) .
      (m && n) && o = m && (n && o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof a := conjunction.annihilation (append_bit &b &m').
      match &a with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      leibniz &r in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinWithZero.induction.
      *
        let proof a := conjunction.annihilation (append_bit &b &m' && append_bit &c &n').
        let proof a' := conjunction.annihilation (append_bit &c &n').
        let proof a'' := conjunction.annihilation (append_bit &b &m').
        match &a with | l r end.
        match &a' with | l' r' end.
        match &a'' with | l'' r'' end.
        leibniz &r, &r', &r'' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.conjunction &b &c &m' &n'),
                <- (appending.distributivity.over.conjunction (&b && &c)%bool &d (&m' && &n') &o'),
                <- (appending.distributivity.over.conjunction &c &d &n' &o'),
                <- (appending.distributivity.over.conjunction &b (&c && &d)%bool &m' (&n' && &o'))
          in |- *.
        leibniz (&IH &n' &o'), (Bool.conjunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* conjunction.idempotence *)
Theorem idempotence
  : forall (n : BinWithZero) . n && n = n.
Proof.
  intro n.
  match n with | | b n' by IH end per BinWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.conjunction &b &b &n' &n') in |- *.
    leibniz &IH in |- *.
    match b with | | end; simpl in |- *; quod idem est.
Qed.

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.identity *)
Theorem identity
  : forall (n : BinWithZero) . (0 || n = n) /\ (n || 0 = n).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m || n = n || m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof i := disjunction.identity (append_bit &b &m').
      match &i with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.disjunction &b &c &m' &n'),
              <- (appending.distributivity.over.disjunction &c &b &n' &m') in |- *.
      leibniz (&IH &n'), (Bool.disjunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* disjunction.associativity *)
Theorem associativity
  : forall (m : BinWithZero) (n : BinWithZero) (o : BinWithZero) .
      (m || n) || o = m || (n || o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof i := disjunction.identity (append_bit &b &m').
      match &i with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinWithZero.induction.
      *
        let proof i := disjunction.identity (append_bit &b &m' || append_bit &c &n').
        let proof i' := disjunction.identity (append_bit &c &n').
        match &i with | l r end.
        match &i' with | l' r' end.
        leibniz &r, &r' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.disjunction &b &c &m' &n'),
                <- (appending.distributivity.over.disjunction (&b || &c)%bool &d (&m' || &n') &o'),
                <- (appending.distributivity.over.disjunction &c &d &n' &o'),
                <- (appending.distributivity.over.disjunction &b (&c || &d)%bool &m' (&n' || &o'))
          in |- *.
        leibniz (&IH &n' &o'), (Bool.disjunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* disjunction.idempotence *)
Theorem idempotence
  : forall (n : BinWithZero) . n || n = n.
Proof.
  intro n.
  match n with | | b n' by IH end per BinWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.disjunction &b &b &n' &n') in |- *.
    leibniz &IH in |- *.
    match b with | | end; simpl in |- *; quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.identity *)
Theorem identity
  : forall (n : BinWithZero) . (0 ^^ n = n) /\ (n ^^ 0 = n).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m ^^ n = n ^^ m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof i := sejunction.identity (append_bit &b &m').
      match &i with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.sejunction &b &c &m' &n'),
              <- (appending.distributivity.over.sejunction &c &b &n' &m') in |- *.
      leibniz (&IH &n'), (Bool.sejunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* sejunction.associativity *)
Theorem associativity
  : forall (m : BinWithZero) (n : BinWithZero) (o : BinWithZero) .
      (m ^^ n) ^^ o = m ^^ (n ^^ o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinWithZero.induction.
    +
      let proof i := sejunction.identity (append_bit &b &m').
      match &i with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinWithZero.induction.
      *
        let proof i := sejunction.identity (append_bit &b &m' ^^ append_bit &c &n').
        let proof i' := sejunction.identity (append_bit &c &n').
        match &i with | l r end.
        match &i' with | l' r' end.
        leibniz &r, &r' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.sejunction &b &c &m' &n'),
                <- (appending.distributivity.over.sejunction (&b ^^ &c)%bool &d (&m' ^^ &n') &o'),
                <- (appending.distributivity.over.sejunction &c &d &n' &o'),
                <- (appending.distributivity.over.sejunction &b (&c ^^ &d)%bool &m' (&n' ^^ &o'))
          in |- *.
        leibniz (&IH &n' &o'), (Bool.sejunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity
  : forall (n : BinWithZero) . n ^^ n = 0.
Proof.
  intro n.
  match n with | | b n' by IH end per BinWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.sejunction &b &b &n' &n') in |- *.
    leibniz &IH, (Bool.sejunction.irreflexivity &b) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End sejunction. (* sejunction *)

Module shift. (* shift *)

(* shift.retraction *)
Theorem retraction
  : forall (n : BinWithZero) (k : Nat0) . shift_right (shift_left n k) k = n.
Proof.
  intros n k.
  match k with | | k' end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl shift_left, shift_right in |- *.
    match k' with | | k'' by IH end per Nat.induction.
    +
      simpl in |- *.
      leibniz (halving.retraction false &n) in |- *.
      quod idem est.
    +
      simpl in |- *.
      leibniz (halving.retraction false (shift_left_nat &n &k'')) in |- *.
      ipso &IH.
Qed.

Module left. (* shift.left *)

(* shift.left.doubling *)
Theorem doubling : forall (n : BinWithZero) . shift_left n 1%n0 = (+ 10%bin_base) * n.
Proof.
  intros n.
  match &n with | Zero | Positive p end; simpl in |- *; quod idem est.
Qed.

(* shift.left.successor *)
Theorem successor
  : forall (n : BinWithZero) (k : Nat) .
      shift_left n (Nat0.Positive (Nat.Successor k))
      = shift_left ((+ 10%bin_base) * n) (Nat0.Positive k).
Proof.
  intros n k.
  simpl shift_left in |- *.
  match k with | One | Successor (k' by IH) end per Nat.induction.
  - lemma once : append_bit false &n = shift_left &n 1%n0.
    {
      simpl in |- *.
      quod idem est.
    }
    simpl shift_left_nat in |- *.
    leibniz &once, (shift.left.doubling &n) in |- *.
    quod idem est.
  - lemma left
      : shift_left_nat &n (Nat.Successor (Nat.Successor &k'))
        = append_bit false (shift_left_nat &n (Nat.Successor &k')).
    {
      simpl in |- *.
      quod idem est.
    }
    lemma right
      : shift_left_nat ((+ 10%bin_base) * &n) (Nat.Successor &k')
        = append_bit false (shift_left_nat ((+ 10%bin_base) * &n) &k').
    {
      simpl in |- *.
      quod idem est.
    }
    leibniz &left, &right, &IH in |- *.
    quod idem est.
Qed.

(* shift.left.multiplication *)
Theorem multiplication
  : forall (n : BinWithZero) (k : Nat0) . shift_left n k = n * shift_left (+ BinBase.One) k.
Proof.
  intros n k.
  lemma facto : to_nat0 (shift_left &n &k) = to_nat0 (&n * shift_left (+ BinBase.One) &k).
  {
    lemma one : to_nat0 (+ BinBase.One) = 1%n0.
    {
      simpl in |- *.
      quod idem est.
    }
    match (Nat0.multiplication.identity (Nat0.Positive (Nat.Successor Nat.One) ^ &k)%n0)
    with | unit _ end.
    leibniz
      (conversion.left.shift &n &k),
      (conversion.multiplication &n (shift_left (+ BinBase.One) &k)),
      (conversion.left.shift (+ BinBase.One) &k),
      &one,
      &unit
      in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &facto).
Qed.

End left. (* shift.left *)

Module right. (* shift.right *)

(* shift.right.successor *)
Theorem successor
  : forall (n : BinWithZero) (i : Nat0) .
      shift_right n (Nat0.inc i) = shift_right (halve n) i.
Proof.
  intros n i.
  match i with | | k end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
Qed.

(* shift.right.quotient *)
Theorem quotient
  : forall (n : BinWithZero) (k : BinBase) .
      shift_right n (BinBase.to_nat k) = n /. (10 ^ k)%bin_base.
Proof.
  intros n k.
  lemma power : BinBase.to_nat (10 ^ &k)%bin_base = (Nat.Successor Nat.One ^ BinBase.to_nat &k)%n.
  {
    leibniz (BinBase.conversion.power 10%bin_base &k) in |- *.
    simpl in |- *.
    quod idem est.
  }
  lemma f
    : to_nat0 (shift_right &n (BinBase.to_nat &k))
      = to_nat0 (&n /. (10 ^ &k)%bin_base).
  {
    leibniz (conversion.right.shift &n (BinBase.to_nat &k)), (conversion.division &n (10 ^ &k)%bin_base),
      &power in |- *.
    quod idem est.
  }
  ipso (conversion.injectivity &f).
Qed.

End right. (* shift.right *)

End shift. (* shift *)

Module bit. (* bit *)

(* bit.absence *)
Theorem absence
  : forall (i : Nat0) . test_bit 0 i = false.
Proof.
  intro i.
  simpl test_bit, shift_right in |- *.
  match i with | | k end.
  -
    quod idem est.
  -
    match k with | | k' by IH end per Nat.induction.
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      ipso &IH.
Qed.

(* bit.parity *)
Theorem parity
  : forall (bit : Bool) (n : BinWithZero) .
      test_bit (append_bit bit n) Nat0.Zero = bit.
Proof.
  intros bit n.
  simpl test_bit, shift_right in |- *.
  match n with | | p end; match bit with | | end; simpl in |- *; quod idem est.
Qed.

(* bit.successor *)
Theorem successor
  : forall (bit : Bool) (n : BinWithZero) (i : Nat0) .
      test_bit (append_bit bit n) (Nat0.inc i) = test_bit n i.
Proof.
  intros bit n i.
  simpl test_bit in |- *.
  leibniz (shift.right.successor (append_bit &bit &n) &i) in |- *.
  leibniz (halving.retraction &bit &n) in |- *.
  quod idem est.
Qed.

End bit. (* bit *)

End BinWithZero. (* BinWithZero *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinWithZero], not [BinWithZero.T]. [Zero] and [Positive] name ctors
 * of [Nat0] and [Integer] as well, so all three write theirs with the
 * prefix.
 *)
Abbreviation BinWithZero := BinWithZero.T.

(* Makes the notations declared in [Module BinWithZero] usable in every
 * file that imports this one, as [(m + n)%bin_with_zero] or under an opened
 * [jwa_bin_with_zero_scope]. Only the notations are exported: [add] and
 * the laws still need the [BinWithZero.] prefix, and the local aliases
 * [0] and [+ p] stay inside the module.
 *)
Export (notations) BinWithZero.

(* A number of the type is written in binary digits under its scope,
 * [1011%bin_with_zero] for eleven, and a closed one prints that way; a
 * literal with any other digit is refused. The short key [b] belongs to
 * [Bin], whose literals carry a sign as well.
 *)
Number Notation BinWithZero.T BinWithZero.from_numeral BinWithZero.to_numeral
  : jwa_bin_with_zero_scope.

(* A [BinBase] stands wherever a [BinWithZero] is expected, read as its
 * [Positive], and the conversion is printed where it happened.
 *)
Coercion BinWithZero.Positive : BinBase >-> BinWithZero.
Add Printing Coercion BinWithZero.Positive.

(* Declared inside [Module BinWithZero], whose proofs use it; an instance
 * declared there is dropped at the module's [End], so it is announced again
 * here.
 *)
Existing Instance BinWithZero.comparable.

Instance BinWithZero_less_than_well_founded
  : WellFounded (<)%bin_with_zero :=
  {| accessibility := BinWithZero.order.strict.wellfoundedness |}.

Instance BinWithZero_add_monoid
  : Monoid BinWithZero.add BinWithZero.Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := BinWithZero.addition.associativity |}
  ; Monoid.identity := BinWithZero.addition.identity
  |}.

Instance BinWithZero_add_cancellative
  : Cancellative BinWithZero.add := {|
    Cancellative.cancellation := BinWithZero.addition.cancellation
  |}.

Instance BinWithZero_mul_monoid
  : Monoid BinWithZero.mul BinBase.One := {|
    Monoid.semigroup := {|
      Semigroup.associativity := BinWithZero.multiplication.associativity |}
  ; Monoid.identity := BinWithZero.multiplication.identity |}.

Instance BinWithZero_add_commutative
  : Commutative BinWithZero.add := {|
      Commutative.commutativity := BinWithZero.addition.commutativity
  |}.

Instance BinWithZero_add_abelian_monoid
  : AbelianMonoid BinWithZero.add BinWithZero.Zero :=
  {| AbelianMonoid.monoid      := BinWithZero_add_monoid
   ; AbelianMonoid.commutative := BinWithZero_add_commutative |}.

Instance BinWithZero_mul_commutative
  : Commutative BinWithZero.mul := {|
    Commutative.commutativity := BinWithZero.multiplication.commutativity
  |}.

Instance BinWithZero_min_semigroup
  : Semigroup BinWithZero.min :=
  {| Semigroup.associativity := Comparable.minimum.associativity |}.

Instance BinWithZero_max_monoid
  : Monoid BinWithZero.max BinWithZero.Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.maximum.associativity |}
   ; Monoid.identity := BinWithZero.maximum.identity |}.

Instance BinWithZero_min_commutative
  : Commutative BinWithZero.min :=
  {| Commutative.commutativity := Comparable.minimum.commutativity |}.

Instance BinWithZero_max_commutative
  : Commutative BinWithZero.max :=
  {| Commutative.commutativity := Comparable.maximum.commutativity |}.

Instance BinWithZero_semiring
  : Semiring BinWithZero.add BinWithZero.Zero BinWithZero.mul
      BinBase.One :=
  {| Semiring.abelian_monoid := BinWithZero_add_abelian_monoid
   ; Semiring.monoid         := BinWithZero_mul_monoid
   ; Semiring.distributivity := BinWithZero.multiplication.distributivity.over.addition
   ; Semiring.annihilation   := BinWithZero.multiplication.annihilation |}.
