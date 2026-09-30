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
From jwa Require Import Data.Number.Bin.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Descent.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [BinWithZero.add].
 * The type and its ctors are declared inside it: [NatWithZero] and [Integer]
 * declare [Zero] and [Positive] too, and across files a duplicate ctor name
 * rebinds the bare one silently and with no warning.
 *)
Module BinWithZero. (* BinWithZero *)

(* [Positive] wraps a [Bin], so the arithmetic here reduces to the
 * [Bin] operation plus the [Zero] cases, as [NatWithZero] does over [Nat].
 *)
Inductive T : Type :=
  | Zero     : T
  | Positive : Bin -> T.

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
      | + q => + (p + q)%bin
      end
  end.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition mul := fun (m : BinWithZero) (n : BinWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => + (p * q)%bin
      end
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End BinWithZero] a client writes [(m + n)%b]. [only
 * parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_bin_with_zero_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_bin_with_zero_scope.

Local Open Scope jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero] *)
Definition inc := fun (n : BinWithZero) .
  match n with
  | 0   => + Bin.One
  | + p => + (Bin.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> BinWithZero] *)
Definition power := fun (m : BinWithZero) (n : BinWithZero) .
  match n with
  | 0   => + Bin.One
  | + q =>
      match m with
      | 0   => 0
      | + p => + (p ^ q)%bin
      end
  end.

Notation "m ^ n" := (power m n) (only parsing)
  : jwa_bin_with_zero_scope.

(* [BinWithZero -> BinWithZero -> Prop] *)
Definition LessThan := fun (m : BinWithZero) (n : BinWithZero) .
  forsome (k : Bin) . m + (+ k) = n.

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
      | + q => Bin.compare p q
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

(* [m - n], [None] when [n] is the greater, as [NatWithZero.sub] is. *)
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
          match Bin.diff p q with
          | Bin.Lt   => None
          | Bin.Eq   => Some 0
          | Bin.Gt d => Some (+ d)
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

(* [BinWithZero -> Option Bin] *)
Definition to_bin := fun (n : BinWithZero) .
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
      | true  => + Bin.One
      | false => 0
      end
  | + p =>
      match bit with
      | true  => + Bin.b1 p
      | false => + Bin.b0 p
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
           Bin.induction (fun (q : Bin) . P (+ q))
             (step true 0 zero)
             (fun (q : Bin) (h : P (+ q)) . step false (+ q) h)
             (fun (q : Bin) (h : P (+ q)) . step true (+ q) h)
             p
       end.

(* [n] with its lowest bit dropped. *)
(* [BinWithZero -> BinWithZero] *)
Definition halve := fun (n : BinWithZero) .
  match n with
  | 0          => 0
  | + Bin.One  => 0
  | + Bin.b0 p => + p
  | + Bin.b1 p => + p
  end.

(* Bit by bit from the least significant end, a number reading as 0s past
 * its leading 1; the bits of the result may all be 0.
 *)
(* [Bin -> Bin -> BinWithZero] *)
Fixpoint and_positive (p : Bin) (q : Bin) : BinWithZero :=
  match p, q with
  | Bin.One, Bin.One     => + Bin.One
  | Bin.One, Bin.b0 _    => 0
  | Bin.One, Bin.b1 _    => + Bin.One
  | Bin.b0 _, Bin.One    => 0
  | Bin.b0 p', Bin.b0 q' => append_bit false (and_positive p' q')
  | Bin.b0 p', Bin.b1 q' => append_bit false (and_positive p' q')
  | Bin.b1 _, Bin.One    => + Bin.One
  | Bin.b1 p', Bin.b0 q' => append_bit false (and_positive p' q')
  | Bin.b1 p', Bin.b1 q' => append_bit true (and_positive p' q')
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
(* [Bin -> Bin -> BinWithZero] *)
Fixpoint or_positive (p : Bin) (q : Bin) : BinWithZero :=
  match p, q with
  | Bin.One, Bin.One     => + Bin.One
  | Bin.One, Bin.b0 q'   => + Bin.b1 q'
  | Bin.One, Bin.b1 q'   => + Bin.b1 q'
  | Bin.b0 p', Bin.One   => + Bin.b1 p'
  | Bin.b0 p', Bin.b0 q' => append_bit false (or_positive p' q')
  | Bin.b0 p', Bin.b1 q' => append_bit true (or_positive p' q')
  | Bin.b1 p', Bin.One   => + Bin.b1 p'
  | Bin.b1 p', Bin.b0 q' => append_bit true (or_positive p' q')
  | Bin.b1 p', Bin.b1 q' => append_bit true (or_positive p' q')
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
(* [Bin -> Bin -> BinWithZero] *)
Fixpoint xor_positive (p : Bin) (q : Bin) : BinWithZero :=
  match p, q with
  | Bin.One, Bin.One     => 0
  | Bin.One, Bin.b0 q'   => + Bin.b1 q'
  | Bin.One, Bin.b1 q'   => + Bin.b0 q'
  | Bin.b0 p', Bin.One   => + Bin.b1 p'
  | Bin.b0 p', Bin.b0 q' => append_bit false (xor_positive p' q')
  | Bin.b0 p', Bin.b1 q' => append_bit true (xor_positive p' q')
  | Bin.b1 p', Bin.One   => + Bin.b0 p'
  | Bin.b1 p', Bin.b0 q' => append_bit true (xor_positive p' q')
  | Bin.b1 p', Bin.b1 q' => append_bit false (xor_positive p' q')
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
(* [BinWithZero -> NatWithZero -> BinWithZero] *)
Definition shift_left := fun (n : BinWithZero) (k : NatWithZero) .
  match k with
  | NatWithZero.Zero        => n
  | NatWithZero.Positive k' => shift_left_nat n k'
  end.

(* [BinWithZero -> Nat -> BinWithZero] *)
Fixpoint shift_right_nat (n : BinWithZero) (k : Nat) : BinWithZero :=
  match k with
  | Nat.One          => halve n
  | Nat.Successor k' => shift_right_nat (halve n) k'
  end.

(* [n] with its [k] lowest bits dropped. *)
(* [BinWithZero -> NatWithZero -> BinWithZero] *)
Definition shift_right := fun (n : BinWithZero) (k : NatWithZero) .
  match k with
  | NatWithZero.Zero        => n
  | NatWithZero.Positive k' => shift_right_nat n k'
  end.

(* Bit [i] of [n], [true] for 1, counted from 0 at the lowest bit. *)
(* [BinWithZero -> NatWithZero -> Bool] *)
Definition test_bit := fun (n : BinWithZero) (i : NatWithZero) .
  match shift_right n i with
  | 0          => false
  | + Bin.One  => true
  | + Bin.b0 _ => false
  | + Bin.b1 _ => true
  end.

(* [n] with the digits [d] appended, [None] once a digit is neither 0 nor 1. *)
(* [BinWithZero -> Numeral.Decimal.Digits -> Option BinWithZero] *)
Fixpoint from_digits (n : BinWithZero) (d : Numeral.Decimal.Digits)
  : Option BinWithZero :=
  match d with
  | Numeral.Decimal.Digits.End     => Some n
  | Numeral.Decimal.Digits.Zero d' => from_digits (append_bit false n) d'
  | Numeral.Decimal.Digits.One d'  => from_digits (append_bit true n) d'
  | _                              => None
  end.

(* The number a literal's digits spell in binary. *)
(* [Numeral.Unsigned -> Option BinWithZero] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal d     => from_digits 0 d
  | Numeral.Unsigned.Hexadecimal _ => None
  end.

(* The digits of [p] written before [rest]. *)
(* [Bin -> Numeral.Decimal.Digits -> Numeral.Decimal.Digits] *)
Fixpoint to_digits (p : Bin) (rest : Numeral.Decimal.Digits) : Numeral.Decimal.Digits :=
  match p with
  | Bin.One   => Numeral.Decimal.Digits.One rest
  | Bin.b0 p' => to_digits p' (Numeral.Decimal.Digits.Zero rest)
  | Bin.b1 p' => to_digits p' (Numeral.Decimal.Digits.One rest)
  end.

(* [BinWithZero -> Numeral.Unsigned] *)
Definition to_numeral := fun (n : BinWithZero) .
  match n with
  | 0   => Numeral.Unsigned.Decimal (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End)
  | + p => Numeral.Unsigned.Decimal (to_digits p Numeral.Decimal.Digits.End)
  end.

(* The conversions to and from [NatWithZero], used to state the laws: they
 * go through [Nat], which is unary, so they are for proofs, not for
 * computing.
 *)
(* [BinWithZero -> NatWithZero] *)
Definition to_nat_with_zero := fun (n : BinWithZero) .
  match n with
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive (Bin.to_nat p)
  end.

(* [NatWithZero -> BinWithZero] *)
Definition from_nat_with_zero := fun (n : NatWithZero) .
  match n with
  | NatWithZero.Zero       => 0
  | NatWithZero.Positive p => + Bin.from_nat p
  end.

Module conversion. (* conversion *)

(* conversion.successor *)
Theorem successor
  : forall (n : BinWithZero) .
      to_nat_with_zero (++ n) = NatWithZero.inc (to_nat_with_zero n).
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Bin.conversion.successor &p) in |- *.
    simpl Nat.inc in |- *.
    quod idem est.
Qed.

(* conversion.retraction *)
Theorem retraction
  : forall (n : NatWithZero) . to_nat_with_zero (from_nat_with_zero n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Bin.conversion.retraction &p) in |- *.
    quod idem est.
Qed.

(* conversion.section *)
Theorem section
  : forall (n : BinWithZero) . from_nat_with_zero (to_nat_with_zero n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Bin.conversion.section &p) in |- *.
    quod idem est.
Qed.

(* conversion.addition *)
Theorem addition
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat_with_zero (m + n)
      = (to_nat_with_zero m + to_nat_with_zero n)%nat_with_zero.
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
    let proof e := Bin.conversion.addition &p &q.
    simpl in |- *.
    leibniz &e in |- *.
    quod idem est.
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat_with_zero (m * n)
      = (to_nat_with_zero m * to_nat_with_zero n)%nat_with_zero.
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
    leibniz (Bin.conversion.multiplication &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.power *)
Theorem power
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat_with_zero (m ^ n)
      = (to_nat_with_zero m ^ to_nat_with_zero n)%nat_with_zero.
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
    leibniz (Bin.conversion.power &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (m : BinWithZero) (n : BinWithZero) .
      compare m n = NatWithZero.compare (to_nat_with_zero m) (to_nat_with_zero n).
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
    ipso (Bin.conversion.comparison &p &q).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (m : BinWithZero) (n : BinWithZero) .
      Option.map to_nat_with_zero (sub m n)
      = NatWithZero.sub (to_nat_with_zero m) (to_nat_with_zero n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    lemma sum
      : (NatWithZero.Zero + NatWithZero.Zero)%nat_with_zero = NatWithZero.Zero.
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (NatWithZero.subtraction.specification
         NatWithZero.Zero NatWithZero.Zero NatWithZero.Zero),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma below
      : (NatWithZero.Zero < NatWithZero.Positive (Bin.to_nat &q))%nat_with_zero.
    {
      simpl NatWithZero.LessThan in |- *.
      exists (Bin.to_nat &q).
      simpl in |- *.
      quod idem est.
    }
    leibniz (NatWithZero.subtraction.truncation &below) in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma sum
      : (NatWithZero.Zero + NatWithZero.Positive (Bin.to_nat &p))%nat_with_zero
        = NatWithZero.Positive (Bin.to_nat &p).
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (NatWithZero.subtraction.specification
         (NatWithZero.Positive (Bin.to_nat &p)) NatWithZero.Zero
         (NatWithZero.Positive (Bin.to_nat &p))),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    let proof h := Bin.conversion.difference &p &q.
    extro &h.
    match (Bin.diff &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      lemma below
        : (NatWithZero.Positive (Bin.to_nat &p)
           < NatWithZero.Positive (Bin.to_nat &q))%nat_with_zero.
      {
        simpl NatWithZero.LessThan in |- *.
        simpl Nat.LessThan in &h.
        match &h with | k e end.
        exists &k.
        simpl in |- *.
        leibniz &e in |- *.
        quod idem est.
      }
      leibniz (NatWithZero.subtraction.truncation &below) in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (NatWithZero.Positive (Bin.to_nat &q) + NatWithZero.Zero)%nat_with_zero
          = NatWithZero.Positive (Bin.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (NatWithZero.subtraction.specification
           (NatWithZero.Positive (Bin.to_nat &p))
           (NatWithZero.Positive (Bin.to_nat &q)) NatWithZero.Zero),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (NatWithZero.Positive (Bin.to_nat &q)
           + NatWithZero.Positive (Bin.to_nat &d))%nat_with_zero
          = NatWithZero.Positive (Bin.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (NatWithZero.subtraction.specification
           (NatWithZero.Positive (Bin.to_nat &p))
           (NatWithZero.Positive (Bin.to_nat &q))
           (NatWithZero.Positive (Bin.to_nat &d))),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
Qed.

Module subtraction. (* conversion.subtraction *)

(* conversion.subtraction.saturating *)
Theorem saturating
  : forall (m : BinWithZero) (n : BinWithZero) .
      to_nat_with_zero (saturating_sub m n)
      = NatWithZero.saturating_sub (to_nat_with_zero m) (to_nat_with_zero n).
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
    let proof h := Bin.conversion.difference &p &q.
    extro &h.
    match (Bin.diff &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      let proof le : (Bin.to_nat &p <= Bin.to_nat &q)%nat := disjoin _, &h.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      let proof le : (Bin.to_nat &p <= Bin.to_nat &q)%nat := disjoin &h, _.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      leibniz <- &h in |- *.
      leibniz (Nat.addition.commutativity (Bin.to_nat &q) (Bin.to_nat &d)) in |- *.
      leibniz (Nat.subtraction.inversion.of.addition (Bin.to_nat &d) (Bin.to_nat &q))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End subtraction. (* conversion.subtraction *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {m : BinWithZero} {n : BinWithZero} .
      to_nat_with_zero m = to_nat_with_zero n -> m = n.
Proof.
  intros m n e.
  leibniz <- (conversion.section &m), <- (conversion.section &n) in |- *.
  leibniz &e in |- *.
  quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (m : BinWithZero) (n : BinWithZero) .
      m < n <-> (to_nat_with_zero m < to_nat_with_zero n)%nat_with_zero.
Proof.
  intros m n.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl NatWithZero.LessThan in |- *.
    exists (Bin.to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &m (+ &k)) in |- *.
    simpl in |- *.
    quod idem est.
  -
    intro h.
    simpl NatWithZero.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (Bin.from_nat &j).
    lemma f : to_nat_with_zero (&m + (+ Bin.from_nat &j)) = to_nat_with_zero &n.
    {
      leibniz (conversion.addition &m (+ Bin.from_nat &j)) in |- *.
      simpl in |- *.
      leibniz (Bin.conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

(* conversion.appending *)
Theorem appending
  : forall (bit : Bool) (n : BinWithZero) .
      to_nat_with_zero (append_bit bit n)
      = match bit with
        | true  => NatWithZero.inc (to_nat_with_zero n + to_nat_with_zero n)%nat_with_zero
        | false => (to_nat_with_zero n + to_nat_with_zero n)%nat_with_zero
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

Module left. (* conversion.left *)

(* conversion.left.shift *)
Theorem shift
  : forall (n : BinWithZero) (k : NatWithZero) .
      to_nat_with_zero (shift_left n k)
      = (to_nat_with_zero n
         * NatWithZero.Positive (Nat.Successor Nat.One) ^ k)%nat_with_zero.
Proof.
  intros n k.
  match k with | | k' end.
  -
    simpl shift_left, NatWithZero.power in |- *.
    let proof i := NatWithZero.multiplication.identity (to_nat_with_zero &n).
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
                   (Bin.to_nat &p) (Nat.Successor Nat.One)) in |- *.
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
                   (Bin.to_nat &p)
                   (Nat.power (Nat.Successor Nat.One) &k'')
                   (Nat.power (Nat.Successor Nat.One) &k'')) in |- *.
        quod idem est.
Qed.

End left. (* conversion.left *)

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : BinWithZero) (m : BinWithZero) (n : BinWithZero) .
      (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  lemma f : to_nat_with_zero ((&l + &m) + &n) = to_nat_with_zero (&l + (&m + &n)).
  {
    leibniz (conversion.addition (&l + &m) &n), (conversion.addition &l &m),
            (conversion.addition &l (&m + &n)), (conversion.addition &m &n) in |- *.
    ipso (NatWithZero.addition.associativity
            (to_nat_with_zero &l) (to_nat_with_zero &m) (to_nat_with_zero &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m + n = n + m.
Proof.
  intros m n.
  lemma f : to_nat_with_zero (&m + &n) = to_nat_with_zero (&n + &m).
  {
    leibniz (conversion.addition &m &n), (conversion.addition &n &m) in |- *.
    ipso (NatWithZero.addition.commutativity (to_nat_with_zero &m) (to_nat_with_zero &n)).
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
  let proof c := NatWithZero.addition.cancellation
                   (to_nat_with_zero &m) (to_nat_with_zero &n) (to_nat_with_zero &k).
  match &c with | l r end.
  divide et impera.
  -
    intro e.
    let proof f := congru to_nat_with_zero, &e.
    leibniz (conversion.addition &m &n), (conversion.addition &m &k) in &f.
    ipso (conversion.injectivity (&l &f)).
  -
    intro e.
    let proof f := congru to_nat_with_zero, &e.
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
  lemma f : to_nat_with_zero ((&l * &m) * &n) = to_nat_with_zero (&l * (&m * &n)).
  {
    leibniz (conversion.multiplication (&l * &m) &n), (conversion.multiplication &l &m),
            (conversion.multiplication &l (&m * &n)), (conversion.multiplication &m &n)
      in |- *.
    ipso (NatWithZero.multiplication.associativity
            (to_nat_with_zero &l) (to_nat_with_zero &m) (to_nat_with_zero &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.commutativity *)
Theorem commutativity
  : forall (m : BinWithZero) (n : BinWithZero) . m * n = n * m.
Proof.
  intros m n.
  lemma f : to_nat_with_zero (&m * &n) = to_nat_with_zero (&n * &m).
  {
    leibniz (conversion.multiplication &m &n), (conversion.multiplication &n &m) in |- *.
    ipso (NatWithZero.multiplication.commutativity
            (to_nat_with_zero &m) (to_nat_with_zero &n)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (n : BinWithZero) . ((+ Bin.One) * n = n) /\ (n * (+ Bin.One) = n).
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
      let proof i := Bin.multiplication.identity &p.
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
  let proof d := NatWithZero.multiplication.distributivity.over.addition
                   (to_nat_with_zero &x) (to_nat_with_zero &y) (to_nat_with_zero &z).
  match &d with | l r end.
  divide et impera.
  -
    lemma f : to_nat_with_zero (&x * (&y + &z)) = to_nat_with_zero ((&x * &y) + (&x * &z)).
    {
      leibniz (conversion.multiplication &x (&y + &z)), (conversion.addition &y &z),
              (conversion.addition (&x * &y) (&x * &z)),
              (conversion.multiplication &x &y), (conversion.multiplication &x &z) in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_nat_with_zero ((&y + &z) * &x) = to_nat_with_zero ((&y * &x) + (&z * &x)).
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
  ipso (NatWithZero.order.strict.irreflexivity (to_nat_with_zero &n)
          (modus aequans (conversion.order &n &n), &h)).
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : BinWithZero} {m : BinWithZero} {n : BinWithZero} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  let proof k := NatWithZero.order.strict.transitivity
                   (modus aequans (conversion.order &l &m), &h1)
                   (modus aequans (conversion.order &m &n), &h2).
  ipso (modus aequans (conversion.order &l &n), &k).
Qed.

(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (n : BinWithZero) . Accessible (<) n.
Proof.
  intro n.
  lemma descent
    : Descent.Step (Induced NatWithZero.LessThan to_nat_with_zero)
        (fun (x : BinWithZero) . Accessible (<) x).
  {
    intros x recurse.
    ipso (Accessible_introduction
            (fun (y : BinWithZero) (h : y < &x) .
               &recurse y (Induced.introduction (modus aequans (conversion.order y &x), h)))).
  }
  ipso (Accessible.recursion &descent &n
          (@accessibility _ _ (WellFounded.induced NatWithZero.LessThan to_nat_with_zero _) &n)).
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
  let proof s := NatWithZero.comparison.specification
                   (to_nat_with_zero &m) (to_nat_with_zero &n).
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
      ipso (modus aequans &equality, (congru to_nat_with_zero, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : BinWithZero) (n : BinWithZero) .
      compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  leibniz (conversion.comparison &m &n), (conversion.comparison &n &m) in |- *.
  ipso (NatWithZero.comparison.antisymmetry (to_nat_with_zero &m) (to_nat_with_zero &n)).
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

Module narrowing. (* narrowing *)

Module bin. (* narrowing.bin *)

(* narrowing.bin.retraction *)
Theorem retraction
  : forall (p : Bin) . to_bin (+ p) = Some p.
Proof.
  intro p.
  simpl to_bin in |- *.
  quod idem est.
Qed.

(* narrowing.bin.specification *)
Theorem specification
  : forall (n : BinWithZero) (p : Bin) . to_bin n = Some p <-> n = + p.
Proof.
  intros n p.
  divide et impera.
  -
    intro e.
    match n with | | q end.
    +
      simpl to_bin in &e.
      ex &e quodlibet.
    +
      simpl to_bin in &e.
      let proof f := Option.some.injectivity &e.
      leibniz &f in |- *.
      quod idem est.
  -
    intro e.
    leibniz &e in |- *.
    ipso (narrowing.bin.retraction &p).
Qed.

(* narrowing.bin.failure *)
Theorem failure
  : forall (n : BinWithZero) . to_bin n = None <-> n = 0.
Proof.
  intro n.
  divide et impera.
  -
    intro e.
    match n with | | q end.
    +
      quod idem est.
    +
      simpl to_bin in &e.
      ex &e quodlibet.
  -
    intro e.
    leibniz &e in |- *.
    simpl to_bin in |- *.
    quod idem est.
Qed.

End bin. (* narrowing.bin *)

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
  : forall (n : BinWithZero) (k : NatWithZero) . shift_right (shift_left n k) k = n.
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

Module right. (* shift.right *)

(* shift.right.successor *)
Theorem successor
  : forall (n : BinWithZero) (i : NatWithZero) .
      shift_right n (NatWithZero.inc i) = shift_right (halve n) i.
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

End right. (* shift.right *)

End shift. (* shift *)

Module bit. (* bit *)

(* bit.absence *)
Theorem absence
  : forall (i : NatWithZero) . test_bit 0 i = false.
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
      test_bit (append_bit bit n) NatWithZero.Zero = bit.
Proof.
  intros bit n.
  simpl test_bit, shift_right in |- *.
  match n with | | p end; match bit with | | end; simpl in |- *; quod idem est.
Qed.

(* bit.successor *)
Theorem successor
  : forall (bit : Bool) (n : BinWithZero) (i : NatWithZero) .
      test_bit (append_bit bit n) (NatWithZero.inc i) = test_bit n i.
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
 * of [NatWithZero] and [Integer] as well, so all three write theirs with the
 * prefix.
 *)
Abbreviation BinWithZero := BinWithZero.T.

(* Makes the notations declared in [Module BinWithZero] usable in every
 * file that imports this one, as [(m + n)%b] or under an opened
 * [jwa_bin_with_zero_scope]. Only the notations are exported: [add] and
 * the laws still need the [BinWithZero.] prefix, and the local aliases
 * [0] and [+ p] stay inside the module.
 *)
Export (notations) BinWithZero.

(* A number of the type is written in binary digits under its scope, [1011%b]
 * for eleven, and a closed one prints that way; a literal with any other
 * digit is refused.
 *)
Number Notation BinWithZero.T BinWithZero.from_numeral BinWithZero.to_numeral
  : jwa_bin_with_zero_scope.

(* A [Bin] stands wherever a [BinWithZero] is expected, read as its
 * [Positive], and the conversion is printed where it happened.
 *)
Coercion BinWithZero.Positive : Bin >-> BinWithZero.
Add Printing Coercion BinWithZero.Positive.

(* Declared inside [Module BinWithZero], whose proofs use it; an instance
 * declared there is dropped at the module's [End], so it is announced again
 * here.
 *)
Existing Instance BinWithZero.comparable.

Instance BinWithZero_less_than_well_founded
  : WellFounded (<)%b :=
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
  : Monoid BinWithZero.mul Bin.One := {|
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
      Bin.One :=
  {| Semiring.abelian_monoid := BinWithZero_add_abelian_monoid
   ; Semiring.monoid         := BinWithZero_mul_monoid
   ; Semiring.distributivity := BinWithZero.multiplication.distributivity.over.addition
   ; Semiring.annihilation   := BinWithZero.multiplication.annihilation |}.
