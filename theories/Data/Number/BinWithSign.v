(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Bin.
From jwa Require Import Data.Number.BinWithZero.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

(* A module may carry the type's name; its members read [BinWithSign.negate].
 * The type and its ctors are declared inside it: [NatWithZero], [Integer] and
 * [BinWithZero] declare [Zero] and [Positive] too, and across files a
 * duplicate ctor name rebinds the bare one silently and with no warning.
 *)
Module BinWithSign. (* BinWithSign *)

(* Both sign cases wrap a [Bin], so a nonzero value carries its magnitude in
 * binary and the arithmetic reduces to [Bin]'s, as [Integer]'s reduces to
 * [Nat]'s.
 *
 * Three cases rather than a sign beside a [BinWithZero]: [Bin] has no zero,
 * so zero has exactly one spelling here. A sign paired with a magnitude that
 * can itself be zero admits both [+ 0] and [- 0], and equality on this type
 * is structural.
 *)
Inductive T : Type :=
  | Negative : Bin -> T
  | Zero     : T
  | Positive : Bin -> T.

(* The carrier is named [T] so that the type itself reads [BinWithSign] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End BinWithSign].
 *)
Abbreviation BinWithSign := T.

(* The eliminator behind the [destruct] tactic, written out: no recursion,
 * since no ctor carries a [BinWithSign].
 *)
Definition induction
  : forall (P : BinWithSign -> Prop) .
      (forall (p : Bin) . P (Negative p)) ->
      P Zero ->
      (forall (p : Bin) . P (Positive p)) ->
      (forall (x : BinWithSign) . P x)
  := fun (P : BinWithSign -> Prop)
       (negative : forall (p : Bin) . P (Negative p))
       (zero : P Zero)
       (positive : forall (p : Bin) . P (Positive p))
       (x : BinWithSign) .
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* Short spellings for this module only: [Local] keeps them out of every file
 * that imports this one. [+ p] and [- p] are prefixes; this round declares no
 * infix [+] for them to sit beside.
 *)
Local Notation "0"   := Zero (only parsing).
Local Notation "+ p" := (Positive p) (at level 35, right associativity, only parsing).
Local Notation "- p" := (Negative p) (at level 35, right associativity, only parsing).

(* [BinWithSign -> BinWithSign] *)
Definition negate := fun (x : BinWithSign) .
  match x with
  | - p => + p
  | 0   => 0
  | + p => - p
  end.

(* [BinWithSign -> BinWithZero] *)
Definition abs := fun (x : BinWithSign) .
  match x with
  | - p => BinWithZero.Positive p
  | 0   => BinWithZero.Zero
  | + p => BinWithZero.Positive p
  end.

(* The positive part, zero below it. It is what lets an addition be written as
 * one difference of two nonnegative numbers rather than as nine sign cases.
 *)
(* [BinWithSign -> BinWithZero] *)
Definition ramp := fun (x : BinWithSign) .
  match x with
  | - _ => BinWithZero.Zero
  | 0   => BinWithZero.Zero
  | + p => BinWithZero.Positive p
  end.

(* [Bin -> BinWithSign] *)
Definition from_bin := fun (p : Bin) . (+ p).

(* [BinWithZero -> BinWithSign] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n return BinWithSign with
  | BinWithZero.Zero       => 0
  | BinWithZero.Positive p => + p
  end.

(* The conversions down: [None] below zero for [BinWithZero], and at or below
 * it for [Bin], which has no zero to answer with.
 *)
(* [BinWithSign -> Option BinWithZero] *)
Definition to_bin_with_zero := fun (x : BinWithSign) .
  match x with
  | - _ => None
  | 0   => Some BinWithZero.Zero
  | + p => Some (BinWithZero.Positive p)
  end.

(* [BinWithSign -> Option Bin] *)
Definition to_bin := fun (x : BinWithSign) .
  match x with
  | - _ => None
  | 0   => None
  | + p => Some p
  end.

(* The bridge to the unary signed type, used to state the laws: [Bin.to_nat]
 * is unary, so this is for proofs, not for computing.
 *)
(* [BinWithSign -> Integer] *)
Definition to_integer := fun (x : BinWithSign) .
  match x with
  | - p => Integer.Negative (Bin.to_nat p)
  | 0   => Integer.Zero
  | + p => Integer.Positive (Bin.to_nat p)
  end.

(* [Bin.diff p q] forgets the magnitude when [p] is the smaller of the two,
 * reporting a bare [Lt], so the size of a negative answer has to be fetched
 * from the other direction. Both directions are taken and whichever reports
 * [Gt] carries the magnitude; equal arguments report [Eq] both ways and fall
 * through to zero. Total, with no unreachable branch, at the price of walking
 * the bits twice.
 *)
(* [Bin -> Bin -> BinWithSign] *)
Definition bin_difference := fun (p : Bin) (q : Bin) .
  match Bin.diff p q, Bin.diff q p with
  | Bin.Gt d, _ => + d
  | _, Bin.Gt d => - d
  | _, _        => 0
  end.

(* [BinWithZero -> BinWithZero -> BinWithSign] *)
Definition bin_with_zero_difference := fun (a : BinWithZero) (b : BinWithZero) .
  match a, b with
  | BinWithZero.Zero, BinWithZero.Zero             => 0
  | BinWithZero.Zero, BinWithZero.Positive q       => - q
  | BinWithZero.Positive p, BinWithZero.Zero       => + p
  | BinWithZero.Positive p, BinWithZero.Positive q => bin_difference p q
  end.

(* Between two negatives the order reverses, the larger magnitude being the
 * smaller number, so those two arguments reach [Bin.compare] the other way
 * round.
 *)
(* [BinWithSign -> BinWithSign -> Comparison] *)
Definition compare := fun (x : BinWithSign) (y : BinWithSign) .
  match x with
  | - p =>
      match y with
      | - q => Bin.compare q p
      | 0   => Comparison.Lt
      | + _ => Comparison.Lt
      end
  | 0 =>
      match y with
      | - _ => Comparison.Gt
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match y with
      | - _ => Comparison.Gt
      | 0   => Comparison.Gt
      | + q => Bin.compare p q
      end
  end.

(* [BinWithSign -> BinWithSign -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* The magnitude is read by [BinWithZero], which already walks decimal digits
 * as binary ones, and the sign is applied after. [- 0] therefore reads as
 * zero rather than being refused: this type has one zero, and [negate] sends
 * it to itself. Hexadecimal is refused as it is there, so the digits a
 * literal may carry are exactly [0] and [1].
 *)
(* [Numeral.Signed -> Option BinWithSign] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      Option.map from_bin_with_zero (BinWithZero.from_digits BinWithZero.Zero d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      Option.map (fun (n : BinWithZero) . negate (from_bin_with_zero n))
        (BinWithZero.from_digits BinWithZero.Zero d)
  | Numeral.Signed.Hexadecimal _ => None
  end.

(* Zero prints as [0] and not as [-0]: [Numeral.Decimal.Signed] has no third
 * case for it, so one of the two signs has to carry it and the positive one
 * is what a reader expects.
 *)
(* [BinWithSign -> Numeral.Signed] *)
Definition to_numeral := fun (x : BinWithSign) .
  match x with
  | - p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative
           (BinWithZero.to_digits p Numeral.Decimal.Digits.End))
  | 0 =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
           (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | + p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
           (BinWithZero.to_digits p Numeral.Decimal.Digits.End))
  end.

(* Everything here is stated against [Integer], the unary signed type, through
 * [to_integer]. That is where the meaning of a sign and a magnitude is already
 * proved, so a law holds here as soon as the two agree.
 *)
Module conversion. (* conversion *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : BinWithSign} {y : BinWithSign} .
      to_integer x = to_integer y -> x = y.
Proof.
  intros x y e.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      leibniz (Bin.conversion.injectivity
                 (Integer.magnitude.negative.injectivity &e)) in |- *.
      quod idem est.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      quod idem est.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      ex &e quodlibet.
    +
      simpl to_integer in &e.
      leibniz (Bin.conversion.injectivity
                 (Integer.magnitude.positive.injectivity &e)) in |- *.
      quod idem est.
Qed.

(* Seven of the nine sign pairs hold by reduction alone, both sides being the
 * same [Comparison] constructor. The two like-signed pairs are where the
 * magnitudes are consulted, and between two negatives the arguments arrive at
 * [Bin.compare] reversed, matching how [Integer.compare] reverses them.
 *)
(* conversion.comparison *)
Theorem comparison
  : forall (x : BinWithSign) (y : BinWithSign) .
      compare x y = Integer.compare (to_integer x) (to_integer y).
Proof.
  intros x y.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    + ipso (Bin.conversion.comparison &q &p).
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  -
    match &y with | q | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  -
    match &y with | q | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
    + ipso (Bin.conversion.comparison &p &q).
Qed.

(* The two-pass bridge against the unary one, which settles that taking both
 * directions of [Bin.diff] recovers what a single pass throws away.
 *
 * [Bin.conversion.difference] reports what each direction means in [Nat], and
 * the two reports together decide each of the nine pairs. A [Gt] in the first
 * pass answers on its own, so the second is never consulted there. Of the six
 * pairs left, four cannot arise and are discharged rather than computed: two
 * strict inequalities facing each other, a strict inequality against an
 * equation, and -- the one that is not an order fact -- an equation against a
 * [Gt], which would make [to_nat p + to_nat d] equal [to_nat p], and no [Bin]
 * is zero.
 *)
(* conversion.difference *)
Theorem difference
  : forall (p : Bin) (q : Bin) .
      to_integer (bin_difference p q)
    = Integer.nat_difference (Bin.to_nat p) (Bin.to_nat q).
Proof.
  intros p q.
  simpl bin_difference in |- *.
  let proof forward := Bin.conversion.difference &p &q.
  let proof backward := Bin.conversion.difference &q &p.
  extros &forward &backward.
  match (Bin.diff &p &q) with | | | d end.
  -
    intro forward.
    match (Bin.diff &q &p) with | | | d end.
    +
      intro backward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p)
            (Nat.order.strict.transitivity &forward &backward)) quodlibet.
    +
      intro backward.
      leibniz &backward in &forward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p) &forward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.negative.specification
                 (Bin.to_nat &p) (Bin.to_nat &q) (Bin.to_nat &d)), &backward).
  -
    intro forward.
    match (Bin.diff &q &p) with | | | d end.
    +
      intro backward.
      leibniz &forward in &backward.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &q) &backward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.zero.specification
                 (Bin.to_nat &p) (Bin.to_nat &q)), &forward).
    +
      intro backward.
      leibniz <- &forward in &backward.
      let proof below := Nat.addition.order.extensivity (Bin.to_nat &p) (Bin.to_nat &d).
      leibniz &backward in &below.
      ex (Nat.order.strict.irreflexivity (Bin.to_nat &p) &below) quodlibet.
  -
    intros forward backward.
    symm in |- *.
    ipso (modus aequans
            (Integer.difference.nat.positive.specification
               (Bin.to_nat &p) (Bin.to_nat &q) (Bin.to_nat &d)), &forward).
Qed.

End conversion. (* conversion *)

End BinWithSign. (* BinWithSign *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinWithSign], not [BinWithSign.T]. [Zero] and [Positive] name ctors of
 * three other number types, so all four write theirs with the prefix.
 *)
Abbreviation BinWithSign := BinWithSign.T.

(* What makes the minus of a negative literal parse. [Numeral.Signed] lets
 * [from_numeral] *receive* a sign, but it does not put one in the grammar:
 * with the prelude off nothing makes [-1011] a term, and without this line
 * [(-1011)%b] is a syntax error at the [-]. Declared outside the module so it
 * does not collide with the [Local] [- p] for [Negative] inside it, and
 * scoped, so [-] keeps whatever else it means elsewhere.
 *
 * [only parsing] costs nothing here: a negative value still prints as
 * [(-1011)%b], because that comes from [to_numeral] below rather than from
 * this notation, so [negate] goes on printing by name as every other
 * operation in the tree does.
 *)
Notation "- x" := (BinWithSign.negate x)
  (at level 35, right associativity, only parsing)
  : jwa_bin_with_sign_scope.

(* A number of the type is written in binary digits under its scope, [1011%b]
 * for eleven and [(-1011)%b] for minus eleven, and a closed one prints that
 * way; a literal with any other digit is refused.
 *)
Number Notation BinWithSign.T BinWithSign.from_numeral BinWithSign.to_numeral
  : jwa_bin_with_sign_scope.
