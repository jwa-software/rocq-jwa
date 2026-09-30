(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Binary.BinBase.
From jwa Require Import Data.Number.Binary.BinWithZero.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [Bin.negate].
 * The type and its ctors are declared inside it: [Nat0], [Integer] and
 * [BinWithZero] declare [Zero] and [Positive] too, and across files a
 * duplicate ctor name rebinds the bare one silently and with no warning.
 *)
Module Bin. (* Bin *)

(* Both sign cases wrap a [BinBase], so a nonzero value carries its magnitude in
 * binary and the arithmetic reduces to [BinBase]'s, as [Integer]'s reduces to
 * [Nat]'s.
 *
 * Three cases rather than a sign beside a [BinWithZero]: [BinBase] has no zero,
 * so zero has exactly one spelling here. A sign paired with a magnitude that
 * can itself be zero admits both [+ 0] and [- 0], and equality on this type
 * is structural.
 *)
Inductive T : Type :=
  | Negative : BinBase -> T
  | Zero     : T
  | Positive : BinBase -> T.

(* The carrier is named [T] so that the type itself reads [Bin] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End Bin].
 *)
Abbreviation Bin := T.

(* The eliminator behind the [destruct] tactic, written out: no recursion,
 * since no ctor carries a [Bin].
 *)
Definition induction
  : forall (P : Bin -> Prop) .
      (forall (p : BinBase) . P (Negative p)) ->
      P Zero ->
      (forall (p : BinBase) . P (Positive p)) ->
      (forall (x : Bin) . P x)
  := fun (P : Bin -> Prop)
       (negative : forall (p : BinBase) . P (Negative p))
       (zero : P Zero)
       (positive : forall (p : BinBase) . P (Positive p))
       (x : Bin) .
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* Short spellings for this module only: [Local] keeps them out of every file
 * that imports this one. [+ p] and [- p] are prefixes, distinct from the
 * infix [+] declared below.
 *)
Local Notation "0"   := Zero (only parsing).
Local Notation "+ p" := (Positive p) (at level 35, right associativity, only parsing).
Local Notation "- p" := (Negative p) (at level 35, right associativity, only parsing).

(* [Bin -> Bin] *)
Definition negate := fun (x : Bin) .
  match x with
  | - p => + p
  | 0   => 0
  | + p => - p
  end.

(* [Bin -> BinWithZero] *)
Definition abs := fun (x : Bin) .
  match x with
  | - p => BinWithZero.Positive p
  | 0   => BinWithZero.Zero
  | + p => BinWithZero.Positive p
  end.

(* The positive part, zero below it; [add] is written from it. *)
(* [Bin -> BinWithZero] *)
Definition ramp := fun (x : Bin) .
  match x with
  | - _ => BinWithZero.Zero
  | 0   => BinWithZero.Zero
  | + p => BinWithZero.Positive p
  end.

(* [BinBase -> Bin] *)
Definition from_bin_base := fun (p : BinBase) . (+ p).

(* [BinWithZero -> Bin] *)
Definition from_bin_with_zero := fun (n : BinWithZero) .
  match n return Bin with
  | BinWithZero.Zero       => 0
  | BinWithZero.Positive p => + p
  end.

(* The conversions down: [None] below zero for [BinWithZero], and at or below
 * it for [BinBase], which has no zero to answer with.
 *)
(* [Bin -> Option BinWithZero] *)
Definition to_bin_with_zero := fun (x : Bin) .
  match x with
  | - _ => None
  | 0   => Some BinWithZero.Zero
  | + p => Some (BinWithZero.Positive p)
  end.

(* [Bin -> Option BinBase] *)
Definition to_bin_base := fun (x : Bin) .
  match x with
  | - _ => None
  | 0   => None
  | + p => Some p
  end.

(* The bridge to the unary signed type, used to state the laws: [BinBase.to_nat]
 * is unary, so this is for proofs, not for computing.
 *)
(* [Bin -> Integer] *)
Definition to_integer := fun (x : Bin) .
  match x with
  | - p => Integer.Negative (BinBase.to_nat p)
  | 0   => Integer.Zero
  | + p => Integer.Positive (BinBase.to_nat p)
  end.

(* [BinBase.diff p q] forgets the magnitude when [p] is the smaller of the two,
 * reporting a bare [Lt], so the size of a negative answer has to be fetched
 * from the other direction. Both directions are taken and whichever reports
 * [Gt] carries the magnitude; equal arguments report [Eq] both ways and fall
 * through to zero. Total, with no unreachable branch, at the price of walking
 * the bits twice.
 *)
(* [BinBase -> BinBase -> Bin] *)
Definition bin_base_difference := fun (p : BinBase) (q : BinBase) .
  match BinBase.diff p q, BinBase.diff q p with
  | BinBase.Gt d, _ => + d
  | _, BinBase.Gt d => - d
  | _, _            => 0
  end.

(* [BinWithZero -> BinWithZero -> Bin] *)
Definition bin_with_zero_difference := fun (a : BinWithZero) (b : BinWithZero) .
  match a, b with
  | BinWithZero.Zero, BinWithZero.Zero             => 0
  | BinWithZero.Zero, BinWithZero.Positive q       => - q
  | BinWithZero.Positive p, BinWithZero.Zero       => + p
  | BinWithZero.Positive p, BinWithZero.Positive q => bin_base_difference p q
  end.

(* Every value is [ramp x] less [ramp (negate x)], one of which is always
 * zero, so a sum is a single difference of two nonnegative numbers instead of
 * nine sign cases. [Integer.add] is written the same way over [Nat0].
 *)
(* [Bin -> Bin -> Bin] *)
Definition add := fun (x : Bin) (y : Bin) .
  bin_with_zero_difference (ramp x + ramp y)%bin_with_zero
                           (ramp (negate x) + ramp (negate y))%bin_with_zero.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Bin] a client writes [(x + y)%b]. [only parsing]
 * keeps goals printing the operations by name. The prefix [+ p] above is a
 * separate notation and coexists with this infix one, as in [Integer].
 *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_bin_scope.

Local Open Scope jwa_bin_scope.

(* No infix [-]: the scope's [-] is the prefix negation that makes [(-1011)%b]
 * parse, and [Integer] declares none either.
 *)
(* [Bin -> Bin -> Bin] *)
Definition sub := fun (x : Bin) (y : Bin) . x + negate y.

(* The magnitudes multiply in [BinBase], and the sign is positive exactly when the
 * two signs agree.
 *)
(* [Bin -> Bin -> Bin] *)
Definition mul := fun (x : Bin) (y : Bin) .
  match x with
  | - p =>
      match y with
      | - q => + (p * q)%bin_base
      | 0   => 0
      | + q => - (p * q)%bin_base
      end
  | 0 => 0
  | + p =>
      match y with
      | - q => - (p * q)%bin_base
      | 0   => 0
      | + q => + (p * q)%bin_base
      end
  end.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_bin_scope.

(* The divisor is a [BinBase], so it is never zero: the magnitude is divided and
 * the sign carried over, so the quotient rounds toward zero.
 *)
(* [Bin -> BinBase -> Bin] *)
Definition divide := fun (x : Bin) (d : BinBase) .
  match x with
  | - p => negate (from_bin_with_zero (p /. d)%bin_with_zero)
  | 0   => 0
  | + p => from_bin_with_zero (p /. d)%bin_with_zero
  end.

Notation "x /. y" := (divide x y) (only parsing)
  : jwa_bin_scope.

(* The witness is a [BinBase], so it is never zero and [<] is strict.
 *)
(* [Bin -> Bin -> Prop] *)
Definition LessThan := fun (x : Bin) (y : Bin) .
  forsome (k : BinBase) . x + (+ k) = y.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_bin_scope.

(* [Bin -> Bin -> Prop] *)
Definition LessOrEqual := fun (x : Bin) (y : Bin) . x = y \/ x < y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_bin_scope.

(* The reversed spellings name no new relation: [x > y] is [y < x] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_bin_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_bin_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_bin_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_bin_scope.

(* Between two negatives the order reverses, the larger magnitude being the
 * smaller number, so those two arguments reach [BinBase.compare] the other way
 * round.
 *)
(* [Bin -> Bin -> Comparison] *)
Definition compare := fun (x : Bin) (y : Bin) .
  match x with
  | - p =>
      match y with
      | - q => BinBase.compare q p
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
      | + q => BinBase.compare p q
      end
  end.

(* [Bin -> Bin -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Bin -> Bin -> Bin] *)
Abbreviation min := (Comparable.min compare).

(* [Bin -> Bin -> Bin] *)
Abbreviation max := (Comparable.max compare).

(* [BinWithZero] reads the magnitude, the sign is applied after. [- 0] reads as
 * zero, this type having one zero and [negate] sending it to itself.
 * Hexadecimal is refused there too, so a literal carries only [0] and [1].
 *)
(* [Numeral.Signed -> Option Bin] *)
Definition from_numeral := fun (s : Numeral.Signed) .
  match s with
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Positive d) =>
      Option.map from_bin_with_zero (BinWithZero.from_digits BinWithZero.Zero d)
  | Numeral.Signed.Decimal (Numeral.Decimal.Signed.Negative d) =>
      Option.map (fun (n : BinWithZero) . negate (from_bin_with_zero n))
        (BinWithZero.from_digits BinWithZero.Zero d)
  | Numeral.Signed.Hexadecimal _ => None
  end.

(* Zero prints as [0], not [-0]: [Numeral.Decimal.Signed] has only the two
 * signs, so one of them carries zero.
 *)
(* [Bin -> Numeral.Signed] *)
Definition to_numeral := fun (x : Bin) .
  match x with
  | - p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Negative
          (BinBase.to_digits p Numeral.Decimal.Digits.End))
  | 0 =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End))
  | + p =>
      Numeral.Signed.Decimal
        (Numeral.Decimal.Signed.Positive
          (BinBase.to_digits p Numeral.Decimal.Digits.End))
  end.

(* The laws state this type against [Integer] through [to_integer]. The signed
 * laws are proved there, so agreement carries them.
 *)
Module conversion. (* conversion *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {x : Bin} {y : Bin} .
      to_integer x = to_integer y -> x = y.
Proof.
  intros x y e.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    +
      simpl to_integer in &e.
      leibniz (BinBase.conversion.injectivity
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
      leibniz (BinBase.conversion.injectivity
                 (Integer.magnitude.positive.injectivity &e)) in |- *.
      quod idem est.
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (x : Bin) (y : Bin) .
      compare x y = Integer.compare (to_integer x) (to_integer y).
Proof.
  intros x y.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    + ipso (BinBase.conversion.comparison &q &p).
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
    + ipso (BinBase.conversion.comparison &p &q).
Qed.

(* Of the nine pairs of [BinBase.diff] outcomes, a [Gt] in the first answers alone.
 * Four of the remaining six cannot arise: [Lt] facing [Lt] or [Eq] either way
 * contradicts the order on [Nat], and [Eq] facing [Gt] would need
 * [to_nat p + to_nat d] to equal [to_nat p], which no [BinBase] permits.
 *)
(* conversion.difference *)
Theorem difference
  : forall (p : BinBase) (q : BinBase) .
      to_integer (bin_base_difference p q)
    = Integer.nat_difference (BinBase.to_nat p) (BinBase.to_nat q).
Proof.
  intros p q.
  simpl bin_base_difference in |- *.
  let proof forward := BinBase.conversion.difference &p &q.
  let proof backward := BinBase.conversion.difference &q &p.
  extros &forward &backward.
  match (BinBase.diff &p &q) with | | | d end.
  -
    intro forward.
    match (BinBase.diff &q &p) with | | | d end.
    +
      intro backward.
      ex (Nat.order.strict.irreflexivity (BinBase.to_nat &p)
            (Nat.order.strict.transitivity &forward &backward)) quodlibet.
    +
      intro backward.
      leibniz &backward in &forward.
      ex (Nat.order.strict.irreflexivity (BinBase.to_nat &p) &forward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.negative.specification
                 (BinBase.to_nat &p) (BinBase.to_nat &q) (BinBase.to_nat &d)), &backward).
  -
    intro forward.
    match (BinBase.diff &q &p) with | | | d end.
    +
      intro backward.
      leibniz &forward in &backward.
      ex (Nat.order.strict.irreflexivity (BinBase.to_nat &q) &backward) quodlibet.
    +
      intro backward.
      symm in |- *.
      ipso (modus aequans
              (Integer.difference.nat.zero.specification
                 (BinBase.to_nat &p) (BinBase.to_nat &q)), &forward).
    +
      intro backward.
      leibniz <- &forward in &backward.
      let proof below := Nat.addition.order.extensivity (BinBase.to_nat &p) (BinBase.to_nat &d).
      leibniz &backward in &below.
      ex (Nat.order.strict.irreflexivity (BinBase.to_nat &p) &below) quodlibet.
  -
    intros forward backward.
    symm in |- *.
    ipso (modus aequans
            (Integer.difference.nat.positive.specification
               (BinBase.to_nat &p) (BinBase.to_nat &q) (BinBase.to_nat &d)), &forward).
Qed.

(* conversion.negation *)
Theorem negation
  : forall (x : Bin) .
      to_integer (negate x) = Integer.negate (to_integer x).
Proof.
  intro x.
  match &x with | p | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

Module difference. (* conversion.difference *)

(* [difference] with the zero cases added. *)
(* conversion.difference.extension *)
Theorem extension
  : forall (a : BinWithZero) (b : BinWithZero) .
      to_integer (bin_with_zero_difference a b)
    = Integer.nat0_difference
        (BinWithZero.to_nat0 a) (BinWithZero.to_nat0 b).
Proof.
  intros a b.
  match &a with | | p end.
  - match &b with | | q end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      quod idem est.
  - match &b with | | q end.
    + simpl in |- *.
      quod idem est.
    + ipso (conversion.difference &p &q).
Qed.

End difference. (* conversion.difference *)

(* conversion.addition *)
Theorem addition
  : forall (x : Bin) (y : Bin) .
      to_integer (x + y) = Integer.add (to_integer x) (to_integer y).
Proof.
  intros x y.
  (* [Integer.add]'s body is an application, not a match, so Rocq's [simpl]
   * leaves it folded.
   *)
  simpl add, Integer.add in |- *.
  match &x with | p | | p end.
  -
    match &y with | q | | q end.
    +
      simpl in |- *.
      leibniz (BinBase.conversion.addition &p &q) in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
    +
      ipso (conversion.difference &q &p).
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
    +
      ipso (conversion.difference &p &q).
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      leibniz (BinBase.conversion.addition &p &q) in |- *.
      quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (x : Bin) (y : Bin) .
      x < y <-> (to_integer x < to_integer y)%z.
Proof.
  intros x y.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Integer.LessThan in |- *.
    exists (BinBase.to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &x (Positive &k)) in |- *.
    simpl to_integer in |- *.
    quod idem est.
  -
    intro h.
    simpl Integer.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (BinBase.from_nat &j).
    lemma f : to_integer (&x + (+ BinBase.from_nat &j)) = to_integer &y.
    {
      leibniz (conversion.addition &x (Positive (BinBase.from_nat &j))) in |- *.
      simpl to_integer in |- *.
      leibniz (BinBase.conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (x : Bin) (y : Bin) .
      to_integer (x * y) = Integer.mul (to_integer x) (to_integer y).
Proof.
  intros x y.
  match &x with | p | | p end; match &y with | q | | q end; simpl in |- *.
  -
    leibniz (BinBase.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    leibniz (BinBase.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    quod idem est.
  -
    quod idem est.
  -
    leibniz (BinBase.conversion.multiplication &p &q) in |- *.
    quod idem est.
  -
    quod idem est.
  -
    leibniz (BinBase.conversion.multiplication &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.division *)
Theorem division
  : forall (x : Bin) (d : BinBase) .
      to_integer (x /. d) = (to_integer x /. BinBase.to_nat d)%z.
Proof.
  intros x d.
  lemma embedding
    : forall (n : BinWithZero) .
        to_integer (from_bin_with_zero n)
        = Integer.from_nat0 (BinWithZero.to_nat0 n).
  {
    intro n.
    match n with | | q end.
    -
      simpl in |- *.
      quod idem est.
    -
      simpl in |- *.
      quod idem est.
  }
  match &x with | p | | p end.
  -
    let proof c
      : BinWithZero.to_nat0 (p /. &d)%bin_with_zero
        = (BinBase.to_nat &p /. BinBase.to_nat &d)%n0
      := BinWithZero.conversion.division p &d.
    simpl divide in |- *.
    simpl to_integer at 2 in |- *.
    simpl Integer.divide in |- *.
    leibniz (conversion.negation (from_bin_with_zero (p /. &d)%bin_with_zero)),
      (&embedding (p /. &d)%bin_with_zero), &c in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    let proof c
      : BinWithZero.to_nat0 (p /. &d)%bin_with_zero
        = (BinBase.to_nat &p /. BinBase.to_nat &d)%n0
      := BinWithZero.conversion.division p &d.
    simpl divide in |- *.
    simpl to_integer at 2 in |- *.
    simpl Integer.divide in |- *.
    leibniz (&embedding (p /. &d)%bin_with_zero), &c in |- *.
    quod idem est.
Qed.

End conversion. (* conversion *)

Module magnitude. (* magnitude *)

Module negative. (* magnitude.negative *)

(* magnitude.negative.injectivity *)
Lemma injectivity
  : forall {p : BinBase} {q : BinBase} . (- p) = - q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : Bin) . match x with | - r => r | 0 => p | + _ => p end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End negative. (* magnitude.negative *)

Module positive. (* magnitude.positive *)

(* magnitude.positive.injectivity *)
Lemma injectivity
  : forall {p : BinBase} {q : BinBase} . (+ p) = + q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : Bin) . match x with | - _ => p | 0 => p | + r => r end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End positive. (* magnitude.positive *)

(* magnitude.injectivity *)
Theorem injectivity
  : forall (p : BinBase) (q : BinBase) .
      ((- p) = - q -> p = q) /\ ((+ p) = + q -> p = q).
Proof.
  intros p q.
  divide et impera.
  - ipso (@magnitude.negative.injectivity p q).
  - ipso (@magnitude.positive.injectivity p q).
Qed.

End magnitude. (* magnitude *)

Module embedding. (* embedding *)

(* embedding.injectivity *)
Theorem injectivity
  : forall {m : BinWithZero} {n : BinWithZero} .
      from_bin_with_zero m = from_bin_with_zero n -> m = n.
Proof.
  intros m n e.
  match &m with | | p end; match &n with | | q end.
  - quod idem est.
  - simpl in &e.
    ex &e quodlibet.
  - simpl in &e.
    ex &e quodlibet.
  - simpl in &e.
    let proof e' := magnitude.positive.injectivity &e.
    leibniz &e' in |- *.
    quod idem est.
Qed.

End embedding. (* embedding *)

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (x : Bin) . negate (negate x) = x.
Proof.
  intro x.
  match &x with | p | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

(* negation.additivity *)
Theorem additivity
  : forall (x : Bin) (y : Bin) .
      negate (x + y) = negate x + negate y.
Proof.
  intros x y.
  lemma f : to_integer (negate (&x + &y)) = to_integer (negate &x + negate &y).
  {
    leibniz (conversion.negation (&x + &y)), (conversion.addition &x &y),
            (conversion.addition (negate &x) (negate &y)),
            (conversion.negation &x), (conversion.negation &y) in |- *.
    ipso (Integer.negation.additivity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

End negation. (* negation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  lemma f : to_integer ((&x + &y) + &z) = to_integer (&x + (&y + &z)).
  {
    leibniz (conversion.addition (&x + &y) &z), (conversion.addition &x &y),
            (conversion.addition &x (&y + &z)), (conversion.addition &y &z) in |- *.
    ipso (Integer.addition.associativity
            (to_integer &x) (to_integer &y) (to_integer &z)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (x : Bin) (y : Bin) . x + y = y + x.
Proof.
  intros x y.
  lemma f : to_integer (&x + &y) = to_integer (&y + &x).
  {
    leibniz (conversion.addition &x &y), (conversion.addition &y &x) in |- *.
    ipso (Integer.addition.commutativity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
Theorem identity : forall (x : Bin) . 0 + x = x.
Proof.
  intro x.
  lemma f : to_integer (0 + &x) = to_integer &x.
  {
    leibniz (conversion.addition 0 &x) in |- *.
    ipso (Integer.addition.left.identity (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (x : Bin) . negate x + x = 0.
Proof.
  intro x.
  lemma f : to_integer (negate &x + &x) = to_integer 0.
  {
    leibniz (conversion.addition (negate &x) &x), (conversion.negation &x) in |- *.
    ipso (Integer.addition.left.inverse (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall {x : Bin} {y : Bin} {z : Bin} .
      x + y = x + z -> y = z.
Proof.
  intros x y z e.
  let proof f := congru to_integer, &e.
  leibniz (conversion.addition &x &y), (conversion.addition &x &z) in &f.
  ipso (conversion.injectivity
          (@Integer.addition.left.cancellation
             (to_integer &x) (to_integer &y) (to_integer &z) &f)).
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
Theorem identity : forall (x : Bin) . x + 0 = x.
Proof.
  intro x.
  lemma f : to_integer (&x + 0) = to_integer &x.
  {
    leibniz (conversion.addition &x 0) in |- *.
    ipso (Integer.addition.right.identity (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (x : Bin) . x + negate x = 0.
Proof.
  intro x.
  lemma f : to_integer (&x + negate &x) = to_integer 0.
  {
    leibniz (conversion.addition &x (negate &x)), (conversion.negation &x) in |- *.
    ipso (Integer.addition.right.inverse (to_integer &x)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall {x : Bin} {y : Bin} {z : Bin} .
      x + y = z + y -> x = z.
Proof.
  intros x y z e.
  let proof f := congru to_integer, &e.
  leibniz (conversion.addition &x &y), (conversion.addition &z &y) in &f.
  ipso (conversion.injectivity
          (@Integer.addition.right.cancellation
             (to_integer &x) (to_integer &z) (to_integer &y) &f)).
Qed.

End right. (* addition.right *)

(* addition.identity *)
Theorem identity
  : forall (x : Bin) . (0 + x = x) /\ (x + 0 = x).
Proof.
  intro x.
  divide et impera.
  - ipso (addition.left.identity  &x).
  - ipso (addition.right.identity &x).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (x : Bin) . (negate x + x = 0) /\ (x + negate x = 0).
Proof.
  intro x.
  divide et impera.
  - ipso (addition.left.inverse  &x).
  - ipso (addition.right.inverse &x).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x + y = x + z -> y = z) /\ (x + y = z + y -> x = z).
Proof.
  intros x y z.
  divide et impera.
  - ipso (@addition.left.cancellation  &x &y &z).
  - ipso (@addition.right.cancellation &x &y &z).
Qed.

End addition. (* addition *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (x : Bin) . ~ (x < x).
Proof.
  simpl (~ _) in |- *.
  intro x.
  intro h.
  ex (Integer.order.strict.irreflexivity (to_integer &x)
        (modus aequans (conversion.order &x &x), &h)) quodlibet.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Bin} {y : Bin} {z : Bin} .
      x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  ipso (modus aequans (conversion.order &x &z),
        (Integer.order.strict.transitivity
           (modus aequans (conversion.order &x &y), &h1)
           (modus aequans (conversion.order &y &z), &h2))).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (x : Bin) (y : Bin) . x * y = y * x.
Proof.
  intros x y.
  lemma f : to_integer (&x * &y) = to_integer (&y * &x).
  {
    leibniz (conversion.multiplication &x &y), (conversion.multiplication &y &x) in |- *.
    ipso (Integer.multiplication.commutativity (to_integer &x) (to_integer &y)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x * y) * z = x * (y * z).
Proof.
  intros x y z.
  lemma f : to_integer ((&x * &y) * &z) = to_integer (&x * (&y * &z)).
  {
    leibniz (conversion.multiplication (&x * &y) &z), (conversion.multiplication &x &y),
            (conversion.multiplication &x (&y * &z)), (conversion.multiplication &y &z)
      in |- *.
    ipso (Integer.multiplication.associativity
            (to_integer &x) (to_integer &y) (to_integer &z)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (x : Bin) . ((+ BinBase.One) * x = x) /\ (x * (+ BinBase.One) = x).
Proof.
  intro x.
  lemma one : to_integer (+ BinBase.One) = Nat.One.
  {
    simpl in |- *.
    quod idem est.
  }
  let proof i := Integer.multiplication.identity (to_integer &x).
  match &i with | l r end.
  divide et impera.
  -
    lemma f : to_integer ((+ BinBase.One) * &x) = to_integer &x.
    {
      leibniz (conversion.multiplication (+ BinBase.One) &x), &one in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_integer (&x * (+ BinBase.One)) = to_integer &x.
    {
      leibniz (conversion.multiplication &x (+ BinBase.One)), &one in |- *.
      ipso &r.
    }
    ipso (conversion.injectivity &f).
Qed.

(* multiplication.annihilation *)
Theorem annihilation
  : forall (x : Bin) . (0 * x = 0) /\ (x * 0 = 0).
Proof.
  intro x.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match &x with | p | | p end; simpl in |- *; quod idem est.
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : Bin) (y : Bin) (z : Bin) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  let proof d := Integer.multiplication.distributivity.over.addition
                   (to_integer &x) (to_integer &y) (to_integer &z).
  match &d with | l r end.
  divide et impera.
  -
    lemma f : to_integer (&x * (&y + &z)) = to_integer ((&x * &y) + (&x * &z)).
    {
      leibniz (conversion.multiplication &x (&y + &z)), (conversion.addition &y &z),
              (conversion.addition (&x * &y) (&x * &z)),
              (conversion.multiplication &x &y), (conversion.multiplication &x &z) in |- *.
      ipso &l.
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_integer ((&y + &z) * &x) = to_integer ((&y * &x) + (&z * &x)).
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

(* multiplication.cancellation *)
Theorem cancellation
  : forall (k : Bin) (x : Bin) (y : Bin) .
      ~ (k = 0) -> k * x = k * y -> x = y.
Proof.
  intros k x y n e.
  lemma m : ~ (to_integer &k = Integer.Zero).
  {
    intro z.
    let proof z : to_integer &k = to_integer 0 := &z.
    ipso (&n (conversion.injectivity &z)).
  }
  let proof f := congru to_integer, &e.
  leibniz (conversion.multiplication &k &x), (conversion.multiplication &k &y) in &f.
  ipso (conversion.injectivity
          (Integer.multiplication.cancellation (to_integer &k) (to_integer &x) (to_integer &y)
             &m &f)).
Qed.

(* multiplication.magnitude *)
Theorem magnitude
  : forall (x : Bin) (y : Bin) .
      abs (x * y) = (abs x * abs y)%bin_with_zero.
Proof.
  intros x y.
  match &x with | p | | p end; match &y with | q | | q end; simpl in |- *; quod idem est.
Qed.

End multiplication. (* multiplication *)

Module division. (* division *)

(* division.magnitude *)
Theorem magnitude
  : forall (x : Bin) (d : BinBase) .
      abs (x /. d) = (abs x /. d)%bin_with_zero.
Proof.
  intros x d.
  match &x with | p | | p end.
  -
    simpl divide, abs in |- *.
    match (p /. &d)%bin_with_zero with | | k end;
      simpl from_bin_with_zero, negate in |- *; quod idem est.
  -
    simpl divide, abs in |- *.
    simpl BinWithZero.divide, BinWithZero.div in |- *.
    simpl in |- *.
    quod idem est.
  -
    simpl divide, abs in |- *.
    match (p /. &d)%bin_with_zero with | | k end;
      simpl from_bin_with_zero in |- *; quod idem est.
Qed.

(* division.invariance *)
Theorem invariance
  : forall (x : Bin) (d : BinBase) (k : BinBase) .
      ((+ k) * x) /. (k * d)%bin_base = x /. d.
Proof.
  intros x d k.
  lemma positive : to_integer (+ &k) = BinBase.to_nat &k.
  {
    simpl in |- *.
    quod idem est.
  }
  lemma f : to_integer (((+ &k) * &x) /. (&k * &d)%bin_base) = to_integer (&x /. &d).
  {
    leibniz (conversion.division ((+ &k) * &x) (&k * &d)%bin_base),
      (conversion.multiplication (+ &k) &x), (BinBase.conversion.multiplication &k &d),
      (conversion.division &x &d), &positive in |- *.
    ipso (Integer.division.invariance (to_integer &x) (BinBase.to_nat &d) (BinBase.to_nat &k)).
  }
  ipso (conversion.injectivity &f).
Qed.

End division. (* division *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : Bin) (y : Bin) .
      compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  leibniz (conversion.comparison &x &y), (conversion.comparison &y &x) in |- *.
  ipso (Integer.comparison.antisymmetry (to_integer &x) (to_integer &y)).
Qed.

(* comparison.specification *)
Theorem specification
  : forall (x : Bin) (y : Bin) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  leibniz (conversion.comparison &x &y) in |- *.
  let proof s := Integer.comparison.specification (to_integer &x) (to_integer &y).
  match &s with | strict equality end.
  divide et impera.
  -
    divide et impera.
    +
      intro c.
      ipso (modus aequans (conversion.order &x &y), (modus aequans &strict, &c)).
    +
      intro h.
      ipso (modus aequans &strict, (modus aequans (conversion.order &x &y), &h)).
  -
    divide et impera.
    +
      intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    +
      intro e.
      ipso (modus aequans &equality, (congru to_integer, &e)).
Qed.

End comparison. (* comparison *)

End Bin. (* Bin *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Bin], not [Bin.T]. [Zero] and [Positive] name ctors of
 * three other number types, so all four write theirs with the prefix.
 *)
Abbreviation Bin := Bin.T.

(* Makes the notations declared in [Module Bin] usable in every file
 * that imports this one, as [(x + y)%b] or under an opened
 * [jwa_bin_scope]. Without it the notations reach no client while
 * this file still compiles, being in scope inside the module. Only the
 * notations are exported: [add] and the laws keep the [Bin.] prefix,
 * and the local aliases [0], [+ p] and [- p] stay inside.
 *)
Export (notations) Bin.

(* What makes the minus of a negative literal parse. [Numeral.Signed] lets
 * [from_numeral] *receive* a sign, but it does not put one in the grammar:
 * with the prelude off nothing makes [-1011] a term, and without this line
 * [(-1011)%b] is a syntax error at the [-]. Declared outside the module, where
 * it does not collide with the [Local] [- p] for [Negative], and scoped, so
 * [-] keeps whatever else it means elsewhere. Under [only parsing] a negative
 * value still prints as [(-1011)%b], that coming from [to_numeral] below.
 *)
Notation "- x" := (Bin.negate x)
  (at level 35, right associativity, only parsing)
  : jwa_bin_scope.

(* A number of the type is written in binary digits under its scope, [1011%b]
 * for eleven and [(-1011)%b] for minus eleven, and a closed one prints that
 * way; a literal with any other digit is refused.
 *)
Number Notation Bin.T Bin.from_numeral Bin.to_numeral
  : jwa_bin_scope.

(* A [BinBase] stands wherever a [Bin] is expected, read as its [Positive],
 * and a [BinWithZero] through [from_bin_with_zero]; both are printed where
 * they happened. The direct [BinBase >-> Bin] and the indirect one through
 * [BinWithZero] give the same term, as [Nat]'s two paths into [Integer] do.
 *)
Coercion Bin.Positive : BinBase >-> Bin.
Coercion Bin.from_bin_with_zero : BinWithZero >-> Bin.
Add Printing Coercion Bin.Positive.
Add Printing Coercion Bin.from_bin_with_zero.

(* [<] is not well founded on a signed type, there being no least value, so
 * the descent is on the magnitude: [abs] lands in [BinWithZero], where [<]
 * is well founded, and [Induced] pulls that back. [Integer] descends the same
 * way over [Nat0].
 *)
Instance Bin_magnitude_well_founded
  : WellFounded (Induced (<)%bin_with_zero Bin.abs) :=
  WellFounded.induced (<)%bin_with_zero Bin.abs
    BinWithZero_less_than_well_founded.

Instance Bin_comparable
  : Comparable Bin.compare (<)%b :=
  {| Comparable.transitivity  := @Bin.order.strict.transitivity
   ; Comparable.specification := Bin.comparison.specification
   ; Comparable.antisymmetry  := Bin.comparison.antisymmetry |}.

Instance Bin_add_monoid
  : Monoid Bin.add Bin.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bin.addition.associativity |}
   ; Monoid.identity := Bin.addition.identity |}.

Instance Bin_add_cancellative : Cancellative Bin.add :=
  {| Cancellative.cancellation := Bin.addition.cancellation |}.

Instance Bin_add_commutative : Commutative Bin.add :=
  {| Commutative.commutativity := Bin.addition.commutativity |}.

(* What the signed type buys over [BinWithZero]: every value has an inverse,
 * so the additive monoid becomes a group.
 *)
Instance Bin_add_group
  : Group Bin.add Bin.Zero Bin.negate :=
  {| Group.monoid  := Bin_add_monoid
   ; Group.inverse := Bin.addition.inverse |}.

Instance Bin_add_abelian_group
  : AbelianGroup Bin.add Bin.Zero Bin.negate :=
  {| AbelianGroup.group       := Bin_add_group
   ; AbelianGroup.commutative := Bin_add_commutative |}.

Instance Bin_mul_monoid
  : Monoid Bin.mul BinBase.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bin.multiplication.associativity |}
   ; Monoid.identity := Bin.multiplication.identity |}.

Instance Bin_mul_commutative : Commutative Bin.mul :=
  {| Commutative.commutativity := Bin.multiplication.commutativity |}.

Instance Bin_ring
  : Ring Bin.add Bin.Zero Bin.negate Bin.mul
      BinBase.One :=
  {| Ring.abelian_group  := Bin_add_abelian_group
   ; Ring.monoid         := Bin_mul_monoid
   ; Ring.distributivity := Bin.multiplication.distributivity.over.addition |}.
