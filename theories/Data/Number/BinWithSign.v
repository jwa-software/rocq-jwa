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
From jwa Require Import Tactics.Witness.

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
 * that imports this one. [+ p] and [- p] are prefixes, distinct from the
 * infix [+] declared below.
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

(* The positive part, zero below it; [add] is written from it. *)
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

(* Every value is [ramp x] less [ramp (negate x)], one of which is always
 * zero, so a sum is a single difference of two nonnegative numbers instead of
 * nine sign cases. [Integer.add] is written the same way over [NatWithZero].
 *)
(* [BinWithSign -> BinWithSign -> BinWithSign] *)
Definition add := fun (x : BinWithSign) (y : BinWithSign) .
  bin_with_zero_difference (ramp x + ramp y)%bin_with_zero
                           (ramp (negate x) + ramp (negate y))%bin_with_zero.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End BinWithSign] a client writes [(x + y)%b]. [only parsing]
 * keeps goals printing the operations by name. The prefix [+ p] above is a
 * separate notation and coexists with this infix one, as in [Integer].
 *)
Notation "x + y" := (add x y) (only parsing)
  : jwa_bin_with_sign_scope.

Local Open Scope jwa_bin_with_sign_scope.

(* No infix [-]: the scope's [-] is the prefix negation that makes [(-1011)%b]
 * parse, and [Integer] declares none either.
 *)
(* [BinWithSign -> BinWithSign -> BinWithSign] *)
Definition sub := fun (x : BinWithSign) (y : BinWithSign) . x + negate y.

(* The witness is a [Bin], so it is never zero and [<] is strict.
 *)
(* [BinWithSign -> BinWithSign -> Prop] *)
Definition LessThan := fun (x : BinWithSign) (y : BinWithSign) .
  forsome (k : Bin) . x + (+ k) = y.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_bin_with_sign_scope.

(* [BinWithSign -> BinWithSign -> Prop] *)
Definition LessOrEqual := fun (x : BinWithSign) (y : BinWithSign) . x = y \/ x < y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_bin_with_sign_scope.

(* The reversed spellings name no new relation: [x > y] is [y < x] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_bin_with_sign_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_bin_with_sign_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_bin_with_sign_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_bin_with_sign_scope.

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

(* [BinWithZero] reads the magnitude, the sign is applied after. [- 0] reads as
 * zero, this type having one zero and [negate] sending it to itself.
 * Hexadecimal is refused there too, so a literal carries only [0] and [1].
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

(* Zero prints as [0], not [-0]: [Numeral.Decimal.Signed] has only the two
 * signs, so one of them carries zero.
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

(* The laws state this type against [Integer] through [to_integer]. The signed
 * laws are proved there, so agreement carries them.
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

(* Of the nine pairs of [Bin.diff] outcomes, a [Gt] in the first answers alone.
 * Four of the remaining six cannot arise: [Lt] facing [Lt] or [Eq] either way
 * contradicts the order on [Nat], and [Eq] facing [Gt] would need
 * [to_nat p + to_nat d] to equal [to_nat p], which no [Bin] permits.
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

(* conversion.negation *)
Theorem negation
  : forall (x : BinWithSign) .
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

(* [difference] with the zero cases added. *)
(* conversion.zero_difference *)
Theorem zero_difference
  : forall (a : BinWithZero) (b : BinWithZero) .
      to_integer (bin_with_zero_difference a b)
    = Integer.nat_with_zero_difference
        (BinWithZero.to_nat_with_zero a) (BinWithZero.to_nat_with_zero b).
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

(* conversion.addition *)
Theorem addition
  : forall (x : BinWithSign) (y : BinWithSign) .
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
      leibniz (Bin.conversion.addition &p &q) in |- *.
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
      leibniz (Bin.conversion.addition &p &q) in |- *.
      quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (x : BinWithSign) (y : BinWithSign) .
      x < y <-> (to_integer x < to_integer y)%integer.
Proof.
  intros x y.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Integer.LessThan in |- *.
    exists (Bin.to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &x (Positive &k)) in |- *.
    simpl to_integer in |- *.
    quod idem est.
  -
    intro h.
    simpl Integer.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (Bin.from_nat &j).
    lemma f : to_integer (&x + (+ Bin.from_nat &j)) = to_integer &y.
    {
      leibniz (conversion.addition &x (Positive (Bin.from_nat &j))) in |- *.
      simpl to_integer in |- *.
      leibniz (Bin.conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

End conversion. (* conversion *)

End BinWithSign. (* BinWithSign *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinWithSign], not [BinWithSign.T]. [Zero] and [Positive] name ctors of
 * three other number types, so all four write theirs with the prefix.
 *)
Abbreviation BinWithSign := BinWithSign.T.

(* Makes the notations declared in [Module BinWithSign] usable in every file
 * that imports this one, as [(x + y)%b] or under an opened
 * [jwa_bin_with_sign_scope]. Without it the notations reach no client while
 * this file still compiles, being in scope inside the module. Only the
 * notations are exported: [add] and the laws keep the [BinWithSign.] prefix,
 * and the local aliases [0], [+ p] and [- p] stay inside.
 *)
Export (notations) BinWithSign.

(* What makes the minus of a negative literal parse. [Numeral.Signed] lets
 * [from_numeral] *receive* a sign, but it does not put one in the grammar:
 * with the prelude off nothing makes [-1011] a term, and without this line
 * [(-1011)%b] is a syntax error at the [-]. Declared outside the module, where
 * it does not collide with the [Local] [- p] for [Negative], and scoped, so
 * [-] keeps whatever else it means elsewhere. Under [only parsing] a negative
 * value still prints as [(-1011)%b], that coming from [to_numeral] below.
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
