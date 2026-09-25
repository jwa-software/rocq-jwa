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
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [Integer.add]. The
 * type and its ctors are declared inside it: [NatWithZero] declares [Zero]
 * and [Positive] too, and across files a duplicate ctor name rebinds the
 * bare one silently and with no warning.
 *)
Module Integer. (* Integer *)

Inductive T : Type :=
  | Negative : Nat -> T
  | Zero     : T
  | Positive : Nat -> T.

(* The carrier is named [T] so that the type itself reads [Integer] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Integer].
 *)
Abbreviation Integer := T.

(* The eliminator behind the [destruct] tactic, written out: no recursion, since no
 * ctor carries an [Integer].
 *)
Definition induction
  : forall (P : Integer -> Prop) .
      (forall (p : Nat) . P (Negative p)) ->
      P Zero ->
      (forall (p : Nat) . P (Positive p)) ->
      (forall (x : Integer) . P x)
  := fun (P : Integer -> Prop)
       (negative : forall (p : Nat) . P (Negative p))
       (zero : P Zero)
       (positive : forall (p : Nat) . P (Positive p))
       (x : Integer) .
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] and [- p] are prefixes, apart from the
 * infix [+]; the ctors of [NatWithZero] keep their qualified names.
 *)
Local Notation "0"   := Zero (only parsing).
Local Notation "+ p" := (Positive p) (at level 35, right associativity, only parsing).
Local Notation "- p" := (Negative p) (at level 35, right associativity, only parsing).

(* [Integer -> Integer] *)
Definition negate := fun (x : Integer) .
  match x with
  | - p => + p
  | 0   => 0
  | + p => - p
  end.

(* [Integer -> NatWithZero] *)
Definition abs := fun (x : Integer) .
  match x with
  | - p => NatWithZero.Positive p
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive p
  end.

(* The bars of the magnitude, in parentheses: a bare [| x |] would be read
 * as the opening of a [match] arm, and [|| x ||] would take the [||] of
 * [Bool.or] away, both of them everywhere and not only where this scope is
 * open.
 *)
Notation "(| x |)" := (abs x) (only parsing)
  : jwa_integer_scope.

(* [Nat -> Integer] *)
Definition from_nat := fun (n : Nat) . (+ n).

(* [NatWithZero -> Integer] *)
Definition from_nat_with_zero := fun (n : NatWithZero) .
  match n return Integer with
  | NatWithZero.Zero       => 0
  | NatWithZero.Positive p => + p
  end.

(* [Integer -> NatWithZero] *)
Definition ramp := fun (x : Integer) .
  match x with
  | - _ => NatWithZero.Zero
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive p
  end.

(* The conversions down: [None] below [0] for [NatWithZero], and at or below
 * it for [Nat], where [ramp] answers [NatWithZero.Zero] instead.
 *)
(* [Integer -> Option NatWithZero] *)
Definition to_nat_with_zero := fun (x : Integer) .
  match x with
  | - _ => None
  | 0   => Some NatWithZero.Zero
  | + p => Some (NatWithZero.Positive p)
  end.

(* [Integer -> Option Nat] *)
Definition to_nat := fun (x : Integer) .
  match x with
  | - _ => None
  | 0   => None
  | + p => Some p
  end.

(* [Nat -> Nat -> Integer] *)
Fixpoint nat_difference (p : Nat) (q : Nat) : Integer :=
  match p, q with
  | Nat.One, Nat.One                   => 0
  | Nat.One, Nat.Successor q'          => - q'
  | Nat.Successor p', Nat.One          => + p'
  | Nat.Successor p', Nat.Successor q' => nat_difference p' q'
  end.

(* [NatWithZero -> NatWithZero -> Integer] *)
Definition nat_with_zero_difference := fun (a : NatWithZero) (b : NatWithZero) .
  match a, b with
  | NatWithZero.Zero, NatWithZero.Zero             => 0
  | NatWithZero.Zero, NatWithZero.Positive q       => - q
  | NatWithZero.Positive p, NatWithZero.Zero       => + p
  | NatWithZero.Positive p, NatWithZero.Positive q => nat_difference p q
  end.

(* [Integer -> Integer -> Integer] *)
Definition add := fun (m : Integer) (n : Integer) .
  nat_with_zero_difference (ramp m + ramp n)%nat_with_zero
                           (ramp (negate m) + ramp (negate n))%nat_with_zero.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Integer] a client writes [(m + n)%integer]. [only
 * parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_integer_scope.

Local Open Scope jwa_integer_scope.

(* [Integer -> Integer -> Integer] *)
Definition sub := fun (m : Integer) (n : Integer) . m + negate n.

(* [Integer -> Integer -> Integer] *)
Definition mul := fun (m : Integer) (n : Integer) .
  match m with
  | - p =>
      match n with
      | - q => + (p * q)%nat
      | 0   => 0
      | + q => - (p * q)%nat
      end
  | 0 => 0
  | + p =>
      match n with
      | - q => - (p * q)%nat
      | 0   => 0
      | + q => + (p * q)%nat
      end
  end.

Notation "m * n" := (mul m n) (only parsing)
  : jwa_integer_scope.

(* The divisor is a [Nat], so it is never zero and no case is missing: the
 * magnitude is divided and the sign carried over.
 *)
(* [Integer -> Nat -> Integer] *)
Definition divide := fun (x : Integer) (d : Nat) .
  match x with
  | - p => negate (from_nat_with_zero (p /. d)%nat_with_zero)
  | 0   => 0
  | + p => from_nat_with_zero (p /. d)%nat_with_zero
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here,
 * and it is written in parentheses as [NatWithZero]'s is, so the dot that
 * ends the token never sits beside the one that ends a command. There is no
 * [%.] to go with it: a remainder on this type needs a sign convention, and
 * none is chosen, so [Integer] carries no [modulo].
 *)
Notation "m /. n" := (divide m n) (only parsing)
  : jwa_integer_scope.

(* [Integer -> Integer -> Prop] *)
Definition LessThan := fun (m : Integer) (n : Integer) .
  forsome (k : Nat) . m + (+ k) = n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_integer_scope.

(* [Integer -> Integer -> Prop] *)
Definition LessOrEqual := fun (m : Integer) (n : Integer) . m = n \/ m < n.

Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_integer_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_integer_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_integer_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_integer_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_integer_scope.

(* [Integer -> Integer -> Comparison] *)
Definition compare := fun (m : Integer) (n : Integer) .
  match m with
  | - p =>
      match n with
      | - q => Nat.compare q p
      | 0   => Comparison.Lt
      | + _ => Comparison.Lt
      end
  | 0 =>
      match n with
      | - _ => Comparison.Gt
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match n with
      | - _ => Comparison.Gt
      | 0   => Comparison.Gt
      | + q => Nat.compare p q
      end
  end.

(* [Integer -> Integer -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Integer -> Integer -> Prop] *)
Definition Divides := fun (d : Integer) (n : Integer) . forsome (k : Integer) . d * k = n.

(* [Integer -> Prop] *)
Definition Even := fun (n : Integer) . Divides (+ (Nat.Successor Nat.One)) n.

(* [Integer -> Prop] *)
Definition Odd := fun (n : Integer) .
  forsome (k : Integer) . ((+ (Nat.Successor Nat.One)) * k) + (+ Nat.One) = n.

Module magnitude. (* magnitude *)

Module negative. (* magnitude.negative *)

(* magnitude.negative.injectivity *)
Lemma injectivity
  : forall {p : Nat} {q : Nat} . (- p) = - q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : Integer) . match x with | - r => r | 0 => p | + _ => p end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End negative. (* magnitude.negative *)

Module positive. (* magnitude.positive *)

(* magnitude.positive.injectivity *)
Lemma injectivity
  : forall {p : Nat} {q : Nat} . (+ p) = + q -> p = q.
Proof.
  intros p q e.
  congru (fun (x : Integer) . match x with | - _ => p | 0 => p | + r => r end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

End positive. (* magnitude.positive *)

(* magnitude.injectivity *)
Theorem injectivity
  : forall (p : Nat) (q : Nat) .
      (- p = - q -> p = q) /\ (+ p = + q -> p = q).
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
  : forall {m : NatWithZero} {n : NatWithZero} .
      from_nat_with_zero m = from_nat_with_zero n -> m = n.
Proof.
  intros m n e.
  match m with | | p end; match n with | | q end.
  - quod idem est.
  - simpl in e.
    ex e quodlibet.
  - simpl in e.
    ex e quodlibet.
  - simpl in e.
    let proof e' := magnitude.positive.injectivity e.
    leibniz e' in |- *.
    quod idem est.
Qed.

End embedding. (* embedding *)

Module difference. (* difference *)

Module nat. (* difference.nat *)

(* difference.nat.reflexivity *)
Lemma reflexivity : forall (n : Nat) . nat_difference n n = 0.
Proof.
  intros n.
  match n with | | n' by IH end per Nat.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso IH.
Qed.

Module left. (* difference.nat.left *)

Module inversion. (* difference.nat.left.inversion *)

Module of. (* difference.nat.left.inversion.of *)

(* difference.nat.left.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (p : Nat) . nat_difference (k + p)%nat p = + k.
Proof.
  intros k p.
  match p with | | p' by IH end per Nat.induction.
  - leibniz (Nat.addition.commutativity k Nat.One) in |- *.
    simpl in |- *.
    quod idem est.
  - leibniz (Nat.addition.commutativity k (Nat.Successor p')) in |- *.
    simpl in |- *.
    leibniz (Nat.addition.commutativity p' k) in |- *.
    ipso IH.
Qed.

End of. (* difference.nat.left.inversion.of *)

End inversion. (* difference.nat.left.inversion *)

End left. (* difference.nat.left *)

Module right. (* difference.nat.right *)

Module inversion. (* difference.nat.right.inversion *)

Module of. (* difference.nat.right.inversion.of *)

(* difference.nat.right.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (p : Nat) . nat_difference p (k + p)%nat = - k.
Proof.
  intros k p.
  match p with | | p' by IH end per Nat.induction.
  - leibniz (Nat.addition.commutativity k Nat.One) in |- *.
    simpl in |- *.
    quod idem est.
  - leibniz (Nat.addition.commutativity k (Nat.Successor p')) in |- *.
    simpl in |- *.
    leibniz (Nat.addition.commutativity p' k) in |- *.
    ipso IH.
Qed.

End of. (* difference.nat.right.inversion.of *)

End inversion. (* difference.nat.right.inversion *)

End right. (* difference.nat.right *)

(* "Well-definedness" keeps its underscore: it is one fixed technical term,
 * not a modifier in front of a noun.
 *)
(* difference.nat.well_definedness *)
Lemma well_definedness
  : forall {p : Nat} {q : Nat} {r : Nat} {s : Nat} .
      (p + s)%nat = (r + q)%nat -> nat_difference p q = nat_difference r s.
Proof.
  intros p q r s h.
  let proof t := Nat.order.strict.trichotomy p q.
  match t with | lt | rest end.
  - simpl ( _ < _ )%nat in lt.
    match lt with | k e end.
    symm in e.
    leibniz e in h |- *.
    leibniz (Nat.addition.commutativity p k) in |- *.
    leibniz (difference.nat.right.inversion.of.addition k p) in |- *.
    leibniz (Nat.addition.left.commutativity r p k) in h.
    let proof e'' := Nat.addition.left.cancellation h.
    leibniz e'' in |- *.
    leibniz (Nat.addition.commutativity r k) in |- *.
    leibniz (difference.nat.right.inversion.of.addition k r) in |- *.
    quod idem est.
  - match rest with | eq | gt end.
    + leibniz &eq in h |- *.
      leibniz (difference.nat.reflexivity q) in |- *.
      leibniz (Nat.addition.commutativity r q) in h.
      let proof e := Nat.addition.left.cancellation h.
      leibniz e in |- *.
      leibniz (difference.nat.reflexivity r) in |- *.
      quod idem est.
    + simpl ( _ < _ )%nat in gt.
      match gt with | k e end.
      symm in e.
      leibniz e in h |- *.
      leibniz (Nat.addition.commutativity q k) in |- *.
      leibniz (difference.nat.left.inversion.of.addition k q) in |- *.
      leibniz (Nat.addition.associativity q k s) in h.
      leibniz (Nat.addition.commutativity r q) in h.
      let proof e'' := Nat.addition.left.cancellation h.
      symm in e''.
      leibniz e'' in |- *.
      leibniz (difference.nat.left.inversion.of.addition k s) in |- *.
      quod idem est.
Qed.

(* difference.nat.negation *)
Lemma negation
  : forall (p : Nat) (q : Nat) . negate (nat_difference p q) = nat_difference q p.
Proof.
  intros p q.
  let proof t := Nat.order.strict.trichotomy p q.
  match t with | lt | rest end.
  - simpl ( _ < _ )%nat in lt.
    match lt with | k e end.
    symm in e.
    leibniz e in |- *.
    leibniz (Nat.addition.commutativity p k) in |- *.
    leibniz (difference.nat.right.inversion.of.addition k p) in |- *.
    leibniz (difference.nat.left.inversion.of.addition  k p) in |- *.
    simpl in |- *.
    quod idem est.
  - match rest with | eq | gt end.
    + leibniz &eq in |- *.
      leibniz (difference.nat.reflexivity q) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl ( _ < _ )%nat in gt.
      match gt with | k e end.
      symm in e.
      leibniz e in |- *.
      leibniz (Nat.addition.commutativity q k) in |- *.
      leibniz (difference.nat.left.inversion.of.addition  k q) in |- *.
      leibniz (difference.nat.right.inversion.of.addition k q) in |- *.
      simpl in |- *.
      quod idem est.
Qed.

(* difference.nat.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) .
      (ramp (nat_difference p q) + q)%nat_with_zero
    = (ramp (negate (nat_difference p q)) + p)%nat_with_zero.
Proof.
  intros p q.
  let proof t := Nat.order.strict.trichotomy p q.
  match t with | lt | rest end.
  - simpl ( _ < _ )%nat in lt.
    match lt with | k e end.
    symm in e.
    leibniz e in |- *.
    leibniz (Nat.addition.commutativity p k) in |- *.
    leibniz (difference.nat.right.inversion.of.addition k p) in |- *.
    simpl in |- *.
    quod idem est.
  - match rest with | eq | gt end.
    + leibniz &eq in |- *.
      leibniz (difference.nat.reflexivity q) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl ( _ < _ )%nat in gt.
      match gt with | k e end.
      symm in e.
      leibniz e in |- *.
      leibniz (Nat.addition.commutativity q k) in |- *.
      leibniz (difference.nat.left.inversion.of.addition k q) in |- *.
      simpl in |- *.
      quod idem est.
Qed.

Module negative. (* difference.nat.negative *)

(* difference.nat.negative.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = - k <-> (p + k)%nat = q.
Proof.
  intros p q k.
  divide et impera.
  - intro e.
    let proof s := difference.nat.specification p q.
    leibniz e in s.
    simpl in s.
    let proof e' := NatWithZero.positive.injectivity s.
    leibniz (Nat.addition.commutativity p k) in |- *.
    ipso (Identity.symmetry e').
  - intro e.
    symm in e.
    leibniz e in |- *.
    leibniz (Nat.addition.commutativity p k) in |- *.
    ipso (difference.nat.right.inversion.of.addition k p).
Qed.

End negative. (* difference.nat.negative *)

Module zero. (* difference.nat.zero *)

(* difference.nat.zero.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) . nat_difference p q = 0 <-> p = q.
Proof.
  intros p q.
  divide et impera.
  - intro e.
    let proof s := difference.nat.specification p q.
    leibniz e in s.
    simpl in s.
    let proof e' := NatWithZero.positive.injectivity s.
    ipso (Identity.symmetry e').
  - intro e.
    leibniz e in |- *.
    ipso (difference.nat.reflexivity q).
Qed.

End zero. (* difference.nat.zero *)

Module positive. (* difference.nat.positive *)

(* difference.nat.positive.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = + k <-> (q + k)%nat = p.
Proof.
  intros p q k.
  divide et impera.
  - intro e.
    let proof s := difference.nat.specification p q.
    leibniz e in s.
    simpl in s.
    let proof e' := NatWithZero.positive.injectivity s.
    leibniz (Nat.addition.commutativity q k) in |- *.
    ipso e'.
  - intro e.
    symm in e.
    leibniz e in |- *.
    leibniz (Nat.addition.commutativity q k) in |- *.
    ipso (difference.nat.left.inversion.of.addition k q).
Qed.

End positive. (* difference.nat.positive *)

(* difference.nat.scaling *)
Lemma scaling
  : forall (k : Nat) (p : Nat) (q : Nat) .
      (+ k) * nat_difference p q = nat_difference (k * p)%nat (k * q)%nat.
Proof.
  intros k p q.
  let proof t := Nat.order.strict.trichotomy p q.
  match t with | lt | rest end.
  - simpl ( _ < _ )%nat in lt.
    match lt with | j e end.
    symm in e.
    leibniz e in |- *.
    leibniz (Nat.addition.commutativity p j) in |- *.
    leibniz (difference.nat.right.inversion.of.addition j p) in |- *.
    simpl in |- *.
    leibniz (Nat.multiplication.left.distributivity.over.addition k j p) in |- *.
    leibniz (difference.nat.right.inversion.of.addition
              (k * j)%nat (k * p)%nat) in |- *.
    quod idem est.
  - match rest with | eq | gt end.
    + leibniz &eq in |- *.
      leibniz (difference.nat.reflexivity q) in |- *.
      leibniz (difference.nat.reflexivity (k * q)%nat) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl ( _ < _ )%nat in gt.
      match gt with | j e end.
      symm in e.
      leibniz e in |- *.
      leibniz (Nat.addition.commutativity q j) in |- *.
      leibniz (difference.nat.left.inversion.of.addition j q) in |- *.
      simpl in |- *.
      leibniz (Nat.multiplication.left.distributivity.over.addition k j q) in |- *.
      leibniz (difference.nat.left.inversion.of.addition
                (k * j)%nat (k * q)%nat) in |- *.
      quod idem est.
Qed.

End nat. (* difference.nat *)

Module nat_with_zero. (* difference.nat_with_zero *)

(* difference.nat_with_zero.canonicity *)
Lemma canonicity
  : forall (x : Integer) . nat_with_zero_difference (ramp x) (ramp (negate x)) = x.
Proof.
  intros x.
  match x with | p | | p end; simpl in |- *; quod idem est.
Qed.

(* difference.nat_with_zero.reflexivity *)
Lemma reflexivity
  : forall (n : NatWithZero) . nat_with_zero_difference n n = 0.
Proof.
  intros n.
  match n with | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (difference.nat.reflexivity p).
Qed.

Module left. (* difference.nat_with_zero.left *)

Module inversion. (* difference.nat_with_zero.left.inversion *)

Module of. (* difference.nat_with_zero.left.inversion.of *)

(* difference.nat_with_zero.left.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (a : NatWithZero) .
      nat_with_zero_difference (k + a)%nat_with_zero a = + k.
Proof.
  intros k a.
  match a with | | q end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (difference.nat.left.inversion.of.addition k q).
Qed.

End of. (* difference.nat_with_zero.left.inversion.of *)

End inversion. (* difference.nat_with_zero.left.inversion *)

End left. (* difference.nat_with_zero.left *)

Module right. (* difference.nat_with_zero.right *)

Module inversion. (* difference.nat_with_zero.right.inversion *)

Module of. (* difference.nat_with_zero.right.inversion.of *)

(* difference.nat_with_zero.right.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (a : NatWithZero) .
      nat_with_zero_difference a (k + a)%nat_with_zero = - k.
Proof.
  intros k a.
  match a with | | q end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (difference.nat.right.inversion.of.addition k q).
Qed.

End of. (* difference.nat_with_zero.right.inversion.of *)

End inversion. (* difference.nat_with_zero.right.inversion *)

End right. (* difference.nat_with_zero.right *)

(* difference.nat_with_zero.specification *)
Lemma specification
  : forall (a : NatWithZero) (b : NatWithZero) .
      (ramp (nat_with_zero_difference a b) + b)%nat_with_zero
      = (ramp (negate (nat_with_zero_difference a b)) + a)%nat_with_zero.
Proof.
  intros a b.
  match a with | | p end; match b with | | q end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (difference.nat.specification p q).
Qed.

(* difference.nat_with_zero.well_definedness *)
Lemma well_definedness
  : forall {a : NatWithZero} {b : NatWithZero} {c : NatWithZero} {d : NatWithZero} .
      (a + d)%nat_with_zero = (c + b)%nat_with_zero ->
      nat_with_zero_difference a b = nat_with_zero_difference c d.
Proof.
  intros a b c d h.
  match a with | | p end; match b with | | q end.
  - simpl in h.
    leibniz (NatWithZero.addition.commutativity c NatWithZero.Zero) in h.
    simpl in h.
    leibniz h in |- *.
    leibniz (difference.nat_with_zero.reflexivity c) in |- *.
    simpl in |- *.
    quod idem est.
  - simpl in h.
    leibniz h in |- *.
    leibniz (NatWithZero.addition.commutativity c q) in |- *.
    leibniz (difference.nat_with_zero.right.inversion.of.addition q c) in |- *.
    simpl in |- *.
    quod idem est.
  - leibniz (NatWithZero.addition.commutativity c NatWithZero.Zero) in h.
    let proof h : (p + d)%nat_with_zero = c := &h.
    symm in h.
    leibniz h in |- *.
    leibniz (difference.nat_with_zero.left.inversion.of.addition p d) in |- *.
    simpl in |- *.
    quod idem est.
  - match c with | | r end; match d with | | s end.
    + simpl in h.
      let proof e := NatWithZero.positive.injectivity h.
      leibniz e in |- *.
      simpl in |- *.
      leibniz (difference.nat.reflexivity q) in |- *.
      quod idem est.
    + simpl in h.
      let proof e := NatWithZero.positive.injectivity h.
      symm in e.
      leibniz e in |- *.
      simpl in |- *.
      leibniz (Nat.addition.commutativity p s) in |- *.
      leibniz (difference.nat.right.inversion.of.addition s p) in |- *.
      quod idem est.
    + simpl in h.
      let proof e := NatWithZero.positive.injectivity h.
      leibniz e in |- *.
      simpl in |- *.
      leibniz (difference.nat.left.inversion.of.addition r q) in |- *.
      quod idem est.
    + simpl in h.
      let proof e := NatWithZero.positive.injectivity h.
      simpl in |- *.
      ipso (difference.nat.well_definedness e).
Qed.

(* difference.nat_with_zero.negation *)
Lemma negation
  : forall (a : NatWithZero) (b : NatWithZero) .
      negate (nat_with_zero_difference a b) = nat_with_zero_difference b a.
Proof.
  intros a b.
  match a with | | p end; match b with | | q end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (difference.nat.negation p q).
Qed.

(* difference.nat_with_zero.additivity *)
Theorem additivity
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero) .
      (nat_with_zero_difference a b) + (nat_with_zero_difference c d)
    = nat_with_zero_difference (a + c)%nat_with_zero (b + d)%nat_with_zero.
Proof.
  intros a b c d.
  simpl add in |- *.
  lemma facto
    : (ramp (nat_with_zero_difference &a &b) + ramp (nat_with_zero_difference &c &d)
       + (&b + &d))%nat_with_zero
      = (&a + &c
         + (ramp (negate (nat_with_zero_difference &a &b))
            + ramp (negate (nat_with_zero_difference &c &d))))%nat_with_zero.
  {
    leibniz (NatWithZero.addition.interchange
              (ramp (nat_with_zero_difference a b))
              (ramp (nat_with_zero_difference c d))
              b d) in |- *.
    leibniz (difference.nat_with_zero.specification a b) in |- *.
    leibniz (difference.nat_with_zero.specification c d) in |- *.
    leibniz (NatWithZero.addition.interchange
               (ramp (negate (nat_with_zero_difference a b))) a
               (ramp (negate (nat_with_zero_difference c d))) c) in |- *.
    leibniz (NatWithZero.addition.commutativity
              (ramp (negate (nat_with_zero_difference a b))
               + ramp (negate (nat_with_zero_difference c d)))%nat_with_zero
              (a + c)%nat_with_zero) in |- *.
    quod idem est.
  }
  ipso (@difference.nat_with_zero.well_definedness
          (ramp (nat_with_zero_difference a b) + ramp (nat_with_zero_difference c d))%nat_with_zero
          (ramp (negate (nat_with_zero_difference a b))
           + ramp (negate (nat_with_zero_difference c d)))%nat_with_zero
          (a + c)%nat_with_zero
          (b + d)%nat_with_zero
          facto).
Qed.

(* difference.nat_with_zero.scaling *)
Lemma scaling
  : forall (k : Nat) (a : NatWithZero) (b : NatWithZero) .
      (+ k) * nat_with_zero_difference a b
      = nat_with_zero_difference
          (k * a)%nat_with_zero
          (k * b)%nat_with_zero.
Proof.
  intros k a b.
  match a with | | p end; match b with | | q end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - lemma facto
      : (+ &k) * nat_difference &p &q = nat_difference (&k * &p)%nat (&k * &q)%nat.
    {
      ipso (difference.nat.scaling k p q).
    }
    let proof facto
      : (+ &k) * nat_with_zero_difference p q
        = nat_difference (&k * &p)%nat (&k * &q)%nat
      := facto.
    ipso facto.
Qed.

End nat_with_zero. (* difference.nat_with_zero *)

End difference. (* difference *)

Module ramp. (* ramp *)

(* ramp.scaling *)
Lemma scaling
  : forall (k : Nat) (x : Integer) .
      ramp ((+ k) * x) = (k * ramp x)%nat_with_zero.
Proof.
  intros k x.
  match x with | x' | | x' end; simpl in |- *; quod idem est.
Qed.

End ramp. (* ramp *)

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (x : Integer) . negate (negate x) = x.
Proof.
  intros x.
  match x with | p | | n end; simpl in |- *; quod idem est.
Qed.

(* negation.additivity *)
Theorem additivity
  : forall (m : Integer) (n : Integer) . negate (m + n) = negate m + negate n.
Proof.
  intros m n.
  simpl add in |- *.
  leibniz (difference.nat_with_zero.negation
            (ramp m + ramp n)%nat_with_zero
            (ramp (negate m) + ramp (negate n))%nat_with_zero) in |- *.
  leibniz (negation.involution m) in |- *.
  leibniz (negation.involution n) in |- *.
  quod idem est.
Qed.

End negation. (* negation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  let proof el := Identity.symmetry (difference.nat_with_zero.canonicity l).
  let proof em := Identity.symmetry (difference.nat_with_zero.canonicity m).
  let proof en := Identity.symmetry (difference.nat_with_zero.canonicity n).
  leibniz el in |- *.
  leibniz em in |- *.
  leibniz en in |- *.
  leibniz (difference.nat_with_zero.additivity
            (ramp l)
            (ramp (negate l))
            (ramp m)
            (ramp (negate m))) in |- *.
  leibniz (difference.nat_with_zero.additivity
            (ramp l + ramp m)%nat_with_zero
            (ramp (negate l) + ramp (negate m))%nat_with_zero
            (ramp n)
            (ramp (negate n))) in |- *.
  leibniz (difference.nat_with_zero.additivity
            (ramp m)
            (ramp (negate m))
            (ramp n)
            (ramp (negate n))) in |- *.
  leibniz (difference.nat_with_zero.additivity
            (ramp l)
            (ramp (negate l))
            (ramp m + ramp n)%nat_with_zero
            (ramp (negate m) + ramp (negate n))%nat_with_zero) in |- *.
  leibniz (NatWithZero.addition.associativity
            (ramp l)
            (ramp m)
            (ramp n)) in |- *.
  leibniz (NatWithZero.addition.associativity
            (ramp (negate l))
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  quod idem est.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : Integer) (n : Integer) . m + n = n + m.
Proof.
  intros m n.
  simpl add in |- *.
  leibniz (NatWithZero.addition.commutativity
            (ramp m)
            (ramp n)) in |- *.
  leibniz (NatWithZero.addition.commutativity
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  quod idem est.
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
Theorem identity : forall (n : Integer) . 0 + n = n.
Proof.
  intros n.
  match n with | n' | | n' end; simpl add in |- *; simpl in |- *; quod idem est.
Qed.

(* addition.left.commutativity *)
Lemma commutativity
  : forall (l : Integer) (m : Integer) (n : Integer) . l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  leibniz (addition.commutativity l (m + n)) in |- *.
  leibniz (addition.associativity m n l)     in |- *.
  leibniz (addition.commutativity n l)       in |- *.
  quod idem est.
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (n : Integer) . negate n + n = 0.
Proof.
  intros n.
  match n with | p | | p end.
  - simpl add in |- *.
    simpl in |- *.
    ipso (difference.nat.reflexivity p).
  - simpl add in |- *.
    simpl in |- *.
    quod idem est.
  - simpl add in |- *.
    simpl in |- *.
    ipso (difference.nat.reflexivity p).
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall {k : Integer} {m : Integer} {n : Integer} . k + m = k + n -> m = n.
Proof.
  intros k m n h.
  congru (add (negate k)), h |- h'.
  leibniz <- (addition.associativity (negate k) k m)
          in h'.
  leibniz <- (addition.associativity (negate k) k n)
          in h'.
  leibniz (addition.left.inverse k)  in h'.
  leibniz (addition.left.identity m) in h'.
  leibniz (addition.left.identity n) in h'.
  ipso h'.
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
Theorem identity : forall (n : Integer) . n + 0 = n.
Proof.
  intros n.
  leibniz (addition.commutativity n 0) in |- *.
  ipso (addition.left.identity n).
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (n : Integer) . n + negate n = 0.
Proof.
  intros n.
  leibniz (addition.commutativity n (negate n)) in |- *.
  ipso (addition.left.inverse n).
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall {m : Integer} {n : Integer} {k : Integer} . m + k = n + k -> m = n.
Proof.
  intros m n k h.
  leibniz (addition.commutativity m k) in h.
  leibniz (addition.commutativity n k) in h.
  ipso (addition.left.cancellation h).
Qed.

End right. (* addition.right *)

(* addition.interchange *)
Theorem interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  leibniz (addition.associativity a b (c + d)) in |- *.
  leibniz (addition.left.commutativity b c d)  in |- *.
  leibniz (addition.associativity a c (b + d)) in |- *.
  quod idem est.
Qed.

(* addition.identity *)
Theorem identity
  : forall (n : Integer) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intros n.
  divide et impera.
  - ipso (addition.left.identity  n).
  - ipso (addition.right.identity n).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (n : Integer) . (negate n + n = 0) /\ (n + negate n = 0).
Proof.
  intros n.
  divide et impera.
  - ipso (addition.left.inverse  n).
  - ipso (addition.right.inverse n).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Integer) (n : Integer) (k : Integer) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  divide et impera.
  - ipso (@addition.left.cancellation  m n k).
  - ipso (@addition.right.cancellation m k n).
Qed.

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* addition.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : Integer) (m : Integer) (n : Integer) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  simpl ( _ < _ ) in h.
  match h with | d e end.
  simpl ( _ < _ ) in |- *.
  exists d.
  leibniz (addition.associativity k m (+ d)) in |- *.
  leibniz e in |- *.
  quod idem est.
Qed.

End strict. (* addition.order.strict *)

End order. (* addition.order *)

End addition. (* addition *)

Module subtraction. (* subtraction *)

Module inversion. (* subtraction.inversion *)

Module of. (* subtraction.inversion.of *)

(* subtraction.inversion.of.addition *)
Theorem addition
  : forall (m : Integer) (n : Integer) . sub (m + n) n = m.
Proof.
  intros m n.
  simpl sub in |- *.
  leibniz (addition.associativity m n (negate n)) in |- *.
  leibniz (addition.right.inverse n) in |- *.
  ipso (addition.right.identity m).
Qed.

End of. (* subtraction.inversion.of *)

End inversion. (* subtraction.inversion *)

End subtraction. (* subtraction *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (m : Integer) (n : Integer) . m * n = n * m.
Proof.
  intros m n.
  match m with | m' | | m' end; match n with | n' | | n' end.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' n') in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' n') in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' n') in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' n') in |- *.
    quod idem est.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (l : Integer) (m : Integer) (n : Integer) . (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  match l with | l' | | l' end.
  - match m with | m' | | m' end.
    + match n with | n' | | n' end.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
      *
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
    + simpl in |- *. quod idem est.
    + match n with | n' | | n' end.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
      *
        simpl in |- *. quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
  - simpl in |- *. quod idem est.
  - match m with | m' | | m' end.
    + match n with | n' | | n' end.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
      *
        simpl in |- *. quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
    + simpl in |- *. quod idem est.
    + match n with | n' | | n' end.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
      *
        simpl in |- *. quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Theorem identity : forall (n : Integer) . (+ Nat.One) * n = n.
Proof.
  intros n.
  match n with | n' | | n' end; simpl in |- *; quod idem est.
Qed.

(* multiplication.left.annihilation *)
Theorem annihilation : forall (n : Integer) . 0 * n = 0.
Proof.
  intros n.
  simpl in |- *.
  quod idem est.
Qed.

(* Negating a factor negates the product: the signs say so under every
 * ctor pair.
 *)
(* multiplication.left.negation *)
Theorem negation
  : forall (m : Integer) (n : Integer) . negate m * n = negate (m * n).
Proof.
  intros m n.
  match m with | m' | | m' end.
  - match n with | n' | | n' end; simpl in |- *; quod idem est.
  - simpl in |- *. quod idem est.
  - match n with | n' | | n' end; simpl in |- *; quod idem est.
Qed.

Module positive. (* multiplication.left.positive *)

Module distributivity. (* multiplication.left.positive.distributivity *)

Module over. (* multiplication.left.positive.distributivity.over *)

(* The positive case, which the general one below reduces to. It takes the
 * negation law from [left] rather than from [right]: [right.negation] is
 * proved from this module's own [negation], so reaching for it here would
 * make the two side modules need each other.
 *)
(* multiplication.left.positive.distributivity.over.addition *)
Lemma addition
  : forall (k : Nat) (m : Integer) (n : Integer) .
      (+ k) * (m + n) = ((+ k) * m) + ((+ k) * n).
Proof.
  intros k m n.
  simpl add in |- *.
  leibniz (difference.nat_with_zero.scaling k
            (ramp m + ramp n)%nat_with_zero
            (ramp (negate m) + ramp (negate n))%nat_with_zero) in |- *.
  leibniz (NatWithZero.multiplication.left.distributivity.over.addition
            k
            (ramp m)
            (ramp n)) in |- *.
  leibniz (NatWithZero.multiplication.left.distributivity.over.addition
            k
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  leibniz (ramp.scaling k m) in |- *.
  leibniz (ramp.scaling k n) in |- *.
  let proof nm := Identity.transitivity
                (Identity.transitivity
                  (multiplication.commutativity (+ k) (negate m))
                  (multiplication.left.negation m (+ k)))
                (congru negate, (multiplication.commutativity m (+ k))).
  let proof nn := Identity.transitivity
                (Identity.transitivity
                  (multiplication.commutativity (+ k) (negate n))
                  (multiplication.left.negation n (+ k)))
                (congru negate, (multiplication.commutativity n (+ k))).
  leibniz <- nm in |- *.
  leibniz <- nn in |- *.
  leibniz (ramp.scaling k (negate m)) in |- *.
  leibniz (ramp.scaling k (negate n)) in |- *.
  quod idem est.
Qed.

End over. (* multiplication.left.positive.distributivity.over *)

End distributivity. (* multiplication.left.positive.distributivity *)

End positive. (* multiplication.left.positive *)

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (l : Integer) (m : Integer) (n : Integer) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  match l with | p | | p end.
  - lemma facto
      : negate (+ &p) * (&m + &n) = (negate (+ &p) * &m) + (negate (+ &p) * &n).
    {
      leibniz -> (multiplication.left.negation (+ p) (m + n))
              in |- *.
      leibniz -> (multiplication.left.negation (+ p) m)
              in |- *.
      leibniz -> (multiplication.left.negation (+ p) n)
              in |- *.
      leibniz <- (negation.additivity ((+ p) * m) ((+ p) * n))
              in |- *.
      leibniz -> (multiplication.left.positive.distributivity.over.addition p m n)
              in |- *.
      quod idem est.
    }
    ipso facto.
  - simpl in |- *.
    leibniz (addition.left.identity 0) in |- *.
    quod idem est.
  - ipso (multiplication.left.positive.distributivity.over.addition p m n).
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

Module order. (* multiplication.left.order *)

Module strict. (* multiplication.left.order.strict *)

(* multiplication.left.order.strict.monotonicity *)
Theorem monotonicity
  : forall (p : Nat) (m : Integer) (n : Integer) .
      m < n -> (+ p) * m < (+ p) * n.
Proof.
  intros p m n h.
  simpl ( _ < _ ) in h.
  match h with | d e end.
  simpl ( _ < _ ) in |- *.
  exists (p * d)%nat.
  lemma facto : ((+ &p) * &m) + ((+ &p) * (+ &d)) = (+ &p) * &n.
  {
    leibniz <- (multiplication.left.distributivity.over.addition (+ p) m (+ d))
            in |- *.
    leibniz -> e
            in |- *.
    quod idem est.
  }
  ipso facto.
Qed.

End strict. (* multiplication.left.order.strict *)

End order. (* multiplication.left.order *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
Theorem identity : forall (n : Integer) . n * (+ Nat.One) = n.
Proof.
  intros n.
  leibniz (multiplication.commutativity n (+ Nat.One)) in |- *.
  ipso (multiplication.left.identity n).
Qed.

(* multiplication.right.annihilation *)
Theorem annihilation : forall (n : Integer) . n * 0 = 0.
Proof.
  intros n.
  leibniz (multiplication.commutativity n 0) in |- *.
  ipso (multiplication.left.annihilation n).
Qed.

(* multiplication.right.negation *)
Theorem negation
  : forall (m : Integer) (n : Integer) . m * negate n = negate (m * n).
Proof.
  intros m n.
  leibniz (multiplication.commutativity m (negate n)) in |- *.
  leibniz (multiplication.left.negation n m) in |- *.
  leibniz (multiplication.commutativity n m) in |- *.
  quod idem est.
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  leibniz (multiplication.commutativity (m + n) l) in |- *.
  leibniz (multiplication.left.distributivity.over.addition l m n) in |- *.
  leibniz (multiplication.commutativity l m) in |- *.
  leibniz (multiplication.commutativity l n) in |- *.
  quod idem est.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (n : Integer) . ((+ Nat.One) * n = n) /\ (n * (+ Nat.One) = n).
Proof.
  intros n.
  divide et impera.
  - ipso (multiplication.left.identity  n).
  - ipso (multiplication.right.identity n).
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : Integer) (y : Integer) (z : Integer) .
      (x * (y + z) = (x * y) + (x * z))
    /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (multiplication.left.distributivity.over.addition  x y z).
  - ipso (multiplication.right.distributivity.over.addition x y z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

(* multiplication.interchange *)
Theorem interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      (a * b) * (c * d) = (a * c) * (b * d).
Proof.
  intros a b c d.
  leibniz (multiplication.associativity a b (c * d)) in |- *.
  let proof inner := Identity.symmetry (multiplication.associativity b c d).
  leibniz inner in |- *.
  leibniz (multiplication.commutativity b c) in |- *.
  leibniz (multiplication.associativity c b d) in |- *.
  let proof outer := Identity.symmetry (multiplication.associativity a c (b * d)).
  leibniz outer in |- *.
  quod idem est.
Qed.

(* multiplication.cancellation *)
Theorem cancellation
  : forall (k : Integer) (m : Integer) (n : Integer) .
      ~ (k = 0) -> k * m = k * n -> m = n.
Proof.
  intros k m n nonzero e.
  match k with | p | | p end.
  - match m with | a | | a end; match n with | b | | b end; simpl in e.
    + match (Nat.multiplication.cancellation p a b) with | cancel _ end.
      leibniz (cancel (magnitude.positive.injectivity e)) in |- *.
      quod idem est.
    + ex e quodlibet.
    + ex e quodlibet.
    + ex e quodlibet.
    + quod idem est.
    + ex e quodlibet.
    + ex e quodlibet.
    + ex e quodlibet.
    + match (Nat.multiplication.cancellation p a b) with | cancel _ end.
      leibniz (cancel (magnitude.negative.injectivity e)) in |- *.
      quod idem est.
  - simpl (~ _) in nonzero.
    modus ponens nonzero, (Identity.reflexivity 0) |- f.
    ex f quodlibet.
  - match m with | a | | a end; match n with | b | | b end; simpl in e.
    + match (Nat.multiplication.cancellation p a b) with | cancel _ end.
      leibniz (cancel (magnitude.negative.injectivity e)) in |- *.
      quod idem est.
    + ex e quodlibet.
    + ex e quodlibet.
    + ex e quodlibet.
    + quod idem est.
    + ex e quodlibet.
    + ex e quodlibet.
    + ex e quodlibet.
    + match (Nat.multiplication.cancellation p a b) with | cancel _ end.
      leibniz (cancel (magnitude.positive.injectivity e)) in |- *.
      quod idem est.
Qed.

(* multiplication.magnitude *)
Theorem magnitude
  : forall (m : Integer) (n : Integer) .
      (| m * n |) = ((| m |) * (| n |))%nat_with_zero.
Proof.
  intros m n.
  match m with | m' | | m' end; match n with | n' | | n' end; simpl in |- *; quod idem est.
Qed.

Module positive. (* multiplication.positive *)

(* multiplication.positive.homomorphism *)
Theorem homomorphism
  : forall (m : Nat) (n : Nat) .
      (+ m) * (+ n) = + (m * n)%nat.
Proof.
  intros m n.
  simpl mul in |- *.
  quod idem est.
Qed.

End positive. (* multiplication.positive *)

End multiplication. (* multiplication *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : Integer) . ~ (n < n).
Proof.
  intros n.
  simpl (~ _) in |- *.
  intro h.
  simpl ( _ < _ ) in h.
  match h with | k e end.
  let proof e' := Identity.transitivity e (Identity.symmetry (addition.right.identity n)).
  let proof f := addition.left.cancellation e'.
  ex f quodlibet.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : Integer} {m : Integer} {n : Integer} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  simpl ( _ < _ ) in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl ( _ < _ ) in |- *.
  exists (k1 + k2)%nat.
  lemma facto : &l + ((+ &k1) + (+ &k2)) = &n.
  {
    leibniz <- (addition.associativity l (+ k1) (+ k2)) in |- *.
    leibniz e1 in |- *.
    ipso e2.
  }
  ipso facto.
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  match m with | m' | | m' end; match n with | n' | | n' end.
  - simpl in |- *.
    ipso (Nat.comparison.antisymmetry n' m').
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (Nat.comparison.antisymmetry m' n').
Qed.

Module strict. (* comparison.strict *)

(* comparison.strict.specification *)
Lemma specification
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.Lt <-> m < n.
Proof.
  intros m n.
  simpl ( _ < _ ) in |- *.
  simpl add in |- *.
  match m with | m' | | m' end; match n with | n' | | n' end; divide et impera; simpl in |- *.
  - intro c.
    let proof lt := Nat.comparison.strict.forward.specification c.
    simpl ( _ < _ )%nat in lt.
    match lt with | k e end.
    exists k.
    leibniz (Nat.addition.commutativity n' k) in e.
    ipso (modus aequans (difference.nat.negative.specification k m' n'), e).
  - intro h.
    match h with | k e end.
    modus aequans (difference.nat.negative.specification k m' n'), e |- e'.
    lemma smaller : (&n' < &m')%nat.
    {
      simpl ( _ < _ )%nat in |- *.
      exists k.
      leibniz (Nat.addition.commutativity n' k) in |- *.
      ipso e'.
    }
    ipso (@Nat.comparison.strict.backward.specification n' m' &smaller).
  - intro c.
    exists m'.
    ipso (difference.nat.reflexivity m').
  - intro h.
    quod idem est.
  - intro c.
    exists (n' + m')%nat.
    ipso (difference.nat.left.inversion.of.addition n' m').
  - intro h.
    quod idem est.
  - intro c.
    ex c quodlibet.
  - intro h.
    match h with | k e end.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro h.
    match h with | k e end.
    ex e quodlibet.
  - intro c.
    exists n'.
    quod idem est.
  - intro h.
    quod idem est.
  - intro c.
    ex c quodlibet.
  - intro h.
    match h with | k e end.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro h.
    match h with | k e end.
    ex e quodlibet.
  - intro c.
    let proof lt := Nat.comparison.strict.forward.specification c.
    simpl ( _ < _ )%nat in lt.
    match lt with | k e end.
    exists k.
    leibniz e in |- *.
    quod idem est.
  - intro h.
    match h with | k e end.
    let proof e' := magnitude.positive.injectivity e.
    lemma smaller : (&m' < &n')%nat.
    {
      simpl ( _ < _ )%nat in |- *.
      exists k.
      ipso e'.
    }
    ipso (@Nat.comparison.strict.backward.specification m' n' &smaller).
Qed.

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Lemma specification
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.Eq <-> m = n.
Proof.
  intros m n.
  match m with | m' | | m' end; match n with | n' | | n' end; divide et impera; simpl in |- *.
  - intro c.
    let proof e := Nat.comparison.equality.forward.specification c.
    leibniz e in |- *.
    quod idem est.
  - intro e.
    let proof e' := magnitude.negative.injectivity e.
    leibniz e' in |- *.
    ipso (Comparable.comparison.reflexivity n').
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    quod idem est.
  - intro e.
    quod idem est.
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    ex c quodlibet.
  - intro e.
    ex e quodlibet.
  - intro c.
    let proof e := Nat.comparison.equality.forward.specification c.
    leibniz e in |- *.
    quod idem est.
  - intro e.
    let proof e' := magnitude.positive.injectivity e.
    leibniz e' in |- *.
    ipso (Comparable.comparison.reflexivity n').
Qed.

End equality. (* comparison.equality *)

(* comparison.specification *)
Theorem specification
  : forall (m : Integer) (n : Integer) .
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
Proof.
  intros m n.
  divide et impera.
  - ipso (comparison.strict.specification m n).
  - ipso (comparison.equality.specification m n).
Qed.

End comparison. (* comparison *)

Module division. (* division *)

(* division.magnitude *)
Theorem magnitude
  : forall (x : Integer) (d : Nat) .
      (| x /. d |) = ((| x |) /. d)%nat_with_zero.
Proof.
  intros x d.
  match x with | p | | p end.
  - simpl divide, abs in |- *.
    match (p /. d)%nat_with_zero with | | k end;
      simpl from_nat_with_zero, negate in |- *; quod idem est.
  - simpl divide, abs in |- *.
    simpl NatWithZero.divide, NatWithZero.div in |- *.
    simpl in |- *.
    quod idem est.
  - simpl divide, abs in |- *.
    match (p /. d)%nat_with_zero with | | k end;
      simpl from_nat_with_zero in |- *; quod idem est.
Qed.

(* division.exactness *)
Theorem exactness
  : forall (x : Integer) (d : Nat) .
      NatWithZero.Divides d (| x |)
      -> (x /. d) * (+ d) = x.
Proof.
  intros x d h.
  match x with | x' | | x' end.
  - simpl divide in |- *.
    let proof e := NatWithZero.division.exactness
                  x' d h.
    match (x' /. d)%nat_with_zero with | | m end.
    + simpl in e.
      ex e quodlibet.
    + simpl in |- *.
      leibniz (NatWithZero.positive.injectivity e) in |- *.
      quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl divide in |- *.
    let proof e := NatWithZero.division.exactness
                  x' d h.
    match (x' /. d)%nat_with_zero with | | m end.
    + simpl in e.
      ex e quodlibet.
    + simpl in |- *.
      leibniz (NatWithZero.positive.injectivity e) in |- *.
      quod idem est.
Qed.

(* division.exhaustiveness *)
Theorem exhaustiveness
  : forall (x : Integer) (d : Nat) .
      NatWithZero.gcd.nat
        (| x /. (NatWithZero.gcd.nat (| x |) d) |)
        (NatWithZero.divide.nat.safe
          d (NatWithZero.gcd.nat (| x |) d)
          (NatWithZero.gcd.nat.right.divisibility (| x |) d))
      = Nat.One.
Proof.
  intros x d.
  leibniz (division.magnitude x (NatWithZero.gcd.nat (| x |) d)) in |- *.
  ipso (NatWithZero.gcd.nat.exhaustiveness (| x |) d).
Qed.

(* division.invariance *)
Theorem invariance
  : forall (x : Integer) (d : Nat) (k : Nat) .
      ((+ k) * x) /. (k * d)%nat = x /. d.
Proof.
  intros x d k.
  match x with | p | | p end.
  - lemma facto : (- (&k * &p)%nat) /. (&k * &d)%nat = (- &p) /. &d.
    {
      simpl divide in |- *.
      let proof h := NatWithZero.division.invariance
                    p d k.
      let proof h
        : ((k * p)%nat /. (k * d)%nat)%nat_with_zero
          = (p /. d)%nat_with_zero
        := &h.
      leibniz h in |- *.
      quod idem est.
    }
    ipso facto.
  - simpl in |- *.
    quod idem est.
  - lemma facto : (+ (&k * &p)%nat) /. (&k * &d)%nat = (+ &p) /. &d.
    {
      simpl divide in |- *.
      let proof h := NatWithZero.division.invariance
                    p d k.
      let proof h
        : ((k * p)%nat /. (k * d)%nat)%nat_with_zero
          = (p /. d)%nat_with_zero
        := &h.
      leibniz h in |- *.
      quod idem est.
    }
    ipso facto.
Qed.

End division. (* division *)

Module divisibility. (* divisibility *)

(* divisibility.reflexivity *)
Theorem reflexivity : forall (n : Integer) . Divides n n.
Proof.
  intros n.
  simpl Divides in |- *.
  exists (+ Nat.One).
  ipso (multiplication.right.identity n).
Qed.

(* divisibility.transitivity *)
Theorem transitivity
  : forall {l : Integer} {m : Integer} {n : Integer} .
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Divides in |- *.
  exists (k1 * k2).
  leibniz <- (multiplication.associativity l k1 k2)
          in |- *.
  leibniz -> e1
          in |- *.
  ipso e2.
Qed.

Module addition. (* divisibility.addition *)

(* divisibility.addition.closure *)
Theorem closure
  : forall {d : Integer} {m : Integer} {n : Integer} .
      Divides d m -> Divides d n -> Divides d (m + n).
Proof.
  intros d m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Divides in |- *.
  exists (k1 + k2).
  leibniz (multiplication.left.distributivity.over.addition d k1 k2) in |- *.
  leibniz e1 in |- *.
  leibniz e2 in |- *.
  quod idem est.
Qed.

End addition. (* divisibility.addition *)

Module multiplication. (* divisibility.multiplication *)

(* divisibility.multiplication.closure *)
Theorem closure
  : forall (d : Integer) (m : Integer) (n : Integer) . Divides d m -> Divides d (m * n).
Proof.
  intros d m n h.
  simpl Divides in h.
  match h with | k e end.
  simpl Divides in |- *.
  exists (k * n).
  leibniz <- (multiplication.associativity d k n) in |- *.
  leibniz e in |- *.
  quod idem est.
Qed.

End multiplication. (* divisibility.multiplication *)

End divisibility. (* divisibility *)

Module parity. (* parity *)

(* parity.totality *)
Theorem totality : forall (n : Integer) . Even n \/ Odd n.
Proof.
  intros n.
  match n with | p | | p end.
  - match p with | | p' by IH end per Nat.induction.
    + lemma side : Odd (- Nat.One).
      {
        simpl Odd in |- *.
        exists (- Nat.One).
        simpl add in |- *.
        simpl in |- *.
        quod idem est.
      }
      ipso (disjoin _, &side).
    + match IH with | ev | od end.
      * lemma side : Odd (- (Nat.Successor &p')).
        {
          simpl Even, Divides in ev.
          match ev with | k e end.
          simpl Odd in |- *.
          exists (k + (- Nat.One)).
          leibniz (multiplication.left.distributivity.over.addition (+ (Nat.Successor Nat.One)) k (- Nat.One))
            in |- *.
          lemma facto
            : (((+ (Nat.Successor Nat.One)) * &k) + (- (Nat.Successor Nat.One))) + (+ Nat.One)
              = (- (Nat.Successor &p')).
          {
            leibniz e in |- *.
            leibniz (addition.associativity (- p') (- (Nat.Successor Nat.One)) (+ Nat.One))
              in |- *.
            lemma facto : (- &p') + (- Nat.One) = (- (Nat.Successor &p')).
            {
              simpl add in |- *.
              simpl in |- *.
              leibniz (Nat.addition.commutativity p' Nat.One) in |- *.
              simpl in |- *.
              quod idem est.
            }
            ipso facto.
          }
          ipso facto.
        }
        ipso (disjoin _, &side).
      * lemma side : Even (- (Nat.Successor &p')).
        {
          simpl Odd in od.
          match od with | k e end.
          simpl Even, Divides in |- *.
          exists k.
          congru (fun (x : Integer) . x + (- Nat.One)), e |- e'.
          let proof e'
            : (((+ (Nat.Successor Nat.One)) * k) + (+ Nat.One)) + (- Nat.One) = (- p') + (- Nat.One)
            := e'.
          leibniz (addition.associativity ((+ (Nat.Successor Nat.One)) * k) (+ Nat.One) (- Nat.One))
            in e'.
          let proof e'
            : ((+ (Nat.Successor Nat.One)) * k) + 0 = (- p') + (- Nat.One)
            := &e'.
          leibniz (addition.right.identity ((+ (Nat.Successor Nat.One)) * k)) in e'.
          leibniz e' in |- *.
          simpl add in |- *.
          simpl in |- *.
          leibniz (Nat.addition.commutativity p' Nat.One) in |- *.
          simpl in |- *.
          quod idem est.
        }
        ipso (disjoin &side, _).
  - lemma side : Even 0.
    {
      simpl Even in |- *.
      simpl Divides in |- *.
      exists 0.
      simpl in |- *.
      quod idem est.
    }
    ipso (disjoin &side, _).
  - match p with | | p' by IH end per Nat.induction.
    + lemma side : Odd (+ Nat.One).
      {
        simpl Odd, add in |- *.
        exists 0.
        simpl in |- *.
        quod idem est.
      }
      ipso (disjoin _, &side).
    + match IH with | ev | od end.
      * lemma side : Odd (+ (Nat.Successor &p')).
        {
          simpl Even, Divides in ev.
          match ev with | k e end.
          simpl Odd in |- *.
          exists k.
          leibniz e in |- *.
          simpl add in |- *.
          simpl in |- *.
          leibniz (Nat.addition.commutativity p' Nat.One) in |- *.
          simpl in |- *.
          quod idem est.
        }
        ipso (disjoin _, &side).
      * lemma side : Even (+ (Nat.Successor &p')).
        {
          simpl Odd in od.
          match od with | k e end.
          simpl Even, Divides in |- *.
          exists (k + (+ Nat.One)).
          leibniz (multiplication.left.distributivity.over.addition
                    (+ (Nat.Successor Nat.One)) k (+ Nat.One)) in |- *.
          lemma facto
            : ((+ (Nat.Successor Nat.One)) * &k) + ((+ Nat.One) + (+ Nat.One))
              = (+ (Nat.Successor &p')).
          {
            leibniz <- (addition.associativity
                          ((+ (Nat.Successor Nat.One)) * k)
                          (+ Nat.One)
                          (+ Nat.One)) in |- *.
            leibniz e in |- *.
            simpl add in |- *.
            simpl in |- *.
            leibniz (Nat.addition.commutativity p' Nat.One) in |- *.
            simpl in |- *.
            quod idem est.
          }
          ipso facto.
        }
        ipso (disjoin &side, _).
Qed.

Module even. (* parity.even *)

Module addition. (* parity.even.addition *)

(* parity.even.addition.closure *)
Theorem closure
  : forall {m : Integer} {n : Integer} . Even m -> Even n -> Even (m + n).
Proof.
  intros m n h1 h2.
  simpl Even in h1.
  simpl Even in h2.
  simpl Even in |- *.
  ipso (divisibility.addition.closure h1 h2).
Qed.

End addition. (* parity.even.addition *)

End even. (* parity.even *)

Module odd. (* parity.odd *)

Module addition. (* parity.odd.addition *)

(* parity.odd.addition.evenness *)
Theorem evenness
  : forall {m : Integer} {n : Integer} . Odd m -> Odd n -> Even (m + n).
Proof.
  intros m n h1 h2.
  simpl Odd in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Even, Divides in |- *.
  exists ((k1 + k2) + (+ Nat.One)).
  symm in e1, e2.
  leibniz e1 in |- *.
  leibniz e2 in |- *.
  leibniz (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) (k1 + k2) (+ Nat.One)) in |- *.
  leibniz (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) k1 k2) in |- *.
  lemma facto
    : (((+ (Nat.Successor Nat.One)) * &k1) + ((+ (Nat.Successor Nat.One)) * &k2))
        + ((+ Nat.One) + (+ Nat.One))
      = (((+ (Nat.Successor Nat.One)) * &k1) + (+ Nat.One))
        + (((+ (Nat.Successor Nat.One)) * &k2) + (+ Nat.One)).
  {
    leibniz (addition.interchange
              ((+ (Nat.Successor Nat.One)) * k1) (+ Nat.One)
              ((+ (Nat.Successor Nat.One)) * k2) (+ Nat.One)) in |- *.
    quod idem est.
  }
  ipso facto.
Qed.

End addition. (* parity.odd.addition *)

End odd. (* parity.odd *)

End parity. (* parity *)

Module narrowing. (* narrowing *)

Module nat_with_zero. (* narrowing.nat_with_zero *)

(* narrowing.nat_with_zero.retraction *)
Theorem retraction
  : forall (n : NatWithZero) . to_nat_with_zero (from_nat_with_zero n) = Some n.
Proof.
  intro n.
  match n with | Zero | Positive p end.
  - simpl from_nat_with_zero, to_nat_with_zero in |- *.
    quod idem est.
  - simpl from_nat_with_zero, to_nat_with_zero in |- *.
    quod idem est.
Qed.

(* narrowing.nat_with_zero.specification *)
Theorem specification
  : forall (x : Integer) (n : NatWithZero) .
      to_nat_with_zero x = Some n <-> x = from_nat_with_zero n.
Proof.
  intros x n.
  divide et impera.
  - intro e.
    match x with | Negative p | Zero | Positive p end.
    + simpl to_nat_with_zero in e.
      ex e quodlibet.
    + simpl to_nat_with_zero in e.
      let proof f := Option.some.injectivity e.
      leibniz <- f in |- *.
      simpl from_nat_with_zero in |- *.
      quod idem est.
    + simpl to_nat_with_zero in e.
      let proof f := Option.some.injectivity e.
      leibniz <- f in |- *.
      simpl from_nat_with_zero in |- *.
      quod idem est.
  - intro e.
    leibniz e in |- *.
    ipso (retraction n).
Qed.

(* narrowing.nat_with_zero.failure *)
Theorem failure
  : forall (x : Integer) . to_nat_with_zero x = None <-> x < 0.
Proof.
  intro x.
  divide et impera.
  - intro e.
    match x with | Negative p | Zero | Positive p end.
    + simpl ( _ < _ ) in |- *.
      exists p.
      ipso (addition.left.inverse (+ p)).
    + simpl to_nat_with_zero in e.
      ex e quodlibet.
    + simpl to_nat_with_zero in e.
      ex e quodlibet.
  - intro h.
    match x with | Negative p | Zero | Positive p end.
    + simpl to_nat_with_zero in |- *.
      quod idem est.
    + ex (order.strict.irreflexivity 0 h) quodlibet.
    + lemma above : 0 < + p.
      {
        simpl ( _ < _ ) in |- *.
        exists p.
        ipso (addition.left.identity (+ p)).
      }
      ex (order.strict.irreflexivity 0 (order.strict.transitivity above h)) quodlibet.
Qed.

End nat_with_zero. (* narrowing.nat_with_zero *)

Module nat. (* narrowing.nat *)

(* narrowing.nat.retraction *)
Theorem retraction
  : forall (p : Nat) . to_nat (+ p) = Some p.
Proof.
  intro p.
  simpl to_nat in |- *.
  quod idem est.
Qed.

(* narrowing.nat.specification *)
Theorem specification
  : forall (x : Integer) (p : Nat) . to_nat x = Some p <-> x = + p.
Proof.
  intros x p.
  divide et impera.
  - intro e.
    match x with | Negative q | Zero | Positive q end.
    + simpl to_nat in e.
      ex e quodlibet.
    + simpl to_nat in e.
      ex e quodlibet.
    + simpl to_nat in e.
      let proof f := Option.some.injectivity e.
      leibniz f in |- *.
      quod idem est.
  - intro e.
    leibniz e in |- *.
    ipso (retraction p).
Qed.

(* narrowing.nat.failure *)
Theorem failure
  : forall (x : Integer) . to_nat x = None <-> x <= 0.
Proof.
  intro x.
  divide et impera.
  - intro e.
    simpl ( _ <= _ ) in |- *.
    match x with | Negative p | Zero | Positive p end.
    + lemma below : - p < 0.
      {
        simpl ( _ < _ ) in |- *.
        exists p.
        ipso (addition.left.inverse (+ p)).
      }
      ipso (disjoin _, below).
    + ipso (disjoin (Identity.reflexivity 0), _).
    + simpl to_nat in e.
      ex e quodlibet.
  - intro h.
    simpl ( _ <= _ ) in h.
    match h with | e | lt end.
    + leibniz e in |- *.
      simpl to_nat in |- *.
      quod idem est.
    + match x with | Negative p | Zero | Positive p end.
      * simpl to_nat in |- *.
        quod idem est.
      * simpl to_nat in |- *.
        quod idem est.
      * lemma above : 0 < + p.
        {
          simpl ( _ < _ ) in |- *.
          exists p.
          ipso (addition.left.identity (+ p)).
        }
        ex (order.strict.irreflexivity 0 (order.strict.transitivity above lt)) quodlibet.
Qed.

End nat. (* narrowing.nat *)

End narrowing. (* narrowing *)

End Integer. (* Integer *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Integer], not [Integer.T]. [Zero] and [Positive] name ctors of
 * [NatWithZero] as well, so both types write theirs with the prefix.
 *)
Abbreviation Integer := Integer.T.

(* Makes the notations declared in [Module Integer] usable in every file that
 * imports this one, as [(m + n)%integer] or under an opened
 * [jwa_integer_scope]. Only the notations are exported: [add] and the laws
 * still need the [Integer.] prefix, and the local aliases [0], [+ p] and
 * [- p] stay inside the module.
 *)
Export (notations) Integer.

Coercion Integer.Positive : Nat >-> Integer.
Coercion Integer.from_nat_with_zero : NatWithZero >-> Integer.
Add Printing Coercion Integer.Positive.
Add Printing Coercion Integer.from_nat_with_zero.

Instance Integer_magnitude_well_founded
  : WellFounded (Induced (<)%nat_with_zero Integer.abs) :=
  WellFounded.induced (<)%nat_with_zero Integer.abs
    NatWithZero_less_than_well_founded.

Instance Integer_comparable
  : Comparable Integer.compare (<)%integer :=
  {| Comparable.transitivity  := @Integer.order.strict.transitivity
   ; Comparable.specification := Integer.comparison.specification
   ; Comparable.antisymmetry  := Integer.comparison.antisymmetry |}.

Instance Integer_add_monoid : Monoid Integer.add Integer.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Integer.addition.associativity |}
   ; Monoid.identity := Integer.addition.identity |}.

Instance Integer_add_cancellative : Cancellative Integer.add :=
  {| Cancellative.cancellation := Integer.addition.cancellation |}.

Instance Integer_add_commutative : Commutative Integer.add :=
  {| Commutative.commutativity := Integer.addition.commutativity |}.

Instance Integer_mul_monoid : Monoid Integer.mul Nat.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Integer.multiplication.associativity |}
   ; Monoid.identity := Integer.multiplication.identity |}.

Instance Integer_mul_commutative : Commutative Integer.mul :=
  {| Commutative.commutativity := Integer.multiplication.commutativity |}.

Instance Integer_add_group
  : Group Integer.add Integer.Zero Integer.negate :=
  {| Group.monoid  := Integer_add_monoid
   ; Group.inverse := Integer.addition.inverse |}.

Instance Integer_add_abelian_group
  : AbelianGroup Integer.add Integer.Zero Integer.negate :=
  {| AbelianGroup.group       := Integer_add_group
   ; AbelianGroup.commutative := Integer_add_commutative |}.

Instance Integer_ring
  : Ring Integer.add Integer.Zero Integer.negate Integer.mul
      Nat.One :=
  {| Ring.abelian_group  := Integer_add_abelian_group
   ; Ring.monoid         := Integer_mul_monoid
   ; Ring.distributivity := Integer.multiplication.distributivity.over.addition |}.
