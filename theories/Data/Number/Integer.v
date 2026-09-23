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
From jwa Require Import Dialect.Simpl.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Modus.

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
  nat_with_zero_difference (NatWithZero.add (ramp m) (ramp n))
                           (NatWithZero.add (ramp (negate m)) (ramp (negate n))).

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
      | - q => + (Nat.mul p q)
      | 0   => 0
      | + q => - (Nat.mul p q)
      end
  | 0 => 0
  | + p =>
      match n with
      | - q => - (Nat.mul p q)
      | 0   => 0
      | + q => + (Nat.mul p q)
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
  | - p => negate (from_nat_with_zero (NatWithZero.divide (NatWithZero.Positive p) d))
  | 0   => 0
  | + p => from_nat_with_zero (NatWithZero.divide (NatWithZero.Positive p) d)
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
  exists (k : Nat) . m + (+ k) = n.

(* [Integer -> Integer -> Prop] *)
Definition LessOrEqual := fun (m : Integer) (n : Integer) . m = n \/ LessThan m n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_integer_scope.
Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_integer_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_integer_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
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
Definition Divides := fun (d : Integer) (n : Integer) . exists (k : Integer) . d * k = n.

(* [Integer -> Prop] *)
Definition Even := fun (n : Integer) . Divides (+ (Nat.Successor Nat.One)) n.

(* [Integer -> Prop] *)
Definition Odd := fun (n : Integer) .
  exists (k : Integer) . ((+ (Nat.Successor Nat.One)) * k) + (+ Nat.One) = n.

Module magnitude. (* magnitude *)

Module negative. (* magnitude.negative *)

(* magnitude.negative.injectivity *)
Lemma injectivity
  : forall {p : Nat} {q : Nat} . (- p) = - q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) . match x with | - r => r | 0 => p | + _ => p end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

End negative. (* magnitude.negative *)

Module positive. (* magnitude.positive *)

(* magnitude.positive.injectivity *)
Lemma injectivity
  : forall {p : Nat} {q : Nat} . (+ p) = + q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) . match x with | - _ => p | 0 => p | + r => r end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

End positive. (* magnitude.positive *)

(* magnitude.injectivity *)
Theorem injectivity
  : forall (p : Nat) (q : Nat) .
      (- p = - q -> p = q) /\ (+ p = + q -> p = q).
Proof.
  intros p q.
  split.
  - exact (@magnitude.negative.injectivity p q).
  - exact (@magnitude.positive.injectivity p q).
Qed.

End magnitude. (* magnitude *)

Module embedding. (* embedding *)

(* embedding.injectivity *)
Theorem injectivity
  : forall {m : NatWithZero} {n : NatWithZero} .
      from_nat_with_zero m = from_nat_with_zero n -> m = n.
Proof.
  intros m n e.
  destruct m as [| p]; destruct n as [| q].
  - reflexivity.
  - simpl in e.
    discriminate e.
  - simpl in e.
    discriminate e.
  - simpl in e.
    pose proof (magnitude.positive.injectivity e) as e'.
    rewrite e' in |- *.
    reflexivity.
Qed.

End embedding. (* embedding *)

Module difference. (* difference *)

Module nat. (* difference.nat *)

(* difference.nat.reflexivity *)
Lemma reflexivity : forall (n : Nat) . nat_difference n n = 0.
Proof.
  intros n.
  induction n as [| n' IH] using Nat.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact IH.
Qed.

Module left. (* difference.nat.left *)

Module inversion. (* difference.nat.left.inversion *)

Module of. (* difference.nat.left.inversion.of *)

(* difference.nat.left.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (p : Nat) . nat_difference (Nat.add k p) p = + k.
Proof.
  intros k p.
  induction p as [| p' IH] using Nat.induction.
  - rewrite (Nat.addition.commutativity k Nat.One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (Nat.addition.commutativity k (Nat.Successor p')) in |- *.
    simpl in |- *.
    rewrite (Nat.addition.commutativity p' k) in |- *.
    exact IH.
Qed.

End of. (* difference.nat.left.inversion.of *)

End inversion. (* difference.nat.left.inversion *)

End left. (* difference.nat.left *)

Module right. (* difference.nat.right *)

Module inversion. (* difference.nat.right.inversion *)

Module of. (* difference.nat.right.inversion.of *)

(* difference.nat.right.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (p : Nat) . nat_difference p (Nat.add k p) = - k.
Proof.
  intros k p.
  induction p as [| p' IH] using Nat.induction.
  - rewrite (Nat.addition.commutativity k Nat.One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (Nat.addition.commutativity k (Nat.Successor p')) in |- *.
    simpl in |- *.
    rewrite (Nat.addition.commutativity p' k) in |- *.
    exact IH.
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
      Nat.add p s = Nat.add r q -> nat_difference p q = nat_difference r s.
Proof.
  intros p q r s h.
  pose proof (Nat.order.strict.trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    symmetry in e.
    rewrite e in h |- *.
    rewrite (Nat.addition.commutativity p k) in |- *.
    rewrite (difference.nat.right.inversion.of.addition k p) in |- *.
    rewrite (Nat.addition.left.commutativity r p k) in h.
    pose proof (Nat.addition.left.cancellation h) as e''.
    rewrite e'' in |- *.
    rewrite (Nat.addition.commutativity r k) in |- *.
    rewrite (difference.nat.right.inversion.of.addition k r) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in h |- *.
      rewrite (difference.nat.reflexivity q) in |- *.
      rewrite (Nat.addition.commutativity r q) in h.
      pose proof (Nat.addition.left.cancellation h) as e.
      rewrite e in |- *.
      rewrite (difference.nat.reflexivity r) in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      symmetry in e.
      rewrite e in h |- *.
      rewrite (Nat.addition.commutativity q k) in |- *.
      rewrite (difference.nat.left.inversion.of.addition k q) in |- *.
      rewrite (Nat.addition.associativity q k s) in h.
      rewrite (Nat.addition.commutativity r q) in h.
      pose proof (Nat.addition.left.cancellation h) as e''.
      symmetry in e''.
      rewrite e'' in |- *.
      rewrite (difference.nat.left.inversion.of.addition k s) in |- *.
      reflexivity.
Qed.

(* difference.nat.negation *)
Lemma negation
  : forall (p : Nat) (q : Nat) . negate (nat_difference p q) = nat_difference q p.
Proof.
  intros p q.
  pose proof (Nat.order.strict.trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    symmetry in e.
    rewrite e in |- *.
    rewrite (Nat.addition.commutativity p k) in |- *.
    rewrite (difference.nat.right.inversion.of.addition k p) in |- *.
    rewrite (difference.nat.left.inversion.of.addition  k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference.nat.reflexivity q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      symmetry in e.
      rewrite e in |- *.
      rewrite (Nat.addition.commutativity q k) in |- *.
      rewrite (difference.nat.left.inversion.of.addition  k q) in |- *.
      rewrite (difference.nat.right.inversion.of.addition k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* difference.nat.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) .
      NatWithZero.add (ramp (nat_difference p q)) (NatWithZero.Positive q)
    = NatWithZero.add (ramp (negate (nat_difference p q))) (NatWithZero.Positive p).
Proof.
  intros p q.
  pose proof (Nat.order.strict.trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    symmetry in e.
    rewrite e in |- *.
    rewrite (Nat.addition.commutativity p k) in |- *.
    rewrite (difference.nat.right.inversion.of.addition k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference.nat.reflexivity q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      symmetry in e.
      rewrite e in |- *.
      rewrite (Nat.addition.commutativity q k) in |- *.
      rewrite (difference.nat.left.inversion.of.addition k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

Module negative. (* difference.nat.negative *)

(* difference.nat.negative.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = - k <-> Nat.add p k = q.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (difference.nat.specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive.injectivity s) as e'.
    rewrite (Nat.addition.commutativity p k) in |- *.
    exact (Identity.symmetry e').
  - intro e.
    symmetry in e.
    rewrite e in |- *.
    rewrite (Nat.addition.commutativity p k) in |- *.
    exact (difference.nat.right.inversion.of.addition k p).
Qed.

End negative. (* difference.nat.negative *)

Module zero. (* difference.nat.zero *)

(* difference.nat.zero.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) . nat_difference p q = 0 <-> p = q.
Proof.
  intros p q.
  split.
  - intro e.
    pose proof (difference.nat.specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive.injectivity s) as e'.
    exact (Identity.symmetry e').
  - intro e.
    rewrite e in |- *.
    exact (difference.nat.reflexivity q).
Qed.

End zero. (* difference.nat.zero *)

Module positive. (* difference.nat.positive *)

(* difference.nat.positive.specification *)
Lemma specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = + k <-> Nat.add q k = p.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (difference.nat.specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive.injectivity s) as e'.
    rewrite (Nat.addition.commutativity q k) in |- *.
    exact e'.
  - intro e.
    symmetry in e.
    rewrite e in |- *.
    rewrite (Nat.addition.commutativity q k) in |- *.
    exact (difference.nat.left.inversion.of.addition k q).
Qed.

End positive. (* difference.nat.positive *)

(* difference.nat.scaling *)
Lemma scaling
  : forall (k : Nat) (p : Nat) (q : Nat) .
      (+ k) * nat_difference p q = nat_difference (Nat.mul k p) (Nat.mul k q).
Proof.
  intros k p q.
  pose proof (Nat.order.strict.trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [j e].
    symmetry in e.
    rewrite e in |- *.
    rewrite (Nat.addition.commutativity p j) in |- *.
    rewrite (difference.nat.right.inversion.of.addition j p) in |- *.
    simpl in |- *.
    rewrite (Nat.multiplication.left.distributivity.over.addition k j p) in |- *.
    rewrite (difference.nat.right.inversion.of.addition
              (Nat.mul k j) (Nat.mul k p)) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference.nat.reflexivity q) in |- *.
      rewrite (difference.nat.reflexivity (Nat.mul k q)) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [j e].
      symmetry in e.
      rewrite e in |- *.
      rewrite (Nat.addition.commutativity q j) in |- *.
      rewrite (difference.nat.left.inversion.of.addition j q) in |- *.
      simpl in |- *.
      rewrite (Nat.multiplication.left.distributivity.over.addition k j q) in |- *.
      rewrite (difference.nat.left.inversion.of.addition
                (Nat.mul k j) (Nat.mul k q)) in |- *.
      reflexivity.
Qed.

End nat. (* difference.nat *)

Module nat_with_zero. (* difference.nat_with_zero *)

(* difference.nat_with_zero.canonicity *)
Lemma canonicity
  : forall (x : Integer) . nat_with_zero_difference (ramp x) (ramp (negate x)) = x.
Proof.
  intros x.
  destruct x as [p | | p]; simpl in |- *; reflexivity.
Qed.

(* difference.nat_with_zero.reflexivity *)
Lemma reflexivity
  : forall (n : NatWithZero) . nat_with_zero_difference n n = 0.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference.nat.reflexivity p).
Qed.

Module left. (* difference.nat_with_zero.left *)

Module inversion. (* difference.nat_with_zero.left.inversion *)

Module of. (* difference.nat_with_zero.left.inversion.of *)

(* difference.nat_with_zero.left.inversion.of.addition *)
Lemma addition
  : forall (k : Nat) (a : NatWithZero) .
      nat_with_zero_difference (NatWithZero.add (NatWithZero.Positive k) a) a = + k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference.nat.left.inversion.of.addition k q).
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
      nat_with_zero_difference a (NatWithZero.add (NatWithZero.Positive k) a) = - k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference.nat.right.inversion.of.addition k q).
Qed.

End of. (* difference.nat_with_zero.right.inversion.of *)

End inversion. (* difference.nat_with_zero.right.inversion *)

End right. (* difference.nat_with_zero.right *)

(* difference.nat_with_zero.specification *)
Lemma specification
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.add (ramp (nat_with_zero_difference a b)) b
      = NatWithZero.add (ramp (negate (nat_with_zero_difference a b))) a.
Proof.
  intros a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference.nat.specification p q).
Qed.

(* difference.nat_with_zero.well_definedness *)
Lemma well_definedness
  : forall {a : NatWithZero} {b : NatWithZero} {c : NatWithZero} {d : NatWithZero} .
      NatWithZero.add a d = NatWithZero.add c b ->
      nat_with_zero_difference a b = nat_with_zero_difference c d.
Proof.
  intros a b c d h.
  destruct a as [| p]; destruct b as [| q].
  - simpl in h.
    rewrite (NatWithZero.addition.commutativity c NatWithZero.Zero) in h.
    simpl in h.
    rewrite h in |- *.
    rewrite (difference.nat_with_zero.reflexivity c) in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in h.
    rewrite h in |- *.
    rewrite (NatWithZero.addition.commutativity c (NatWithZero.Positive q)) in |- *.
    rewrite (difference.nat_with_zero.right.inversion.of.addition q c) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (NatWithZero.addition.commutativity c NatWithZero.Zero) in h.
    change (NatWithZero.add NatWithZero.Zero c) with c in h.
    symmetry in h.
    rewrite h in |- *.
    rewrite (difference.nat_with_zero.left.inversion.of.addition p d) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct c as [| r]; destruct d as [| s].
    + simpl in h.
      pose proof (NatWithZero.positive.injectivity h) as e.
      rewrite e in |- *.
      simpl in |- *.
      rewrite (difference.nat.reflexivity q) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive.injectivity h) as e.
      symmetry in e.
      rewrite e in |- *.
      simpl in |- *.
      rewrite (Nat.addition.commutativity p s) in |- *.
      rewrite (difference.nat.right.inversion.of.addition s p) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive.injectivity h) as e.
      rewrite e in |- *.
      simpl in |- *.
      rewrite (difference.nat.left.inversion.of.addition r q) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive.injectivity h) as e.
      simpl in |- *.
      exact (difference.nat.well_definedness e).
Qed.

(* difference.nat_with_zero.negation *)
Lemma negation
  : forall (a : NatWithZero) (b : NatWithZero) .
      negate (nat_with_zero_difference a b) = nat_with_zero_difference b a.
Proof.
  intros a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference.nat.negation p q).
Qed.

(* difference.nat_with_zero.additivity *)
Theorem additivity
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero) .
      (nat_with_zero_difference a b) + (nat_with_zero_difference c d)
    = nat_with_zero_difference (NatWithZero.add a c) (NatWithZero.add b d).
Proof.
  intros a b c d.
  unfold add in |- *.
  apply (@difference.nat_with_zero.well_definedness
           (NatWithZero.add
              (ramp (nat_with_zero_difference a b))
              (ramp (nat_with_zero_difference c d)))
           (NatWithZero.add
              (ramp (negate (nat_with_zero_difference a b)))
              (ramp (negate (nat_with_zero_difference c d))))
           (NatWithZero.add a c)
           (NatWithZero.add b d)).
  rewrite (NatWithZero.addition.interchange
            (ramp (nat_with_zero_difference a b))
            (ramp (nat_with_zero_difference c d))
            b d) in |- *.
  rewrite (difference.nat_with_zero.specification a b) in |- *.
  rewrite (difference.nat_with_zero.specification c d) in |- *.
  rewrite (NatWithZero.addition.interchange
             (ramp (negate (nat_with_zero_difference a b))) a
             (ramp (negate (nat_with_zero_difference c d))) c) in |- *.
  rewrite (NatWithZero.addition.commutativity
            (NatWithZero.add
              (ramp (negate (nat_with_zero_difference a b)))
              (ramp (negate (nat_with_zero_difference c d))))
            (NatWithZero.add
              a
              c)) in |- *.
  reflexivity.
Qed.

(* difference.nat_with_zero.scaling *)
Lemma scaling
  : forall (k : Nat) (a : NatWithZero) (b : NatWithZero) .
      (+ k) * nat_with_zero_difference a b
      = nat_with_zero_difference
          (NatWithZero.mul (NatWithZero.Positive k) a)
          (NatWithZero.mul (NatWithZero.Positive k) b).
Proof.
  intros k a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - change (nat_with_zero_difference
              (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive p))
              (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive q)))
      with (nat_difference (Nat.mul k p) (Nat.mul k q))
      in |- *.
    change (nat_with_zero_difference
              (NatWithZero.Positive p)
              (NatWithZero.Positive q))
      with (nat_difference p q)
      in |- *.
    exact (difference.nat.scaling k p q).
Qed.

End nat_with_zero. (* difference.nat_with_zero *)

End difference. (* difference *)

Module ramp. (* ramp *)

(* ramp.scaling *)
Lemma scaling
  : forall (k : Nat) (x : Integer) .
      ramp ((+ k) * x) = NatWithZero.mul (NatWithZero.Positive k) (ramp x).
Proof.
  intros k x.
  destruct x as [x' | | x']; simpl in |- *; reflexivity.
Qed.

End ramp. (* ramp *)

Module negation. (* negation *)

(* negation.involution *)
Theorem involution : forall (x : Integer) . negate (negate x) = x.
Proof.
  intros x.
  destruct x as [p | | n]; simpl in |- *; reflexivity.
Qed.

(* negation.additivity *)
Theorem additivity
  : forall (m : Integer) (n : Integer) . negate (m + n) = negate m + negate n.
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (difference.nat_with_zero.negation
            (NatWithZero.add
              (ramp m)
              (ramp n))
            (NatWithZero.add
              (ramp (negate m))
              (ramp (negate n)))) in |- *.
  rewrite (negation.involution m) in |- *.
  rewrite (negation.involution n) in |- *.
  reflexivity.
Qed.

End negation. (* negation *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  pose proof (Identity.symmetry (difference.nat_with_zero.canonicity l)) as el.
  pose proof (Identity.symmetry (difference.nat_with_zero.canonicity m)) as em.
  pose proof (Identity.symmetry (difference.nat_with_zero.canonicity n)) as en.
  rewrite el, em, en in |- *.
  rewrite (difference.nat_with_zero.additivity
            (ramp l)
            (ramp (negate l))
            (ramp m)
            (ramp (negate m))) in |- *.
  rewrite (difference.nat_with_zero.additivity
            (NatWithZero.add (ramp l) (ramp m))
            (NatWithZero.add (ramp (negate l)) (ramp (negate m)))
            (ramp n)
            (ramp (negate n))) in |- *.
  rewrite (difference.nat_with_zero.additivity
            (ramp m)
            (ramp (negate m))
            (ramp n)
            (ramp (negate n))) in |- *.
  rewrite (difference.nat_with_zero.additivity
            (ramp l)
            (ramp (negate l))
            (NatWithZero.add
              (ramp m)
              (ramp n))
            (NatWithZero.add
              (ramp (negate m))
              (ramp (negate n)))) in |- *.
  rewrite (NatWithZero.addition.associativity
            (ramp l)
            (ramp m)
            (ramp n)) in |- *.
  rewrite (NatWithZero.addition.associativity
            (ramp (negate l))
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  reflexivity.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : Integer) (n : Integer) . m + n = n + m.
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (NatWithZero.addition.commutativity
            (ramp m)
            (ramp n)) in |- *.
  rewrite (NatWithZero.addition.commutativity
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  reflexivity.
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
Theorem identity : forall (n : Integer) . 0 + n = n.
Proof.
  intros n.
  destruct n as [n' | | n']; unfold add in |- *; simpl in |- *; reflexivity.
Qed.

(* addition.left.commutativity *)
Lemma commutativity
  : forall (l : Integer) (m : Integer) (n : Integer) . l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  rewrite (addition.commutativity l (m + n)) in |- *.
  rewrite (addition.associativity m n l)     in |- *.
  rewrite (addition.commutativity n l)       in |- *.
  reflexivity.
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (n : Integer) . negate n + n = 0.
Proof.
  intros n.
  destruct n as [p | | p].
  - unfold add in |- *.
    simpl in |- *.
    exact (difference.nat.reflexivity p).
  - unfold add in |- *.
    simpl in |- *.
    reflexivity.
  - unfold add in |- *.
    simpl in |- *.
    exact (difference.nat.reflexivity p).
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall {k : Integer} {m : Integer} {n : Integer} . k + m = k + n -> m = n.
Proof.
  intros k m n h.
  pose proof (Identity.congruence (add (negate k)) h)
          as h'.
  rewrite <- (addition.associativity (negate k) k m)
          in h'.
  rewrite <- (addition.associativity (negate k) k n)
          in h'.
  rewrite (addition.left.inverse k)  in h'.
  rewrite (addition.left.identity m) in h'.
  rewrite (addition.left.identity n) in h'.
  exact h'.
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
Theorem identity : forall (n : Integer) . n + 0 = n.
Proof.
  intros n.
  rewrite (addition.commutativity n 0) in |- *.
  exact (addition.left.identity n).
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (n : Integer) . n + negate n = 0.
Proof.
  intros n.
  rewrite (addition.commutativity n (negate n)) in |- *.
  exact (addition.left.inverse n).
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall {m : Integer} {n : Integer} {k : Integer} . m + k = n + k -> m = n.
Proof.
  intros m n k h.
  rewrite (addition.commutativity m k) in h.
  rewrite (addition.commutativity n k) in h.
  exact (addition.left.cancellation h).
Qed.

End right. (* addition.right *)

(* addition.interchange *)
Theorem interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  rewrite (addition.associativity a b (c + d)) in |- *.
  rewrite (addition.left.commutativity b c d)  in |- *.
  rewrite (addition.associativity a c (b + d)) in |- *.
  reflexivity.
Qed.

(* addition.identity *)
Theorem identity
  : forall (n : Integer) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intros n.
  split.
  - exact (addition.left.identity  n).
  - exact (addition.right.identity n).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (n : Integer) . (negate n + n = 0) /\ (n + negate n = 0).
Proof.
  intros n.
  split.
  - exact (addition.left.inverse  n).
  - exact (addition.right.inverse n).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Integer) (n : Integer) (k : Integer) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (@addition.left.cancellation  m n k).
  - exact (@addition.right.cancellation m k n).
Qed.

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* addition.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : Integer) (m : Integer) (n : Integer) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition.associativity k m (+ d)) in |- *.
  rewrite e in |- *.
  reflexivity.
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
  unfold sub in |- *.
  rewrite (addition.associativity m n (negate n)) in |- *.
  rewrite (addition.right.inverse n) in |- *.
  exact (addition.right.identity m).
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
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' n') in |- *.
    reflexivity.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (l : Integer) (m : Integer) (n : Integer) . (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  destruct l as [l' | | l'].
  - destruct m as [m' | | m'].
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *.
        reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
    + simpl in |- *. reflexivity.
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
  - simpl in |- *. reflexivity.
  - destruct m as [m' | | m'].
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
    + simpl in |- *. reflexivity.
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Theorem identity : forall (n : Integer) . (+ Nat.One) * n = n.
Proof.
  intros n.
  destruct n as [n' | | n']; simpl in |- *; reflexivity.
Qed.

(* multiplication.left.annihilation *)
Theorem annihilation : forall (n : Integer) . 0 * n = 0.
Proof.
  intros n.
  simpl in |- *.
  reflexivity.
Qed.

(* Negating a factor negates the product: the signs say so under every
 * ctor pair.
 *)
(* multiplication.left.negation *)
Theorem negation
  : forall (m : Integer) (n : Integer) . negate m * n = negate (m * n).
Proof.
  intros m n.
  destruct m as [m' | | m'].
  - destruct n as [n' | | n']; simpl in |- *; reflexivity.
  - simpl in |- *. reflexivity.
  - destruct n as [n' | | n']; simpl in |- *; reflexivity.
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
  unfold add in |- *.
  rewrite (difference.nat_with_zero.scaling k
            (NatWithZero.add
              (ramp m)
              (ramp n))
            (NatWithZero.add
              (ramp (negate m))
              (ramp (negate n)))) in |- *.
  rewrite (NatWithZero.multiplication.left.distributivity.over.addition
            (NatWithZero.Positive k)
            (ramp m)
            (ramp n)) in |- *.
  rewrite (NatWithZero.multiplication.left.distributivity.over.addition
            (NatWithZero.Positive k)
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  rewrite (ramp.scaling k m) in |- *.
  rewrite (ramp.scaling k n) in |- *.
  pose proof (Identity.transitivity
                (Identity.transitivity
                  (multiplication.commutativity (+ k) (negate m))
                  (multiplication.left.negation m (+ k)))
                (Identity.congruence negate (multiplication.commutativity m (+ k))))
    as nm.
  pose proof (Identity.transitivity
                (Identity.transitivity
                  (multiplication.commutativity (+ k) (negate n))
                  (multiplication.left.negation n (+ k)))
                (Identity.congruence negate (multiplication.commutativity n (+ k))))
    as nn.
  rewrite <- nm in |- *.
  rewrite <- nn in |- *.
  rewrite (ramp.scaling k (negate m)) in |- *.
  rewrite (ramp.scaling k (negate n)) in |- *.
  reflexivity.
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
  destruct l as [p | | p].
  - change (- p) with (negate (+ p)) in |- *.
    rewrite -> (multiplication.left.negation (+ p) (m + n))
            in |- *.
    rewrite -> (multiplication.left.negation (+ p) m)
            in |- *.
    rewrite -> (multiplication.left.negation (+ p) n)
            in |- *.
    rewrite <- (negation.additivity ((+ p) * m) ((+ p) * n))
            in |- *.
    rewrite -> (multiplication.left.positive.distributivity.over.addition p m n)
            in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (addition.left.identity 0) in |- *.
    reflexivity.
  - exact (multiplication.left.positive.distributivity.over.addition p m n).
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
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul p d)).
  change (+ (Nat.mul p d)) with ((+ p) * (+ d)) in |- *.
  rewrite <- (multiplication.left.distributivity.over.addition (+ p) m (+ d))
          in |- *.
  rewrite -> e
          in |- *.
  reflexivity.
Qed.

End strict. (* multiplication.left.order.strict *)

End order. (* multiplication.left.order *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
Theorem identity : forall (n : Integer) . n * (+ Nat.One) = n.
Proof.
  intros n.
  rewrite (multiplication.commutativity n (+ Nat.One)) in |- *.
  exact (multiplication.left.identity n).
Qed.

(* multiplication.right.annihilation *)
Theorem annihilation : forall (n : Integer) . n * 0 = 0.
Proof.
  intros n.
  rewrite (multiplication.commutativity n 0) in |- *.
  exact (multiplication.left.annihilation n).
Qed.

(* multiplication.right.negation *)
Theorem negation
  : forall (m : Integer) (n : Integer) . m * negate n = negate (m * n).
Proof.
  intros m n.
  rewrite (multiplication.commutativity m (negate n)) in |- *.
  rewrite (multiplication.left.negation n m) in |- *.
  rewrite (multiplication.commutativity n m) in |- *.
  reflexivity.
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  rewrite (multiplication.commutativity (m + n) l) in |- *.
  rewrite (multiplication.left.distributivity.over.addition l m n) in |- *.
  rewrite (multiplication.commutativity l m) in |- *.
  rewrite (multiplication.commutativity l n) in |- *.
  reflexivity.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (n : Integer) . ((+ Nat.One) * n = n) /\ (n * (+ Nat.One) = n).
Proof.
  intros n.
  split.
  - exact (multiplication.left.identity  n).
  - exact (multiplication.right.identity n).
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
  split.
  - exact (multiplication.left.distributivity.over.addition  x y z).
  - exact (multiplication.right.distributivity.over.addition x y z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

(* multiplication.interchange *)
Theorem interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      (a * b) * (c * d) = (a * c) * (b * d).
Proof.
  intros a b c d.
  rewrite (multiplication.associativity a b (c * d)) in |- *.
  pose proof (Identity.symmetry (multiplication.associativity b c d)) as inner.
  rewrite inner in |- *.
  rewrite (multiplication.commutativity b c) in |- *.
  rewrite (multiplication.associativity c b d) in |- *.
  pose proof (Identity.symmetry (multiplication.associativity a c (b * d))) as outer.
  rewrite outer in |- *.
  reflexivity.
Qed.

(* multiplication.cancellation *)
Theorem cancellation
  : forall (k : Integer) (m : Integer) (n : Integer) .
      ~ (k = 0) -> k * m = k * n -> m = n.
Proof.
  intros k m n nonzero e.
  destruct k as [p | | p].
  - destruct m as [a | | a]; destruct n as [b | | b]; simpl in e.
    + destruct (Nat.multiplication.cancellation p a b) as [cancel _].
      rewrite (cancel (magnitude.positive.injectivity e)) in |- *.
      reflexivity.
    + discriminate e.
    + discriminate e.
    + discriminate e.
    + reflexivity.
    + discriminate e.
    + discriminate e.
    + discriminate e.
    + destruct (Nat.multiplication.cancellation p a b) as [cancel _].
      rewrite (cancel (magnitude.negative.injectivity e)) in |- *.
      reflexivity.
  - unfold Negation in nonzero.
    modus ponens nonzero, (Identity.reflexivity 0) as f.
    contradiction f.
  - destruct m as [a | | a]; destruct n as [b | | b]; simpl in e.
    + destruct (Nat.multiplication.cancellation p a b) as [cancel _].
      rewrite (cancel (magnitude.negative.injectivity e)) in |- *.
      reflexivity.
    + discriminate e.
    + discriminate e.
    + discriminate e.
    + reflexivity.
    + discriminate e.
    + discriminate e.
    + discriminate e.
    + destruct (Nat.multiplication.cancellation p a b) as [cancel _].
      rewrite (cancel (magnitude.positive.injectivity e)) in |- *.
      reflexivity.
Qed.

(* multiplication.magnitude *)
Theorem magnitude
  : forall (m : Integer) (n : Integer) .
      (| m * n |) = NatWithZero.mul (| m |) (| n |).
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n']; simpl in |- *; reflexivity.
Qed.

End multiplication. (* multiplication *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : Integer) . ~ (n < n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  pose proof (Identity.transitivity e (Identity.symmetry (addition.right.identity n)))
          as e'.
  pose proof (addition.left.cancellation e')
          as f.
  discriminate f.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : Integer} {m : Integer} {n : Integer} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  change (+ (Nat.add k1 k2))
    with ((+ k1) + (+ k2))
    in |- *.
  rewrite <- (addition.associativity l (+ k1) (+ k2)) in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    exact (Nat.comparison.antisymmetry n' m').
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (Nat.comparison.antisymmetry m' n').
Qed.

Module strict. (* comparison.strict *)

(* comparison.strict.specification *)
Lemma specification
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.Lt <-> m < n.
Proof.
  intros m n.
  unfold LessThan in |- *.
  unfold add in |- *.
  destruct m as [m' | | m']; destruct n as [n' | | n']; split; simpl in |- *.
  - intro c.
    pose proof (Nat.comparison.strict.forward.specification c) as lt.
    unfold Nat.LessThan in lt.
    destruct lt as [k e].
    apply (Exists_introduction k).
    rewrite (Nat.addition.commutativity n' k) in e.
    exact (modus aequans (difference.nat.negative.specification k m' n'), e).
  - intro h.
    destruct h as [k e].
    modus aequans (difference.nat.negative.specification k m' n'), e as e'.
    apply (@Nat.comparison.strict.backward.specification n' m').
    unfold Nat.LessThan in |- *.
    apply (Exists_introduction k).
    rewrite (Nat.addition.commutativity n' k) in |- *.
    exact e'.
  - intro c.
    apply (Exists_introduction m').
    exact (difference.nat.reflexivity m').
  - intro h.
    reflexivity.
  - intro c.
    apply (Exists_introduction (Nat.add n' m')).
    exact (difference.nat.left.inversion.of.addition n' m').
  - intro h.
    reflexivity.
  - intro c.
    discriminate c.
  - intro h.
    destruct h as [k e].
    discriminate e.
  - intro c.
    discriminate c.
  - intro h.
    destruct h as [k e].
    discriminate e.
  - intro c.
    apply (Exists_introduction n').
    reflexivity.
  - intro h.
    reflexivity.
  - intro c.
    discriminate c.
  - intro h.
    destruct h as [k e].
    discriminate e.
  - intro c.
    discriminate c.
  - intro h.
    destruct h as [k e].
    discriminate e.
  - intro c.
    pose proof (Nat.comparison.strict.forward.specification c) as lt.
    unfold Nat.LessThan in lt.
    destruct lt as [k e].
    apply (Exists_introduction k).
    rewrite e in |- *.
    reflexivity.
  - intro h.
    destruct h as [k e].
    pose proof (magnitude.positive.injectivity e) as e'.
    apply (@Nat.comparison.strict.backward.specification m' n').
    unfold Nat.LessThan in |- *.
    apply (Exists_introduction k).
    exact e'.
Qed.

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Lemma specification
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.Eq <-> m = n.
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n']; split; simpl in |- *.
  - intro c.
    pose proof (Nat.comparison.equality.forward.specification c) as e.
    rewrite e in |- *.
    reflexivity.
  - intro e.
    pose proof (magnitude.negative.injectivity e) as e'.
    rewrite e' in |- *.
    exact (Comparable.comparison.reflexivity n').
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    reflexivity.
  - intro e.
    reflexivity.
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    discriminate c.
  - intro e.
    discriminate e.
  - intro c.
    pose proof (Nat.comparison.equality.forward.specification c) as e.
    rewrite e in |- *.
    reflexivity.
  - intro e.
    pose proof (magnitude.positive.injectivity e) as e'.
    rewrite e' in |- *.
    exact (Comparable.comparison.reflexivity n').
Qed.

End equality. (* comparison.equality *)

(* comparison.specification *)
Theorem specification
  : forall (m : Integer) (n : Integer) .
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
Proof.
  intros m n.
  split.
  - exact (comparison.strict.specification m n).
  - exact (comparison.equality.specification m n).
Qed.

End comparison. (* comparison *)

Module division. (* division *)

(* division.magnitude *)
Theorem magnitude
  : forall (x : Integer) (d : Nat) .
      (| x /. d |) = NatWithZero.divide (| x |) d.
Proof.
  intros x d.
  destruct x as [p | | p].
  - simpl divide, abs in |- *.
    destruct (NatWithZero.divide (NatWithZero.Positive p) d) as [| k]; reflexivity.
  - reflexivity.
  - simpl divide, abs in |- *.
    destruct (NatWithZero.divide (NatWithZero.Positive p) d) as [| k]; reflexivity.
Qed.

(* division.exactness *)
Theorem exactness
  : forall (x : Integer) (d : Nat) .
      NatWithZero.Divides (NatWithZero.Positive d) (| x |)
      -> (x /. d) * (+ d) = x.
Proof.
  intros x d h.
  destruct x as [x' | | x'].
  - simpl divide in |- *.
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive x') d h) as e.
    destruct (NatWithZero.divide (NatWithZero.Positive x') d) as [| m].
    + simpl in e.
      discriminate e.
    + simpl in |- *.
      rewrite (NatWithZero.positive.injectivity e) in |- *.
      reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl divide in |- *.
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive x') d h) as e.
    destruct (NatWithZero.divide (NatWithZero.Positive x') d) as [| m].
    + simpl in e.
      discriminate e.
    + simpl in |- *.
      rewrite (NatWithZero.positive.injectivity e) in |- *.
      reflexivity.
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
  rewrite (division.magnitude x (NatWithZero.gcd.nat (| x |) d)) in |- *.
  exact (NatWithZero.gcd.nat.exhaustiveness (| x |) d).
Qed.

(* division.invariance *)
Theorem invariance
  : forall (x : Integer) (d : Nat) (k : Nat) .
      ((+ k) * x) /. (Nat.mul k d) = x /. d.
Proof.
  intros x d k.
  destruct x as [p | | p].
  - change ((+ k) * (- p)) with (- (Nat.mul k p)) in |- *.
    simpl divide in |- *.
    pose proof (NatWithZero.division.invariance
                  (NatWithZero.Positive p) d k) as h.
    change (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive p))
      with (NatWithZero.Positive (Nat.mul k p)) in h.
    rewrite h in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - change ((+ k) * (+ p)) with (+ (Nat.mul k p)) in |- *.
    simpl divide in |- *.
    pose proof (NatWithZero.division.invariance
                  (NatWithZero.Positive p) d k) as h.
    change (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive p))
      with (NatWithZero.Positive (Nat.mul k p)) in h.
    rewrite h in |- *.
    reflexivity.
Qed.

End division. (* division *)

Module divisibility. (* divisibility *)

(* divisibility.reflexivity *)
Theorem reflexivity : forall (n : Integer) . Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (+ Nat.One)).
  exact (multiplication.right.identity n).
Qed.

(* divisibility.transitivity *)
Theorem transitivity
  : forall {l : Integer} {m : Integer} {n : Integer} .
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  unfold Divides in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 * k2)).
  rewrite <- (multiplication.associativity l k1 k2)
          in |- *.
  rewrite -> e1
          in |- *.
  exact e2.
Qed.

Module addition. (* divisibility.addition *)

(* divisibility.addition.closure *)
Theorem closure
  : forall {d : Integer} {m : Integer} {n : Integer} .
      Divides d m -> Divides d n -> Divides d (m + n).
Proof.
  intros d m n h1 h2.
  unfold Divides in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 + k2)).
  rewrite (multiplication.left.distributivity.over.addition d k1 k2) in |- *.
  rewrite e1, e2 in |- *.
  reflexivity.
Qed.

End addition. (* divisibility.addition *)

Module multiplication. (* divisibility.multiplication *)

(* divisibility.multiplication.closure *)
Theorem closure
  : forall (d : Integer) (m : Integer) (n : Integer) . Divides d m -> Divides d (m * n).
Proof.
  intros d m n h.
  unfold Divides in h.
  destruct h as [k e].
  unfold Divides in |- *.
  apply (Exists_introduction (k * n)).
  rewrite <- (multiplication.associativity d k n) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

End multiplication. (* divisibility.multiplication *)

End divisibility. (* divisibility *)

Module parity. (* parity *)

(* parity.totality *)
Theorem totality : forall (n : Integer) . Even n \/ Odd n.
Proof.
  intros n.
  destruct n as [p | | p].
  - induction p as [| p' IH] using Nat.induction.
    + apply Disjunction.R.
      unfold Odd in |- *.
      apply (Exists_introduction (- Nat.One)).
      unfold add in |- *.
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.R.
        unfold Even, Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction (k + (- Nat.One))).
        rewrite (multiplication.left.distributivity.over.addition (+ (Nat.Successor Nat.One)) k (- Nat.One))
          in |- *.
        change ((+ (Nat.Successor Nat.One)) * (- Nat.One))
          with (- (Nat.Successor Nat.One))
          in |- *.
        rewrite e in |- *.
        rewrite (addition.associativity (- p') (- (Nat.Successor Nat.One)) (+ Nat.One))
          in |- *.
        change ((- (Nat.Successor Nat.One)) + (+ Nat.One))
          with (- Nat.One)
          in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' Nat.One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even, Divides in |- *.
        apply (Exists_introduction k).
        pose proof (Identity.congruence (fun (x : Integer) . x + (- Nat.One)) e)
                as e'.
        change ((((+ (Nat.Successor Nat.One)) * k) + (+ Nat.One)) + (- Nat.One) = (- p') + (- Nat.One))
          in e'.
        rewrite (addition.associativity ((+ (Nat.Successor Nat.One)) * k) (+ Nat.One) (- Nat.One))
          in e'.
        change ((+ Nat.One) + (- Nat.One))
          with 0
          in e'.
        rewrite (addition.right.identity ((+ (Nat.Successor Nat.One)) * k)) in e'.
        rewrite e' in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' Nat.One) in |- *.
        simpl in |- *.
        reflexivity.
  - apply Disjunction.L.
    unfold Even in |- *.
    unfold Divides in |- *.
    apply (Exists_introduction 0).
    simpl in |- *.
    reflexivity.
  - induction p as [| p' IH] using Nat.induction.
    + apply Disjunction.R.
      unfold Odd, add in |- *.
      apply (Exists_introduction 0).
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.R.
        unfold Even, Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction k).
        rewrite e in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' Nat.One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even, Divides in |- *.
        apply (Exists_introduction (k + (+ Nat.One))).
        rewrite (multiplication.left.distributivity.over.addition
                  (+ (Nat.Successor Nat.One)) k (+ Nat.One)) in |- *.
        change ((+ (Nat.Successor Nat.One)) * (+ Nat.One))
          with ((+ Nat.One) + (+ Nat.One))
          in |- *.
        rewrite <- (addition.associativity
                      ((+ (Nat.Successor Nat.One)) * k)
                      (+ Nat.One)
                      (+ Nat.One)) in |- *.
        rewrite e in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' Nat.One) in |- *.
        simpl in |- *.
        reflexivity.
Qed.

Module even. (* parity.even *)

Module addition. (* parity.even.addition *)

(* parity.even.addition.closure *)
Theorem closure
  : forall {m : Integer} {n : Integer} . Even m -> Even n -> Even (m + n).
Proof.
  intros m n h1 h2.
  unfold Even in h1.
  unfold Even in h2.
  unfold Even in |- *.
  exact (divisibility.addition.closure h1 h2).
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
  unfold Odd in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Even, Divides in |- *.
  apply (Exists_introduction ((k1 + k2) + (+ Nat.One))).
  symmetry in e1, e2.
  rewrite e1, e2 in |- *.
  rewrite (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) (k1 + k2) (+ Nat.One)) in |- *.
  rewrite (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) k1 k2) in |- *.
  change ((+ (Nat.Successor Nat.One)) * (+ Nat.One))
    with ((+ Nat.One) + (+ Nat.One))
    in |- *.
  rewrite (addition.interchange
            ((+ (Nat.Successor Nat.One)) * k1) (+ Nat.One)
            ((+ (Nat.Successor Nat.One)) * k2) (+ Nat.One)) in |- *.
  reflexivity.
Qed.

End addition. (* parity.odd.addition *)

End odd. (* parity.odd *)

End parity. (* parity *)

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

(* [Integer.LessThan] is not well founded -- [0], [- 1], [- 2] descends for
 * ever -- so a recursion on an [Integer] descends on its magnitude instead,
 * and that relation is well founded for nothing but [NatWithZero]'s being
 * so.
 *)
Instance Integer_magnitude_well_founded
  : WellFounded (Induced NatWithZero.LessThan Integer.abs) :=
  WellFounded.induced NatWithZero.LessThan Integer.abs
    NatWithZero_less_than_well_founded.

Instance Integer_comparable
  : Comparable Integer.compare Integer.LessThan :=
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

Instance Integer_mul_monoid : Monoid Integer.mul (Integer.Positive Nat.One) :=
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
      (Integer.Positive Nat.One) :=
  {| Ring.abelian_group  := Integer_add_abelian_group
   ; Ring.monoid         := Integer_mul_monoid
   ; Ring.distributivity := Integer.multiplication.distributivity.over.addition |}.
