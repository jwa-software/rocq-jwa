(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Descent.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [Bin.add]. The type
 * and its ctors are declared inside it, so no later file can rebind them.
 *)
Module Bin. (* Bin *)

(* A positive number in binary, its leading bit innermost: [One] is 1, [b0]
 * appends a 0 at the low end and [b1] appends a 1, so six, 110 in binary, is
 * [b0 (b1 One)]. The leading bit is always 1, so every positive number has
 * exactly one term; [NatWithZero]'s counterpart [BinWithZero] adds zero on
 * top.
 *)
Inductive T : Type :=
  | One : T
  | b0  : T -> T
  | b1  : T -> T.

(* The carrier is named [T] so that the type itself reads [Bin] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Bin].
 *)
Abbreviation Bin := T.

Definition induction
  : forall (P : Bin -> Prop) .
      P One ->
      (forall (b : Bin) . P b -> P (b0 b)) ->
      (forall (b : Bin) . P b -> P (b1 b)) ->
      forall (b : Bin) . P b
  := fun (P : Bin -> Prop)
         (one : P One)
         (append_zero : forall (b : Bin) . P b -> P (b0 b))
         (append_one : forall (b : Bin) . P b -> P (b1 b)) .
       fix go (b : Bin) : P b :=
         match b with
         | One   => one
         | b0 b' => append_zero b' (go b')
         | b1 b' => append_one b' (go b')
         end.

(* [Bin -> Bin] *)
Fixpoint inc (b : Bin) : Bin :=
  match b with
  | One   => b0 One
  | b0 b' => b1 b'
  | b1 b' => b0 (inc b')
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Bin] a client writes [(a + b)%bin]. [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "++ b" := (inc b) (only parsing)
  : jwa_bin_scope.

(* [b] with [bit] written after its lowest bit: [2b], or [2b + 1] when [bit]
 * is [true]. [BinWithZero] carries the same operation on its own type, and
 * takes its arguments in the same order.
 *)
(* [Bool -> Bin -> Bin] *)
Definition append_bit := fun (bit : Bool) (b : Bin) .
  match bit with
  | true  => b1 b
  | false => b0 b
  end.

(* [b] incremented when [bit] is [true] and left alone when it is [false]:
 * a carry added to a number, where [append_bit] writes a bit beside one.
 *)
(* [Bool -> Bin -> Bin] *)
Definition inc_if := fun (bit : Bool) (b : Bin) .
  match bit with
  | true  => inc b
  | false => b
  end.

(* Bit by bit from the least significant end, the carry passed on: [a + b]
 * when [carry] is [false], [a + b + 1] when it is [true]. Each bit is read
 * once, so a sum costs as many steps as the longer operand has bits.
 *
 * Every case is [append_bit <this bit> <the rest>], so each reads as the
 * arithmetic it stands for rather than as an entry in a table. The bit is
 * [carry] where the two bits taken from [a] and [b] sum to an even number,
 * and its negation where they sum to an odd one. The rest is what is left
 * to add, and takes a carry of its own wherever the column can reach two.
 *
 * The carry is threaded rather than dropped: [a + b + 1] is [inc (a + b)],
 * so the carried cases are redundant in principle, but [b1] meeting [b1]
 * would then call [inc] once per digit and a sum would cost the square of
 * its length instead of its length.
 *)
(* [Bool -> Bin -> Bin -> Bin] *)
Fixpoint add_with_carry (carry : Bool) (a : Bin) (b : Bin) : Bin :=
  match a, b with
  | One, One     => append_bit carry One
  | One, b0 b'   => append_bit (Bool.negate carry) (inc_if carry b')
  | One, b1 b'   => append_bit carry (inc b')
  | b0 a', One   => append_bit (Bool.negate carry) (inc_if carry a')
  | b0 a', b0 b' => append_bit carry (add_with_carry false a' b')
  | b0 a', b1 b' => append_bit (Bool.negate carry) (add_with_carry carry a' b')
  | b1 a', One   => append_bit carry (inc a')
  | b1 a', b0 b' => append_bit (Bool.negate carry) (add_with_carry carry a' b')
  | b1 a', b1 b' => append_bit carry (add_with_carry true a' b')
  end.

(* [Bin -> Bin -> Bin] *)
Definition add := fun (a : Bin) (b : Bin) . add_with_carry false a b.

Notation "a + b" := (add a b) (only parsing)
  : jwa_bin_scope.

(* Shift and add: [2a * b] is [a * b] shifted, [(2a + 1) * b] adds [b]. *)
(* [Bin -> Bin -> Bin] *)
Fixpoint mul (a : Bin) (b : Bin) : Bin :=
  match a with
  | One   => b
  | b0 a' => b0 (mul a' b)
  | b1 a' => add b (b0 (mul a' b))
  end.

Notation "a * b" := (mul a b) (only parsing)
  : jwa_bin_scope.

Local Open Scope jwa_bin_scope.

(* [Bin -> Bin] *)
Definition square := fun (b : Bin) . b * b.

(* Squaring once per bit of the exponent: [a ^ 2n] squares [a ^ n] instead
 * of computing it twice, so a power costs as many steps as [n] has bits.
 *)
(* [Bin -> Bin -> Bin] *)
Fixpoint power (a : Bin) (n : Bin) : Bin :=
  match n with
  | One   => a
  | b0 n' => square (power a n')
  | b1 n' => a * square (power a n')
  end.

Notation "a ^ n" := (power a n) (only parsing)
  : jwa_bin_scope.

(* Where [a] sits relative to [b], which is all [a - b] can report when only
 * positives exist: less, equal, or greater by this much. [Comparison] gives
 * the same three answers without the witness, so [compare] below is this type
 * with its payload forgotten.
 *)
Inductive Difference : Type :=
  | Lt : Difference
  | Eq : Difference
  | Gt : Bin -> Difference.

(* [2d] for a difference [d]. *)
(* [Difference -> Difference] *)
Definition append_zero_difference := fun (d : Difference) .
  match d with
  | Lt   => Lt
  | Eq   => Eq
  | Gt p => Gt (b0 p)
  end.

(* [2d + 1]: from zero it reaches one. *)
(* [Difference -> Difference] *)
Definition append_one_difference := fun (d : Difference) .
  match d with
  | Lt   => Lt
  | Eq   => Gt One
  | Gt p => Gt (b1 p)
  end.

(* [2d], or [2d + 1] when [bit] is [true]: the [Difference] counterpart of
 * [append_bit], and what lets one arm below answer for both borrows.
 *)
(* [Bool -> Difference -> Difference] *)
Definition append_bit_difference := fun (bit : Bool) (d : Difference) .
  match bit with
  | true  => append_one_difference d
  | false => append_zero_difference d
  end.

(* Bit by bit from the least significant end, the borrow passed on as
 * [add_with_carry] passes its carry: [a - b] when [borrow] is [false],
 * [a - b - 1] when it is [true].
 *
 * Seven of the nine cases answer for both borrows at once, in the shape
 * [append_bit_difference <this bit> <the rest>] that every case of
 * [add_with_carry] has. Two cannot. At [One] against [One] the answer is
 * [Eq] or [Lt], and neither is a bit appended to anything. At [b1]
 * against [One] the borrow decides whether the rest is [a'] or [a' - 1],
 * which are answers of different shapes rather than one answer under two
 * bits. Those two keep a [match borrow] of their own.
 *)
(* [Bool -> Bin -> Bin -> Difference] *)
Fixpoint difference_with_borrow (borrow : Bool) (a : Bin) (b : Bin) : Difference :=
  match a, b with
  | One, One     =>
      match borrow with
      | true  => Lt
      | false => Eq
      end
  | One, b0 _    => Lt
  | One, b1 _    => Lt
  | b0 a', One   => append_bit_difference (Bool.negate borrow) (difference_with_borrow false a' One)
  | b0 a', b0 b' => append_bit_difference borrow (difference_with_borrow borrow a' b')
  | b0 a', b1 b' => append_bit_difference (Bool.negate borrow) (difference_with_borrow true a' b')
  | b1 a', One   =>
      match borrow with
      | true  => append_bit_difference true (difference_with_borrow false a' One)
      | false => Gt (b0 a')
      end
  | b1 a', b0 b' => append_bit_difference (Bool.negate borrow) (difference_with_borrow false a' b')
  | b1 a', b1 b' => append_bit_difference borrow (difference_with_borrow borrow a' b')
  end.

(* [Bin -> Bin -> Difference] *)
Definition diff := fun (a : Bin) (b : Bin) . difference_with_borrow false a b.

(* [Bin -> Bin -> Prop] *)
Definition LessThan := fun (a : Bin) (b : Bin) . forsome (k : Bin) . a + k = b.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_bin_scope.

Notation "a < b" := (LessThan a b) (only parsing)
  : jwa_bin_scope.

(* [Bin -> Bin -> Prop] *)
Definition LessOrEqual := fun (a : Bin) (b : Bin) . (a = b) \/ (a < b).

Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_bin_scope.

Notation "a <= b" := (LessOrEqual a b) (only parsing)
  : jwa_bin_scope.

Notation "a > b" := (b < a) (only parsing)
  : jwa_bin_scope.

Notation "a >= b" := (LessOrEqual b a) (only parsing)
  : jwa_bin_scope.

(* [Bin -> Bin -> Comparison] *)
Definition compare := fun (a : Bin) (b : Bin) .
  match diff a b with
  | Lt   => Comparison.Lt
  | Eq   => Comparison.Eq
  | Gt _ => Comparison.Gt
  end.

(* [Bin -> Bin -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Bin -> Bin -> Bin] *)
Abbreviation min := (Comparable.min compare).

(* [Bin -> Bin -> Bin] *)
Abbreviation max := (Comparable.max compare).

(* [a - b], [None] unless it is positive, as [Nat.sub] is. *)
(* [Bin -> Bin -> Option Bin] *)
Definition sub := fun (a : Bin) (b : Bin) .
  match diff a b with
  | Gt p => Some p
  | _    => None
  end.

(* [One] where [sub] has nothing, as [Nat.saturating_sub] does. *)
(* [Bin -> Bin -> Bin] *)
Definition saturating_sub := fun (a : Bin) (b : Bin) .
  match sub a b with
  | Some k => k
  | None   => One
  end.

(* The conversions to and from [Nat], used to state the laws: [to_nat] is
 * unary, so it is for proofs, not for computing.
 *)
(* [Bin -> Nat] *)
Fixpoint to_nat (b : Bin) : Nat :=
  match b with
  | One   => Nat.One
  | b0 b' => (to_nat b' + to_nat b')%n
  | b1 b' => Nat.Successor (to_nat b' + to_nat b')%n
  end.

(* [Nat -> Bin] *)
Fixpoint from_nat (n : Nat) : Bin :=
  match n with
  | Nat.One          => One
  | Nat.Successor n' => ++ from_nat n'
  end.

Module conversion. (* conversion *)

(* conversion.successor *)
Theorem successor
  : forall (b : Bin) . to_nat (++ b) = Nat.Successor (to_nat b).
Proof.
  intro b.
  match b with | | b' by IH | b' by IH end per Bin.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz &IH in |- *.
    simpl in |- *.
    leibniz (Nat.addition.right.successor (to_nat &b') (to_nat &b')) in |- *.
    quod idem est.
Qed.

(* conversion.retraction *)
Theorem retraction
  : forall (n : Nat) . to_nat (from_nat n) = n.
Proof.
  intro n.
  match n with | | n' by IH end per Nat.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (conversion.successor (from_nat &n')) in |- *.
    leibniz &IH in |- *.
    quod idem est.
Qed.

(* conversion.doubling *)
Lemma doubling
  : forall (n : Nat) . from_nat (n + n)%n = b0 (from_nat n).
Proof.
  intro n.
  match n with | | n' by IH end per Nat.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Nat.addition.right.successor &n' &n') in |- *.
    simpl in |- *.
    leibniz &IH in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conversion.section *)
Theorem section
  : forall (b : Bin) . from_nat (to_nat b) = b.
Proof.
  intro b.
  match b with | | b' by IH | b' by IH end per Bin.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (conversion.doubling (to_nat &b')) in |- *.
    leibniz &IH in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (conversion.doubling (to_nat &b')) in |- *.
    leibniz &IH in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conversion.carry *)
Lemma carry
  : forall (carry : Bool) (a : Bin) (b : Bin) .
      to_nat (add_with_carry carry a b)
      = match carry with
        | true  => Nat.Successor (to_nat a + to_nat b)%n
        | false => (to_nat a + to_nat b)%n
        end.
Proof.
  intros carry a.
  extro &carry.
  match a with | | a' by IH | a' by IH end per Bin.induction.
  -
    intros carry b.
    match b with | | b' | b' end.
    +
      match carry with | | end.
      *
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &b') in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &b') (to_nat &b')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &b') in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &b') (to_nat &b')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (conversion.successor &b') in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &b') (to_nat &b')) in |- *.
        quod idem est.
  -
    intros carry b.
    match b with | | b' | b' end.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%n Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%n Nat.One) in |- *.
        simpl in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%n
          := &IH false &b'.
        leibniz &e in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%n
          := &IH false &b'.
        leibniz &e in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%n
          := &IH true &b'.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%n
                                              (to_nat &a' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%n
                                              (to_nat &b' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%n
          := &IH false &b'.
        leibniz &e in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%n
                                              (to_nat &b' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
  -
    intros carry b.
    match b with | | b' | b' end.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%n Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%n Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%n
          := &IH true &b'.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%n
                                              (to_nat &a' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%n
          := &IH false &b'.
        leibniz &e in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%n
          := &IH true &b'.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%n
                                              (to_nat &a' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%n
                                              (to_nat &b' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%n
          := &IH true &b'.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%n
                                              (to_nat &a' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%n
                                              (to_nat &b' + to_nat &b')%n) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
Qed.

(* conversion.addition *)
Theorem addition
  : forall (a : Bin) (b : Bin) . to_nat (a + b) = (to_nat a + to_nat b)%n.
Proof.
  intros a b.
  simpl add in |- *.
  ipso (conversion.carry false &a &b).
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (a : Bin) (b : Bin) . to_nat (a * b) = (to_nat a * to_nat b)%n.
Proof.
  intros a b.
  match a with | | a' by IH | a' by IH end per Bin.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz &IH in |- *.
    leibniz (Nat.multiplication.right.distributivity.over.addition
               (to_nat &b) (to_nat &a') (to_nat &a')) in |- *.
    quod idem est.
  -
    let proof e := conversion.addition &b (b0 (mul &a' &b)).
    simpl in &e |- *.
    leibniz &e in |- *.
    leibniz &IH in |- *.
    leibniz (Nat.multiplication.right.distributivity.over.addition
               (to_nat &b) (to_nat &a') (to_nat &a')) in |- *.
    quod idem est.
Qed.

(* conversion.power *)
Theorem power
  : forall (a : Bin) (n : Bin) . to_nat (a ^ n) = (to_nat a ^ to_nat n)%n.
Proof.
  intros a n.
  match n with | | n' by IH | n' by IH end per Bin.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    simpl square in |- *.
    leibniz (conversion.multiplication (power &a &n') (power &a &n')) in |- *.
    leibniz &IH in |- *.
    leibniz (Nat.power.exponent.addition (to_nat &a) (to_nat &n') (to_nat &n')) in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (conversion.multiplication &a (square (power &a &n'))) in |- *.
    simpl square in |- *.
    leibniz (conversion.multiplication (power &a &n') (power &a &n')) in |- *.
    leibniz &IH in |- *.
    leibniz (Nat.power.exponent.addition (to_nat &a) (to_nat &n') (to_nat &n')) in |- *.
    quod idem est.
Qed.

Module difference. (* conversion.difference *)

(* A difference [d] stands for [m - n] when its outcome agrees with [m] and
 * [n]; the lemmas below carry that agreement through the operations
 * [difference_with_borrow] applies to the difference of the rest.
 *)
(* conversion.difference.doubling *)
Lemma doubling
  : forall (d : Difference) (m : Nat) (n : Nat) .
      match d with
      | Lt   => (m < n)%n
      | Eq   => m = n
      | Gt p => (n + to_nat p)%n = m
      end ->
      match append_zero_difference d with
      | Lt   => (m + m < n + n)%n
      | Eq   => (m + m)%n = (n + n)%n
      | Gt p => (n + n + to_nat p)%n = (m + m)%n
      end.
Proof.
  intros d m n.
  match d with | | | p end.
  -
    intro h.
    simpl in |- *.
    simpl Nat.LessThan in &h |- *.
    match &h with | k e end.
    exists (&k + &k)%n.
    leibniz <- &e in |- *.
    leibniz (Nat.addition.interchange &m &k &m &k) in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz &h in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz <- &h in |- *.
    leibniz (Nat.addition.interchange &n (to_nat &p) &n (to_nat &p)) in |- *.
    quod idem est.
Qed.

Module doubling. (* conversion.difference.doubling *)

(* conversion.difference.doubling.successor *)
Lemma successor
  : forall (d : Difference) (m : Nat) (n : Nat) .
      match d with
      | Lt   => (m < n)%n
      | Eq   => m = n
      | Gt p => (n + to_nat p)%n = m
      end ->
      match append_one_difference d with
      | Lt   => (Nat.Successor (m + m) < n + n)%n
      | Eq   => Nat.Successor (m + m)%n = (n + n)%n
      | Gt p => (n + n + to_nat p)%n = Nat.Successor (m + m)%n
      end.
Proof.
  intros d m n.
  match d with | | | p end.
  -
    intro h.
    simpl in |- *.
    simpl Nat.LessThan in &h |- *.
    match &h with | k e end.
    match &k with | | k' end.
    +
      exists Nat.One.
      simpl in |- *.
      leibniz <- &e in |- *.
      leibniz (Nat.addition.interchange &m Nat.One &m Nat.One) in |- *.
      simpl in |- *.
      leibniz (Nat.addition.right.successor (&m + &m)%n Nat.One) in |- *.
      quod idem est.
    +
      exists (&k' + Nat.Successor &k')%n.
      simpl in |- *.
      leibniz <- &e in |- *.
      leibniz (Nat.addition.interchange &m (Nat.Successor &k') &m (Nat.Successor &k')) in |- *.
      simpl in |- *.
      leibniz (Nat.addition.right.successor (&m + &m)%n (&k' + Nat.Successor &k')%n)
        in |- *.
      quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz &h in |- *.
    leibniz (Nat.addition.commutativity (&n + &n)%n Nat.One) in |- *.
    simpl in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz (Nat.addition.right.successor (&n + &n)%n (to_nat &p + to_nat &p)%n) in |- *.
    leibniz <- &h in |- *.
    leibniz (Nat.addition.interchange &n (to_nat &p) &n (to_nat &p)) in |- *.
    quod idem est.
Qed.

End doubling. (* conversion.difference.doubling *)

(* conversion.difference.cancellation *)
Lemma cancellation
  : forall (d : Difference) (m : Nat) (n : Nat) .
      match d with
      | Lt   => (Nat.Successor m < Nat.Successor n)%n
      | Eq   => Nat.Successor m = Nat.Successor n
      | Gt p => (Nat.Successor n + to_nat p)%n = Nat.Successor m
      end
      <->
      match d with
      | Lt   => (m < n)%n
      | Eq   => m = n
      | Gt p => (n + to_nat p)%n = m
      end.
Proof.
  intros d m n.
  match d with | | | p end.
  -
    divide et impera.
    +
      ipso (@Nat.successor.order.monotonicity.inversion &m &n).
    +
      ipso (@Nat.successor.order.monotonicity &m &n).
  -
    divide et impera.
    +
      ipso (@Nat.successor.injectivity &m &n).
    +
      intro e.
      ipso (congru Nat.Successor, &e).
  -
    divide et impera.
    +
      intro e.
      simpl in &e.
      ipso (Nat.successor.injectivity &e).
    +
      intro e.
      simpl in |- *.
      leibniz &e in |- *.
      quod idem est.
Qed.

End difference. (* conversion.difference *)

(* conversion.borrow *)
Lemma borrow
  : forall (borrow : Bool) (a : Bin) (b : Bin) .
      match borrow with
      | true  =>
          match difference_with_borrow true a b with
          | Lt   => (to_nat a < Nat.Successor (to_nat b))%n
          | Eq   => to_nat a = Nat.Successor (to_nat b)
          | Gt p => (Nat.Successor (to_nat b) + to_nat p)%n = to_nat a
          end
      | false =>
          match difference_with_borrow false a b with
          | Lt   => (to_nat a < to_nat b)%n
          | Eq   => to_nat a = to_nat b
          | Gt p => (to_nat b + to_nat p)%n = to_nat a
          end
      end.
Proof.
  intros borrow a.
  extro &borrow.
  match a with | | a' by IH | a' by IH end per Bin.induction.
  -
    intros borrow b.
    match b with | | b' | b' end.
    +
      match borrow with | | end.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists Nat.One.
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        quod idem est.
    +
      match borrow with | | end.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists (to_nat &b' + to_nat &b')%n.
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        match (to_nat &b') with | | k end.
        --
          exists Nat.One.
          quod idem est.
        --
          exists (&k + Nat.Successor &k)%n.
          simpl in |- *.
          quod idem est.
    +
      match borrow with | | end.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists (Nat.Successor (to_nat &b' + to_nat &b')%n).
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists (to_nat &b' + to_nat &b')%n.
        simpl in |- *.
        quod idem est.
  -
    intros borrow b.
    match b with | | b' | b' end.
    +
      match borrow with | | end.
      *
        ipso (conversion.difference.doubling
                (difference_with_borrow false &a' One) (to_nat &a') Nat.One (&IH false One)).
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow false &a' One) (to_nat &a') Nat.One
                         (&IH false One).
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow false &a' One))
                   (to_nat &a' + to_nat &a')%n Nat.One),
                &h).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH true &b').
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow true &a' &b'))
                   (to_nat &a' + to_nat &a')%n
                   (Nat.Successor (to_nat &b' + to_nat &b')%n)),
                &h).
      *
        ipso (conversion.difference.doubling
                (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                (&IH false &b')).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH true &b').
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso &h.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH true &b').
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow true &a' &b'))
                   (to_nat &a' + to_nat &a')%n
                   (Nat.Successor (to_nat &b' + to_nat &b')%n)),
                &h).
  -
    intros borrow b.
    match b with | | b' | b' end.
    +
      match borrow with | | end.
      *
        ipso (conversion.difference.doubling.successor
                (difference_with_borrow false &a' One) (to_nat &a') Nat.One (&IH false One)).
      *
        simpl in |- *.
        quod idem est.
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                         (&IH false &b').
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_zero_difference (difference_with_borrow false &a' &b'))
                   (to_nat &a' + to_nat &a')%n (to_nat &b' + to_nat &b')%n),
                &h).
      *
        ipso (conversion.difference.doubling.successor
                (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                (&IH false &b')).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH true &b').
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso &h.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                         (&IH false &b').
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_zero_difference (difference_with_borrow false &a' &b'))
                   (to_nat &a' + to_nat &a')%n (to_nat &b' + to_nat &b')%n),
                &h).
Qed.

(* What each outcome of [diff] says of the two numbers. *)
(* conversion.difference *)
Lemma difference
  : forall (a : Bin) (b : Bin) .
      match Bin.diff a b with
      | Lt   => (to_nat a < to_nat b)%n
      | Eq   => to_nat a = to_nat b
      | Gt p => (to_nat b + to_nat p)%n = to_nat a
      end.
Proof.
  intros a b.
  ipso (conversion.borrow false &a &b).
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (a : Bin) (b : Bin) .
      compare a b = Nat.compare (to_nat a) (to_nat b).
Proof.
  intros a b.
  simpl compare in |- *.
  let proof h := conversion.difference &a &b.
  extro &h.
  match (Bin.diff &a &b) with | | | p end.
  -
    intro h.
    ipso (symm (Nat.comparison.strict.backward.specification &h)).
  -
    intro h.
    ipso (symm (Nat.comparison.equality.backward.specification &h)).
  -
    intro h.
    lemma below : (to_nat &b < to_nat &a)%n.
    {
      simpl Nat.LessThan in |- *.
      exists (to_nat &p).
      ipso &h.
    }
    leibniz (Nat.comparison.antisymmetry (to_nat &a) (to_nat &b)) in |- *.
    leibniz (Nat.comparison.strict.backward.specification &below) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (a : Bin) (b : Bin) .
      Option.map to_nat (sub a b) = Nat.sub (to_nat a) (to_nat b).
Proof.
  intros a b.
  simpl sub in |- *.
  let proof h := conversion.difference &a &b.
  extro &h.
  match (Bin.diff &a &b) with | | | p end.
  -
    intro h.
    simpl in |- *.
    let proof le : (to_nat &a <= to_nat &b)%n := disjoin _, &h.
    leibniz (Nat.subtraction.truncation &le) in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    let proof le : (to_nat &a <= to_nat &b)%n := disjoin &h, _.
    leibniz (Nat.subtraction.truncation &le) in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz <- &h in |- *.
    leibniz (Nat.addition.commutativity (to_nat &b) (to_nat &p)) in |- *.
    leibniz (Nat.subtraction.inversion.of.addition (to_nat &p) (to_nat &b)) in |- *.
    quod idem est.
Qed.

Module subtraction. (* conversion.subtraction *)

(* conversion.subtraction.saturating *)
Theorem saturating
  : forall (a : Bin) (b : Bin) .
      to_nat (saturating_sub a b) = Nat.saturating_sub (to_nat a) (to_nat b).
Proof.
  intros a b.
  simpl saturating_sub, Nat.saturating_sub in |- *.
  let proof e := conversion.subtraction &a &b.
  extro &e.
  match (sub &a &b) with | | k end.
  -
    intro e.
    simpl in &e |- *.
    leibniz <- &e in |- *.
    simpl in |- *.
    quod idem est.
  -
    intro e.
    simpl in &e.
    leibniz <- &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End subtraction. (* conversion.subtraction *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {a : Bin} {b : Bin} . to_nat a = to_nat b -> a = b.
Proof.
  intros a b e.
  leibniz <- (conversion.section &a), <- (conversion.section &b) in |- *.
  leibniz &e in |- *.
  quod idem est.
Qed.

(* conversion.order *)
Theorem order
  : forall (a : Bin) (b : Bin) . a < b <-> (to_nat a < to_nat b)%n.
Proof.
  intros a b.
  divide et impera.
  -
    intro h.
    simpl LessThan in &h.
    match &h with | k e end.
    simpl Nat.LessThan in |- *.
    exists (to_nat &k).
    leibniz <- &e in |- *.
    leibniz (conversion.addition &a &k) in |- *.
    quod idem est.
  -
    intro h.
    simpl Nat.LessThan in &h.
    match &h with | j e end.
    simpl LessThan in |- *.
    exists (from_nat &j).
    lemma f : to_nat (&a + from_nat &j) = to_nat &b.
    {
      leibniz (conversion.addition &a (from_nat &j)), (conversion.retraction &j) in |- *.
      ipso &e.
    }
    ipso (conversion.injectivity &f).
Qed.

End conversion. (* conversion *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (a : Bin) (b : Bin) (c : Bin) . (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  lemma f : to_nat ((&a + &b) + &c) = to_nat (&a + (&b + &c)).
  {
    leibniz (conversion.addition (&a + &b) &c), (conversion.addition &a &b),
            (conversion.addition &a (&b + &c)), (conversion.addition &b &c) in |- *.
    ipso (Nat.addition.associativity (to_nat &a) (to_nat &b) (to_nat &c)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (a : Bin) (b : Bin) . a + b = b + a.
Proof.
  intros a b.
  lemma f : to_nat (&a + &b) = to_nat (&b + &a).
  {
    leibniz (conversion.addition &a &b), (conversion.addition &b &a) in |- *.
    ipso (Nat.addition.commutativity (to_nat &a) (to_nat &b)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (a : Bin) (b : Bin) (c : Bin) .
    (a + b = a + c -> b = c) /\ (a + b = c + b -> a = c).
Proof.
  intros a b c.
  let proof n := Nat.addition.cancellation (to_nat &a) (to_nat &b) (to_nat &c).
  match &n with | l r end.
  divide et impera.
  -
    intro e.
    let proof f := congru to_nat, &e.
    leibniz (conversion.addition &a &b), (conversion.addition &a &c) in &f.
    ipso (conversion.injectivity (&l &f)).
  -
    intro e.
    let proof f := congru to_nat, &e.
    leibniz (conversion.addition &a &b), (conversion.addition &c &b) in &f.
    ipso (conversion.injectivity (&r &f)).
Qed.

End addition. (* addition *)

Module multiplication. (* multiplication *)

(* multiplication.associativity *)
Theorem associativity
  : forall (a : Bin) (b : Bin) (c : Bin) . (a * b) * c = a * (b * c).
Proof.
  intros a b c.
  lemma f : to_nat ((&a * &b) * &c) = to_nat (&a * (&b * &c)).
  {
    leibniz (conversion.multiplication (&a * &b) &c), (conversion.multiplication &a &b),
            (conversion.multiplication &a (&b * &c)), (conversion.multiplication &b &c)
      in |- *.
    ipso (Nat.multiplication.associativity (to_nat &a) (to_nat &b) (to_nat &c)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.commutativity *)
Theorem commutativity : forall (a : Bin) (b : Bin) . a * b = b * a.
Proof.
  intros a b.
  lemma f : to_nat (&a * &b) = to_nat (&b * &a).
  {
    leibniz (conversion.multiplication &a &b), (conversion.multiplication &b &a) in |- *.
    ipso (Nat.multiplication.commutativity (to_nat &a) (to_nat &b)).
  }
  ipso (conversion.injectivity &f).
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (b : Bin) . (One * b = b) /\ (b * One = b).
Proof.
  intro b.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    let proof i := Nat.multiplication.identity (to_nat &b).
    match &i with | l r end.
    lemma f : to_nat (&b * One) = to_nat &b.
    {
      leibniz (conversion.multiplication &b One) in |- *.
      ipso &r.
    }
    ipso (conversion.injectivity &f).
Qed.

(* multiplication.cancellation *)
Theorem cancellation
  : forall (a : Bin) (b : Bin) (c : Bin) .
      (a * b = a * c -> b = c) /\ (a * b = c * b -> a = c).
Proof.
  intros a b c.
  let proof n := Nat.multiplication.cancellation (to_nat &a) (to_nat &b) (to_nat &c).
  match &n with | l r end.
  divide et impera.
  -
    intro e.
    let proof f := congru to_nat, &e.
    leibniz (conversion.multiplication &a &b), (conversion.multiplication &a &c) in &f.
    ipso (conversion.injectivity (&l &f)).
  -
    intro e.
    let proof f := congru to_nat, &e.
    leibniz (conversion.multiplication &a &b), (conversion.multiplication &c &b) in &f.
    ipso (conversion.injectivity (&r &f)).
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (a : Bin) (b : Bin) (c : Bin) .
      (a * (b + c) = (a * b) + (a * c)) /\ ((b + c) * a = (b * a) + (c * a)).
Proof.
  intros a b c.
  divide et impera.
  -
    lemma f : to_nat (&a * (&b + &c)) = to_nat ((&a * &b) + (&a * &c)).
    {
      leibniz (conversion.multiplication &a (&b + &c)), (conversion.addition &b &c),
              (conversion.addition (&a * &b) (&a * &c)),
              (conversion.multiplication &a &b), (conversion.multiplication &a &c) in |- *.
      ipso (Nat.multiplication.left.distributivity.over.addition
              (to_nat &a) (to_nat &b) (to_nat &c)).
    }
    ipso (conversion.injectivity &f).
  -
    lemma f : to_nat ((&b + &c) * &a) = to_nat ((&b * &a) + (&c * &a)).
    {
      leibniz (conversion.multiplication (&b + &c) &a), (conversion.addition &b &c),
              (conversion.addition (&b * &a) (&c * &a)),
              (conversion.multiplication &b &a), (conversion.multiplication &c &a) in |- *.
      ipso (Nat.multiplication.right.distributivity.over.addition
              (to_nat &a) (to_nat &b) (to_nat &c)).
    }
    ipso (conversion.injectivity &f).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (b : Bin) . ~ (b < b).
Proof.
  intros b h.
  ipso (Nat.order.strict.irreflexivity (to_nat &b) (modus aequans (conversion.order &b &b), &h)).
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {a : Bin} {b : Bin} {c : Bin} . a < b -> b < c -> a < c.
Proof.
  intros a b c h1 h2.
  let proof n := Nat.order.strict.transitivity
                   (modus aequans (conversion.order &a &b), &h1)
                   (modus aequans (conversion.order &b &c), &h2).
  ipso (modus aequans (conversion.order &a &c), &n).
Qed.

(* order.strict.trichotomy *)
Theorem trichotomy
  : forall (a : Bin) (b : Bin) . (a < b) \/ (a = b) \/ (b < a).
Proof.
  intros a b.
  let proof t := Nat.order.strict.trichotomy (to_nat &a) (to_nat &b).
  match &t with | lt | rest end.
  -
    ipso (disjoin (modus aequans (conversion.order &a &b), &lt), _).
  -
    match &rest with | same | gt end.
    +
      ipso (disjoin _, (disjoin (conversion.injectivity &same), _)).
    +
      ipso (disjoin _, (disjoin _, (modus aequans (conversion.order &b &a), &gt))).
Qed.

(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (b : Bin) . Accessible (<) b.
Proof.
  intro b.
  lemma descent
    : Descent.Step (Induced Nat.LessThan to_nat) (fun (x : Bin) . Accessible (<) x).
  {
    intros x recurse.
    ipso (Accessible_introduction
            (fun (y : Bin) (h : y < &x) .
               &recurse y (Induced.introduction (modus aequans (conversion.order y &x), h)))).
  }
  ipso (Accessible.recursion &descent &b
          (@accessibility _ _ (WellFounded.induced Nat.LessThan to_nat _) &b)).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (a : Bin) (b : Bin) .
      (compare a b = Comparison.Lt <-> a < b) /\ (compare a b = Comparison.Eq <-> a = b).
Proof.
  intros a b.
  leibniz (conversion.comparison &a &b) in |- *.
  let proof s := Nat.comparison.specification (to_nat &a) (to_nat &b).
  match &s with | strict equality end.
  divide et impera.
  -
    divide et impera.
    +
      intro c.
      ipso (modus aequans (conversion.order &a &b), (modus aequans &strict, &c)).
    +
      intro h.
      ipso (modus aequans &strict, (modus aequans (conversion.order &a &b), &h)).
  -
    divide et impera.
    +
      intro c.
      ipso (conversion.injectivity (modus aequans &equality, &c)).
    +
      intro e.
      ipso (modus aequans &equality, (congru to_nat, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (a : Bin) (b : Bin) . compare a b = Comparison.transpose (compare b a).
Proof.
  intros a b.
  leibniz (conversion.comparison &a &b), (conversion.comparison &b &a) in |- *.
  ipso (Nat.comparison.antisymmetry (to_nat &a) (to_nat &b)).
Qed.

Module maximum. (* comparison.maximum *)

(* comparison.maximum.identity *)
Theorem identity
  : forall (b : Bin) . (max One b = b) /\ (max b One = b).
Proof.
  intro b.
  divide et impera.
  -
    simpl Comparable.max in |- *.
    leibniz (conversion.comparison One &b) in |- *.
    simpl in |- *.
    match (to_nat &b) with | | n end |- e.
    +
      let proof e : to_nat &b = to_nat One := &e.
      ipso (symm (conversion.injectivity &e)).
    +
      quod idem est.
  -
    simpl Comparable.max in |- *.
    leibniz (conversion.comparison &b One) in |- *.
    simpl in |- *.
    match (to_nat &b) with | | n end.
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
Qed.

End maximum. (* comparison.maximum *)

End comparison. (* comparison *)

End Bin. (* Bin *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Bin], not [Bin.T].
 *)
Abbreviation Bin := Bin.T.

(* Makes the notations declared in [Module Bin] usable in every file that
 * imports this one, as [(a + b)%bin] or under an opened
 * [jwa_bin_scope]. Only the notations are exported: [add] and the laws
 * still need the [Bin.] prefix.
 *)
Export (notations) Bin.

Instance Bin_less_than_well_founded
  : WellFounded (<)%bin :=
  {| accessibility := Bin.order.strict.wellfoundedness |}.

Instance Bin_comparable
  : Comparable Bin.compare (<)%bin :=
  {| Comparable.transitivity  := @Bin.order.strict.transitivity
   ; Comparable.specification := Bin.comparison.specification
   ; Comparable.antisymmetry  := Bin.comparison.antisymmetry |}.

Instance Bin_add_semigroup
  : Semigroup Bin.add :=
  {| Semigroup.associativity := Bin.addition.associativity |}.

Instance Bin_add_cancellative
  : Cancellative Bin.add :=
  {| Cancellative.cancellation := Bin.addition.cancellation |}.

Instance Bin_mul_cancellative
  : Cancellative Bin.mul :=
  {| Cancellative.cancellation := Bin.multiplication.cancellation |}.

Instance Bin_mul_monoid
  : Monoid Bin.mul Bin.One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Bin.multiplication.associativity |}
   ; Monoid.identity := Bin.multiplication.identity |}.

Instance Bin_add_commutative
  : Commutative Bin.add :=
  {| Commutative.commutativity := Bin.addition.commutativity |}.

Instance Bin_mul_commutative
  : Commutative Bin.mul :=
  {| Commutative.commutativity := Bin.multiplication.commutativity |}.

Instance Bin_min_semigroup
  : Semigroup Bin.min :=
  {| Semigroup.associativity := Comparable.minimum.associativity |}.

Instance Bin_max_monoid
  : Monoid Bin.max Bin.One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.maximum.associativity |}
   ; Monoid.identity := Bin.comparison.maximum.identity |}.

Instance Bin_min_commutative
  : Commutative Bin.min :=
  {| Commutative.commutativity := Comparable.minimum.commutativity |}.

Instance Bin_max_commutative
  : Commutative Bin.max :=
  {| Commutative.commutativity := Comparable.maximum.commutativity |}.
