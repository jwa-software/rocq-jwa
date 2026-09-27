(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [Binary.add]. The type
 * and its ctors are declared inside it, so no later file can rebind them.
 *)
Module Binary. (* Binary *)

(* A positive number in binary, its leading bit innermost: [One] is 1, and
 * [AppendZero] and [AppendOne] append a bit at the low end, so six, 110 in
 * binary, is [AppendZero (AppendOne One)]. The leading bit is always 1, so
 * every positive number has exactly one term; [NatWithZero]'s counterpart
 * [BinaryWithZero] adds zero on top.
 *)
Inductive T : Type :=
  | One        : T
  | AppendZero : T -> T
  | AppendOne  : T -> T.

(* The carrier is named [T] so that the type itself reads [Binary] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Binary].
 *)
Abbreviation Binary := T.

Definition induction
  : forall (P : Binary -> Prop) .
      P One ->
      (forall (b : Binary) . P b -> P (AppendZero b)) ->
      (forall (b : Binary) . P b -> P (AppendOne b)) ->
      forall (b : Binary) . P b
  := fun (P : Binary -> Prop)
         (one : P One)
         (append_zero : forall (b : Binary) . P b -> P (AppendZero b))
         (append_one : forall (b : Binary) . P b -> P (AppendOne b)) .
       fix go (b : Binary) : P b :=
         match b with
         | One           => one
         | AppendZero b' => append_zero b' (go b')
         | AppendOne b'  => append_one b' (go b')
         end.

(* [Binary -> Binary] *)
Fixpoint inc (b : Binary) : Binary :=
  match b with
  | One           => AppendZero One
  | AppendZero b' => AppendOne b'
  | AppendOne b'  => AppendZero (inc b')
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Binary] a client writes [(a + b)%binary]. [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "++ b" := (inc b) (only parsing)
  : jwa_binary_scope.

(* Bit by bit from the least significant end, the carry passed on: [a + b]
 * when [carry] is [false], [a + b + 1] when it is [true]. Each bit is read
 * once, so a sum costs as many steps as the longer operand has bits.
 *)
(* [Bool -> Binary -> Binary -> Binary] *)
Fixpoint add_with_carry (carry : Bool) (a : Binary) (b : Binary) : Binary :=
  match carry with
  | false =>
      match a, b with
      | One, One                     => AppendZero One
      | One, AppendZero b'           => AppendOne b'
      | One, AppendOne b'            => AppendZero (inc b')
      | AppendZero a', One           => AppendOne a'
      | AppendZero a', AppendZero b' => AppendZero (add_with_carry false a' b')
      | AppendZero a', AppendOne b'  => AppendOne (add_with_carry false a' b')
      | AppendOne a', One            => AppendZero (inc a')
      | AppendOne a', AppendZero b'  => AppendOne (add_with_carry false a' b')
      | AppendOne a', AppendOne b'   => AppendZero (add_with_carry true a' b')
      end
  | true =>
      match a, b with
      | One, One                     => AppendOne One
      | One, AppendZero b'           => AppendZero (inc b')
      | One, AppendOne b'            => AppendOne (inc b')
      | AppendZero a', One           => AppendZero (inc a')
      | AppendZero a', AppendZero b' => AppendOne (add_with_carry false a' b')
      | AppendZero a', AppendOne b'  => AppendZero (add_with_carry true a' b')
      | AppendOne a', One            => AppendOne (inc a')
      | AppendOne a', AppendZero b'  => AppendZero (add_with_carry true a' b')
      | AppendOne a', AppendOne b'   => AppendOne (add_with_carry true a' b')
      end
  end.

(* [Binary -> Binary -> Binary] *)
Definition add := fun (a : Binary) (b : Binary) . add_with_carry false a b.

Notation "a + b" := (add a b) (only parsing)
  : jwa_binary_scope.

(* Shift and add: [2a * b] is [a * b] shifted, [(2a + 1) * b] adds [b]. *)
(* [Binary -> Binary -> Binary] *)
Fixpoint mul (a : Binary) (b : Binary) : Binary :=
  match a with
  | One           => b
  | AppendZero a' => AppendZero (mul a' b)
  | AppendOne a'  => add b (AppendZero (mul a' b))
  end.

Notation "a * b" := (mul a b) (only parsing)
  : jwa_binary_scope.

Local Open Scope jwa_binary_scope.

(* [Binary -> Binary] *)
Definition square := fun (b : Binary) . b * b.

(* Squaring once per bit of the exponent: [a ^ 2n] squares [a ^ n] instead
 * of computing it twice, so a power costs as many steps as [n] has bits.
 *)
(* [Binary -> Binary -> Binary] *)
Fixpoint power (a : Binary) (n : Binary) : Binary :=
  match n with
  | One           => a
  | AppendZero n' => square (power a n')
  | AppendOne n'  => a * square (power a n')
  end.

Notation "a ^ n" := (power a n) (only parsing)
  : jwa_binary_scope.

(* The outcome of [a - b] where only positives exist: below zero, zero, or
 * the positive difference.
 *)
Inductive Difference : Type :=
  | Below : Difference
  | Equal : Difference
  | Above : Binary -> Difference.

(* [2d] for a difference [d]. *)
(* [Difference -> Difference] *)
Definition append_zero_difference := fun (d : Difference) .
  match d with
  | Below   => Below
  | Equal   => Equal
  | Above p => Above (AppendZero p)
  end.

(* [2d + 1]: from zero it reaches one. *)
(* [Difference -> Difference] *)
Definition append_one_difference := fun (d : Difference) .
  match d with
  | Below   => Below
  | Equal   => Above One
  | Above p => Above (AppendOne p)
  end.

(* Bit by bit from the least significant end, the borrow passed on as
 * [add_with_carry] passes its carry: [a - b] when [borrow] is [false],
 * [a - b - 1] when it is [true].
 *)
(* [Bool -> Binary -> Binary -> Difference] *)
Fixpoint difference_with_borrow (borrow : Bool) (a : Binary) (b : Binary) : Difference :=
  match borrow with
  | false =>
      match a, b with
      | One, One                     => Equal
      | One, AppendZero _            => Below
      | One, AppendOne _             => Below
      | AppendZero a', One           => append_one_difference (difference_with_borrow false a' One)
      | AppendZero a', AppendZero b' => append_zero_difference (difference_with_borrow false a' b')
      | AppendZero a', AppendOne b'  => append_one_difference (difference_with_borrow true a' b')
      | AppendOne a', One            => Above (AppendZero a')
      | AppendOne a', AppendZero b'  => append_one_difference (difference_with_borrow false a' b')
      | AppendOne a', AppendOne b'   => append_zero_difference (difference_with_borrow false a' b')
      end
  | true =>
      match a, b with
      | One, One                     => Below
      | One, AppendZero _            => Below
      | One, AppendOne _             => Below
      | AppendZero a', One           => append_zero_difference (difference_with_borrow false a' One)
      | AppendZero a', AppendZero b' => append_one_difference (difference_with_borrow true a' b')
      | AppendZero a', AppendOne b'  => append_zero_difference (difference_with_borrow true a' b')
      | AppendOne a', One            => append_one_difference (difference_with_borrow false a' One)
      | AppendOne a', AppendZero b'  => append_zero_difference (difference_with_borrow false a' b')
      | AppendOne a', AppendOne b'   => append_one_difference (difference_with_borrow true a' b')
      end
  end.

(* [Binary -> Binary -> Difference] *)
Definition difference := fun (a : Binary) (b : Binary) . difference_with_borrow false a b.

(* [Binary -> Binary -> Comparison] *)
Definition compare := fun (a : Binary) (b : Binary) .
  match difference a b with
  | Below   => Comparison.Lt
  | Equal   => Comparison.Eq
  | Above _ => Comparison.Gt
  end.

(* [a - b], [None] unless it is positive, as [Nat.sub] is. *)
(* [Binary -> Binary -> Option Binary] *)
Definition sub := fun (a : Binary) (b : Binary) .
  match difference a b with
  | Above p => Some p
  | _       => None
  end.

(* [One] where [sub] has nothing, as [Nat.saturating_sub] does. *)
(* [Binary -> Binary -> Binary] *)
Definition saturating_sub := fun (a : Binary) (b : Binary) .
  match sub a b with
  | Some k => k
  | None   => One
  end.

(* The conversions to and from [Nat], used to state the laws: [to_nat] is
 * unary, so it is for proofs, not for computing.
 *)
(* [Binary -> Nat] *)
Fixpoint to_nat (b : Binary) : Nat :=
  match b with
  | One           => Nat.One
  | AppendZero b' => (to_nat b' + to_nat b')%nat
  | AppendOne b'  => Nat.Successor (to_nat b' + to_nat b')%nat
  end.

(* [Nat -> Binary] *)
Fixpoint from_nat (n : Nat) : Binary :=
  match n with
  | Nat.One          => One
  | Nat.Successor n' => ++ from_nat n'
  end.

Module conversion. (* conversion *)

(* conversion.successor *)
Theorem successor
  : forall (b : Binary) . to_nat (++ b) = Nat.Successor (to_nat b).
Proof.
  intro b.
  match b with | | b' by IH | b' by IH end per Binary.induction.
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
  : forall (n : Nat) . from_nat (n + n)%nat = AppendZero (from_nat n).
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
  : forall (b : Binary) . from_nat (to_nat b) = b.
Proof.
  intro b.
  match b with | | b' by IH | b' by IH end per Binary.induction.
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
  : forall (a : Binary) (b : Binary) (carry : Bool) .
      to_nat (add_with_carry carry a b)
      = match carry with
        | true  => Nat.Successor (to_nat a + to_nat b)%nat
        | false => (to_nat a + to_nat b)%nat
        end.
Proof.
  intro a.
  match a with | | a' by IH | a' by IH end per Binary.induction.
  -
    intros b carry.
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
    intros b carry.
    match b with | | b' | b' end.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%nat Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%nat Nat.One) in |- *.
        simpl in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%nat
          := &IH &b' false.
        leibniz &e in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%nat
          := &IH &b' false.
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
            = Nat.Successor (to_nat &a' + to_nat &b')%nat
          := &IH &b' true.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%nat
                                              (to_nat &a' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%nat
                                              (to_nat &b' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%nat
          := &IH &b' false.
        leibniz &e in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%nat
                                              (to_nat &b' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
  -
    intros b carry.
    match b with | | b' | b' end.
    +
      match carry with | | end.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%nat Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
      *
        simpl in |- *.
        leibniz (conversion.successor &a') in |- *.
        leibniz (Nat.addition.commutativity (to_nat &a' + to_nat &a')%nat Nat.One) in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a') (to_nat &a')) in |- *.
        quod idem est.
    +
      match carry with | | end.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%nat
          := &IH &b' true.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%nat
                                              (to_nat &a' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry false &a' &b') = (to_nat &a' + to_nat &b')%nat
          := &IH &b' false.
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
            = Nat.Successor (to_nat &a' + to_nat &b')%nat
          := &IH &b' true.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%nat
                                              (to_nat &a' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%nat
                                              (to_nat &b' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
      *
        simpl in |- *.
        let proof e
          : to_nat (add_with_carry true &a' &b')
            = Nat.Successor (to_nat &a' + to_nat &b')%nat
          := &IH &b' true.
        leibniz &e in |- *.
        simpl in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &b')%nat
                                              (to_nat &a' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.right.successor (to_nat &a' + to_nat &a')%nat
                                              (to_nat &b' + to_nat &b')%nat) in |- *.
        leibniz (Nat.addition.interchange (to_nat &a') (to_nat &a') (to_nat &b') (to_nat &b'))
          in |- *.
        quod idem est.
Qed.

(* conversion.addition *)
Theorem addition
  : forall (a : Binary) (b : Binary) . to_nat (a + b) = (to_nat a + to_nat b)%nat.
Proof.
  intros a b.
  simpl add in |- *.
  ipso (conversion.carry &a &b false).
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (a : Binary) (b : Binary) . to_nat (a * b) = (to_nat a * to_nat b)%nat.
Proof.
  intros a b.
  match a with | | a' by IH | a' by IH end per Binary.induction.
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
    let proof e := conversion.addition &b (AppendZero (mul &a' &b)).
    simpl in &e |- *.
    leibniz &e in |- *.
    leibniz &IH in |- *.
    leibniz (Nat.multiplication.right.distributivity.over.addition
               (to_nat &b) (to_nat &a') (to_nat &a')) in |- *.
    quod idem est.
Qed.

(* conversion.power *)
Theorem power
  : forall (a : Binary) (n : Binary) . to_nat (a ^ n) = (to_nat a ^ to_nat n)%nat.
Proof.
  intros a n.
  match n with | | n' by IH | n' by IH end per Binary.induction.
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
      | Below   => (m < n)%nat
      | Equal   => m = n
      | Above p => (n + to_nat p)%nat = m
      end ->
      match append_zero_difference d with
      | Below   => (m + m < n + n)%nat
      | Equal   => (m + m)%nat = (n + n)%nat
      | Above p => (n + n + to_nat p)%nat = (m + m)%nat
      end.
Proof.
  intros d m n.
  match d with | | | p end.
  -
    intro h.
    simpl in |- *.
    simpl Nat.LessThan in &h |- *.
    match &h with | k e end.
    exists (&k + &k)%nat.
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
      | Below   => (m < n)%nat
      | Equal   => m = n
      | Above p => (n + to_nat p)%nat = m
      end ->
      match append_one_difference d with
      | Below   => (Nat.Successor (m + m) < n + n)%nat
      | Equal   => Nat.Successor (m + m)%nat = (n + n)%nat
      | Above p => (n + n + to_nat p)%nat = Nat.Successor (m + m)%nat
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
      leibniz (Nat.addition.right.successor (&m + &m)%nat Nat.One) in |- *.
      quod idem est.
    +
      exists (&k' + Nat.Successor &k')%nat.
      simpl in |- *.
      leibniz <- &e in |- *.
      leibniz (Nat.addition.interchange &m (Nat.Successor &k') &m (Nat.Successor &k')) in |- *.
      simpl in |- *.
      leibniz (Nat.addition.right.successor (&m + &m)%nat (&k' + Nat.Successor &k')%nat)
        in |- *.
      quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz &h in |- *.
    leibniz (Nat.addition.commutativity (&n + &n)%nat Nat.One) in |- *.
    simpl in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    leibniz (Nat.addition.right.successor (&n + &n)%nat (to_nat &p + to_nat &p)%nat) in |- *.
    leibniz <- &h in |- *.
    leibniz (Nat.addition.interchange &n (to_nat &p) &n (to_nat &p)) in |- *.
    quod idem est.
Qed.

End doubling. (* conversion.difference.doubling *)

(* conversion.difference.cancellation *)
Lemma cancellation
  : forall (d : Difference) (m : Nat) (n : Nat) .
      match d with
      | Below   => (Nat.Successor m < Nat.Successor n)%nat
      | Equal   => Nat.Successor m = Nat.Successor n
      | Above p => (Nat.Successor n + to_nat p)%nat = Nat.Successor m
      end
      <->
      match d with
      | Below   => (m < n)%nat
      | Equal   => m = n
      | Above p => (n + to_nat p)%nat = m
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
  : forall (a : Binary) (b : Binary) (borrow : Bool) .
      match borrow with
      | true  =>
          match difference_with_borrow true a b with
          | Below   => (to_nat a < Nat.Successor (to_nat b))%nat
          | Equal   => to_nat a = Nat.Successor (to_nat b)
          | Above p => (Nat.Successor (to_nat b) + to_nat p)%nat = to_nat a
          end
      | false =>
          match difference_with_borrow false a b with
          | Below   => (to_nat a < to_nat b)%nat
          | Equal   => to_nat a = to_nat b
          | Above p => (to_nat b + to_nat p)%nat = to_nat a
          end
      end.
Proof.
  intro a.
  match a with | | a' by IH | a' by IH end per Binary.induction.
  -
    intros b borrow.
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
        exists (to_nat &b' + to_nat &b')%nat.
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
          exists (&k + Nat.Successor &k)%nat.
          simpl in |- *.
          quod idem est.
    +
      match borrow with | | end.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists (Nat.Successor (to_nat &b' + to_nat &b')%nat).
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl Nat.LessThan in |- *.
        exists (to_nat &b' + to_nat &b')%nat.
        simpl in |- *.
        quod idem est.
  -
    intros b borrow.
    match b with | | b' | b' end.
    +
      match borrow with | | end.
      *
        ipso (conversion.difference.doubling
                (difference_with_borrow false &a' One) (to_nat &a') Nat.One (&IH One false)).
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow false &a' One) (to_nat &a') Nat.One
                         (&IH One false).
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow false &a' One))
                   (to_nat &a' + to_nat &a')%nat Nat.One),
                &h).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH &b' true).
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow true &a' &b'))
                   (to_nat &a' + to_nat &a')%nat
                   (Nat.Successor (to_nat &b' + to_nat &b')%nat)),
                &h).
      *
        ipso (conversion.difference.doubling
                (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                (&IH &b' false)).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH &b' true).
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso &h.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH &b' true).
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_one_difference (difference_with_borrow true &a' &b'))
                   (to_nat &a' + to_nat &a')%nat
                   (Nat.Successor (to_nat &b' + to_nat &b')%nat)),
                &h).
  -
    intros b borrow.
    match b with | | b' | b' end.
    +
      match borrow with | | end.
      *
        ipso (conversion.difference.doubling.successor
                (difference_with_borrow false &a' One) (to_nat &a') Nat.One (&IH One false)).
      *
        simpl in |- *.
        quod idem est.
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                         (&IH &b' false).
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_zero_difference (difference_with_borrow false &a' &b'))
                   (to_nat &a' + to_nat &a')%nat (to_nat &b' + to_nat &b')%nat),
                &h).
      *
        ipso (conversion.difference.doubling.successor
                (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                (&IH &b' false)).
    +
      match borrow with | | end.
      *
        let proof h := conversion.difference.doubling.successor
                         (difference_with_borrow true &a' &b') (to_nat &a')
                         (Nat.Successor (to_nat &b')) (&IH &b' true).
        leibniz (Nat.addition.successor (to_nat &b') (to_nat &b')) in &h.
        ipso &h.
      *
        let proof h := conversion.difference.doubling
                         (difference_with_borrow false &a' &b') (to_nat &a') (to_nat &b')
                         (&IH &b' false).
        ipso (modus aequans
                (conversion.difference.cancellation
                   (append_zero_difference (difference_with_borrow false &a' &b'))
                   (to_nat &a' + to_nat &a')%nat (to_nat &b' + to_nat &b')%nat),
                &h).
Qed.

(* What each outcome of [difference] says of the two numbers. *)
(* conversion.difference *)
Lemma difference
  : forall (a : Binary) (b : Binary) .
      match Binary.difference a b with
      | Below   => (to_nat a < to_nat b)%nat
      | Equal   => to_nat a = to_nat b
      | Above p => (to_nat b + to_nat p)%nat = to_nat a
      end.
Proof.
  intros a b.
  ipso (conversion.borrow &a &b false).
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (a : Binary) (b : Binary) .
      compare a b = Nat.compare (to_nat a) (to_nat b).
Proof.
  intros a b.
  simpl compare in |- *.
  let proof h := conversion.difference &a &b.
  extro &h.
  match (Binary.difference &a &b) with | | | p end.
  -
    intro h.
    ipso (symm (Nat.comparison.strict.backward.specification &h)).
  -
    intro h.
    ipso (symm (Nat.comparison.equality.backward.specification &h)).
  -
    intro h.
    lemma below : (to_nat &b < to_nat &a)%nat.
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
  : forall (a : Binary) (b : Binary) .
      Option.map to_nat (sub a b) = Nat.sub (to_nat a) (to_nat b).
Proof.
  intros a b.
  simpl sub in |- *.
  let proof h := conversion.difference &a &b.
  extro &h.
  match (Binary.difference &a &b) with | | | p end.
  -
    intro h.
    simpl in |- *.
    let proof le : (to_nat &a <= to_nat &b)%nat := disjoin _, &h.
    leibniz (Nat.subtraction.truncation &le) in |- *.
    quod idem est.
  -
    intro h.
    simpl in |- *.
    let proof le : (to_nat &a <= to_nat &b)%nat := disjoin &h, _.
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
  : forall (a : Binary) (b : Binary) .
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

End conversion. (* conversion *)

End Binary. (* Binary *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Binary], not [Binary.T].
 *)
Abbreviation Binary := Binary.T.

(* Makes the notations declared in [Module Binary] usable in every file that
 * imports this one, as [(a + b)%binary] or under an opened
 * [jwa_binary_scope]. Only the notations are exported: [add] and the laws
 * still need the [Binary.] prefix.
 *)
Export (notations) Binary.
