(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Bin.
From jwa Require Import Data.Number.BinWithZero.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Option.

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

End BinWithSign. (* BinWithSign *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinWithSign], not [BinWithSign.T]. [Zero] and [Positive] name ctors of
 * three other number types, so all four write theirs with the prefix.
 *)
Abbreviation BinWithSign := BinWithSign.T.
