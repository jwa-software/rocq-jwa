(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.

Module Rational. (* Rational *)

(* A fraction, an [Integer] over a [Nat]: the denominator is never zero by
 * its type. The ctor stays behind this module; [make] is the way in, and
 * what it builds is in lowest terms.
 *)
Inductive T : Type :=
  | Fraction : Integer -> Nat -> T.

Abbreviation Rational := T.

(* [Rational -> Integer] *)
Definition numerator := fun (x : Rational) .
  match x with
  | Fraction n _ => n
  end.

(* [Rational -> Nat] *)
Definition denominator := fun (x : Rational) .
  match x with
  | Fraction _ d => d
  end.

(* [Integer -> Nat -> Rational] *)
Definition make := fun (n : Integer) (d : Nat) .
  let g := NatWithZero.gcd.nat (Integer.abs n) d in
  Fraction
    (Integer.divide n g)
    (NatWithZero.divide.nat.safe d g
       (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)).

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.
