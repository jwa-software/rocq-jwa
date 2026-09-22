(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Tactics.Simplify.

Module Rational. (* Rational *)

(* A fraction, an [Integer] over a [Nat]: the denominator is never zero by
 * its type. The ctor stays behind this module; [make] is the way in, and
 * what it builds is in lowest terms.
 *)
Inductive T : Type :=
  | Rational_introduction : Integer -> Nat -> T.

Abbreviation Rational := T.

(* [Rational -> Integer] *)
Definition numerator := fun (x : Rational) .
  match x with
  | Rational_introduction n _ => n
  end.

(* [Rational -> Nat] *)
Definition denominator := fun (x : Rational) .
  match x with
  | Rational_introduction _ d => d
  end.

(* [Integer -> Nat -> Rational] *)
Definition make := fun (n : Integer) (d : Nat) .
  let g := NatWithZero.gcd.nat (Integer.abs n) d in
  Rational_introduction
    (Integer.divide n g)
    (NatWithZero.divide.nat.safe d g
       (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)).

Module make. (* make *)

Local Open Scope jwa_integer_scope.

(* make.invariance *)
Theorem invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      make ((Integer.Positive k) * n) (Nat.mul k d) = make n d.
Proof.
  intros n d k.

  assert (common
          : NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d)
          = Nat.mul k (NatWithZero.gcd.nat (| n |) d)).
  {
    pose proof (Integer.multiplication.magnitude (Integer.Positive k) n) as am.
    change (| Integer.Positive k |) with (NatWithZero.Positive k) in am.
    rewrite am in |- *.
    pose proof (NatWithZero.gcd.nat.left.distributivity.of.multiplication k d (| n |))
            as gd.
    symmetry in gd.
    exact gd.
  }

  simplify make in |- *.

  assert (top
          : ((Integer.Positive k) * n) /. (NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d))
          = n /. (NatWithZero.gcd.nat (| n |) d)).
  {
    rewrite common in |- *.
    exact (Integer.division.invariance n (NatWithZero.gcd.nat (| n |) d) k).
  }

  assert (bottom
          : NatWithZero.divide.nat.safe
                (Nat.mul k d)
                (NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d))
                (NatWithZero.gcd.nat.right.divisibility (| (Integer.Positive k) * n |) (Nat.mul k d))
          = NatWithZero.divide.nat.safe
                d
                (NatWithZero.gcd.nat (| n |) d)
                (NatWithZero.gcd.nat.right.divisibility (| n |) d)).
  {
    apply NatWithZero.divide.nat.safe.congruence.
    rewrite common in |- *.
    pose proof (NatWithZero.division.invariance
                  (NatWithZero.Positive d)
                  (NatWithZero.gcd.nat (| n |) d) k)
            as inv.
    change (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive d))
      with (NatWithZero.Positive (Nat.mul k d))
        in inv.
    exact inv.
  }

  rewrite top    in |- *.
  rewrite bottom in |- *.
  reflexivity.
Qed.

Local Close Scope jwa_integer_scope.

End make. (* make *)

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.
