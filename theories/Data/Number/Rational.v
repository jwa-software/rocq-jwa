(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Tactics.Simplify.

Module Rational. (* Rational *)

(* A fraction, an [Integer] over a [Nat]: the denominator is never zero by
 * its type. The ctor stays behind this module; [make] is the way in, and
 * what it builds is in lowest terms.
 *)
Inductive T : Type :=
  | Rational_introduction : Integer -> Nat -> T.

Abbreviation Rational := T.

(* [Integer -> Nat -> Rational] *)
Definition make := fun (n : Integer) (d : Nat) .
  let n' := Integer.abs n in
  let g  := NatWithZero.gcd.nat n' d in
  let numerator := Integer.divide n g in
  let denominator := NatWithZero.divide.nat.safe d g (NatWithZero.gcd.nat.right.divisibility n' d) in
  Rational_introduction numerator denominator.

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

(* [Rational -> Rational] *)
Definition negate := fun (x : Rational) .
  let n := Integer.negate (numerator x) in
  let d := denominator x in
  make n d.

(* [Rational -> Rational -> Rational] *)
Definition add := fun (x : Rational) (y : Rational) .
  let nx := numerator x in
  let ny := numerator y in
  let dx := denominator x in
  let dy := denominator y in
  let dx' := Integer.from_nat dx in
  let dy' := Integer.from_nat dy in
  let n := Integer.add (Integer.mul nx dy') (Integer.mul ny dx') in
  let d := Nat.mul dx dy in
  make n d.

(* [Rational -> Rational -> Rational] *)
Definition sub := fun (x : Rational) (y : Rational) . let y := negate y in add x y.

(* [Rational -> Rational -> Rational] *)
Definition mul := fun (x : Rational) (y : Rational) .
  let n := Integer.mul (numerator x) (numerator y)
  in
  let d := Nat.mul (denominator x) ( denominator y)
  in
  make n d.

(* x/y -> y/x *)
(* [Rational -> Option Rational] *)
Definition inverse := fun (x : Rational) .
  let n := numerator   x in
  let d := denominator x in
  match n with
  | Integer.Negative n => let d := Integer.Negative d in Some (make d n)
  | Integer.Zero       => None
  | Integer.Positive n => let d := Integer.Positive d in Some (make d n)
  end.

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

(* make.proportionality *)
Theorem proportionality
  : forall (a : Integer) (b : Nat) .
      (numerator (make a b)) * (Integer.from_nat b)
      = a * (Integer.from_nat (denominator (make a b))).
Proof.
  intros a b.
  simplify make in |- *.
  simplify numerator, denominator in |- *.

  assert (bottom
          : Nat.mul
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (| a |) b)
                (NatWithZero.gcd.nat.right.divisibility (| a |) b))
              (NatWithZero.gcd.nat (| a |) b)
          = b).
  {
    pose proof (NatWithZero.divide.nat.safe.specification
                  b (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)) as s.
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive b) (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)) as e.
    symmetry in s.
    rewrite s in e.
    exact (NatWithZero.positive.injectivity e).
  }

  assert (lifted
          : Integer.from_nat b
          = (Integer.from_nat
              (NatWithZero.divide.nat.safe
                  b (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)))
            * (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))).
  {
    pose proof (Identity.congruence Integer.from_nat bottom) as c.
    symmetry in c.
    rewrite c in |- *.
    reflexivity.
  }

  assert (whole
          : (a /. (NatWithZero.gcd.nat (| a |) b)) * (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))
          = a).
  {
    exact (Integer.division.exactness
            a (NatWithZero.gcd.nat (| a |) b)
            (NatWithZero.gcd.nat.left.divisibility (| a |) b)).
  }

  rewrite lifted in |- *.
  rewrite (Integer.multiplication.commutativity
            (Integer.from_nat
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (| a |) b)
                (NatWithZero.gcd.nat.right.divisibility (| a |) b)))
            (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))) in |- *.
  pose proof (Identity.symmetry
                (Integer.multiplication.associativity
                  (a /. (NatWithZero.gcd.nat (| a |) b))
                  (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))
                  (Integer.from_nat
                    (NatWithZero.divide.nat.safe
                      b (NatWithZero.gcd.nat (| a |) b)
                      (NatWithZero.gcd.nat.right.divisibility (| a |) b)))))
          as assoc.
  rewrite assoc in |- *.
  rewrite whole in |- *.
  reflexivity.
Qed.

(* make.irreducibility *)
Theorem irreducibility
  : forall (a : Integer) (b : Nat) .
      NatWithZero.gcd.nat
        (| numerator (make a b) |)
        (denominator (make a b))
      = Nat.One.
Proof.
  intros a b.
  simplify make in |- *.
  simplify numerator, denominator in |- *.
  rewrite (Integer.division.magnitude a (NatWithZero.gcd.nat (| a |) b)) in |- *.
  exact (NatWithZero.gcd.nat.exhaustiveness (| a |) b).
Qed.

Local Close Scope jwa_integer_scope.

End make. (* make *)

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.
