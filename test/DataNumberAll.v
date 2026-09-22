(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Number.All.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.WellFounded.

Definition data_number_all_delivers
  : Nat -> NatWithZero -> Integer -> ~ Falsum -> Verum
  := fun (_ : Nat) (_ : NatWithZero) (_ : Integer) (_ : ~ Falsum) . I.

Definition data_number_all_delivers_operations
  : Integer
  := (Integer.Zero + Integer.Negative Nat.One * Integer.Positive Nat.One)%integer.

Definition data_number_all_delivers_well_founded
  : forall (m : Nat) (n : NatWithZero) (x : Integer) .
      Accessible Nat.LessThan m
  := fun (m : Nat) (n : NatWithZero) (x : Integer) . accessibility m.

Definition data_number_all_delivers_well_founded_with_zero
  : forall (n : NatWithZero) . Accessible NatWithZero.LessThan n
  := fun (n : NatWithZero) . accessibility n.

Definition data_number_all_delivers_gcd_zero
  : forall (a : NatWithZero) . NatWithZero.gcd a NatWithZero.Zero = a
  := NatWithZero.gcd.zero.

Definition data_number_all_delivers_gcd_recurrence
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.gcd a (NatWithZero.Positive q)
      = NatWithZero.gcd (NatWithZero.Positive q) (NatWithZero.modulo a q)
  := NatWithZero.gcd.recurrence.

Definition data_number_all_delivers_gcd_divisibility
  : forall (b : NatWithZero) (a : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := NatWithZero.gcd.divisibility.

Definition data_number_all_delivers_gcd_left_right_divisibility
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := fun (a : NatWithZero) (b : NatWithZero) .
       Conjunction_introduction
         (NatWithZero.gcd.left.divisibility a b) (NatWithZero.gcd.right.divisibility a b).

Definition data_number_all_delivers_gcd_universality
  : forall (b : NatWithZero) (a : NatWithZero) (d : NatWithZero) .
      NatWithZero.Divides d a ->
      NatWithZero.Divides d b -> NatWithZero.Divides d (NatWithZero.gcd a b)
  := NatWithZero.gcd.universality.

Definition data_number_all_delivers_gcd_nat
  : forall (q : Nat) (a : NatWithZero) .
      NatWithZero.gcd a (NatWithZero.Positive q)
      = NatWithZero.Positive (NatWithZero.gcd.nat a q)
  := NatWithZero.gcd.nat.specification.

Definition data_number_all_delivers_integer_divide
  : forall (x : Integer) (d : Nat) .
      Integer.abs (Integer.divide x d) = NatWithZero.divide (Integer.abs x) d
  := Integer.division.magnitude.

Definition data_number_all_delivers_well_founded_magnitude
  : forall (x : Integer) .
      Accessible (Induced NatWithZero.LessThan Integer.abs) x
  := fun (x : Integer) . accessibility x.

Definition data_number_all_delivers_divide_nat_safe
  : forall (d : Nat) (g : Nat)
      (h : NatWithZero.Divides (NatWithZero.Positive g) (NatWithZero.Positive d)) .
      NatWithZero.Positive (NatWithZero.divide.nat.safe d g h)
      = NatWithZero.divide (NatWithZero.Positive d) g
  := NatWithZero.divide.nat.safe.specification.

Definition data_number_all_delivers_gcd_nat_left_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides (NatWithZero.Positive (NatWithZero.gcd.nat a q)) a
  := NatWithZero.gcd.nat.left.divisibility.

Definition data_number_all_delivers_gcd_nat_right_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides
        (NatWithZero.Positive (NatWithZero.gcd.nat a q)) (NatWithZero.Positive q)
  := NatWithZero.gcd.nat.right.divisibility.

Definition data_number_all_delivers_gcd_nat_divisibility
  : forall (a : NatWithZero) (q : Nat) .
      NatWithZero.Divides (NatWithZero.Positive (NatWithZero.gcd.nat a q)) a
      /\ NatWithZero.Divides
           (NatWithZero.Positive (NatWithZero.gcd.nat a q)) (NatWithZero.Positive q)
  := NatWithZero.gcd.nat.divisibility.

Definition data_number_all_delivers_rational_numerator
  : Rational -> Integer
  := Rational.numerator.

Definition data_number_all_delivers_rational_denominator
  : Rational -> Nat
  := Rational.denominator.

Definition data_number_all_delivers_rational_make
  : Integer -> Nat -> Rational
  := Rational.make.
