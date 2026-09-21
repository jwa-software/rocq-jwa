(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Number.All.
From jwa Require Import Relation.Accessible.
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

Definition data_number_all_delivers_gcd_common
  : forall (b : NatWithZero) (a : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := NatWithZero.gcd.common.

Definition data_number_all_delivers_gcd_projections
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.Divides (NatWithZero.gcd a b) a
      /\ NatWithZero.Divides (NatWithZero.gcd a b) b
  := fun (a : NatWithZero) (b : NatWithZero) .
       Conjunction_introduction (NatWithZero.gcd.left a b) (NatWithZero.gcd.right a b).

Definition data_number_all_delivers_gcd_greatest
  : forall (b : NatWithZero) (a : NatWithZero) (d : NatWithZero) .
      NatWithZero.Divides d a ->
      NatWithZero.Divides d b -> NatWithZero.Divides d (NatWithZero.gcd a b)
  := NatWithZero.gcd.greatest.

Definition data_number_all_delivers_well_founded_magnitude
  : forall (x : Integer) .
      Accessible (Preimage Integer.abs NatWithZero.LessThan) x
  := fun (x : Integer) . accessibility x.
