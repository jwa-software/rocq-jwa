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

Definition data_number_all_delivers_well_founded_magnitude
  : forall (x : Integer) .
      Accessible (Preimage Integer.abs NatWithZero.LessThan) x
  := fun (x : Integer) . accessibility x.
