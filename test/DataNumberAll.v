(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Number.All.

Definition data_number_all_delivers
  : Nat -> NatWithZero -> Integer -> ~ Falsum -> Verum
  := fun (_ : Nat) (_ : NatWithZero) (_ : Integer) (_ : ~ Falsum) . I.

Definition data_number_all_delivers_operations
  : Integer
  := (Integer.Zero + Negative One * Integer.Positive One)%integer.
