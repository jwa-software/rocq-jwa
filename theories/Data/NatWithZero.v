(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]; [Data.Nat] is the type [Positive] wraps. *)
From jwa Require Import Core.All.
From jwa Require Import Data.Nat.

(* [Positive] wraps a [Nat], so an operation here reduces to the [Nat] one
   plus the [Zero] cases. *)
Inductive NatWithZero : Type :=
  | Zero     : NatWithZero
  | Positive : Nat -> NatWithZero.
