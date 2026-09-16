(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires. *)
From jwa Require Import Core.All.

(* Zero is not a [Nat]; [One] is the smallest. [Data.NatWithZero] is the type
   that has it. *)
Inductive Nat : Type :=
  | One       : Nat
  | Successor : Nat -> Nat.
