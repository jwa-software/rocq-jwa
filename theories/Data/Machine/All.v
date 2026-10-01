(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Machine]: re-exports the machine units, so a client
 * imports them with [From jwa Require Import Data.Machine.All].
 *
 * A machine unit is a value of fixed width, the shape a machine stores and
 * moves. [Bit] is one binary digit, [Byte] eight.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Bool] for
 * [Bit.from_bool] and [Bit.to_bool], [Nat] and [Nat0] for the counts of the
 * shifts and rotations and for the values, [Product] for the carry and the
 * borrow, [Comparison] for [Byte.compare], [Numeral] and [Option] for the
 * literals.
 *)
From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Base.Comparison.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.Nat0.
From jwa Require Export Data.Number.Numeral.
From jwa Require Export Data.Option.
From jwa Require Export Data.Product.

From jwa Require Export Data.Machine.Bit.
From jwa Require Export Data.Machine.Byte.
