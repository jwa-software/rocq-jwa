(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Machine]: re-exports the machine units, so a client
 * imports them with [From jwa Require Import Data.Machine.All].
 *
 * A machine unit is a value of fixed width, the shape a machine stores and
 * moves. [Bit] is one binary digit, [Byte] eight, [HWord] sixteen, [Word]
 * thirty-two, [DWord] sixty-four, [QWord] a hundred and twenty-eight, [UInt8]
 * a [Byte] read as a number from 0 to 255, and [Int8] a [Byte] read in two's
 * complement, from -128 to 127.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Bool] for
 * [Bit.from_bool] and [Bit.to_bool], [Nat] and [Nat0] for the counts of the
 * shifts and rotations and for the values, [Integer] for the signed values,
 * [Product] for the carry, the borrow and the overflow, [Comparison] for
 * [compare], [Numeral] and [Option] for the literals, [List] for the bytes
 * of a word, [Endian] for the order they are laid out in.
 *)
From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Base.Comparison.
From jwa Require Export Data.Collection.List.
From jwa Require Export Data.Number.Integer.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.Nat0.
From jwa Require Export Data.Number.Numeral.
From jwa Require Export Data.Option.
From jwa Require Export Data.Product.

From jwa Require Export Data.Machine.Bit.
From jwa Require Export Data.Machine.Byte.
From jwa Require Export Data.Machine.DWord.
From jwa Require Export Data.Machine.Endian.
From jwa Require Export Data.Machine.HWord.
From jwa Require Export Data.Machine.Int8.
From jwa Require Export Data.Machine.QWord.
From jwa Require Export Data.Machine.UInt8.
From jwa Require Export Data.Machine.Word.
