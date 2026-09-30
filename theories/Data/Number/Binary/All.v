(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Number.Binary]: re-exports the three binary number
 * types, so a client imports them with
 * [From jwa Require Import Data.Number.Binary.All].
 *
 * A binary number carries its digits, where the unary types carry their value
 * in units, so an operation costs a step per digit rather than per unit.
 * [Bin] is the positives, [BinWithZero] adds zero, [BinWithSign] adds a sign.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name, so that a
 * client can write down what they take and return: [Comparison] for
 * [compare], [Bool] for [eq] and [append_bit], [Option] for [sub] and the
 * narrowings, [Nat], [Nat0] and [Integer] for the conversions, the
 * shift counts and the bit indices, [Numeral] for the literals, [Product]
 * for [div], and [Accessible], [Induced] and [WellFounded] for the descent
 * theorems and the instances.
 *)
From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Base.Comparison.
From jwa Require Export Data.Number.Integer.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.Nat0.
From jwa Require Export Data.Number.Numeral.
From jwa Require Export Data.Option.
From jwa Require Export Data.Product.
From jwa Require Export Relation.Accessible.
From jwa Require Export Relation.Induced.
From jwa Require Export Relation.WellFounded.

From jwa Require Export Data.Number.Binary.Bin.
From jwa Require Export Data.Number.Binary.BinWithSign.
From jwa Require Export Data.Number.Binary.BinWithZero.
