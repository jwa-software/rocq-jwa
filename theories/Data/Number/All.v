(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Number]: re-exports the seven number types, so a
 * client imports them with [From jwa Require Import Data.Number.All]. The
 * three binary ones arrive through their own group umbrella.
 *)

From jwa Require Export Core.All.

From jwa Require Export Data.Number.Binary.All.
From jwa Require Export Data.Number.Integer.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.NatWithZero.
From jwa Require Export Data.Number.Rational.
From jwa Require Export Data.Option.
