(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Collection]: re-exports every collection type and
 * every interface they answer to, so a client imports them with
 * [From jwa Require Import Data.Collection.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [NatWithZero]
 * for the index [nth], [take] and [drop] count with, [Option] for what [nth]
 * returns, [Nat] for [NonEmptyList]'s length, and [Bool] for the deciders.
 *)
From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.NatWithZero.
From jwa Require Export Data.Option.

From jwa Require Export Data.Collection.List.
From jwa Require Export Data.Collection.Membership.
From jwa Require Export Data.Collection.NonEmptyList.
From jwa Require Export Data.Collection.Sized.
