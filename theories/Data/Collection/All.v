(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Collection]: re-exports every collection type and
 * every interface they answer to, so a client imports them with
 * [From jwa Require Import Data.Collection.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Nat0]
 * for the index [nth], [take] and [drop] count with, [Option] for what [nth]
 * returns, [Nat] for [NonEmptyList]'s length, [Bool] for the deciders,
 * [Comparison] for what [compare] returns and [Comparable] for the premise of
 * its laws.
 *)
From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Base.Comparison.
From jwa Require Export Data.Comparable.
From jwa Require Export Data.Number.Nat.
From jwa Require Export Data.Number.Nat0.
From jwa Require Export Data.Option.

From jwa Require Export Data.Collection.BinaryTree.
From jwa Require Export Data.Collection.List.
From jwa Require Export Data.Collection.Membership.
From jwa Require Export Data.Collection.NonEmptyList.
From jwa Require Export Data.Collection.Sized.
From jwa Require Export Data.Functor.
