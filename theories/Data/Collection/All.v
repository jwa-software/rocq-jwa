(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Collection]: re-exports every collection type and
 * every interface they answer to, so a client imports them with
 * [From jwa Require Import Data.Collection.All].
 *)

(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Data.Collection.List.
From jwa Require Export Data.Collection.Sized.
