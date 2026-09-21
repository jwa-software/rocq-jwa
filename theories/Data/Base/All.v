(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Base]: re-exports the base types, so a client
 * imports them with [From jwa Require Import Data.Base.All].
 *
 * A base type is built from no other type: every ctor takes no argument,
 * so the values can be listed. [Empty] has none, [Unit] one, [Bool] two,
 * [Comparison] three.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

From jwa Require Export Data.Base.Bool.
From jwa Require Export Data.Base.Comparison.
From jwa Require Export Data.Base.Empty.
From jwa Require Export Data.Base.Unit.
