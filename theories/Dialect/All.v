(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Dialect]: re-exports every module of the layer, so a
 * file writes its proofs in this library's tactic language by importing
 * [From jwa Require Import Dialect.All].
 *
 * The layer is the tactic language itself: Ltac2 with Rocq's own tactic
 * syntax hidden, and the tactics that name no definition of this tree. The
 * tactics built on its logic live in [jwa.Tactics].
 *)
From jwa Require Export Dialect.Context.
From jwa Require Export Dialect.Ipso.
From jwa Require Export Dialect.Leibniz.
From jwa Require Export Dialect.Let.
From jwa Require Export Dialect.Loanword.
From jwa Require Export Dialect.Ltac.
From jwa Require Export Dialect.Place.
From jwa Require Export Dialect.Simpl.
