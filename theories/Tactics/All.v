(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Tactics]: re-exports every module of the layer, so a
 * client imports the whole layer with [From jwa Require Import Tactics.All].
 *)

(* [Require Export], not a plain [Require]: a tactic notation reaches a client
 * only through [Import].
 *)
From jwa Require Export Tactics.DeMorgan.
From jwa Require Export Tactics.DoubleNegation.
From jwa Require Export Tactics.Equation.
From jwa Require Export Tactics.Join.
From jwa Require Export Tactics.Modus.
From jwa Require Export Tactics.Syllogism.
From jwa Require Export Tactics.Witness.
