(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Core]: re-exports every module of the layer, so a
   client imports the whole layer with [From jwa Require Import Core.All]. *)

(* [Require Export], not a plain [Require]: a notation and an open scope reach
   a client only through [Import], so qualified access would deliver nothing. *)
From jwa Require Export Core.Notations.
From jwa Require Export Core.Ltac.
From jwa Require Export Core.Logic.All.
From jwa Require Export Core.Eq.
From jwa Require Export Core.Bool.
