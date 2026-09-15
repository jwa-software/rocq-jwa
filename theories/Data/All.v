(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data]: re-exports every module of the layer, so a
   client imports the whole layer with [From jwa Require Import Data.All]. *)

(* [Export] so a client writes [Option A], not [Option.Option A]. *)
From jwa Require Export Data.Option.
