(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Logic.Conditional] carries
   [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.False.

(* [Prop -> Prop] *)
Definition Not := fun (A : Prop) => A -> False.

Notation "~ A" := (Not A) : jwa_type_scope.
