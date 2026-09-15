(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] declares
   the scope and reserves the level that the notation below needs. *)
From jwa Require Import Core.Notations.

Record And (A : Prop) (B : Prop) : Prop := { And_left : A ; And_right : B }.

Arguments And_left  {A} {B} _.
Arguments And_right {A} {B} _.

Notation "A /\ B" := (And A B) : jwa_type_scope.
