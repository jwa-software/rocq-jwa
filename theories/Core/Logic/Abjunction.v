(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Logic.Subjunction] carries
   [->], [Core.Logic.Unjunction] carries [~]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Unjunction.

(* Abjunction is material nonimplication: [A] holds and [B] does not, the
   one case in which [A -> B] fails. *)
Record Abjunction (A : Prop) (B : Prop) : Prop :=
  { Abjunction_left : A ; Abjunction_right : ~ B }.

Arguments Abjunction_left  {A} {B} _.
Arguments Abjunction_right {A} {B} _.

Notation "A -/> B" := (Abjunction A B) : jwa_type_scope.
