(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Logic.Subjunction] carries
   [->], [Core.Logic.Unjunction] carries [~]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Unjunction.

(* Abjunction is material nonimplication: [A] holds and [B] does not, the
   one case in which [A -> B] fails. *)
Inductive Abjunction (A : Prop) (B : Prop) : Prop :=
  | Abjunction_introduction : A -> ~ B -> Abjunction A B.

Arguments Abjunction_introduction {A} {B} a not_b.

Notation "A -/> B" := (Abjunction A B) : jwa_type_scope.
