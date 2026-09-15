(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Logic.Conditional] carries
   [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Conditional.

Inductive Or (A : Prop) (B : Prop) : Prop :=
  | Or_left  : A -> Or A B
  | Or_right : B -> Or A B.

(* The unused side is not determined by the argument. It comes from the
   expected type, and a use that has none needs [@Or_left]. *)
Arguments Or_left  {A} {B} a.
Arguments Or_right {A} {B} b.

Notation "A \/ B" := (Or A B) : jwa_type_scope.
