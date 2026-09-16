(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Logic.Conditional] carries
   [->], [Core.Logic.Not] carries [~]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Not.

(* [Theorem t : True _\/_ True.] is accepted and [Proof.] opens, but no step
   reaches [Qed.]: either ctor demands [~ True], and no term has that type.
   Being writable does not make a statement provable. *)
Inductive Xor (A : Prop) (B : Prop) : Prop :=
  | Xor_left  : A -> ~ B -> Xor A B
  | Xor_right : ~ A -> B -> Xor A B.

Arguments Xor_left  {A} {B} a not_b.
Arguments Xor_right {A} {B} not_a b.

Notation "A _\/_ B" := (Xor A B) : jwa_type_scope.
