(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Conditional] carries [->], [Core.Logic.Not]
   carries [~]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
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

Theorem Xor_commutativity
  : forall (A : Prop) (B : Prop), A _\/_ B -> B _\/_ A.
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> B _\/_ A] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- B _\/_ A] *)
  intro h.
  (* [Xor] has two ctors with two fields each, so [h] gives two goals: one
     with [a : A] and [not_b : ~ B], one with [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [Xor_right] asks for [~ B] then [A], the two fields in the other
       order. *)
    exact (Xor_right not_b a).
  - (* [Xor_left] asks for [B] then [~ A]. *)
    exact (Xor_left b not_a).
Qed.

(* Associativity is not a theorem of this module. From [~ (A _\/_ B)] and
   [C], a proof of [A _\/_ (B _\/_ C)] has to pick a ctor, and which one is
   right depends on whether [A] holds; no term decides that. *)
