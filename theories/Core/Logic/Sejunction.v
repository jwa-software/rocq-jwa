(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Unjunction]
   carries [~]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Unjunction.

(* Sejunction is exclusive disjunction: one side holds and the other does
   not. [Theorem t : Verum _\/_ Verum.] is accepted and [Proof.] opens, but no
   step reaches [Qed.]: either ctor demands [~ Verum], and no term has that
   type. Being writable does not make a statement provable. *)
Inductive Sejunction (A : Prop) (B : Prop) : Prop :=
  | Sejunction_left  : A -> ~ B -> Sejunction A B
  | Sejunction_right : ~ A -> B -> Sejunction A B.

Arguments Sejunction_left  {A} {B} a not_b.
Arguments Sejunction_right {A} {B} not_a b.

Notation "A _\/_ B" := (Sejunction A B) : jwa_type_scope.

Theorem Sejunction_commutativity
  : forall (A : Prop) (B : Prop), A _\/_ B -> B _\/_ A.
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> B _\/_ A] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- B _\/_ A] *)
  intro h.
  (* [Sejunction] has two ctors with two fields each, so [h] gives two
     goals: one with [a : A] and [not_b : ~ B], one with [not_a : ~ A] and
     [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [Sejunction_right] asks for [~ B] then [A], the two fields in the
       other order. *)
    exact (Sejunction_right not_b a).
  - (* [Sejunction_left] asks for [B] then [~ A]. *)
    exact (Sejunction_left b not_a).
Qed.

(* Associativity is not a theorem of this module. From [~ (A _\/_ B)] and
   [C], a proof of [A _\/_ (B _\/_ C)] has to pick a ctor, and which one is
   right depends on whether [A] holds; no term decides that. *)
