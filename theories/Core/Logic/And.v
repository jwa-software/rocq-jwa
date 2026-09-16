(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] declares
   the scope and reserves the level that the notation below needs,
   [Core.Ltac] carries the tactic language, [Core.Logic.Conditional]
   carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Conditional.

Record And (A : Prop) (B : Prop) : Prop := { And_left : A ; And_right : B }.

Arguments And_left  {A} {B} _.
Arguments And_right {A} {B} _.

Notation "A /\ B" := (And A B) : jwa_type_scope.

(* The laws are implications: [<->] is built from [And] and cannot be used
   here. Commutativity is its own converse, so one theorem covers both
   directions; associativity takes one per direction. *)

Theorem And_commutativity : forall (A : Prop) (B : Prop), A /\ B -> B /\ A.
Proof.
  (* The context gains [A] and [B]: [|- A /\ B -> B /\ A] *)
  intros A B.
  (* The context gains [h : A /\ B]: [|- B /\ A] *)
  intro h.
  (* [And] has one ctor with two fields, so [h] splits into [a : A] and
     [b : B]. *)
  destruct h as [a b].
  (* [And] has one ctor with two fields, so the goal splits into two goals:
     [|- B] and [|- A]. *)
  split.
  - exact b.
  - exact a.
Qed.

Lemma And_associativity_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A /\ B) /\ C -> A /\ (B /\ C)] *)
  intros A B C.
  (* The context gains [h : (A /\ B) /\ C]: [|- A /\ (B /\ C)] *)
  intro h.
  (* [h] splits into [ab : A /\ B] and [c : C]. *)
  destruct h as [ab c].
  (* [ab] splits into [a : A] and [b : B]. *)
  destruct ab as [a b].
  (* [|- A /\ (B /\ C)] splits into [|- A] and [|- B /\ C]. *)
  split.
  - exact a.
  - split.
    + exact b.
    + exact c.
Qed.

Lemma And_associativity_backward
  : forall (A : Prop) (B : Prop) (C : Prop), A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  (* The context gains [A], [B] and [C]:
     [|- A /\ (B /\ C) -> (A /\ B) /\ C] *)
  intros A B C.
  (* The context gains [h : A /\ (B /\ C)]: [|- (A /\ B) /\ C] *)
  intro h.
  (* [h] splits into [a : A] and [bc : B /\ C]. *)
  destruct h as [a bc].
  (* [bc] splits into [b : B] and [c : C]. *)
  destruct bc as [b c].
  split.
  - split.
    + exact a.
    + exact b.
  - exact c.
Qed.

Theorem And_associativity
  : forall (A : Prop) (B : Prop) (C : Prop),
      ((A /\ B) /\ C -> A /\ (B /\ C)) /\ (A /\ (B /\ C) -> (A /\ B) /\ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- ((A /\ B) /\ C -> A /\ (B /\ C))
         /\ (A /\ (B /\ C) -> (A /\ B) /\ C)] *)
  intros A B C.
  (* The goal splits into two goals:
     [|- (A /\ B) /\ C -> A /\ (B /\ C)] and
     [|- A /\ (B /\ C) -> (A /\ B) /\ C]. *)
  split.
  - (* [And_associativity_forward A B C] is a proof of the goal as it stands. *)
    exact (And_associativity_forward A B C).
  - (* [And_associativity_backward A B C] is a proof of the goal as it stands. *)
    exact (And_associativity_backward A B C).
Qed.
