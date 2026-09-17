(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] declares
   the scope and reserves the level that the notation below needs,
   [Core.Ltac] carries the tactic language, [Core.Logic.Subjunction]
   carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.

Inductive Conjunction (A : Prop) (B : Prop) : Prop :=
  | Conjunction_introduction : A -> B -> Conjunction A B.

Arguments Conjunction_introduction {A} {B} a b.

Notation "A /\ B" := (Conjunction A B) : jwa_type_scope.

(* The laws are implications: [<->] is built from [Conjunction] and cannot
   be used here. Commutativity is its own converse, so one theorem covers
   both directions; associativity takes one per direction. *)

Theorem Conjunction_commutativity
  : forall (A : Prop) (B : Prop), A /\ B -> B /\ A.
Proof.
  (* The context gains [A] and [B]: [|- A /\ B -> B /\ A] *)
  intros A B.
  (* The context gains [h : A /\ B]: [|- B /\ A] *)
  intro h.
  (* [Conjunction] has one ctor with two fields, so [h] splits into [a : A]
     and [b : B]. *)
  destruct h as [a b].
  (* [Conjunction] has one ctor with two fields, so the goal splits into
     two goals: [|- B] and [|- A]. *)
  split.
  - exact b.
  - exact a.
Qed.

Lemma Conjunction_associativity_forward
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

Lemma Conjunction_associativity_backward
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

Theorem Conjunction_associativity
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
  - (* [Conjunction_associativity_forward A B C] is a proof of the goal as
       it stands. *)
    exact (Conjunction_associativity_forward A B C).
  - (* [Conjunction_associativity_backward A B C] is a proof of the goal as
       it stands. *)
    exact (Conjunction_associativity_backward A B C).
Qed.

Lemma Subjunction_currying_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B -> C) -> A -> B -> C.
Proof.
  (* The context gains [A], [B] and [C]: [|- (A /\ B -> C) -> A -> B -> C] *)
  intros A B C.
  (* The context gains [f : A /\ B -> C]: [|- A -> B -> C] *)
  intro f.
  (* The context gains [a : A]: [|- B -> C] *)
  intro a.
  (* The context gains [b : B]: [|- C] *)
  intro b.
  (* [f] turns a proof of [A /\ B] into a proof of [C]: [|- A /\ B] *)
  apply f.
  (* The goal splits into two goals: [|- A] and [|- B]. *)
  split.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.

Lemma Subjunction_currying_backward
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B -> C) -> A /\ B -> C.
Proof.
  (* The context gains [A], [B] and [C]: [|- (A -> B -> C) -> A /\ B -> C] *)
  intros A B C.
  (* The context gains [f : A -> B -> C]: [|- A /\ B -> C] *)
  intro f.
  (* The context gains [h : A /\ B]: [|- C] *)
  intro h.
  (* [h] splits into [a : A] and [b : B]. *)
  destruct h as [a b].
  (* [f] turns proofs of [A] and of [B] into a proof of [C], so the goal
     splits into two goals: [|- A] and [|- B]. *)
  apply f.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.

Theorem Subjunction_currying
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B -> C) <-> (A -> B -> C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A /\ B -> C) <-> (A -> B -> C)] *)
  intros A B C.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- (A /\ B -> C) -> A -> B -> C] and
     [|- (A -> B -> C) -> A /\ B -> C]. *)
  split.
  - (* [Subjunction_currying_forward A B C] is a proof of the goal as it
       stands. *)
    exact (Subjunction_currying_forward A B C).
  - (* [Subjunction_currying_backward A B C] is a proof of the goal as it
       stands. *)
    exact (Subjunction_currying_backward A B C).
Qed.
