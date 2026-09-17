(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] declares
   the scope and reserves the level that the notation below needs,
   [Core.Ltac] carries the tactic language, [Core.Logic.Subjunction]
   carries [->], [Core.Logic.Bijunction] carries [<->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Bijunction.

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

(* How [->] interacts with [/\]: a conjunction on the left of an arrow is
   two arrows in a row, and a conjunction on the right is two arrows side by
   side. Each is a [<->] with its halves as lemmas. *)

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

Lemma Subjunction_distributivity_over_Conjunction_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B /\ C) -> (A -> B) /\ (A -> C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A -> B /\ C) -> (A -> B) /\ (A -> C)] *)
  intros A B C.
  (* The context gains [f : A -> B /\ C]: [|- (A -> B) /\ (A -> C)] *)
  intro f.
  (* The goal splits into two goals: [|- A -> B] and [|- A -> C]. *)
  split.
  - (* The context gains [a : A]: [|- B] *)
    intro a.
    (* [f a] is a proof of [B /\ C]; only its left half is needed:
       [b : B]. *)
    destruct (f a) as [b _].
    (* [b] is a proof of the goal as it stands. *)
    exact b.
  - (* The context gains [a : A]: [|- C] *)
    intro a.
    (* [f a] is a proof of [B /\ C]; only its right half is needed:
       [c : C]. *)
    destruct (f a) as [_ c].
    (* [c] is a proof of the goal as it stands. *)
    exact c.
Qed.

Lemma Subjunction_distributivity_over_Conjunction_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B) /\ (A -> C) -> A -> B /\ C.
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A -> B) /\ (A -> C) -> A -> B /\ C] *)
  intros A B C.
  (* The context gains [h : (A -> B) /\ (A -> C)]: [|- A -> B /\ C] *)
  intro h.
  (* [h] splits into [ab : A -> B] and [ac : A -> C]. *)
  destruct h as [ab ac].
  (* The context gains [a : A]: [|- B /\ C] *)
  intro a.
  (* The goal splits into two goals: [|- B] and [|- C]. *)
  split.
  - (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [ac] turns a proof of [A] into a proof of [C]: [|- A] *)
    apply ac.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
Qed.

Theorem Subjunction_distributivity_over_Conjunction
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A -> B /\ C) <-> (A -> B) /\ (A -> C)] *)
  intros A B C.
  split.
  - exact (Subjunction_distributivity_over_Conjunction_forward A B C).
  - exact (Subjunction_distributivity_over_Conjunction_backward A B C).
Qed.
