(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Bijunction.

Inductive Conjunction (A : Prop) (B : Prop) : Prop :=
  | Conjunction_introduction : A -> B -> Conjunction A B.

Arguments Conjunction_introduction {A} {B} a b.

Notation "A /\ B" := (Conjunction A B)
  : jwa_type_scope.

Theorem Conjunction_commutativity
  : forall (A : Prop) (B : Prop), A /\ B -> B /\ A.
Proof.
  intros A B.
  intro h.
  destruct h as [a b].
  (* [Conjunction] has one ctor with two fields,
   * so the goal splits into two goals: [|- B] and [|- A].
   *)
  split.
  - exact b.
  - exact a.
Qed.

Lemma Conjunction_associativity_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intros A B C.
  intro h.
  destruct h  as [ab c].
  destruct ab as [a b].
  split.
  - exact a.
  - split.
    + exact b.
    + exact c.
Qed.

Lemma Conjunction_associativity_backward
  : forall (A : Prop) (B : Prop) (C : Prop), A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C.
  intro h.
  destruct h  as [a bc].
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
  intros A B C.
  split.
  - exact (Conjunction_associativity_forward  A B C).
  - exact (Conjunction_associativity_backward A B C).
Qed.

Lemma Subjunction_currying_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intro f.
  intro a.
  intro b.
  apply f.
  split.
  - exact a.
  - exact b.
Qed.

Lemma Subjunction_currying_backward
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B -> C) -> A /\ B -> C.
Proof.
  intros A B C.
  intro f.
  intro h.
  destruct h as [a b].
  apply f.
  - exact a.
  - exact b.
Qed.

Theorem Subjunction_currying
  : forall (A : Prop) (B : Prop) (C : Prop), (A /\ B -> C) <-> (A -> B -> C).
Proof.
  intros A B C.
  split.
  - exact (Subjunction_currying_forward  A B C).
  - exact (Subjunction_currying_backward A B C).
Qed.

Lemma Subjunction_distributivity_over_Conjunction_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B /\ C) -> (A -> B) /\ (A -> C).
Proof.
  intros A B C.
  intro f.
  split; intro a; destruct (f a) as [b c].
  - exact b.
  - exact c.
Qed.

Lemma Subjunction_distributivity_over_Conjunction_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B) /\ (A -> C) -> A -> B /\ C.
Proof.
  intros A B C.
  intro h.
  destruct h as [ab ac].
  intro a.
  split.
  - apply ab.
    exact a.
  - apply ac.
    exact a.
Qed.

Theorem Subjunction_distributivity_over_Conjunction
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  intros A B C.
  split.
  - exact (Subjunction_distributivity_over_Conjunction_forward  A B C).
  - exact (Subjunction_distributivity_over_Conjunction_backward A B C).
Qed.

Theorem Conjunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 /\ B1 <-> A2 /\ B2).
Proof.
  intros A1 A2 B1 B2.
  intros a b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A1 /\ B1 -> A2 /\ B2] and [|- A2 /\ B2 -> A1 /\ B1]. *)
  split.
  - (* [h : A1 /\ B1]: [|- A2 /\ B2] *)
    intro h.
    destruct h as [a1 b1].
    (* The goal splits into [|- A2] and [|- B2]. *)
    split.
    + apply a12.
      exact a1.
    + apply b12.
      exact b1.
  - (* [h : A2 /\ B2]: [|- A1 /\ B1] *)
    intro h.
    destruct h as [a2 b2].
    (* The goal splits into [|- A1] and [|- B1]. *)
    split.
    + apply a21.
      exact a2.
    + apply b21.
      exact b2.
Qed.
