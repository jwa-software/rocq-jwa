(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Bijunction.

Inductive Disjunction (A : Prop) (B : Prop) : Prop :=
  | Disjunction_left  : A -> Disjunction A B
  | Disjunction_right : B -> Disjunction A B.

(* The unused side is not determined by the argument. It comes from the
 * expected type, and a use that has none needs [@Disjunction_left].
 *)
Arguments Disjunction_left  {A} {B} a.
Arguments Disjunction_right {A} {B} b.

Notation "A \/ B" := (Disjunction A B)
  : jwa_type_scope.

Theorem Disjunction_commutativity
  : forall (A : Prop) (B : Prop), A \/ B -> B \/ A.
Proof.
  intros A B.
  intro h.
  (* [Disjunction] has two ctors, so [h] gives two same goals with different contexts;
   * - one with [a : A],
   * - one with [b : B].
   *)
  destruct h as [a | b].
  - exact (Disjunction_right a).
  - exact (Disjunction_left  b).
Qed.

Lemma Disjunction_associativity_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  intros A B C.
  intro h.
  destruct h as [ab | c].
  - destruct ab as [a | b].
    + exact (Disjunction_left a).
    + exact (Disjunction_right (Disjunction_left b)).
  - exact (Disjunction_right (Disjunction_right c)).
Qed.

Lemma Disjunction_associativity_backward
  : forall (A : Prop) (B : Prop) (C : Prop), A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C.
  intro h.
  destruct h as [a | bc].
  - exact (Disjunction_left (Disjunction_left a)).
  - destruct bc as [b | c].
    + exact (Disjunction_left (Disjunction_right b)).
    + exact (Disjunction_right c).
Qed.

Theorem Disjunction_associativity
  : forall (A : Prop) (B : Prop) (C : Prop),
      ((A \/ B) \/ C -> A \/ (B \/ C)) /\ (A \/ (B \/ C) -> (A \/ B) \/ C).
Proof.
  intros A B C.
  split.
  - exact (Disjunction_associativity_forward  A B C).
  - exact (Disjunction_associativity_backward A B C).
Qed.

Lemma Conjunction_distributivity_over_Disjunction_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  intro h.
  destruct h as [a bc].
  destruct bc as [b | c].
  - (* [|- A /\ B] *)
    apply Disjunction_left.
    split.
    + exact a.
    + exact b.
  - (* [|- A /\ C] *)
    apply Disjunction_right.
    split.
    + exact a.
    + exact c.
Qed.

Lemma Conjunction_distributivity_over_Disjunction_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A /\ B) \/ (A /\ C) -> A /\ (B \/ C).
Proof.
  intros A B C.
  intro h.
  destruct h as [ab | ac].
  - destruct ab as [a b].
    split.
    + exact a.
    + exact (Disjunction_left b).
  - destruct ac as [a c].
    split.
    + exact a.
    + exact (Disjunction_right c).
Qed.

Theorem Conjunction_distributivity_over_Disjunction
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A /\ (B \/ C) -> (A /\ B) \/ (A /\ C)) /\ ((A /\ B) \/ (A /\ C) -> A /\ (B \/ C)).
Proof.
  intros A B C.
  split.
  - exact (Conjunction_distributivity_over_Disjunction_forward  A B C).
  - exact (Conjunction_distributivity_over_Disjunction_backward A B C).
Qed.

Lemma Disjunction_distributivity_over_Conjunction_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  intro h.
  destruct h as [a | bc].
  - split.
    + exact (Disjunction_left a).
    + exact (Disjunction_left a).
  - destruct bc as [b c].
    split.
    + exact (Disjunction_right b).
    + exact (Disjunction_right c).
Qed.

Lemma Disjunction_distributivity_over_Conjunction_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B) /\ (A \/ C) -> A \/ (B /\ C).
Proof.
  intros A B C.
  intro h.
  destruct h  as [ab ac].
  destruct ab as [a | b].
  - exact (Disjunction_left a).
  - destruct ac as [a | c].
    + exact (Disjunction_left a).
    + apply Disjunction_right.
      split.
      * exact b.
      * exact c.
Qed.

Theorem Disjunction_distributivity_over_Conjunction
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ (B /\ C) -> (A \/ B) /\ (A \/ C))
      /\ ((A \/ B) /\ (A \/ C) -> A \/ (B /\ C)).
Proof.
  intros A B C.
  split.
  - exact (Disjunction_distributivity_over_Conjunction_forward  A B C).
  - exact (Disjunction_distributivity_over_Conjunction_backward A B C).
Qed.

Lemma Disjunction_elimination_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  intros A B C.
  intro f.
  split.
  - intro a.
    apply f.
    exact (Disjunction_left a).
  - intro b.
    apply f.
    exact (Disjunction_right b).
Qed.

Lemma Disjunction_elimination_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> C) /\ (B -> C) -> A \/ B -> C.
Proof.
  intros A B C.
  intro h.
  destruct h as [ac bc].
  intro ab.
  destruct ab as [a | b].
  - apply ac.
    exact a.
  - apply bc.
    exact b.
Qed.

Theorem Disjunction_elimination
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  intros A B C.
  split.
  - exact (Disjunction_elimination_forward  A B C).
  - exact (Disjunction_elimination_backward A B C).
Qed.

Theorem Disjunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2).
Proof.
  intros A1 A2 B1 B2.
  intro a.
  intro b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  split; intro h.
  - (* [h : A1 \/ B1]: [|- A2 \/ B2] *)
    destruct h as [a1 | b1].
    + (* [|- A2] *)
      apply Disjunction_left.
      apply a12.
      exact a1.
    + (* [|- B2] *)
      apply Disjunction_right.
      apply b12.
      exact b1.
  - (* [h : A2 \/ B2]: [|- A1 \/ B1] *)
    destruct h as [a2 | b2].
    + (* [|- A1] *)
      apply Disjunction_left.
      apply a21.
      exact a2.
    + (* [|- B1] *)
      apply Disjunction_right.
      apply b21.
      exact b2.
Qed.
