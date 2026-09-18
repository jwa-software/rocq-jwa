(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Falsum.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Bijunction.

(* Unjunction is negation: a proof of [A] leads to [Falsum]. *)
(* [Prop -> Prop] *)
Definition Unjunction := fun (A : Prop) => A -> Falsum.

Notation "~ A" := (Unjunction A) : jwa_type_scope.

Theorem De_Morgan_Disjunction
  : forall (A : Prop) (B : Prop), ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  intros A B.
  unfold Unjunction in |- *.
  intro h.
  split.
  - intro a.
    apply h.
    exact (Disjunction_left a).
  - intro b.
    apply h.
    exact (Disjunction_right b).
Qed.

Theorem De_Morgan_Disjunction_backward
  : forall (A : Prop) (B : Prop), ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  intros A B.
  unfold Unjunction in |- *.
  intro h.
  destruct h as [not_a not_b].
  intro ab.
  destruct ab as [a | b].
  - exact (not_a a).
  - exact (not_b b).
Qed.

Theorem De_Morgan_Conjunction
  : forall (A : Prop) (B : Prop), ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  intros A B.
  unfold Unjunction in |- *.
  intro h.
  intro ab.
  destruct ab as [a b].
  destruct h as [not_a | not_b].
  - exact (not_a a).
  - exact (not_b b).
Qed.

Theorem Unjunction_twice : forall (A : Prop), A -> ~ ~ A.
Proof.
  intro A.
  intro a.
  unfold Unjunction in |- *.
  intro not_a.
  exact (not_a a).
Qed.

Theorem Unjunction_thrice : forall (A : Prop), ~ ~ ~ A -> ~ A.
Proof.
  intro A.
  unfold Unjunction in |- *.
  intro not_not_not_a.
  intro a.
  apply not_not_not_a.
  intro not_a.
  exact (not_a a).
Qed.

Theorem Subjunction_contraposition
  : forall (A : Prop) (B : Prop), (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B.

  (* [|- (A -> B) -> (B -> Falsum) -> (A -> Falsum)] *)
  unfold Unjunction in |- *.

  (* The context gains [ab : A -> B]: [|- (B -> Falsum) -> A -> Falsum] *)
  intro ab.
  (* The context gains [not_b : B -> Falsum]: [|- A -> Falsum] *)
  intro not_b.
  (* The context gains [a : A]: [|- Falsum] *)
  intro a.

  (* [|- B] *)
  apply not_b.
  (* [|- A] *)
  apply ab.

  exact a.
Qed.

Theorem Unjunction_congruence
  : forall (A1 : Prop) (A2 : Prop), (A1 <-> A2) -> (~ A1 <-> ~ A2).
Proof.
  intros A1 A2.
  intro ea.

  (* [a12 : A1 -> A2]
   * [a21 : A2 -> A1].
   *)
  destruct ea as [a12 a21].

  (* [|- (A1 -> Falsum) <-> (A2 -> Falsum)] *)
  unfold Unjunction in |- *.

  (* [Bijunction] has one ctor with two fields,
   * so the goal splits into two goals:
   * [|- (A1 -> Falsum) -> (A2 -> Falsum)]
   * [|- (A2 -> Falsum) -> (A1 -> Falsum)].
   *)
  split.

  - intro not_a1.
    intro a2.

    (* [|- A1] *)
    apply not_a1.
    (* [|- A2] *)
    apply a21.

    exact a2.

  - intro not_a2.
    intro a1.

    (* [|- A2] *)
    apply not_a2.
    (* [|- A1] *)
    apply a12.

    exact a1.
Qed.
