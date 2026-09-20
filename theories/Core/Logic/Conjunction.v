(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biimplication.
From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

Inductive Conjunction (A : Prop) (B : Prop) : Prop :=
  | Conjunction_introduction : A -> B -> Conjunction A B.

Arguments Conjunction_introduction {A} {B} a b.

Notation "A /\ B" := (Conjunction A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Conjunction.commutativity].
 *)
Module Conjunction.

Theorem commutativity
  : forall {A : Prop} {B : Prop} . A /\ B -> B /\ A.
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

Theorem associativity
  : forall (A : Prop) (B : Prop) (C : Prop) . (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  intros A B C.
  split.
  - intro h.
    destruct h  as [ab c].
    destruct ab as [a b].
    split.
    + exact a.
    + split.
      * exact b.
      * exact c.
  - intro h.
    destruct h  as [a bc].
    destruct bc as [b c].
    split.
    + split.
      * exact a.
      * exact b.
    + exact c.
Qed.

(* Currying: a proof from a pair is a proof from the first that returns a
 * proof from the second.
 *)
Theorem currying
  : forall (A : Prop) (B : Prop) (C : Prop) . (A /\ B -> C) <-> (A -> B -> C).
Proof.
  intros A B C.
  split.
  - intro f.
    intro a.
    intro b.
    apply f.
    split.
    + exact a.
    + exact b.
  - intro f.
    intro h.
    destruct h as [a b].
    apply f.
    + exact a.
    + exact b.
Qed.

(* The universal property of [/\] as a product: a proof of [B /\ C] from [A]
 * is a pair of proofs from [A], one of [B] and one of [C].
 *)
Theorem universality
  : forall (A : Prop) (B : Prop) (C : Prop) .
      (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  intros A B C.
  split.
  - intro f.
    split; intro a; destruct (f a) as [b c].
    + exact b.
    + exact c.
  - intro h.
    destruct h as [ab ac].
    intro a.
    split.
    + apply ab.
      exact a.
    + apply ac.
      exact a.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 /\ B1 <-> A2 /\ B2).
Proof.
  intros A1 A2 B1 B2.
  intros a b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
   * goals: [|- A1 /\ B1 -> A2 /\ B2] and [|- A2 /\ B2 -> A1 /\ B1].
   *)
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

(* [Conjunction.distributivity_over_disjunction] is stated in
 * [Core.Logic.Disjunction], the lowest file that knows both connectives,
 * in a second module of this name.
 *)

End Conjunction.
