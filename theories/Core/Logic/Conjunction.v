(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

Inductive Conjunction (A : Prop) (B : Prop) : Prop :=
  | Conjunction_introduction : A -> B -> Conjunction A B.

Arguments Conjunction_introduction {A} {B} a b.

Notation "A /\ B" := (Conjunction A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Conjunction.commutativity].
 *)
Module Conjunction. (* Conjunction *)

Theorem commutativity
  : forall {A : Prop} {B : Prop} . A /\ B -> B /\ A.
Proof.
  intros A B.
  intro h.
  destruct h as [a b].
  (* [Conjunction] has one ctor with two fields,
   * so the goal splits into two goals: [|- B] and [|- A].
   *)
  divide et impera.
  - ipso b.
  - ipso a.
Qed.

Theorem associativity
  : forall (A : Prop) (B : Prop) (C : Prop) . (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  intros A B C.
  divide et impera.
  - intro h.
    destruct h  as [ab c].
    destruct ab as [a b].
    divide et impera.
    + ipso a.
    + divide et impera.
      * ipso b.
      * ipso c.
  - intro h.
    destruct h  as [a bc].
    destruct bc as [b c].
    divide et impera.
    + divide et impera.
      * ipso a.
      * ipso b.
    + ipso c.
Qed.

(* Currying: a proof from a pair is a proof from the first that returns a
 * proof from the second.
 *)
Theorem currying
  : forall (A : Prop) (B : Prop) (C : Prop) . (A /\ B -> C) <-> (A -> B -> C).
Proof.
  intros A B C.
  divide et impera.
  - intro f.
    intro a.
    intro b.
    apply f.
    divide et impera.
    + ipso a.
    + ipso b.
  - intro f.
    intro h.
    destruct h as [a b].
    apply f.
    + ipso a.
    + ipso b.
Qed.

(* The universal property of [/\] as a product: a proof of [B /\ C] from [A]
 * is a pair of proofs from [A], one of [B] and one of [C].
 *)
Theorem universality
  : forall (A : Prop) (B : Prop) (C : Prop) .
      (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  intros A B C.
  divide et impera.
  - intro f.
    divide et impera; intro a; destruct (f a) as [b c].
    + ipso b.
    + ipso c.
  - intro h.
    destruct h as [ab ac].
    intro a.
    divide et impera.
    + apply ab.
      ipso a.
    + apply ac.
      ipso a.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 /\ B1 <-> A2 /\ B2).
Proof.
  intros A1 A2 B1 B2.
  intros a b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  (* [Biconditional] has one ctor with two fields, so the goal splits into two
   * goals: [|- A1 /\ B1 -> A2 /\ B2] and [|- A2 /\ B2 -> A1 /\ B1].
   *)
  divide et impera.
  - (* [h : A1 /\ B1]: [|- A2 /\ B2] *)
    intro h.
    destruct h as [a1 b1].
    (* The goal splits into [|- A2] and [|- B2]. *)
    divide et impera.
    + apply a12.
      ipso a1.
    + apply b12.
      ipso b1.
  - (* [h : A2 /\ B2]: [|- A1 /\ B1] *)
    intro h.
    destruct h as [a2 b2].
    (* The goal splits into [|- A1] and [|- B1]. *)
    divide et impera.
    + apply a21.
      ipso a2.
    + apply b21.
      ipso b2.
Qed.

(* [Conjunction.distributivity.over.disjunction] is stated in
 * [Core.Logic.Disjunction], the lowest file that knows both connectives,
 * in a second module of this name.
 *)

End Conjunction. (* Conjunction *)
