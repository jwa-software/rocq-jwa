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
  match h with | a b end.
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
    match h  with | ab c end.
    match ab with | a b end.
    divide et impera.
    + ipso a.
    + divide et impera.
      * ipso b.
      * ipso c.
  - intro h.
    match h  with | a bc end.
    match bc with | b c end.
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
    ipso (f (Conjunction_introduction a b)).
  - intro f.
    intro h.
    match h with | a b end.
    ipso (f a b).
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
    divide et impera; intro a; match (f a) with | b c end.
    + ipso b.
    + ipso c.
  - intro h.
    match h with | ab ac end.
    intro a.
    divide et impera.
    + ipso (ab a).
    + ipso (ac a).
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 /\ B1 <-> A2 /\ B2).
Proof.
  intros A1 A2 B1 B2.
  intros a b.
  match a with | a12 a21 end.
  match b with | b12 b21 end.
  (* [Biconditional] has one ctor with two fields, so the goal splits into two
   * goals: [|- A1 /\ B1 -> A2 /\ B2] and [|- A2 /\ B2 -> A1 /\ B1].
   *)
  divide et impera.
  - (* [h : A1 /\ B1]: [|- A2 /\ B2] *)
    intro h.
    match h with | a1 b1 end.
    (* The goal splits into [|- A2] and [|- B2]. *)
    divide et impera.
    + ipso (a12 a1).
    + ipso (b12 b1).
  - (* [h : A2 /\ B2]: [|- A1 /\ B1] *)
    intro h.
    match h with | a2 b2 end.
    (* The goal splits into [|- A1] and [|- B1]. *)
    divide et impera.
    + ipso (a21 a2).
    + ipso (b21 b2).
Qed.

(* [Conjunction.distributivity.over.disjunction] is stated in
 * [Core.Logic.Disjunction], the lowest file that knows both connectives,
 * in a second module of this name.
 *)

End Conjunction. (* Conjunction *)
