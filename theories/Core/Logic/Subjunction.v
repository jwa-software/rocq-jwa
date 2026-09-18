(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.

(* Subjunction is the conditional, [if A then B]. [->] is the kernel's
 * non-dependent [forall], which this line only gives a spelling.
 *)
Notation "A -> B" := (forall (_ : A), B) : jwa_type_scope.

Theorem Subjunction_reflexivity : forall (A : Prop), A -> A.
Proof.
  intro A.
  intro a.
  exact a.
Qed.

Theorem Subjunction_transitivity
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intro ab.
  intro bc.
  intro a.
  apply bc.
  apply ab.
  exact a.
Qed.

Theorem Subjunction_weakening : forall (A : Prop) (B : Prop), A -> B -> A.
Proof.
  intros A B.
  intro a.
  intro b.
  exact a.
Qed.

Theorem Subjunction_contraction
  : forall (A : Prop) (B : Prop), (A -> A -> B) -> A -> B.
Proof.
  intros A B.
  intro f.
  intro a.
  apply f.
  - exact a.
  - exact a.
Qed.

(* Its own converse: applying it twice restores the order. *)
Theorem Subjunction_exchange
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  intro f.
  intro b.
  intro a.
  apply f.
  - exact a.
  - exact b.
Qed.

(* [Subjunction.abjunction_incompatibility] is stated in
 * [Core.Logic.Abjunction], the lowest file that knows both connectives, in
 * a module named after this one.
 *)
