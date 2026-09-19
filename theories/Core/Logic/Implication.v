(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Implication is the conditional, [if A then B]. [->] is the kernel's
 * non-dependent [forall], which this line only gives a spelling.
 *)
Notation "A -> B" := (forall (_ : A), B)
  : jwa_type_scope.

(* No type is declared for [->], so the module carries the connective's
 * name by itself; its laws read [Implication.transitivity].
 *)
Module Implication.

Theorem reflexivity : forall {A : Prop}, A -> A.
Proof.
  intro A.
  intro a.
  exact a.
Qed.

Theorem transitivity
  : forall {A : Prop} {B : Prop} {C : Prop}, (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intro ab.
  intro bc.
  intro a.
  apply bc.
  apply ab.
  exact a.
Qed.

(* The three structural rules of Gentzen's sequent calculus, as theorems
 * about [->]: weakening, contraction and exchange.
 *)

Theorem weakening : forall {A : Prop} {B : Prop}, A -> B -> A.
Proof.
  intros A B.
  intro a.
  intro b.
  exact a.
Qed.

Theorem contraction
  : forall {A : Prop} {B : Prop}, (A -> A -> B) -> A -> B.
Proof.
  intros A B.
  intro f.
  intro a.
  apply f.
  - exact a.
  - exact a.
Qed.

(* Its own converse: applying it twice restores the order. *)
Theorem exchange
  : forall {A : Prop} {B : Prop} {C : Prop}, (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  intro f.
  intro b.
  intro a.
  apply f.
  - exact a.
  - exact b.
Qed.

(* Two laws of [->] are stated higher up, each in a second module of this
 * name in the lowest file that knows both connectives:
 * [Implication.congruence] in [Core.Logic.Biimplication] and
 * [Implication.abjunction_incompatibility] in [Core.Logic.Abjunction].
 *)

End Implication.
