(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Conditional is the conditional, [if A then B]. [->] is the kernel's
 * non-dependent [forall], which this line only gives a spelling.
 *)
Notation "A -> B" := (forall (_ : A) . B)
  : jwa_type_scope.

(* No type is declared for [->], so the module carries the connective's
 * name by itself; its laws read [Conditional.transitivity].
 *)
Module Conditional. (* Conditional *)

Theorem reflexivity : forall {A : Prop} . A -> A.
Proof.
  intro A.
  intro a.
  ipso a.
Qed.

Theorem transitivity
  : forall {A : Prop} {B : Prop} {C : Prop} . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intro ab.
  intro bc.
  intro a.
  let proof b := ab a.
  let proof facto := bc b.
  ipso facto.
Qed.

(* The three structural rules of Gentzen's sequent calculus, as theorems
 * about [->]: weakening, contraction and exchange.
 *)

Theorem weakening : forall {A : Prop} {B : Prop} . A -> B -> A.
Proof.
  intros A B.
  intro a.
  intro b.
  ipso a.
Qed.

Theorem contraction
  : forall {A : Prop} {B : Prop} . (A -> A -> B) -> A -> B.
Proof.
  intros A B.
  intro f.
  intro a.
  ipso (f a a).
Qed.

(* Its own converse: applying it twice restores the order. *)
Theorem exchange
  : forall {A : Prop} {B : Prop} {C : Prop} . (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  intro f.
  intro b.
  intro a.
  ipso (f a b).
Qed.

(* Two laws of [->] are stated higher up, each in a second module of this
 * name in the lowest file that knows both connectives:
 * [Conditional.congruence] in [Core.Logic.Biconditional] and
 * [Conditional.exclusion.of.abjunction] in [Core.Logic.Abjunction].
 *)

End Conditional. (* Conditional *)
