(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

Inductive Biimplication (A : Prop) (B : Prop) : Prop :=
  | Biimplication_introduction : (A -> B) -> (B -> A) -> Biimplication A B.

Arguments Biimplication_introduction {A} {B} forward backward.

Notation "A <-> B" := (Biimplication A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Biimplication.symmetry].
 *)
Module Biimplication.

Theorem reflexivity : forall (A : Prop), A <-> A.
Proof.
  intro A.
  split; intro a; exact a.
Qed.

Theorem symmetry
  : forall (A : Prop) (B : Prop), (A <-> B) -> (B <-> A).
Proof.
  intros A B.
  intro h.
  destruct h as [ab ba].
  split.
  - exact ba.
  - exact ab.
Qed.

Theorem transitivity
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
  intros A B C.
  intro hab.
  intro hbc.
  destruct hab as [ab ba].
  destruct hbc as [bc cb].
  split.
  - intro a.
    apply bc.
    apply ab.
    exact a.
  - intro c.
    apply ba.
    apply cb.
    exact c.
Qed.

Theorem elimination_forward
  : forall (A : Prop) (B : Prop), (A <-> B) -> A -> B.
Proof.
  intros A B.
  intro e.
  destruct e as [ab ba].
  exact ab.
Qed.

Theorem elimination_backward
  : forall (A : Prop) (B : Prop), (A <-> B) -> B -> A.
Proof.
  intros A B.
  intro e.
  destruct e as [ab ba].
  exact ba.
Qed.

Theorem congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> ((A1 <-> B1) <-> (A2 <-> B2)).
Proof.
  intros A1 A2 B1 B2.
  intro a.
  intro b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  split; intro e; destruct e as [ab ba]; split.
  +
    intro a2.
    apply b12.
    apply ab.
    apply a21.
    exact a2.
  +
    intro b2.
    apply a12.
    apply ba.
    apply b21.
    exact b2.
  +
    intro a1.
    apply b21.
    apply ab.
    apply a12.
    exact a1.
  +
    intro b1.
    apply a21.
    apply ba.
    apply b12.
    exact b1.
Qed.

(* [Biimplication.sejunction_incompatibility] is stated in
 * [Core.Logic.Sejunction], the lowest file that knows both connectives, in
 * a second module of this name.
 *)

End Biimplication.

(* The congruence of [->] belongs to [Implication], but its statement needs
 * [<->], so it can be stated only here. A second module of that name
 * carries it, and a client reads [Implication.congruence].
 *)
Module Implication.

Theorem congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> ((A1 -> B1) <-> (A2 -> B2)).
Proof.
  intros A1 A2 B1 B2.
  intro a.
  intro b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  split; intro f.
  - intro a2.
    apply b12.
    apply f.
    apply a21.
    exact a2.
  - intro a1.
    apply b21.
    apply f.
    apply a12.
    exact a1.
Qed.

End Implication.
