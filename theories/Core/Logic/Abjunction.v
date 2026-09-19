(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biimplication.
From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Abjunction is material nonimplication: [A] holds and [B] does not, the
 * one case in which [A -> B] fails.
 *)
Inductive Abjunction (A : Prop) (B : Prop) : Prop :=
  | Abjunction_introduction : A -> ~ B -> Abjunction A B.

Arguments Abjunction_introduction {A} {B} a nb.

Notation "A -/> B" := (Abjunction A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Abjunction.congruence].
 *)
Module Abjunction.

(* Two propositions are incompatible when they cannot both hold: an
 * abjunction and the implication between the same two sides.
 *)
Theorem implication_incompatibility
  : forall {A : Prop} {B : Prop}, A -/> B -> ~ (A -> B).
Proof.
  intros A B.
  intro h.
  destruct h as [a nb].
  unfold Negation in nb |- *.
  intro ab.
  apply nb.
  apply ab.
  exact a.
Qed.

Theorem negation_specification
  : forall (A : Prop) (B : Prop), ~ (A -/> B) <-> (A -> ~ ~ B).
Proof.
  intros A B.
  split.
  - intro h.
    unfold Negation in h |- *.
    intro a.
    intro nb.
    apply h.
    split.
    + exact a.
    + exact nb.
  - unfold Negation in |- *.
    intro f.
    intro h.
    destruct h as [a nb].
    apply f.
    + exact a.
    + exact nb.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop},
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 -/> B1 <-> A2 -/> B2).
Proof.
  intros A1 A2 B1 B2.
  intro ea.
  intro eb.
  destruct ea as [a12 a21].
  destruct eb as [b12 b21].
  split; intro h.
  - destruct h as [a1 nb1].
    split.
    + apply a12.
      exact a1.
    + unfold Negation in nb1 |- *.
      intro b2.
      apply nb1.
      apply b21.
      exact b2.
  - destruct h as [a2 nb2].
    split.
    + apply a21.
      exact a2.
    + unfold Negation in nb2 |- *.
      intro b1.
      apply nb2.
      apply b12.
      exact b1.
Qed.

End Abjunction.

(* The same incompatibility read from the implication's side belongs to
 * [Implication], but it can be stated only here, where [-/>] is known. A
 * second module of that name carries it, and a client reads
 * [Implication.abjunction_incompatibility].
 *)
Module Implication.

Theorem abjunction_incompatibility
  : forall {A : Prop} {B : Prop}, (A -> B) -> ~ (A -/> B).
Proof.
  intros A B.
  intro ab.
  unfold Negation in |- *.
  intro h.
  destruct h as [a nb].
  unfold Negation in nb.
  apply nb.
  apply ab.
  exact a.
Qed.

End Implication.
