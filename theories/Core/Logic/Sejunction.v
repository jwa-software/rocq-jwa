(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Abjunction.
From jwa Require Import Core.Logic.Bijunction.

(* Sejunction is exclusive disjunction: one side holds and the other does
 * not. [Theorem t : Verum _\/_ Verum.] is accepted and [Proof.] opens, but no
 * step reaches [Qed.]: either ctor demands [~ Verum], and no term has that
 * type. Being writable does not make a statement provable.
 *)
Inductive Sejunction (A : Prop) (B : Prop) : Prop :=
  | Sejunction_left  : A -> ~ B -> Sejunction A B
  | Sejunction_right : ~ A -> B -> Sejunction A B.

Arguments Sejunction_left  {A} {B} a  nb.
Arguments Sejunction_right {A} {B} na b.

Notation "A _\/_ B" := (Sejunction A B)
  : jwa_type_scope.

Theorem Sejunction_commutativity
  : forall (A : Prop) (B : Prop), A _\/_ B -> B _\/_ A.
Proof.
  intros A B.
  intro h.
  (* [Sejunction] has two ctors with two fields each,
   * so [h] gives two same goals with different contexts:
   * - one with [a : A]    and [nb : ~ B],
   * - one with [na : ~ A] and [b : B].
   *)
  destruct h as [a nb | na b].
  - exact (Sejunction_right nb  a).
  - exact (Sejunction_left   b na).
Qed.

Lemma Sejunction_as_abjunctions_forward
  : forall (A : Prop) (B : Prop), A _\/_ B -> (A -/> B) \/ (B -/> A).
Proof.
  intros A B.
  intro h.
  destruct h as [a nb | na b].
  - apply Disjunction.left.
    split.
    + exact a.
    + exact nb.
  - apply Disjunction.right.
    split.
    + exact b.
    + exact na.
Qed.

Lemma Sejunction_as_abjunctions_backward
  : forall (A : Prop) (B : Prop), (A -/> B) \/ (B -/> A) -> A _\/_ B.
Proof.
  intros A B.
  intro h.
  destruct h as [ab | ba].
  - destruct ab as [a nb].
    exact (Sejunction_left a nb).
  - destruct ba as [b na].
    exact (Sejunction_right na b).
Qed.

Theorem Sejunction_as_abjunctions
  : forall (A : Prop) (B : Prop), A _\/_ B <-> (A -/> B) \/ (B -/> A).
Proof.
  intros A B.
  split.
  - exact (Sejunction_as_abjunctions_forward  A B).
  - exact (Sejunction_as_abjunctions_backward A B).
Qed.

Lemma Sejunction_as_disjunction_without_conjunction_forward
  : forall (A : Prop) (B : Prop), A _\/_ B -> (A \/ B) /\ ~ (A /\ B).
Proof.
  intros A B.
  intro h.
  destruct h as [a nb | na b]; split.
  + exact (Disjunction.left a).
  + unfold Negation in nb |- *.
    intro ab.
    destruct ab as [_ b].
    exact (nb b).
  + exact (Disjunction.right b).
  + unfold Negation in na |- *.
    intro ab.
    destruct ab as [a _].
    exact (na a).
Qed.

Lemma Sejunction_as_disjunction_without_conjunction_backward
  : forall (A : Prop) (B : Prop), (A \/ B) /\ ~ (A /\ B) -> A _\/_ B.
Proof.
  intros A B.
  intro h.
  destruct h as [ab nab].
  unfold Negation in nab.
  destruct ab as [a | b].
  - apply Sejunction_left.
    + exact a.
    + unfold Negation in |- *.
      intro b.
      apply nab.
      split.
      * exact a.
      * exact b.
  - apply Sejunction_right.
    + unfold Negation in |- *.
      intro a.
      apply nab.
      split.
      * exact a.
      * exact b.
    + exact b.
Qed.

Theorem Sejunction_as_disjunction_without_conjunction
  : forall (A : Prop) (B : Prop), A _\/_ B <-> (A \/ B) /\ ~ (A /\ B).
Proof.
  intros A B.
  split.
  - exact (Sejunction_as_disjunction_without_conjunction_forward  A B).
  - exact (Sejunction_as_disjunction_without_conjunction_backward A B).
Qed.

Theorem Sejunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2).
Proof.
  intros A1 A2 B1 B2.
  intro ea.
  intro eb.
  destruct ea as [a12 a21].
  destruct eb as [b12 b21].
  split; intro h.
  - destruct h as [a1 nb1 | na1 b1].
    + apply Sejunction_left.
      * apply a12.
        exact a1.
      * unfold Negation in nb1 |- *.
        intro b2.
        apply nb1.
        apply b21.
        exact b2.
    + apply Sejunction_right.
      * unfold Negation in na1 |- *.
        intro a2.
        apply na1.
        apply a21.
        exact a2.
      * apply b12.
        exact b1.
  - destruct h as [a2 nb2 | na2 b2].
    + apply Sejunction_left.
      * apply a21.
        exact a2.
      * unfold Negation in nb2 |- *.
        intro b1.
        apply nb2.
        apply b12.
        exact b1.
    + apply Sejunction_right.
      * unfold Negation in na2 |- *.
        intro a1.
        apply na2.
        apply a12.
        exact a1.
      * apply b21.
        exact b2.
Qed.

Theorem Sejunction_implies_Disjunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> A \/ B.
Proof.
  intros A B.
  intro h.
  destruct h as [a nb | na b].
  - exact (Disjunction.left  a).
  - exact (Disjunction.right b).
Qed.

Theorem Sejunction_refutes_Conjunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> ~ (A /\ B).
Proof.
  intros A B.
  intro h.
  unfold Negation in |- *.
  intro ab.
  destruct ab as [a b].
  destruct h  as [_ nb | na _].
  - exact (nb b).
  - exact (na a).
Qed.

Theorem Bijunction_refutes_Sejunction
  : forall (A : Prop) (B : Prop), (A <-> B) -> ~ (A _\/_ B).
Proof.
  intros A B.
  intro e.
  destruct e as [ab ba].
  unfold Negation in |- *.
  intro h.
  destruct h as [a nb | na b].
  - unfold Negation in nb.
    apply nb.
    apply ab.
    exact a.
  - unfold Negation in na.
    apply na.
    apply ba.
    exact b.
Qed.

Theorem Sejunction_refutes_Bijunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> ~ (A <-> B).
Proof.
  intros A B.
  intro h.
  unfold Negation in |- *.
  intro e.
  destruct e as [ab ba].
  destruct h as [a nb | na b].
  - unfold Negation in nb.
    apply nb.
    apply ab.
    exact a.
  - unfold Negation in na.
    apply na.
    apply ba.
    exact b.
Qed.
