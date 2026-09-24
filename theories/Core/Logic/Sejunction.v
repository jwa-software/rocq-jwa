(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Abjunction.
From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Sejunction is exclusive disjunction: one side holds and the other does
 * not. [Theorem t : Verum _\/_ Verum.] is accepted and [Proof.] opens, but no
 * step reaches [Qed.]: either ctor demands [~ Verum], and no term has that
 * type. Being writable does not make a statement provable.
 *)
Inductive Sejunction (A : Prop) (B : Prop) : Prop :=
  | Sejunction_introduction_left  : A -> ~ B -> Sejunction A B
  | Sejunction_introduction_right : ~ A -> B -> Sejunction A B.

Arguments Sejunction_introduction_left  {A} {B} a  nb.
Arguments Sejunction_introduction_right {A} {B} na b.

Notation "A _\/_ B" := (Sejunction A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Sejunction.commutativity].
 *)
Module Sejunction. (* Sejunction *)

(* The two ctors under the names a proof writes: [Sejunction.left a nb] and
 * [Sejunction.right na b]. An abbreviation is the ctor itself, so it also
 * serves as a pattern; Rocq prints the ctor's own name.
 *)
Abbreviation left  := Sejunction_introduction_left.
Abbreviation right := Sejunction_introduction_right.
Abbreviation L     := Sejunction_introduction_left  (only parsing).
Abbreviation R     := Sejunction_introduction_right (only parsing).

Theorem commutativity
  : forall {A : Prop} {B : Prop} . A _\/_ B -> B _\/_ A.
Proof.
  intros A B.
  intro h.
  (* [Sejunction] has two ctors with two fields each,
   * so [h] gives two same goals with different contexts:
   * - one with [a : A]    and [nb : ~ B],
   * - one with [na : ~ A] and [b : B].
   *)
  match h with | a nb | na b end.
  - ipso (Sejunction.right nb  a).
  - ipso (Sejunction.left   b na).
Qed.

Module decomposition. (* decomposition *)

Module into. (* decomposition.into *)

(* A sejunction is one of the two abjunctions: the left side without the
 * right, or the right side without the left.
 *)
(* decomposition.into.abjunction *)
Theorem abjunction
  : forall (A : Prop) (B : Prop) . A _\/_ B <-> (A -/> B) \/ (B -/> A).
Proof.
  intros A B.
  divide et impera.
  - intro h.
    match h with | a nb | na b end.
    + apply Disjunction.left.
      divide et impera.
      * ipso a.
      * ipso nb.
    + apply Disjunction.right.
      divide et impera.
      * ipso b.
      * ipso na.
  - intro h.
    match h with | ab | ba end.
    + match ab with | a nb end.
      ipso (Sejunction.left a nb).
    + match ba with | b na end.
      ipso (Sejunction.right na b).
Qed.

End into. (* decomposition.into *)

End decomposition. (* decomposition *)

(* The textbook definition of exclusive disjunction, as a theorem: one of
 * the two holds, and not both.
 *)
Theorem specification
  : forall (A : Prop) (B : Prop) . A _\/_ B <-> (A \/ B) /\ ~ (A /\ B).
Proof.
  intros A B.
  divide et impera.
  - intro h.
    match h with | a nb | na b end; divide et impera.
    + ipso (Disjunction.left a).
    + unfold Negation in nb |- *.
      intro ab.
      match ab with | _ b end.
      ipso (nb b).
    + ipso (Disjunction.right b).
    + unfold Negation in na |- *.
      intro ab.
      match ab with | a _ end.
      ipso (na a).
  - intro h.
    match h with | ab nab end.
    unfold Negation in nab.
    match ab with | a | b end.
    + apply Sejunction.left.
      * ipso a.
      * unfold Negation in |- *.
        intro b.
        apply nab.
        divide et impera.
        { ipso a. }
        { ipso b. }
    + apply Sejunction.right.
      * unfold Negation in |- *.
        intro a.
        apply nab.
        divide et impera.
        { ipso a. }
        { ipso b. }
      * ipso b.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2).
Proof.
  intros A1 A2 B1 B2.
  intro ea.
  intro eb.
  match ea with | a12 a21 end.
  match eb with | b12 b21 end.
  divide et impera; intro h.
  - match h with | a1 nb1 | na1 b1 end.
    + apply Sejunction.left.
      * ipso (a12 a1).
      * unfold Negation in nb1 |- *.
        intro b2.
        let proof b1 := b21 b2.
        let proof facto := nb1 b1.
        ipso facto.
    + apply Sejunction.right.
      * unfold Negation in na1 |- *.
        intro a2.
        let proof a1 := a21 a2.
        let proof facto := na1 a1.
        ipso facto.
      * ipso (b12 b1).
  - match h with | a2 nb2 | na2 b2 end.
    + apply Sejunction.left.
      * ipso (a21 a2).
      * unfold Negation in nb2 |- *.
        intro b1.
        let proof b2 := b12 b1.
        let proof facto := nb2 b2.
        ipso facto.
    + apply Sejunction.right.
      * unfold Negation in na2 |- *.
        intro a1.
        let proof a2 := a12 a1.
        let proof facto := na2 a2.
        ipso facto.
      * ipso (b21 b2).
Qed.

Module weakening. (* weakening *)

Module to. (* weakening.to *)

(* A sejunction is a disjunction that has forgotten which side fails. *)
(* weakening.to.disjunction *)
Theorem disjunction
  : forall {A : Prop} {B : Prop} . A _\/_ B -> A \/ B.
Proof.
  intros A B.
  intro h.
  match h with | a nb | na b end.
  - ipso (Disjunction.left  a).
  - ipso (Disjunction.right b).
Qed.

End to. (* weakening.to *)

End weakening. (* weakening *)

(* Two propositions are incompatible when they cannot both hold. A
 * sejunction is incompatible with the conjunction of its sides and with
 * their biconditional.
 *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* exclusion.of.conjunction *)
Theorem conjunction
  : forall {A : Prop} {B : Prop} . A _\/_ B -> ~ (A /\ B).
Proof.
  intros A B.
  intro h.
  unfold Negation in |- *.
  intro ab.
  match ab with | a b end.
  match h  with | _ nb | na _ end.
  - ipso (nb b).
  - ipso (na a).
Qed.

(* exclusion.of.biconditional *)
Theorem biconditional
  : forall {A : Prop} {B : Prop} . A _\/_ B -> ~ (A <-> B).
Proof.
  intros A B.
  intro h.
  unfold Negation in |- *.
  intro e.
  match e with | ab ba end.
  match h with | a nb | na b end.
  - unfold Negation in nb.
    let proof b := ab a.
    let proof facto := nb b.
    ipso facto.
  - unfold Negation in na.
    let proof a := ba b.
    let proof facto := na a.
    ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

End Sejunction. (* Sejunction *)

(* The same incompatibility read from the biconditional's side belongs to
 * [Biconditional], but it can be stated only here, where [_\/_] is known. A
 * second module of that name carries it, and a client reads
 * [Biconditional.exclusion.of.sejunction].
 *)
Module Biconditional. (* Biconditional *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* exclusion.of.sejunction *)
Theorem sejunction
  : forall {A : Prop} {B : Prop} . (A <-> B) -> ~ (A _\/_ B).
Proof.
  intros A B.
  intro e.
  match e with | ab ba end.
  unfold Negation in |- *.
  intro h.
  match h with | a nb | na b end.
  - unfold Negation in nb.
    let proof b := ab a.
    let proof facto := nb b.
    ipso facto.
  - unfold Negation in na.
    let proof a := ba b.
    let proof facto := na a.
    ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

End Biconditional. (* Biconditional *)
