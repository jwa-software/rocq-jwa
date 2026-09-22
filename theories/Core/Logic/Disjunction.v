(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

Inductive Disjunction (A : Prop) (B : Prop) : Prop :=
  | Disjunction_introduction_left  : A -> Disjunction A B
  | Disjunction_introduction_right : B -> Disjunction A B.

(* The unused side is not determined by the argument. It comes from the
 * expected type, and a use that has none needs
 * [@Disjunction_introduction_left].
 *)
Arguments Disjunction_introduction_left  {A} {B} a.
Arguments Disjunction_introduction_right {A} {B} b.

Notation "A \/ B" := (Disjunction A B)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Disjunction.commutativity].
 *)
Module Disjunction. (* Disjunction *)

(* The two ctors under the names a proof writes: [Disjunction.left a] and
 * [Disjunction.right b]. An abbreviation is the ctor itself, so it also
 * serves as a pattern; Rocq prints the ctor's own name.
 *)
Abbreviation left  := Disjunction_introduction_left.
Abbreviation right := Disjunction_introduction_right.
Abbreviation L     := Disjunction_introduction_left  (only parsing).
Abbreviation R     := Disjunction_introduction_right (only parsing).

Theorem commutativity
  : forall {A : Prop} {B : Prop} . A \/ B -> B \/ A.
Proof.
  intros A B.
  intro h.
  (* [Disjunction] has two ctors, so [h] gives two same goals with different contexts;
   * - one with [a : A],
   * - one with [b : B].
   *)
  destruct h as [a | b].
  - exact (right a).
  - exact (left  b).
Qed.

Theorem associativity
  : forall (A : Prop) (B : Prop) (C : Prop) . (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  intros A B C.
  split.
  - intro h.
    destruct h as [ab | c].
    + destruct ab as [a | b].
      * exact (Disjunction.left a).
      * exact (Disjunction.right (Disjunction.left b)).
    + exact (Disjunction.right (Disjunction.right c)).
  - intro h.
    destruct h as [a | bc].
    + exact (Disjunction.left (Disjunction.left a)).
    + destruct bc as [b | c].
      * exact (Disjunction.left (Disjunction.right b)).
      * exact (Disjunction.right c).
Qed.

Module distributivity. (* distributivity *)

Module over. (* distributivity.over *)

(* distributivity.over.conjunction *)
Theorem conjunction
  : forall (A : Prop) (B : Prop) (C : Prop) . A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split.
  - intro h.
    destruct h as [a | bc].
    + split.
      * exact (Disjunction.left a).
      * exact (Disjunction.left a).
    + destruct bc as [b c].
      split.
      * exact (Disjunction.right b).
      * exact (Disjunction.right c).
  - intro h.
    destruct h  as [ab ac].
    destruct ab as [a | b].
    + exact (Disjunction.left a).
    + destruct ac as [a | c].
      * exact (Disjunction.left a).
      * apply Disjunction.right.
        split.
        { exact b. }
        { exact c. }
Qed.

End over. (* distributivity.over *)

End distributivity. (* distributivity *)

(* The universal property of [\/] as a coproduct: a proof of [C] from
 * [A \/ B] is a pair of proofs of [C], one from [A] and one from [B]. It is
 * the dual of [Conjunction.universality].
 *)
Theorem universality
  : forall (A : Prop) (B : Prop) (C : Prop) . (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  intros A B C.
  split.
  - intro f.
    split.
    + intro a.
      apply f.
      exact (Disjunction.left a).
    + intro b.
      apply f.
      exact (Disjunction.right b).
  - intro h.
    destruct h as [ac bc].
    intro ab.
    destruct ab as [a | b].
    + apply ac.
      exact a.
    + apply bc.
      exact b.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2).
Proof.
  intros A1 A2 B1 B2.
  intro a.
  intro b.
  destruct a as [a12 a21].
  destruct b as [b12 b21].
  split; intro h.
  - (* [h : A1 \/ B1]: [|- A2 \/ B2] *)
    destruct h as [a1 | b1].
    + (* [|- A2] *)
      apply Disjunction.left.
      apply a12.
      exact a1.
    + (* [|- B2] *)
      apply Disjunction.right.
      apply b12.
      exact b1.
  - (* [h : A2 \/ B2]: [|- A1 \/ B1] *)
    destruct h as [a2 | b2].
    + (* [|- A1] *)
      apply Disjunction.left.
      apply a21.
      exact a2.
    + (* [|- B1] *)
      apply Disjunction.right.
      apply b21.
      exact b2.
Qed.

End Disjunction. (* Disjunction *)

(* The law of [/\] over [\/] belongs to [Conjunction], but it can be stated
 * only here, the lowest file that knows both connectives. A module cannot
 * be reopened across files; a second module of the same name continues
 * it, and a client reads [Conjunction.distributivity.over.disjunction]
 * under one prefix with the laws of [Core.Logic.Conjunction].
 *)
Module Conjunction. (* Conjunction *)

Module distributivity. (* distributivity *)

Module over. (* distributivity.over *)

(* distributivity.over.disjunction *)
Theorem disjunction
  : forall (A : Prop) (B : Prop) (C : Prop) . A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.
  - intro h.
    destruct h as [a bc].
    destruct bc as [b | c].
    + (* [|- A /\ B] *)
      apply Disjunction.left.
      split.
      * exact a.
      * exact b.
    + (* [|- A /\ C] *)
      apply Disjunction.right.
      split.
      * exact a.
      * exact c.
  - intro h.
    destruct h as [ab | ac].
    + destruct ab as [a b].
      split.
      * exact a.
      * exact (Disjunction.left b).
    + destruct ac as [a c].
      split.
      * exact a.
      * exact (Disjunction.right c).
Qed.

End over. (* distributivity.over *)

End distributivity. (* distributivity *)

End Conjunction. (* Conjunction *)
