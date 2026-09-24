(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

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
  match h with | a | b end.
  - ipso (right a).
  - ipso (left  b).
Qed.

Theorem associativity
  : forall (A : Prop) (B : Prop) (C : Prop) . (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  intros A B C.
  divide et impera.
  - intro h.
    match h with | ab | c end.
    + match ab with | a | b end.
      * ipso (Disjunction.left a).
      * ipso (Disjunction.right (Disjunction.left b)).
    + ipso (Disjunction.right (Disjunction.right c)).
  - intro h.
    match h with | a | bc end.
    + ipso (Disjunction.left (Disjunction.left a)).
    + match bc with | b | c end.
      * ipso (Disjunction.left (Disjunction.right b)).
      * ipso (Disjunction.right c).
Qed.

Module distributivity. (* distributivity *)

Module over. (* distributivity.over *)

(* distributivity.over.conjunction *)
Theorem conjunction
  : forall (A : Prop) (B : Prop) (C : Prop) . A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  divide et impera.
  - intro h.
    match h with | a | bc end.
    + divide et impera.
      * ipso (Disjunction.left a).
      * ipso (Disjunction.left a).
    + match bc with | b c end.
      divide et impera.
      * ipso (Disjunction.right b).
      * ipso (Disjunction.right c).
  - intro h.
    match h  with | ab ac end.
    match ab with | a | b end.
    + ipso (Disjunction.left a).
    + match ac with | a | c end.
      * ipso (Disjunction.left a).
      * apply Disjunction.right.
        divide et impera.
        { ipso b. }
        { ipso c. }
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
  divide et impera.
  - intro f.
    divide et impera.
    + intro a.
      apply f.
      ipso (Disjunction.left a).
    + intro b.
      apply f.
      ipso (Disjunction.right b).
  - intro h.
    match h with | ac bc end.
    intro ab.
    match ab with | a | b end.
    + apply ac.
      ipso a.
    + apply bc.
      ipso b.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2).
Proof.
  intros A1 A2 B1 B2.
  intro a.
  intro b.
  match a with | a12 a21 end.
  match b with | b12 b21 end.
  divide et impera; intro h.
  - (* [h : A1 \/ B1]: [|- A2 \/ B2] *)
    match h with | a1 | b1 end.
    + (* [|- A2] *)
      apply Disjunction.left.
      apply a12.
      ipso a1.
    + (* [|- B2] *)
      apply Disjunction.right.
      apply b12.
      ipso b1.
  - (* [h : A2 \/ B2]: [|- A1 \/ B1] *)
    match h with | a2 | b2 end.
    + (* [|- A1] *)
      apply Disjunction.left.
      apply a21.
      ipso a2.
    + (* [|- B1] *)
      apply Disjunction.right.
      apply b21.
      ipso b2.
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
  divide et impera.
  - intro h.
    match h with | a bc end.
    match bc with | b | c end.
    + (* [|- A /\ B] *)
      apply Disjunction.left.
      divide et impera.
      * ipso a.
      * ipso b.
    + (* [|- A /\ C] *)
      apply Disjunction.right.
      divide et impera.
      * ipso a.
      * ipso c.
  - intro h.
    match h with | ab | ac end.
    + match ab with | a b end.
      divide et impera.
      * ipso a.
      * ipso (Disjunction.left b).
    + match ac with | a c end.
      divide et impera.
      * ipso a.
      * ipso (Disjunction.right c).
Qed.

End over. (* distributivity.over *)

End distributivity. (* distributivity *)

End Conjunction. (* Conjunction *)
