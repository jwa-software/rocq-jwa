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

(* [disjoin a, _] : [A \/ B] from [a : A], and [disjoin _, b] from [b : B];
 * the side written [_] comes from the expected type.
 *)
Notation "'disjoin' a , '_'" := (Disjunction_introduction_left a) (only parsing).
Notation "'disjoin' '_' , b" := (Disjunction_introduction_right b) (only parsing).

(* A module may carry the type's name; its laws read
 * [Disjunction.commutativity].
 *)
Module Disjunction. (* Disjunction *)

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
  - ipso (disjoin _, a).
  - ipso (disjoin b, _).
Qed.

Theorem associativity
  : forall (A : Prop) (B : Prop) (C : Prop) . (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  intros A B C.
  divide et impera.
  - intro h.
    match h with | ab | c end.
    + match ab with | a | b end.
      * ipso (disjoin a, _).
      * ipso (disjoin _, (disjoin b, _)).
    + ipso (disjoin _, (disjoin _, c)).
  - intro h.
    match h with | a | bc end.
    + ipso (disjoin (disjoin a, _), _).
    + match bc with | b | c end.
      * ipso (disjoin (disjoin _, b), _).
      * ipso (disjoin _, c).
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
      * ipso (disjoin a, _).
      * ipso (disjoin a, _).
    + match bc with | b c end.
      divide et impera.
      * ipso (disjoin _, b).
      * ipso (disjoin _, c).
  - intro h.
    match h  with | ab ac end.
    match ab with | a | b end.
    + ipso (disjoin a, _).
    + match ac with | a | c end.
      * ipso (disjoin a, _).
      * ipso (disjoin _, (conjoin b, c)).
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
      ipso (f (disjoin a, _)).
    + intro b.
      ipso (f (disjoin _, b)).
  - intro h.
    match h with | ac bc end.
    intro ab.
    match ab with | a | b end.
    + ipso (ac a).
    + ipso (bc b).
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
    + let proof a2 := a12 a1.
      ipso (disjoin a2, _).
    + let proof b2 := b12 b1.
      ipso (disjoin _, b2).
  - (* [h : A2 \/ B2]: [|- A1 \/ B1] *)
    match h with | a2 | b2 end.
    + let proof a1 := a21 a2.
      ipso (disjoin a1, _).
    + let proof b1 := b21 b2.
      ipso (disjoin _, b1).
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
    + ipso (disjoin (conjoin a, b), _).
    + ipso (disjoin _, (conjoin a, c)).
  - intro h.
    match h with | ab | ac end.
    + match ab with | a b end.
      divide et impera.
      * ipso a.
      * ipso (disjoin b, _).
    + match ac with | a c end.
      divide et impera.
      * ipso a.
      * ipso (disjoin _, c).
Qed.

End over. (* distributivity.over *)

End distributivity. (* distributivity *)

End Conjunction. (* Conjunction *)
