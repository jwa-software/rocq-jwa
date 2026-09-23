(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

Inductive Biconditional (P : Prop) (Q : Prop) : Prop :=
  | Biconditional_introduction : (P -> Q) -> (Q -> P) -> Biconditional P Q.

Arguments Biconditional_introduction {P} {Q} forward backward.

Notation "P <-> Q" := (Biconditional P Q)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Biconditional.symmetry].
 *)
Module Biconditional. (* Biconditional *)

Theorem reflexivity : forall (P : Prop) . P <-> P.
Proof.
  intro P.
  split; intro p; ipso p.
Qed.

Theorem symmetry
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  intro h.
  destruct h as [pq qp].
  split.
  - ipso qp.
  - ipso pq.
Qed.

Theorem transitivity
  : forall {P : Prop} {Q : Prop} {R : Prop} .
      (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q C.
  intro hpq.
  intro hqr.
  destruct hpq as [pq qp].
  destruct hqr as [qr rq].
  split.
  - intro p.
    apply qr.
    apply pq.
    ipso p.
  - intro r.
    apply qp.
    apply rq.
    ipso r.
Qed.

Module forward. (* forward *)

(* forward.elimination *)
Theorem elimination
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> P -> Q.
Proof.
  intros P Q.
  intro e.
  destruct e as [pq qp].
  ipso pq.
Qed.

End forward. (* forward *)

Module backward. (* backward *)

(* backward.elimination *)
Theorem elimination
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> Q -> P.
Proof.
  intros P Q.
  intro e.
  destruct e as [pq qp].
  ipso qp.
Qed.

End backward. (* backward *)

Theorem congruence
  : forall {P1 : Prop} {P2 : Prop} {Q1 : Prop} {Q2 : Prop} .
      (P1 <-> P2) -> (Q1 <-> Q2) -> ((P1 <-> Q1) <-> (P2 <-> Q2)).
Proof.
  intros P1 P2 Q1 Q2.
  intro a.
  intro b.
  destruct a as [p12 p21].
  destruct b as [q12 q21].
  split; intro e; destruct e as [pq qp]; split.
  +
    intro p2.
    apply q12.
    apply pq.
    apply p21.
    ipso p2.
  +
    intro q2.
    apply p12.
    apply qp.
    apply q21.
    ipso q2.
  +
    intro p1.
    apply q21.
    apply pq.
    apply p12.
    ipso p1.
  +
    intro q1.
    apply p21.
    apply qp.
    apply q12.
    ipso q1.
Qed.

(* [Biconditional.exclusion.of.sejunction] is stated in
 * [Core.Logic.Sejunction], the lowest file that knows both connectives, in
 * a second module of this name.
 *)

End Biconditional. (* Biconditional *)

(* The congruence of [->] belongs to [Conditional], but its statement needs
 * [<->], so it can be stated only here. A second module of that name
 * carries it, and a client reads [Conditional.congruence].
 *)
Module Conditional. (* Conditional *)

Theorem congruence
  : forall {P1 : Prop} {P2 : Prop} {Q1 : Prop} {Q2 : Prop} .
      (P1 <-> P2) -> (Q1 <-> Q2) -> ((P1 -> Q1) <-> (P2 -> Q2)).
Proof.
  intros P1 P2 Q1 Q2.
  intro a.
  intro b.
  destruct a as [p12 p21].
  destruct b as [q12 q21].
  split; intro f.
  - intro p2.
    apply q12.
    apply f.
    apply p21.
    ipso p2.
  - intro p1.
    apply q21.
    apply f.
    apply p12.
    ipso p1.
Qed.

End Conditional. (* Conditional *)
