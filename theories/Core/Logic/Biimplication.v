(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

Inductive Biimplication (P : Prop) (Q : Prop) : Prop :=
  | Biimplication_introduction : (P -> Q) -> (Q -> P) -> Biimplication P Q.

Arguments Biimplication_introduction {P} {Q} forward backward.

Notation "P <-> Q" := (Biimplication P Q)
  : jwa_type_scope.

(* A module may carry the type's name; its laws read
 * [Biimplication.symmetry].
 *)
Module Biimplication.

Theorem reflexivity : forall (P : Prop) . P <-> P.
Proof.
  intro P.
  split; intro p; exact p.
Qed.

Theorem symmetry
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  intro h.
  destruct h as [pq qp].
  split.
  - exact qp.
  - exact pq.
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
    exact p.
  - intro r.
    apply qp.
    apply rq.
    exact r.
Qed.

Theorem forward_elimination
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> P -> Q.
Proof.
  intros P Q.
  intro e.
  destruct e as [pq qp].
  exact pq.
Qed.

Theorem backward_elimination
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> Q -> P.
Proof.
  intros P Q.
  intro e.
  destruct e as [pq qp].
  exact qp.
Qed.

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
    exact p2.
  +
    intro q2.
    apply p12.
    apply qp.
    apply q21.
    exact q2.
  +
    intro p1.
    apply q21.
    apply pq.
    apply p12.
    exact p1.
  +
    intro q1.
    apply p21.
    apply qp.
    apply q12.
    exact q1.
Qed.

(* [Biimplication.sejunction_incompatibility] is stated in
 * [Core.Logic.Sejunction], the lowest file that knows both connectives, in
 * a second module of this name.
 *)

End Biimplication.

(* [->elim h p] and [<-elim h q] run [h : P <-> Q] forward and backward, as
 * [Biimplication.forward_elimination] and [backward_elimination]. Not to be
 * confused with [->E] and [<-E] in [Core.Logic.Implication], which are
 * modus ponens.
 *)
Notation "->elim" := Biimplication.forward_elimination (only parsing).
Notation "<-elim" := Biimplication.backward_elimination (only parsing).

(* The congruence of [->] belongs to [Implication], but its statement needs
 * [<->], so it can be stated only here. A second module of that name
 * carries it, and a client reads [Implication.congruence].
 *)
Module Implication.

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
    exact p2.
  - intro p1.
    apply q21.
    apply f.
    apply p12.
    exact p1.
Qed.

End Implication.
