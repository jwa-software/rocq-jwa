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
  divide et impera; intro p; ipso p.
Qed.

Theorem symmetry
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  intro h.
  match h with | pq qp end.
  divide et impera.
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
  match hpq with | pq qp end.
  match hqr with | qr rq end.
  divide et impera.
  - intro p.
    let proof q := pq p.
    let proof facto := qr q.
    ipso facto.
  - intro r.
    let proof q := rq r.
    let proof facto := qp q.
    ipso facto.
Qed.

Module forward. (* forward *)

(* forward.elimination *)
Theorem elimination
  : forall {P : Prop} {Q : Prop} . (P <-> Q) -> P -> Q.
Proof.
  intros P Q.
  intro e.
  match e with | pq qp end.
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
  match e with | pq qp end.
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
  match a with | p12 p21 end.
  match b with | q12 q21 end.
  divide et impera; intro e; match e with | pq qp end; divide et impera.
  +
    intro p2.
    let proof p1 := p21 p2.
    let proof q1 := pq p1.
    let proof facto := q12 q1.
    ipso facto.
  +
    intro q2.
    let proof q1 := q21 q2.
    let proof p1 := qp q1.
    let proof facto := p12 p1.
    ipso facto.
  +
    intro p1.
    let proof p2 := p12 p1.
    let proof q2 := pq p2.
    let proof facto := q21 q2.
    ipso facto.
  +
    intro q1.
    let proof q2 := q12 q1.
    let proof p2 := qp q2.
    let proof facto := p21 p2.
    ipso facto.
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
  match a with | p12 p21 end.
  match b with | q12 q21 end.
  divide et impera; intro f.
  - intro p2.
    let proof p1 := p21 p2.
    let proof q1 := f p1.
    let proof facto := q12 q1.
    ipso facto.
  - intro p1.
    let proof p2 := p12 p1.
    let proof q2 := f p2.
    let proof facto := q21 q2.
    ipso facto.
Qed.

End Conditional. (* Conditional *)
