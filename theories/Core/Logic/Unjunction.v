(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Conjunction] and
   [Core.Logic.Disjunction] the two connectives the laws below relate. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Falsum.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.

(* Unjunction is negation: a proof of [A] leads to [Falsum]. *)
(* [Prop -> Prop] *)
Definition Unjunction := fun (A : Prop) => A -> Falsum.

Notation "~ A" := (Unjunction A) : jwa_type_scope.

(* De Morgan's laws. [Unjunction] is a definition, so each proof unfolds it
   first and the arrows underneath show; a negation is then introduced and
   its argument refuted. *)

Theorem De_Morgan_Disjunction
  : forall (A : Prop) (B : Prop), ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  (* The context gains [A] and [B]: [|- ~ (A \/ B) -> ~ A /\ ~ B] *)
  intros A B.
  (* [|- (A \/ B -> Falsum) -> (A -> Falsum) /\ (B -> Falsum)] *)
  unfold Unjunction in |- *.
  (* The context gains [h : A \/ B -> Falsum]:
     [|- (A -> Falsum) /\ (B -> Falsum)] *)
  intro h.
  (* The goal splits into two goals: [|- A -> Falsum] and [|- B -> Falsum]. *)
  split.
  - (* The context gains [a : A]: [|- Falsum] *)
    intro a.
    (* [h] turns a proof of [A \/ B] into a proof of [Falsum]: [|- A \/ B] *)
    apply h.
    (* [a] is the left side of [A \/ B]. *)
    exact (Disjunction_left a).
  - (* The context gains [b : B]: [|- Falsum] *)
    intro b.
    (* [h] turns a proof of [A \/ B] into a proof of [Falsum]: [|- A \/ B] *)
    apply h.
    (* [b] is the right side of [A \/ B]. *)
    exact (Disjunction_right b).
Qed.

Theorem De_Morgan_Disjunction_backward
  : forall (A : Prop) (B : Prop), ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  (* The context gains [A] and [B]: [|- ~ A /\ ~ B -> ~ (A \/ B)] *)
  intros A B.
  (* [|- (A -> Falsum) /\ (B -> Falsum) -> A \/ B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [h : (A -> Falsum) /\ (B -> Falsum)]:
     [|- A \/ B -> Falsum] *)
  intro h.
  (* [h] splits into [not_a : A -> Falsum] and [not_b : B -> Falsum]. *)
  destruct h as [not_a not_b].
  (* The context gains [ab : A \/ B]: [|- Falsum] *)
  intro ab.
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [not_a] turns [a] into a proof of [Falsum]. *)
    exact (not_a a).
  - (* [not_b] turns [b] into a proof of [Falsum]. *)
    exact (not_b b).
Qed.

Theorem De_Morgan_Conjunction
  : forall (A : Prop) (B : Prop), ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  (* The context gains [A] and [B]: [|- ~ A \/ ~ B -> ~ (A /\ B)] *)
  intros A B.
  (* [|- (A -> Falsum) \/ (B -> Falsum) -> A /\ B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [h : (A -> Falsum) \/ (B -> Falsum)]:
     [|- A /\ B -> Falsum] *)
  intro h.
  (* The context gains [ab : A /\ B]: [|- Falsum] *)
  intro ab.
  (* [ab] splits into [a : A] and [b : B]. *)
  destruct ab as [a b].
  (* [h] gives two goals: one with [not_a : A -> Falsum], one with
     [not_b : B -> Falsum]. *)
  destruct h as [not_a | not_b].
  - (* [not_a] turns [a] into a proof of [Falsum]. *)
    exact (not_a a).
  - (* [not_b] turns [b] into a proof of [Falsum]. *)
    exact (not_b b).
Qed.

(* Negation on its own: what [~] does to [Falsum], to a proposition, to its
   own iterations, and to an implication. Every proof unfolds [Unjunction]
   first, so the arrows show, and refutes the argument it is handed. *)

Theorem Unjunction_of_Falsum : ~ Falsum.
Proof.
  (* [|- Falsum -> Falsum] *)
  unfold Unjunction in |- *.
  intro f.
  exact f.
Qed.

Theorem Unjunction_twice : forall (A : Prop), A -> ~ ~ A.
Proof.
  (* The context gains [A]: [|- A -> ~ ~ A] *)
  intro A.
  (* The context gains [a : A]: [|- ~ ~ A] *)
  intro a.
  (* [|- (A -> Falsum) -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [not_a : A -> Falsum]: [|- Falsum] *)
  intro not_a.
  (* [not_a] turns [a] into a proof of [Falsum]. *)
  exact (not_a a).
Qed.

(* Two negations do not cancel here, but three collapse to one. *)
Theorem Unjunction_thrice : forall (A : Prop), ~ ~ ~ A -> ~ A.
Proof.
  (* The context gains [A]: [|- ~ ~ ~ A -> ~ A] *)
  intro A.
  (* [|- (((A -> Falsum) -> Falsum) -> Falsum) -> A -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [not_not_not_a : ((A -> Falsum) -> Falsum) -> Falsum]:
     [|- A -> Falsum] *)
  intro not_not_not_a.
  (* The context gains [a : A]: [|- Falsum] *)
  intro a.
  (* [not_not_not_a] turns a proof of [(A -> Falsum) -> Falsum] into a proof
     of [Falsum]: [|- (A -> Falsum) -> Falsum] *)
  apply not_not_not_a.
  (* The context gains [not_a : A -> Falsum]: [|- Falsum] *)
  intro not_a.
  (* [not_a] turns [a] into a proof of [Falsum]. *)
  exact (not_a a).
Qed.

Theorem Subjunction_contraposition
  : forall (A : Prop) (B : Prop), (A -> B) -> ~ B -> ~ A.
Proof.
  (* The context gains [A] and [B]: [|- (A -> B) -> ~ B -> ~ A] *)
  intros A B.
  (* [|- (A -> B) -> (B -> Falsum) -> A -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [ab : A -> B]: [|- (B -> Falsum) -> A -> Falsum] *)
  intro ab.
  (* The context gains [not_b : B -> Falsum]: [|- A -> Falsum] *)
  intro not_b.
  (* The context gains [a : A]: [|- Falsum] *)
  intro a.
  (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
  apply not_b.
  (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
  apply ab.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.
