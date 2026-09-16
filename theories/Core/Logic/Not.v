(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Conditional] carries [->], [Core.Logic.And] and
   [Core.Logic.Or] the two connectives the laws below relate. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.False.
From jwa Require Import Core.Logic.And.
From jwa Require Import Core.Logic.Or.

(* [Prop -> Prop] *)
Definition Not := fun (A : Prop) => A -> False.

Notation "~ A" := (Not A) : jwa_type_scope.

(* De Morgan's laws. [Not] is a definition, so each proof unfolds it first
   and the arrows underneath show; a negation is then introduced and its
   argument refuted. *)

Lemma De_Morgan_Or_forward
  : forall (A : Prop) (B : Prop), ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  (* The context gains [A] and [B]: [|- ~ (A \/ B) -> ~ A /\ ~ B] *)
  intros A B.
  (* [|- (A \/ B -> False) -> (A -> False) /\ (B -> False)] *)
  unfold Not in |- *.
  (* The context gains [h : A \/ B -> False]:
     [|- (A -> False) /\ (B -> False)] *)
  intro h.
  (* The goal splits into two goals: [|- A -> False] and [|- B -> False]. *)
  split.
  - (* The context gains [a : A]: [|- False] *)
    intro a.
    (* [h] turns a proof of [A \/ B] into a proof of [False]: [|- A \/ B] *)
    apply h.
    (* [a] is the left side of [A \/ B]. *)
    exact (Or_left a).
  - (* The context gains [b : B]: [|- False] *)
    intro b.
    (* [h] turns a proof of [A \/ B] into a proof of [False]: [|- A \/ B] *)
    apply h.
    (* [b] is the right side of [A \/ B]. *)
    exact (Or_right b).
Qed.

Lemma De_Morgan_Or_backward
  : forall (A : Prop) (B : Prop), ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  (* The context gains [A] and [B]: [|- ~ A /\ ~ B -> ~ (A \/ B)] *)
  intros A B.
  (* [|- (A -> False) /\ (B -> False) -> A \/ B -> False] *)
  unfold Not in |- *.
  (* The context gains [h : (A -> False) /\ (B -> False)]:
     [|- A \/ B -> False] *)
  intro h.
  (* [h] splits into [not_a : A -> False] and [not_b : B -> False]. *)
  destruct h as [not_a not_b].
  (* The context gains [ab : A \/ B]: [|- False] *)
  intro ab.
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [not_a] turns [a] into a proof of [False]. *)
    exact (not_a a).
  - (* [not_b] turns [b] into a proof of [False]. *)
    exact (not_b b).
Qed.

Theorem De_Morgan_Or
  : forall (A : Prop) (B : Prop),
      (~ (A \/ B) -> ~ A /\ ~ B) /\ (~ A /\ ~ B -> ~ (A \/ B)).
Proof.
  (* The context gains [A] and [B]:
     [|- (~ (A \/ B) -> ~ A /\ ~ B) /\ (~ A /\ ~ B -> ~ (A \/ B))] *)
  intros A B.
  (* The goal splits into two goals: [|- ~ (A \/ B) -> ~ A /\ ~ B] and
     [|- ~ A /\ ~ B -> ~ (A \/ B)]. *)
  split.
  - (* [De_Morgan_Or_forward A B] is a proof of the goal as it stands. *)
    exact (De_Morgan_Or_forward A B).
  - (* [De_Morgan_Or_backward A B] is a proof of the goal as it stands. *)
    exact (De_Morgan_Or_backward A B).
Qed.

(* Only this direction of the law for [And] is a theorem here. Its converse,
   [~ (A /\ B) -> ~ A \/ ~ B], has to pick a ctor of [~ A \/ ~ B], and which
   one is right depends on whether [A] holds; no term decides that. *)
Theorem De_Morgan_And
  : forall (A : Prop) (B : Prop), ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  (* The context gains [A] and [B]: [|- ~ A \/ ~ B -> ~ (A /\ B)] *)
  intros A B.
  (* [|- (A -> False) \/ (B -> False) -> A /\ B -> False] *)
  unfold Not in |- *.
  (* The context gains [h : (A -> False) \/ (B -> False)]:
     [|- A /\ B -> False] *)
  intro h.
  (* The context gains [ab : A /\ B]: [|- False] *)
  intro ab.
  (* [ab] splits into [a : A] and [b : B]. *)
  destruct ab as [a b].
  (* [h] gives two goals: one with [not_a : A -> False], one with
     [not_b : B -> False]. *)
  destruct h as [not_a | not_b].
  - (* [not_a] turns [a] into a proof of [False]. *)
    exact (not_a a).
  - (* [not_b] turns [b] into a proof of [False]. *)
    exact (not_b b).
Qed.
