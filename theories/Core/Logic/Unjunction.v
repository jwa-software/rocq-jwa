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

Lemma De_Morgan_Disjunction_forward
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

Lemma De_Morgan_Disjunction_backward
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

Theorem De_Morgan_Disjunction
  : forall (A : Prop) (B : Prop),
      (~ (A \/ B) -> ~ A /\ ~ B) /\ (~ A /\ ~ B -> ~ (A \/ B)).
Proof.
  (* The context gains [A] and [B]:
     [|- (~ (A \/ B) -> ~ A /\ ~ B) /\ (~ A /\ ~ B -> ~ (A \/ B))] *)
  intros A B.
  (* The goal splits into two goals: [|- ~ (A \/ B) -> ~ A /\ ~ B] and
     [|- ~ A /\ ~ B -> ~ (A \/ B)]. *)
  split.
  - (* [De_Morgan_Disjunction_forward A B] is a proof of the goal as it
       stands. *)
    exact (De_Morgan_Disjunction_forward A B).
  - (* [De_Morgan_Disjunction_backward A B] is a proof of the goal as it
       stands. *)
    exact (De_Morgan_Disjunction_backward A B).
Qed.

(* Only this direction of the law for [Conjunction] is a theorem here. Its
   converse, [~ (A /\ B) -> ~ A \/ ~ B], has to pick a ctor of [~ A \/ ~ B],
   and which one is right depends on whether [A] holds; no term decides
   that. *)
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
