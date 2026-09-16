(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Conditional] carries [->], [Core.Logic.And]
   carries [/\]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.And.

Inductive Or (A : Prop) (B : Prop) : Prop :=
  | Or_left  : A -> Or A B
  | Or_right : B -> Or A B.

(* The unused side is not determined by the argument. It comes from the
   expected type, and a use that has none needs [@Or_left]. *)
Arguments Or_left  {A} {B} a.
Arguments Or_right {A} {B} b.

Notation "A \/ B" := (Or A B) : jwa_type_scope.

(* The laws are implications, as in [Core.Logic.And]. A proof of a
   disjunction is one ctor applied to one side, so each case below is a
   single [exact]. *)

Theorem Or_commutativity : forall (A : Prop) (B : Prop), A \/ B -> B \/ A.
Proof.
  (* The context gains [A] and [B]: [|- A \/ B -> B \/ A] *)
  intros A B.
  (* The context gains [h : A \/ B]: [|- B \/ A] *)
  intro h.
  (* [Or] has two ctors, so [h] gives two goals: one with [a : A], one with
     [b : B]. *)
  destruct h as [a | b].
  - (* [a] is the right side of [B \/ A]. *)
    exact (Or_right a).
  - (* [b] is the left side of [B \/ A]. *)
    exact (Or_left b).
Qed.

Lemma Or_associativity_forward
  : forall (A : Prop) (B : Prop) (C : Prop), (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A \/ B) \/ C -> A \/ (B \/ C)] *)
  intros A B C.
  (* The context gains [h : (A \/ B) \/ C]: [|- A \/ (B \/ C)] *)
  intro h.
  (* [h] gives two goals: one with [ab : A \/ B], one with [c : C]. *)
  destruct h as [ab | c].
  - (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
    destruct ab as [a | b].
    + (* [a] is the left side of [A \/ (B \/ C)]. *)
      exact (Or_left a).
    + (* [b] is the left side of [B \/ C], which is the right side of
         [A \/ (B \/ C)]. *)
      exact (Or_right (Or_left b)).
  - (* [c] is the right side of [B \/ C], which is the right side of
       [A \/ (B \/ C)]. *)
    exact (Or_right (Or_right c)).
Qed.

Lemma Or_associativity_backward
  : forall (A : Prop) (B : Prop) (C : Prop), A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  (* The context gains [A], [B] and [C]:
     [|- A \/ (B \/ C) -> (A \/ B) \/ C] *)
  intros A B C.
  (* The context gains [h : A \/ (B \/ C)]: [|- (A \/ B) \/ C] *)
  intro h.
  (* [h] gives two goals: one with [a : A], one with [bc : B \/ C]. *)
  destruct h as [a | bc].
  - (* [a] is the left side of [A \/ B], which is the left side of
       [(A \/ B) \/ C]. *)
    exact (Or_left (Or_left a)).
  - (* [bc] gives two goals: one with [b : B], one with [c : C]. *)
    destruct bc as [b | c].
    + (* [b] is the right side of [A \/ B], which is the left side of
         [(A \/ B) \/ C]. *)
      exact (Or_left (Or_right b)).
    + (* [c] is the right side of [(A \/ B) \/ C]. *)
      exact (Or_right c).
Qed.

Theorem Or_associativity
  : forall (A : Prop) (B : Prop) (C : Prop),
      ((A \/ B) \/ C -> A \/ (B \/ C)) /\ (A \/ (B \/ C) -> (A \/ B) \/ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- ((A \/ B) \/ C -> A \/ (B \/ C))
         /\ (A \/ (B \/ C) -> (A \/ B) \/ C)] *)
  intros A B C.
  (* The goal splits into two goals:
     [|- (A \/ B) \/ C -> A \/ (B \/ C)] and
     [|- A \/ (B \/ C) -> (A \/ B) \/ C]. *)
  split.
  - (* [Or_associativity_forward A B C] is a proof of the goal as it
       stands. *)
    exact (Or_associativity_forward A B C).
  - (* [Or_associativity_backward A B C] is a proof of the goal as it
       stands. *)
    exact (Or_associativity_backward A B C).
Qed.

(* Distributivity needs both connectives, and this module is the one that
   imports the other, so both laws sit here. *)

Lemma And_distributivity_over_Or_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- A /\ (B \/ C) -> (A /\ B) \/ (A /\ C)] *)
  intros A B C.
  (* The context gains [h : A /\ (B \/ C)]: [|- (A /\ B) \/ (A /\ C)] *)
  intro h.
  (* [h] splits into [a : A] and [bc : B \/ C]. *)
  destruct h as [a bc].
  (* [bc] gives two goals: one with [b : B], one with [c : C]. *)
  destruct bc as [b | c].
  - (* [Or_left] turns the goal into its left side: [|- A /\ B] *)
    apply Or_left.
    (* The goal splits into two goals: [|- A] and [|- B]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [b] is a proof of the goal as it stands. *)
      exact b.
  - (* [Or_right] turns the goal into its right side: [|- A /\ C] *)
    apply Or_right.
    (* The goal splits into two goals: [|- A] and [|- C]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [c] is a proof of the goal as it stands. *)
      exact c.
Qed.

Lemma And_distributivity_over_Or_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A /\ B) \/ (A /\ C) -> A /\ (B \/ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A /\ B) \/ (A /\ C) -> A /\ (B \/ C)] *)
  intros A B C.
  (* The context gains [h : (A /\ B) \/ (A /\ C)]: [|- A /\ (B \/ C)] *)
  intro h.
  (* [h] gives two goals: one with [ab : A /\ B], one with [ac : A /\ C]. *)
  destruct h as [ab | ac].
  - (* [ab] splits into [a : A] and [b : B]. *)
    destruct ab as [a b].
    (* The goal splits into two goals: [|- A] and [|- B \/ C]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [b] is the left side of [B \/ C]. *)
      exact (Or_left b).
  - (* [ac] splits into [a : A] and [c : C]. *)
    destruct ac as [a c].
    (* The goal splits into two goals: [|- A] and [|- B \/ C]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [c] is the right side of [B \/ C]. *)
      exact (Or_right c).
Qed.

Theorem And_distributivity_over_Or
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A /\ (B \/ C) -> (A /\ B) \/ (A /\ C))
      /\ ((A /\ B) \/ (A /\ C) -> A /\ (B \/ C)).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A /\ (B \/ C) -> (A /\ B) \/ (A /\ C))
         /\ ((A /\ B) \/ (A /\ C) -> A /\ (B \/ C))] *)
  intros A B C.
  (* The goal splits into two goals:
     [|- A /\ (B \/ C) -> (A /\ B) \/ (A /\ C)] and
     [|- (A /\ B) \/ (A /\ C) -> A /\ (B \/ C)]. *)
  split.
  - (* [And_distributivity_over_Or_forward A B C] is a proof of the goal as
       it stands. *)
    exact (And_distributivity_over_Or_forward A B C).
  - (* [And_distributivity_over_Or_backward A B C] is a proof of the goal as
       it stands. *)
    exact (And_distributivity_over_Or_backward A B C).
Qed.

Lemma Or_distributivity_over_And_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- A \/ (B /\ C) -> (A \/ B) /\ (A \/ C)] *)
  intros A B C.
  (* The context gains [h : A \/ (B /\ C)]: [|- (A \/ B) /\ (A \/ C)] *)
  intro h.
  (* [h] gives two goals: one with [a : A], one with [bc : B /\ C]. *)
  destruct h as [a | bc].
  - (* The goal splits into two goals: [|- A \/ B] and [|- A \/ C]. *)
    split.
    + (* [a] is the left side of [A \/ B]. *)
      exact (Or_left a).
    + (* [a] is the left side of [A \/ C]. *)
      exact (Or_left a).
  - (* [bc] splits into [b : B] and [c : C]. *)
    destruct bc as [b c].
    (* The goal splits into two goals: [|- A \/ B] and [|- A \/ C]. *)
    split.
    + (* [b] is the right side of [A \/ B]. *)
      exact (Or_right b).
    + (* [c] is the right side of [A \/ C]. *)
      exact (Or_right c).
Qed.

Lemma Or_distributivity_over_And_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B) /\ (A \/ C) -> A \/ (B /\ C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A \/ B) /\ (A \/ C) -> A \/ (B /\ C)] *)
  intros A B C.
  (* The context gains [h : (A \/ B) /\ (A \/ C)]: [|- A \/ (B /\ C)] *)
  intro h.
  (* [h] splits into [ab : A \/ B] and [ac : A \/ C]. *)
  destruct h as [ab ac].
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [a] is the left side of [A \/ (B /\ C)]. *)
    exact (Or_left a).
  - (* [ac] gives two goals: one with [a : A], one with [c : C]. *)
    destruct ac as [a | c].
    + (* [a] is the left side of [A \/ (B /\ C)]. *)
      exact (Or_left a).
    + (* [Or_right] turns the goal into its right side: [|- B /\ C] *)
      apply Or_right.
      (* The goal splits into two goals: [|- B] and [|- C]. *)
      split.
      * (* [b] is a proof of the goal as it stands. *)
        exact b.
      * (* [c] is a proof of the goal as it stands. *)
        exact c.
Qed.

Theorem Or_distributivity_over_And
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ (B /\ C) -> (A \/ B) /\ (A \/ C))
      /\ ((A \/ B) /\ (A \/ C) -> A \/ (B /\ C)).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A \/ (B /\ C) -> (A \/ B) /\ (A \/ C))
         /\ ((A \/ B) /\ (A \/ C) -> A \/ (B /\ C))] *)
  intros A B C.
  (* The goal splits into two goals:
     [|- A \/ (B /\ C) -> (A \/ B) /\ (A \/ C)] and
     [|- (A \/ B) /\ (A \/ C) -> A \/ (B /\ C)]. *)
  split.
  - (* [Or_distributivity_over_And_forward A B C] is a proof of the goal as
       it stands. *)
    exact (Or_distributivity_over_And_forward A B C).
  - (* [Or_distributivity_over_And_backward A B C] is a proof of the goal as
       it stands. *)
    exact (Or_distributivity_over_And_backward A B C).
Qed.
