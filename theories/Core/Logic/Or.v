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
