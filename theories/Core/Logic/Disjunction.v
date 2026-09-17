(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Conjunction]
   carries [/\]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Conjunction.

Inductive Disjunction (A : Prop) (B : Prop) : Prop :=
  | Disjunction_left  : A -> Disjunction A B
  | Disjunction_right : B -> Disjunction A B.

(* The unused side is not determined by the argument. It comes from the
   expected type, and a use that has none needs [@Disjunction_left]. *)
Arguments Disjunction_left  {A} {B} a.
Arguments Disjunction_right {A} {B} b.

Notation "A \/ B" := (Disjunction A B) : jwa_type_scope.

(* The laws are implications, as in [Core.Logic.Conjunction]. A proof of a
   disjunction is one ctor applied to one side, so each case below is a
   single [exact]. *)

Theorem Disjunction_commutativity
  : forall (A : Prop) (B : Prop), A \/ B -> B \/ A.
Proof.
  (* The context gains [A] and [B]: [|- A \/ B -> B \/ A] *)
  intros A B.
  (* The context gains [h : A \/ B]: [|- B \/ A] *)
  intro h.
  (* [Disjunction] has two ctors, so [h] gives two goals: one with [a : A],
     one with [b : B]. *)
  destruct h as [a | b].
  - (* [a] is the right side of [B \/ A]. *)
    exact (Disjunction_right a).
  - (* [b] is the left side of [B \/ A]. *)
    exact (Disjunction_left b).
Qed.

Lemma Disjunction_associativity_forward
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
      exact (Disjunction_left a).
    + (* [b] is the left side of [B \/ C], which is the right side of
         [A \/ (B \/ C)]. *)
      exact (Disjunction_right (Disjunction_left b)).
  - (* [c] is the right side of [B \/ C], which is the right side of
       [A \/ (B \/ C)]. *)
    exact (Disjunction_right (Disjunction_right c)).
Qed.

Lemma Disjunction_associativity_backward
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
    exact (Disjunction_left (Disjunction_left a)).
  - (* [bc] gives two goals: one with [b : B], one with [c : C]. *)
    destruct bc as [b | c].
    + (* [b] is the right side of [A \/ B], which is the left side of
         [(A \/ B) \/ C]. *)
      exact (Disjunction_left (Disjunction_right b)).
    + (* [c] is the right side of [(A \/ B) \/ C]. *)
      exact (Disjunction_right c).
Qed.

Theorem Disjunction_associativity
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
  - (* [Disjunction_associativity_forward A B C] is a proof of the goal as it
       stands. *)
    exact (Disjunction_associativity_forward A B C).
  - (* [Disjunction_associativity_backward A B C] is a proof of the goal as it
       stands. *)
    exact (Disjunction_associativity_backward A B C).
Qed.

(* Distributivity needs both connectives, and this module is the one that
   imports the other, so both laws sit here. *)

Lemma Conjunction_distributivity_over_Disjunction_forward
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
  - (* [Disjunction_left] turns the goal into its left side: [|- A /\ B] *)
    apply Disjunction_left.
    (* The goal splits into two goals: [|- A] and [|- B]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [b] is a proof of the goal as it stands. *)
      exact b.
  - (* [Disjunction_right] turns the goal into its right side: [|- A /\ C] *)
    apply Disjunction_right.
    (* The goal splits into two goals: [|- A] and [|- C]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [c] is a proof of the goal as it stands. *)
      exact c.
Qed.

Lemma Conjunction_distributivity_over_Disjunction_backward
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
      exact (Disjunction_left b).
  - (* [ac] splits into [a : A] and [c : C]. *)
    destruct ac as [a c].
    (* The goal splits into two goals: [|- A] and [|- B \/ C]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [c] is the right side of [B \/ C]. *)
      exact (Disjunction_right c).
Qed.

Theorem Conjunction_distributivity_over_Disjunction
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
  - (* [Conjunction_distributivity_over_Disjunction_forward A B C] is a
       proof of the goal as it stands. *)
    exact (Conjunction_distributivity_over_Disjunction_forward A B C).
  - (* [Conjunction_distributivity_over_Disjunction_backward A B C] is a
       proof of the goal as it stands. *)
    exact (Conjunction_distributivity_over_Disjunction_backward A B C).
Qed.

Lemma Disjunction_distributivity_over_Conjunction_forward
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
      exact (Disjunction_left a).
    + (* [a] is the left side of [A \/ C]. *)
      exact (Disjunction_left a).
  - (* [bc] splits into [b : B] and [c : C]. *)
    destruct bc as [b c].
    (* The goal splits into two goals: [|- A \/ B] and [|- A \/ C]. *)
    split.
    + (* [b] is the right side of [A \/ B]. *)
      exact (Disjunction_right b).
    + (* [c] is the right side of [A \/ C]. *)
      exact (Disjunction_right c).
Qed.

Lemma Disjunction_distributivity_over_Conjunction_backward
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
    exact (Disjunction_left a).
  - (* [ac] gives two goals: one with [a : A], one with [c : C]. *)
    destruct ac as [a | c].
    + (* [a] is the left side of [A \/ (B /\ C)]. *)
      exact (Disjunction_left a).
    + (* [Disjunction_right] turns the goal into its right side: [|- B /\ C] *)
      apply Disjunction_right.
      (* The goal splits into two goals: [|- B] and [|- C]. *)
      split.
      * (* [b] is a proof of the goal as it stands. *)
        exact b.
      * (* [c] is a proof of the goal as it stands. *)
        exact c.
Qed.

Theorem Disjunction_distributivity_over_Conjunction
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
  - (* [Disjunction_distributivity_over_Conjunction_forward A B C] is a
       proof of the goal as it stands. *)
    exact (Disjunction_distributivity_over_Conjunction_forward A B C).
  - (* [Disjunction_distributivity_over_Conjunction_backward A B C] is a
       proof of the goal as it stands. *)
    exact (Disjunction_distributivity_over_Conjunction_backward A B C).
Qed.


Lemma Disjunction_elimination_forward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A \/ B -> C) -> (A -> C) /\ (B -> C)] *)
  intros A B C.
  (* The context gains [f : A \/ B -> C]: [|- (A -> C) /\ (B -> C)] *)
  intro f.
  (* The goal splits into two goals: [|- A -> C] and [|- B -> C]. *)
  split.
  - (* The context gains [a : A]: [|- C] *)
    intro a.
    (* [f] turns a proof of [A \/ B] into a proof of [C]: [|- A \/ B] *)
    apply f.
    (* [a] is the left side of [A \/ B]. *)
    exact (Disjunction_left a).
  - (* The context gains [b : B]: [|- C] *)
    intro b.
    (* [f] turns a proof of [A \/ B] into a proof of [C]: [|- A \/ B] *)
    apply f.
    (* [b] is the right side of [A \/ B]. *)
    exact (Disjunction_right b).
Qed.
