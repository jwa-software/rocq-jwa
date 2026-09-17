(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Conjunction]
   carries [/\], [Core.Logic.Bijunction] carries [<->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Bijunction.

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

(* Disjunction elimination, the rule that a proof of [C] from each side is a
   proof of [C] from [A \/ B], stated with its inverse: an arrow out of a
   disjunction is an arrow out of each side. A [<->] with its halves as
   lemmas. *)

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

Lemma Disjunction_elimination_backward
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A -> C) /\ (B -> C) -> A \/ B -> C.
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A -> C) /\ (B -> C) -> A \/ B -> C] *)
  intros A B C.
  (* The context gains [h : (A -> C) /\ (B -> C)]: [|- A \/ B -> C] *)
  intro h.
  (* [h] splits into [ac : A -> C] and [bc : B -> C]. *)
  destruct h as [ac bc].
  (* The context gains [ab : A \/ B]: [|- C] *)
  intro ab.
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [ac] turns a proof of [A] into a proof of [C]: [|- A] *)
    apply ac.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [bc] turns a proof of [B] into a proof of [C]: [|- B] *)
    apply bc.
    (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.

Theorem Disjunction_elimination
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  (* The context gains [A], [B] and [C]:
     [|- (A \/ B -> C) <-> (A -> C) /\ (B -> C)] *)
  intros A B C.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- (A \/ B -> C) -> (A -> C) /\ (B -> C)] and
     [|- (A -> C) /\ (B -> C) -> A \/ B -> C]. *)
  split.
  - (* [Disjunction_elimination_forward A B C] is a proof of the goal
       as it stands. *)
    exact (Disjunction_elimination_forward A B C).
  - (* [Disjunction_elimination_backward A B C] is a proof of the goal
       as it stands. *)
    exact (Disjunction_elimination_backward A B C).
Qed.

(* [<->] is respected by [\/]: replacing each side by an equivalent one
   gives an equivalent disjunction. *)
Theorem Disjunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2).
Proof.
  (* The context gains [A1], [A2], [B1] and [B2]:
     [|- (A1 <-> A2) -> (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2)] *)
  intros A1 A2 B1 B2.
  (* The context gains [ea : A1 <-> A2]:
     [|- (B1 <-> B2) -> (A1 \/ B1 <-> A2 \/ B2)] *)
  intro ea.
  (* The context gains [eb : B1 <-> B2]: [|- A1 \/ B1 <-> A2 \/ B2] *)
  intro eb.
  (* [ea] splits into [a12 : A1 -> A2] and [a21 : A2 -> A1]. *)
  destruct ea as [a12 a21].
  (* [eb] splits into [b12 : B1 -> B2] and [b21 : B2 -> B1]. *)
  destruct eb as [b12 b21].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A1 \/ B1 -> A2 \/ B2] and [|- A2 \/ B2 -> A1 \/ B1]. *)
  split.
  - (* The context gains [h : A1 \/ B1]: [|- A2 \/ B2] *)
    intro h.
    (* [h] gives two goals: one with [a1 : A1], one with [b1 : B1]. *)
    destruct h as [a1 | b1].
    + (* [Disjunction_left] turns the goal into its left side: [|- A2] *)
      apply Disjunction_left.
      (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
      apply a12.
      (* [a1] is a proof of the goal as it stands. *)
      exact a1.
    + (* [Disjunction_right] turns the goal into its right side: [|- B2] *)
      apply Disjunction_right.
      (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
      apply b12.
      (* [b1] is a proof of the goal as it stands. *)
      exact b1.
  - (* The context gains [h : A2 \/ B2]: [|- A1 \/ B1] *)
    intro h.
    (* [h] gives two goals: one with [a2 : A2], one with [b2 : B2]. *)
    destruct h as [a2 | b2].
    + (* [Disjunction_left] turns the goal into its left side: [|- A1] *)
      apply Disjunction_left.
      (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
      apply a21.
      (* [a2] is a proof of the goal as it stands. *)
      exact a2.
    + (* [Disjunction_right] turns the goal into its right side: [|- B1] *)
      apply Disjunction_right.
      (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
      apply b21.
      (* [b2] is a proof of the goal as it stands. *)
      exact b2.
Qed.
