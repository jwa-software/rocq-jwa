(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Unjunction]
   carries [~], and [Conjunction], [Disjunction], [Abjunction], [Bijunction]
   are the connectives the laws at the bottom relate this one to. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Unjunction.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Abjunction.
From jwa Require Import Core.Logic.Bijunction.

(* Sejunction is exclusive disjunction: one side holds and the other does
   not. [Theorem t : Verum _\/_ Verum.] is accepted and [Proof.] opens, but no
   step reaches [Qed.]: either ctor demands [~ Verum], and no term has that
   type. Being writable does not make a statement provable. *)
Inductive Sejunction (A : Prop) (B : Prop) : Prop :=
  | Sejunction_left  : A -> ~ B -> Sejunction A B
  | Sejunction_right : ~ A -> B -> Sejunction A B.

Arguments Sejunction_left  {A} {B} a not_b.
Arguments Sejunction_right {A} {B} not_a b.

Notation "A _\/_ B" := (Sejunction A B) : jwa_type_scope.

Theorem Sejunction_commutativity
  : forall (A : Prop) (B : Prop), A _\/_ B -> B _\/_ A.
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> B _\/_ A] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- B _\/_ A] *)
  intro h.
  (* [Sejunction] has two ctors with two fields each, so [h] gives two
     goals: one with [a : A] and [not_b : ~ B], one with [not_a : ~ A] and
     [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [Sejunction_right] asks for [~ B] then [A], the two fields in the
       other order. *)
    exact (Sejunction_right not_b a).
  - (* [Sejunction_left] asks for [B] then [~ A]. *)
    exact (Sejunction_left b not_a).
Qed.

(* Associativity is not a theorem of this module. From [~ (A _\/_ B)] and
   [C], a proof of [A _\/_ (B _\/_ C)] has to pick a ctor, and which one is
   right depends on whether [A] holds; no term decides that. *)

(* Two characterisations of [_\/_], each a [<->] with its halves as lemmas:
   as one of two [-/>], and as a [\/] that is not a [/\]. *)

Lemma Sejunction_as_abjunctions_forward
  : forall (A : Prop) (B : Prop), A _\/_ B -> (A -/> B) \/ (B -/> A).
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> (A -/> B) \/ (B -/> A)] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- (A -/> B) \/ (B -/> A)] *)
  intro h.
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [Disjunction_left] turns the goal into its left side: [|- A -/> B] *)
    apply Disjunction_left.
    (* [Abjunction] has one ctor with two fields, so the goal splits into two
       goals: [|- A] and [|- ~ B]. *)
    split.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [not_b] is a proof of the goal as it stands. *)
      exact not_b.
  - (* [Disjunction_right] turns the goal into its right side:
       [|- B -/> A] *)
    apply Disjunction_right.
    (* The goal splits into two goals: [|- B] and [|- ~ A]. *)
    split.
    + (* [b] is a proof of the goal as it stands. *)
      exact b.
    + (* [not_a] is a proof of the goal as it stands. *)
      exact not_a.
Qed.

Lemma Sejunction_as_abjunctions_backward
  : forall (A : Prop) (B : Prop), (A -/> B) \/ (B -/> A) -> A _\/_ B.
Proof.
  (* The context gains [A] and [B]: [|- (A -/> B) \/ (B -/> A) -> A _\/_ B] *)
  intros A B.
  (* The context gains [h : (A -/> B) \/ (B -/> A)]: [|- A _\/_ B] *)
  intro h.
  (* [h] gives two goals: one with [ab : A -/> B], one with [ba : B -/> A]. *)
  destruct h as [ab | ba].
  - (* [ab] splits into [a : A] and [not_b : ~ B]. *)
    destruct ab as [a not_b].
    (* [Sejunction_left] asks for [A] then [~ B]. *)
    exact (Sejunction_left a not_b).
  - (* [ba] splits into [b : B] and [not_a : ~ A]. *)
    destruct ba as [b not_a].
    (* [Sejunction_right] asks for [~ A] then [B]. *)
    exact (Sejunction_right not_a b).
Qed.

Theorem Sejunction_as_abjunctions
  : forall (A : Prop) (B : Prop), A _\/_ B <-> (A -/> B) \/ (B -/> A).
Proof.
  (* The context gains [A] and [B]:
     [|- A _\/_ B <-> (A -/> B) \/ (B -/> A)] *)
  intros A B.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A _\/_ B -> (A -/> B) \/ (B -/> A)] and
     [|- (A -/> B) \/ (B -/> A) -> A _\/_ B]. *)
  split.
  - (* [Sejunction_as_abjunctions_forward A B] is a proof of the goal as it
       stands. *)
    exact (Sejunction_as_abjunctions_forward A B).
  - (* [Sejunction_as_abjunctions_backward A B] is a proof of the goal as it
       stands. *)
    exact (Sejunction_as_abjunctions_backward A B).
Qed.

Lemma Sejunction_as_disjunction_without_conjunction_forward
  : forall (A : Prop) (B : Prop), A _\/_ B -> (A \/ B) /\ ~ (A /\ B).
Proof.
  (* The context gains [A] and [B]:
     [|- A _\/_ B -> (A \/ B) /\ ~ (A /\ B)] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- (A \/ B) /\ ~ (A /\ B)] *)
  intro h.
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* The goal splits into two goals: [|- A \/ B] and [|- ~ (A /\ B)]. *)
    split.
    + (* [a] is the left side of [A \/ B]. *)
      exact (Disjunction_left a).
    + (* [not_b] goes from [~ B] to [B -> Falsum]; the goal from
         [~ (A /\ B)] to [A /\ B -> Falsum]. *)
      unfold Unjunction in not_b |- *.
      (* The context gains [ab : A /\ B]: [|- Falsum] *)
      intro ab.
      (* Only the right half of [ab] is needed: [b : B]. *)
      destruct ab as [_ b].
      (* [not_b] turns [b] into a proof of [Falsum]. *)
      exact (not_b b).
  - (* The goal splits into two goals: [|- A \/ B] and [|- ~ (A /\ B)]. *)
    split.
    + (* [b] is the right side of [A \/ B]. *)
      exact (Disjunction_right b).
    + (* [not_a] goes from [~ A] to [A -> Falsum]; the goal from
         [~ (A /\ B)] to [A /\ B -> Falsum]. *)
      unfold Unjunction in not_a |- *.
      (* The context gains [ab : A /\ B]: [|- Falsum] *)
      intro ab.
      (* Only the left half of [ab] is needed: [a : A]. *)
      destruct ab as [a _].
      (* [not_a] turns [a] into a proof of [Falsum]. *)
      exact (not_a a).
Qed.

Lemma Sejunction_as_disjunction_without_conjunction_backward
  : forall (A : Prop) (B : Prop), (A \/ B) /\ ~ (A /\ B) -> A _\/_ B.
Proof.
  (* The context gains [A] and [B]:
     [|- (A \/ B) /\ ~ (A /\ B) -> A _\/_ B] *)
  intros A B.
  (* The context gains [h : (A \/ B) /\ ~ (A /\ B)]: [|- A _\/_ B] *)
  intro h.
  (* [h] splits into [ab : A \/ B] and [not_ab : ~ (A /\ B)]. *)
  destruct h as [ab not_ab].
  (* [not_ab] goes from [~ (A /\ B)] to [A /\ B -> Falsum]. *)
  unfold Unjunction in not_ab.
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [Sejunction_left] asks for [A] then [~ B], so the goal splits into
       two goals: [|- A] and [|- ~ B]. *)
    apply Sejunction_left.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [|- B -> Falsum] *)
      unfold Unjunction in |- *.
      (* The context gains [b : B]: [|- Falsum] *)
      intro b.
      (* [not_ab] turns a proof of [A /\ B] into a proof of [Falsum]:
         [|- A /\ B] *)
      apply not_ab.
      (* The goal splits into two goals: [|- A] and [|- B]. *)
      split.
      * (* [a] is a proof of the goal as it stands. *)
        exact a.
      * (* [b] is a proof of the goal as it stands. *)
        exact b.
  - (* [Sejunction_right] asks for [~ A] then [B], so the goal splits into
       two goals: [|- ~ A] and [|- B]. *)
    apply Sejunction_right.
    + (* [|- A -> Falsum] *)
      unfold Unjunction in |- *.
      (* The context gains [a : A]: [|- Falsum] *)
      intro a.
      (* [not_ab] turns a proof of [A /\ B] into a proof of [Falsum]:
         [|- A /\ B] *)
      apply not_ab.
      (* The goal splits into two goals: [|- A] and [|- B]. *)
      split.
      * (* [a] is a proof of the goal as it stands. *)
        exact a.
      * (* [b] is a proof of the goal as it stands. *)
        exact b.
    + (* [b] is a proof of the goal as it stands. *)
      exact b.
Qed.

Theorem Sejunction_as_disjunction_without_conjunction
  : forall (A : Prop) (B : Prop), A _\/_ B <-> (A \/ B) /\ ~ (A /\ B).
Proof.
  (* The context gains [A] and [B]:
     [|- A _\/_ B <-> (A \/ B) /\ ~ (A /\ B)] *)
  intros A B.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A _\/_ B -> (A \/ B) /\ ~ (A /\ B)] and
     [|- (A \/ B) /\ ~ (A /\ B) -> A _\/_ B]. *)
  split.
  - (* [Sejunction_as_disjunction_without_conjunction_forward A B] is a
       proof of the goal as it stands. *)
    exact (Sejunction_as_disjunction_without_conjunction_forward A B).
  - (* [Sejunction_as_disjunction_without_conjunction_backward A B] is a
       proof of the goal as it stands. *)
    exact (Sejunction_as_disjunction_without_conjunction_backward A B).
Qed.

(* What [_\/_] gives and what it excludes: it implies [\/], it refutes [/\],
   and it and [<->] refute each other. *)

Theorem Sejunction_implies_Disjunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> A \/ B.
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> A \/ B] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- A \/ B] *)
  intro h.
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [a] is the left side of [A \/ B]. *)
    exact (Disjunction_left a).
  - (* [b] is the right side of [A \/ B]. *)
    exact (Disjunction_right b).
Qed.

Theorem Sejunction_refutes_Conjunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> ~ (A /\ B).
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> ~ (A /\ B)] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- ~ (A /\ B)] *)
  intro h.
  (* [|- A /\ B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [ab : A /\ B]: [|- Falsum] *)
  intro ab.
  (* [ab] splits into [a : A] and [b : B]. *)
  destruct ab as [a b].
  (* [h] gives two goals: one with [not_b : ~ B], one with [not_a : ~ A];
     the other field of each ctor is not needed. *)
  destruct h as [_ not_b | not_a _].
  - (* [not_b] turns [b] into a proof of [Falsum]. *)
    exact (not_b b).
  - (* [not_a] turns [a] into a proof of [Falsum]. *)
    exact (not_a a).
Qed.

Theorem Bijunction_refutes_Sejunction
  : forall (A : Prop) (B : Prop), (A <-> B) -> ~ (A _\/_ B).
Proof.
  (* The context gains [A] and [B]: [|- (A <-> B) -> ~ (A _\/_ B)] *)
  intros A B.
  (* The context gains [e : A <-> B]: [|- ~ (A _\/_ B)] *)
  intro e.
  (* [e] splits into [ab : A -> B] and [ba : B -> A]. *)
  destruct e as [ab ba].
  (* [|- A _\/_ B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [h : A _\/_ B]: [|- Falsum] *)
  intro h.
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [not_b] goes from [~ B] to [B -> Falsum]. *)
    unfold Unjunction in not_b.
    (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
    apply not_b.
    (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [not_a] goes from [~ A] to [A -> Falsum]. *)
    unfold Unjunction in not_a.
    (* [not_a] turns a proof of [A] into a proof of [Falsum]: [|- A] *)
    apply not_a.
    (* [ba] turns a proof of [B] into a proof of [A]: [|- B] *)
    apply ba.
    (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.

Theorem Sejunction_refutes_Bijunction
  : forall (A : Prop) (B : Prop), A _\/_ B -> ~ (A <-> B).
Proof.
  (* The context gains [A] and [B]: [|- A _\/_ B -> ~ (A <-> B)] *)
  intros A B.
  (* The context gains [h : A _\/_ B]: [|- ~ (A <-> B)] *)
  intro h.
  (* [|- (A <-> B) -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [e : A <-> B]: [|- Falsum] *)
  intro e.
  (* [e] splits into [ab : A -> B] and [ba : B -> A]. *)
  destruct e as [ab ba].
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [not_b] goes from [~ B] to [B -> Falsum]. *)
    unfold Unjunction in not_b.
    (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
    apply not_b.
    (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [not_a] goes from [~ A] to [A -> Falsum]. *)
    unfold Unjunction in not_a.
    (* [not_a] turns a proof of [A] into a proof of [Falsum]: [|- A] *)
    apply not_a.
    (* [ba] turns a proof of [B] into a proof of [A]: [|- B] *)
    apply ba.
    (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.
