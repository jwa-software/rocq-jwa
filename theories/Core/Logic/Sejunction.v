(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Negation]
   carries [~], and [Conjunction], [Disjunction], [Abjunction], [Bijunction]
   are the connectives the laws at the bottom relate this one to. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Negation.
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
      unfold Negation in not_b |- *.
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
      unfold Negation in not_a |- *.
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
  unfold Negation in not_ab.
  (* [ab] gives two goals: one with [a : A], one with [b : B]. *)
  destruct ab as [a | b].
  - (* [Sejunction_left] asks for [A] then [~ B], so the goal splits into
       two goals: [|- A] and [|- ~ B]. *)
    apply Sejunction_left.
    + (* [a] is a proof of the goal as it stands. *)
      exact a.
    + (* [|- B -> Falsum] *)
      unfold Negation in |- *.
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
      unfold Negation in |- *.
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

(* [<->] is respected by [_\/_]: each ctor carries one side and the
   negation of the other, and both travel across the equivalences. *)
Theorem Sejunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2).
Proof.
  (* The context gains [A1], [A2], [B1] and [B2]:
     [|- (A1 <-> A2) -> (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2)] *)
  intros A1 A2 B1 B2.
  (* The context gains [ea : A1 <-> A2]:
     [|- (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2)] *)
  intro ea.
  (* The context gains [eb : B1 <-> B2]: [|- A1 _\/_ B1 <-> A2 _\/_ B2] *)
  intro eb.
  (* [ea] splits into [a12 : A1 -> A2] and [a21 : A2 -> A1]. *)
  destruct ea as [a12 a21].
  (* [eb] splits into [b12 : B1 -> B2] and [b21 : B2 -> B1]. *)
  destruct eb as [b12 b21].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A1 _\/_ B1 -> A2 _\/_ B2] and
     [|- A2 _\/_ B2 -> A1 _\/_ B1]. *)
  split.
  - (* The context gains [h : A1 _\/_ B1]: [|- A2 _\/_ B2] *)
    intro h.
    (* [h] gives two goals: one with [a1 : A1] and [not_b1 : ~ B1], one with
       [not_a1 : ~ A1] and [b1 : B1]. *)
    destruct h as [a1 not_b1 | not_a1 b1].
    + (* [Sejunction_left] asks for [A2] then [~ B2], so the goal splits
         into two goals: [|- A2] and [|- ~ B2]. *)
      apply Sejunction_left.
      * (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
        apply a12.
        (* [a1] is a proof of the goal as it stands. *)
        exact a1.
      * (* [not_b1] goes from [~ B1] to [B1 -> Falsum]; the goal from
           [~ B2] to [B2 -> Falsum]. *)
        unfold Negation in not_b1 |- *.
        (* The context gains [b2 : B2]: [|- Falsum] *)
        intro b2.
        (* [not_b1] turns a proof of [B1] into a proof of [Falsum]:
           [|- B1] *)
        apply not_b1.
        (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
        apply b21.
        (* [b2] is a proof of the goal as it stands. *)
        exact b2.
    + (* [Sejunction_right] asks for [~ A2] then [B2], so the goal splits
         into two goals: [|- ~ A2] and [|- B2]. *)
      apply Sejunction_right.
      * (* [not_a1] goes from [~ A1] to [A1 -> Falsum]; the goal from
           [~ A2] to [A2 -> Falsum]. *)
        unfold Negation in not_a1 |- *.
        (* The context gains [a2 : A2]: [|- Falsum] *)
        intro a2.
        (* [not_a1] turns a proof of [A1] into a proof of [Falsum]:
           [|- A1] *)
        apply not_a1.
        (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
        apply a21.
        (* [a2] is a proof of the goal as it stands. *)
        exact a2.
      * (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
        apply b12.
        (* [b1] is a proof of the goal as it stands. *)
        exact b1.
  - (* The context gains [h : A2 _\/_ B2]: [|- A1 _\/_ B1] *)
    intro h.
    (* [h] gives two goals: one with [a2 : A2] and [not_b2 : ~ B2], one with
       [not_a2 : ~ A2] and [b2 : B2]. *)
    destruct h as [a2 not_b2 | not_a2 b2].
    + (* [Sejunction_left] asks for [A1] then [~ B1], so the goal splits
         into two goals: [|- A1] and [|- ~ B1]. *)
      apply Sejunction_left.
      * (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
        apply a21.
        (* [a2] is a proof of the goal as it stands. *)
        exact a2.
      * (* [not_b2] goes from [~ B2] to [B2 -> Falsum]; the goal from
           [~ B1] to [B1 -> Falsum]. *)
        unfold Negation in not_b2 |- *.
        (* The context gains [b1 : B1]: [|- Falsum] *)
        intro b1.
        (* [not_b2] turns a proof of [B2] into a proof of [Falsum]:
           [|- B2] *)
        apply not_b2.
        (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
        apply b12.
        (* [b1] is a proof of the goal as it stands. *)
        exact b1.
    + (* [Sejunction_right] asks for [~ A1] then [B1], so the goal splits
         into two goals: [|- ~ A1] and [|- B1]. *)
      apply Sejunction_right.
      * (* [not_a2] goes from [~ A2] to [A2 -> Falsum]; the goal from
           [~ A1] to [A1 -> Falsum]. *)
        unfold Negation in not_a2 |- *.
        (* The context gains [a1 : A1]: [|- Falsum] *)
        intro a1.
        (* [not_a2] turns a proof of [A2] into a proof of [Falsum]:
           [|- A2] *)
        apply not_a2.
        (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
        apply a12.
        (* [a1] is a proof of the goal as it stands. *)
        exact a1.
      * (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
        apply b21.
        (* [b2] is a proof of the goal as it stands. *)
        exact b2.
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
  unfold Negation in |- *.
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
  unfold Negation in |- *.
  (* The context gains [h : A _\/_ B]: [|- Falsum] *)
  intro h.
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [not_b] goes from [~ B] to [B -> Falsum]. *)
    unfold Negation in not_b.
    (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
    apply not_b.
    (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [not_a] goes from [~ A] to [A -> Falsum]. *)
    unfold Negation in not_a.
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
  unfold Negation in |- *.
  (* The context gains [e : A <-> B]: [|- Falsum] *)
  intro e.
  (* [e] splits into [ab : A -> B] and [ba : B -> A]. *)
  destruct e as [ab ba].
  (* [h] gives two goals: one with [a : A] and [not_b : ~ B], one with
     [not_a : ~ A] and [b : B]. *)
  destruct h as [a not_b | not_a b].
  - (* [not_b] goes from [~ B] to [B -> Falsum]. *)
    unfold Negation in not_b.
    (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
    apply not_b.
    (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [not_a] goes from [~ A] to [A -> Falsum]. *)
    unfold Negation in not_a.
    (* [not_a] turns a proof of [A] into a proof of [Falsum]: [|- A] *)
    apply not_a.
    (* [ba] turns a proof of [B] into a proof of [A]: [|- B] *)
    apply ba.
    (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.
