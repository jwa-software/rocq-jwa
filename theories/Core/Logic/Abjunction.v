(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level that the notation below needs, [Core.Ltac] carries the tactic
   language, [Core.Logic.Subjunction] carries [->], [Core.Logic.Unjunction]
   carries [~], [Core.Logic.Bijunction] carries [<->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Logic.Unjunction.
From jwa Require Import Core.Logic.Bijunction.

(* Abjunction is material nonimplication: [A] holds and [B] does not, the
   one case in which [A -> B] fails. *)
Inductive Abjunction (A : Prop) (B : Prop) : Prop :=
  | Abjunction_introduction : A -> ~ B -> Abjunction A B.

Arguments Abjunction_introduction {A} {B} a not_b.

Notation "A -/> B" := (Abjunction A B) : jwa_type_scope.

(* [-/>] against [->]: each refutes the other. *)

Theorem Abjunction_refutes_Subjunction
  : forall (A : Prop) (B : Prop), A -/> B -> ~ (A -> B).
Proof.
  (* The context gains [A] and [B]: [|- A -/> B -> ~ (A -> B)] *)
  intros A B.
  (* The context gains [h : A -/> B]: [|- ~ (A -> B)] *)
  intro h.
  (* [Abjunction] has one ctor with two fields, so [h] splits into [a : A]
     and [not_b : ~ B]. *)
  destruct h as [a not_b].
  (* [not_b] goes from [~ B] to [B -> Falsum]; the goal from [~ (A -> B)]
     to [(A -> B) -> Falsum]. *)
  unfold Unjunction in not_b |- *.
  (* The context gains [ab : A -> B]: [|- Falsum] *)
  intro ab.
  (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
  apply not_b.
  (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
  apply ab.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

Theorem Subjunction_refutes_Abjunction
  : forall (A : Prop) (B : Prop), (A -> B) -> ~ (A -/> B).
Proof.
  (* The context gains [A] and [B]: [|- (A -> B) -> ~ (A -/> B)] *)
  intros A B.
  (* The context gains [ab : A -> B]: [|- ~ (A -/> B)] *)
  intro ab.
  (* [|- A -/> B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [h : A -/> B]: [|- Falsum] *)
  intro h.
  (* [h] splits into [a : A] and [not_b : ~ B]. *)
  destruct h as [a not_b].
  (* [not_b] goes from [~ B] to [B -> Falsum]. *)
  unfold Unjunction in not_b.
  (* [not_b] turns a proof of [B] into a proof of [Falsum]: [|- B] *)
  apply not_b.
  (* [ab] turns a proof of [A] into a proof of [B]: [|- A] *)
  apply ab.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

(* [~] pushed through [-/>]: refuting [A -/> B] is the same as turning a
   proof of [A] into a refutation of [~ B]. The two halves are lemmas, the
   [<->] the theorem. *)

Lemma Unjunction_over_Abjunction_forward
  : forall (A : Prop) (B : Prop), ~ (A -/> B) -> A -> ~ ~ B.
Proof.
  (* The context gains [A] and [B]: [|- ~ (A -/> B) -> A -> ~ ~ B] *)
  intros A B.
  (* [|- (A -/> B -> Falsum) -> A -> (B -> Falsum) -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [h : A -/> B -> Falsum]:
     [|- A -> (B -> Falsum) -> Falsum] *)
  intro h.
  (* The context gains [a : A]: [|- (B -> Falsum) -> Falsum] *)
  intro a.
  (* The context gains [not_b : B -> Falsum]: [|- Falsum] *)
  intro not_b.
  (* [h] turns a proof of [A -/> B] into a proof of [Falsum]:
     [|- A -/> B] *)
  apply h.
  (* [Abjunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A] and [|- ~ B]. *)
  split.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [~ B] is [B -> Falsum], which [not_b] proves. *)
    exact not_b.
Qed.

Lemma Unjunction_over_Abjunction_backward
  : forall (A : Prop) (B : Prop), (A -> ~ ~ B) -> ~ (A -/> B).
Proof.
  (* The context gains [A] and [B]: [|- (A -> ~ ~ B) -> ~ (A -/> B)] *)
  intros A B.
  (* [|- (A -> (B -> Falsum) -> Falsum) -> A -/> B -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [f : A -> (B -> Falsum) -> Falsum]:
     [|- A -/> B -> Falsum] *)
  intro f.
  (* The context gains [h : A -/> B]: [|- Falsum] *)
  intro h.
  (* [h] splits into [a : A] and [not_b : ~ B]. *)
  destruct h as [a not_b].
  (* [f] turns proofs of [A] and of [B -> Falsum] into a proof of [Falsum],
     so the goal splits into two goals: [|- A] and [|- B -> Falsum]. *)
  apply f.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [not_b : ~ B] is [B -> Falsum]. *)
    exact not_b.
Qed.

Theorem Unjunction_over_Abjunction
  : forall (A : Prop) (B : Prop), ~ (A -/> B) <-> (A -> ~ ~ B).
Proof.
  (* The context gains [A] and [B]: [|- ~ (A -/> B) <-> (A -> ~ ~ B)] *)
  intros A B.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- ~ (A -/> B) -> A -> ~ ~ B] and
     [|- (A -> ~ ~ B) -> ~ (A -/> B)]. *)
  split.
  - (* [Unjunction_over_Abjunction_forward A B] is a proof of the goal as it
       stands. *)
    exact (Unjunction_over_Abjunction_forward A B).
  - (* [Unjunction_over_Abjunction_backward A B] is a proof of the goal as
       it stands. *)
    exact (Unjunction_over_Abjunction_backward A B).
Qed.

(* [<->] is respected by [-/>]: the held side and the refuted side each
   travel across their equivalence. *)
Theorem Abjunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 -/> B1 <-> A2 -/> B2).
Proof.
  (* The context gains [A1], [A2], [B1] and [B2]:
     [|- (A1 <-> A2) -> (B1 <-> B2) -> (A1 -/> B1 <-> A2 -/> B2)] *)
  intros A1 A2 B1 B2.
  (* The context gains [ea : A1 <-> A2]:
     [|- (B1 <-> B2) -> (A1 -/> B1 <-> A2 -/> B2)] *)
  intro ea.
  (* The context gains [eb : B1 <-> B2]: [|- A1 -/> B1 <-> A2 -/> B2] *)
  intro eb.
  (* [ea] splits into [a12 : A1 -> A2] and [a21 : A2 -> A1]. *)
  destruct ea as [a12 a21].
  (* [eb] splits into [b12 : B1 -> B2] and [b21 : B2 -> B1]. *)
  destruct eb as [b12 b21].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- A1 -/> B1 -> A2 -/> B2] and [|- A2 -/> B2 -> A1 -/> B1]. *)
  split.
  - (* The context gains [h : A1 -/> B1]: [|- A2 -/> B2] *)
    intro h.
    (* [h] splits into [a1 : A1] and [not_b1 : ~ B1]. *)
    destruct h as [a1 not_b1].
    (* [Abjunction] has one ctor with two fields, so the goal splits into
       two goals: [|- A2] and [|- ~ B2]. *)
    split.
    + (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
      apply a12.
      (* [a1] is a proof of the goal as it stands. *)
      exact a1.
    + (* [not_b1] goes from [~ B1] to [B1 -> Falsum]; the goal from [~ B2]
         to [B2 -> Falsum]. *)
      unfold Unjunction in not_b1 |- *.
      (* The context gains [b2 : B2]: [|- Falsum] *)
      intro b2.
      (* [not_b1] turns a proof of [B1] into a proof of [Falsum]: [|- B1] *)
      apply not_b1.
      (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
      apply b21.
      (* [b2] is a proof of the goal as it stands. *)
      exact b2.
  - (* The context gains [h : A2 -/> B2]: [|- A1 -/> B1] *)
    intro h.
    (* [h] splits into [a2 : A2] and [not_b2 : ~ B2]. *)
    destruct h as [a2 not_b2].
    (* The goal splits into two goals: [|- A1] and [|- ~ B1]. *)
    split.
    + (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
      apply a21.
      (* [a2] is a proof of the goal as it stands. *)
      exact a2.
    + (* [not_b2] goes from [~ B2] to [B2 -> Falsum]; the goal from [~ B1]
         to [B1 -> Falsum]. *)
      unfold Unjunction in not_b2 |- *.
      (* The context gains [b1 : B1]: [|- Falsum] *)
      intro b1.
      (* [not_b2] turns a proof of [B2] into a proof of [Falsum]: [|- B2] *)
      apply not_b2.
      (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
      apply b12.
      (* [b1] is a proof of the goal as it stands. *)
      exact b1.
Qed.
