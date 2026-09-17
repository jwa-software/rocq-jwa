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
