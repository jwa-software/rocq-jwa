(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level below and [Core.Ltac] carries the tactic language. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.

(* Subjunction is the conditional, [if A then B]. [->] is the kernel's
   non-dependent [forall], which this line only gives a spelling. *)
Notation "A -> B" := (forall (_ : A), B) : jwa_type_scope.

(* The two basic facts of the conditional are the identity function and
   function composition, stated as theorems. *)

Theorem Subjunction_reflexivity : forall (A : Prop), A -> A.
Proof.
  (* The context gains [A : Prop]; the goal is now [A -> A]. *)
  intro A.
  (* The context gains [a : A]; the goal is now [A]. *)
  intro a.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

Theorem Subjunction_transitivity
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B) -> (B -> C) -> (A -> C).
Proof.
  (* The context gains [A], [B] and [C]; the goal is now
     [(A -> B) -> (B -> C) -> (A -> C)]. *)
  intros A B C.
  (* The context gains [ab : A -> B]; the goal is now
     [(B -> C) -> (A -> C)]. *)
  intro ab.
  (* The context gains [bc : B -> C]; the goal is now [A -> C]. *)
  intro bc.
  (* The context gains [a : A]; the goal is now [C]. *)
  intro a.
  (* [bc : B -> C] turns a proof of [B] into a proof of [C], so proving [C]
     reduces to proving [B]; the goal is now [B]. *)
  apply bc.
  (* [ab : A -> B] turns a proof of [A] into a proof of [B]; the goal is now
     [A]. *)
  apply ab.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

(* The three structural rules: a hypothesis may be added unused
   (weakening), a repeated one may be merged (contraction), and two may
   change places (exchange). *)

Theorem Subjunction_weakening : forall (A : Prop) (B : Prop), A -> B -> A.
Proof.
  (* The context gains [A] and [B]: [|- A -> B -> A] *)
  intros A B.
  (* The context gains [a : A]: [|- B -> A] *)
  intro a.
  (* The context gains [b : B], which is never used: [|- A] *)
  intro b.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

Theorem Subjunction_contraction
  : forall (A : Prop) (B : Prop), (A -> A -> B) -> A -> B.
Proof.
  (* The context gains [A] and [B]: [|- (A -> A -> B) -> A -> B] *)
  intros A B.
  (* The context gains [f : A -> A -> B]: [|- A -> B] *)
  intro f.
  (* The context gains [a : A]: [|- B] *)
  intro a.
  (* [f] turns two proofs of [A] into a proof of [B], so the goal splits
     into two goals, [|- A] and [|- A]. *)
  apply f.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
Qed.

(* Its own converse: applying it twice restores the order. *)
Theorem Subjunction_exchange
  : forall (A : Prop) (B : Prop) (C : Prop), (A -> B -> C) -> B -> A -> C.
Proof.
  (* The context gains [A], [B] and [C]: [|- (A -> B -> C) -> B -> A -> C] *)
  intros A B C.
  (* The context gains [f : A -> B -> C]: [|- B -> A -> C] *)
  intro f.
  (* The context gains [b : B]: [|- A -> C] *)
  intro b.
  (* The context gains [a : A]: [|- C] *)
  intro a.
  (* [f] turns proofs of [A] and of [B] into a proof of [C], so the goal
     splits into two goals: [|- A] and [|- B]. *)
  apply f.
  - (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* [b] is a proof of the goal as it stands. *)
    exact b.
Qed.

(* [Subjunction.abjunction_incompatibility] is stated in
 * [Core.Logic.Abjunction], the lowest file that knows both connectives, in
 * a module named after this one.
 *)
