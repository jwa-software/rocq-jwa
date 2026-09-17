(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level below, [Core.Ltac] carries the tactic language,
   [Core.Logic.Subjunction] carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Subjunction.

(* Bijunction is the biconditional: each side implies the other, and the one
   ctor carries both directions. *)
Inductive Bijunction (A : Prop) (B : Prop) : Prop :=
  | Bijunction_introduction : (A -> B) -> (B -> A) -> Bijunction A B.

Arguments Bijunction_introduction {A} {B} forward backward.

Notation "A <-> B" := (Bijunction A B) : jwa_type_scope.

Theorem Bijunction_reflexivity : forall (A : Prop), A <-> A.
Proof.
  (* The context gains [A : Prop]; the goal is now [A <-> A]. *)
  intro A.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [A -> A] and [A -> A]. *)
  split.
  - (* The context gains [a : A]; the goal is now [A]. *)
    intro a.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* The context gains [a : A]; the goal is now [A]. *)
    intro a.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
Qed.

(* With reflexivity above, symmetry and transitivity make [<->] an
   equivalence relation: each is the two halves of the [Bijunction] handled
   one direction at a time. *)

Theorem Bijunction_symmetry
  : forall (A : Prop) (B : Prop), (A <-> B) -> (B <-> A).
Proof.
  (* The context gains [A] and [B]; the goal is now
     [(A <-> B) -> (B <-> A)]. *)
  intros A B.
  (* The context gains [h : A <-> B]; the goal is now [B <-> A]. *)
  intro h.
  (* [Bijunction] has one ctor with two fields, so [h] splits into
     [ab : A -> B] and [ba : B -> A]. *)
  destruct h as [ab ba].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [B -> A] and [A -> B]. *)
  split.
  - (* [ba] is a proof of the goal as it stands. *)
    exact ba.
  - (* [ab] is a proof of the goal as it stands. *)
    exact ab.
Qed.

Theorem Bijunction_transitivity
  : forall (A : Prop) (B : Prop) (C : Prop),
      (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
  (* The context gains [A], [B] and [C]; the goal is now
     [(A <-> B) -> (B <-> C) -> (A <-> C)]. *)
  intros A B C.
  (* The context gains [hab : A <-> B]; the goal is now
     [(B <-> C) -> (A <-> C)]. *)
  intro hab.
  (* The context gains [hbc : B <-> C]; the goal is now [A <-> C]. *)
  intro hbc.
  (* [Bijunction] has one ctor with two fields, so [hab] splits into
     [ab : A -> B] and [ba : B -> A]. *)
  destruct hab as [ab ba].
  (* Likewise [hbc] splits into [bc : B -> C] and [cb : C -> B]. *)
  destruct hbc as [bc cb].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [A -> C] and [C -> A]. *)
  split.
  - (* The context gains [a : A]; the goal is now [C]. *)
    intro a.
    (* [bc : B -> C] turns a proof of [B] into a proof of [C], so proving
       [C] reduces to proving [B]; the goal is now [B]. *)
    apply bc.
    (* [ab : A -> B] turns a proof of [A] into a proof of [B]; the goal is
       now [A]. *)
    apply ab.
    (* [a] is a proof of the goal as it stands. *)
    exact a.
  - (* The context gains [c : C]; the goal is now [A]. *)
    intro c.
    (* [ba : B -> A] turns a proof of [B] into a proof of [A], so proving
       [A] reduces to proving [B]; the goal is now [B]. *)
    apply ba.
    (* [cb : C -> B] turns a proof of [C] into a proof of [B]; the goal is
       now [C]. *)
    apply cb.
    (* [c] is a proof of the goal as it stands. *)
    exact c.
Qed.


Theorem Bijunction_elimination_forward
  : forall (A : Prop) (B : Prop), (A <-> B) -> A -> B.
Proof.
  (* The context gains [A] and [B]: [|- (A <-> B) -> A -> B] *)
  intros A B.
  (* The context gains [e : A <-> B]: [|- A -> B] *)
  intro e.
  (* [e] splits into [ab : A -> B] and [ba : B -> A]. *)
  destruct e as [ab ba].
  (* [ab] is a proof of the goal as it stands. *)
  exact ab.
Qed.

Theorem Bijunction_elimination_backward
  : forall (A : Prop) (B : Prop), (A <-> B) -> B -> A.
Proof.
  (* The context gains [A] and [B]: [|- (A <-> B) -> B -> A] *)
  intros A B.
  (* The context gains [e : A <-> B]: [|- B -> A] *)
  intro e.
  (* [e] splits into [ab : A -> B] and [ba : B -> A]. *)
  destruct e as [ab ba].
  (* [ba] is a proof of the goal as it stands. *)
  exact ba.
Qed.
