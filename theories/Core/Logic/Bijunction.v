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

(* Bijunction elimination: either direction of a [<->] on its own, so a law
   stated as a [<->] can be used one way without naming its halves. *)

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

(* [<->] is respected by [->] and by [<->] itself. [Core.Logic.Subjunction]
   cannot see [<->], so the congruence of [->] sits here. *)

Theorem Subjunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> ((A1 -> B1) <-> (A2 -> B2)).
Proof.
  (* The context gains [A1], [A2], [B1] and [B2]:
     [|- (A1 <-> A2) -> (B1 <-> B2) -> ((A1 -> B1) <-> (A2 -> B2))] *)
  intros A1 A2 B1 B2.
  (* The context gains [ea : A1 <-> A2]:
     [|- (B1 <-> B2) -> ((A1 -> B1) <-> (A2 -> B2))] *)
  intro ea.
  (* The context gains [eb : B1 <-> B2]: [|- (A1 -> B1) <-> (A2 -> B2)] *)
  intro eb.
  (* [ea] splits into [a12 : A1 -> A2] and [a21 : A2 -> A1]. *)
  destruct ea as [a12 a21].
  (* [eb] splits into [b12 : B1 -> B2] and [b21 : B2 -> B1]. *)
  destruct eb as [b12 b21].
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals: [|- (A1 -> B1) -> A2 -> B2] and [|- (A2 -> B2) -> A1 -> B1]. *)
  split.
  - (* The context gains [f : A1 -> B1]: [|- A2 -> B2] *)
    intro f.
    (* The context gains [a2 : A2]: [|- B2] *)
    intro a2.
    (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
    apply b12.
    (* [f] turns a proof of [A1] into a proof of [B1]: [|- A1] *)
    apply f.
    (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
    apply a21.
    (* [a2] is a proof of the goal as it stands. *)
    exact a2.
  - (* The context gains [f : A2 -> B2]: [|- A1 -> B1] *)
    intro f.
    (* The context gains [a1 : A1]: [|- B1] *)
    intro a1.
    (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
    apply b21.
    (* [f] turns a proof of [A2] into a proof of [B2]: [|- A2] *)
    apply f.
    (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
    apply a12.
    (* [a1] is a proof of the goal as it stands. *)
    exact a1.
Qed.

Theorem Bijunction_congruence
  : forall (A1 : Prop) (A2 : Prop) (B1 : Prop) (B2 : Prop),
      (A1 <-> A2) -> (B1 <-> B2) -> ((A1 <-> B1) <-> (A2 <-> B2)).
Proof.
  (* The context gains [A1], [A2], [B1] and [B2]:
     [|- (A1 <-> A2) -> (B1 <-> B2) -> ((A1 <-> B1) <-> (A2 <-> B2))] *)
  intros A1 A2 B1 B2.
  (* The context gains [ea : A1 <-> A2]:
     [|- (B1 <-> B2) -> ((A1 <-> B1) <-> (A2 <-> B2))] *)
  intro ea.
  (* The context gains [eb : B1 <-> B2]: [|- (A1 <-> B1) <-> (A2 <-> B2)] *)
  intro eb.
  (* [ea] splits into [a12 : A1 -> A2] and [a21 : A2 -> A1]. *)
  destruct ea as [a12 a21].
  (* [eb] splits into [b12 : B1 -> B2] and [b21 : B2 -> B1]. *)
  destruct eb as [b12 b21].
  (* The goal splits into two goals: [|- (A1 <-> B1) -> (A2 <-> B2)] and
     [|- (A2 <-> B2) -> (A1 <-> B1)]. *)
  split.
  - (* The context gains [e : A1 <-> B1]: [|- A2 <-> B2] *)
    intro e.
    (* [e] splits into [ab : A1 -> B1] and [ba : B1 -> A1]. *)
    destruct e as [ab ba].
    (* The goal splits into two goals: [|- A2 -> B2] and [|- B2 -> A2]. *)
    split.
    + (* The context gains [a2 : A2]: [|- B2] *)
      intro a2.
      (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
      apply b12.
      (* [ab] turns a proof of [A1] into a proof of [B1]: [|- A1] *)
      apply ab.
      (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
      apply a21.
      (* [a2] is a proof of the goal as it stands. *)
      exact a2.
    + (* The context gains [b2 : B2]: [|- A2] *)
      intro b2.
      (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
      apply a12.
      (* [ba] turns a proof of [B1] into a proof of [A1]: [|- B1] *)
      apply ba.
      (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
      apply b21.
      (* [b2] is a proof of the goal as it stands. *)
      exact b2.
  - (* The context gains [e : A2 <-> B2]: [|- A1 <-> B1] *)
    intro e.
    (* [e] splits into [ab : A2 -> B2] and [ba : B2 -> A2]. *)
    destruct e as [ab ba].
    (* The goal splits into two goals: [|- A1 -> B1] and [|- B1 -> A1]. *)
    split.
    + (* The context gains [a1 : A1]: [|- B1] *)
      intro a1.
      (* [b21] turns a proof of [B2] into a proof of [B1]: [|- B2] *)
      apply b21.
      (* [ab] turns a proof of [A2] into a proof of [B2]: [|- A2] *)
      apply ab.
      (* [a12] turns a proof of [A1] into a proof of [A2]: [|- A1] *)
      apply a12.
      (* [a1] is a proof of the goal as it stands. *)
      exact a1.
    + (* The context gains [b1 : B1]: [|- A1] *)
      intro b1.
      (* [a21] turns a proof of [A2] into a proof of [A1]: [|- A2] *)
      apply a21.
      (* [ba] turns a proof of [B2] into a proof of [A2]: [|- B2] *)
      apply ba.
      (* [b12] turns a proof of [B1] into a proof of [B2]: [|- B1] *)
      apply b12.
      (* [b1] is a proof of the goal as it stands. *)
      exact b1.
Qed.
