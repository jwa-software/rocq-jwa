(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]. [Core.Ltac] is needed by
   the theorem at the end of this file. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.

(* [discriminate] looks both of these up by registered name and reports
   [not found in table: core.True.type] without them. *)

Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .

Register True as core.True.type.
Register False as core.False.type.
Register I as core.True.I.

Record And (A : Prop) (B : Prop) : Prop := { And_left : A ; And_right : B }.

Arguments And_left  {A} {B} _.
Arguments And_right {A} {B} _.

Inductive Or (A : Prop) (B : Prop) : Prop :=
  | Or_left  : A -> Or A B
  | Or_right : B -> Or A B.

(* The unused side is not determined by the argument. It comes from the
   expected type, and a use that has none needs [@Or_left]. *)
Arguments Or_left  {A} {B} a.
Arguments Or_right {A} {B} b.

(* [Prop -> Prop] *)
Definition Not := fun (A : Prop) => A -> False.

(* [Prop -> Prop -> Prop] *)
Definition Biconditional := fun (A : Prop) (B : Prop) =>
  And (A -> B) (B -> A).

Notation "A /\ B"  := (And A B)           : jwa_type_scope.
Notation "A \/ B"  := (Or  A B)           : jwa_type_scope.
Notation "~ A"     := (Not A)             : jwa_type_scope.
Notation "A <-> B" := (Biconditional A B) : jwa_type_scope.

(* The conditional is [->] from [Core.Notations]. Its two basic facts are the
   identity function and function composition, stated as theorems. *)

Theorem Conditional_reflexivity : forall (A : Prop), A -> A.
Proof.
  (* The context gains [A : Prop]; the goal is now [A -> A]. *)
  intro A.
  (* The context gains [a : A]; the goal is now [A]. *)
  intro a.
  (* [a] is a proof of the goal as it stands. *)
  exact a.
Qed.

Theorem Conditional_transitivity
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

Theorem Biconditional_reflexivity : forall (A : Prop), A <-> A.
Proof.
  (* The context gains [A : Prop]; the goal is now [A <-> A]. *)
  intro A.
  (* The goal goes from [A <-> A] to [And (A -> A) (A -> A)]. *)
  unfold Biconditional in |- *.
  (* [And] has one ctor with two fields, so the goal splits into two goals:
     [A -> A] and [A -> A]. *)
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
