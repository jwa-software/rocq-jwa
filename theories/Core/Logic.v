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
