(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level below, [Core.Ltac] carries the tactic language,
   [Core.Logic.Conditional] carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.And.

(* [Prop -> Prop -> Prop] *)
Definition Biconditional := fun (A : Prop) (B : Prop) =>
  And (A -> B) (B -> A).

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
