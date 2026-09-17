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
