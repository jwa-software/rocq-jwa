(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]. [Core.Logic] and [Core.Eq]
   only [Import] the notations, so [~] and [=] have to be required here too;
   [Core.Ltac] is what makes [Proof] parse at all. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.
From jwa Require Import Core.Eq.

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.

Theorem Bool_distinctness : ~ (true = false).
Proof.
  (* The goal goes from [~ (true = false)] to [true = false -> False]. *)
  unfold Not.
  (* The goal goes from [true = false -> False] to [False], and the context
     gains [e : true = false]. *)
  intro e.
  (* [e] claims [true = false], but the only way to build an equality is
     [Eq_reflexivity], whose two sides are the same term, and [true] and
     [false] are different ctors. No such proof exists, and from that
     impossibility [discriminate] proves the goal [False]. *)
  discriminate e.
Qed.
