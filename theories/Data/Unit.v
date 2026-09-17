(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. *)
From jwa Require Import Core.All.

(* The type with exactly one element, the unit of [Pair]. The ctor is named
   as the [-junction] ctors are, since [Unit] is to types what [Verum] is to
   propositions. *)
Inductive Unit : Type :=
  | Unit_introduction : Unit.

(* The eliminator behind [induction], written out. Nothing recurses and
   there is one ctor, so the [match] has one branch and no hypothesis. *)
Definition Unit_induction
  : forall (P : Unit -> Prop), P Unit_introduction -> forall (u : Unit), P u
  := fun (P : Unit -> Prop) (base : P Unit_introduction) (u : Unit) =>
       match u with
       | Unit_introduction => base
       end.

(* A module may carry the type's name; its members read
   [Unit.introduction_surjectivity]. *)
Module Unit.

(* [Unit_introduction] is surjective: every element is the one ctor. This is
   the eta rule for [Unit], which an [Inductive] does not compute, so it is
   proved. *)
Theorem introduction_surjectivity : forall (u : Unit), u = Unit_introduction.
Proof.
  intros u. destruct u. reflexivity.
Qed.

End Unit.
