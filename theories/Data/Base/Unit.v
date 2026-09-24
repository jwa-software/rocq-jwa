(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

(* The type with exactly one element, the unit of [Product]: [Unit] is to
 * types what [Verum] is to propositions.
 *)
Inductive Unit : Type :=
  | Unit_introduction : Unit.

(* [forall (P : Unit -> Prop) . P Unit_introduction -> forall (u : Unit) . P u] *)
Definition Unit_induction
  : forall (P : Unit -> Prop) . P Unit_introduction -> forall (u : Unit) . P u
  := fun (P : Unit -> Prop) (base : P Unit_introduction) (u : Unit) .
       match u with
       | Unit_introduction => base
       end.

(* A module may carry the type's name; its members read [Unit.surjectivity]. *)
Module Unit.

(* [Unit_introduction] is surjective: every element is the one ctor. This is
 * the eta rule for [Unit], which an [Inductive] does not compute, so it is
 * proved.
 *)
Theorem surjectivity : forall (u : Unit) . u = Unit_introduction.
Proof.
  intros u. match u with end. reflexivity.
Qed.

End Unit.
