(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

(* The type with no element, the unit of [Sum]. No ctor, so the definition
 * ends at the [:=]; [Empty] is to types what [Falsum] is to propositions.
 *)
Inductive Empty : Type := .

(* The eliminator behind [induction], written out. With no ctor the [match]
 * has no branch, and that is the whole proof: there is no [e] to prove
 * anything about.
 *)
(* [forall (P : Empty -> Prop) (e : Empty), P e] *)
Definition Empty_induction
  : forall (P : Empty -> Prop) (e : Empty), P e
  := fun (P : Empty -> Prop) (e : Empty) =>
       match e with | end.

(* A module may carry the type's name; its members read [Empty.elimination]. *)
Module Empty.

(* From nothing, anything: the [Type]-level counterpart of [Falsum.elimination]. *)
(* [forall (A : Type), Empty -> A] *)
Definition elimination := fun (A : Type) (e : Empty) =>
  match e return A with | end.

End Empty.
