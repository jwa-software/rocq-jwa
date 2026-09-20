(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

(* What it is for an element to be in a container. The relation is one
 * function taken at every element type at once, which is what makes it a
 * fact about the container rather than about what is stored in it.
 *
 * The class states no law of its own, for the reason [Sized] states none:
 * a relation alone constrains nothing, any [A -> F A -> Prop] filling it.
 * The laws arrive where a second operation is in view -- membership against
 * a join, against a map, against a count -- and belong to whichever class or
 * container carries that operation.
 *)
Class Membership (F : Type -> Type) : Type :=
  { Contains : forall {A : Type} . A -> F A -> Prop }.
