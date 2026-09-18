(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
 * carries [->], [Structures.Class] the hint database that instance
 * resolution looks up.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The class sits in a module named after the property, so the class reads
 * [Reflexive.R] and its law [Reflexive.reflexivity]: the module is
 * the prefix, and the bare [reflexivity] is spent nowhere. The tactic of
 * that name is unaffected, tactics and constants being separate
 * namespaces.
 *)
Module Reflexive.
  (* A relation that holds between every element and itself. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { reflexivity : forall (x : A), relation x x }.
End Reflexive.
