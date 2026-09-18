(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
 * carries [->] and [~], [Structures.Class] the hint database that instance
 * resolution looks up.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Irreflexive.R] and its law
 * [Irreflexive.irreflexivity].
 *)
Module Irreflexive.
  (* A relation that holds between no element and itself: the shape of a
   * strict order.
   *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { irreflexivity : forall (x : A), ~ relation x x }.
End Irreflexive.
