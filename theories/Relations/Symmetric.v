(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Symmetric.Relation] and its
   law [Symmetric.symmetry], the bare name being spent nowhere. *)
Module Symmetric.
  (* A relation that holds in both directions or in neither. *)
  Class Relation (A : Type) (R : A -> A -> Prop) : Prop :=
    { symmetry : forall (x : A) (y : A), R x y -> R y x }.
End Symmetric.
