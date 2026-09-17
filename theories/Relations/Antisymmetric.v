(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Antisymmetric.R] and its law
   [Antisymmetric.antisymmetry]. *)
Module Antisymmetric.
  (* A relation that holds both ways only between equal elements: what
     separates an order from a preorder. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { antisymmetry
        : forall (x : A) (y : A), relation x y -> relation y x -> x = y }.
End Antisymmetric.
