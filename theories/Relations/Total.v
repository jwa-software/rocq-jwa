(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
 * carries [\/], [Structures.Class] the hint database that instance
 * resolution looks up.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Total.R] and its law
 * [Total.totality].
 *)
Module Total.
  (* A relation that holds one way or the other between any two elements:
   * what makes an order linear.
   *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { totality : forall (x : A) (y : A), relation x y \/ relation y x }.
End Total.
