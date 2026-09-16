(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Transitive.R] and its
   law [Transitive.transitivity], the bare name being spent nowhere. *)
Module Transitive.
  (* A relation that chains: from [x] to [y] and from [y] to [z] gives from
     [x] to [z]. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { transitivity
        : forall (x : A) (y : A) (z : A),
            relation x y -> relation y z -> relation x z }.
End Transitive.
