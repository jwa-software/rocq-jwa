(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->], [Structures.Class] the hint database, and the two modules
   below the classes this one is built on. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Relations.Irreflexive.
From jwa Require Import Relations.Transitive.

(* The module is the prefix: the class reads [StrictOrder.R] and its fields
   [StrictOrder.irreflexive] and [StrictOrder.transitive]. *)
Module StrictOrder.
  (* An irreflexive transitive relation, the shape of [<]. The [::] on each
     field declares it an instance as well as a projection, as in
     [Equivalence.R]. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { irreflexive :: Irreflexive.R A relation
    ; transitive  :: Transitive.R  A relation }.
End StrictOrder.

(* The instance hints that [::] declares are scoped to the module they are
   declared in; this lets them out while the names stay qualified. *)
Export (hints) StrictOrder.
