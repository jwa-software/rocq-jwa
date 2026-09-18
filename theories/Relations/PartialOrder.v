(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database, and the three
   modules below the classes this one is built on. *)
From jwa Require Import Core.All.
From jwa Require Import Relations.Reflexive.
From jwa Require Import Relations.Antisymmetric.
From jwa Require Import Relations.Transitive.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [PartialOrder.R] and its fields
   [PartialOrder.reflexive] and so on. *)
Module PartialOrder.
  (* A reflexive antisymmetric transitive relation, the shape of [<=]. The
     [::] on each field declares it an instance as well as a projection, as
     in [Equivalence.R]. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { reflexive     :: Reflexive.R     A relation
    ; antisymmetric :: Antisymmetric.R A relation
    ; transitive    :: Transitive.R    A relation }.
End PartialOrder.

(* The instance hints that [::] declares are scoped to the module they are
   declared in; this lets them out while the names stay qualified. *)
Export (hints) PartialOrder.
