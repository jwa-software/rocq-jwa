(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
 * carries [->], [Structures.Class] the hint database, and the two modules
 * below the classes this one is built on.
 *)
From jwa Require Import Core.All.
From jwa Require Import Relations.PartialOrder.
From jwa Require Import Relations.Total.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [TotalOrder.R] and its fields
 * [TotalOrder.partial_order] and [TotalOrder.total].
 *)
Module TotalOrder.
  (* A partial order in which any two elements compare, the shape of [<=]
   * on numbers. The [::] on each field declares it an instance as well as a
   * projection, as in [Equivalence.R].
   *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { partial_order :: PartialOrder.R A relation
    ; total         :: Total.R A relation }.
End TotalOrder.

(* The instance hints that [::] declares are scoped to the module they are
 * declared in; this lets them out while the names stay qualified.
 *)
Export (hints) TotalOrder.
