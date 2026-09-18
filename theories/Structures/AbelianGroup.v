(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
 * carries [->], [Structures.Class] the hint database, and
 * [Structures.Commutative] and [Structures.Group] the two classes this one
 * joins.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Group.

(* The module is the prefix: the class reads [AbelianGroup.T] and its
 * fields [AbelianGroup.group] and [AbelianGroup.commutative].
 *)
Module AbelianGroup.
  (* A [Group.T] whose operation commutes. Nothing is stated twice: the two
   * fields are the two classes, and the [::] on each declares it an
   * instance as well as a projection, so an abelian group is found
   * wherever either is asked for.
   *)
  Class T (A : Type) (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
    { group       :: Group.T A op identity inverse
    ; commutative :: Commutative.T A op }.
End AbelianGroup.

(* The instance hints that [::] declares are scoped to the module; this
 * lets them out while the names stay qualified.
 *)
Export (hints) AbelianGroup.
