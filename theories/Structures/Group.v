(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
 * carries [->] and [=], [Structures.Class] the hint database, and
 * [Structures.Monoid] the class this one is built on.
 *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Structures.Monoid.

(* The module is the prefix: the class reads [Group.T] and its fields
 * [Group.monoid], [Group.left_inverse] and [Group.right_inverse].
 *)
Module Group.
  (* A [Monoid.T] in which every element is undone by another: [inverse x]
   * on either side of [x] gives the identity. [inverse] is a binder here
   * rather than a global, as [identity] is in [Monoid.T]. The [::] on the
   * first field declares it an instance as well as a projection, which is
   * what lets a group be used wherever a monoid is asked for.
   *)
  Class T (A : Type) (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
    { monoid        :: Monoid.T A op identity
    ; left_inverse  : forall (x : A), op (inverse x) x = identity
    ; right_inverse : forall (x : A), op x (inverse x) = identity }.
End Group.

(* The instance hint that [::] declares is scoped to the module it is
 * declared in; this lets it out while the names stay qualified.
 *)
Export (hints) Group.
