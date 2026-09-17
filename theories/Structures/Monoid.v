(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database, and
   [Structures.Semigroup] the class this one is built on. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Structures.Semigroup.

(* The module is the prefix: the class reads [Monoid.T] and its
   fields [Monoid.semigroup], [Monoid.left_identity] and
   [Monoid.right_identity]. *)
Module Monoid.
  (* A [Semigroup.T] with an element that changes nothing on either
     side. [identity] is a binder here rather than a global, so the name
     costs the library nothing. The [::] on the first field declares it an
     instance as well as a projection, which is what lets a monoid be used
     wherever a semigroup is asked for. *)
  Class T (A : Type) (op : A -> A -> A) (identity : A) : Prop :=
    { semigroup      :: Semigroup.T A op
    ; left_identity  : forall (x : A), op identity x = x
    ; right_identity : forall (x : A), op x identity = x }.
End Monoid.

(* The instance hint that [::] declares is scoped to the module it is
   declared in; this lets it out while the names stay qualified. Without it
   [Semigroup.T A op] is not found from a [Monoid.T A op e]
   outside the module. *)
Export (hints) Monoid.
