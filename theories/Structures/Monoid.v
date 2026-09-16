(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database, and
   [Structures.Semigroup] the class this one is built on. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Structures.Semigroup.

(* A [Semigroup] with an element that changes nothing on either side.
   [identity] is a binder here rather than a global, so the name costs the
   library nothing. The [::] on the first field declares it an instance as
   well as a projection, which is what lets a [Monoid] be used wherever a
   [Semigroup] is asked for. *)
Class Monoid (A : Type) (op : A -> A -> A) (identity : A) : Prop :=
  { Monoid_semigroup      :: Semigroup A op
  ; Monoid_identity_left  : forall (x : A), op identity x = x
  ; Monoid_identity_right : forall (x : A), op x identity = x }.
