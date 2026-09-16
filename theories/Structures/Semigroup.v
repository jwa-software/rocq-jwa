(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* An associative binary operation and nothing more. The field name is
   prefixed because a class field becomes a top-level projection, so a bare
   [associativity] would spend that name for the whole library. *)
Class Semigroup (A : Type) (op : A -> A -> A) : Prop :=
  { Semigroup_associativity
      : forall (x : A) (y : A) (z : A), op (op x y) z = op x (op y z) }.
