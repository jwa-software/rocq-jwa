(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Semigroup.T] and its
   law [Semigroup.associativity], the bare name being spent nowhere. *)
Module Semigroup.
  (* An associative binary operation and nothing more. *)
  Class T (A : Type) (op : A -> A -> A) : Prop :=
    { associativity
        : forall (x : A) (y : A) (z : A), op (op x y) z = op x (op y z) }.
End Semigroup.
