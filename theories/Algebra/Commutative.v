(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Algebra.All] would be circular from inside [Algebra]; [Core.All]
 * carries [->] and [=], [Core.Class] the hint database that instance
 * resolution looks up.
 *)
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

(* The module is the prefix: the class reads [Commutative.T] and its law
 * [Commutative.commutativity].
 *)
Module Commutative.
  (* A binary operation whose arguments may be swapped, and nothing more:
   * associativity is [Semigroup]'s business, so the two combine freely.
   *)
  Class T (A : Type) (op : A -> A -> A) : Prop :=
    { commutativity : forall (x : A) (y : A), op x y = op y x }.
End Commutative.
