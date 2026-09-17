(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Cancellative.T] and its laws
   [Cancellative.cancellation_left] and [Cancellative.cancellation_right]. *)
Module Cancellative.
  (* A binary operation whose common operand can be struck from both sides
     of an equation, on the left and on the right. Nothing else is asked:
     associativity is [Semigroup.T]'s business. *)
  Class T (A : Type) (op : A -> A -> A) : Prop :=
    { cancellation_left
        : forall (x : A) (y : A) (z : A), op x y = op x z -> y = z
    ; cancellation_right
        : forall (x : A) (y : A) (z : A), op x z = op y z -> x = y }.
End Cancellative.
