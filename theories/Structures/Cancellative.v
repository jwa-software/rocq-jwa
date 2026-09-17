(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Cancellative.T] and its laws
   [Cancellative.left_cancellation] and [Cancellative.right_cancellation]. *)
Module Cancellative.
  (* A binary operation whose common operand can be struck from both sides
     of an equation, on the left and on the right. Nothing else is asked:
     associativity is [Semigroup.T]'s business. *)
  Class T (A : Type) (op : A -> A -> A) : Prop :=
    { left_cancellation
        : forall (x : A) (y : A) (z : A), op x y = op x z -> y = z
    ; right_cancellation
        : forall (x : A) (y : A) (z : A), op x z = op y z -> x = y }.
End Cancellative.
