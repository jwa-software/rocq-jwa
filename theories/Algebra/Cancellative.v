(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Cancellative. (* Cancellative *)

Class T {A : Type} (op : A -> A -> A) : Prop :=
  { cancellation
    : forall (x : A) (y : A) (z : A) .
      (op x y = op x z -> y = z) /\ (op x y = op z y -> x = z) }.

Abbreviation Cancellative := T.

End Cancellative. (* Cancellative *)

Abbreviation Cancellative := Cancellative.T.
