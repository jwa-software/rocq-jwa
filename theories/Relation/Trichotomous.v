(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Trichotomous. (* Trichotomous *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { trichotomy
    : forall (x : A) (y : A) . R x y \/ x = y \/ R y x }.

Abbreviation Trichotomous := T.

End Trichotomous. (* Trichotomous *)

Abbreviation Trichotomous := Trichotomous.T.
