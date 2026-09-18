(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Group.
  Class T (A : Type) (op : A -> A -> A) (identity : A) (inverse : A -> A) : Prop :=
    { monoid        :: Monoid op identity
    ; left_inverse  : forall (x : A), op (inverse x) x = identity
    ; right_inverse : forall (x : A), op x (inverse x) = identity }.
End Group.

(* The instance hint that [::] declares is scoped to the module it is
 * declared in; this lets it out while the names stay qualified.
 *)
Export (hints) Group.
