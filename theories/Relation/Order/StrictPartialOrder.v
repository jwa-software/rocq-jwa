(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Transitive.

Module StrictPartialOrder. (* StrictPartialOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { irreflexivity :: Irreflexive R
  ; transitivity  :: Transitive  R }.

Abbreviation StrictPartialOrder := T.

End StrictPartialOrder. (* StrictPartialOrder *)

Abbreviation StrictPartialOrder := StrictPartialOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance StrictPartialOrder.irreflexivity.
#[export] Existing Instance StrictPartialOrder.transitivity.
