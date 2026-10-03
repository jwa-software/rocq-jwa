(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Transitive.

Module PartialOrder. (* PartialOrder *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive     R
  ; antisymmetry :: Antisymmetric R
  ; transitivity :: Transitive    R }.

Abbreviation PartialOrder := T.

End PartialOrder. (* PartialOrder *)

Abbreviation PartialOrder := PartialOrder.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance PartialOrder.reflexivity.
#[export] Existing Instance PartialOrder.antisymmetry.
#[export] Existing Instance PartialOrder.transitivity.
