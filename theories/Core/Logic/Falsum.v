(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Falsum is the false proposition: no constructor, so no proof.
 * [discriminate] looks this up by registered name and reports
 * [not found in table: core.False.type] without it.
 *)

Inductive Falsum : Prop := .

Register Falsum as core.False.type.

(* A module may carry the type's name; its laws read [Falsum.elimination]. *)
Module Falsum.

(* Ex falso: a proof of [Falsum] proves anything, since there is no case to
 * handle.
 *)
Theorem elimination : forall (A : Prop) . Falsum -> A.
Proof.
  intro A.
  intro f.
  contradiction f.
Qed.

End Falsum.
