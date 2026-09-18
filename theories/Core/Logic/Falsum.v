(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.Notations] opens the scope every notation lives in, [Core.Ltac]
   carries the tactic language, [Core.Logic.Implication] carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Implication.

(* Falsum is the false proposition: no constructor, so no proof.
   [discriminate] looks this up by registered name and reports
   [not found in table: core.False.type] without it. *)

Inductive Falsum : Prop := .

Register Falsum as core.False.type.

(* Ex falso: a proof of [Falsum] proves anything, since there is no case to
   handle. *)
Theorem Falsum_elimination : forall (A : Prop), Falsum -> A.
Proof.
  (* The context gains [A]: [|- Falsum -> A] *)
  intro A.
  (* The context gains [f : Falsum]: [|- A] *)
  intro f.
  (* [f : Falsum], which is what [contradiction] looks for. *)
  contradiction.
Qed.
