(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. *)
From jwa Require Import Core.All.

(* The answer of a three-way comparison, read as "the first argument is
   ... the second". *)
Inductive Comparison : Type :=
  | Lt : Comparison
  | Eq : Comparison
  | Gt : Comparison.

(* The eliminator behind [induction], written out. Nothing recurses: one
   branch per ctor and no hypothesis. *)
Definition Comparison_induction
  : forall (P : Comparison -> Prop),
      P Lt -> P Eq -> P Gt -> forall (c : Comparison), P c
  := fun (P : Comparison -> Prop)
         (lt : P Lt) (eq : P Eq) (gt : P Gt)
         (c : Comparison) =>
       match c with
       | Lt => lt
       | Eq => eq
       | Gt => gt
       end.

(* A module may carry the type's name; its members read
   [Comparison.converse]. *)
Module Comparison.

Definition converse := fun (c : Comparison) =>
  match c with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

Theorem converse_involution
  : forall (c : Comparison), converse (converse c) = c.
Proof.
  intros c.
  destruct c as [| |]; simpl in |- *; reflexivity.
Qed.

End Comparison.
