(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

(* The answer of a three-way comparison,
 * read as "the first argument is ... the second".
 *)
Inductive Comparison : Type :=
  | Lt : Comparison
  | Eq : Comparison
  | Gt : Comparison.

(* [forall (P : Comparison -> Prop) . P Lt -> P Eq -> P Gt -> forall (c : Comparison) . P c] *)
Definition Comparison_induction
  : forall (P : Comparison -> Prop) .
      P Lt ->
      P Eq ->
      P Gt ->
      forall (c : Comparison) . P c
  := fun (P : Comparison -> Prop)
         (lt : P Lt)
         (eq : P Eq)
         (gt : P Gt)
         (c : Comparison) .
       match c with
       | Lt => lt
       | Eq => eq
       | Gt => gt
       end.

(* A module may carry the type's name;
 * its members read [Comparison.transpose].
 *)
Module Comparison. (* Comparison *)

(* [Comparison -> Comparison] *)
Definition transpose := fun (c : Comparison) .
  match c with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

Module transposition. (* transposition *)

(* transposition.involution *)
Theorem involution
  : forall (c : Comparison) . transpose (transpose c) = c.
Proof.
  intros c.
  destruct c as [| |]; simpl in |- *; reflexivity.
Qed.

End transposition. (* transposition *)

End Comparison. (* Comparison *)
