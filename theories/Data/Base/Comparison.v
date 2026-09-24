(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

(* A module may carry the type's name;
 * its members read [Comparison.transpose].
 * The type and its ctors are declared inside it: a ctor at the top level is
 * rebound by any later file declaring the same name, silently and with no
 * warning.
 *)
Module Comparison. (* Comparison *)

(* The answer of a three-way comparison,
 * read as "the first argument is ... the second".
 *)
Inductive T : Type :=
  | Lt : T
  | Eq : T
  | Gt : T.

(* The carrier is named [T] so that the type itself reads [Comparison] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End Comparison].
 *)
Abbreviation Comparison := T.

(* [forall (P : Comparison -> Prop) . P Lt -> P Eq -> P Gt -> forall (c : Comparison) . P c] *)
Definition induction
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
  match c with | | | end; simpl in |- *; quod idem est.
Qed.

End transposition. (* transposition *)

End Comparison. (* Comparison *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Comparison], not [Comparison.T].
 *)
Abbreviation Comparison := Comparison.T.
