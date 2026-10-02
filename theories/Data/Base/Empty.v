(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

Module Empty.

(* The type with no element, the unit of [Coproduct]. No ctor, so the
 * definition ends at the [:=]; [Empty] is to types what [Falsum] is to
 * propositions.
 *)
Inductive T : Type := .

Abbreviation Empty := T.

(* The eliminator that [match ... per] takes, written out. With no ctor the [match]
 * has no branch, and that is the whole proof: there is no [e] to prove
 * anything about.
 *)
(* [forall (P : Empty -> Prop) (e : Empty) . P e] *)
Definition induction
  : forall (P : Empty -> Prop) (e : Empty) . P e
  := fun (P : Empty -> Prop) (e : Empty) .
       match e with | end.

(* From nothing, anything: the [Type]-level counterpart of [Falsum.elimination]. *)
(* [forall (A : Type) . Empty -> A] *)
Definition elimination := fun (A : Type) (e : Empty) .
  match e return A with | end.

End Empty.

(* The counterpart of the abbreviation inside the module: a client writes
 * [Empty], not [Empty.T].
 *)
Abbreviation Empty := Empty.T.
