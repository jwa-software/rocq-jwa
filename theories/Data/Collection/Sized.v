(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Data.Assert.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Dialect.ExFalso.

(* How many elements a container holds. The count is one function taken at
 * every element type at once, which is what makes it a fact about the
 * container's shape rather than about what is stored in it.
 *
 * The class states no law of its own: any [F A -> NatWithZero] fills it. A
 * law would have to relate the count to a second operation, so it belongs
 * to whichever class carries that operation, not here.
 *)
Class Sized (F : Type -> Type) : Type :=
  { cardinality : forall {A : Type} . F A -> NatWithZero }.

Module Sized. (* Sized *)

(* [Bool]'s scope is opened for the [!] of [is_not_empty]. *)
Local Open Scope jwa_bool_scope.

(* [forall {F : Type -> Type} {S : Sized F} {A : Type} . F A -> Bool] *)
Definition is_empty := fun {F : Type -> Type} {S : Sized F} {A : Type} (x : F A) .
  match cardinality x with
  | NatWithZero.Zero       => true
  | NatWithZero.Positive _ => false
  end.

(* [forall {F : Type -> Type} {S : Sized F} {A : Type} . F A -> Bool] *)
Definition is_not_empty := fun {F : Type -> Type} {S : Sized F} {A : Type} (x : F A) . ! is_empty x.

Module emptiness. (* emptiness *)

(* emptiness.reflection *)
Theorem reflection
  : forall {F : Type -> Type} {S : Sized F} {A : Type}
      (x : F A) .
      Assert (is_empty x) <-> cardinality x = NatWithZero.Zero.
Proof.
  intros F S A x.
  simpl is_empty in |- *.
  match (cardinality x) per c with | | p end; divide et impera; simpl in |- *.
  - intro h.
    quod idem est.
  - intro e.
    ipso I.
  - intro h.
    ex h quodlibet.
  - intro e.
    discriminate e.
Qed.

End emptiness. (* emptiness *)

Module inhabitation. (* inhabitation *)

(* inhabitation.reflection *)
Theorem reflection
  : forall {F : Type -> Type} {S : Sized F} {A : Type} (x : F A) .
      Assert (is_not_empty x) <-> ~ (cardinality x = NatWithZero.Zero).
Proof.
  intros F S A x.
  simpl is_not_empty in |- *.
  let proof n := Assert.negation (is_empty x).
  let proof c := Negation.congruence (emptiness.reflection x).
  ipso (Biconditional.transitivity n c).
Qed.

End inhabitation. (* inhabitation *)

End Sized. (* Sized *)
