(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Notations.

Module Exists. (* Exists *)

(* [P] is a predicate, not a binder: [forsome x . p] is [Exists (fun x . p)],
 * so the [x] is bound by the [fun] and [Exists] never binds anything.
 *)
Inductive T (A : Type) (P : A -> Prop) : Prop :=
  | introduction : forall (x : A) . P x -> T A P.

Arguments Exists.T {A} P.
Arguments Exists.introduction {A} {P} x _.

Abbreviation Exists := T.

(* The [..] is what lets one [forsome] carry several binders, nesting into
 * one [Exists] each. The dot matches [fun x . body] and [forall x . p].
 *)
Notation "'forsome' x .. y '.' p" := (Exists (fun x . .. (Exists (fun y . p)) ..))
  : jwa_type_scope.

(* A witness, then a proof of [P] at it. [false] cannot be the witness here:
 * the second argument would have to prove [false = true].
 *
 *   Exists.introduction true (Identity.reflexivity true)
 *                       ^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 *                       |     proof
 *                       witness
 *
 * has type [forsome (b : Bool) . b = true].
 *)

End Exists. (* Exists *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Exists], not [Exists.T].
 *)
Abbreviation Exists := Exists.T.

(* Makes [forsome], declared in [Module Exists], usable in every file that
 * imports this one.
 *)
Export (notations) Exists.
