(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Notations.

(* [P] is a predicate, not a binder: [exists x . p] is [Exists (fun x . p)],
 * so the [x] is bound by the [fun] and [Exists] never binds anything.
 *)
Inductive Exists (A : Type) (P : A -> Prop) : Prop :=
  | Exists_introduction : forall (x : A) . P x -> Exists A P.

Arguments Exists {A} P.
Arguments Exists_introduction {A} {P} x _.

(* The [..] is what lets one [exists] carry several binders, nesting into
 * one [Exists] each. The dotted spelling matches [fun x . body] and
 * [forall x . p]; the comma stays until the rest of the tree is written
 * with the dot.
 *)
Notation "'exists' x .. y , p" := (Exists (fun x . .. (Exists (fun y . p)) ..))
  : jwa_type_scope.
Notation "'exists' x .. y '.' p" := (Exists (fun x . .. (Exists (fun y . p)) ..))
  : jwa_type_scope.

(* A witness, then a proof of [P] at it. [false] cannot be the witness here:
 * the second argument would have to prove [false = true].
 *
 *   Exists_introduction true (Identity.reflexivity true)
 *                       ^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 *                       |     proof
 *                       witness
 *
 * has type [exists (b : Bool) . b = true].
 *)
