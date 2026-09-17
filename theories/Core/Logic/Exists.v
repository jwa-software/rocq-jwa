(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level below, [Core.Logic.Subjunction] carries [->]. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Logic.Subjunction.

(* [P] is a predicate, not a binder: [exists x, p] is [Exists (fun x => p)],
   so the [x] is bound by the [fun] and [Exists] never binds anything. *)
Inductive Exists (A : Type) (P : A -> Prop) : Prop :=
  | Exists_introduction : forall (x : A), P x -> Exists A P.

Arguments Exists {A} P.
Arguments Exists_introduction {A} {P} x _.

(* The [..] is what lets one [exists] carry several binders, nesting into one
   [Exists] each. *)
Notation "'exists' x .. y , p"
  := (Exists (fun x => .. (Exists (fun y => p)) ..)) : jwa_type_scope.

(* A witness, then a proof of [P] at it. [false] cannot be the witness here:
   the second argument would have to prove [false = true].

     Exists_introduction true (Equijunction_reflexivity true)
                         ^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                         |     proof
                         witness

   has type [exists (b : Bool), b = true]. *)
