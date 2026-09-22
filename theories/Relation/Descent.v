(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

Module Descent. (* Descent *)

(* One step of a descent: it answers at [x] from the answers below [x].
 *
 * [R] is what the descent runs on: [R y x] says [y] is below [x].
 * [P] is what it produces: [P x] is the type of the answer at [x].
 *)
(* [forall {A : Type} . (A -> A -> Prop) -> (A -> Type) -> Type] *)
Definition Step :=
  fun {A : Type} (R : A -> A -> Prop) (P : A -> Type) .
    (forall (x : A) . (forall (y : A) . R y x -> P y) -> P x).

(* [step] is extensional when this holds: if [f] and [g] give the same
 * output for every input, then [step x f] and [step x g] are the same.
 *)
(* [forall {A : Type} {R : A -> A -> Prop} {P : A -> Type} . Step R P -> Prop] *)
Definition Extensional :=
  fun {A : Type} {R : A -> A -> Prop} {P : A -> Type} (step : Step R P) .
    (forall (x : A)
       (f : forall (y : A) . R y x -> P y)
       (g : forall (y : A) . R y x -> P y) .
       (forall (y : A) (r : R y x) . f y r = g y r) -> step x f = step x g).

End Descent. (* Descent *)
