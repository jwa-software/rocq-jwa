(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Accessible.
From jwa Require Import Tactics.Simplify.

(* [R] points downwards here: [R y x] says that [y] is below [x]. *)

(* [R] is well founded when every point is accessible. *)
Class WellFounded {A : Type} (R : A -> A -> Prop) : Prop :=
  { accessibility : forall (x : A) . Accessible R x }.

(* [y] is below [x] under [Preimage f R] exactly when [f y] is below [f x]
 * under [R].
 *)
(* [forall {A : Type} {B : Type} . (A -> B) -> (B -> B -> Prop) -> A -> A -> Prop] *)
Definition Preimage :=
  fun {A : Type} {B : Type}
    (f : A -> B) (R : B -> B -> Prop) (y : A) (x : A) .
    (R (f y) (f x)).

Module WellFounded. (* WellFounded *)

(* What a definition by descent is written with: one step, answering at [x]
 * from the answers below [x], together with [R]'s well foundedness.
 *)
(* [forall {A : Type} {P : A -> Type} {R : A -> A -> Prop} {W : WellFounded R} .
 *    (forall (x : A) . (forall (y : A) . R y x -> P y) -> P x) ->
 *    (forall (x : A) . P x)]
 *)
Definition recursion :=
  fun {A : Type} {P : A -> Type} {R : A -> A -> Prop} {W : WellFounded R}
    (step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x)
    (x : A) . (Accessible.recursion step x (accessibility x)).

Module recursion. (* recursion *)

(* recursion.unfolding *)
Theorem unfolding
  : forall {A : Type} {P : A -> Type} {R : A -> A -> Prop} {W : WellFounded R}
      {step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x} .
      Extensional step ->
      (forall (x : A) .
         WellFounded.recursion step x
         = step x (fun (y : A) (r : R y x) . WellFounded.recursion step y)).
Proof.
  intros A P R W step extensional x.
  simplify WellFounded.recursion in |- *.
  rewrite (Accessible.recursion.unfolding step x (accessibility x)) in |- *.
  apply extensional.
  intros y r.
  exact (Accessible.recursion.independence extensional y
           (Accessible.descend (accessibility x) r) (accessibility y)).
Qed.

End recursion. (* recursion *)

Module preimage. (* preimage *)

(* If [f x] is accessible under [R], then [x] is accessible under
 * [Preimage f R].
 *)
(* [forall {A : Type} {B : Type} {f : A -> B} {R : B -> B -> Prop} {b : B} .
 *    (Accessible R b) ->
 *    (forall (x : A) . R (f x) b -> Accessible (Preimage f R) x)]
 *)
(* preimage.accessibility *)
Theorem accessibility
  : forall {A : Type} {B : Type} {f : A -> B} {R : B -> B -> Prop} {b : B} .
      (Accessible R b) ->
      (forall (x : A) . R (f x) b -> Accessible (Preimage f R) x).
Proof.
  intros A B f R b a.
  apply (Accessible.recursion
           (R := R)
           (P := fun (c : B) .
                 forall (x : A) . R (f x) c -> Accessible (Preimage f R) x)).
  - intros c recurse x r.
    apply Accessible_introduction.
    intros y s.
    exact (recurse (f x) r y s).
  - exact a.
Qed.

End preimage. (* preimage *)

(* Well foundedness follows, being accessibility at every point. *)
(* WellFounded.preimage *)
Theorem preimage
  : forall {A : Type} {B : Type} (f : A -> B) (R : B -> B -> Prop) .
      WellFounded R -> WellFounded (Preimage f R).
Proof.
  intros A B f R W.
  exact {| accessibility :=
             fun (x : A) .
               Accessible_introduction
                 (fun (y : A) (s : Preimage f R y x) .
                    preimage.accessibility (accessibility (f x)) y s) |}.
Qed.

End WellFounded. (* WellFounded *)
