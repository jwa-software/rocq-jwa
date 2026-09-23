(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Descent.
From jwa Require Import Relation.Induced.

(* [R] points downwards here: [R y x] says that [y] is below [x]. *)

(* [R] is well founded when every point is accessible. *)
Class WellFounded {A : Type} (R : A -> A -> Prop) : Prop :=
  { accessibility : forall (x : A) . Accessible R x }.

Module WellFounded. (* WellFounded *)

(* What a definition by descent is written with: one step, answering at [x]
 * from the answers below [x], together with [R]'s well foundedness.
 *)
(* [forall {A : Type} {R : A -> A -> Prop} {P : A -> Type} {W : WellFounded R} .
 *    Descent.Step R P -> (forall (x : A) . P x)]
 *)
Definition recursion :=
  fun {A : Type} {R : A -> A -> Prop} {P : A -> Type} {W : WellFounded R}
    (step : Descent.Step R P) (x : A) .
    (Accessible.recursion step x (accessibility x)).

Module recursion. (* recursion *)

(* recursion.unfolding *)
Theorem unfolding
  : forall {A : Type} {R : A -> A -> Prop} {P : A -> Type} {W : WellFounded R}
      {step : Descent.Step R P} .
      Descent.Extensional step ->
      forall (x : A) .
        recursion step x
      = step x (fun (y : A) (r : R y x) . recursion step y).
Proof.
  intros A R P W step extensional x.
  simpl recursion in |- *.
  rewrite (Accessible.recursion.unfolding step x (accessibility x)) in |- *.
  apply extensional.
  intros y r.
  ipso (Accessible.recursion.independence
          extensional
          y
          (Accessible.descend (accessibility x) r)
          (accessibility y)).
Qed.

End recursion. (* recursion *)

Module induced. (* induced *)

(* If [f x] is accessible under [R], then [x] is accessible under
 * [Induced R f].
 *)
(* [forall {A : Type} {B : Type} {R : B -> B -> Prop} {f : A -> B} {b : B} .
 *    (Accessible R b) ->
 *    (forall (x : A) . R (f x) b -> Accessible (Induced R f) x)]
 *)
(* induced.accessibility *)
Theorem accessibility
  : forall {A : Type} {B : Type} {R : B -> B -> Prop} {f : A -> B} {b : B} .
      (Accessible R b) ->
      (forall (x : A) . R (f x) b -> Accessible (Induced R f) x).
Proof.
  intros A B R f b a.
  apply (Accessible.recursion
           (R := R)
           (P := fun (c : B) .
                 forall (x : A) . R (f x) c -> Accessible (Induced R f) x)).
  - intros c recurse x r.
    apply Accessible_introduction.
    intros y s.
    ipso (recurse (f x) r y (Induced.elimination s)).
  - ipso a.
Qed.

End induced. (* induced *)

(* Well foundedness follows, being accessibility at every point. *)
(* WellFounded.induced *)
Theorem induced
  : forall {A : Type} {B : Type} (R : B -> B -> Prop) (f : A -> B) .
      WellFounded R -> WellFounded (Induced R f).
Proof.
  intros A B R f W.
  ipso {| accessibility :=
             fun (x : A) .
               Accessible_introduction
                 (fun (y : A) (s : Induced R f y x) .
                    induced.accessibility (accessibility (f x)) y
                                          (Induced.elimination s)) |}.
Qed.

End WellFounded. (* WellFounded *)
