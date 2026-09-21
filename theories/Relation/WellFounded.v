(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

(* [R] points downwards throughout this file: its first argument is the
 * lower one, so [R y x] says that [y] is below [x]. [Accessible R x] holds
 * when every [y] below [x] is accessible, which under "is less than" makes
 * every number accessible, the smallest for free and the rest standing on
 * it. The proof is what a recursion descends on, since the proof for [y]
 * sits inside the proof for [x].
 *)
Inductive Accessible {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
  | Accessible_introduction
    : (forall (y : A) . R y x -> Accessible R y) -> Accessible R x.

(* [A], [R] and [x] are all read off the proof, so none is written. *)
Arguments Accessible_introduction {A} {R} {x} descend.

Module Accessible. (* Accessible *)

(* Every recursion in this file calls it. Because what it returns is a
 * piece of the proof handed in, and Rocq accepts a recursion only when the
 * argument it recurses on is such a piece.
 *)
(* [forall {A : Type} {R : A -> A -> Prop} {x : A} {y : A} .
 *    Accessible R x -> R y x -> Accessible R y]
 *)
Definition descend :=
  fun {A : Type} {R : A -> A -> Prop} {x : A} {y : A}
    (a : Accessible R x) (r : R y x) .
    match a with
    | Accessible_introduction step => step y r
    end.

(* This is where the recursion happens. *)
(* [forall {A : Type} {P : A -> Type} {R : A -> A -> Prop} .
 *    (forall (x : A) . (forall (y : A) . R y x -> P y) -> P x) ->
 *    (forall (x : A) . Accessible R x -> P x)]
 *)
Fixpoint recursion
  {A : Type} {P : A -> Type} {R : A -> A -> Prop}
  (step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x)
  (x : A) (a : Accessible R x) {struct a} : P x :=
  step x (fun (y : A) (r : R y x) . recursion step y (descend a r)).

End Accessible. (* Accessible *)

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
