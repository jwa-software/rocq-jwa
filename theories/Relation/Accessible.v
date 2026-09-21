(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

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

(* A step is extensional when it reads the answers below [x] as values only,
 * never as the proofs that produced them.
 *)
(* [forall {A : Type} {P : A -> Type} {R : A -> A -> Prop} .
 *    (forall (x : A) . (forall (y : A) . R y x -> P y) -> P x) -> Prop]
 *)
Definition Extensional :=
  fun {A : Type} {P : A -> Type} {R : A -> A -> Prop}
    (step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x) .
    (forall (x : A)
       (f : forall (y : A) . R y x -> P y)
       (g : forall (y : A) . R y x -> P y) .
       (forall (y : A) (r : R y x) . f y r = g y r) -> step x f = step x g).

Module Accessible. (* Accessible *)

(* Every recursion calls it. Because what it returns is a piece of the proof
 * handed in, and Rocq accepts a recursion only when the argument it recurses
 * on is such a piece.
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

Module recursion. (* recursion *)

(* recursion.unfolding *)
Theorem unfolding
  : forall {A : Type} {P : A -> Type} {R : A -> A -> Prop}
      (step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x)
      (x : A) (a : Accessible R x) .
      Accessible.recursion step x a
      = step x (fun (y : A) (r : R y x) .
                  Accessible.recursion step y (Accessible.descend a r)).
Proof.
  intros A P R step x a.
  destruct a as [f].
  reflexivity.
Qed.

(* recursion.independence *)
Theorem independence
  : forall {A : Type} {P : A -> Type} {R : A -> A -> Prop}
      {step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x} .
      Extensional step ->
      (forall (x : A) (a : Accessible R x) (b : Accessible R x) .
         Accessible.recursion step x a = Accessible.recursion step x b).
Proof.
  intros A P R step extensional x a b.
  apply (Accessible.recursion
           (R := R)
           (P := fun (c : A) .
                 forall (u : Accessible R c) (v : Accessible R c) .
                   Accessible.recursion step c u = Accessible.recursion step c v)).
  - intros c recurse u v.
    rewrite (unfolding step c u) in |- *.
    rewrite (unfolding step c v) in |- *.
    apply extensional.
    intros y r.
    exact (recurse y r (Accessible.descend u r) (Accessible.descend v r)).
  - exact a.
Qed.

End recursion. (* recursion *)

End Accessible. (* Accessible *)
