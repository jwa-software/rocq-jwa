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
  (x : A)
  (a : Accessible R x)
  {struct a}
  : P x :=
  step x (fun (y : A) (r : R y x) . recursion step y (descend a r)).

Module recursion. (* recursion *)

(* recursion.unfolding *)
Theorem unfolding
  : forall {A : Type} {P : A -> Type} {R : A -> A -> Prop}
      (step : forall (x : A) . (forall (y : A) . R y x -> P y) -> P x)
      (x : A)
      (a : Accessible R x) .
      recursion step x a
    = step x (fun (y : A) (r : R y x) . recursion step y (Accessible.descend a r)).
Proof.
  intros A P R step x a.
  destruct a as [f].
  reflexivity.
Qed.

(* recursion.independence *)
Theorem independence
  : forall {A : Type} {R : A -> A -> Prop} {P : A -> Type} {step : Descent.Step R P} .
      Descent.Extensional step ->
      forall (x : A) (a : Accessible R x) (b : Accessible R x) .
      recursion step x a = recursion step x b.
Proof.
  (* [A : Type]
   * [R : A -> A -> Prop]
   * [_P : A -> Type]
   * [step : Descent.Step R _P]
   * [extensional : Descent.Extensional step]
   * [x : A]
   * [a : Accessible R x]
   * [b : Accessible R x]
   * :
   * [|- recursion step x a = recursion step x b]
   *)
  intros A R _P step extensional x a b.

  (* [P := fun (x : A) .
   *       forall (a : Accessible R x) (b : Accessible R x) .
   *         recursion step x a = recursion step x b]
   *)
  set (P := fun (x : A) .
            forall (a : Accessible R x) (b : Accessible R x) .
              recursion step x a = recursion step x b).

  (* The context gains
   * [recursor : Descent.Step R P -> forall (x : A) . Accessible R x -> P x]
   *)
  pose proof (recursion (R := R) (P := P)) as recursor.

  (* [at 2] is the occurrence of [P] in the conclusion; the one in the
   * premise stays folded.
   * [recursor : Descent.Step R P ->
   *             forall (x : A) . Accessible R x ->
   *             forall (a : Accessible R x) (b : Accessible R x) .
   *               recursion step x a = recursion step x b]
   *)
  unfold P at 2 in recursor.

  (* [|- Descent.Step R P]
   * [|- Accessible R x]
   *)
  apply recursor.

  - clear a b x.

    (* [|- forall (x : A) . (forall (y : A) . R y x -> P y) -> P x] *)
    simplify Descent.Step in |- *.

    (* [x : A]
     * [recurse : forall (y : A) . R y x -> P y]
     * :
     * [|- P x]
     *)
    intros x recurse.

    (* [|- forall (a : Accessible R x) (b : Accessible R x) .
     *      recursion step x a = recursion step x b]
     *)
    simplify P in |- *.

    (* [a : Accessible R x]
     * [b : Accessible R x]
     * :
     * [|- recursion step x a = recursion step x b]
     *)
    intros a b.

    (* [|- step x (fun (y : A) (r : R y x) . recursion step y (descend a r))
     *  = recursion step x b]
     *)
    rewrite (unfolding step x a) in |- *.

    (* [|- step x (fun (y : A) (r : R y x) . recursion step y (descend a r))
     *  = step x (fun (y : A) (r : R y x) . recursion step y (descend b r))]
     *)
    rewrite (unfolding step x b) in |- *.

    (* [f := fun (y : A) (r : R y x) . recursion step y (descend a r)]
     * :
     * [|- step x f
     *  = step x (fun (y : A) (r : R y x) . recursion step y (descend b r))]
     *)
    set (f := fun (y : A) (r : R y x) . recursion step y (descend a r)).

    (* [g := fun (y : A) (r : R y x) . recursion step y (descend b r)]
     * :
     * [|- step x f = step x g]
     *)
    set (g := fun (y : A) (r : R y x) . recursion step y (descend b r)).

    (* The context gains
     * [H : forall (f : forall (y : A) . R y x -> _P y)
     *             (g : forall (y : A) . R y x -> _P y) .
     *        (forall (y : A) (r : R y x) . f y r = g y r) -> step x f = step x g]
     *)
    pose proof (extensional x) as H.

    (* The context gains
     * [H' : (forall (y : A) (r : R y x) . f y r = g y r) -> step x f = step x g]
     *)
    pose proof (H f g) as H'.

    assert (pointwise : forall (y : A) (r : R y x) . f y r = g y r).
    {
      intros y r.

      (* [|- recursion step y (descend a r)
       *  = recursion step y (descend b r) ]
       *)
      simplify f, g in |- *.

      (* [|- recursion step y a'
       *  = recursion step y b' ]
       *)
      set (a' := descend a r).
      set (b' := descend b r).

      (* The context gains [h : P y] *)
      pose proof (recurse y r) as h.

      (* [h : forall (a : Accessible R y) (b : Accessible R y) .
       *      recursion step y a = recursion step y b]
       *)
      simplify P in h.

      exact (h a' b').
    }

    modus ponens H', pointwise.

  - exact a.
Qed.

End recursion. (* recursion *)

End Accessible. (* Accessible *)
