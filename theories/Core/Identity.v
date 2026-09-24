(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Falsum.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Gottfried Leibniz, seventeenth century: two things are the same exactly
 * when no property tells them apart. If everything true of [x] is true of
 * [y], there is nothing left over that could distinguish them, so there is
 * nothing left to mean by "different".
 *)
(* [forall {A : Type} . A -> A -> Prop] *)
Definition Leibniz := fun {A : Type} (x : A) (y : A) .
  forall (P : A -> Prop) . P x -> P y.

(* The identity type, which [=] spells: two terms of one type that are the
 * same term. [x] is a parameter and the second argument an index, so the
 * one ctor can only ever produce [Identity A x x]. A proof that [x] equals
 * something will exist only when that something is [x].
 *)
Inductive Identity (A : Type) (x : A) : A -> Prop :=
  | Identity_introduction : Identity A x x.

Arguments Identity              {A} x _.
Arguments Identity_introduction {A} x.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "x = y" := (Identity x y)
  : jwa_type_scope.

(* The same with no arguments, for where the relation is passed rather than
 * applied.
 *)
Notation "'(=)'" := Identity (only parsing)
  : jwa_type_scope.

(* Carries a proof across the equation. The tactics fill the slots of
 * [core.eq.ind] by position, so this order -- [P] before the proof and
 * [y] after it -- is the order the registration needs.
 *)
Theorem Identity_induction
  : forall {A : Type} (x : A) (P : A -> Prop) . P x ->
    forall (y : A) . x = y -> P y.
Proof.
  (* The context gains [A], [x], [P] and [p]:
   * [|- forall (y : A) . x = y -> P y]
   *)
  intros A x P p.
  (* The context gains [y] and [e]: [|- P y] *)
  intros y e.
  (* [x] is a parameter, so fixed for every ctor; [y] is an index, so each
   * ctor chooses it. [Identity_introduction] is the only ctor and it
   * chooses the parameter, which is why [y] becomes [x] and not the other
   * way: [|- P x]
   *)
  match e with end.
  (* [p] is a proof of the goal as it stands. *)
  ipso p.
Defined.

(* A module may carry the type's name; its laws read [Identity.symmetry]. *)
Module Identity.

(* Every term equals itself: the reflexivity law of [=]. *)
Theorem reflexivity
  : forall {A : Type} (x : A) . x = x.
Proof.
  intros A x.
  ipso (Identity_introduction x).
Defined.

Theorem symmetry
  : forall {A : Type} {x : A} {y : A} . x = y -> y = x.
Proof.
  intros A x y e.
  match e with end.
  quod idem est.
Defined.

Theorem transitivity
  : forall {A : Type} {x : A} {y : A} {z : A} . x = y -> y = z -> x = z.
Proof.
  intros A x y z e1 e2.
  match e2 with end.
  ipso e1.
Defined.

Theorem congruence
  : forall {A : Type} {B : Type} {x : A} {y : A} (f : A -> B) . x = y -> f x = f y.
Proof.
  intros A B x y f e.
  match e with end.
  quod idem est.
Defined.

Local Theorem cancellation
  : forall {A : Type} {x : A} {y : A} (r : x = y) .
      transitivity (symmetry r) r = reflexivity y.
Proof.
  intros A x y r.
  (*
   * [|- transitivity
   *       (symmetry (Identity_introduction x))
   *       (Identity_introduction x)
   *     = reflexivity x]
   *)
  match r with end.
  lemma facto : Identity_introduction &x = Identity_introduction &x.
  {
    quod idem est.
  }

  let proof facto
    : Identity_introduction &x = reflexivity &x
    := &facto.

  let proof facto
    : transitivity
        (Identity_introduction &x)
        (Identity_introduction &x)
      = reflexivity &x
    := &facto.

  let proof facto
    : transitivity
        (symmetry (Identity_introduction &x))
        (Identity_introduction &x)
      = reflexivity &x
    := &facto.

  ipso &facto.
Qed.

Module hedberg. (* hedberg *)

(* [forall {A : Type} .
 *    (forall (x : A) (y : A) . x = y \/ ~ (x = y)) ->
 *    forall (x : A) (y : A) . x = y -> x = y]
 *)
(* hedberg.decided *)
Local Definition decided
  :=
  fun {A : Type}
    (decide : forall (x : A) (y : A) . x = y \/ ~ (x = y))
    (x : A) (y : A) (e : x = y) .
    match decide x y with
    | Disjunction.L l => l
    | Disjunction.R r => let falsum: Falsum := (r e) in Falsum.elimination (x = y) falsum
    end.

(* hedberg.constancy *)
Local Theorem constancy
  : forall {A : Type}
      (decide : forall (x : A) (y : A) . x = y \/ ~ (x = y))
      (x : A) (y : A) (p : x = y) (q : x = y) .
      decided decide x y p = decided decide x y q.
Proof.
  intros A decide x y p q.
  simpl decided in |- *.
  match (decide x y) with | r | n end.
  - quod idem est.
  - simpl Negation in n.
    let proof absurdity := n p.
    ex absurdity quodlibet.
Qed.

(* hedberg.retraction *)
Local Theorem retraction
  : forall {A : Type}
      (decide : forall (x : A) (y : A) . x = y \/ ~ (x = y))
      (x : A) (y : A) (e : x = y) .
      transitivity
        (symmetry (decided decide x x (reflexivity x)))
        (decided decide x y e)
      = e.
Proof.
  intros A decide x y p.
  match p with end.
  ipso (cancellation (decided decide x x (reflexivity x))).
Qed.

(* hedberg.uniqueness *)
Theorem uniqueness
  : forall {A : Type} .
      (forall (x : A) (y : A) . x = y \/ ~ (x = y)) ->
      forall (x : A) (y : A) (p : x = y) (q : x = y) . p = q.
Proof.
  intros A decide x y p q.

  let proof rp := retraction decide x y p.
  let proof rq := retraction decide x y q.
  let proof c  := constancy  decide x y p q.

  let base := decided decide x x (reflexivity x)
  in *.

  let shift := fun (e : x = y) . transitivity (symmetry base) e.

  let proof step := congruence shift c.
  let proof rp' := symmetry rp.
  ipso (transitivity rp' (transitivity step rq)).
Qed.

End hedberg. (* hedberg *)

End Identity.

(* [rewrite] builds its proof term out of these two, which carry a proof
 * along the equation into [Type], forwards and backwards. [Defined] keeps
 * them transparent.
 *)

Definition Identity_rewrite_forward
  : forall (A : Type) (x : A) (P : A -> Type) .
      P x -> forall (y : A) . x = y -> P y.
Proof.
  intros A x P p.
  intros y e.
  match e with end.
  ipso p.
Defined.

Definition Identity_rewrite_backward
  : forall (A : Type) (x : A) (y : A) (P : A -> Type) .
      P y -> x = y -> P x.
Proof.
  intros A x y P p.
  intro e.
  match e with end.
  ipso p.
Defined.

(* [Register Scheme] is what points [rewrite] at them. The kinds [rew] and
 * [rew_r] are Rocq's own, fixed like a registration key.
 *)
Register Scheme Identity_rewrite_forward  as rew   for Identity.
Register Scheme Identity_rewrite_backward as rew_r for Identity.

(* [build_eqdata_gen] in rocqlib.ml demands exactly these six; a single
 * missing one surfaces as [No primitive equality found].
 *)
Register Identity              as core.eq.type.
Register Identity_introduction as core.eq.refl.
Register Identity_induction    as core.eq.ind.
Register Identity.symmetry     as core.eq.sym.
Register Identity.transitivity as core.eq.trans.
Register Identity.congruence   as core.eq.congr.
