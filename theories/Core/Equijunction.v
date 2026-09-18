(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Subjunction.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Gottfried Leibniz, seventeenth century: two things are the same exactly
 * when no property tells them apart. If everything true of [x] is true of
 * [y], there is nothing left over that could distinguish them, so there is
 * nothing left to mean by "different".
 *)
(* [forall {A : Type}, A -> A -> Prop] *)
Definition Leibniz := fun {A : Type} (x : A) (y : A) =>
  forall (P : A -> Prop), P x -> P y.

(* Equijunction is equality: it joins two terms of one type that are the
 * same. [x] is a parameter and the second argument an index, so the one
 * ctor can only ever produce [Equijunction A x x]. A proof that [x]
 * equals something will exist only when that something is [x].
 *)
Inductive Equijunction (A : Type) (x : A) : A -> Prop :=
  | Equijunction_introduction : Equijunction A x x.

Arguments Equijunction              {A} x _.
Arguments Equijunction_introduction {A} x.

(* Carries a proof across the equation. The tactics fill the slots of
 * [core.eq.ind] by position, so this order -- [P] before the proof and
 * [y] after it -- is the order the registration needs.
 *)
Theorem Equijunction_induction
  : forall {A : Type} (x : A) (P : A -> Prop),
      P x -> forall (y : A), Equijunction x y -> P y.
Proof.
  (* The context gains [A], [x], [P] and [p]:
   * [|- forall (y : A), Equijunction x y -> P y]
   *)
  intros A x P p.
  (* The context gains [y] and [e]: [|- P y] *)
  intros y e.
  (* [x] is a parameter, so fixed for every ctor; [y] is an index, so each
   * ctor chooses it. [Equijunction_introduction] is the only ctor and it
   * chooses the parameter, which is why [y] becomes [x] and not the other
   * way: [|- P x]
   *)
  destruct e.
  (* [p] is a proof of the goal as it stands. *)
  exact p.
Defined.

(* Every term equals itself: the reflexivity law of [=]. *)
Theorem Equijunction_reflexivity
  : forall {A : Type} (x : A), Equijunction x x.
Proof.
  intros A x.
  exact (Equijunction_introduction x).
Qed.

Theorem Equijunction_symmetry
  : forall {A : Type} {x : A} {y : A}, Equijunction x y -> Equijunction y x.
Proof.
  intros A x y e.
  destruct e.
  reflexivity.
Qed.

Theorem Equijunction_transitivity
  : forall {A : Type} {x : A} {y : A} {z : A},
      Equijunction x y -> Equijunction y z -> Equijunction x z.
Proof.
  intros A x y z e1 e2.
  destruct e2.
  exact e1.
Qed.

Theorem Equijunction_congruence
  : forall {A : Type} {B : Type} (f : A -> B) {x : A} {y : A},
      Equijunction x y -> Equijunction (f x) (f y).
Proof.
  intros A B f x y e.
  destruct e.
  reflexivity.
Qed.

(* [rewrite] builds its proof term out of these two, which carry a proof
 * along the equation into [Type], forwards and backwards. [Defined] keeps
 * them transparent.
 *)

Definition Equijunction_rewrite_forward
  : forall (A : Type) (x : A) (P : A -> Type),
      P x -> forall (y : A), Equijunction x y -> P y.
Proof.
  intros A x P p.
  intros y e.
  destruct e.
  exact p.
Defined.

Definition Equijunction_rewrite_backward
  : forall (A : Type) (x : A) (y : A) (P : A -> Type),
      P y -> Equijunction x y -> P x.
Proof.
  intros A x y P p.
  intro e.
  destruct e.
  exact p.
Defined.


(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "x = y" := (Equijunction x y)
  : jwa_type_scope.

(* [Register Scheme] is what points [rewrite] at them. The kinds [rew] and
 * [rew_r] are Rocq's own, fixed like a registration key.
 *)
Register Scheme Equijunction_rewrite_forward  as rew   for Equijunction.
Register Scheme Equijunction_rewrite_backward as rew_r for Equijunction.

(* [build_eqdata_gen] in rocqlib.ml demands exactly these six; a single
 * missing one surfaces as [No primitive equality found].
 *)
Register Equijunction              as core.eq.type.
Register Equijunction_introduction as core.eq.refl.
Register Equijunction_induction    as core.eq.ind.
Register Equijunction_symmetry     as core.eq.sym.
Register Equijunction_transitivity as core.eq.trans.
Register Equijunction_congruence   as core.eq.congr.
