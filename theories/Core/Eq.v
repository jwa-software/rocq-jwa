(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level of [=], [Core.Logic.Conditional] carries [->], [Core.Ltac] is
   what makes [Proof] parse at all. *)
From jwa Require Import Core.Notations.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Logic.Conditional.

(* Gottfried Leibniz, seventeenth century: two things are the same exactly when
   no property tells them apart. If everything true of x is true of y, there is
   nothing left over that could distinguish them, so there is nothing left to
   mean by "different". *)
(* [forall {A : Type}, A -> A -> Prop] *)
Definition Leibniz := fun {A : Type} (x : A) (y : A) =>
  forall P : A -> Prop, P x -> P y.

(* [x] is a parameter and the second argument an index, so the one constructor
   can only ever produce [Eq A x x]. A proof that [x] equals something exists
   only when that something is [x], and that is the whole content of equality
   here. *)
Inductive Eq (A : Type) (x : A) : A -> Prop :=
  | Eq_reflexivity : Eq A x x.

Arguments Eq             {A} x _.
Arguments Eq_reflexivity {A} x.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "x = y" := (Eq x y) : jwa_type_scope.

(* Carries a proof across the equation. The tactics fill the slots of
   [core.eq.ind] by position, so this order -- [P] before the proof and [y]
   after it -- is the order the registration needs. *)
Theorem Eq_transport
  : forall {A : Type} (x : A) (P : A -> Prop), P x -> forall (y : A), Eq x y -> P y.
Proof.
  (* The context gains [A], [x], [P] and [p]:
     [|- forall (y : A), Eq x y -> P y] *)
  intros A x P p.
  (* The context gains [y] and [e]: [|- P y] *)
  intros y e.
  (* [x] is a parameter, so fixed for every ctor; [y] is an index, so each
     ctor chooses it. [Eq_reflexivity] is the only ctor and it chooses the
     parameter, which is why [y] becomes [x] and not the other way:
     [|- P x] *)
  destruct e.
  (* [p] is a proof of the goal as it stands. *)
  exact p.
Defined.

Theorem Eq_symmetry : forall {A : Type} {x : A} {y : A}, Eq x y -> Eq y x.
Proof.
  (* The context gains [A], [x], [y] and [e]: [|- Eq y x] *)
  intros A x y e.
  (* The index [y] takes the parameter's value: [|- Eq x x] *)
  destruct e.
  (* Both sides are the same term. *)
  reflexivity.
Defined.

Theorem Eq_transitivity
  : forall {A : Type} {x : A} {y : A} {z : A}, Eq x y -> Eq y z -> Eq x z.
Proof.
  (* The context gains [A], [x], [y], [z], [e1] and [e2]: [|- Eq x z] *)
  intros A x y z e1 e2.
  (* In [e2 : Eq y z] the parameter is [y] and the index [z], so the index
     takes [y]: [|- Eq x y] *)
  destruct e2.
  (* [e1] is a proof of the goal as it stands. *)
  exact e1.
Defined.

Theorem Eq_congruence
  : forall {A : Type} {B : Type} (f : A -> B) {x : A} {y : A},
      Eq x y -> Eq (f x) (f y).
Proof.
  (* The context gains [A], [B], [f], [x], [y] and [e]: [|- Eq (f x) (f y)] *)
  intros A B f x y e.
  (* The index [y] takes the parameter's value: [|- Eq (f x) (f x)] *)
  destruct e.
  (* Both sides are the same term. *)
  reflexivity.
Defined.

(* [rewrite] builds its proof term out of these two, which carry a proof along
   the equation into [Type], forwards and backwards. [Defined] keeps them
   transparent: [rewrite] leaves them in the term, where they have to reduce. *)
Theorem Eq_rewrite_forward
  : forall (A : Type) (x : A) (P : A -> Type), P x -> forall (y : A), Eq x y -> P y.
Proof.
  (* The context gains [A], [x], [P] and [p]:
     [|- forall (y : A), Eq x y -> P y] *)
  intros A x P p.
  (* The context gains [y] and [e]: [|- P y] *)
  intros y e.
  (* The index [y] takes the parameter's value: [|- P x] *)
  destruct e.
  (* [p] is a proof of the goal as it stands. *)
  exact p.
Defined.

Theorem Eq_rewrite_backward
  : forall (A : Type) (x : A) (y : A) (P : A -> Type), P y -> Eq x y -> P x.
Proof.
  (* The context gains [A], [x], [y], [P] and [p]: [|- Eq x y -> P x] *)
  intros A x y P p.
  (* The context gains [e]: [|- P x] *)
  intro e.
  (* The index [y] takes the parameter's value, and [p] changes type with it:
     [|- P x] with [p : P x] *)
  destruct e.
  (* [p] is a proof of the goal as it stands. *)
  exact p.
Defined.

(* [Register Scheme] is what points [rewrite] at them. The kinds [rew] and
   [rew_r] are Rocq's own, fixed like a registration key. *)
Register Scheme Eq_rewrite_forward  as rew   for Eq.
Register Scheme Eq_rewrite_backward as rew_r for Eq.

(* [build_eqdata_gen] in rocqlib.ml demands exactly these six; a single missing
   one surfaces as [No primitive equality found]. *)
Register Eq              as core.eq.type.
Register Eq_reflexivity  as core.eq.refl.
Register Eq_transport    as core.eq.ind.
Register Eq_symmetry     as core.eq.sym.
Register Eq_transitivity as core.eq.trans.
Register Eq_congruence   as core.eq.congr.
