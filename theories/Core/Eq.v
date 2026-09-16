(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] would be circular from inside [Core]; [Core.Notations] reserves
   the level of [=], [Core.Logic.Conditional] carries [->]. *)
From jwa Require Import Core.Notations.
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

(* The tactics fill the slots of [core.eq.ind] by position, in the order
   [Corelib] uses, so the registration needs that order and not the one above.
   Rewriting the arguments here is what keeps [discriminate] and [rewrite]
   working. *)
Definition Eq_transport_registered
  : forall {A : Type} (x : A) (P : A -> Prop), P x -> forall (y : A), Eq x y -> P y :=
  fun {A : Type} (x : A) (P : A -> Prop) (p : P x) (y : A) (e : Eq x y) =>
    Eq_transport x y P p e.

(* [forall {A : Type} {x : A} {y : A}, Eq x y -> Eq y x] *)
Definition Eq_symmetry
  : forall {A : Type} {x : A} {y : A}, Eq x y -> Eq y x :=
  fun {A : Type} {x : A} {y : A} (e : Eq x y) =>
    Eq_transport x y (fun a => Eq a x) (Eq_reflexivity x) e.

(* [forall {A : Type} {x : A} {y : A} {z : A},
      Eq x y -> Eq y z -> Eq x z] *)
Definition Eq_transitivity
  : forall {A : Type} {x : A} {y : A} {z : A}, Eq x y -> Eq y z -> Eq x z :=
  fun {A : Type} {x : A} {y : A} {z : A} (e1 : Eq x y) (e2 : Eq y z) =>
    Eq_transport y z (fun a => Eq x a) e1 e2.

(* [forall {A : Type} {B : Type} (f : A -> B) {x : A} {y : A},
      Eq x y -> Eq (f x) (f y)] *)
Definition Eq_congruence
  : forall {A : Type} {B : Type} (f : A -> B) {x : A} {y : A}, Eq x y -> Eq (f x) (f y) :=
  fun {A : Type} {B : Type} (f : A -> B) {x : A} {y : A} (e : Eq x y) =>
    Eq_transport x y (fun a => Eq (f x) (f a)) (Eq_reflexivity (f x)) e.

(* [build_eqdata_gen] in rocqlib.ml demands exactly these six; a single missing
   one surfaces as [No primitive equality found]. *)
Register Eq                      as core.eq.type.
Register Eq_reflexivity          as core.eq.refl.
Register Eq_transport_registered as core.eq.ind.
Register Eq_symmetry             as core.eq.sym.
Register Eq_transitivity         as core.eq.trans.
Register Eq_congruence           as core.eq.congr.
