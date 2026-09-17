(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Relations.All], imported alone. It forwards [Core.All] as well as
   the ten modules, so names from both appear below. *)
From jwa Require Import Relations.All.

Definition relations_all_delivers
  : forall (A : Type) (R : A -> A -> Prop),
      Reflexive.R A R -> Irreflexive.R A R -> Symmetric.R A R
      -> Antisymmetric.R A R -> Transitive.R A R -> Total.R A R
      -> Equivalence.R A R -> StrictOrder.R A R -> PartialOrder.R A R
      -> TotalOrder.R A R -> ~ Falsum -> Verum
  := fun (A : Type) (R : A -> A -> Prop)
         (_ : Reflexive.R A R) (_ : Irreflexive.R A R) (_ : Symmetric.R A R)
         (_ : Antisymmetric.R A R) (_ : Transitive.R A R) (_ : Total.R A R)
         (_ : Equivalence.R A R) (_ : StrictOrder.R A R) (_ : PartialOrder.R A R)
         (_ : TotalOrder.R A R) (_ : ~ Falsum) => I.

(* The [::] chain of [TotalOrder.R] reaches [Reflexive.reflexivity] two hints
   deep, which also checks that both hints left their modules. *)
Definition relations_all_delivers_order_projections
  : forall (A : Type) (R : A -> A -> Prop) (t : TotalOrder.R A R) (x : A),
      R x x
  := fun (A : Type) (R : A -> A -> Prop) (t : TotalOrder.R A R) (x : A) =>
       Reflexive.reflexivity x.

(* The projections are constants of their modules, so the umbrella has to
   forward them too; the one below is reached through the [::] field of
   [Equivalence.R], which also checks that its hint left the
   module. *)
Definition relations_all_delivers_projections
  : forall (A : Type) (R : A -> A -> Prop) (e : Equivalence.R A R)
           (x : A),
      R x x
  := fun (A : Type) (R : A -> A -> Prop) (e : Equivalence.R A R)
         (x : A) =>
       Reflexive.reflexivity x.

(* The instances are found by resolution rather than named. *)
Definition relations_all_delivers_equijunction_instance
  : forall (A : Type) (x : A) (y : A), x = y -> y = x
  := fun (A : Type) (x : A) (y : A) => Symmetric.symmetry x y.

Definition relations_all_delivers_bijunction_instance
  : forall (P : Prop) (Q : Prop) (S : Prop),
      (P <-> Q) -> (Q <-> S) -> (P <-> S)
  := fun (P : Prop) (Q : Prop) (S : Prop) => Transitive.transitivity P Q S.
