(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Relations.All], imported alone. It forwards [Core.All] as well as
   the four modules, so names from both appear below. *)
From jwa Require Import Relations.All.

Definition relations_all_delivers
  : forall (A : Type) (R : A -> A -> Prop),
      Reflexive.Relation A R -> Symmetric.Relation A R
      -> Transitive.Relation A R -> Equivalence.Relation A R
      -> ~ False -> True
  := fun (A : Type) (R : A -> A -> Prop)
         (_ : Reflexive.Relation A R) (_ : Symmetric.Relation A R)
         (_ : Transitive.Relation A R) (_ : Equivalence.Relation A R)
         (_ : ~ False) => I.

(* The projections are constants of their modules, so the umbrella has to
   forward them too; the one below is reached through the [::] field of
   [Equivalence.Relation], which also checks that its hint left the
   module. *)
Definition relations_all_delivers_projections
  : forall (A : Type) (R : A -> A -> Prop) (e : Equivalence.Relation A R)
           (x : A),
      R x x
  := fun (A : Type) (R : A -> A -> Prop) (e : Equivalence.Relation A R)
         (x : A) =>
       Reflexive.reflexivity x.

(* The instances are found by resolution rather than named. *)
Definition relations_all_delivers_eq_instance
  : forall (A : Type) (x : A) (y : A), x = y -> y = x
  := fun (A : Type) (x : A) (y : A) => Symmetric.symmetry x y.

Definition relations_all_delivers_biconditional_instance
  : forall (P : Prop) (Q : Prop) (S : Prop),
      (P <-> Q) -> (Q <-> S) -> (P <-> S)
  := fun (P : Prop) (Q : Prop) (S : Prop) => Transitive.transitivity P Q S.
