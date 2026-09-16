(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Relations.All], imported alone. It forwards [Core.All] as well as
   the four modules, so names from both appear below. *)
From jwa Require Import Relations.All.

Definition relations_all_delivers
  : forall (A : Type) (R : A -> A -> Prop),
      Reflexive.R A R -> Symmetric.R A R
      -> Transitive.R A R -> Equivalence.R A R
      -> ~ False -> True
  := fun (A : Type) (R : A -> A -> Prop)
         (_ : Reflexive.R A R) (_ : Symmetric.R A R)
         (_ : Transitive.R A R) (_ : Equivalence.R A R)
         (_ : ~ False) => I.

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
Definition relations_all_delivers_eq_instance
  : forall (A : Type) (x : A) (y : A), x = y -> y = x
  := fun (A : Type) (x : A) (y : A) => Symmetric.symmetry x y.

Definition relations_all_delivers_biconditional_instance
  : forall (P : Prop) (Q : Prop) (S : Prop),
      (P <-> Q) -> (Q <-> S) -> (P <-> S)
  := fun (P : Prop) (Q : Prop) (S : Prop) => Transitive.transitivity P Q S.
