(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Relation.All.

Definition relation_all_delivers
  : forall (A : Type) (R : A -> A -> Prop) .
      Reflexive R -> Irreflexive R -> Symmetric R
      -> Antisymmetric R -> Transitive R -> Total R -> Trichotomous R
      -> Equivalence R -> StrictPartialOrder R -> StrictTotalOrder R
      -> PartialOrder R -> TotalOrder R -> ~ Falsum -> Verum
  := fun (A : Type) (R : A -> A -> Prop)
         (_ : Reflexive R) (_ : Irreflexive R) (_ : Symmetric R)
         (_ : Antisymmetric R) (_ : Transitive R) (_ : Total R) (_ : Trichotomous R)
         (_ : Equivalence R) (_ : StrictPartialOrder R) (_ : StrictTotalOrder R)
         (_ : PartialOrder R) (_ : TotalOrder R) (_ : ~ Falsum) . I.

Definition relation_all_delivers_well_founded
  : forall (A : Type) (R : A -> A -> Prop) . WellFounded R -> Verum
  := fun (A : Type) (R : A -> A -> Prop) (_ : WellFounded R) . I.

Definition relation_all_delivers_accessibility
  : forall (A : Type) (R : A -> A -> Prop) (w : WellFounded R) (x : A) .
      Accessible R x
  := fun (A : Type) (R : A -> A -> Prop) (w : WellFounded R) (x : A) .
       accessibility x.

Definition relation_all_delivers_accessible_descend
  : forall (A : Type) (R : A -> A -> Prop) (x : A) (y : A) .
      Accessible R x -> R y x -> Accessible R y
  := fun (A : Type) (R : A -> A -> Prop) (x : A) (y : A) . Accessible.descend.

Definition relation_all_delivers_well_founded_recursion
  : forall (A : Type) (R : A -> A -> Prop) (w : WellFounded R) (x : A) . Verum
  := fun (A : Type) (R : A -> A -> Prop) (w : WellFounded R) .
       WellFounded.recursion (fun (x : A) (_ : forall (y : A) . R y x -> Verum) . I).

Definition relation_all_delivers_induced
  : forall (A : Type) (B : Type) (f : A -> B) (R : B -> B -> Prop) .
      WellFounded R -> WellFounded (Induced R f)
  := fun (A : Type) (B : Type) (f : A -> B) (R : B -> B -> Prop) .
       WellFounded.induced R f.

Definition relation_all_delivers_induced_rules
  : forall (A : Type) (B : Type) (f : A -> B) (R : B -> B -> Prop) (y : A) (x : A) .
      (R (f y) (f x) -> Induced R f y x) /\ (Induced R f y x -> R (f y) (f x))
  := fun (A : Type) (B : Type) (f : A -> B) (R : B -> B -> Prop) (y : A) (x : A) .
       Conjunction_introduction Induced.introduction Induced.elimination.

Definition relation_all_delivers_extensional
  : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type) (step : Descent.Step R P) .
      Descent.Extensional step -> Verum
  := fun (A : Type) (R : A -> A -> Prop) (P : A -> Type) (step : Descent.Step R P)
       (_ : Descent.Extensional step) . I.

Definition relation_all_delivers_accessible_recursion_independence
  : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type) (step : Descent.Step R P) .
      Descent.Extensional step ->
      (forall (x : A) (a : Accessible R x) (b : Accessible R x) .
         Accessible.recursion step x a = Accessible.recursion step x b)
  := fun (A : Type) (R : A -> A -> Prop) (P : A -> Type) (step : Descent.Step R P) .
       Accessible.recursion.independence.

Definition relation_all_delivers_well_founded_recursion_unfolding
  : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type) (W : WellFounded R)
      (step : Descent.Step R P) .
      Descent.Extensional step ->
      (forall (x : A) .
         WellFounded.recursion step x
         = step x (fun (y : A) (r : R y x) . WellFounded.recursion step y))
  := fun (A : Type) (R : A -> A -> Prop) (P : A -> Type) (W : WellFounded R)
       (step : Descent.Step R P) .
       WellFounded.recursion.unfolding.

Definition relation_all_delivers_order_projections
  : forall (A : Type) (R : A -> A -> Prop) (t : TotalOrder R) (x : A) .
      R x x
  := fun (A : Type) (R : A -> A -> Prop) (t : TotalOrder R) (x : A) .
       Reflexive.reflexivity x.

Definition relation_all_delivers_projections
  : forall (A : Type) (R : A -> A -> Prop) (e : Equivalence R) (x : A) .
      R x x
  := fun (A : Type) (R : A -> A -> Prop) (e : Equivalence R) (x : A) .
       Reflexive.reflexivity x.

Definition relation_all_delivers_identity_instance
  : forall (A : Type) (x : A) (y : A) . x = y -> y = x
  := fun (A : Type) (x : A) (y : A) . Symmetric.symmetry x y.

Definition relation_all_delivers_biconditional_instance
  : forall (P : Prop) (Q : Prop) (S : Prop) .
      (P <-> Q) -> (Q <-> S) -> (P <-> S)
  := fun (P : Prop) (Q : Prop) (S : Prop) . Transitive.transitivity P Q S.
