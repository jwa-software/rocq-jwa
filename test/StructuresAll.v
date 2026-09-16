(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Structures.All], imported alone. It forwards [Core.All] as well as
   the two classes, so names from both appear below. *)
From jwa Require Import Structures.All.

Definition structures_all_delivers
  : forall (A : Type) (op : A -> A -> A) (e : A),
      forall (F : Type -> Type),
      Semigroup A op -> Monoid A op e -> Functor F -> ~ (true = false) -> True
  := fun (A : Type) (op : A -> A -> A) (e : A) (F : Type -> Type)
         (_ : Semigroup A op) (_ : Monoid A op e) (_ : Functor F)
         (_ : ~ (true = false)) => I.

(* The projections are top-level constants, so the umbrella has to forward
   them too. *)
Definition structures_all_delivers_projections
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid A op e) (x : A),
      op e x = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid A op e) (x : A) =>
       Monoid_identity_left x.
