(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Structures.All], imported alone. It forwards [Core.All] as well as
   the three modules, so names from both appear below. *)
From jwa Require Import Structures.All.

Definition structures_all_delivers
  : forall (A : Type) (op : A -> A -> A) (e : A),
      forall (F : Type -> Type),
      Semigroup.T A op -> Monoid.T A op e
      -> Functor.T F -> ~ Falsum -> Verum
  := fun (A : Type) (op : A -> A -> A) (e : A) (F : Type -> Type)
         (_ : Semigroup.T A op) (_ : Monoid.T A op e)
         (_ : Functor.T F) (_ : ~ Falsum) => I.

(* The projections are constants of their modules, so the umbrella has to
   forward them too. *)
Definition structures_all_delivers_projections
  : forall (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e)
           (x : A),
      op e x = x
  := fun (A : Type) (op : A -> A -> A) (e : A) (m : Monoid.T A op e)
         (x : A) =>
       Monoid.identity_left x.
