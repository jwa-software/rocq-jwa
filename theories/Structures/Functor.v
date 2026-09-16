(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* [: Type] and not [: Prop]: [Functor_map] is a function rather than a proof,
   and a [Prop] record cannot project out a field that lives in [Type].
   [Semigroup] and [Monoid] hold only laws, which is why they can be [Prop].

   [F] ranges over [Type -> Type] rather than [Type], so what is abstracted
   is [F] itself and not the type it is applied to. Any [Type -> Type] can
   qualify; being a container is not required. *)
Class Functor (F : Type -> Type) : Type :=
  { Functor_map
      : forall {A : Type} {B : Type}, (A -> B) -> F A -> F B
  ; Functor_map_identity
      : forall (A : Type) (x : F A), Functor_map (fun (a : A) => a) x = x
  ; Functor_map_composition
      : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : F A),
          Functor_map g (Functor_map f x) = Functor_map (fun (a : A) => g (f a)) x }.
