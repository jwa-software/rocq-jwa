(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Structures.All] would be circular from inside [Structures]; [Core.All]
   carries [->] and [=], [Structures.Class] the hint database that instance
   resolution looks up. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.

(* The module is the prefix: the class reads [Functor.T], its
   operation [Functor.map] and its laws [Functor.map_identity] and
   [Functor.map_composition]. *)
Module Functor.
  (* [: Type] and not [: Prop]: [map] is a function rather than a proof, and
     a [Prop] record cannot project out a field that lives in [Type].
     [Semigroup.T] and [Monoid.T] hold only laws, which is
     why they can be [Prop].

     [F] ranges over [Type -> Type] rather than [Type], so what is
     abstracted is [F] itself and not the type it is applied to. Any
     [Type -> Type] can qualify; being a container is not required. *)
  Class T (F : Type -> Type) : Type :=
    { map
        : forall {A : Type} {B : Type}, (A -> B) -> F A -> F B
    ; map_identity
        : forall (A : Type) (x : F A), map (fun (a : A) => a) x = x
    ; map_composition
        : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : F A),
            map g (map f x) = map (fun (a : A) => g (f a)) x }.
End Functor.
