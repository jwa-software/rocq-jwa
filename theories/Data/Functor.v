(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Functor (F : Type -> Type) : Type :=
  { map
    : forall {A : Type} {B : Type} .
      (A -> B) -> F A -> F B
  ; map_identity
    : forall (A : Type) (x : F A) .
      map (fun (a : A) . a) x = x
  ; map_composition
    : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : F A) .
      map g (map f x) = map (fun (a : A) . g (f a)) x }.
