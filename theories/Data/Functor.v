(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Functor. (* Functor *)

Class T (F : Type -> Type) : Type :=
  { map
    : forall {A : Type} {B : Type} .
      (A -> B) -> F A -> F B
  ; identity
    : forall (A : Type) (x : F A) .
      map (fun (a : A) . a) x = x
  ; composition
    : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : F A) .
      map g (map f x) = map (fun (a : A) . g (f a)) x }.

Abbreviation Functor := T.

End Functor. (* Functor *)

Abbreviation Functor := Functor.T.
