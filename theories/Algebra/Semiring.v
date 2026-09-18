(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianMonoid.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Semiring {A : Type}
               (add : A -> A -> A) (zero : A)
               (mul : A -> A -> A) (one  : A)
               : Prop :=
  { abelian_monoid
    :: AbelianMonoid add zero
  ; monoid
    :: Monoid mul one
  ; distributivity
    : forall (x : A) (y : A) (z : A),
      mul x (add y z) = add (mul x y) (mul x z)
    /\ mul (add y z) x = add (mul y x) (mul z x)
  ; annihilation
    : forall (x : A),
      mul zero x = zero /\ mul x zero = zero }.
