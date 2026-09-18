(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Class Ring {A : Type}
           (add : A -> A -> A) (zero : A) (negate : A -> A)
           (mul : A -> A -> A) (one : A)
           : Prop :=
  { abelian_group
    :: AbelianGroup add zero negate
  ; monoid
    :: Monoid mul one
  ; distributivity
    : forall (x : A) (y : A) (z : A),
      mul x (add y z) = add (mul x y) (mul x z)
    /\ mul (add y z) x = add (mul y x) (mul z x) }.
