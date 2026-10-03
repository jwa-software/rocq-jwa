(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Core.All.
From jwa Require Import Core.Class.

Module Ring. (* Ring *)

Class T {A : Type}
        (add : A -> A -> A) (zero : A) (negate : A -> A)
        (mul : A -> A -> A) (one : A)
        : Prop :=
  { abelian_group
    :: AbelianGroup add zero negate
  ; monoid
    :: Monoid mul one
  ; distributivity
    : forall (x : A) (y : A) (z : A) .
      mul x (add y z) = add (mul x y) (mul x z)
    /\ mul (add y z) x = add (mul y x) (mul z x) }.

Abbreviation Ring := T.

End Ring. (* Ring *)

Abbreviation Ring := Ring.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance Ring.abelian_group.
#[export] Existing Instance Ring.monoid.
