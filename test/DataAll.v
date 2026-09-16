(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Data.All], imported alone. It forwards [Core.All] as well as
   [Data.Option], so names from both appear below. *)
From jwa Require Import Data.All.

Definition data_all_delivers_some
  : forall (A : Type) (B : Type) (f : A -> B) (a : A),
      ~ (true = false) -> Option.map f (Some a) = Some (f a)
  := fun (A : Type) (B : Type) (f : A -> B) (a : A) (_ : ~ (true = false)) =>
       Eq_reflexivity (Some (f a)).

Definition data_all_delivers_none
  : forall (A : Type),
      Option.map (fun (a : A) => a) None = None
  := fun (A : Type) =>
      Eq_reflexivity None.

Definition data_all_delivers_nat : Nat := Successor One.

Definition data_all_delivers_zero : NatWithZero := Zero.

Definition data_all_delivers_positive : NatWithZero := Positive One.

Definition data_all_delivers_add : NatWithZero
  := NatWithZero.add (Positive (Nat.add One One)) Zero.

(* The instances are found by resolution rather than named, so this also
   checks that [Structures.All] reaches a client through this umbrella. *)
Definition data_all_delivers_instances
  : forall (x : Nat) (y : Nat) (z : Nat) (w : NatWithZero),
      Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z)
  := fun (x : Nat) (y : Nat) (z : Nat) (_ : NatWithZero) =>
       Semigroup_associativity x y z.

Definition data_all_delivers_monoid
  : forall (w : NatWithZero), NatWithZero.add Zero w = w
  := Monoid_identity_left.

Definition data_all_delivers_functor : Option Bool
  := Functor_map (fun (b : Bool) => b) (Some true).
