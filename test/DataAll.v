(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.All.

Definition data_all_delivers_some
  : forall (A : Type) (B : Type) (f : A -> B) (a : A),
      ~ (true = false) -> Option.map f (Some a) = Some (f a)
  := fun (A : Type) (B : Type) (f : A -> B) (a : A) (_ : ~ (true = false)) =>
       Identity.reflexivity (Some (f a)).

Definition data_all_delivers_none
  : forall (A : Type),
      Option.map (fun (a : A) => a) None = None
  := fun (A : Type) =>
       Identity.reflexivity None.

Definition data_all_delivers_pair
  : Bool * Bool
  := (true , false)%pair.

Definition data_all_delivers_first
  : forall (A : Type) (a : A) (b : A), Pair.first (Pair_introduction a b) = a
  := fun (A : Type) (a : A) (b : A) => Identity.reflexivity a.

Definition data_all_delivers_projections
  : Bool * Bool
  := (pi_2 (true , false) , pi_1 (true , false))%pair.

Definition data_all_delivers_pair_functor
  : Bool * Bool
  := Functor.map (fun (b : Bool) => b) (Pair_introduction true false).

Definition data_all_delivers_pair_monoid
  : forall (p : Bool * Bool),
      Pair.product Bool.and Bool.or (Pair_introduction true false) p
      = p
  := Monoid.left_identity.

Definition data_all_delivers_sum
  : Bool + Bool
  := Sum_left true.

Definition data_all_delivers_copair
  : forall (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B),
      Sum.copair f g (Sum_right b) = g b
  := fun (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) =>
       Identity.reflexivity (g b).

Definition data_all_delivers_sum_functor
  : Bool + Bool
  := Functor.map (fun (b : Bool) => b) (Sum_right true).

Definition data_all_delivers_unit
  : forall (u : Unit), u = Unit_introduction
  := Unit.surjectivity.

Definition data_all_delivers_empty
  : Empty -> Bool
  := Empty.elimination Bool.

Definition data_all_delivers_nat
  : Nat
  := Successor One.

Definition data_all_delivers_zero
  : NatWithZero
  := NatWithZero.Zero.

Definition data_all_delivers_positive
  : NatWithZero
  := NatWithZero.Positive One.

Definition data_all_delivers_add
  : NatWithZero
  := NatWithZero.add (NatWithZero.Positive (Nat.add One One)) NatWithZero.Zero.

Definition data_all_delivers_instances
  : forall (x : Nat) (y : Nat) (z : Nat) (w : NatWithZero),
      Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z)
  := fun (x : Nat) (y : Nat) (z : Nat) (_ : NatWithZero) =>
       Semigroup.associativity x y z.

Definition data_all_delivers_monoid
  : forall (w : NatWithZero), NatWithZero.add NatWithZero.Zero w = w
  := Monoid.left_identity.

Definition data_all_delivers_cancellative
  : forall (n : Nat) (m : Nat) (k : Nat), Nat.add n m = Nat.add n k -> m = k
  := Cancellative.left_cancellation.

Definition data_all_delivers_cancellative_with_zero
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      NatWithZero.add m n = NatWithZero.add k n -> m = k
  := Cancellative.right_cancellation.

Definition data_all_delivers_nat_operations
  : Nat
  := (One + One * Successor One)%nat.

Definition data_all_delivers_nat_with_zero_operations
  : NatWithZero
  := (NatWithZero.Zero + NatWithZero.Positive One * NatWithZero.Positive One)%nat_with_zero.

Definition data_all_delivers_power
  : Nat
  := Nat.power (Successor One) One.

Definition data_all_delivers_subtract
  : Option Nat
  := Nat.subtract (Successor One) One.

Definition data_all_delivers_mul_monoid
  : forall (n : Nat), Nat.mul One n = n
  := Monoid.left_identity.

Definition data_all_delivers_commutative
  : forall (p1 : Nat * Bool) (p2 : Nat * Bool),
      Pair.product Nat.mul Bool.xor p1 p2
      = Pair.product Nat.mul Bool.xor p2 p1
  := Commutative.commutativity.

Definition data_all_delivers_functor
  : Option Bool
  := Functor.map (fun (b : Bool) => b) (Some true).

Definition data_all_delivers_bool_operations
  : Bool
  := (true || false) && (Bool.negate false ^^ true).

Definition data_all_delivers_bool_monoids
  : forall (b : Bool), Bool.and true b = b
  := Monoid.left_identity.

Definition data_all_delivers_bool_bridge
  : forall (b1 : Bool) (b2 : Bool),
      Bool.Assert (Bool.and b1 b2) <-> Bool.Assert b1 /\ Bool.Assert b2
  := Bool.assert_conjunction.

Definition data_all_delivers_list
  : List Bool
  := (Cons true Nil ++ Cons false Nil)%list.

Definition data_all_delivers_list_monoid
  : forall (A : Type) (l : List A), (Nil ++ l)%list = l
  := fun (A : Type) => Monoid.left_identity.

Definition data_all_delivers_empty_list
  : List Bool
  := []%list.

Definition data_all_delivers_cons
  : List Bool
  := (true :: false :: [])%list.

Definition data_all_delivers_list_functor
  : List Bool
  := Functor.map (fun (b : Bool) => b) (Cons true Nil).

Definition data_all_delivers_contains
  : Prop
  := (Cons true Nil contains_member true)%list.

Definition data_all_delivers_belongs_to
  : Prop
  := (true belongs_to Cons true Nil)%list.

Definition data_all_delivers_does_not_contain_member
  : Prop
  := (Nil does_not_contain_member true)%list.

Definition data_all_delivers_does_not_belong_to
  : Prop
  := (true does_not_belong_to Nil)%list.

Definition data_all_delivers_nat_order
  : Prop
  := (One < Successor One)%nat.

Definition data_all_delivers_nat_with_zero_order
  : Prop
  := (NatWithZero.Zero <= NatWithZero.Positive One)%nat_with_zero.

Definition data_all_delivers_reversed_order
  : Prop
  := (Successor One > One)%nat /\ (NatWithZero.Positive One >= NatWithZero.Zero)%nat_with_zero.

Definition data_all_delivers_compare
  : Comparison
  := Nat.compare One (Successor One).

Definition data_all_delivers_equal
  : Bool
  := NatWithZero.equal NatWithZero.Zero NatWithZero.Zero.

Definition data_all_delivers_total_order
  : forall (m : Nat) (n : Nat), Nat.LessOrEqual m n \/ Nat.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_strict_order
  : forall (n : NatWithZero), ~ NatWithZero.LessThan n n
  := Irreflexive.irreflexivity.

Definition data_all_delivers_max_monoid
  : forall (n : NatWithZero), NatWithZero.max NatWithZero.Zero n = n
  := Monoid.left_identity.

Definition data_all_delivers_nat_max_monoid
  : forall (n : Nat), Nat.max One n = n
  := Monoid.left_identity.

Definition data_all_delivers_division
  : NatWithZero * NatWithZero
  := Pair_introduction (NatWithZero.divide (NatWithZero.Positive One) One)
                       (NatWithZero.modulo (NatWithZero.Positive One) One).

Definition data_all_delivers_nth
  : Option Bool
  := List.nth (Cons true Nil) NatWithZero.Zero.

Definition data_all_delivers_split_at
  : List Bool * List Bool
  := List.split_at (NatWithZero.Positive One) (Cons true (Cons false Nil)).

Definition data_all_delivers_replicate
  : List Bool
  := List.replicate (NatWithZero.Positive One) true.

Definition data_all_delivers_list_sum
  : NatWithZero
  := NatWithZero.add (List.sum (Cons (NatWithZero.Positive One) Nil)) (List.product Nil).

Definition data_all_delivers_count
  : NatWithZero
  := List.count (fun (b : Bool) => b) (Cons true Nil).

Definition data_all_delivers_sorting
  : forall (l : List NatWithZero),
      List.Sorted NatWithZero.at_most (List.insertion_sort NatWithZero.at_most l)
  := List.insertion_sort_sortedness NatWithZero NatWithZero.at_most
       NatWithZero.at_most_totality NatWithZero.at_most_transitivity.

Definition data_all_delivers_integer
  : Integer
  := Integer.add (Negative One) (Integer.Positive One).

Definition data_all_delivers_integer_operations
  : Integer
  := (Integer.Zero + Negative One * Integer.Positive One)%integer.

Definition data_all_delivers_integer_order
  : Prop
  := (Negative One < Integer.Zero)%integer /\ (Integer.Positive One >= Integer.Zero)%integer.

Definition data_all_delivers_integer_monoid
  : forall (x : Integer), Integer.add Integer.Zero x = x
  := Monoid.left_identity.

Definition data_all_delivers_integer_mul_monoid
  : forall (x : Integer), Integer.mul (Integer.Positive One) x = x
  := Monoid.left_identity.

Definition data_all_delivers_integer_cancellative
  : forall (k : Integer) (m : Integer) (n : Integer),
      Integer.add k m = Integer.add k n -> m = n
  := Cancellative.left_cancellation.

Definition data_all_delivers_integer_total_order
  : forall (m : Integer) (n : Integer), Integer.LessOrEqual m n \/ Integer.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_integer_embedding
  : Integer
  := Integer.from_nat_with_zero (NatWithZero.Positive One).

Definition data_all_delivers_integer_equal
  : Bool
  := Integer.equal (Negative One) (Integer.negate (Integer.Positive One)).

Definition data_all_delivers_range
  : List NatWithZero
  := List.range (NatWithZero.Positive One).

Definition data_all_delivers_extrema
  : NatWithZero * Option NatWithZero
  := Pair_introduction (List.maximum_of (Cons NatWithZero.Zero Nil))
                       (List.minimum_of (Cons NatWithZero.Zero Nil)).

Definition data_all_delivers_gauss
  : NatWithZero.mul (NatWithZero.Positive (Successor One))
      (List.sum (List.range (NatWithZero.Positive (Successor One))))
    = NatWithZero.mul (NatWithZero.Positive One) (NatWithZero.Positive (Successor One))
  := List.sum_range_closed_form One.

Definition data_all_delivers_divides
  : Prop
  := NatWithZero.Divides (NatWithZero.Positive One) NatWithZero.Zero.

Definition data_all_delivers_divides_partial_order
  : forall (m : NatWithZero) (n : NatWithZero),
      NatWithZero.Divides m n -> NatWithZero.Divides n m -> m = n
  := Antisymmetric.antisymmetry.

Definition data_all_delivers_parity
  : Prop
  := NatWithZero.Even NatWithZero.Zero /\ Integer.Odd (Negative One).

Definition data_all_delivers_semiring
  : forall (n : NatWithZero), NatWithZero.mul NatWithZero.Zero n = NatWithZero.Zero
  := Semiring.left_absorption.

Definition data_all_delivers_group
  : forall (x : Integer), Integer.add (Integer.negate x) x = Integer.Zero
  := Group.left_inverse.

Definition data_all_delivers_ring
  : forall (x : Integer) (y : Integer) (z : Integer),
      Integer.mul x (Integer.add y z) = Integer.add (Integer.mul x y) (Integer.mul x z)
  := Ring.left_distributivity.

Definition data_all_delivers_boolean_ring
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      Bool.and b1 (Bool.xor b2 b3) = Bool.xor (Bool.and b1 b2) (Bool.and b1 b3)
  := Ring.left_distributivity.

Definition data_all_delivers_mul_cancellative
  : forall (k : Nat) (m : Nat) (n : Nat), Nat.mul k m = Nat.mul k n -> m = n
  := Cancellative.left_cancellation.
