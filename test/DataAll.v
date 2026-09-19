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

Definition data_all_delivers_product
  : Bool * Bool
  := (true , false)%product.

Definition data_all_delivers_first
  : forall (A : Type) (a : A) (b : A), Product.first (Product_introduction a b) = a
  := fun (A : Type) (a : A) (b : A) => Identity.reflexivity a.

Definition data_all_delivers_projections
  : Bool * Bool
  := (pi_2 (true , false) , pi_1 (true , false))%product.

Definition data_all_delivers_product_functor
  : Bool * Bool
  := Functor.map (fun (b : Bool) => b) (Product_introduction true false).

Definition data_all_delivers_product_monoid
  : forall (p : Bool * Bool),
      Product.direct_product Bool.and Bool.or (Product_introduction true false) p = p
      /\ Product.direct_product Bool.and Bool.or p (Product_introduction true false) = p
  := Monoid.identity.

Definition data_all_delivers_coproduct
  : Bool + Bool
  := Coproduct.left true.

Definition data_all_delivers_copair
  : forall (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B),
      Coproduct.copair f g (Coproduct.right b) = g b
  := fun (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) =>
       Identity.reflexivity (g b).

Definition data_all_delivers_coproduct_functor
  : Bool + Bool
  := Functor.map (fun (b : Bool) => b) (Coproduct.right true).

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
  : forall (w : NatWithZero),
      NatWithZero.add NatWithZero.Zero w = w /\ NatWithZero.add w NatWithZero.Zero = w
  := Monoid.identity.

Definition data_all_delivers_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat),
      (Nat.add x y = Nat.add x z -> y = z) /\ (Nat.add x y = Nat.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_cancellative_with_zero
  : forall (x : NatWithZero) (y : NatWithZero) (z : NatWithZero),
      (NatWithZero.add x y = NatWithZero.add x z -> y = z)
      /\ (NatWithZero.add x y = NatWithZero.add z y -> x = z)
  := Cancellative.cancellation.

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
  : forall (n : Nat), Nat.mul One n = n /\ Nat.mul n One = n
  := Monoid.identity.

Definition data_all_delivers_commutative
  : forall (p1 : Nat * Bool) (p2 : Nat * Bool),
      Product.direct_product Nat.mul Bool.xor p1 p2
      = Product.direct_product Nat.mul Bool.xor p2 p1
  := Commutative.commutativity.

Definition data_all_delivers_functor
  : Option Bool
  := Functor.map (fun (b : Bool) => b) (Some true).

Definition data_all_delivers_bool_operations
  : Bool
  := (true || false) && (Bool.negate false ^^ true).

Definition data_all_delivers_bool_monoids
  : forall (b : Bool), Bool.and true b = b /\ Bool.and b true = b
  := Monoid.identity.

Definition data_all_delivers_bool_bridge
  : forall (b1 : Bool) (b2 : Bool),
      Bool.Assert (Bool.and b1 b2) <-> Bool.Assert b1 /\ Bool.Assert b2
  := Bool.assert_conjunction.

Definition data_all_delivers_list
  : List Bool
  := (Cons true Nil ++ Cons false Nil)%list.

Definition data_all_delivers_list_monoid
  : forall (A : Type) (l : List A), (Nil ++ l)%list = l /\ (l ++ Nil)%list = l
  := fun (A : Type) => Monoid.identity.

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

Definition data_all_delivers_comparable
  : forall (m : Nat) (n : Nat), Nat.LessThan m n \/ m = n \/ Nat.LessThan n m
  := Comparable.trichotomy.

Definition data_all_delivers_comparable_min
  : forall (m : NatWithZero) (n : NatWithZero),
      NatWithZero.min m n = NatWithZero.min n m
  := Comparable.min_commutativity.

Definition data_all_delivers_total_order
  : forall (m : Nat) (n : Nat), Nat.LessOrEqual m n \/ Nat.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_strict_partial_order
  : forall (n : NatWithZero), ~ NatWithZero.LessThan n n
  := Irreflexive.irreflexivity.

Definition data_all_delivers_strict_total_order
  : forall (m : Integer) (n : Integer),
      Integer.LessThan m n \/ m = n \/ Integer.LessThan n m
  := Trichotomous.trichotomy.

Definition data_all_delivers_max_monoid
  : forall (n : NatWithZero),
      NatWithZero.max NatWithZero.Zero n = n /\ NatWithZero.max n NatWithZero.Zero = n
  := Monoid.identity.

Definition data_all_delivers_nat_max_monoid
  : forall (n : Nat), Nat.max One n = n /\ Nat.max n One = n
  := Monoid.identity.

Definition data_all_delivers_division
  : NatWithZero * NatWithZero
  := Product_introduction (NatWithZero.divide (NatWithZero.Positive One) One)
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
       Comparable.at_most_totality Comparable.at_most_transitivity.

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
  : forall (x : Integer), Integer.add Integer.Zero x = x /\ Integer.add x Integer.Zero = x
  := Monoid.identity.

Definition data_all_delivers_integer_mul_monoid
  : forall (x : Integer),
      Integer.mul (Integer.Positive One) x = x /\ Integer.mul x (Integer.Positive One) = x
  := Monoid.identity.

Definition data_all_delivers_integer_cancellative
  : forall (x : Integer) (y : Integer) (z : Integer),
      (Integer.add x y = Integer.add x z -> y = z)
      /\ (Integer.add x y = Integer.add z y -> x = z)
  := Cancellative.cancellation.

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
  := Product_introduction (List.maximum_of (Cons NatWithZero.Zero Nil))
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
  : forall (n : NatWithZero),
      NatWithZero.mul NatWithZero.Zero n = NatWithZero.Zero
      /\ NatWithZero.mul n NatWithZero.Zero = NatWithZero.Zero
  := Semiring.annihilation.

Definition data_all_delivers_group
  : forall (x : Integer),
      Integer.add (Integer.negate x) x = Integer.Zero
      /\ Integer.add x (Integer.negate x) = Integer.Zero
  := Group.inverse.

Definition data_all_delivers_ring
  : forall (x : Integer) (y : Integer) (z : Integer),
      Integer.mul x (Integer.add y z) = Integer.add (Integer.mul x y) (Integer.mul x z)
      /\ Integer.mul (Integer.add y z) x = Integer.add (Integer.mul y x) (Integer.mul z x)
  := Ring.distributivity.

Definition data_all_delivers_boolean_ring
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      Bool.and b1 (Bool.xor b2 b3) = Bool.xor (Bool.and b1 b2) (Bool.and b1 b3)
      /\ Bool.and (Bool.xor b2 b3) b1 = Bool.xor (Bool.and b2 b1) (Bool.and b3 b1)
  := Ring.distributivity.

Definition data_all_delivers_mul_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat),
      (Nat.mul x y = Nat.mul x z -> y = z) /\ (Nat.mul x y = Nat.mul z y -> x = z)
  := Cancellative.cancellation.
