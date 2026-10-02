(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.All.

Definition data_all_delivers_some
  : forall (A : Type) (B : Type) (f : A -> B) (a : A) .
      ~ (true = false) -> Option.map f (Some a) = Some (f a)
  := fun (A : Type) (B : Type) (f : A -> B) (a : A) (_ : ~ (true = false)) .
       Identity.reflexivity (Some (f a)).

Definition data_all_delivers_none
  : forall (A : Type) .
      Option.map (fun (a : A) . a) None = None
  := fun (A : Type) .
       Identity.reflexivity None.

Definition data_all_delivers_option_defaulting_retraction
  : forall (A : Type) (d : A) (a : A) . Option.unwrap_or d (Some a) = a
  := @Option.defaulting.retraction.

Definition data_all_delivers_option_defaulting_fallback
  : forall (A : Type) (d : A) . Option.unwrap_or d None = d
  := @Option.defaulting.fallback.

Definition data_all_delivers_option_unwrapping_retraction
  : forall (A : Type) (a : A) (h : ~ (Some a = None)) . Option.unwrap (Some a) h = a
  := @Option.unwrapping.retraction.

Definition data_all_delivers_option_unwrapping_restoration
  : forall (A : Type) (o : Option A) (h : ~ (o = None)) . Some (Option.unwrap o h) = o
  := @Option.unwrapping.restoration.

Definition data_all_delivers_option_unwrapping_irrelevance
  : forall (A : Type) (o : Option A) (h1 : ~ (o = None)) (h2 : ~ (o = None)) .
      Option.unwrap o h1 = Option.unwrap o h2
  := @Option.unwrapping.irrelevance.

Definition data_all_delivers_option_unwrap_or_of_a_value
  : Option.unwrap_or false (Some true) = true
  := Identity.reflexivity true.

Theorem data_all_delivers_some_is_not_none
  : ~ (Some true = None).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

Definition data_all_delivers_option_unwrap_of_a_value
  : Option.unwrap (Some true) data_all_delivers_some_is_not_none = true
  := Identity.reflexivity true.

Definition data_all_delivers_product
  : Bool * Bool
  := (true , false)%product.

Definition data_all_delivers_bit
  : forall (b : Bit) . (b ^. b)%bit = Bit.Zero
  := Bit.sejunction.irreflexivity.

Definition data_all_delivers_first
  : forall (A : Type) (a : A) (b : A) . Product.first (a , b)%product = a
  := fun (A : Type) (a : A) (b : A) . Identity.reflexivity a.

Definition data_all_delivers_projections
  : Bool * Bool
  := (pi_2 (true , false) , pi_1 (true , false))%product.

Definition data_all_delivers_product_functor
  : Bool * Bool
  := Functor.map (fun (b : Bool) . b) (true , false)%product.

Definition data_all_delivers_product_monoid
  : forall (p : Bool * Bool) .
      Product.direct_product Bool.and Bool.or (true , false)%product p = p
      /\ Product.direct_product Bool.and Bool.or p (true , false)%product = p
  := Monoid.identity.

Definition data_all_delivers_coproduct
  : Bool + Bool
  := Coproduct.left true.

Definition data_all_delivers_copair
  : forall (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) .
      Coproduct.copair f g (Coproduct.right b) = g b
  := fun (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) .
       Identity.reflexivity (g b).

Definition data_all_delivers_coproduct_functor
  : Bool + Bool
  := Functor.map (fun (b : Bool) . b) (Coproduct.right true).

Definition data_all_delivers_unit
  : forall (u : Unit) . u = Unit.introduction
  := Unit.surjectivity.

Definition data_all_delivers_empty
  : Empty -> Bool
  := Empty.elimination Bool.

Definition data_all_delivers_nat
  : Nat
  := Nat.Successor Nat.One.

Definition data_all_delivers_zero
  : Nat0
  := Nat0.Zero.

Definition data_all_delivers_positive
  : Nat0
  := Nat0.Positive Nat.One.

Definition data_all_delivers_add
  : Nat0
  := Nat0.add (Nat0.Positive (Nat.add Nat.One Nat.One)) Nat0.Zero.

Definition data_all_delivers_instances
  : forall (x : Nat) (y : Nat) (z : Nat) (w : Nat0) .
      Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z)
  := fun (x : Nat) (y : Nat) (z : Nat) (_ : Nat0) .
       Semigroup.associativity x y z.

Definition data_all_delivers_monoid
  : forall (w : Nat0) .
      Nat0.add Nat0.Zero w = w /\ Nat0.add w Nat0.Zero = w
  := Monoid.identity.

Definition data_all_delivers_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat) .
      (Nat.add x y = Nat.add x z -> y = z) /\ (Nat.add x y = Nat.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_cancellative_with_zero
  : forall (x : Nat0) (y : Nat0) (z : Nat0) .
      (Nat0.add x y = Nat0.add x z -> y = z)
      /\ (Nat0.add x y = Nat0.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_nat_operations
  : Nat
  := (Nat.One + Nat.One * Nat.Successor Nat.One)%n.

Definition data_all_delivers_nat0_operations
  : Nat0
  := (Nat0.Zero + Nat0.Positive Nat.One * Nat0.Positive Nat.One)%n0.

Definition data_all_delivers_power
  : Nat
  := Nat.power (Nat.Successor Nat.One) Nat.One.

Definition data_all_delivers_power_notation
  : Nat
  := (Nat.Successor Nat.One ^ Nat.One)%n.

Definition data_all_delivers_nat0_power_notation
  : Nat0
  := (Nat0.Positive Nat.One ^ Nat0.Zero)%n0.

Definition data_all_delivers_sub
  : Option Nat
  := Nat.sub (Nat.Successor Nat.One) Nat.One.

Definition data_all_delivers_mul_monoid
  : forall (n : Nat) . Nat.mul Nat.One n = n /\ Nat.mul n Nat.One = n
  := Monoid.identity.

Definition data_all_delivers_commutative
  : forall (p1 : Nat * Bool) (p2 : Nat * Bool) .
      Product.direct_product Nat.mul Bool.xor p1 p2
      = Product.direct_product Nat.mul Bool.xor p2 p1
  := Commutative.commutativity.

Definition data_all_delivers_functor
  : Option Bool
  := Functor.map (fun (b : Bool) . b) (Some true).

Definition data_all_delivers_bool_operations
  : Bool
  := ((true || false) && (! false ^^ true))%bool.

Definition data_all_delivers_bool_monoids
  : forall (b : Bool) . Bool.and true b = b /\ Bool.and b true = b
  := Monoid.identity.

Definition data_all_delivers_bool_bridge
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (Bool.and b1 b2) <-> Assert b1 /\ Assert b2
  := Assert.conjunction.

Definition data_all_delivers_list
  : List Bool
  := (List.Cons true List.Nil ++ List.Cons false List.Nil)%list.

Definition data_all_delivers_list_monoid
  : forall (A : Type) (l : List A) .
      (List.Nil ++ l)%list = l /\ (l ++ List.Nil)%list = l
  := fun (A : Type) . Monoid.identity.

Definition data_all_delivers_empty_list
  : List Bool
  := []%list.

Definition data_all_delivers_cons
  : List Bool
  := (true :: false :: [])%list.

Definition data_all_delivers_list_functor
  : List Bool
  := Functor.map (fun (b : Bool) . b) (List.Cons true List.Nil).

Definition data_all_delivers_contains
  : Prop
  := (List.Cons true List.Nil contains_member true)%list.

Definition data_all_delivers_belongs_to
  : Prop
  := (true belongs_to List.Cons true List.Nil)%list.

Definition data_all_delivers_does_not_contain_member
  : Prop
  := (List.Nil does_not_contain_member true)%list.

Definition data_all_delivers_does_not_belong_to
  : Prop
  := (true does_not_belong_to List.Nil)%list.

Definition data_all_delivers_nat_order
  : Prop
  := (Nat.One < Nat.Successor Nat.One)%n.

Definition data_all_delivers_nat0_order
  : Prop
  := (Nat0.Zero <= Nat0.Positive Nat.One)%n0.

Definition data_all_delivers_reversed_order
  : Prop
  := (Nat.Successor Nat.One > Nat.One)%n /\ (Nat0.Positive Nat.One >= Nat0.Zero)%n0.

Definition data_all_delivers_compare
  : Comparison
  := Nat.compare Nat.One (Nat.Successor Nat.One).

Definition data_all_delivers_eq
  : Bool
  := Nat0.eq Nat0.Zero Nat0.Zero.

Definition data_all_delivers_comparable_specifications
  : forall (m : Nat) (n : Nat) .
      (Nat.compare m n = Comparison.Lt <-> Nat.LessThan m n)
    /\ (Nat.compare m n = Comparison.Gt <-> Nat.LessThan n m)
  := fun (m : Nat) (n : Nat) .
       conjoin
         (Comparable.comparison.strict.specification m n),
         (Comparable.comparison.strict.transposition.specification m n).

Definition data_all_delivers_comparable
  : forall (m : Nat) (n : Nat) . Nat.LessThan m n \/ m = n \/ Nat.LessThan n m
  := Comparable.order.strict.trichotomy.

Definition data_all_delivers_comparable_min
  : forall (m : Nat0) (n : Nat0) .
      Nat0.min m n = Nat0.min n m
  := Comparable.minimum.commutativity.

Definition data_all_delivers_total_order
  : forall (m : Nat) (n : Nat) . Nat.LessOrEqual m n \/ Nat.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_strict_partial_order
  : forall (n : Nat0) . ~ Nat0.LessThan n n
  := Irreflexive.irreflexivity.

Definition data_all_delivers_strict_total_order
  : forall (m : Integer) (n : Integer) .
      Integer.LessThan m n \/ m = n \/ Integer.LessThan n m
  := Trichotomous.trichotomy.

Definition data_all_delivers_max_monoid
  : forall (n : Nat0) .
      Nat0.max Nat0.Zero n = n /\ Nat0.max n Nat0.Zero = n
  := Monoid.identity.

Definition data_all_delivers_nat_max_monoid
  : forall (n : Nat) . Nat.max Nat.One n = n /\ Nat.max n Nat.One = n
  := Monoid.identity.

Definition data_all_delivers_division
  : Nat0 * Nat0
  := (Nat0.divide (Nat0.Positive Nat.One) Nat.One
     , Nat0.modulo (Nat0.Positive Nat.One) Nat.One)%product.

Definition data_all_delivers_nth
  : Option Bool
  := List.nth (List.Cons true List.Nil) Nat0.Zero.

Definition data_all_delivers_split_at
  : List Bool * List Bool
  := List.split_at (Nat0.Positive Nat.One) (List.Cons true (List.Cons false List.Nil)).

Definition data_all_delivers_replicate
  : List Bool
  := List.replicate (Nat0.Positive Nat.One) true.

Definition data_all_delivers_list_sum
  : Nat0
  := Nat0.add (List.sum (List.Cons (Nat0.Positive Nat.One) List.Nil))
                     (List.product List.Nil).

Definition data_all_delivers_count
  : Nat0
  := List.count (fun (b : Bool) . b) (List.Cons true List.Nil).

Definition data_all_delivers_sorting
  : forall (l : List Nat0) .
      List.Sorted Nat0.le (List.insertion_sort Nat0.le l)
  := List.sorting.sortedness
       (fun (m : Nat0) (n : Nat0) .
          Biconditional.backward.elimination
            (Disjunction.congruence
               (Comparable.order.reflection m n) (Comparable.order.reflection n m))
            (Comparable.order.totality m n))
       (fun (a : Nat0) (b : Nat0) (c : Nat0)
            (h1 : Nat0.le a b = true) (h2 : Nat0.le b c = true) .
          Biconditional.backward.elimination
            (Comparable.order.reflection a c)
            (Comparable.order.transitivity a b c
               (Biconditional.forward.elimination (Comparable.order.reflection a b) h1)
               (Biconditional.forward.elimination (Comparable.order.reflection b c) h2))).

Definition data_all_delivers_integer
  : Integer
  := Integer.add (Integer.Negative Nat.One) (Integer.Positive Nat.One).

Definition data_all_delivers_integer_operations
  : Integer
  := (Integer.Zero + Integer.Negative Nat.One * Integer.Positive Nat.One)%z.

Definition data_all_delivers_integer_order
  : Prop
  := (Integer.Negative Nat.One < Integer.Zero)%z /\ (Integer.Positive Nat.One >= Integer.Zero)%z.

Definition data_all_delivers_integer_monoid
  : forall (x : Integer) . Integer.add Integer.Zero x = x /\ Integer.add x Integer.Zero = x
  := Monoid.identity.

Definition data_all_delivers_integer_mul_monoid
  : forall (x : Integer) .
      Integer.mul (Integer.Positive Nat.One) x = x /\ Integer.mul x (Integer.Positive Nat.One) = x
  := Monoid.identity.

Definition data_all_delivers_integer_cancellative
  : forall (x : Integer) (y : Integer) (z : Integer) .
      (Integer.add x y = Integer.add x z -> y = z)
      /\ (Integer.add x y = Integer.add z y -> x = z)
  := Cancellative.cancellation.

Definition data_all_delivers_integer_total_order
  : forall (m : Integer) (n : Integer) . Integer.LessOrEqual m n \/ Integer.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_integer_embedding
  : Integer
  := Integer.from_nat0 (Nat0.Positive Nat.One).

Definition data_all_delivers_integer_eq
  : Bool
  := Integer.eq (Integer.Negative Nat.One) (Integer.negate (Integer.Positive Nat.One)).

Definition data_all_delivers_range_from_zero
  : List Nat0
  := List.range_from_zero (Nat0.Positive Nat.One).

Definition data_all_delivers_range
  : List Nat0
  := List.range (Nat0.Positive Nat.One) (Nat0.Positive (Nat.Successor Nat.One)).

Definition data_all_delivers_range_inclusive
  : List Nat0
  := List.range_inclusive Nat0.Zero (Nat0.Positive Nat.One).

Definition data_all_delivers_extrema
  : Option Nat0 * Option Nat0
  := (List.maximum_of Nat0.le (List.Cons Nat0.Zero List.Nil)
     , List.minimum_of Nat0.le (List.Cons Nat0.Zero List.Nil))%product.

Definition data_all_delivers_gauss
  : Nat0.mul (Nat0.Positive (Nat.Successor Nat.One))
      (List.sum (List.range_from_zero (Nat0.Positive (Nat.Successor Nat.One))))
    = Nat0.mul (Nat0.Positive Nat.One) (Nat0.Positive (Nat.Successor Nat.One))
  := List.range.from_zero.sum.closed_form Nat.One.

Definition data_all_delivers_divides
  : Prop
  := Nat0.Divides (Nat0.Positive Nat.One) Nat0.Zero.

Definition data_all_delivers_divides_partial_order
  : forall (m : Nat0) (n : Nat0) .
      Nat0.Divides m n -> Nat0.Divides n m -> m = n
  := Antisymmetric.antisymmetry.

Definition data_all_delivers_parity
  : Prop
  := Nat0.Even Nat0.Zero /\ Integer.Odd (Integer.Negative Nat.One).

Definition data_all_delivers_semiring
  : forall (n : Nat0) .
      Nat0.mul Nat0.Zero n = Nat0.Zero
      /\ Nat0.mul n Nat0.Zero = Nat0.Zero
  := Semiring.annihilation.

Definition data_all_delivers_group
  : forall (x : Integer) .
      Integer.add (Integer.negate x) x = Integer.Zero
      /\ Integer.add x (Integer.negate x) = Integer.Zero
  := Group.inverse.

Definition data_all_delivers_ring
  : forall (x : Integer) (y : Integer) (z : Integer) .
      Integer.mul x (Integer.add y z) = Integer.add (Integer.mul x y) (Integer.mul x z)
      /\ Integer.mul (Integer.add y z) x = Integer.add (Integer.mul y x) (Integer.mul z x)
  := Ring.distributivity.

Definition data_all_delivers_boolean_ring
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      Bool.and b1 (Bool.xor b2 b3) = Bool.xor (Bool.and b1 b2) (Bool.and b1 b3)
      /\ Bool.and (Bool.xor b2 b3) b1 = Bool.xor (Bool.and b2 b1) (Bool.and b3 b1)
  := Ring.distributivity.

Definition data_all_delivers_mul_cancellative
  : forall (x : Nat) (y : Nat) (z : Nat) .
      (Nat.mul x y = Nat.mul x z -> y = z) /\ (Nat.mul x y = Nat.mul z y -> x = z)
  := Cancellative.cancellation.
