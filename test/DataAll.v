(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Data.All], imported alone. It forwards [Core.All] as well as
   [Data.Option], so names from both appear below. *)
From jwa Require Import Data.All.

Definition data_all_delivers_some
  : forall (A : Type) (B : Type) (f : A -> B) (a : A),
      ~ (true = false) -> Option.map f (Some a) = Some (f a)
  := fun (A : Type) (B : Type) (f : A -> B) (a : A) (_ : ~ (true = false)) =>
       Equijunction_reflexivity (Some (f a)).

Definition data_all_delivers_none
  : forall (A : Type),
      Option.map (fun (a : A) => a) None = None
  := fun (A : Type) =>
      Equijunction_reflexivity None.

(* [*] is a notation in [jwa_type_scope]; [( , )], [pi_1] and [pi_2] are in
   [jwa_pair_scope], reached here through its delimiter. *)
Definition data_all_delivers_pair : Bool * Bool := (true , false)%pair.

Definition data_all_delivers_first
  : forall (A : Type) (a : A) (b : A), Pair.first (Pair_introduction a b) = a
  := fun (A : Type) (a : A) (b : A) => Equijunction_reflexivity a.

Definition data_all_delivers_projections : Bool * Bool
  := (pi_2 (true , false) , pi_1 (true , false))%pair.

Definition data_all_delivers_pair_functor : Bool * Bool
  := Functor.map (fun (b : Bool) => b) (Pair_introduction true false).

(* The product monoid is found from the two [Bool] monoids by resolution. *)
Definition data_all_delivers_pair_monoid
  : forall (p : Bool * Bool),
      Pair.product Bool.and Bool.or (Pair_introduction true false) p
      = p
  := Monoid.left_identity.

(* [+] is a notation in [jwa_type_scope]. *)
Definition data_all_delivers_sum : Bool + Bool := Sum_left true.

Definition data_all_delivers_copair
  : forall (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B),
      Sum.copair f g (Sum_right b) = g b
  := fun (A : Type) (B : Type) (f : A -> Bool) (g : B -> Bool) (b : B) =>
       Equijunction_reflexivity (g b).

Definition data_all_delivers_sum_functor : Bool + Bool
  := Functor.map (fun (b : Bool) => b) (Sum_right true).

Definition data_all_delivers_unit : forall (u : Unit), u = Unit_introduction
  := Unit.introduction_surjectivity.

Definition data_all_delivers_empty : Empty -> Bool := Empty.elimination Bool.

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
       Semigroup.associativity x y z.

Definition data_all_delivers_monoid
  : forall (w : NatWithZero), NatWithZero.add Zero w = w
  := Monoid.left_identity.

(* The cancellative instances are found by resolution, one per type. *)
Definition data_all_delivers_cancellative
  : forall (n : Nat) (m : Nat) (k : Nat), Nat.add n m = Nat.add n k -> m = k
  := Cancellative.left_cancellation.

Definition data_all_delivers_cancellative_with_zero
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      NatWithZero.add m n = NatWithZero.add k n -> m = k
  := Cancellative.right_cancellation.

(* [+] and [*] live in one unopened scope per numeral type, reached here
   through the delimiters; [*] binds tighter, so the first is
   [add One (mul One (Successor One))]. *)
Definition data_all_delivers_nat_operations : Nat
  := (One + One * Successor One)%nat.

Definition data_all_delivers_nat_with_zero_operations : NatWithZero
  := (Zero + Positive One * Positive One)%nat_with_zero.

Definition data_all_delivers_power : Nat := Nat.power (Successor One) One.

Definition data_all_delivers_subtract : Option Nat := Nat.subtract (Successor One) One.

Definition data_all_delivers_mul_monoid
  : forall (n : Nat), Nat.mul One n = n
  := Monoid.left_identity.

(* The commutative instances are found by resolution; the [Pair] one from
   the two component instances. *)
Definition data_all_delivers_commutative
  : forall (p1 : Nat * Bool) (p2 : Nat * Bool),
      Pair.product Nat.mul Bool.xor p1 p2
      = Pair.product Nat.mul Bool.xor p2 p1
  := Commutative.commutativity.

Definition data_all_delivers_functor : Option Bool
  := Functor.map (fun (b : Bool) => b) (Some true).

(* The three operators are notations, so this also checks that they reach a
   client through the umbrella. *)
Definition data_all_delivers_bool_operations : Bool
  := (true || false) && (Bool.negate false ^^ true).

Definition data_all_delivers_bool_monoids
  : forall (b : Bool), Bool.and true b = b
  := Monoid.left_identity.

Definition data_all_delivers_bool_bridge
  : forall (b1 : Bool) (b2 : Bool),
      Bool.Assert (Bool.and b1 b2) <-> Bool.Assert b1 /\ Bool.Assert b2
  := Bool.assert_conjunction.

(* [++] is a notation in [jwa_list_scope], reached here through its
   delimiter; this also checks that it reaches a client through the
   umbrella. *)
Definition data_all_delivers_list : List Bool
  := (Cons true Nil ++ Cons false Nil)%list.

Definition data_all_delivers_list_monoid
  : forall (A : Type) (l : List A), (Nil ++ l)%list = l
  := fun (A : Type) => Monoid.left_identity.

(* [[]] and [::] are in [jwa_list_scope], reached here through its
   delimiter. *)
Definition data_all_delivers_empty_list : List Bool := []%list.

Definition data_all_delivers_cons : List Bool := (true :: false :: [])%list.

Definition data_all_delivers_list_functor : List Bool
  := Functor.map (fun (b : Bool) => b) (Cons true Nil).

(* [contains_member] and [belongs_to] are keyword notations in
   [jwa_list_scope]. *)
Definition data_all_delivers_contains : Prop
  := (Cons true Nil contains_member true)%list.

Definition data_all_delivers_belongs_to : Prop
  := (true belongs_to Cons true Nil)%list.

Definition data_all_delivers_does_not_contain_member : Prop
  := (Nil does_not_contain_member true)%list.

Definition data_all_delivers_does_not_belong_to : Prop
  := (true does_not_belong_to Nil)%list.

(* [<] and [<=] sit beside [+] and [*] in each numeral scope. *)
Definition data_all_delivers_nat_order : Prop := (One < Successor One)%nat.

Definition data_all_delivers_nat_with_zero_order : Prop
  := (Zero <= Positive One)%nat_with_zero.

Definition data_all_delivers_reversed_order : Prop
  := (Successor One > One)%nat /\ (Positive One >= Zero)%nat_with_zero.

Definition data_all_delivers_compare : Comparison
  := Nat.compare One (Successor One).

Definition data_all_delivers_equal : Bool := NatWithZero.equal Zero Zero.

(* The order instances are found by resolution, which also checks that
   [Relations.All] reaches a client through this umbrella. *)
Definition data_all_delivers_total_order
  : forall (m : Nat) (n : Nat), Nat.LessOrEqual m n \/ Nat.LessOrEqual n m
  := Total.totality.

Definition data_all_delivers_strict_order
  : forall (n : NatWithZero), ~ NatWithZero.LessThan n n
  := Irreflexive.irreflexivity.

Definition data_all_delivers_max_monoid
  : forall (n : NatWithZero), NatWithZero.max Zero n = n
  := Monoid.left_identity.

Definition data_all_delivers_nat_max_monoid
  : forall (n : Nat), Nat.max One n = n
  := Monoid.left_identity.

Definition data_all_delivers_division : NatWithZero * NatWithZero
  := Pair_introduction (NatWithZero.divide (Positive One) One)
                       (NatWithZero.modulo (Positive One) One).

Definition data_all_delivers_nth : Option Bool := List.nth (Cons true Nil) Zero.

Definition data_all_delivers_split_at : List Bool * List Bool
  := List.split_at (Positive One) (Cons true (Cons false Nil)).

Definition data_all_delivers_replicate : List Bool := List.replicate (Positive One) true.

Definition data_all_delivers_list_sum : NatWithZero
  := NatWithZero.add (List.sum (Cons (Positive One) Nil)) (List.product Nil).

Definition data_all_delivers_count : NatWithZero
  := List.count (fun (b : Bool) => b) (Cons true Nil).

(* The sorting theorem instantiated on [NatWithZero] through [at_most],
   whose two laws discharge the premises. *)
Definition data_all_delivers_sorting
  : forall (l : List NatWithZero),
      List.Sorted NatWithZero.at_most (List.insertion_sort NatWithZero.at_most l)
  := List.insertion_sort_sortedness NatWithZero NatWithZero.at_most
       NatWithZero.at_most_totality NatWithZero.at_most_transitivity.

(* [Integer] is exported before [NatWithZero], so the bare [Zero] and
   [Positive] above are the latter's; the integer ctors are reached
   qualified, except [Negative], which is only theirs. *)
Definition data_all_delivers_integer : Integer
  := Integer.add (Negative One) (Integer.Positive One).

(* [+], [*], [<] and [>=] in the integer scope, reached through its
   delimiter. *)
Definition data_all_delivers_integer_operations : Integer
  := (Integer.Zero + Negative One * Integer.Positive One)%integer.

Definition data_all_delivers_integer_order : Prop
  := (Negative One < Integer.Zero)%integer /\ (Integer.Positive One >= Integer.Zero)%integer.

(* The integer instances are found by resolution, one per operation. *)
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

Definition data_all_delivers_integer_embedding : Integer
  := Integer.from_nat_with_zero (Positive One).

Definition data_all_delivers_integer_equal : Bool
  := Integer.equal (Negative One) (Integer.negate (Integer.Positive One)).
