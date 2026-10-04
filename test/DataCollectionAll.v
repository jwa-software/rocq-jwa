(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Collection.All.

Definition data_collection_all_delivers
  : forall (A : Type) (a : A) . List A
  := fun (A : Type) (a : A) . (a :: [])%list.

Definition data_collection_all_delivers_operations
  : forall (A : Type) (l : List A) . List A
  := fun (A : Type) (l : List A) . (l ++ List.Nil)%list.

Definition data_collection_all_delivers_sized
  : forall (A : Type) (l : List A) . Nat0
  := fun (A : Type) (l : List A) . Sized.cardinality l.

Definition data_collection_all_delivers_membership
  : forall (A : Type) (a : A) . Prop
  := fun (A : Type) (a : A) . Membership.Contains a (a :: [])%list.

Definition data_collection_all_delivers_non_empty_list
  : forall (A : Type) (a : A) . NonEmptyList A
  := fun (A : Type) (a : A) . NonEmptyList.Cons a (NonEmptyList.One a).

Definition data_collection_all_delivers_non_empty_list_head
  : forall (A : Type) (x : NonEmptyList A) . A
  := fun (A : Type) (x : NonEmptyList A) . NonEmptyList.head x.

Definition data_collection_all_delivers_non_empty_list_last
  : forall (A : Type) (x : NonEmptyList A) . A
  := fun (A : Type) (x : NonEmptyList A) . NonEmptyList.last x.

Definition data_collection_all_delivers_non_empty_list_length
  : forall (A : Type) (x : NonEmptyList A) . Nat
  := fun (A : Type) (x : NonEmptyList A) . NonEmptyList.length x.

Definition data_collection_all_delivers_non_empty_list_to_list
  : forall (A : Type) (x : NonEmptyList A) . List A
  := fun (A : Type) (x : NonEmptyList A) . NonEmptyList.to_list x.

Definition data_collection_all_delivers_non_empty_list_notations
  : forall (A : Type) (a : A) (x : NonEmptyList A) . NonEmptyList A
  := fun (A : Type) (a : A) (x : NonEmptyList A) .
       ((a :: x) ++ [a])%non_empty_list.

Definition data_collection_all_delivers_non_empty_list_sized
  : forall (A : Type) (x : NonEmptyList A) . Nat0
  := fun (A : Type) (x : NonEmptyList A) . Sized.cardinality x.

Definition data_collection_all_delivers_non_empty_list_membership
  : forall (A : Type) (a : A) . Prop
  := fun (A : Type) (a : A) . Membership.Contains a (NonEmptyList.One a).

Definition data_collection_all_delivers_non_empty_list_functor
  : forall (A : Type) (x : NonEmptyList A) . NonEmptyList A
  := fun (A : Type) (x : NonEmptyList A) . Functor.map (fun (a : A) . a) x.

Definition data_collection_all_delivers_non_empty_list_extrema
  : forall (A : Type) (le : A -> A -> Bool) (x : NonEmptyList A) . A
  := fun (A : Type) (le : A -> A -> Bool) (x : NonEmptyList A) .
       NonEmptyList.maximum_of le (NonEmptyList.One (NonEmptyList.minimum_of le x)).

Definition data_collection_all_delivers_non_empty_list_conversion
  : forall (A : Type) (le : A -> A -> Bool) (x : NonEmptyList A) .
      List.maximum_of le (NonEmptyList.to_list x)
      = Some (NonEmptyList.maximum_of le x)
  := @NonEmptyList.conversion.maximum.

Definition data_collection_all_delivers_list_indexing_left
  : forall (A : Type) (l1 : List A) (l2 : List A) (i : Nat0) .
      (i < List.length l1)%n0 -> List.nth (l1 ++ l2)%list i = List.nth l1 i
  := @List.indexing.left.invariance.

Definition data_collection_all_delivers_list_indexing_right
  : forall (A : Type) (l1 : List A) (l2 : List A) (i : Nat0) .
      List.nth (l1 ++ l2)%list (List.length l1 + i)%n0 = List.nth l2 i
  := @List.indexing.right.translation.

Definition data_collection_all_delivers_list_taking_identity
  : forall (A : Type) (l : List A) . List.take (List.length l) l = l
  := @List.taking.identity.

Definition data_collection_all_delivers_list_dropping_identity
  : forall (A : Type) (l : List A) . List.drop Nat0.Zero l = l
  := @List.dropping.identity.

Definition data_collection_all_delivers_list_cons_injectivity
  : forall (A : Type) (a : A) (b : A) (l : List A) (m : List A) .
      (a :: l)%list = (b :: m)%list -> a = b /\ l = m
  := @List.cons.injectivity.

Definition data_collection_all_delivers_list_comparison_specification
  : forall (A : Type) (cmp : A -> A -> Comparison) (lt : A -> A -> Prop) .
      Comparable cmp lt ->
      forall (l : List A) (m : List A) .
        (List.compare cmp l m = Comparison.Lt <-> List.LessThan cmp l m)
        /\ (List.compare cmp l m = Comparison.Eq <-> l = m)
  := @List.comparison.specification.

Definition data_collection_all_delivers_list_comparison_antisymmetry
  : forall (A : Type) (cmp : A -> A -> Comparison) (lt : A -> A -> Prop) .
      Comparable cmp lt ->
      forall (l : List A) (m : List A) .
        List.compare cmp l m = Comparison.transpose (List.compare cmp m l)
  := @List.comparison.antisymmetry.

Definition data_collection_all_delivers_list_comparison_transitivity
  : forall (A : Type) (cmp : A -> A -> Comparison) (lt : A -> A -> Prop) .
      Comparable cmp lt ->
      forall (l : List A) (m : List A) (n : List A) .
        List.LessThan cmp l m -> List.LessThan cmp m n -> List.LessThan cmp l n
  := @List.comparison.transitivity.

Definition data_collection_all_delivers_binary_tree
  : forall (A : Type) (a : A) . BinaryTree A
  := fun (A : Type) (a : A) . BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf.

Definition data_collection_all_delivers_binary_tree_induction
  : forall (A : Type) (P : BinaryTree A -> Prop) .
      P BinaryTree.Leaf ->
      (forall (l : BinaryTree A) . P l ->
        forall (a : A) (r : BinaryTree A) . P r -> P (BinaryTree.Node l a r)) ->
      (forall (t : BinaryTree A) . P t)
  := BinaryTree.induction.

Definition data_collection_all_computes_binary_tree_size
  : forall (A : Type) (a : A) (b : A) (c : A) .
      BinaryTree.size
        (BinaryTree.Node
          (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf)
          b
          (BinaryTree.Node BinaryTree.Leaf c BinaryTree.Leaf))
      = 3%n0
  := fun (A : Type) (a : A) (b : A) (c : A) . Identity.reflexivity _.

Definition data_collection_all_computes_binary_tree_height
  : forall (A : Type) (a : A) (b : A) (c : A) .
      BinaryTree.height
        (BinaryTree.Node
          (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf)
          b
          (BinaryTree.Node BinaryTree.Leaf c BinaryTree.Leaf))
      = 2%n0
  := fun (A : Type) (a : A) (b : A) (c : A) . Identity.reflexivity _.

Definition data_collection_all_computes_binary_tree_to_list
  : forall (A : Type) (a : A) (b : A) (c : A) .
      BinaryTree.to_list
        (BinaryTree.Node
          (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf)
          b
          (BinaryTree.Node BinaryTree.Leaf c BinaryTree.Leaf))
      = (a :: b :: c :: [])%list
  := fun (A : Type) (a : A) (b : A) (c : A) . Identity.reflexivity _.

Definition data_collection_all_computes_binary_tree_mirror
  : forall (A : Type) (a : A) (b : A) .
      BinaryTree.mirror
        (BinaryTree.Node (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf) b BinaryTree.Leaf)
      = BinaryTree.Node BinaryTree.Leaf b (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf)
  := fun (A : Type) (a : A) (b : A) . Identity.reflexivity _.

Definition data_collection_all_delivers_binary_tree_contains
  : forall (A : Type) (a : A) (t : BinaryTree A) . Prop
  := fun (A : Type) (a : A) (t : BinaryTree A) . BinaryTree.Contains a t.

Definition data_collection_all_delivers_binary_tree_quantifiers
  : forall (A : Type) (P : A -> Prop) (t : BinaryTree A) . Prop
  := fun (A : Type) (P : A -> Prop) (t : BinaryTree A) .
      BinaryTree.All P t /\ BinaryTree.Any P t.

Definition data_collection_all_delivers_binary_tree_sized
  : forall (A : Type) (t : BinaryTree A) . Nat0
  := fun (A : Type) (t : BinaryTree A) . Sized.cardinality t.

Definition data_collection_all_delivers_binary_tree_membership
  : forall (A : Type) (a : A) . Prop
  := fun (A : Type) (a : A) .
      Membership.Contains a (BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf).

Definition data_collection_all_delivers_binary_tree_functor
  : forall (A : Type) (t : BinaryTree A) . BinaryTree A
  := fun (A : Type) (t : BinaryTree A) . Functor.map (fun (a : A) . a) t.

Definition data_collection_all_delivers_binary_tree_mapping_identity
  : forall (A : Type) (t : BinaryTree A) . BinaryTree.map (fun (a : A) . a) t = t
  := BinaryTree.mapping.identity.

Definition data_collection_all_delivers_binary_tree_mapping_composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (t : BinaryTree A) .
      BinaryTree.map g (BinaryTree.map f t) = BinaryTree.map (fun (a : A) . g (f a)) t
  := BinaryTree.mapping.composition.

Definition data_collection_all_delivers_binary_tree_mapping_preservation_size
  : forall (A : Type) (B : Type) (f : A -> B) (t : BinaryTree A) .
      BinaryTree.size (BinaryTree.map f t) = BinaryTree.size t
  := @BinaryTree.mapping.preservation.size.

Definition data_collection_all_delivers_binary_tree_conversion_size
  : forall (A : Type) (t : BinaryTree A) .
      List.length (BinaryTree.to_list t) = BinaryTree.size t
  := @BinaryTree.conversion.size.

Definition data_collection_all_delivers_binary_tree_conversion_mapping
  : forall (A : Type) (B : Type) (f : A -> B) (t : BinaryTree A) .
      BinaryTree.to_list (BinaryTree.map f t) = List.map f (BinaryTree.to_list t)
  := @BinaryTree.conversion.mapping.

Definition data_collection_all_delivers_binary_tree_height_bound
  : forall (A : Type) (t : BinaryTree A) . (BinaryTree.height t <= BinaryTree.size t)%n0
  := @BinaryTree.height.bound.

Definition data_collection_all_delivers_binary_tree_mapping_preservation_height
  : forall (A : Type) (B : Type) (f : A -> B) (t : BinaryTree A) .
      BinaryTree.height (BinaryTree.map f t) = BinaryTree.height t
  := @BinaryTree.mapping.preservation.height.

Definition data_collection_all_delivers_binary_tree_mapping_preservation_membership
  : forall (A : Type) (B : Type) (f : A -> B) (a : A) (t : BinaryTree A) .
      BinaryTree.Contains a t -> BinaryTree.Contains (f a) (BinaryTree.map f t)
  := @BinaryTree.mapping.preservation.membership.

Definition data_collection_all_delivers_binary_tree_mirroring_involution
  : forall (A : Type) (t : BinaryTree A) . BinaryTree.mirror (BinaryTree.mirror t) = t
  := @BinaryTree.mirroring.involution.

Definition data_collection_all_delivers_binary_tree_mirroring_preservation_size
  : forall (A : Type) (t : BinaryTree A) .
      BinaryTree.size (BinaryTree.mirror t) = BinaryTree.size t
  := @BinaryTree.mirroring.preservation.size.

Definition data_collection_all_delivers_binary_tree_mirroring_preservation_height
  : forall (A : Type) (t : BinaryTree A) .
      BinaryTree.height (BinaryTree.mirror t) = BinaryTree.height t
  := @BinaryTree.mirroring.preservation.height.

Definition data_collection_all_delivers_binary_tree_mirroring_preservation_membership
  : forall (A : Type) (a : A) (t : BinaryTree A) .
      BinaryTree.Contains a (BinaryTree.mirror t) <-> BinaryTree.Contains a t
  := @BinaryTree.mirroring.preservation.membership.

Definition data_collection_all_delivers_binary_tree_conversion_mirroring
  : forall (A : Type) (t : BinaryTree A) .
      BinaryTree.to_list (BinaryTree.mirror t) = List.reverse (BinaryTree.to_list t)
  := @BinaryTree.conversion.mirroring.

Definition data_collection_all_delivers_binary_tree_conversion_membership
  : forall (A : Type) (a : A) (t : BinaryTree A) .
      BinaryTree.Contains a t <-> List.Contains a (BinaryTree.to_list t)
  := @BinaryTree.conversion.membership.

Definition data_collection_all_delivers_binary_tree_conversion_all
  : forall (A : Type) (P : A -> Prop) (t : BinaryTree A) .
      BinaryTree.All P t <-> List.All P (BinaryTree.to_list t)
  := @BinaryTree.conversion.all.

Definition data_collection_all_delivers_binary_tree_conversion_any
  : forall (A : Type) (P : A -> Prop) (t : BinaryTree A) .
      BinaryTree.Any P t <-> List.Any P (BinaryTree.to_list t)
  := @BinaryTree.conversion.any.
