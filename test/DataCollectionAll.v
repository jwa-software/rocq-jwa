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
  := fun (A : Type) (l : List A) . cardinality l.

Definition data_collection_all_delivers_membership
  : forall (A : Type) (a : A) . Prop
  := fun (A : Type) (a : A) . Contains a (a :: [])%list.

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
  := fun (A : Type) (x : NonEmptyList A) . cardinality x.

Definition data_collection_all_delivers_non_empty_list_membership
  : forall (A : Type) (a : A) . Prop
  := fun (A : Type) (a : A) . Contains a (NonEmptyList.One a).

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
