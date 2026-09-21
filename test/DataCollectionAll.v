(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Collection.All.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.

Definition data_collection_all_delivers
  : forall (A : Type) (a : A) . List A
  := fun (A : Type) (a : A) . (a :: [])%list.

Definition data_collection_all_delivers_operations
  : forall (A : Type) (l : List A) . List A
  := fun (A : Type) (l : List A) . (l ++ List.Nil)%list.

Definition data_collection_all_delivers_sized
  : forall (A : Type) (l : List A) . NatWithZero
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
  : forall (A : Type) (x : NonEmptyList A) . NatWithZero
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
