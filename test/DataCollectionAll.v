(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Collection.All.
From jwa Require Import Data.Number.NatWithZero.

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
