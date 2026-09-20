(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Collection.All.

Definition data_collection_all_delivers
  : forall (A : Type) (a : A) . List A
  := fun (A : Type) (a : A) . (a :: [])%list.

Definition data_collection_all_delivers_operations
  : forall (A : Type) (l : List A) . List A
  := fun (A : Type) (l : List A) . (l ++ Nil)%list.
