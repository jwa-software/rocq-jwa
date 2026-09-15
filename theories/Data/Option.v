(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires. *)
From jwa Require Import Core.All.

Inductive Option (A : Type) : Type :=
  | None : Option A
  | Some : A -> Option A.

Arguments None {A}.
Arguments Some {A} a.

(* A module may carry the type's name; its members read [Option.map]. *)
Module Option.

(* [forall {A : Type} {B : Type}, (A -> B) -> Option A -> Option B] *)
Definition map := fun {A : Type} {B : Type} (f : A -> B) (o : Option A) =>
  match o return Option B
  with
  | None   => None
  | Some a => Some (f a)
  end.

End Option.
