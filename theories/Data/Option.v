(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires. *)
From jwa Require Import Core.All.

Inductive Option (A : Type) : Type :=
  | None : Option A
  | Some : A -> Option A.

Arguments None {A}.
Arguments Some {A} a.
