(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.
