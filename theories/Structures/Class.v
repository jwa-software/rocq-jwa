(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Instance resolution looks up a hint database named [typeclass_instances],
   and [class_tactics.ml] expects it to already exist rather than creating it.
   [Corelib.Init.Notations] is where it normally comes from; with [-noinit]
   this line is. Declaring a class with a substructure field is the first
   thing that reaches for it. *)
Create HintDb typeclass_instances discriminated.
