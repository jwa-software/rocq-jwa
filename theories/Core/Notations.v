(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [->] is a notation, not syntax, and [-noinit] keeps [Corelib.Init.Prelude]
   out. Without this line no function type can be written. *)

(* The scope name carries no mechanism; [Bind] below is what makes it apply
   where a type is expected. *)
Declare Scope jwa_type_scope.
Delimit Scope jwa_type_scope with jwa_type.

(* [Bind] covers type positions, [Open] the ones Rocq cannot classify. *)
Bind Scope jwa_type_scope with Sortclass.
Open Scope jwa_type_scope.

(* A level is a claim against every other notation in the library, so every one
   is declared here even when the meaning is supplied elsewhere -- [=] in
   [Core.Eq]. These are the levels Rocq developments read [->] and [=] at;
   changing them would silently reassociate terms written anywhere else. *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x = y"  (at level 70, no associativity).

Notation "A -> B" := (forall (_ : A), B) : jwa_type_scope.
