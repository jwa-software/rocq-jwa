(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [->] is a notation, not syntax, and [-noinit] keeps [Corelib.Init.Prelude]
   out. Without this line no function type can be written. *)

(* Not Corelib's [type_scope]: the name carries no mechanism -- [Bind] does --
   so reusing it would only share a namespace. *)
Declare Scope jwa_type_scope.
Delimit Scope jwa_type_scope with jwa_type.

(* [Bind] covers type positions, [Open] the ones Rocq cannot classify. *)
Bind Scope jwa_type_scope with Sortclass.
Open Scope jwa_type_scope.

(* The levels Rocq developments read [->] at; changing them would silently
   reassociate terms elsewhere. *)
Notation "A -> B" := (forall (_ : A), B)
  (at level 99, right associativity, B at level 200) : jwa_type_scope.
