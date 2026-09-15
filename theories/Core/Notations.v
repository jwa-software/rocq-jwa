(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [-noinit] keeps [Corelib.Init.Prelude] out, so every notation, [->]
   included, is declared by this tree: the scope and the levels here, each
   meaning beside the thing it denotes. *)

(* The scope name carries no mechanism; [Bind] below is what makes it apply
   where a type is expected. *)
Declare Scope jwa_type_scope.
Delimit Scope jwa_type_scope with jwa_type.

(* [Bind] covers type positions, [Open] the ones Rocq cannot classify. *)
Bind Scope jwa_type_scope with Sortclass.
Open Scope jwa_type_scope.

(* A level is a claim against every other notation in the library, so all of
   them are declared here, while every meaning is supplied elsewhere: [=] in
   [Core.Eq]; [->], [~], [/\], [\/] and [<->] in [Core.Logic]. *)

(* The ordering is the load-bearing part: 70 < 75 < 80 < 85 < 95 < 99 is what
   reads [~ x = y /\ P -> Q] as [((~ (x = y)) /\ P) -> Q], and [A \/ B <-> C]
   as [(A \/ B) <-> C]. *)
Reserved Notation "x -> y"
  (at level 99, right associativity, y at level 200).
Reserved Notation "x = y"
  (at level 70, no associativity).
Reserved Notation "x /\ y"
  (at level 80, right associativity).
Reserved Notation "x \/ y"
  (at level 85, right associativity).
Reserved Notation "x <-> y"
  (at level 95, no associativity).
Reserved Notation "~ x"
  (at level 75, right associativity).
