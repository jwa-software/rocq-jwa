(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

Module Endian. (* Endian *)

(* The order in which the bytes of a word are laid out: [Little] puts the
 * least significant byte first, [Big] the most significant.
 *)
Inductive T : Type :=
  | Little : T
  | Big : T.

Abbreviation Endian := T.

End Endian. (* Endian *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Endian], not [Endian.T].
 *)
Abbreviation Endian := Endian.T.
