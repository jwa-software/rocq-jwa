(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Option.

(* The plugin behind [Number Notation]. It reads a numeral literal into the
 * types below and hands that to the parsing function a notation names; it
 * finds each type by the name it is registered under and builds its terms by
 * constructor position, so every type here has the shape the plugin expects.
 * Digits run most significant first: [1011] is [One (Zero (One (One End)))].
 *)
Declare ML Module "rocq-runtime.plugins.number_string_notation".

Module Numeral. (* Numeral *)

Module Decimal. (* Decimal *)

Module Digits. (* Digits *)

Inductive T : Type :=
  | End   : T
  | Zero  : T -> T
  | One   : T -> T
  | Two   : T -> T
  | Three : T -> T
  | Four  : T -> T
  | Five  : T -> T
  | Six   : T -> T
  | Seven : T -> T
  | Eight : T -> T
  | Nine  : T -> T.

Abbreviation Digits := T.

End Digits. (* Digits *)

Abbreviation Digits := Digits.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Positive : Digits -> T
  | Negative : Digits -> T.

Abbreviation Signed := T.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

(* [1.5] is [Point 1 5], [1.5e3] is [PointExponent 1 5 3]. *)
Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Point         : Signed -> Digits -> T
  | PointExponent : Signed -> Digits -> Signed -> T.

Abbreviation Fractional := T.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Decimal. (* Decimal *)

Module Hexadecimal. (* Hexadecimal *)

Module Digits. (* Digits *)

Inductive T : Type :=
  | End      : T
  | Zero     : T -> T
  | One      : T -> T
  | Two      : T -> T
  | Three    : T -> T
  | Four     : T -> T
  | Five     : T -> T
  | Six      : T -> T
  | Seven    : T -> T
  | Eight    : T -> T
  | Nine     : T -> T
  | Ten      : T -> T
  | Eleven   : T -> T
  | Twelve   : T -> T
  | Thirteen : T -> T
  | Fourteen : T -> T
  | Fifteen  : T -> T.

Abbreviation Digits := T.

End Digits. (* Digits *)

Abbreviation Digits := Digits.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Positive : Digits -> T
  | Negative : Digits -> T.

Abbreviation Signed := T.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

(* The exponent of a hexadecimal literal is written in decimal. *)
Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Point         : Signed -> Digits -> T
  | PointExponent : Signed -> Digits -> Decimal.Signed -> T.

Abbreviation Fractional := T.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Hexadecimal. (* Hexadecimal *)

Module Unsigned. (* Unsigned *)

Inductive T : Type :=
  | Decimal     : Decimal.Digits -> T
  | Hexadecimal : Hexadecimal.Digits -> T.

Abbreviation Unsigned := T.

End Unsigned. (* Unsigned *)

Abbreviation Unsigned := Unsigned.T.

Module Signed. (* Signed *)

Inductive T : Type :=
  | Decimal     : Decimal.Signed -> T
  | Hexadecimal : Hexadecimal.Signed -> T.

Abbreviation Signed := T.

End Signed. (* Signed *)

Abbreviation Signed := Signed.T.

Module Fractional. (* Fractional *)

Inductive T : Type :=
  | Decimal     : Decimal.Fractional -> T
  | Hexadecimal : Hexadecimal.Fractional -> T.

Abbreviation Fractional := T.

End Fractional. (* Fractional *)

Abbreviation Fractional := Fractional.T.

End Numeral. (* Numeral *)

Register Numeral.Decimal.Digits.T         as num.uint.type.
Register Numeral.Decimal.Signed.T         as num.int.type.
Register Numeral.Decimal.Fractional.T     as num.decimal.type.
Register Numeral.Hexadecimal.Digits.T     as num.hexadecimal_uint.type.
Register Numeral.Hexadecimal.Signed.T     as num.hexadecimal_int.type.
Register Numeral.Hexadecimal.Fractional.T as num.hexadecimal.type.
Register Numeral.Unsigned.T               as num.num_uint.type.
Register Numeral.Signed.T                 as num.num_int.type.
Register Numeral.Fractional.T             as num.number.type.

(* A parsing function answering [None] refuses the literal. The plugin tells
 * [Some] from [None] by their arguments, not their order, so [Option] serves
 * as it is.
 *)
Register Option.T as core.option.type.
