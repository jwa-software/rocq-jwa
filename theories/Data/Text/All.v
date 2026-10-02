(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Umbrella for [jwa.Data.Text]: re-exports the text types, so a client imports
 * them with [From jwa Require Import Data.Text.All].
 *
 * [SourceByte] is a byte of the source text, the form a string literal
 * arrives in; [Ascii] is a character of one byte, ASCII below 128 and Latin-1
 * above.
 *)
(* The modules below only [Import] [Core.All], so the open scope reaches a
 * client of this umbrella only from here.
 *)
From jwa Require Export Core.All.

(* An umbrella exports every type the interfaces under it name: [Byte] for
 * the conversions to and from bytes, [List] and [Option] for those to and
 * from a string literal.
 *)
From jwa Require Export Data.Collection.List.
From jwa Require Export Data.Machine.Byte.
From jwa Require Export Data.Option.

From jwa Require Export Data.Text.Ascii.
From jwa Require Export Data.Text.SourceByte.
