(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.SourceByte.

Module Ascii. (* Ascii *)

(* A character of one byte: codes 0 to 127 are ASCII, and 128 to 255 are
 * Latin-1, which maps them one to one onto U+0080 to U+00FF.
 *)
Inductive T : Type :=
  | Ascii_introduction : Byte -> T.

Abbreviation Ascii := T.

(* [Ascii -> Byte] *)
Definition to_byte := fun (c : Ascii) .
  match c with
  | Ascii_introduction b => b
  end.

(* [Byte -> Ascii] *)
Definition from_byte := fun (b : Byte) . Ascii_introduction b.

Local Open Scope jwa_list_scope.

(* Reads the UTF-8 bytes of a string literal as one character:
 *
 *   Some c   the bytes spell exactly one character c, of code 0 to 255
 *   None     otherwise: no character, two or more, a code above 255, or bytes
 *            that are not UTF-8
 *
 * The code's bits, most significant first, and the UTF-8 bytes that spell it:
 *
 *   0 b6 b5 b4 b3 b2 b1 b0   one byte    0  b6 b5 b4 b3 b2 b1 b0
 *   1 b6 b5 b4 b3 b2 b1 b0   two bytes   1  1  0  0  0  0  1  b6
 *                                        1  0  b5 b4 b3 b2 b1 b0
 *)
(* [List SourceByte -> Option Ascii] *)
Definition from_source_bytes := fun (l : List SourceByte) .
  match l with
  | s :: [] =>
      match SourceByte.to_byte s with
      | Byte.Byte_introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0 =>
          Some (Ascii_introduction (Byte.Byte_introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0))
      | _ => None
      end
  | s1 :: s2 :: [] =>
      match SourceByte.to_byte s1, SourceByte.to_byte s2 with
      | Byte.Byte_introduction Bit.One Bit.One  Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6,
        Byte.Byte_introduction Bit.One Bit.Zero b5       b4       b3       b2       b1      b0 =>
          Some (Ascii_introduction (Byte.Byte_introduction Bit.One b6 b5 b4 b3 b2 b1 b0))
      | _, _ => None
      end
  | _ => None
  end.

(* The UTF-8 bytes of [c], as the table above [from_source_bytes] lays them out. *)
(* [Ascii -> List SourceByte] *)
Definition to_source_bytes := fun (c : Ascii) .
  match c with
  | Ascii_introduction (Byte.Byte_introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte (Byte.Byte_introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) :: []
  | Ascii_introduction (Byte.Byte_introduction Bit.One b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte
        (Byte.Byte_introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6)
      :: SourceByte.from_byte (Byte.Byte_introduction Bit.One Bit.Zero b5 b4 b3 b2 b1 b0)
      :: []
  end.

Module conversion. (* conversion *)

Module byte. (* conversion.byte *)

(* [g (f a) = a]: [f] is a section of [g], [g] a retraction of [f]. Each law
 * below is named by what [to_byte] is:
 *
 *   retraction   to_byte (from_byte b) = b   to_byte is a retraction of from_byte
 *   section      from_byte (to_byte c) = c   to_byte is a section of from_byte
 *)
(* conversion.byte.retraction *)
Theorem retraction : forall (b : Byte) . to_byte (from_byte b) = b.
Proof.
  intros b.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

(* conversion.byte.section *)
Theorem section : forall (c : Ascii) . from_byte (to_byte c) = c.
Proof.
  intros c.
  match &c with | Ascii_introduction b end.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

End byte. (* conversion.byte *)

Module source_bytes. (* conversion.source_bytes *)

(* [from_source_bytes (to_source_bytes c) = Some c]: [to_source_bytes] is a
 * section of [from_source_bytes], so every character prints as a literal that
 * reads back.
 *)
(* conversion.source_bytes.section *)
Theorem section : forall (c : Ascii) . from_source_bytes (to_source_bytes c) = Some c.
Proof.
  intros c.
  match &c with | Ascii_introduction b end.
  match &b with | Byte_introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end.
  - simpl to_source_bytes, from_source_bytes in |- *.
    leibniz
      (SourceByte.conversion.byte.retraction
        (Byte.Byte_introduction Bit.Zero &b6 &b5 &b4 &b3 &b2 &b1 &b0))
      in |- *.
    simpl in |- *.
    quod idem est.
  - simpl to_source_bytes, from_source_bytes in |- *.
    leibniz
      (SourceByte.conversion.byte.retraction
        (Byte.Byte_introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One &b6)),
      (SourceByte.conversion.byte.retraction
        (Byte.Byte_introduction Bit.One Bit.Zero &b5 &b4 &b3 &b2 &b1 &b0))
      in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End source_bytes. (* conversion.source_bytes *)

End conversion. (* conversion *)

End Ascii. (* Ascii *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Ascii], not [Ascii.T].
 *)
Abbreviation Ascii := Ascii.T.

(* A character is written as a string of one character under its key,
 * ["A"%ac], and a closed one prints back so.
 *)
String Notation Ascii.T Ascii.from_source_bytes Ascii.to_source_bytes
  : jwa_ascii_scope.

(* Where an [Ascii] is expected, a literal reads in this scope without its
 * [%ac].
 *)
Bind Scope jwa_ascii_scope with Ascii.T.
