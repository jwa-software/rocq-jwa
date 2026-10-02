(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Literal.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Machine.UInt8.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.SourceByte.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

Module Ascii. (* Ascii *)

(* A character of one byte: codes 0 to 127 are ASCII, and 128 to 255 are
 * Latin-1, which maps them one to one onto U+0080 to U+00FF.
 *)
Inductive T : Type :=
  | introduction : Byte -> T.

Abbreviation Ascii := T.

(* [Ascii -> Byte] *)
Definition to_byte := fun (c : Ascii) .
  match c with
  | Ascii.introduction b => b
  end.

(* [Byte -> Ascii] *)
Definition from_byte := fun (b : Byte) . Ascii.introduction b.

(* The character's code, from 0 to 255, as an unsigned byte. *)
(* [Ascii -> UInt8] *)
Definition code := fun (c : Ascii) . UInt8.from_byte (to_byte c).

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
      | Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0 =>
          Some (Ascii.introduction (Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0))
      | _ => None
      end
  | s1 :: s2 :: [] =>
      match SourceByte.to_byte s1, SourceByte.to_byte s2 with
      | Byte.introduction Bit.One Bit.One  Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6,
        Byte.introduction Bit.One Bit.Zero b5       b4       b3       b2       b1      b0 =>
          Some (Ascii.introduction (Byte.introduction Bit.One b6 b5 b4 b3 b2 b1 b0))
      | _, _ => None
      end
  | _ => None
  end.

(* The UTF-8 bytes of [c], as the table above [from_source_bytes] lays them out. *)
(* [Ascii -> List SourceByte] *)
Definition to_source_bytes := fun (c : Ascii) .
  match c with
  | Ascii.introduction (Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte (Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) :: []
  | Ascii.introduction (Byte.introduction Bit.One b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte
        (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6)
      :: SourceByte.from_byte (Byte.introduction Bit.One Bit.Zero b5 b4 b3 b2 b1 b0)
      :: []
  end.

(* Characters are ordered by their codes. *)
(* [Ascii -> Ascii -> Prop] *)
Definition LessThan := fun (x : Ascii) (y : Ascii) . (code x < code y)%uint8.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_ascii_scope.

(* [Ascii -> Ascii -> Prop] *)
Definition LessOrEqual := fun (x : Ascii) (y : Ascii) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_ascii_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_ascii_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_ascii_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_ascii_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_ascii_scope.

(* [Ascii -> Ascii -> Comparison] *)
Definition compare := fun (x : Ascii) (y : Ascii) . UInt8.compare (code x) (code y).

(* [Ascii -> Ascii -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Ascii -> Ascii -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Ascii -> Ascii -> Ascii] *)
Abbreviation min := (Comparable.min compare).

(* [Ascii -> Ascii -> Ascii] *)
Abbreviation max := (Comparable.max compare).

Local Open Scope jwa_ascii_scope.

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
  match &c with | introduction b end.
  simpl to_byte, from_byte in |- *.
  quod idem est.
Qed.

End byte. (* conversion.byte *)

Module code. (* conversion.code *)

(* conversion.code.injectivity *)
Theorem injectivity : forall {x : Ascii} {y : Ascii} . code x = code y -> x = y.
Proof.
  intros x y e.
  simpl code in &e.
  congru UInt8.to_byte, &e |- f.
  leibniz
    (UInt8.conversion.byte.retraction (to_byte &x)),
    (UInt8.conversion.byte.retraction (to_byte &y))
    in &f.
  congru from_byte, &f |- g.
  leibniz (conversion.byte.section &x), (conversion.byte.section &y) in &g.
  ipso &g.
Qed.

End code. (* conversion.code *)

Module source_bytes. (* conversion.source_bytes *)

(* [from_source_bytes (to_source_bytes c) = Some c]: [to_source_bytes] is a
 * section of [from_source_bytes], so every character prints as a literal that
 * reads back.
 *)
(* conversion.source_bytes.section *)
Theorem section : forall (c : Ascii) . from_source_bytes (to_source_bytes c) = Some c.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end.
  - simpl to_source_bytes, from_source_bytes in |- *.
    leibniz
      (SourceByte.conversion.byte.retraction
        (Byte.introduction Bit.Zero &b6 &b5 &b4 &b3 &b2 &b1 &b0))
      in |- *.
    simpl in |- *.
    quod idem est.
  - simpl to_source_bytes, from_source_bytes in |- *.
    leibniz
      (SourceByte.conversion.byte.retraction
        (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One &b6)),
      (SourceByte.conversion.byte.retraction
        (Byte.introduction Bit.One Bit.Zero &b5 &b4 &b3 &b2 &b1 &b0))
      in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End source_bytes. (* conversion.source_bytes *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Ascii} {y : Ascii} {z : Ascii} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (UInt8.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : Ascii) (y : Ascii) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  simpl compare, LessThan in |- *.
  let proof s := UInt8.comparison.specification (code &x) (code &y).
  match &s with | strict equality end.
  divide et impera.
  - ipso &strict.
  - divide et impera.
    + intro c.
      ipso (conversion.code.injectivity (modus aequans &equality, &c)).
    + intro e.
      ipso (modus aequans &equality, (congru code, &e)).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : Ascii) (y : Ascii) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (UInt8.comparison.antisymmetry (code &x) (code &y)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

End Ascii. (* Ascii *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Ascii], not [Ascii.T].
 *)
Abbreviation Ascii := Ascii.T.

(* Makes the notations declared in [Module Ascii] usable in every file that
 * imports this one, as [(x < y)%ac] or under an opened [jwa_ascii_scope].
 *)
Export (notations) Ascii.

(* A character is written as a string of one character under its key,
 * ["A"%ac], and a closed one prints back so.
 *)
String Notation Ascii.T Ascii.from_source_bytes Ascii.to_source_bytes
  : jwa_ascii_scope.

(* Where an [Ascii] is expected, a literal reads in this scope without its
 * [%ac].
 *)
Bind Scope jwa_ascii_scope with Ascii.T.
