(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Assert.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Literal.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Machine.UInt32.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.Ascii.
From jwa Require Import Data.Text.SourceByte.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.

Module Utf8. (* Utf8 *)

(* The ctors below take only bytes that spell a character, so the checks
 * they assert come first. Each follows a rule of the grammar of UTF-8 in
 * RFC 3629, section 4, written below as the bits of each byte, most
 * significant first, with x for a bit of the character's code.
 *)

(* A continuation byte:
 *
 *   10xxxxxx
 *)
(* [Byte -> Bool] *)
Definition is_tail := fun (x : Byte) .
  match x with
  | Byte.introduction 1 0 _ _ _ _ _ _ => true
  | _ => false
  end.

(* A character of one byte:
 *
 *   0xxxxxxx
 *)
(* [Byte -> Bool] *)
Definition is_one_byte := fun (x : Byte) .
  match x with
  | Byte.introduction 0 _ _ _ _ _ _ _ => true
  | _ => false
  end.

(* A character of two bytes:
 *
 *   110xxxxx 10xxxxxx
 *
 * except a first byte 1100000x, which would spell U+0000 to U+007F again.
 *)
(* [Byte -> Byte -> Bool] *)
Definition is_two_bytes := fun (x : Byte) (y : Byte) .
  match x with
  | Byte.introduction 1 1 0 0 0 0 0 _ => false
  | Byte.introduction 1 1 0 _ _ _ _ _ => is_tail y
  | _ => false
  end.

(* A character of three bytes:
 *
 *   1110xxxx 10xxxxxx 10xxxxxx
 *
 * except a second byte 100xxxxx after 11100000, which would spell U+0000 to
 * U+07FF again, and 101xxxxx after 11101101, which would spell the
 * surrogates U+D800 to U+DFFF.
 *)
(* [Byte -> Byte -> Byte -> Bool] *)
Definition is_three_bytes := fun (x : Byte) (y : Byte) (z : Byte) .
  match x with
  | Byte.introduction 1 1 1 0 0 0 0 0 =>
      match y with
      | Byte.introduction 1 0 1 _ _ _ _ _ => is_tail z
      | _ => false
      end
  | Byte.introduction 1 1 1 0 1 1 0 1 =>
      match y with
      | Byte.introduction 1 0 0 _ _ _ _ _ => is_tail z
      | _ => false
      end
  | Byte.introduction 1 1 1 0 _ _ _ _ =>
      Bool.and (is_tail y) (is_tail z)
  | _ => false
  end.

(* A character of four bytes:
 *
 *   11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
 *
 * except a first byte past 11110100, a second byte 1000xxxx after 11110000,
 * which would spell U+0000 to U+FFFF again, and one past 1000xxxx after
 * 11110100, which would pass U+10FFFF.
 *)
(* [Byte -> Byte -> Byte -> Byte -> Bool] *)
Definition is_four_bytes := fun (x : Byte) (y : Byte) (z : Byte) (w : Byte) .
  match x with
  | Byte.introduction 1 1 1 1 0 0 0 0 =>
      match y with
      | Byte.introduction 1 0 0 0 _ _ _ _ => false
      | Byte.introduction 1 0 _ _ _ _ _ _ => Bool.and (is_tail z) (is_tail w)
      | _ => false
      end
  | Byte.introduction 1 1 1 1 0 1 0 0 =>
      match y with
      | Byte.introduction 1 0 0 0 _ _ _ _ =>
          Bool.and (is_tail z) (is_tail w)
      | _ => false
      end
  | Byte.introduction 1 1 1 1 0 0 _ _ =>
      Bool.and (is_tail y) (Bool.and (is_tail z) (is_tail w))
  | _ => false
  end.

(* A Unicode character, U+0000 to U+10FFFF without the surrogates U+D800 to
 * U+DFFF, held as the one to four bytes UTF-8 spells it with, first byte
 * first. Each ctor carries the proof that its bytes spell a character, so no
 * other value can be built.
 *)
Inductive T : Type :=
  | OneByte    : forall (x : Byte) . Assert (is_one_byte x) -> T
  | TwoBytes   : forall (x : Byte) (y : Byte) . Assert (is_two_bytes x y) -> T
  | ThreeBytes : forall (x : Byte) (y : Byte) (z : Byte) . Assert (is_three_bytes x y z) -> T
  | FourBytes  : forall (x : Byte) (y : Byte) (z : Byte) (w : Byte) . Assert (is_four_bytes x y z w) -> T.

Abbreviation Utf8 := T.

Local Open Scope jwa_list_scope.

(* [Utf8 -> List Byte] *)
Definition to_bytes := fun (c : Utf8) .
  match c with
  | Utf8.OneByte x _ => x :: []
  | Utf8.TwoBytes x y _ => x :: y :: []
  | Utf8.ThreeBytes x y z _ => x :: y :: z :: []
  | Utf8.FourBytes x y z w _ => x :: y :: z :: w :: []
  end.

(* [Some c] when the bytes spell exactly one character [c], [None] otherwise. *)
(* [List Byte -> Option Utf8] *)
Definition from_bytes := fun (l : List Byte) .
  match l with
  | x :: [] => Assert.guard (is_one_byte x) (Utf8.OneByte x)
  | x :: y :: [] => Assert.guard (is_two_bytes x y) (Utf8.TwoBytes x y)
  | x :: y :: z :: [] => Assert.guard (is_three_bytes x y z) (Utf8.ThreeBytes x y z)
  | x :: y :: z :: w :: [] => Assert.guard (is_four_bytes x y z w) (Utf8.FourBytes x y z w)
  | _ => None
  end.

(* Reads the UTF-8 bytes of a string literal as one character, by
 * [from_bytes].
 *)
(* [List SourceByte -> Option Utf8] *)
Definition from_source_bytes := fun (l : List SourceByte) .
  from_bytes (List.map SourceByte.to_byte l).

(* The UTF-8 bytes of [c], which are its own bytes. *)
(* [Utf8 -> List SourceByte] *)
Definition to_source_bytes := fun (c : Utf8) .
  List.map SourceByte.from_byte (to_bytes c).

(* An [Ascii] character read as Latin-1, whose 256 codes are U+0000 to
 * U+00FF: a code below 128 takes one byte, 0xxxxxxx, and one from 128 two,
 * 1100001x 10xxxxxx.
 *)
(* [Ascii -> Utf8] *)
Definition from_ascii := fun (a : Ascii) .
  match a with
  | Ascii.introduction (Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0) =>
      Utf8.OneByte (Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0) I
  | Ascii.introduction (Byte.introduction 1 b6 b5 b4 b3 b2 b1 b0) =>
      Utf8.TwoBytes
        (Byte.introduction 1 1 0 0 0 0 1 b6)
        (Byte.introduction 1 0 b5 b4 b3 b2 b1 b0)
        I
  end.

(* [Some a] for U+0000 to U+00FF, the characters [from_ascii] gives, and
 * [None] from U+0100 on.
 *)
(* [Utf8 -> Option Ascii] *)
Definition to_ascii := fun (c : Utf8) .
  match c with
  | Utf8.OneByte x _ => Some (Ascii.introduction x)
  | Utf8.TwoBytes
      (Byte.introduction 1 1 0 0 0 0 1 b6)
      (Byte.introduction 1 0 b5 b4 b3 b2 b1 b0)
      _ =>
      Some (Ascii.introduction (Byte.introduction 1 b6 b5 b4 b3 b2 b1 b0))
  | _ => None
  end.

(* The code the bits of one to four UTF-8 bytes spell, their marker bits read
 * past: 0xxxxxxx gives xxxxxxx, 110xxxxx 10yyyyyy gives xxxxxyyyyyy, and so on
 * to four bytes; any other number of bytes gives 0.
 *)
(* [List Byte -> UInt32] *)
Definition decode := fun (l : List Byte) .
  match l with
  | Byte.introduction _ a6 a5 a4 a3 a2 a1 a0 :: [] =>
      UInt32.introduction
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 a6 a5 a4 a3 a2 a1 a0)
  | Byte.introduction _ _ _ a10 a9 a8 a7 a6
    :: Byte.introduction _ _ a5 a4 a3 a2 a1 a0
    :: [] =>
      UInt32.introduction
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 0 0 a10 a9 a8)
        (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0)
  | Byte.introduction _ _ _ _ a15 a14 a13 a12
    :: Byte.introduction _ _ a11 a10 a9 a8 a7 a6
    :: Byte.introduction _ _ a5 a4 a3 a2 a1 a0
    :: [] =>
      UInt32.introduction
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction a15 a14 a13 a12 a11 a10 a9 a8)
        (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0)
  | Byte.introduction _ _ _ _ _ a20 a19 a18
    :: Byte.introduction _ _ a17 a16 a15 a14 a13 a12
    :: Byte.introduction _ _ a11 a10 a9 a8 a7 a6
    :: Byte.introduction _ _ a5 a4 a3 a2 a1 a0
    :: [] =>
      UInt32.introduction
        (Byte.introduction 0 0 0 0 0 0 0 0)
        (Byte.introduction 0 0 0 a20 a19 a18 a17 a16)
        (Byte.introduction a15 a14 a13 a12 a11 a10 a9 a8)
        (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0)
  | _ => UInt32.Zero
  end.

(* The code point of [c], U+0000 to U+10FFFF: the bits its bytes spell. *)
(* [Utf8 -> UInt32] *)
Definition code := fun (c : Utf8) . decode (to_bytes c).

(* The UTF-8 bytes of a code, as few as its bits allow: one byte below 2^7,
 * two below 2^11, three below 2^16, four below 2^21, and none from 2^21 on.
 * No other rule of UTF-8 is applied, so a surrogate is written all the same.
 *)
(* [UInt32 -> List Byte] *)
Definition encode := fun (u : UInt32) .
  match u with
  | UInt32.introduction
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 a6 a5 a4 a3 a2 a1 a0) =>
      Byte.introduction 0 a6 a5 a4 a3 a2 a1 a0 :: []
  | UInt32.introduction
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 0 0 a10 a9 a8)
      (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0) =>
      Byte.introduction 1 1 0 a10 a9 a8 a7 a6
      :: Byte.introduction 1 0 a5 a4 a3 a2 a1 a0
      :: []
  | UInt32.introduction
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction a15 a14 a13 a12 a11 a10 a9 a8)
      (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0) =>
      Byte.introduction 1 1 1 0 a15 a14 a13 a12
      :: Byte.introduction 1 0 a11 a10 a9 a8 a7 a6
      :: Byte.introduction 1 0 a5 a4 a3 a2 a1 a0
      :: []
  | UInt32.introduction
      (Byte.introduction 0 0 0 0 0 0 0 0)
      (Byte.introduction 0 0 0 a20 a19 a18 a17 a16)
      (Byte.introduction a15 a14 a13 a12 a11 a10 a9 a8)
      (Byte.introduction a7 a6 a5 a4 a3 a2 a1 a0) =>
      Byte.introduction 1 1 1 1 0 a20 a19 a18
      :: Byte.introduction 1 0 a17 a16 a15 a14 a13 a12
      :: Byte.introduction 1 0 a11 a10 a9 a8 a7 a6
      :: Byte.introduction 1 0 a5 a4 a3 a2 a1 a0
      :: []
  | _ => []
  end.

(* [Some c] for the code of a character [c], and [None] for a surrogate,
 * U+D800 to U+DFFF, or a code past U+10FFFF, whose bytes from [encode] are
 * refused by [from_bytes].
 *)
(* [UInt32 -> Option Utf8] *)
Definition from_code := fun (u : UInt32) . from_bytes (encode u).

(* Characters are ordered by their codes. *)
(* [Utf8 -> Utf8 -> Prop] *)
Definition LessThan := fun (x : Utf8) (y : Utf8) . (code x < code y)%uint32.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_utf8_scope.

(* [Utf8 -> Utf8 -> Prop] *)
Definition LessOrEqual := fun (x : Utf8) (y : Utf8) . x = y \/ LessThan x y.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_utf8_scope.

Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_utf8_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_utf8_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_utf8_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_utf8_scope.

(* [Utf8 -> Utf8 -> Comparison] *)
Definition compare := fun (x : Utf8) (y : Utf8) . UInt32.compare (code x) (code y).

(* [Utf8 -> Utf8 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Utf8 -> Utf8 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Utf8 -> Utf8 -> Utf8] *)
Abbreviation min := (Comparable.min compare).

(* [Utf8 -> Utf8 -> Utf8] *)
Abbreviation max := (Comparable.max compare).

(* The digits [0] to [9], U+0030 to U+0039. *)
(* [Utf8 -> Bool] *)
Definition is_digit := fun (c : Utf8) .
  Bool.and (le (Utf8.OneByte 0x30%byte I) c) (le c (Utf8.OneByte 0x39%byte I)).

(* The upper case letters [A] to [Z], U+0041 to U+005A. *)
(* [Utf8 -> Bool] *)
Definition is_upper := fun (c : Utf8) .
  Bool.and (le (Utf8.OneByte 0x41%byte I) c) (le c (Utf8.OneByte 0x5a%byte I)).

(* The lower case letters [a] to [z], U+0061 to U+007A. *)
(* [Utf8 -> Bool] *)
Definition is_lower := fun (c : Utf8) .
  Bool.and (le (Utf8.OneByte 0x61%byte I) c) (le c (Utf8.OneByte 0x7a%byte I)).

(* The ASCII letters of either case; no other letter is one of them. *)
(* [Utf8 -> Bool] *)
Definition is_letter := fun (c : Utf8) . Bool.or (is_upper c) (is_lower c).

(* The space, U+0020, and the controls tab, line feed, vertical tab, form
 * feed and carriage return, U+0009 to U+000D.
 *)
(* [Utf8 -> Bool] *)
Definition is_whitespace := fun (c : Utf8) .
  Bool.or
    (eq c (Utf8.OneByte 0x20%byte I))
    (Bool.and (le (Utf8.OneByte 0x09%byte I) c) (le c (Utf8.OneByte 0x0d%byte I))).

(* A character up to U+00FF turned upper case by [Ascii.to_upper], which
 * changes the ASCII lower case letters alone; any other character unchanged.
 *)
(* [Utf8 -> Utf8] *)
Definition to_upper := fun (c : Utf8) .
  match to_ascii c with
  | None   => c
  | Some a => from_ascii (Ascii.to_upper a)
  end.

(* A character up to U+00FF turned lower case by [Ascii.to_lower], which
 * changes the ASCII upper case letters alone; any other character unchanged.
 *)
(* [Utf8 -> Utf8] *)
Definition to_lower := fun (c : Utf8) .
  match to_ascii c with
  | None   => c
  | Some a => from_ascii (Ascii.to_lower a)
  end.

Local Open Scope jwa_utf8_scope.

Module conversion. (* conversion *)

Module bytes. (* conversion.bytes *)

(* [from_bytes (to_bytes c) = Some c]: [to_bytes] is a section of
 * [from_bytes], so a character's bytes read back as that character.
 *)
(* conversion.bytes.section *)
Theorem section : forall (c : Utf8) . from_bytes (to_bytes c) = Some c.
Proof.
  intros c.
  match &c with
  | OneByte x p | TwoBytes x y p | ThreeBytes x y z p | FourBytes x y z w p
  end.
  - simpl to_bytes, from_bytes in |- *.
    ipso (Assert.guarding.evaluation (is_one_byte &x) (Utf8.OneByte &x) &p).
  - simpl to_bytes, from_bytes in |- *.
    ipso (Assert.guarding.evaluation (is_two_bytes &x &y) (Utf8.TwoBytes &x &y) &p).
  - simpl to_bytes, from_bytes in |- *.
    ipso (Assert.guarding.evaluation (is_three_bytes &x &y &z) (Utf8.ThreeBytes &x &y &z) &p).
  - simpl to_bytes, from_bytes in |- *.
    ipso
      (Assert.guarding.evaluation (is_four_bytes &x &y &z &w) (Utf8.FourBytes &x &y &z &w) &p).
Qed.

(* [from_bytes l = Some c] only for [l = to_bytes c]: the bytes a character
 * reads from are its own.
 *)
(* conversion.bytes.inversion *)
Theorem inversion
  : forall (l : List Byte) (c : Utf8) . from_bytes l = Some c -> to_bytes c = l.
Proof.
  intros l c h.
  match &l with | Nil | Cons x l1 end.
  - simpl from_bytes in &h.
    ex &h quodlibet.
  - match &l1 with | Nil | Cons y l2 end.
    + simpl from_bytes in &h.
      let proof k := Assert.guarding.inversion (is_one_byte &x) (Utf8.OneByte &x) &c &h.
      match &k with | p e end.
      leibniz <- &e in |- *.
      simpl to_bytes in |- *.
      quod idem est.
    + match &l2 with | Nil | Cons z l3 end.
      * simpl from_bytes in &h.
        let proof k := Assert.guarding.inversion (is_two_bytes &x &y) (Utf8.TwoBytes &x &y) &c &h.
        match &k with | p e end.
        leibniz <- &e in |- *.
        simpl to_bytes in |- *.
        quod idem est.
      * match &l3 with | Nil | Cons w l4 end.
        -- simpl from_bytes in &h.
           let proof k :=
             Assert.guarding.inversion
               (is_three_bytes &x &y &z) (Utf8.ThreeBytes &x &y &z) &c &h.
           match &k with | p e end.
           leibniz <- &e in |- *.
           simpl to_bytes in |- *.
           quod idem est.
        -- match &l4 with | Nil | Cons v l5 end.
           ++ simpl from_bytes in &h.
              let proof k :=
                Assert.guarding.inversion
                  (is_four_bytes &x &y &z &w) (Utf8.FourBytes &x &y &z &w) &c &h.
              match &k with | p e end.
              leibniz <- &e in |- *.
              simpl to_bytes in |- *.
              quod idem est.
           ++ simpl from_bytes in &h.
              ex &h quodlibet.
Qed.

(* conversion.bytes.injectivity *)
Theorem injectivity : forall {c : Utf8} {d : Utf8} . to_bytes c = to_bytes d -> c = d.
Proof.
  intros c d e.
  congru from_bytes, &e |- f.
  leibniz (conversion.bytes.section &c), (conversion.bytes.section &d) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bytes. (* conversion.bytes *)

Module source_bytes. (* conversion.source_bytes *)

(* [from_source_bytes (to_source_bytes c) = Some c]: [to_source_bytes] is a
 * section of [from_source_bytes], so every character prints as a literal
 * that reads back.
 *)
(* conversion.source_bytes.section *)
Theorem section : forall (c : Utf8) . from_source_bytes (to_source_bytes c) = Some c.
Proof.
  intros c.
  simpl from_source_bytes, to_source_bytes in |- *.
  leibniz (SourceByte.conversion.bytes.retraction (to_bytes &c)) in |- *.
  ipso (conversion.bytes.section &c).
Qed.

End source_bytes. (* conversion.source_bytes *)

Module ascii. (* conversion.ascii *)

(* [to_ascii (from_ascii a) = Some a]: [to_ascii] is a retraction of
 * [from_ascii], so every [Ascii] character comes back from its [Utf8] form.
 *)
(* conversion.ascii.retraction *)
Theorem retraction : forall (a : Ascii) . to_ascii (from_ascii a) = Some a.
Proof.
  intros a.
  match &a with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end.
  - simpl from_ascii, to_ascii in |- *.
    quod idem est.
  - simpl from_ascii, to_ascii in |- *.
    quod idem est.
Qed.

(* [to_ascii c = Some a] only for [c = from_ascii a]: the [Utf8] characters
 * that read as [Ascii] are those [from_ascii] gives.
 *)
(* conversion.ascii.inversion *)
Theorem inversion
  : forall (c : Utf8) (a : Ascii) . to_ascii c = Some a -> from_ascii a = c.
Proof.
  intros c a h.
  (* Both sides are [None] where [to_ascii] answers [None], so one chain of
   * steps closes every case of the bits [to_ascii] and the proof in [c] read.
   *)
  lemma agreement
    : Option.map from_ascii (to_ascii &c) = Option.map (fun (_ : Ascii) . &c) (to_ascii &c).
  {
    match &c with
    | OneByte x p | TwoBytes x y p | ThreeBytes x y z p | FourBytes x y z w p
    end.
    - match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end;
        simpl in &p;
        match &p with end;
        simpl in |- *;
        quod idem est.
    - match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &y with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
      match &b7 with | Zero | One end;
        match &b6 with | Zero | One end;
        match &b5 with | Zero | One end;
        match &b4 with | Zero | One end;
        match &b3 with | Zero | One end;
        match &b2 with | Zero | One end;
        match &b1 with | Zero | One end;
        match &b0 with | Zero | One end;
        match &y7 with | Zero | One end;
        match &y6 with | Zero | One end;
        simpl in &p;
        match &p with end;
        simpl in |- *;
        quod idem est.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      quod idem est.
  }
  leibniz &h in &agreement.
  simpl in &agreement.
  ipso (Option.some.injectivity &agreement).
Qed.

Module classification. (* conversion.ascii.classification *)

(* The [Utf8] form of an [Ascii] character is upper case exactly when the
 * character is.
 *)
(* conversion.ascii.classification.upper *)
Theorem upper : forall (a : Ascii) . is_upper (from_ascii a) = Ascii.is_upper a.
Proof.
  intros a.
  match &a with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl is_upper, Ascii.is_upper, Comparable.le in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* The [Utf8] form of an [Ascii] character is lower case exactly when the
 * character is.
 *)
(* conversion.ascii.classification.lower *)
Theorem lower : forall (a : Ascii) . is_lower (from_ascii a) = Ascii.is_lower a.
Proof.
  intros a.
  match &a with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl is_lower, Ascii.is_lower, Comparable.le in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End classification. (* conversion.ascii.classification *)

(* conversion.ascii.uppercasing *)
Theorem uppercasing
  : forall (a : Ascii) . to_upper (from_ascii a) = from_ascii (Ascii.to_upper a).
Proof.
  intros a.
  simpl to_upper in |- *.
  leibniz (conversion.ascii.retraction &a) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.ascii.lowercasing *)
Theorem lowercasing
  : forall (a : Ascii) . to_lower (from_ascii a) = from_ascii (Ascii.to_lower a).
Proof.
  intros a.
  simpl to_lower in |- *.
  leibniz (conversion.ascii.retraction &a) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End ascii. (* conversion.ascii *)

Module code. (* conversion.code *)

(* [encode (code c) = to_bytes c]: a character's code is written back as its
 * own bytes, UTF-8 spelling each code one way. Each bit a ctor's proof fixes
 * is settled first, the case its proof refutes closed at once, so that only
 * the bits left free are split together.
 *)
(* conversion.code.encoding *)
Theorem encoding : forall (c : Utf8) . encode (code c) = to_bytes c.
Proof.
  intros c.
  simpl code in |- *.
  match &c with
  | OneByte x p | TwoBytes x y p | ThreeBytes x y z p | FourBytes x y z w p
  end.
  - match &x with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &x7 with | Zero | One end.
    2: simpl in &p; match &p with end.
    simpl in |- *.
    quod idem est.
  - match &x with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &y with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
    match &x7 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x6 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x5 with | Zero | One end.
    2: simpl in &p; match &p with end.
    match &x4 with | Zero | One end;
      match &x3 with | Zero | One end;
      match &x2 with | Zero | One end;
      match &x1 with | Zero | One end;
      match &y7 with | Zero | One end;
      match &y6 with | Zero | One end;
      simpl in &p;
      match &p with end;
      simpl in |- *;
      quod idem est.
  - match &x with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &y with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
    match &z with | introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
    match &x7 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x6 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x5 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x4 with | Zero | One end.
    2: simpl in &p; match &p with end.
    match &x3 with | Zero | One end;
      match &x2 with | Zero | One end;
      match &x1 with | Zero | One end;
      match &x0 with | Zero | One end;
      match &y7 with | Zero | One end;
      match &y6 with | Zero | One end;
      match &y5 with | Zero | One end;
      match &z7 with | Zero | One end;
      match &z6 with | Zero | One end;
      simpl in &p;
      match &p with end;
      simpl in |- *;
      quod idem est.
  - match &x with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &y with | introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
    match &z with | introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
    match &w with | introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
    match &x7 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x6 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x5 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x4 with | Zero | One end.
    1: simpl in &p; match &p with end.
    match &x3 with | Zero | One end.
    2: simpl in &p; match &p with end.
    match &x2 with | Zero | One end;
      match &x1 with | Zero | One end;
      match &x0 with | Zero | One end;
      match &y7 with | Zero | One end;
      match &y6 with | Zero | One end;
      match &y5 with | Zero | One end;
      match &y4 with | Zero | One end;
      match &z7 with | Zero | One end;
      match &z6 with | Zero | One end;
      match &w7 with | Zero | One end;
      match &w6 with | Zero | One end;
      simpl in &p;
      match &p with end;
      simpl in |- *;
      quod idem est.
Qed.

(* [decode (encode u) = u] whenever [encode] writes any byte: a code below
 * 2^21 is read back from its bytes. The bits of [u] are split from the most
 * significant down, and each case [encode] has already decided is closed at
 * once, the code read back or no byte written.
 *)
(* conversion.code.decoding *)
Theorem decoding : forall (u : UInt32) . ~ (encode u = []) -> decode (encode u) = u.
Proof.
  intros u n.
  lemma all
    : match encode &u with
      | [] => &u
      | _ :: _ => decode (encode &u)
      end = &u.
  {
    match &u with | introduction b3 b2 b1 b0 end.
    match &b3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
    match &b2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
    match &b1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
    match &b0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    match &x31 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x30 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x29 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x28 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x27 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x26 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x25 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x24 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x23 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x22 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x21 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x20 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x19 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x18 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x17 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x16 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x15 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x14 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x13 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x12 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x11 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x10 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x9 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x8 with | Zero | One end.
    2: simpl in |- *; quod idem est.
    match &x7 with | Zero | One end;
      simpl in |- *;
      quod idem est.
  }
  match (encode &u) with | | v l end.
  - ex (&n (Identity.reflexivity [])) quodlibet.
  - simpl in &all.
    ipso &all.
Qed.

(* [from_code (code c) = Some c]: [code] is a section of [from_code], so
 * every character comes back from its code.
 *)
(* conversion.code.section *)
Theorem section : forall (c : Utf8) . from_code (code c) = Some c.
Proof.
  intros c.
  simpl from_code in |- *.
  leibniz (conversion.code.encoding &c) in |- *.
  ipso (conversion.bytes.section &c).
Qed.

(* [from_code u = Some c] only for [u = code c]: the character a code reads
 * as has that code.
 *)
(* conversion.code.inversion *)
Theorem inversion
  : forall (u : UInt32) (c : Utf8) . from_code u = Some c -> code c = u.
Proof.
  intros u c h.
  simpl from_code in &h.
  let proof b := conversion.bytes.inversion (encode &u) &c &h.
  lemma n : ~ (encode &u = []).
  {
    intro e.
    leibniz &e in &h.
    simpl in &h.
    ex &h quodlibet.
  }
  simpl code in |- *.
  leibniz &b in |- *.
  ipso (conversion.code.decoding &u &n).
Qed.

(* conversion.code.injectivity *)
Theorem injectivity : forall {c : Utf8} {d : Utf8} . code c = code d -> c = d.
Proof.
  intros c d e.
  congru from_code, &e |- f.
  leibniz (conversion.code.section &c), (conversion.code.section &d) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End code. (* conversion.code *)

End conversion. (* conversion *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall {x : Utf8} {y : Utf8} {z : Utf8} . x < y -> y < z -> x < z.
Proof.
  intros x y z h1 h2.
  simpl LessThan in &h1, &h2 |- *.
  ipso (UInt32.order.strict.transitivity &h1 &h2).
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : Utf8) (y : Utf8) .
      (compare x y = Comparison.Lt <-> x < y) /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.
  simpl compare, LessThan in |- *.
  let proof s := UInt32.comparison.specification (code &x) (code &y).
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
  : forall (x : Utf8) (y : Utf8) . compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  simpl compare in |- *.
  ipso (UInt32.comparison.antisymmetry (code &x) (code &y)).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity := @order.strict.transitivity
  ; Comparable.specification := comparison.specification
  ; Comparable.antisymmetry := comparison.antisymmetry |}.

Module classification. (* classification *)

Module range. (* classification.range *)

(* The two comparisons a class makes, read as the two orders they decide. *)
(* classification.range.specification *)
Lemma specification
  : forall (low : Utf8) (high : Utf8) (c : Utf8) .
      Bool.and (le low c) (le c high) = true <-> low <= c /\ c <= high.
Proof.
  intros low high c.
  let proof h := Comparable.order.reflection (compare := compare) (lt := LessThan) &c &high.
  simpl Bool.and in |- *.
  match (le &low &c) with | | end |- el.
  - let proof l := Comparable.order.reflection (compare := compare) (lt := LessThan) &low &c.
    divide et impera.
    + intro e.
      divide et impera.
      * ipso (modus aequans &l, &el).
      * ipso (modus aequans &h, &e).
    + intro p.
      match &p with | _ q end.
      ipso (modus aequans &h, &q).
  - let proof l := Comparable.order.reflection (compare := compare) (lt := LessThan) &low &c.
    divide et impera.
    + intro e.
      ex e quodlibet.
    + intro p.
      match &p with | q _ end.
      let proof t := modus aequans &l, &q.
      leibniz &el in &t.
      ex t quodlibet.
Qed.

End range. (* classification.range *)

Module digit. (* classification.digit *)

(* classification.digit.specification *)
Theorem specification
  : forall (c : Utf8) .
      is_digit c = true <-> Utf8.OneByte 0x30%byte I <= c /\ c <= Utf8.OneByte 0x39%byte I.
Proof.
  intros c.
  simpl is_digit in |- *.
  ipso
    (classification.range.specification
      (Utf8.OneByte 0x30%byte I) (Utf8.OneByte 0x39%byte I) &c).
Qed.

End digit. (* classification.digit *)

Module upper. (* classification.upper *)

(* classification.upper.specification *)
Theorem specification
  : forall (c : Utf8) .
      is_upper c = true <-> Utf8.OneByte 0x41%byte I <= c /\ c <= Utf8.OneByte 0x5a%byte I.
Proof.
  intros c.
  simpl is_upper in |- *.
  ipso
    (classification.range.specification
      (Utf8.OneByte 0x41%byte I) (Utf8.OneByte 0x5a%byte I) &c).
Qed.

End upper. (* classification.upper *)

Module lower. (* classification.lower *)

(* classification.lower.specification *)
Theorem specification
  : forall (c : Utf8) .
      is_lower c = true <-> Utf8.OneByte 0x61%byte I <= c /\ c <= Utf8.OneByte 0x7a%byte I.
Proof.
  intros c.
  simpl is_lower in |- *.
  ipso
    (classification.range.specification
      (Utf8.OneByte 0x61%byte I) (Utf8.OneByte 0x7a%byte I) &c).
Qed.

End lower. (* classification.lower *)

Module letter. (* classification.letter *)

(* classification.letter.specification *)
Theorem specification
  : forall (c : Utf8) . is_letter c = true <-> is_upper c = true \/ is_lower c = true.
Proof.
  intros c.
  simpl is_letter in |- *.
  simpl Bool.or in |- *.
  match (is_upper &c) with | | end.
  - divide et impera.
    + intro e.
      ipso (disjoin e, _).
    + intro d.
      quod idem est.
  - divide et impera.
    + intro e.
      ipso (disjoin _, e).
    + intro d.
      match &d with | e | e end.
      * ex e quodlibet.
      * ipso &e.
Qed.

End letter. (* classification.letter *)

Module whitespace. (* classification.whitespace *)

(* classification.whitespace.specification *)
Theorem specification
  : forall (c : Utf8) .
      is_whitespace c = true
      <-> c = Utf8.OneByte 0x20%byte I
        \/ (Utf8.OneByte 0x09%byte I <= c /\ c <= Utf8.OneByte 0x0d%byte I).
Proof.
  intros c.
  let proof r :=
    classification.range.specification
      (Utf8.OneByte 0x09%byte I) (Utf8.OneByte 0x0d%byte I) &c.
  simpl is_whitespace in |- *.
  simpl Bool.or in |- *.
  match (eq &c (Utf8.OneByte 0x20%byte I)) with | | end |- e.
  - let proof s :=
      Comparable.comparison.equality.reflection
        (compare := compare) (lt := LessThan) &c (Utf8.OneByte 0x20%byte I).
    divide et impera.
    + intro t.
      ipso (disjoin (modus aequans &s, &e), _).
    + intro d.
      quod idem est.
  - let proof s :=
      Comparable.comparison.equality.reflection
        (compare := compare) (lt := LessThan) &c (Utf8.OneByte 0x20%byte I).
    divide et impera.
    + intro t.
      ipso (disjoin _, (modus aequans &r, &t)).
    + intro d.
      match &d with | q | q end.
      * let proof t := modus aequans &s, &q.
        leibniz &e in &t.
        ex t quodlibet.
      * ipso (modus aequans &r, &q).
Qed.

End whitespace. (* classification.whitespace *)

(* No character is both upper and lower case: one that were would lie
 * between [a] and [Z], and [Z] comes before [a].
 *)
(* classification.exclusion *)
Theorem exclusion : forall (c : Utf8) . Bool.and (is_upper c) (is_lower c) = false.
Proof.
  intros c.
  match (is_upper &c) with | | end |- u.
  - match (is_lower &c) with | | end |- l.
    + let proof s := modus aequans (classification.upper.specification &c), &u.
      let proof t := modus aequans (classification.lower.specification &c), &l.
      match &s with | _ high end.
      match &t with | low _ end.
      let proof b :=
        Comparable.order.transitivity
          (compare := compare) (lt := LessThan)
          (Utf8.OneByte 0x61%byte I) &c (Utf8.OneByte 0x5a%byte I) &low &high.
      let proof r :=
        Comparable.order.reflection
          (compare := compare) (lt := LessThan)
          (Utf8.OneByte 0x61%byte I) (Utf8.OneByte 0x5a%byte I).
      let proof f := modus aequans &r, &b.
      simpl Comparable.le in &f.
      simpl in &f.
      ex &f quodlibet.
    + simpl in |- *.
      quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

End classification. (* classification *)

Module uppercasing. (* uppercasing *)

(* uppercasing.invariance *)
Theorem invariance : forall (c : Utf8) . is_lower c = false -> to_upper c = c.
Proof.
  intros c h.
  match (to_ascii &c) with | | a end |- e.
  - simpl to_upper in |- *.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in &h |- *.
    leibniz (conversion.ascii.classification.lower &a) in &h.
    leibniz (conversion.ascii.uppercasing &a), (Ascii.uppercasing.invariance &a &h) in |- *.
    quod idem est.
Qed.

(* uppercasing.idempotence *)
Theorem idempotence : forall (c : Utf8) . to_upper (to_upper c) = to_upper c.
Proof.
  intros c.
  match (to_ascii &c) with | | a end |- e.
  - lemma u : to_upper &c = &c.
    {
      simpl to_upper in |- *.
      leibniz &e in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &u, &u in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in |- *.
    leibniz
      (conversion.ascii.uppercasing &a),
      (conversion.ascii.uppercasing (Ascii.to_upper &a)),
      (Ascii.uppercasing.idempotence &a)
      in |- *.
    quod idem est.
Qed.

(* Turning a character lower case first changes nothing [to_upper] makes of it. *)
(* uppercasing.absorption *)
Theorem absorption : forall (c : Utf8) . to_upper (to_lower c) = to_upper c.
Proof.
  intros c.
  match (to_ascii &c) with | | a end |- e.
  - lemma l : to_lower &c = &c.
    {
      simpl to_lower in |- *.
      leibniz &e in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &l in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in |- *.
    leibniz
      (conversion.ascii.lowercasing &a),
      (conversion.ascii.uppercasing (Ascii.to_lower &a)),
      (conversion.ascii.uppercasing &a),
      (Ascii.uppercasing.absorption &a)
      in |- *.
    quod idem est.
Qed.

Module inversion. (* uppercasing.inversion *)

(* uppercasing.inversion.lowercasing *)
Theorem lowercasing : forall (c : Utf8) . is_upper c = true -> to_upper (to_lower c) = c.
Proof.
  intros c h.
  let proof x := classification.exclusion &c.
  leibniz &h in &x.
  match (Bool.conjunction.identity (is_lower &c)) with | l _ end.
  leibniz &l in &x.
  leibniz (uppercasing.absorption &c) in |- *.
  ipso (uppercasing.invariance &c &x).
Qed.

End inversion. (* uppercasing.inversion *)

End uppercasing. (* uppercasing *)

Module lowercasing. (* lowercasing *)

(* lowercasing.invariance *)
Theorem invariance : forall (c : Utf8) . is_upper c = false -> to_lower c = c.
Proof.
  intros c h.
  match (to_ascii &c) with | | a end |- e.
  - simpl to_lower in |- *.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in &h |- *.
    leibniz (conversion.ascii.classification.upper &a) in &h.
    leibniz (conversion.ascii.lowercasing &a), (Ascii.lowercasing.invariance &a &h) in |- *.
    quod idem est.
Qed.

(* lowercasing.idempotence *)
Theorem idempotence : forall (c : Utf8) . to_lower (to_lower c) = to_lower c.
Proof.
  intros c.
  match (to_ascii &c) with | | a end |- e.
  - lemma l : to_lower &c = &c.
    {
      simpl to_lower in |- *.
      leibniz &e in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &l, &l in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in |- *.
    leibniz
      (conversion.ascii.lowercasing &a),
      (conversion.ascii.lowercasing (Ascii.to_lower &a)),
      (Ascii.lowercasing.idempotence &a)
      in |- *.
    quod idem est.
Qed.

(* Turning a character upper case first changes nothing [to_lower] makes of it. *)
(* lowercasing.absorption *)
Theorem absorption : forall (c : Utf8) . to_lower (to_upper c) = to_lower c.
Proof.
  intros c.
  match (to_ascii &c) with | | a end |- e.
  - lemma u : to_upper &c = &c.
    {
      simpl to_upper in |- *.
      leibniz &e in |- *.
      simpl in |- *.
      quod idem est.
    }
    leibniz &u in |- *.
    quod idem est.
  - let proof i := conversion.ascii.inversion &c &a &e.
    leibniz <- &i in |- *.
    leibniz
      (conversion.ascii.uppercasing &a),
      (conversion.ascii.lowercasing (Ascii.to_upper &a)),
      (conversion.ascii.lowercasing &a),
      (Ascii.lowercasing.absorption &a)
      in |- *.
    quod idem est.
Qed.

Module inversion. (* lowercasing.inversion *)

(* lowercasing.inversion.uppercasing *)
Theorem uppercasing : forall (c : Utf8) . is_lower c = true -> to_lower (to_upper c) = c.
Proof.
  intros c h.
  let proof x := classification.exclusion &c.
  leibniz &h in &x.
  match (Bool.conjunction.identity (is_upper &c)) with | _ r end.
  leibniz &r in &x.
  leibniz (lowercasing.absorption &c) in |- *.
  ipso (lowercasing.invariance &c &x).
Qed.

End inversion. (* lowercasing.inversion *)

End lowercasing. (* lowercasing *)

End Utf8. (* Utf8 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Utf8], not [Utf8.T].
 *)
Abbreviation Utf8 := Utf8.T.

(* Makes the notations declared in [Module Utf8] usable in every file that
 * imports this one, as [(x < y)%u8c] or under an opened [jwa_utf8_scope].
 *)
Export (notations) Utf8.

(* A character is written as a string of one character under its key,
 * ["A"%u8c], and a closed one prints back so.
 *)
String Notation Utf8.T Utf8.from_source_bytes Utf8.to_source_bytes
  : jwa_utf8_scope.

(* Where a [Utf8] is expected, a literal reads in this scope without its
 * [%u8c].
 *)
Bind Scope jwa_utf8_scope with Utf8.T.

(* Declared inside [Module Utf8], whose proofs use it; an instance declared
 * there is dropped at the module's [End], so it is announced again here.
 *)
Existing Instance Utf8.comparable.
