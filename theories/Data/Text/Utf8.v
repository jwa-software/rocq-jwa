(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Assert.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Literal.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.Ascii.
From jwa Require Import Data.Text.SourceByte.
From jwa Require Import Tactics.Equation.

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
  | Byte.introduction Bit.One Bit.Zero _ _ _ _ _ _ => true
  | _ => false
  end.

(* A character of one byte:
 *
 *   0xxxxxxx
 *)
(* [Byte -> Bool] *)
Definition is_one_byte := fun (x : Byte) .
  match x with
  | Byte.introduction Bit.Zero _ _ _ _ _ _ _ => true
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
  | Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero _ => false
  | Byte.introduction Bit.One Bit.One Bit.Zero _ _ _ _ _ => is_tail y
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
  | Byte.introduction Bit.One Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero =>
      match y with
      | Byte.introduction Bit.One Bit.Zero Bit.One _ _ _ _ _ => is_tail z
      | _ => false
      end
  | Byte.introduction Bit.One Bit.One Bit.One Bit.Zero Bit.One Bit.One Bit.Zero Bit.One =>
      match y with
      | Byte.introduction Bit.One Bit.Zero Bit.Zero _ _ _ _ _ => is_tail z
      | _ => false
      end
  | Byte.introduction Bit.One Bit.One Bit.One Bit.Zero _ _ _ _ =>
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
  | Byte.introduction Bit.One Bit.One Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero =>
      match y with
      | Byte.introduction Bit.One Bit.Zero Bit.Zero Bit.Zero _ _ _ _ => false
      | Byte.introduction Bit.One Bit.Zero _ _ _ _ _ _ => Bool.and (is_tail z) (is_tail w)
      | _ => false
      end
  | Byte.introduction Bit.One Bit.One Bit.One Bit.One Bit.Zero Bit.One Bit.Zero Bit.Zero =>
      match y with
      | Byte.introduction Bit.One Bit.Zero Bit.Zero Bit.Zero _ _ _ _ =>
          Bool.and (is_tail z) (is_tail w)
      | _ => false
      end
  | Byte.introduction Bit.One Bit.One Bit.One Bit.One Bit.Zero Bit.Zero _ _ =>
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
  | Ascii.introduction (Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) =>
      Utf8.OneByte (Byte.introduction Bit.Zero b6 b5 b4 b3 b2 b1 b0) I
  | Ascii.introduction (Byte.introduction Bit.One b6 b5 b4 b3 b2 b1 b0) =>
      Utf8.TwoBytes
        (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6)
        (Byte.introduction Bit.One Bit.Zero b5 b4 b3 b2 b1 b0)
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
      (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One b6)
      (Byte.introduction Bit.One Bit.Zero b5 b4 b3 b2 b1 b0)
      _ =>
      Some (Ascii.introduction (Byte.introduction Bit.One b6 b5 b4 b3 b2 b1 b0))
  | _ => None
  end.

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

End ascii. (* conversion.ascii *)

End conversion. (* conversion *)

End Utf8. (* Utf8 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Utf8], not [Utf8.T].
 *)
Abbreviation Utf8 := Utf8.T.

(* A character is written as a string of one character under its key,
 * ["A"%u8c], and a closed one prints back so.
 *)
String Notation Utf8.T Utf8.from_source_bytes Utf8.to_source_bytes
  : jwa_utf8_scope.

(* Where a [Utf8] is expected, a literal reads in this scope without its
 * [%u8c].
 *)
Bind Scope jwa_utf8_scope with Utf8.T.
