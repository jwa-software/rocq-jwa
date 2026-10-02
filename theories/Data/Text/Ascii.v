(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
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
      | Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0 =>
          Some (Ascii.introduction (Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0))
      | _ => None
      end
  | s1 :: s2 :: [] =>
      match SourceByte.to_byte s1, SourceByte.to_byte s2 with
      | Byte.introduction 1 1 0  0  0  0  1  b6,
        Byte.introduction 1 0 b5 b4 b3 b2 b1 b0 =>
          Some (Ascii.introduction (Byte.introduction 1 b6 b5 b4 b3 b2 b1 b0))
      | _, _ => None
      end
  | _ => None
  end.

(* The UTF-8 bytes of [c], as the table above [from_source_bytes] lays them out. *)
(* [Ascii -> List SourceByte] *)
Definition to_source_bytes := fun (c : Ascii) .
  match c with
  | Ascii.introduction (Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte (Byte.introduction 0 b6 b5 b4 b3 b2 b1 b0) :: []
  | Ascii.introduction (Byte.introduction 1 b6 b5 b4 b3 b2 b1 b0) =>
      SourceByte.from_byte
        (Byte.introduction 1 1 0 0 0 0 1 b6)
      :: SourceByte.from_byte (Byte.introduction 1 0 b5 b4 b3 b2 b1 b0)
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

(* The digits [0] to [9], codes 0x30 to 0x39. *)
(* [Ascii -> Bool] *)
Definition is_digit := fun (c : Ascii) .
  Bool.and (le (from_byte 0x30%byte) c) (le c (from_byte 0x39%byte)).

(* The upper case letters [A] to [Z], codes 0x41 to 0x5a. *)
(* [Ascii -> Bool] *)
Definition is_upper := fun (c : Ascii) .
  Bool.and (le (from_byte 0x41%byte) c) (le c (from_byte 0x5a%byte)).

(* The lower case letters [a] to [z], codes 0x61 to 0x7a. *)
(* [Ascii -> Bool] *)
Definition is_lower := fun (c : Ascii) .
  Bool.and (le (from_byte 0x61%byte) c) (le c (from_byte 0x7a%byte)).

(* The ASCII letters of either case; a Latin-1 letter is none of them. *)
(* [Ascii -> Bool] *)
Definition is_letter := fun (c : Ascii) . Bool.or (is_upper c) (is_lower c).

(* The space, code 0x20, and the controls tab, line feed, vertical tab, form
 * feed and carriage return, codes 0x09 to 0x0d.
 *)
(* [Ascii -> Bool] *)
Definition is_whitespace := fun (c : Ascii) .
  Bool.or
    (eq c (from_byte 0x20%byte))
    (Bool.and (le (from_byte 0x09%byte) c) (le c (from_byte 0x0d%byte))).

(* A lower case letter turned upper case by clearing the bit 0x20 that tells
 * the two cases apart; any other character unchanged.
 *)
(* [Ascii -> Ascii] *)
Definition to_upper := fun (c : Ascii) .
  match is_lower c with
  | true  => from_byte (Byte.and (to_byte c) 0xdf%byte)
  | false => c
  end.

(* An upper case letter turned lower case by setting the bit 0x20; any other
 * character unchanged.
 *)
(* [Ascii -> Ascii] *)
Definition to_lower := fun (c : Ascii) .
  match is_upper c with
  | true  => from_byte (Byte.or (to_byte c) 0x20%byte)
  | false => c
  end.

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
        (Byte.introduction 0 &b6 &b5 &b4 &b3 &b2 &b1 &b0))
      in |- *.
    simpl in |- *.
    quod idem est.
  - simpl to_source_bytes, from_source_bytes in |- *.
    leibniz
      (SourceByte.conversion.byte.retraction
        (Byte.introduction 1 1 0 0 0 0 1 &b6)),
      (SourceByte.conversion.byte.retraction
        (Byte.introduction 1 0 &b5 &b4 &b3 &b2 &b1 &b0))
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

Module classification. (* classification *)

Module range. (* classification.range *)

(* The two comparisons a class makes, read as the two orders they decide. *)
(* classification.range.specification *)
Lemma specification
  : forall (low : Ascii) (high : Ascii) (c : Ascii) .
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
  : forall (c : Ascii) .
      is_digit c = true <-> from_byte 0x30%byte <= c /\ c <= from_byte 0x39%byte.
Proof.
  intros c.
  simpl is_digit in |- *.
  ipso (classification.range.specification (from_byte 0x30%byte) (from_byte 0x39%byte) &c).
Qed.

End digit. (* classification.digit *)

Module upper. (* classification.upper *)

(* classification.upper.specification *)
Theorem specification
  : forall (c : Ascii) .
      is_upper c = true <-> from_byte 0x41%byte <= c /\ c <= from_byte 0x5a%byte.
Proof.
  intros c.
  simpl is_upper in |- *.
  ipso (classification.range.specification (from_byte 0x41%byte) (from_byte 0x5a%byte) &c).
Qed.

End upper. (* classification.upper *)

Module lower. (* classification.lower *)

(* classification.lower.specification *)
Theorem specification
  : forall (c : Ascii) .
      is_lower c = true <-> from_byte 0x61%byte <= c /\ c <= from_byte 0x7a%byte.
Proof.
  intros c.
  simpl is_lower in |- *.
  ipso (classification.range.specification (from_byte 0x61%byte) (from_byte 0x7a%byte) &c).
Qed.

End lower. (* classification.lower *)

Module letter. (* classification.letter *)

(* classification.letter.specification *)
Theorem specification
  : forall (c : Ascii) . is_letter c = true <-> is_upper c = true \/ is_lower c = true.
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
  : forall (c : Ascii) .
      is_whitespace c = true
      <-> c = from_byte 0x20%byte \/ (from_byte 0x09%byte <= c /\ c <= from_byte 0x0d%byte).
Proof.
  intros c.
  let proof r :=
    classification.range.specification (from_byte 0x09%byte) (from_byte 0x0d%byte) &c.
  simpl is_whitespace in |- *.
  simpl Bool.or in |- *.
  match (eq &c (from_byte 0x20%byte)) with | | end |- e.
  - let proof s :=
      Comparable.comparison.equality.reflection
        (compare := compare) (lt := LessThan) &c (from_byte 0x20%byte).
    divide et impera.
    + intro t.
      ipso (disjoin (modus aequans &s, &e), _).
    + intro d.
      quod idem est.
  - let proof s :=
      Comparable.comparison.equality.reflection
        (compare := compare) (lt := LessThan) &c (from_byte 0x20%byte).
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

(* No character is both upper and lower case. *)
(* classification.exclusion *)
Theorem exclusion : forall (c : Ascii) . Bool.and (is_upper c) (is_lower c) = false.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl is_upper, is_lower in |- *;
    simpl in |- *;
    quod idem est.
Qed.

End classification. (* classification *)

Module uppercasing. (* uppercasing *)

(* uppercasing.invariance *)
Theorem invariance : forall (c : Ascii) . is_lower c = false -> to_upper c = c.
Proof.
  intros c h.
  simpl to_upper in |- *.
  leibniz &h in |- *.
  simpl in |- *.
  quod idem est.
Qed.

(* uppercasing.idempotence *)
Theorem idempotence : forall (c : Ascii) . to_upper (to_upper c) = to_upper c.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl to_upper, is_lower, from_byte in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* Turning a character lower case first changes nothing [to_upper] makes of it. *)
(* uppercasing.absorption *)
Theorem absorption : forall (c : Ascii) . to_upper (to_lower c) = to_upper c.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl to_upper, to_lower, is_lower, is_upper, from_byte in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module inversion. (* uppercasing.inversion *)

(* uppercasing.inversion.lowercasing *)
Theorem lowercasing : forall (c : Ascii) . is_upper c = true -> to_upper (to_lower c) = c.
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
Theorem invariance : forall (c : Ascii) . is_upper c = false -> to_lower c = c.
Proof.
  intros c h.
  simpl to_lower in |- *.
  leibniz &h in |- *.
  simpl in |- *.
  quod idem est.
Qed.

(* lowercasing.idempotence *)
Theorem idempotence : forall (c : Ascii) . to_lower (to_lower c) = to_lower c.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl to_lower, is_upper, from_byte in |- *;
    simpl in |- *;
    quod idem est.
Qed.

(* Turning a character upper case first changes nothing [to_lower] makes of it. *)
(* lowercasing.absorption *)
Theorem absorption : forall (c : Ascii) . to_lower (to_upper c) = to_lower c.
Proof.
  intros c.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl to_lower, to_upper, is_upper, is_lower, from_byte in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module inversion. (* lowercasing.inversion *)

(* lowercasing.inversion.uppercasing *)
Theorem uppercasing : forall (c : Ascii) . is_lower c = true -> to_lower (to_upper c) = c.
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
