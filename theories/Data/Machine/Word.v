(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Machine.Endian.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Number.Numeral.
From jwa Require Import Data.Option.

Module Word. (* Word *)

Inductive T : Type :=
  | introduction : Endian -> Byte -> Byte -> Byte -> Byte -> T.

Abbreviation Word := T.

(* [Word -> Endian] *)
Definition endian := fun (x : Word) .
  match x with
  | Word.introduction e _ _ _ _ => e
  end.

(* The least significant byte, wherever the endianness lays it; [byte1] to
 * [byte3] follow in significance.
 *)
(* [Word -> Byte] *)
Definition byte0 := fun (x : Word) .
  match x with
  | Word.introduction Endian.Little b0 _  _  _  => b0
  | Word.introduction Endian.Big    _  _  _  b0 => b0
  end.

(* [Word -> Byte] *)
Definition byte1 := fun (x : Word) .
  match x with
  | Word.introduction Endian.Little _  b1 _  _  => b1
  | Word.introduction Endian.Big    _  _  b1 _  => b1
  end.

(* [Word -> Byte] *)
Definition byte2 := fun (x : Word) .
  match x with
  | Word.introduction Endian.Little _  _  b2 _  => b2
  | Word.introduction Endian.Big    _  b2 _  _  => b2
  end.

(* [Word -> Byte] *)
Definition byte3 := fun (x : Word) .
  match x with
  | Word.introduction Endian.Little _  _  _  b3 => b3
  | Word.introduction Endian.Big    b3 _  _  _  => b3
  end.

(* The word of endianness [e] whose bytes, least significant first, are
 * [b0] to [b3], laid out in the order [e] names.
 *)
(* [Endian -> Byte -> Byte -> Byte -> Byte -> Word] *)
Definition make := fun (e : Endian) (b0 : Byte) (b1 : Byte) (b2 : Byte) (b3 : Byte) .
  match e with
  | Endian.Little => Word.introduction Endian.Little b0 b1 b2 b3
  | Endian.Big    => Word.introduction Endian.Big    b3 b2 b1 b0
  end.

(* The same value, laid out in the order [e] names. *)
(* [Endian -> Word -> Word] *)
Definition with_endian := fun (e : Endian) (x : Word) .
  make e (byte0 x) (byte1 x) (byte2 x) (byte3 x).

(* [Endian -> Word] *)
Definition Zero := fun (e : Endian) . make e Byte.Zero Byte.Zero Byte.Zero Byte.Zero.

(* [Word -> Word] *)
Definition flip := fun (x : Word) .
  make (endian x)
    (Byte.flip (byte0 x)) (Byte.flip (byte1 x)) (Byte.flip (byte2 x)) (Byte.flip (byte3 x)).

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_word_scope.

(* [x] converted to little-endian, then flipped. *)
(* [Word -> Word] *)
Definition flip_little_endian := fun (x : Word) . flip (with_endian Endian.Little x).

(* [x] converted to big-endian, then flipped. *)
(* [Word -> Word] *)
Definition flip_big_endian := fun (x : Word) . flip (with_endian Endian.Big x).

(* [y] converted to the endianness of [x], then combined with it byte by
 * byte: the result takes the endianness of [x].
 *)
(* [Word -> Word -> Word] *)
Definition and := fun (x : Word) (y : Word) .
  make (endian x)
    (Byte.and (byte0 x) (byte0 y)) (Byte.and (byte1 x) (byte1 y))
    (Byte.and (byte2 x) (byte2 y)) (Byte.and (byte3 x) (byte3 y)).

Notation "x &. y" := (and x y) (only parsing)
  : jwa_word_scope.

(* Both operands converted to little-endian, then combined: the result is
 * little-endian whatever theirs.
 *)
(* [Word -> Word -> Word] *)
Definition and_little_endian := fun (x : Word) (y : Word) .
  and (with_endian Endian.Little x) y.

(* Both operands converted to big-endian, then combined: the result is
 * big-endian whatever theirs.
 *)
(* [Word -> Word -> Word] *)
Definition and_big_endian := fun (x : Word) (y : Word) .
  and (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [Word -> Word -> Word] *)
Definition or := fun (x : Word) (y : Word) .
  make (endian x)
    (Byte.or (byte0 x) (byte0 y)) (Byte.or (byte1 x) (byte1 y))
    (Byte.or (byte2 x) (byte2 y)) (Byte.or (byte3 x) (byte3 y)).

Notation "x |. y" := (or x y) (only parsing)
  : jwa_word_scope.

(* [Word -> Word -> Word] *)
Definition or_little_endian := fun (x : Word) (y : Word) .
  or (with_endian Endian.Little x) y.

(* [Word -> Word -> Word] *)
Definition or_big_endian := fun (x : Word) (y : Word) .
  or (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [Word -> Word -> Word] *)
Definition xor := fun (x : Word) (y : Word) .
  make (endian x)
    (Byte.xor (byte0 x) (byte0 y)) (Byte.xor (byte1 x) (byte1 y))
    (Byte.xor (byte2 x) (byte2 y)) (Byte.xor (byte3 x) (byte3 y)).

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_word_scope.

(* [Word -> Word -> Word] *)
Definition xor_little_endian := fun (x : Word) (y : Word) .
  xor (with_endian Endian.Little x) y.

(* [Word -> Word -> Word] *)
Definition xor_big_endian := fun (x : Word) (y : Word) .
  xor (with_endian Endian.Big x) y.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1]. The bit leaving each
 * byte at its top enters the next byte up at its bottom, and the result
 * keeps the endianness. Each endianness has its branch, so that a step
 * takes its argument apart once: through [byte0] to [byte3] and [endian] it
 * would do so five times, and [simpl] would copy the previous step into
 * each.
 *)
(* [Word -> Nat -> Word] *)
Fixpoint rotate_left_nat (x : Word) (k : Nat) : Word :=
  let y :=
    match x with
    | Word.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24) =>
        Word.introduction Endian.Little
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 x31)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
    | Word.introduction Endian.Big
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Word.introduction Endian.Big
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 x31)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [Word -> Nat -> Word] *)
Fixpoint rotate_right_nat (x : Word) (k : Nat) : Word :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | Word.introduction Endian.Little
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24) =>
      Word.introduction Endian.Little
        (Byte.introduction y8 y7 y6 y5 y4 y3 y2 y1)
        (Byte.introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.introduction y0 y31 y30 y29 y28 y27 y26 y25)
  | Word.introduction Endian.Big
      (Byte.introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      Word.introduction Endian.Big
        (Byte.introduction y0 y31 y30 y29 y28 y27 y26 y25)
        (Byte.introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.introduction y8 y7 y6 y5 y4 y3 y2 y1)
  end.

(* [Word -> Nat0 -> Word] *)
Definition rotate_left := fun (x : Word) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [Word -> Nat0 -> Word] *)
Definition rotate_right := fun (x : Word) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [Bit.Zero] coming in at the
 * other, in the order and the branches of [rotate_left_nat].
 *)
(* [Word -> Nat -> Word] *)
Fixpoint shift_left_nat (x : Word) (k : Nat) : Word :=
  let y :=
    match x with
    | Word.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24) =>
        Word.introduction Endian.Little
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
    | Word.introduction Endian.Big
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Word.introduction Endian.Big
          (Byte.introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [k] places toward the least significant end, a [Bit.Zero] coming in at
 * the other; one place first, then [k - 1], as [shift_left_nat].
 *)
(* [Word -> Nat -> Word] *)
Fixpoint shift_right_nat (x : Word) (k : Nat) : Word :=
  let y :=
    match x with
    | Word.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24) =>
        Word.introduction Endian.Little
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
          (Byte.introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.introduction Bit.Zero x31 x30 x29 x28 x27 x26 x25)
    | Word.introduction Endian.Big
        (Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        Word.introduction Endian.Big
          (Byte.introduction Bit.Zero x31 x30 x29 x28 x27 x26 x25)
          (Byte.introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [Word -> Nat0 -> Word] *)
Definition shift_left := fun (x : Word) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [Word -> Nat0 -> Word] *)
Definition shift_right := fun (x : Word) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* The four bytes in the order they are laid out. *)
(* [Word -> List Byte] *)
Definition to_bytes := fun (x : Word) .
  match x with
  | Word.introduction _ b0 b1 b2 b3 =>
      List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3 List.Nil)))
  end.

(* The word of endianness [e] laid out as the bytes of [l], or [None] for a
 * list of any length but four.
 *)
(* [Endian -> List Byte -> Option Word] *)
Definition from_bytes := fun (e : Endian) (l : List Byte) .
  match l with
  | List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3 List.Nil))) =>
      Some (Word.introduction e b0 b1 b2 b3)
  | _ =>
      None
  end.

(* [x] with the four bits of a hexadecimal digit shifted in at the least
 * significant end, or [None] when that would push a 1 out at the other, so
 * that a literal past eight significant digits is refused; one branch per
 * endianness, as [rotate_left_nat].
 *)
(* [Option Word -> Bit -> Bit -> Bit -> Bit -> Option Word] *)
Definition append_digit := fun (x : Option Word) (d3 : Bit) (d2 : Bit) (d1 : Bit) (d0 : Bit) .
  match x with
  | Some
      (Word.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x27 x26 x25 x24)) =>
      Some
        (Word.introduction Endian.Little
          (Byte.introduction x3 x2 x1 x0 d3 d2 d1 d0)
          (Byte.introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.introduction x19 x18 x17 x16 x15 x14 x13 x12)
          (Byte.introduction x27 x26 x25 x24 x23 x22 x21 x20))
  | Some
      (Word.introduction Endian.Big
        (Byte.introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x27 x26 x25 x24)
        (Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) =>
      Some
        (Word.introduction Endian.Big
          (Byte.introduction x27 x26 x25 x24 x23 x22 x21 x20)
          (Byte.introduction x19 x18 x17 x16 x15 x14 x13 x12)
          (Byte.introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.introduction x3 x2 x1 x0 d3 d2 d1 d0))
  | _ => None
  end.

(* [x] with the hexadecimal digits [h] appended, most significant first. *)
(* [Option Word -> Numeral.Hexadecimal.Digits -> Option Word] *)
Fixpoint from_hexadecimal (x : Option Word) (h : Numeral.Hexadecimal.Digits) : Option Word :=
  match h with
  | Numeral.Hexadecimal.Digits.End         =>
      x
  | Numeral.Hexadecimal.Digits.Zero h'     =>
      from_hexadecimal (append_digit x Bit.Zero Bit.Zero Bit.Zero Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.One h'      =>
      from_hexadecimal (append_digit x Bit.Zero Bit.Zero Bit.Zero Bit.One) h'
  | Numeral.Hexadecimal.Digits.Two h'      =>
      from_hexadecimal (append_digit x Bit.Zero Bit.Zero Bit.One Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Three h'    =>
      from_hexadecimal (append_digit x Bit.Zero Bit.Zero Bit.One Bit.One) h'
  | Numeral.Hexadecimal.Digits.Four h'     =>
      from_hexadecimal (append_digit x Bit.Zero Bit.One Bit.Zero Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Five h'     =>
      from_hexadecimal (append_digit x Bit.Zero Bit.One Bit.Zero Bit.One) h'
  | Numeral.Hexadecimal.Digits.Six h'      =>
      from_hexadecimal (append_digit x Bit.Zero Bit.One Bit.One Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Seven h'    =>
      from_hexadecimal (append_digit x Bit.Zero Bit.One Bit.One Bit.One) h'
  | Numeral.Hexadecimal.Digits.Eight h'    =>
      from_hexadecimal (append_digit x Bit.One Bit.Zero Bit.Zero Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Nine h'     =>
      from_hexadecimal (append_digit x Bit.One Bit.Zero Bit.Zero Bit.One) h'
  | Numeral.Hexadecimal.Digits.Ten h'      =>
      from_hexadecimal (append_digit x Bit.One Bit.Zero Bit.One Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Eleven h'   =>
      from_hexadecimal (append_digit x Bit.One Bit.Zero Bit.One Bit.One) h'
  | Numeral.Hexadecimal.Digits.Twelve h'   =>
      from_hexadecimal (append_digit x Bit.One Bit.One Bit.Zero Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Thirteen h' =>
      from_hexadecimal (append_digit x Bit.One Bit.One Bit.Zero Bit.One) h'
  | Numeral.Hexadecimal.Digits.Fourteen h' =>
      from_hexadecimal (append_digit x Bit.One Bit.One Bit.One Bit.Zero) h'
  | Numeral.Hexadecimal.Digits.Fifteen h'  =>
      from_hexadecimal (append_digit x Bit.One Bit.One Bit.One Bit.One) h'
  end.

(* A literal in hexadecimal, read as the bits it spells and laid out in the
 * order [e] names; a decimal one is refused, since a word is bits and not a
 * number.
 *)
(* [Endian -> Numeral.Unsigned -> Option Word] *)
Definition from_numeral := fun (e : Endian) (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal _     => None
  | Numeral.Unsigned.Hexadecimal h => from_hexadecimal (Some (Zero e)) h
  end.

(* [Numeral.Unsigned -> Option Word] *)
Definition from_little_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Little u.

(* [Numeral.Unsigned -> Option Word] *)
Definition from_big_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Big u.

(* [x] as a literal of eight hexadecimal digits, the most significant byte's
 * first, when its endianness is [e], and [None] otherwise, so that a
 * literal scope prints only the words it reads back.
 *)
(* [Endian -> Word -> Option Numeral.Unsigned] *)
Definition to_numeral := fun (e : Endian) (x : Word) .
  let digits :=
    match byte0 x, byte1 x, byte2 x, byte3 x with
    | Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0,
      Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8,
      Byte.introduction x23 x22 x21 x20 x19 x18 x17 x16,
      Byte.introduction x31 x30 x29 x28 x27 x26 x25 x24 =>
        Numeral.Unsigned.Hexadecimal
          (Byte.hexadecimal_digit x31 x30 x29 x28
            (Byte.hexadecimal_digit x27 x26 x25 x24
              (Byte.hexadecimal_digit x23 x22 x21 x20
                (Byte.hexadecimal_digit x19 x18 x17 x16
                  (Byte.hexadecimal_digit x15 x14 x13 x12
                    (Byte.hexadecimal_digit x11 x10 x9 x8
                      (Byte.hexadecimal_digit x7 x6 x5 x4
                        (Byte.hexadecimal_digit x3 x2 x1 x0
                          Numeral.Hexadecimal.Digits.End))))))))
    end in
  match e, endian x with
  | Endian.Little, Endian.Little => Some digits
  | Endian.Big, Endian.Big       => Some digits
  | _, _                         => None
  end.

(* [Word -> Option Numeral.Unsigned] *)
Definition to_little_numeral := fun (x : Word) . to_numeral Endian.Little x.

(* [Word -> Option Numeral.Unsigned] *)
Definition to_big_numeral := fun (x : Word) . to_numeral Endian.Big x.

Local Open Scope jwa_word_scope.

(* Equal bytes in each place make equal words of one endianness; each law
 * below is its [Byte] counterpart taken byte by byte through this.
 *)
(* congruence *)
Lemma congruence
  : forall {e : Endian} {a0 : Byte} {a1 : Byte} {a2 : Byte} {a3 : Byte}
      {b0 : Byte} {b1 : Byte} {b2 : Byte} {b3 : Byte} .
      a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 ->
      Word.introduction e a0 a1 a2 a3 = Word.introduction e b0 b1 b2 b3.
Proof.
  intros e a0 a1 a2 a3 b0 b1 b2 b3 e0 e1 e2 e3.
  leibniz &e0, &e1, &e2, &e3 in |- *.
  quod idem est.
Qed.

Module endianness. (* endianness *)

(* endianness.specification *)
Theorem specification : forall (e : Endian) (x : Word) . endian (with_endian e x) = e.
Proof.
  intros e x.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.identity *)
Theorem identity : forall (x : Word) . with_endian (endian x) x = x.
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.absorption *)
Theorem absorption
  : forall (e : Endian) (f : Endian) (x : Word) .
      with_endian e (with_endian f x) = with_endian e x.
Proof.
  intros e f x.
  match &e with | Little | Big end;
    match &f with | Little | Big end;
    simpl in |- *;
    quod idem est.
Qed.

End endianness. (* endianness *)

Module flipping. (* flipping *)

(* flipping.involution *)
Theorem involution : forall (x : Word) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end;
    simpl flip in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.flipping.involution &x0) (Byte.flipping.involution &x1)
        (Byte.flipping.involution &x2) (Byte.flipping.involution &x3)).
Qed.

Module endian. (* flipping.endian *)

Module little. (* flipping.endian.little *)

(* flipping.endian.little.specification *)
Theorem specification : forall (x : Word) . endian (flip_little_endian x) = Endian.Little.
Proof.
  intros x.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* flipping.endian.little *)

Module big. (* flipping.endian.big *)

(* flipping.endian.big.specification *)
Theorem specification : forall (x : Word) . endian (flip_big_endian x) = Endian.Big.
Proof.
  intros x.
  simpl in |- *.
  quod idem est.
Qed.

End big. (* flipping.endian.big *)

End endian. (* flipping.endian *)

End flipping. (* flipping *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (x : Word) (y : Word) (z : Word) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  match &z with | introduction ez z0 z1 z2 z3 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)).
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (x : Word) . (~. Zero (endian x) &. x = x) /\ (x &. ~. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match (Byte.conjunction.identity &x0) with | left0 right0 end.
  match (Byte.conjunction.identity &x1) with | left1 right1 end.
  match (Byte.conjunction.identity &x2) with | left2 right2 end.
  match (Byte.conjunction.identity &x3) with | left3 right3 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
Qed.

Module endian. (* conjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* conjunction.endian.conversion *)
Theorem conversion
  : forall (x : Word) (y : Word) . x &. y = x &. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end;
    simpl and, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* conjunction.endian.little *)

(* conjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Little -> endian y = Endian.Little -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)
      (Byte.conjunction.commutativity &x2 &y2)
      (Byte.conjunction.commutativity &x3 &y3)).
Qed.

(* conjunction.endian.little.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (and_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* conjunction.endian.little *)

Module big. (* conjunction.endian.big *)

(* conjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Big -> endian y = Endian.Big -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)
      (Byte.conjunction.commutativity &x2 &y2)
      (Byte.conjunction.commutativity &x3 &y3)).
Qed.

(* conjunction.endian.big.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (and_big_endian x y) = Endian.Big.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End big. (* conjunction.endian.big *)

End endian. (* conjunction.endian *)

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Word) (y : Word) (z : Word) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  match &z with | introduction ez z0 z1 z2 z3 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and, xor in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)).
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Word) (y : Word) (z : Word) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  match &z with | introduction ez z0 z1 z2 z3 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and, xor in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)).
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Word) (y : Word) (z : Word) .
      (x &. (y ^. z) = (x &. y) ^. (x &. z))
    /\ ((y ^. z) &. x = (y &. x) ^. (z &. x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (conjunction.left.distributivity.over.sejunction  &x &y &z).
  - ipso (conjunction.right.distributivity.over.sejunction &x &y &z).
Qed.

End over. (* conjunction.distributivity.over *)

End distributivity. (* conjunction.distributivity *)

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.associativity *)
Theorem associativity
  : forall (x : Word) (y : Word) (z : Word) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  match &z with | introduction ez z0 z1 z2 z3 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl or in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)).
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (x : Word) . (Zero (endian x) |. x = x) /\ (x |. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match (Byte.disjunction.identity &x0) with | left0 right0 end.
  match (Byte.disjunction.identity &x1) with | left1 right1 end.
  match (Byte.disjunction.identity &x2) with | left2 right2 end.
  match (Byte.disjunction.identity &x3) with | left3 right3 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
Qed.

Module endian. (* disjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* disjunction.endian.conversion *)
Theorem conversion
  : forall (x : Word) (y : Word) . x |. y = x |. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end;
    simpl or, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* disjunction.endian.little *)

(* disjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Little -> endian y = Endian.Little -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)
      (Byte.disjunction.commutativity &x2 &y2)
      (Byte.disjunction.commutativity &x3 &y3)).
Qed.

(* disjunction.endian.little.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (or_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* disjunction.endian.little *)

Module big. (* disjunction.endian.big *)

(* disjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Big -> endian y = Endian.Big -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)
      (Byte.disjunction.commutativity &x2 &y2)
      (Byte.disjunction.commutativity &x3 &y3)).
Qed.

(* disjunction.endian.big.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (or_big_endian x y) = Endian.Big.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End big. (* disjunction.endian.big *)

End endian. (* disjunction.endian *)

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.associativity *)
Theorem associativity
  : forall (x : Word) (y : Word) (z : Word) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  match &z with | introduction ez z0 z1 z2 z3 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl xor in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)).
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (x : Word) . (Zero (endian x) ^. x = x) /\ (x ^. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match (Byte.sejunction.identity &x0) with | left0 right0 end.
  match (Byte.sejunction.identity &x1) with | left1 right1 end.
  match (Byte.sejunction.identity &x2) with | left2 right2 end.
  match (Byte.sejunction.identity &x3) with | left3 right3 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3).
    + ipso (congruence &right0 &right1 &right2 &right3).
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : Word) . x ^. x = Zero (endian x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end;
    ipso
      (congruence
        (Byte.sejunction.irreflexivity &x0) (Byte.sejunction.irreflexivity &x1)
        (Byte.sejunction.irreflexivity &x2) (Byte.sejunction.irreflexivity &x3)).
Qed.

Module endian. (* sejunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* sejunction.endian.conversion *)
Theorem conversion
  : forall (x : Word) (y : Word) . x ^. y = x ^. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 x2 x3 end.
  match &e with | Little | Big end;
    simpl xor, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* sejunction.endian.little *)

(* sejunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Little -> endian y = Endian.Little -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)
      (Byte.sejunction.commutativity &x2 &y2)
      (Byte.sejunction.commutativity &x3 &y3)).
Qed.

(* sejunction.endian.little.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (xor_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* sejunction.endian.little *)

Module big. (* sejunction.endian.big *)

(* sejunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : Word) (y : Word) .
      endian x = Endian.Big -> endian y = Endian.Big -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 x2 x3 end.
  match &y with | introduction ey y0 y1 y2 y3 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)
      (Byte.sejunction.commutativity &x2 &y2)
      (Byte.sejunction.commutativity &x3 &y3)).
Qed.

(* sejunction.endian.big.specification *)
Theorem specification
  : forall (x : Word) (y : Word) . endian (xor_big_endian x y) = Endian.Big.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End big. (* sejunction.endian.big *)

End endian. (* sejunction.endian *)

End sejunction. (* sejunction *)

Module rotation. (* rotation *)

Module left. (* rotation.left *)

(* rotation.left.period *)
Theorem period : forall (x : Word) . rotate_left x 32%n0 = x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 b2 b3 end.
  match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b2 with | introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &b3 with | introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : Word) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with | introduction e b0 b1 b2 b3 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + intros x.
      match &x with | introduction e b0 b1 b2 b3 end.
      match &e with | Little | Big end.
      * match &b0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        match &b1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b2 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b3 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        simpl in |- *.
        leibniz
          (&IH
            (Word.introduction Endian.Little
              (Byte.introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x31)
              (Byte.introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)))
          in |- *.
        simpl in |- *.
        quod idem est.
      * match &b0 with | introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        match &b1 with | introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b2 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b3 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        simpl in |- *.
        leibniz
          (&IH
            (Word.introduction Endian.Big
              (Byte.introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)
              (Byte.introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x31)))
          in |- *.
        simpl in |- *.
        quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : Word) . rotate_right x 32%n0 = x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 b2 b3 end.
  match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b2 with | introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &b3 with | introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : Word) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with | introduction e b0 b1 b2 b3 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with | introduction e b0 b1 b2 b3 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &e with | Little | Big end; ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

Module conversion. (* conversion *)

Module bytes. (* conversion.bytes *)

(* conversion.bytes.section *)
Theorem section : forall (x : Word) . from_bytes (endian x) (to_bytes x) = Some x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 b2 b3 end.
  simpl from_bytes, to_bytes, endian in |- *.
  quod idem est.
Qed.

End bytes. (* conversion.bytes *)

End conversion. (* conversion *)

End Word. (* Word *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Word], not [Word.T].
 *)
Abbreviation Word := Word.T.

(* Makes the notations declared in [Module Word] usable in every file that
 * imports this one, as [(x &. y)%word] or under an opened [jwa_word_scope].
 *)
Export (notations) Word.

(* A word is written in hexadecimal, [0x12345678%word_little] or
 * [0x12345678%word_big] laid out as the key names, and prints back the same
 * way, in eight digits. The plain key reads little-endian and is declared
 * last, so a little-endian word prints as [0x12345678%word].
 *)
Number Notation Word.T Word.from_little_numeral Word.to_little_numeral
  : jwa_word_little_scope.
Number Notation Word.T Word.from_big_numeral Word.to_big_numeral
  : jwa_word_big_scope.
Number Notation Word.T Word.from_little_numeral Word.to_little_numeral
  : jwa_word_scope.

(* Where a [Word] is expected, a literal or a notation reads in this scope
 * without its [%word].
 *)
Bind Scope jwa_word_scope with Word.T.
