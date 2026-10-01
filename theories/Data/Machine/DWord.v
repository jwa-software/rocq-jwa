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

Module DWord. (* DWord *)

Inductive T : Type :=
  | DWord_introduction :
      Endian -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> T.

Abbreviation DWord := T.

(* [DWord -> Endian] *)
Definition endian := fun (x : DWord) .
  match x with
  | DWord_introduction e _ _ _ _ _ _ _ _ => e
  end.

(* The least significant byte, wherever the endianness lays it; [byte1] to
 * [byte7] follow in significance.
 *)
(* [DWord -> Byte] *)
Definition byte0 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little b0 _  _  _  _  _  _  _  => b0
  | DWord_introduction Endian.Big    _  _  _  _  _  _  _  b0 => b0
  end.

(* [DWord -> Byte] *)
Definition byte1 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  b1 _  _  _  _  _  _  => b1
  | DWord_introduction Endian.Big    _  _  _  _  _  _  b1 _  => b1
  end.

(* [DWord -> Byte] *)
Definition byte2 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  b2 _  _  _  _  _  => b2
  | DWord_introduction Endian.Big    _  _  _  _  _  b2 _  _  => b2
  end.

(* [DWord -> Byte] *)
Definition byte3 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  _  b3 _  _  _  _  => b3
  | DWord_introduction Endian.Big    _  _  _  _  b3 _  _  _  => b3
  end.

(* [DWord -> Byte] *)
Definition byte4 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  _  _  b4 _  _  _  => b4
  | DWord_introduction Endian.Big    _  _  _  b4 _  _  _  _  => b4
  end.

(* [DWord -> Byte] *)
Definition byte5 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  _  _  _  b5 _  _  => b5
  | DWord_introduction Endian.Big    _  _  b5 _  _  _  _  _  => b5
  end.

(* [DWord -> Byte] *)
Definition byte6 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  _  _  _  _  b6 _  => b6
  | DWord_introduction Endian.Big    _  b6 _  _  _  _  _  _  => b6
  end.

(* [DWord -> Byte] *)
Definition byte7 := fun (x : DWord) .
  match x with
  | DWord_introduction Endian.Little _  _  _  _  _  _  _  b7 => b7
  | DWord_introduction Endian.Big    b7 _  _  _  _  _  _  _  => b7
  end.

(* The double word of endianness [e] whose bytes, least significant first, are
 * [b0] to [b7], laid out in the order [e] names.
 *)
(* [Endian -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> DWord] *)
Definition make :=
  fun (e : Endian)
      (b0 : Byte) (b1 : Byte) (b2 : Byte) (b3 : Byte)
      (b4 : Byte) (b5 : Byte) (b6 : Byte) (b7 : Byte) .
  match e with
  | Endian.Little => DWord_introduction Endian.Little b0 b1 b2 b3 b4 b5 b6 b7
  | Endian.Big    => DWord_introduction Endian.Big    b7 b6 b5 b4 b3 b2 b1 b0
  end.

(* The same value, laid out in the order [e] names. *)
(* [Endian -> DWord -> DWord] *)
Definition with_endian := fun (e : Endian) (x : DWord) .
  make e (byte0 x) (byte1 x) (byte2 x) (byte3 x) (byte4 x) (byte5 x) (byte6 x) (byte7 x).

(* [Endian -> DWord] *)
Definition Zero := fun (e : Endian) .
  make e
    Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero.

(* [DWord -> DWord] *)
Definition flip := fun (x : DWord) .
  make (endian x)
    (Byte.flip (byte0 x)) (Byte.flip (byte1 x)) (Byte.flip (byte2 x)) (Byte.flip (byte3 x))
    (Byte.flip (byte4 x)) (Byte.flip (byte5 x)) (Byte.flip (byte6 x)) (Byte.flip (byte7 x)).

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_dword_scope.

(* [x] converted to little-endian, then flipped. *)
(* [DWord -> DWord] *)
Definition flip_little_endian := fun (x : DWord) . flip (with_endian Endian.Little x).

(* [x] converted to big-endian, then flipped. *)
(* [DWord -> DWord] *)
Definition flip_big_endian := fun (x : DWord) . flip (with_endian Endian.Big x).

(* [y] converted to the endianness of [x], then combined with it byte by
 * byte: the result takes the endianness of [x].
 *)
(* [DWord -> DWord -> DWord] *)
Definition and := fun (x : DWord) (y : DWord) .
  make (endian x)
    (Byte.and (byte0 x) (byte0 y)) (Byte.and (byte1 x) (byte1 y))
    (Byte.and (byte2 x) (byte2 y)) (Byte.and (byte3 x) (byte3 y))
    (Byte.and (byte4 x) (byte4 y)) (Byte.and (byte5 x) (byte5 y))
    (Byte.and (byte6 x) (byte6 y)) (Byte.and (byte7 x) (byte7 y)).

Notation "x &. y" := (and x y) (only parsing)
  : jwa_dword_scope.

(* Both operands converted to little-endian, then combined: the result is
 * little-endian whatever theirs.
 *)
(* [DWord -> DWord -> DWord] *)
Definition and_little_endian := fun (x : DWord) (y : DWord) .
  and (with_endian Endian.Little x) y.

(* Both operands converted to big-endian, then combined: the result is
 * big-endian whatever theirs.
 *)
(* [DWord -> DWord -> DWord] *)
Definition and_big_endian := fun (x : DWord) (y : DWord) .
  and (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [DWord -> DWord -> DWord] *)
Definition or := fun (x : DWord) (y : DWord) .
  make (endian x)
    (Byte.or (byte0 x) (byte0 y)) (Byte.or (byte1 x) (byte1 y))
    (Byte.or (byte2 x) (byte2 y)) (Byte.or (byte3 x) (byte3 y))
    (Byte.or (byte4 x) (byte4 y)) (Byte.or (byte5 x) (byte5 y))
    (Byte.or (byte6 x) (byte6 y)) (Byte.or (byte7 x) (byte7 y)).

Notation "x |. y" := (or x y) (only parsing)
  : jwa_dword_scope.

(* [DWord -> DWord -> DWord] *)
Definition or_little_endian := fun (x : DWord) (y : DWord) .
  or (with_endian Endian.Little x) y.

(* [DWord -> DWord -> DWord] *)
Definition or_big_endian := fun (x : DWord) (y : DWord) .
  or (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [DWord -> DWord -> DWord] *)
Definition xor := fun (x : DWord) (y : DWord) .
  make (endian x)
    (Byte.xor (byte0 x) (byte0 y)) (Byte.xor (byte1 x) (byte1 y))
    (Byte.xor (byte2 x) (byte2 y)) (Byte.xor (byte3 x) (byte3 y))
    (Byte.xor (byte4 x) (byte4 y)) (Byte.xor (byte5 x) (byte5 y))
    (Byte.xor (byte6 x) (byte6 y)) (Byte.xor (byte7 x) (byte7 y)).

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_dword_scope.

(* [DWord -> DWord -> DWord] *)
Definition xor_little_endian := fun (x : DWord) (y : DWord) .
  xor (with_endian Endian.Little x) y.

(* [DWord -> DWord -> DWord] *)
Definition xor_big_endian := fun (x : DWord) (y : DWord) .
  xor (with_endian Endian.Big x) y.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1]. The bit leaving each
 * byte at its top enters the next byte up at its bottom, and the result
 * keeps the endianness. Each endianness has its branch, so that a step
 * takes its argument apart once: through [byte0] to [byte7] and [endian] it
 * would do so nine times, and [simpl] would copy the previous step into
 * each.
 *)
(* [DWord -> Nat -> DWord] *)
Fixpoint rotate_left_nat (x : DWord) (k : Nat) : DWord :=
  let y :=
    match x with
    | DWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56) =>
        DWord_introduction Endian.Little
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 x63)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
    | DWord_introduction Endian.Big
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        DWord_introduction Endian.Big
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 x63)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [DWord -> Nat -> DWord] *)
Fixpoint rotate_right_nat (x : DWord) (k : Nat) : DWord :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | DWord_introduction Endian.Little
      (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0)
      (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.Byte_introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.Byte_introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.Byte_introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.Byte_introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.Byte_introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.Byte_introduction y63 y62 y61 y60 y59 y58 y57 y56) =>
      DWord_introduction Endian.Little
        (Byte.Byte_introduction y8 y7 y6 y5 y4 y3 y2 y1)
        (Byte.Byte_introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.Byte_introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.Byte_introduction y32 y31 y30 y29 y28 y27 y26 y25)
        (Byte.Byte_introduction y40 y39 y38 y37 y36 y35 y34 y33)
        (Byte.Byte_introduction y48 y47 y46 y45 y44 y43 y42 y41)
        (Byte.Byte_introduction y56 y55 y54 y53 y52 y51 y50 y49)
        (Byte.Byte_introduction y0 y63 y62 y61 y60 y59 y58 y57)
  | DWord_introduction Endian.Big
      (Byte.Byte_introduction y63 y62 y61 y60 y59 y58 y57 y56)
      (Byte.Byte_introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.Byte_introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.Byte_introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.Byte_introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.Byte_introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      DWord_introduction Endian.Big
        (Byte.Byte_introduction y0 y63 y62 y61 y60 y59 y58 y57)
        (Byte.Byte_introduction y56 y55 y54 y53 y52 y51 y50 y49)
        (Byte.Byte_introduction y48 y47 y46 y45 y44 y43 y42 y41)
        (Byte.Byte_introduction y40 y39 y38 y37 y36 y35 y34 y33)
        (Byte.Byte_introduction y32 y31 y30 y29 y28 y27 y26 y25)
        (Byte.Byte_introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.Byte_introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.Byte_introduction y8 y7 y6 y5 y4 y3 y2 y1)
  end.

(* [DWord -> Nat0 -> DWord] *)
Definition rotate_left := fun (x : DWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [DWord -> Nat0 -> DWord] *)
Definition rotate_right := fun (x : DWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [Bit.Zero] coming in at the
 * other, in the order and the branches of [rotate_left_nat].
 *)
(* [DWord -> Nat -> DWord] *)
Fixpoint shift_left_nat (x : DWord) (k : Nat) : DWord :=
  let y :=
    match x with
    | DWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56) =>
        DWord_introduction Endian.Little
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
    | DWord_introduction Endian.Big
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        DWord_introduction Endian.Big
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [k] places toward the least significant end, a [Bit.Zero] coming in at
 * the other; one place first, then [k - 1], as [shift_left_nat].
 *)
(* [DWord -> Nat -> DWord] *)
Fixpoint shift_right_nat (x : DWord) (k : Nat) : DWord :=
  let y :=
    match x with
    | DWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56) =>
        DWord_introduction Endian.Little
          (Byte.Byte_introduction x8 x7 x6 x5 x4 x3 x2 x1)
          (Byte.Byte_introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.Byte_introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.Byte_introduction x32 x31 x30 x29 x28 x27 x26 x25)
          (Byte.Byte_introduction x40 x39 x38 x37 x36 x35 x34 x33)
          (Byte.Byte_introduction x48 x47 x46 x45 x44 x43 x42 x41)
          (Byte.Byte_introduction x56 x55 x54 x53 x52 x51 x50 x49)
          (Byte.Byte_introduction Bit.Zero x63 x62 x61 x60 x59 x58 x57)
    | DWord_introduction Endian.Big
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        DWord_introduction Endian.Big
          (Byte.Byte_introduction Bit.Zero x63 x62 x61 x60 x59 x58 x57)
          (Byte.Byte_introduction x56 x55 x54 x53 x52 x51 x50 x49)
          (Byte.Byte_introduction x48 x47 x46 x45 x44 x43 x42 x41)
          (Byte.Byte_introduction x40 x39 x38 x37 x36 x35 x34 x33)
          (Byte.Byte_introduction x32 x31 x30 x29 x28 x27 x26 x25)
          (Byte.Byte_introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.Byte_introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.Byte_introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [DWord -> Nat0 -> DWord] *)
Definition shift_left := fun (x : DWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [DWord -> Nat0 -> DWord] *)
Definition shift_right := fun (x : DWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* The eight bytes in the order they are laid out. *)
(* [DWord -> List Byte] *)
Definition to_bytes := fun (x : DWord) .
  match x with
  | DWord_introduction _ b0 b1 b2 b3 b4 b5 b6 b7 =>
      List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3
        (List.Cons b4 (List.Cons b5 (List.Cons b6 (List.Cons b7 List.Nil)))))))
  end.

(* The double word of endianness [e] laid out as the bytes of [l], or [None] for a
 * list of any length but eight.
 *)
(* [Endian -> List Byte -> Option DWord] *)
Definition from_bytes := fun (e : Endian) (l : List Byte) .
  match l with
  | List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3
      (List.Cons b4 (List.Cons b5 (List.Cons b6 (List.Cons b7 List.Nil))))))) =>
      Some (DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7)
  | _ =>
      None
  end.

(* [x] with the four bits of a hexadecimal digit shifted in at the least
 * significant end, or [None] when that would push a 1 out at the other, so
 * that a literal past sixteen significant digits is refused; one branch per
 * endianness, as [rotate_left_nat].
 *)
(* [Option DWord -> Bit -> Bit -> Bit -> Bit -> Option DWord] *)
Definition append_digit := fun (x : Option DWord) (d3 : Bit) (d2 : Bit) (d1 : Bit) (d0 : Bit) .
  match x with
  | Some
      (DWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x59 x58 x57 x56)) =>
      Some
        (DWord_introduction Endian.Little
          (Byte.Byte_introduction x3 x2 x1 x0 d3 d2 d1 d0)
          (Byte.Byte_introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.Byte_introduction x19 x18 x17 x16 x15 x14 x13 x12)
          (Byte.Byte_introduction x27 x26 x25 x24 x23 x22 x21 x20)
          (Byte.Byte_introduction x35 x34 x33 x32 x31 x30 x29 x28)
          (Byte.Byte_introduction x43 x42 x41 x40 x39 x38 x37 x36)
          (Byte.Byte_introduction x51 x50 x49 x48 x47 x46 x45 x44)
          (Byte.Byte_introduction x59 x58 x57 x56 x55 x54 x53 x52))
  | Some
      (DWord_introduction Endian.Big
        (Byte.Byte_introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)) =>
      Some
        (DWord_introduction Endian.Big
          (Byte.Byte_introduction x59 x58 x57 x56 x55 x54 x53 x52)
          (Byte.Byte_introduction x51 x50 x49 x48 x47 x46 x45 x44)
          (Byte.Byte_introduction x43 x42 x41 x40 x39 x38 x37 x36)
          (Byte.Byte_introduction x35 x34 x33 x32 x31 x30 x29 x28)
          (Byte.Byte_introduction x27 x26 x25 x24 x23 x22 x21 x20)
          (Byte.Byte_introduction x19 x18 x17 x16 x15 x14 x13 x12)
          (Byte.Byte_introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.Byte_introduction x3 x2 x1 x0 d3 d2 d1 d0))
  | _ => None
  end.

(* [x] with the hexadecimal digits [h] appended, most significant first. *)
(* [Option DWord -> Numeral.Hexadecimal.Digits -> Option DWord] *)
Fixpoint from_hexadecimal (x : Option DWord) (h : Numeral.Hexadecimal.Digits) : Option DWord :=
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
 * order [e] names; a decimal one is refused, since a double word is bits and not a
 * number.
 *)
(* [Endian -> Numeral.Unsigned -> Option DWord] *)
Definition from_numeral := fun (e : Endian) (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal _     => None
  | Numeral.Unsigned.Hexadecimal h => from_hexadecimal (Some (Zero e)) h
  end.

(* [Numeral.Unsigned -> Option DWord] *)
Definition from_little_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Little u.

(* [Numeral.Unsigned -> Option DWord] *)
Definition from_big_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Big u.

(* [x] as a literal of sixteen hexadecimal digits, the most significant byte's
 * first, when its endianness is [e], and [None] otherwise, so that a
 * literal scope prints only the double words it reads back.
 *)
(* [Endian -> DWord -> Option Numeral.Unsigned] *)
Definition to_numeral := fun (e : Endian) (x : DWord) .
  let digits :=
    match byte0 x, byte1 x, byte2 x, byte3 x, byte4 x, byte5 x, byte6 x, byte7 x with
    | Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0,
      Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8,
      Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16,
      Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24,
      Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32,
      Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40,
      Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48,
      Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56 =>
        Numeral.Unsigned.Hexadecimal
          (Byte.hexadecimal_digit x63 x62 x61 x60
            (Byte.hexadecimal_digit x59 x58 x57 x56
              (Byte.hexadecimal_digit x55 x54 x53 x52
                (Byte.hexadecimal_digit x51 x50 x49 x48
                  (Byte.hexadecimal_digit x47 x46 x45 x44
                    (Byte.hexadecimal_digit x43 x42 x41 x40
                      (Byte.hexadecimal_digit x39 x38 x37 x36
                        (Byte.hexadecimal_digit x35 x34 x33 x32
                          (Byte.hexadecimal_digit x31 x30 x29 x28
                            (Byte.hexadecimal_digit x27 x26 x25 x24
                              (Byte.hexadecimal_digit x23 x22 x21 x20
                                (Byte.hexadecimal_digit x19 x18 x17 x16
                                  (Byte.hexadecimal_digit x15 x14 x13 x12
                                    (Byte.hexadecimal_digit x11 x10 x9 x8
                                      (Byte.hexadecimal_digit x7 x6 x5 x4
                                        (Byte.hexadecimal_digit x3 x2 x1 x0
                                          Numeral.Hexadecimal.Digits.End))))))))))))))))
    end in
  match e, endian x with
  | Endian.Little, Endian.Little => Some digits
  | Endian.Big, Endian.Big       => Some digits
  | _, _                         => None
  end.

(* [DWord -> Option Numeral.Unsigned] *)
Definition to_little_numeral := fun (x : DWord) . to_numeral Endian.Little x.

(* [DWord -> Option Numeral.Unsigned] *)
Definition to_big_numeral := fun (x : DWord) . to_numeral Endian.Big x.

Local Open Scope jwa_dword_scope.

(* Equal bytes in each place make equal double words of one endianness; each law
 * below is its [Byte] counterpart taken byte by byte through this.
 *)
(* congruence *)
Lemma congruence
  : forall {e : Endian} {a0 : Byte} {a1 : Byte} {a2 : Byte} {a3 : Byte}
      {a4 : Byte} {a5 : Byte} {a6 : Byte} {a7 : Byte}
      {b0 : Byte} {b1 : Byte} {b2 : Byte} {b3 : Byte}
      {b4 : Byte} {b5 : Byte} {b6 : Byte} {b7 : Byte} .
      a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 ->
      a4 = b4 -> a5 = b5 -> a6 = b6 -> a7 = b7 ->
      DWord_introduction e a0 a1 a2 a3 a4 a5 a6 a7 = DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7.
Proof.
  intros e a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 e0 e1 e2 e3 e4 e5 e6 e7.
  leibniz &e0, &e1, &e2, &e3, &e4, &e5, &e6, &e7 in |- *.
  quod idem est.
Qed.

Module endianness. (* endianness *)

(* endianness.specification *)
Theorem specification : forall (e : Endian) (x : DWord) . endian (with_endian e x) = e.
Proof.
  intros e x.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.identity *)
Theorem identity : forall (x : DWord) . with_endian (endian x) x = x.
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.absorption *)
Theorem absorption
  : forall (e : Endian) (f : Endian) (x : DWord) .
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
Theorem involution : forall (x : DWord) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end;
    simpl flip in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.flipping.involution &x0) (Byte.flipping.involution &x1)
        (Byte.flipping.involution &x2) (Byte.flipping.involution &x3)
        (Byte.flipping.involution &x4) (Byte.flipping.involution &x5)
        (Byte.flipping.involution &x6) (Byte.flipping.involution &x7)).
Qed.

Module endian. (* flipping.endian *)

Module little. (* flipping.endian.little *)

(* flipping.endian.little.specification *)
Theorem specification : forall (x : DWord) . endian (flip_little_endian x) = Endian.Little.
Proof.
  intros x.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* flipping.endian.little *)

Module big. (* flipping.endian.big *)

(* flipping.endian.big.specification *)
Theorem specification : forall (x : DWord) . endian (flip_big_endian x) = Endian.Big.
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  match &z with | DWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 end.
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
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)).
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (x : DWord) . (~. Zero (endian x) &. x = x) /\ (x &. ~. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match (Byte.conjunction.identity &x0) with | left0 right0 end.
  match (Byte.conjunction.identity &x1) with | left1 right1 end.
  match (Byte.conjunction.identity &x2) with | left2 right2 end.
  match (Byte.conjunction.identity &x3) with | left3 right3 end.
  match (Byte.conjunction.identity &x4) with | left4 right4 end.
  match (Byte.conjunction.identity &x5) with | left5 right5 end.
  match (Byte.conjunction.identity &x6) with | left6 right6 end.
  match (Byte.conjunction.identity &x7) with | left7 right7 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
Qed.

Module endian. (* conjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* conjunction.endian.conversion *)
Theorem conversion
  : forall (x : DWord) (y : DWord) . x &. y = x &. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end;
    simpl and, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* conjunction.endian.little *)

(* conjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)
      (Byte.conjunction.commutativity &x2 &y2)
      (Byte.conjunction.commutativity &x3 &y3)
      (Byte.conjunction.commutativity &x4 &y4)
      (Byte.conjunction.commutativity &x5 &y5)
      (Byte.conjunction.commutativity &x6 &y6)
      (Byte.conjunction.commutativity &x7 &y7)).
Qed.

(* conjunction.endian.little.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (and_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* conjunction.endian.little *)

Module big. (* conjunction.endian.big *)

(* conjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)
      (Byte.conjunction.commutativity &x2 &y2)
      (Byte.conjunction.commutativity &x3 &y3)
      (Byte.conjunction.commutativity &x4 &y4)
      (Byte.conjunction.commutativity &x5 &y5)
      (Byte.conjunction.commutativity &x6 &y6)
      (Byte.conjunction.commutativity &x7 &y7)).
Qed.

(* conjunction.endian.big.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (and_big_endian x y) = Endian.Big.
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  match &z with | DWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 end.
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
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  match &z with | DWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 end.
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
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  match &z with | DWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 end.
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
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)).
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (x : DWord) . (Zero (endian x) |. x = x) /\ (x |. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match (Byte.disjunction.identity &x0) with | left0 right0 end.
  match (Byte.disjunction.identity &x1) with | left1 right1 end.
  match (Byte.disjunction.identity &x2) with | left2 right2 end.
  match (Byte.disjunction.identity &x3) with | left3 right3 end.
  match (Byte.disjunction.identity &x4) with | left4 right4 end.
  match (Byte.disjunction.identity &x5) with | left5 right5 end.
  match (Byte.disjunction.identity &x6) with | left6 right6 end.
  match (Byte.disjunction.identity &x7) with | left7 right7 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
Qed.

Module endian. (* disjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* disjunction.endian.conversion *)
Theorem conversion
  : forall (x : DWord) (y : DWord) . x |. y = x |. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end;
    simpl or, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* disjunction.endian.little *)

(* disjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)
      (Byte.disjunction.commutativity &x2 &y2)
      (Byte.disjunction.commutativity &x3 &y3)
      (Byte.disjunction.commutativity &x4 &y4)
      (Byte.disjunction.commutativity &x5 &y5)
      (Byte.disjunction.commutativity &x6 &y6)
      (Byte.disjunction.commutativity &x7 &y7)).
Qed.

(* disjunction.endian.little.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (or_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* disjunction.endian.little *)

Module big. (* disjunction.endian.big *)

(* disjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)
      (Byte.disjunction.commutativity &x2 &y2)
      (Byte.disjunction.commutativity &x3 &y3)
      (Byte.disjunction.commutativity &x4 &y4)
      (Byte.disjunction.commutativity &x5 &y5)
      (Byte.disjunction.commutativity &x6 &y6)
      (Byte.disjunction.commutativity &x7 &y7)).
Qed.

(* disjunction.endian.big.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (or_big_endian x y) = Endian.Big.
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
  : forall (x : DWord) (y : DWord) (z : DWord) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  match &z with | DWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 end.
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
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)).
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (x : DWord) . (Zero (endian x) ^. x = x) /\ (x ^. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match (Byte.sejunction.identity &x0) with | left0 right0 end.
  match (Byte.sejunction.identity &x1) with | left1 right1 end.
  match (Byte.sejunction.identity &x2) with | left2 right2 end.
  match (Byte.sejunction.identity &x3) with | left3 right3 end.
  match (Byte.sejunction.identity &x4) with | left4 right4 end.
  match (Byte.sejunction.identity &x5) with | left5 right5 end.
  match (Byte.sejunction.identity &x6) with | left6 right6 end.
  match (Byte.sejunction.identity &x7) with | left7 right7 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
  - divide et impera.
    + ipso (congruence &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7).
    + ipso (congruence &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7).
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : DWord) . x ^. x = Zero (endian x).
Proof.
  intros x.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end;
    ipso
      (congruence
        (Byte.sejunction.irreflexivity &x0) (Byte.sejunction.irreflexivity &x1)
        (Byte.sejunction.irreflexivity &x2) (Byte.sejunction.irreflexivity &x3)
        (Byte.sejunction.irreflexivity &x4) (Byte.sejunction.irreflexivity &x5)
        (Byte.sejunction.irreflexivity &x6) (Byte.sejunction.irreflexivity &x7)).
Qed.

Module endian. (* sejunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* sejunction.endian.conversion *)
Theorem conversion
  : forall (x : DWord) (y : DWord) . x ^. y = x ^. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | DWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &e with | Little | Big end;
    simpl xor, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* sejunction.endian.little *)

(* sejunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)
      (Byte.sejunction.commutativity &x2 &y2)
      (Byte.sejunction.commutativity &x3 &y3)
      (Byte.sejunction.commutativity &x4 &y4)
      (Byte.sejunction.commutativity &x5 &y5)
      (Byte.sejunction.commutativity &x6 &y6)
      (Byte.sejunction.commutativity &x7 &y7)).
Qed.

(* sejunction.endian.little.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (xor_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* sejunction.endian.little *)

Module big. (* sejunction.endian.big *)

(* sejunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : DWord) (y : DWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | DWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 end.
  match &y with | DWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)
      (Byte.sejunction.commutativity &x2 &y2)
      (Byte.sejunction.commutativity &x3 &y3)
      (Byte.sejunction.commutativity &x4 &y4)
      (Byte.sejunction.commutativity &x5 &y5)
      (Byte.sejunction.commutativity &x6 &y6)
      (Byte.sejunction.commutativity &x7 &y7)).
Qed.

(* sejunction.endian.big.specification *)
Theorem specification
  : forall (x : DWord) (y : DWord) . endian (xor_big_endian x y) = Endian.Big.
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
Theorem period : forall (x : DWord) . rotate_left x 64%n0 = x.
Proof.
  intros x.
  match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
  match &b0 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b2 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &b3 with | Byte_introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
  match &b4 with | Byte_introduction t7 t6 t5 t4 t3 t2 t1 t0 end.
  match &b5 with | Byte_introduction u7 u6 u5 u4 u3 u2 u1 u0 end.
  match &b6 with | Byte_introduction v7 v6 v5 v4 v3 v2 v1 v0 end.
  match &b7 with | Byte_introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : DWord) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
      match &b0 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | Byte_introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &b4 with | Byte_introduction t7 t6 t5 t4 t3 t2 t1 t0 end.
      match &b5 with | Byte_introduction u7 u6 u5 u4 u3 u2 u1 u0 end.
      match &b6 with | Byte_introduction v7 v6 v5 v4 v3 v2 v1 v0 end.
      match &b7 with | Byte_introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + intros x.
      match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
      match &e with | Little | Big end.
      * match &b0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        match &b1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b2 with | Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b3 with | Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        match &b4 with | Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
        match &b5 with | Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
        match &b6 with | Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
        match &b7 with | Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
        simpl in |- *.
        leibniz
          (&IH
            (DWord_introduction Endian.Little
              (Byte.Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x63)
              (Byte.Byte_introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.Byte_introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.Byte_introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)
              (Byte.Byte_introduction &x38 &x37 &x36 &x35 &x34 &x33 &x32 &x31)
              (Byte.Byte_introduction &x46 &x45 &x44 &x43 &x42 &x41 &x40 &x39)
              (Byte.Byte_introduction &x54 &x53 &x52 &x51 &x50 &x49 &x48 &x47)
              (Byte.Byte_introduction &x62 &x61 &x60 &x59 &x58 &x57 &x56 &x55)))
          in |- *.
        simpl in |- *.
        quod idem est.
      * match &b0 with | Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
        match &b1 with | Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
        match &b2 with | Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
        match &b3 with | Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
        match &b4 with | Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        match &b5 with | Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b6 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b7 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        simpl in |- *.
        leibniz
          (&IH
            (DWord_introduction Endian.Big
              (Byte.Byte_introduction &x62 &x61 &x60 &x59 &x58 &x57 &x56 &x55)
              (Byte.Byte_introduction &x54 &x53 &x52 &x51 &x50 &x49 &x48 &x47)
              (Byte.Byte_introduction &x46 &x45 &x44 &x43 &x42 &x41 &x40 &x39)
              (Byte.Byte_introduction &x38 &x37 &x36 &x35 &x34 &x33 &x32 &x31)
              (Byte.Byte_introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)
              (Byte.Byte_introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.Byte_introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x63)))
          in |- *.
        simpl in |- *.
        quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : DWord) . rotate_right x 64%n0 = x.
Proof.
  intros x.
  match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
  match &b0 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b2 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &b3 with | Byte_introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
  match &b4 with | Byte_introduction t7 t6 t5 t4 t3 t2 t1 t0 end.
  match &b5 with | Byte_introduction u7 u6 u5 u4 u3 u2 u1 u0 end.
  match &b6 with | Byte_introduction v7 v6 v5 v4 v3 v2 v1 v0 end.
  match &b7 with | Byte_introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : DWord) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
      match &b0 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | Byte_introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &b4 with | Byte_introduction t7 t6 t5 t4 t3 t2 t1 t0 end.
      match &b5 with | Byte_introduction u7 u6 u5 u4 u3 u2 u1 u0 end.
      match &b6 with | Byte_introduction v7 v6 v5 v4 v3 v2 v1 v0 end.
      match &b7 with | Byte_introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
      match &b0 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b2 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &b3 with | Byte_introduction s7 s6 s5 s4 s3 s2 s1 s0 end.
      match &b4 with | Byte_introduction t7 t6 t5 t4 t3 t2 t1 t0 end.
      match &b5 with | Byte_introduction u7 u6 u5 u4 u3 u2 u1 u0 end.
      match &b6 with | Byte_introduction v7 v6 v5 v4 v3 v2 v1 v0 end.
      match &b7 with | Byte_introduction w7 w6 w5 w4 w3 w2 w1 w0 end.
      match &e with | Little | Big end; ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

Module conversion. (* conversion *)

Module bytes. (* conversion.bytes *)

(* conversion.bytes.retraction *)
Theorem retraction : forall (x : DWord) . from_bytes (endian x) (to_bytes x) = Some x.
Proof.
  intros x.
  match &x with | DWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 end.
  simpl from_bytes, to_bytes, endian in |- *.
  quod idem est.
Qed.

End bytes. (* conversion.bytes *)

End conversion. (* conversion *)

End DWord. (* DWord *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [DWord], not [DWord.T].
 *)
Abbreviation DWord := DWord.T.

(* Makes the notations declared in [Module DWord] usable in every file that
 * imports this one, as [(x &. y)%dword] or under an opened [jwa_dword_scope].
 *)
Export (notations) DWord.

(* A double word is written in hexadecimal,
 * [0x0123456789abcdef%dword_little] or [0x0123456789abcdef%dword_big] laid
 * out as the key names, and prints back the same way, in sixteen digits.
 * The plain key reads little-endian and is declared last, so a
 * little-endian double word prints as [0x0123456789abcdef%dword].
 *)
Number Notation DWord.T DWord.from_little_numeral DWord.to_little_numeral
  : jwa_dword_little_scope.
Number Notation DWord.T DWord.from_big_numeral DWord.to_big_numeral
  : jwa_dword_big_scope.
Number Notation DWord.T DWord.from_little_numeral DWord.to_little_numeral
  : jwa_dword_scope.

(* Where a [DWord] is expected, a literal or a notation reads in this scope
 * without its [%dword].
 *)
Bind Scope jwa_dword_scope with DWord.T.
