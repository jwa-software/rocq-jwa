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

Module QWord. (* QWord *)

Inductive T : Type :=
  | QWord_introduction :
      Endian ->
      Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte ->
      Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte ->
      T.

Abbreviation QWord := T.

(* [QWord -> Endian] *)
Definition endian := fun (x : QWord) .
  match x with
  | QWord_introduction e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => e
  end.

(* The least significant byte, wherever the endianness lays it; [byte1] to
 * [byte15] follow in significance.
 *)
(* [QWord -> Byte] *)
Definition byte0 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      b0  _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   => b0
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   b0  => b0
  end.

(* [QWord -> Byte] *)
Definition byte1 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   b1  _   _   _   _   _   _   _   _   _   _   _   _   _   _   => b1
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   _   _   _   _   b1  _   => b1
  end.

(* [QWord -> Byte] *)
Definition byte2 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   b2  _   _   _   _   _   _   _   _   _   _   _   _   _   => b2
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   _   _   _   b2  _   _   => b2
  end.

(* [QWord -> Byte] *)
Definition byte3 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   b3  _   _   _   _   _   _   _   _   _   _   _   _   => b3
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   _   _   b3  _   _   _   => b3
  end.

(* [QWord -> Byte] *)
Definition byte4 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   b4  _   _   _   _   _   _   _   _   _   _   _   => b4
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   _   b4  _   _   _   _   => b4
  end.

(* [QWord -> Byte] *)
Definition byte5 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   b5  _   _   _   _   _   _   _   _   _   _   => b5
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   _   b5  _   _   _   _   _   => b5
  end.

(* [QWord -> Byte] *)
Definition byte6 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   b6  _   _   _   _   _   _   _   _   _   => b6
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   _   b6  _   _   _   _   _   _   => b6
  end.

(* [QWord -> Byte] *)
Definition byte7 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   b7  _   _   _   _   _   _   _   _   => b7
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   _   b7  _   _   _   _   _   _   _   => b7
  end.

(* [QWord -> Byte] *)
Definition byte8 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   b8  _   _   _   _   _   _   _   => b8
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   _   b8  _   _   _   _   _   _   _   _   => b8
  end.

(* [QWord -> Byte] *)
Definition byte9 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   b9  _   _   _   _   _   _   => b9
  | QWord_introduction Endian.Big
      _   _   _   _   _   _   b9  _   _   _   _   _   _   _   _   _   => b9
  end.

(* [QWord -> Byte] *)
Definition byte10 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   b10 _   _   _   _   _   => b10
  | QWord_introduction Endian.Big
      _   _   _   _   _   b10 _   _   _   _   _   _   _   _   _   _   => b10
  end.

(* [QWord -> Byte] *)
Definition byte11 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   _   b11 _   _   _   _   => b11
  | QWord_introduction Endian.Big
      _   _   _   _   b11 _   _   _   _   _   _   _   _   _   _   _   => b11
  end.

(* [QWord -> Byte] *)
Definition byte12 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   _   _   b12 _   _   _   => b12
  | QWord_introduction Endian.Big
      _   _   _   b12 _   _   _   _   _   _   _   _   _   _   _   _   => b12
  end.

(* [QWord -> Byte] *)
Definition byte13 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   _   _   _   b13 _   _   => b13
  | QWord_introduction Endian.Big
      _   _   b13 _   _   _   _   _   _   _   _   _   _   _   _   _   => b13
  end.

(* [QWord -> Byte] *)
Definition byte14 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   _   _   _   _   b14 _   => b14
  | QWord_introduction Endian.Big
      _   b14 _   _   _   _   _   _   _   _   _   _   _   _   _   _   => b14
  end.

(* [QWord -> Byte] *)
Definition byte15 := fun (x : QWord) .
  match x with
  | QWord_introduction Endian.Little
      _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   b15 => b15
  | QWord_introduction Endian.Big
      b15 _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   => b15
  end.

(* The quadruple word of endianness [e] whose bytes, least significant first, are
 * [b0] to [b15], laid out in the order [e] names.
 *)
(* [Endian -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte ->
 *  Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> Byte -> QWord]
 *)
Definition make :=
  fun (e : Endian)
      (b0 : Byte) (b1 : Byte) (b2 : Byte) (b3 : Byte)
      (b4 : Byte) (b5 : Byte) (b6 : Byte) (b7 : Byte)
      (b8 : Byte) (b9 : Byte) (b10 : Byte) (b11 : Byte)
      (b12 : Byte) (b13 : Byte) (b14 : Byte) (b15 : Byte) .
  match e with
  | Endian.Little =>
      QWord_introduction Endian.Little
        b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  | Endian.Big    =>
      QWord_introduction Endian.Big
        b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0
  end.

(* The same value, laid out in the order [e] names. *)
(* [Endian -> QWord -> QWord] *)
Definition with_endian := fun (e : Endian) (x : QWord) .
  make e
    (byte0 x) (byte1 x) (byte2 x) (byte3 x) (byte4 x) (byte5 x) (byte6 x) (byte7 x)
    (byte8 x) (byte9 x) (byte10 x) (byte11 x) (byte12 x) (byte13 x) (byte14 x) (byte15 x).

(* [Endian -> QWord] *)
Definition Zero := fun (e : Endian) .
  make e
    Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero
    Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero Byte.Zero.

(* [QWord -> QWord] *)
Definition flip := fun (x : QWord) .
  make (endian x)
    (Byte.flip (byte0 x)) (Byte.flip (byte1 x)) (Byte.flip (byte2 x)) (Byte.flip (byte3 x))
    (Byte.flip (byte4 x)) (Byte.flip (byte5 x)) (Byte.flip (byte6 x)) (Byte.flip (byte7 x))
    (Byte.flip (byte8 x)) (Byte.flip (byte9 x)) (Byte.flip (byte10 x)) (Byte.flip (byte11 x))
    (Byte.flip (byte12 x)) (Byte.flip (byte13 x)) (Byte.flip (byte14 x)) (Byte.flip (byte15 x)).

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_qword_scope.

(* [x] converted to little-endian, then flipped. *)
(* [QWord -> QWord] *)
Definition flip_little_endian := fun (x : QWord) . flip (with_endian Endian.Little x).

(* [x] converted to big-endian, then flipped. *)
(* [QWord -> QWord] *)
Definition flip_big_endian := fun (x : QWord) . flip (with_endian Endian.Big x).

(* [y] converted to the endianness of [x], then combined with it byte by
 * byte: the result takes the endianness of [x].
 *)
(* [QWord -> QWord -> QWord] *)
Definition and := fun (x : QWord) (y : QWord) .
  make (endian x)
    (Byte.and (byte0 x) (byte0 y)) (Byte.and (byte1 x) (byte1 y))
    (Byte.and (byte2 x) (byte2 y)) (Byte.and (byte3 x) (byte3 y))
    (Byte.and (byte4 x) (byte4 y)) (Byte.and (byte5 x) (byte5 y))
    (Byte.and (byte6 x) (byte6 y)) (Byte.and (byte7 x) (byte7 y))
    (Byte.and (byte8 x) (byte8 y)) (Byte.and (byte9 x) (byte9 y))
    (Byte.and (byte10 x) (byte10 y)) (Byte.and (byte11 x) (byte11 y))
    (Byte.and (byte12 x) (byte12 y)) (Byte.and (byte13 x) (byte13 y))
    (Byte.and (byte14 x) (byte14 y)) (Byte.and (byte15 x) (byte15 y)).

Notation "x &. y" := (and x y) (only parsing)
  : jwa_qword_scope.

(* Both operands converted to little-endian, then combined: the result is
 * little-endian whatever theirs.
 *)
(* [QWord -> QWord -> QWord] *)
Definition and_little_endian := fun (x : QWord) (y : QWord) .
  and (with_endian Endian.Little x) y.

(* Both operands converted to big-endian, then combined: the result is
 * big-endian whatever theirs.
 *)
(* [QWord -> QWord -> QWord] *)
Definition and_big_endian := fun (x : QWord) (y : QWord) .
  and (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [QWord -> QWord -> QWord] *)
Definition or := fun (x : QWord) (y : QWord) .
  make (endian x)
    (Byte.or (byte0 x) (byte0 y)) (Byte.or (byte1 x) (byte1 y))
    (Byte.or (byte2 x) (byte2 y)) (Byte.or (byte3 x) (byte3 y))
    (Byte.or (byte4 x) (byte4 y)) (Byte.or (byte5 x) (byte5 y))
    (Byte.or (byte6 x) (byte6 y)) (Byte.or (byte7 x) (byte7 y))
    (Byte.or (byte8 x) (byte8 y)) (Byte.or (byte9 x) (byte9 y))
    (Byte.or (byte10 x) (byte10 y)) (Byte.or (byte11 x) (byte11 y))
    (Byte.or (byte12 x) (byte12 y)) (Byte.or (byte13 x) (byte13 y))
    (Byte.or (byte14 x) (byte14 y)) (Byte.or (byte15 x) (byte15 y)).

Notation "x |. y" := (or x y) (only parsing)
  : jwa_qword_scope.

(* [QWord -> QWord -> QWord] *)
Definition or_little_endian := fun (x : QWord) (y : QWord) .
  or (with_endian Endian.Little x) y.

(* [QWord -> QWord -> QWord] *)
Definition or_big_endian := fun (x : QWord) (y : QWord) .
  or (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [QWord -> QWord -> QWord] *)
Definition xor := fun (x : QWord) (y : QWord) .
  make (endian x)
    (Byte.xor (byte0 x) (byte0 y)) (Byte.xor (byte1 x) (byte1 y))
    (Byte.xor (byte2 x) (byte2 y)) (Byte.xor (byte3 x) (byte3 y))
    (Byte.xor (byte4 x) (byte4 y)) (Byte.xor (byte5 x) (byte5 y))
    (Byte.xor (byte6 x) (byte6 y)) (Byte.xor (byte7 x) (byte7 y))
    (Byte.xor (byte8 x) (byte8 y)) (Byte.xor (byte9 x) (byte9 y))
    (Byte.xor (byte10 x) (byte10 y)) (Byte.xor (byte11 x) (byte11 y))
    (Byte.xor (byte12 x) (byte12 y)) (Byte.xor (byte13 x) (byte13 y))
    (Byte.xor (byte14 x) (byte14 y)) (Byte.xor (byte15 x) (byte15 y)).

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_qword_scope.

(* [QWord -> QWord -> QWord] *)
Definition xor_little_endian := fun (x : QWord) (y : QWord) .
  xor (with_endian Endian.Little x) y.

(* [QWord -> QWord -> QWord] *)
Definition xor_big_endian := fun (x : QWord) (y : QWord) .
  xor (with_endian Endian.Big x) y.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1]. The bit leaving each
 * byte at its top enters the next byte up at its bottom, and the result
 * keeps the endianness. Each endianness has its branch, so that a step
 * takes its argument apart once: through [byte0] to [byte15] and [endian] it
 * would do so seventeen times, and [simpl] would copy the previous step into
 * each.
 *)
(* [QWord -> Nat -> QWord] *)
Fixpoint rotate_left_nat (x : QWord) (k : Nat) : QWord :=
  let y :=
    match x with
    | QWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120) =>
        QWord_introduction Endian.Little
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 x127)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.Byte_introduction x70 x69 x68 x67 x66 x65 x64 x63)
          (Byte.Byte_introduction x78 x77 x76 x75 x74 x73 x72 x71)
          (Byte.Byte_introduction x86 x85 x84 x83 x82 x81 x80 x79)
          (Byte.Byte_introduction x94 x93 x92 x91 x90 x89 x88 x87)
          (Byte.Byte_introduction x102 x101 x100 x99 x98 x97 x96 x95)
          (Byte.Byte_introduction x110 x109 x108 x107 x106 x105 x104 x103)
          (Byte.Byte_introduction x118 x117 x116 x115 x114 x113 x112 x111)
          (Byte.Byte_introduction x126 x125 x124 x123 x122 x121 x120 x119)
    | QWord_introduction Endian.Big
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        QWord_introduction Endian.Big
          (Byte.Byte_introduction x126 x125 x124 x123 x122 x121 x120 x119)
          (Byte.Byte_introduction x118 x117 x116 x115 x114 x113 x112 x111)
          (Byte.Byte_introduction x110 x109 x108 x107 x106 x105 x104 x103)
          (Byte.Byte_introduction x102 x101 x100 x99 x98 x97 x96 x95)
          (Byte.Byte_introduction x94 x93 x92 x91 x90 x89 x88 x87)
          (Byte.Byte_introduction x86 x85 x84 x83 x82 x81 x80 x79)
          (Byte.Byte_introduction x78 x77 x76 x75 x74 x73 x72 x71)
          (Byte.Byte_introduction x70 x69 x68 x67 x66 x65 x64 x63)
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 x127)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [QWord -> Nat -> QWord] *)
Fixpoint rotate_right_nat (x : QWord) (k : Nat) : QWord :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | QWord_introduction Endian.Little
      (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0)
      (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.Byte_introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.Byte_introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.Byte_introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.Byte_introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.Byte_introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.Byte_introduction y63 y62 y61 y60 y59 y58 y57 y56)
      (Byte.Byte_introduction y71 y70 y69 y68 y67 y66 y65 y64)
      (Byte.Byte_introduction y79 y78 y77 y76 y75 y74 y73 y72)
      (Byte.Byte_introduction y87 y86 y85 y84 y83 y82 y81 y80)
      (Byte.Byte_introduction y95 y94 y93 y92 y91 y90 y89 y88)
      (Byte.Byte_introduction y103 y102 y101 y100 y99 y98 y97 y96)
      (Byte.Byte_introduction y111 y110 y109 y108 y107 y106 y105 y104)
      (Byte.Byte_introduction y119 y118 y117 y116 y115 y114 y113 y112)
      (Byte.Byte_introduction y127 y126 y125 y124 y123 y122 y121 y120) =>
      QWord_introduction Endian.Little
        (Byte.Byte_introduction y8 y7 y6 y5 y4 y3 y2 y1)
        (Byte.Byte_introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.Byte_introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.Byte_introduction y32 y31 y30 y29 y28 y27 y26 y25)
        (Byte.Byte_introduction y40 y39 y38 y37 y36 y35 y34 y33)
        (Byte.Byte_introduction y48 y47 y46 y45 y44 y43 y42 y41)
        (Byte.Byte_introduction y56 y55 y54 y53 y52 y51 y50 y49)
        (Byte.Byte_introduction y64 y63 y62 y61 y60 y59 y58 y57)
        (Byte.Byte_introduction y72 y71 y70 y69 y68 y67 y66 y65)
        (Byte.Byte_introduction y80 y79 y78 y77 y76 y75 y74 y73)
        (Byte.Byte_introduction y88 y87 y86 y85 y84 y83 y82 y81)
        (Byte.Byte_introduction y96 y95 y94 y93 y92 y91 y90 y89)
        (Byte.Byte_introduction y104 y103 y102 y101 y100 y99 y98 y97)
        (Byte.Byte_introduction y112 y111 y110 y109 y108 y107 y106 y105)
        (Byte.Byte_introduction y120 y119 y118 y117 y116 y115 y114 y113)
        (Byte.Byte_introduction y0 y127 y126 y125 y124 y123 y122 y121)
  | QWord_introduction Endian.Big
      (Byte.Byte_introduction y127 y126 y125 y124 y123 y122 y121 y120)
      (Byte.Byte_introduction y119 y118 y117 y116 y115 y114 y113 y112)
      (Byte.Byte_introduction y111 y110 y109 y108 y107 y106 y105 y104)
      (Byte.Byte_introduction y103 y102 y101 y100 y99 y98 y97 y96)
      (Byte.Byte_introduction y95 y94 y93 y92 y91 y90 y89 y88)
      (Byte.Byte_introduction y87 y86 y85 y84 y83 y82 y81 y80)
      (Byte.Byte_introduction y79 y78 y77 y76 y75 y74 y73 y72)
      (Byte.Byte_introduction y71 y70 y69 y68 y67 y66 y65 y64)
      (Byte.Byte_introduction y63 y62 y61 y60 y59 y58 y57 y56)
      (Byte.Byte_introduction y55 y54 y53 y52 y51 y50 y49 y48)
      (Byte.Byte_introduction y47 y46 y45 y44 y43 y42 y41 y40)
      (Byte.Byte_introduction y39 y38 y37 y36 y35 y34 y33 y32)
      (Byte.Byte_introduction y31 y30 y29 y28 y27 y26 y25 y24)
      (Byte.Byte_introduction y23 y22 y21 y20 y19 y18 y17 y16)
      (Byte.Byte_introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      QWord_introduction Endian.Big
        (Byte.Byte_introduction y0 y127 y126 y125 y124 y123 y122 y121)
        (Byte.Byte_introduction y120 y119 y118 y117 y116 y115 y114 y113)
        (Byte.Byte_introduction y112 y111 y110 y109 y108 y107 y106 y105)
        (Byte.Byte_introduction y104 y103 y102 y101 y100 y99 y98 y97)
        (Byte.Byte_introduction y96 y95 y94 y93 y92 y91 y90 y89)
        (Byte.Byte_introduction y88 y87 y86 y85 y84 y83 y82 y81)
        (Byte.Byte_introduction y80 y79 y78 y77 y76 y75 y74 y73)
        (Byte.Byte_introduction y72 y71 y70 y69 y68 y67 y66 y65)
        (Byte.Byte_introduction y64 y63 y62 y61 y60 y59 y58 y57)
        (Byte.Byte_introduction y56 y55 y54 y53 y52 y51 y50 y49)
        (Byte.Byte_introduction y48 y47 y46 y45 y44 y43 y42 y41)
        (Byte.Byte_introduction y40 y39 y38 y37 y36 y35 y34 y33)
        (Byte.Byte_introduction y32 y31 y30 y29 y28 y27 y26 y25)
        (Byte.Byte_introduction y24 y23 y22 y21 y20 y19 y18 y17)
        (Byte.Byte_introduction y16 y15 y14 y13 y12 y11 y10 y9)
        (Byte.Byte_introduction y8 y7 y6 y5 y4 y3 y2 y1)
  end.

(* [QWord -> Nat0 -> QWord] *)
Definition rotate_left := fun (x : QWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [QWord -> Nat0 -> QWord] *)
Definition rotate_right := fun (x : QWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [Bit.Zero] coming in at the
 * other, in the order and the branches of [rotate_left_nat].
 *)
(* [QWord -> Nat -> QWord] *)
Fixpoint shift_left_nat (x : QWord) (k : Nat) : QWord :=
  let y :=
    match x with
    | QWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120) =>
        QWord_introduction Endian.Little
          (Byte.Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero)
          (Byte.Byte_introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.Byte_introduction x22 x21 x20 x19 x18 x17 x16 x15)
          (Byte.Byte_introduction x30 x29 x28 x27 x26 x25 x24 x23)
          (Byte.Byte_introduction x38 x37 x36 x35 x34 x33 x32 x31)
          (Byte.Byte_introduction x46 x45 x44 x43 x42 x41 x40 x39)
          (Byte.Byte_introduction x54 x53 x52 x51 x50 x49 x48 x47)
          (Byte.Byte_introduction x62 x61 x60 x59 x58 x57 x56 x55)
          (Byte.Byte_introduction x70 x69 x68 x67 x66 x65 x64 x63)
          (Byte.Byte_introduction x78 x77 x76 x75 x74 x73 x72 x71)
          (Byte.Byte_introduction x86 x85 x84 x83 x82 x81 x80 x79)
          (Byte.Byte_introduction x94 x93 x92 x91 x90 x89 x88 x87)
          (Byte.Byte_introduction x102 x101 x100 x99 x98 x97 x96 x95)
          (Byte.Byte_introduction x110 x109 x108 x107 x106 x105 x104 x103)
          (Byte.Byte_introduction x118 x117 x116 x115 x114 x113 x112 x111)
          (Byte.Byte_introduction x126 x125 x124 x123 x122 x121 x120 x119)
    | QWord_introduction Endian.Big
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        QWord_introduction Endian.Big
          (Byte.Byte_introduction x126 x125 x124 x123 x122 x121 x120 x119)
          (Byte.Byte_introduction x118 x117 x116 x115 x114 x113 x112 x111)
          (Byte.Byte_introduction x110 x109 x108 x107 x106 x105 x104 x103)
          (Byte.Byte_introduction x102 x101 x100 x99 x98 x97 x96 x95)
          (Byte.Byte_introduction x94 x93 x92 x91 x90 x89 x88 x87)
          (Byte.Byte_introduction x86 x85 x84 x83 x82 x81 x80 x79)
          (Byte.Byte_introduction x78 x77 x76 x75 x74 x73 x72 x71)
          (Byte.Byte_introduction x70 x69 x68 x67 x66 x65 x64 x63)
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
(* [QWord -> Nat -> QWord] *)
Fixpoint shift_right_nat (x : QWord) (k : Nat) : QWord :=
  let y :=
    match x with
    | QWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120) =>
        QWord_introduction Endian.Little
          (Byte.Byte_introduction x8 x7 x6 x5 x4 x3 x2 x1)
          (Byte.Byte_introduction x16 x15 x14 x13 x12 x11 x10 x9)
          (Byte.Byte_introduction x24 x23 x22 x21 x20 x19 x18 x17)
          (Byte.Byte_introduction x32 x31 x30 x29 x28 x27 x26 x25)
          (Byte.Byte_introduction x40 x39 x38 x37 x36 x35 x34 x33)
          (Byte.Byte_introduction x48 x47 x46 x45 x44 x43 x42 x41)
          (Byte.Byte_introduction x56 x55 x54 x53 x52 x51 x50 x49)
          (Byte.Byte_introduction x64 x63 x62 x61 x60 x59 x58 x57)
          (Byte.Byte_introduction x72 x71 x70 x69 x68 x67 x66 x65)
          (Byte.Byte_introduction x80 x79 x78 x77 x76 x75 x74 x73)
          (Byte.Byte_introduction x88 x87 x86 x85 x84 x83 x82 x81)
          (Byte.Byte_introduction x96 x95 x94 x93 x92 x91 x90 x89)
          (Byte.Byte_introduction x104 x103 x102 x101 x100 x99 x98 x97)
          (Byte.Byte_introduction x112 x111 x110 x109 x108 x107 x106 x105)
          (Byte.Byte_introduction x120 x119 x118 x117 x116 x115 x114 x113)
          (Byte.Byte_introduction Bit.Zero x127 x126 x125 x124 x123 x122 x121)
    | QWord_introduction Endian.Big
        (Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        QWord_introduction Endian.Big
          (Byte.Byte_introduction Bit.Zero x127 x126 x125 x124 x123 x122 x121)
          (Byte.Byte_introduction x120 x119 x118 x117 x116 x115 x114 x113)
          (Byte.Byte_introduction x112 x111 x110 x109 x108 x107 x106 x105)
          (Byte.Byte_introduction x104 x103 x102 x101 x100 x99 x98 x97)
          (Byte.Byte_introduction x96 x95 x94 x93 x92 x91 x90 x89)
          (Byte.Byte_introduction x88 x87 x86 x85 x84 x83 x82 x81)
          (Byte.Byte_introduction x80 x79 x78 x77 x76 x75 x74 x73)
          (Byte.Byte_introduction x72 x71 x70 x69 x68 x67 x66 x65)
          (Byte.Byte_introduction x64 x63 x62 x61 x60 x59 x58 x57)
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

(* [QWord -> Nat0 -> QWord] *)
Definition shift_left := fun (x : QWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [QWord -> Nat0 -> QWord] *)
Definition shift_right := fun (x : QWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* The sixteen bytes in the order they are laid out. *)
(* [QWord -> List Byte] *)
Definition to_bytes := fun (x : QWord) .
  match x with
  | QWord_introduction _ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
      List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3
        (List.Cons b4 (List.Cons b5 (List.Cons b6 (List.Cons b7
        (List.Cons b8 (List.Cons b9 (List.Cons b10 (List.Cons b11
        (List.Cons b12 (List.Cons b13 (List.Cons b14 (List.Cons b15 List.Nil)))))))))))))))
  end.

(* The quadruple word of endianness [e] laid out as the bytes of [l], or [None] for a
 * list of any length but sixteen.
 *)
(* [Endian -> List Byte -> Option QWord] *)
Definition from_bytes := fun (e : Endian) (l : List Byte) .
  match l with
  | List.Cons b0 (List.Cons b1 (List.Cons b2 (List.Cons b3
      (List.Cons b4 (List.Cons b5 (List.Cons b6 (List.Cons b7
      (List.Cons b8 (List.Cons b9 (List.Cons b10 (List.Cons b11
      (List.Cons b12 (List.Cons b13 (List.Cons b14 (List.Cons b15 List.Nil))))))))))))))) =>
      Some (QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)
  | _ =>
      None
  end.

(* [x] with the four bits of a hexadecimal digit shifted in at the least
 * significant end, or [None] when that would push a 1 out at the other, so
 * that a literal past thirty-two significant digits is refused; one branch per
 * endianness, as [rotate_left_nat].
 *)
(* [Option QWord -> Bit -> Bit -> Bit -> Bit -> Option QWord] *)
Definition append_digit := fun (x : Option QWord) (d3 : Bit) (d2 : Bit) (d1 : Bit) (d0 : Bit) .
  match x with
  | Some
      (QWord_introduction Endian.Little
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x123 x122 x121 x120)) =>
      Some
        (QWord_introduction Endian.Little
          (Byte.Byte_introduction x3 x2 x1 x0 d3 d2 d1 d0)
          (Byte.Byte_introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.Byte_introduction x19 x18 x17 x16 x15 x14 x13 x12)
          (Byte.Byte_introduction x27 x26 x25 x24 x23 x22 x21 x20)
          (Byte.Byte_introduction x35 x34 x33 x32 x31 x30 x29 x28)
          (Byte.Byte_introduction x43 x42 x41 x40 x39 x38 x37 x36)
          (Byte.Byte_introduction x51 x50 x49 x48 x47 x46 x45 x44)
          (Byte.Byte_introduction x59 x58 x57 x56 x55 x54 x53 x52)
          (Byte.Byte_introduction x67 x66 x65 x64 x63 x62 x61 x60)
          (Byte.Byte_introduction x75 x74 x73 x72 x71 x70 x69 x68)
          (Byte.Byte_introduction x83 x82 x81 x80 x79 x78 x77 x76)
          (Byte.Byte_introduction x91 x90 x89 x88 x87 x86 x85 x84)
          (Byte.Byte_introduction x99 x98 x97 x96 x95 x94 x93 x92)
          (Byte.Byte_introduction x107 x106 x105 x104 x103 x102 x101 x100)
          (Byte.Byte_introduction x115 x114 x113 x112 x111 x110 x109 x108)
          (Byte.Byte_introduction x123 x122 x121 x120 x119 x118 x117 x116))
  | Some
      (QWord_introduction Endian.Big
        (Byte.Byte_introduction Bit.Zero Bit.Zero Bit.Zero Bit.Zero x123 x122 x121 x120)
        (Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112)
        (Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104)
        (Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96)
        (Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88)
        (Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80)
        (Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72)
        (Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64)
        (Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56)
        (Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48)
        (Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40)
        (Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32)
        (Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24)
        (Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16)
        (Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0)) =>
      Some
        (QWord_introduction Endian.Big
          (Byte.Byte_introduction x123 x122 x121 x120 x119 x118 x117 x116)
          (Byte.Byte_introduction x115 x114 x113 x112 x111 x110 x109 x108)
          (Byte.Byte_introduction x107 x106 x105 x104 x103 x102 x101 x100)
          (Byte.Byte_introduction x99 x98 x97 x96 x95 x94 x93 x92)
          (Byte.Byte_introduction x91 x90 x89 x88 x87 x86 x85 x84)
          (Byte.Byte_introduction x83 x82 x81 x80 x79 x78 x77 x76)
          (Byte.Byte_introduction x75 x74 x73 x72 x71 x70 x69 x68)
          (Byte.Byte_introduction x67 x66 x65 x64 x63 x62 x61 x60)
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
(* [Option QWord -> Numeral.Hexadecimal.Digits -> Option QWord] *)
Fixpoint from_hexadecimal (x : Option QWord) (h : Numeral.Hexadecimal.Digits) : Option QWord :=
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
 * order [e] names; a decimal one is refused, since a quadruple word is bits and not a
 * number.
 *)
(* [Endian -> Numeral.Unsigned -> Option QWord] *)
Definition from_numeral := fun (e : Endian) (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal _     => None
  | Numeral.Unsigned.Hexadecimal h => from_hexadecimal (Some (Zero e)) h
  end.

(* [Numeral.Unsigned -> Option QWord] *)
Definition from_little_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Little u.

(* [Numeral.Unsigned -> Option QWord] *)
Definition from_big_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Big u.

(* [x] as a literal of thirty-two hexadecimal digits, the most significant byte's
 * first, when its endianness is [e], and [None] otherwise, so that a
 * literal scope prints only the quadruple words it reads back.
 *)
(* [Endian -> QWord -> Option Numeral.Unsigned] *)
Definition to_numeral := fun (e : Endian) (x : QWord) .
  let digits :=
    match byte0 x, byte1 x, byte2 x, byte3 x,
          byte4 x, byte5 x, byte6 x, byte7 x,
          byte8 x, byte9 x, byte10 x, byte11 x,
          byte12 x, byte13 x, byte14 x, byte15 x with
    | Byte.Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0,
      Byte.Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8,
      Byte.Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16,
      Byte.Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24,
      Byte.Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32,
      Byte.Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40,
      Byte.Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48,
      Byte.Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56,
      Byte.Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64,
      Byte.Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72,
      Byte.Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80,
      Byte.Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88,
      Byte.Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96,
      Byte.Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104,
      Byte.Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112,
      Byte.Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120 =>
        Numeral.Unsigned.Hexadecimal
          (Byte.hexadecimal_digit x127 x126 x125 x124
          (Byte.hexadecimal_digit x123 x122 x121 x120
          (Byte.hexadecimal_digit x119 x118 x117 x116
          (Byte.hexadecimal_digit x115 x114 x113 x112
          (Byte.hexadecimal_digit x111 x110 x109 x108
          (Byte.hexadecimal_digit x107 x106 x105 x104
          (Byte.hexadecimal_digit x103 x102 x101 x100
          (Byte.hexadecimal_digit x99 x98 x97 x96
          (Byte.hexadecimal_digit x95 x94 x93 x92
          (Byte.hexadecimal_digit x91 x90 x89 x88
          (Byte.hexadecimal_digit x87 x86 x85 x84
          (Byte.hexadecimal_digit x83 x82 x81 x80
          (Byte.hexadecimal_digit x79 x78 x77 x76
          (Byte.hexadecimal_digit x75 x74 x73 x72
          (Byte.hexadecimal_digit x71 x70 x69 x68
          (Byte.hexadecimal_digit x67 x66 x65 x64
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
          Numeral.Hexadecimal.Digits.End))))))))))))))))))))))))))))))))
    end in
  match e, endian x with
  | Endian.Little, Endian.Little => Some digits
  | Endian.Big, Endian.Big       => Some digits
  | _, _                         => None
  end.

(* [QWord -> Option Numeral.Unsigned] *)
Definition to_little_numeral := fun (x : QWord) . to_numeral Endian.Little x.

(* [QWord -> Option Numeral.Unsigned] *)
Definition to_big_numeral := fun (x : QWord) . to_numeral Endian.Big x.

Local Open Scope jwa_qword_scope.

(* Equal bytes in each place make equal quadruple words of one endianness; each law
 * below is its [Byte] counterpart taken byte by byte through this.
 *)
(* congruence *)
Lemma congruence
  : forall {e : Endian} {a0 : Byte} {a1 : Byte} {a2 : Byte} {a3 : Byte}
      {a4 : Byte} {a5 : Byte} {a6 : Byte} {a7 : Byte}
      {a8 : Byte} {a9 : Byte} {a10 : Byte} {a11 : Byte}
      {a12 : Byte} {a13 : Byte} {a14 : Byte} {a15 : Byte}
      {b0 : Byte} {b1 : Byte} {b2 : Byte} {b3 : Byte}
      {b4 : Byte} {b5 : Byte} {b6 : Byte} {b7 : Byte}
      {b8 : Byte} {b9 : Byte} {b10 : Byte} {b11 : Byte}
      {b12 : Byte} {b13 : Byte} {b14 : Byte} {b15 : Byte} .
      a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 ->
      a4 = b4 -> a5 = b5 -> a6 = b6 -> a7 = b7 ->
      a8 = b8 -> a9 = b9 -> a10 = b10 -> a11 = b11 ->
      a12 = b12 -> a13 = b13 -> a14 = b14 -> a15 = b15 ->
      QWord_introduction e a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
        = QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15.
Proof.
  intros e
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
  leibniz
    &e0, &e1, &e2, &e3, &e4, &e5, &e6, &e7,
    &e8, &e9, &e10, &e11, &e12, &e13, &e14, &e15
    in |- *.
  quod idem est.
Qed.

Module endianness. (* endianness *)

(* endianness.specification *)
Theorem specification : forall (e : Endian) (x : QWord) . endian (with_endian e x) = e.
Proof.
  intros e x.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.identity *)
Theorem identity : forall (x : QWord) . with_endian (endian x) x = x.
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.absorption *)
Theorem absorption
  : forall (e : Endian) (f : Endian) (x : QWord) .
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
Theorem involution : forall (x : QWord) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end;
    simpl flip in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.flipping.involution &x0) (Byte.flipping.involution &x1)
        (Byte.flipping.involution &x2) (Byte.flipping.involution &x3)
        (Byte.flipping.involution &x4) (Byte.flipping.involution &x5)
        (Byte.flipping.involution &x6) (Byte.flipping.involution &x7)
        (Byte.flipping.involution &x8) (Byte.flipping.involution &x9)
        (Byte.flipping.involution &x10) (Byte.flipping.involution &x11)
        (Byte.flipping.involution &x12) (Byte.flipping.involution &x13)
        (Byte.flipping.involution &x14) (Byte.flipping.involution &x15)).
Qed.

Module endian. (* flipping.endian *)

Module little. (* flipping.endian.little *)

(* flipping.endian.little.specification *)
Theorem specification : forall (x : QWord) . endian (flip_little_endian x) = Endian.Little.
Proof.
  intros x.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* flipping.endian.little *)

Module big. (* flipping.endian.big *)

(* flipping.endian.big.specification *)
Theorem specification : forall (x : QWord) . endian (flip_big_endian x) = Endian.Big.
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
  match &z with | QWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 end.
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
        (Byte.conjunction.associativity _ _ _)
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
  : forall (x : QWord) . (~. Zero (endian x) &. x = x) /\ (x &. ~. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match (Byte.conjunction.identity &x0) with | left0 right0 end.
  match (Byte.conjunction.identity &x1) with | left1 right1 end.
  match (Byte.conjunction.identity &x2) with | left2 right2 end.
  match (Byte.conjunction.identity &x3) with | left3 right3 end.
  match (Byte.conjunction.identity &x4) with | left4 right4 end.
  match (Byte.conjunction.identity &x5) with | left5 right5 end.
  match (Byte.conjunction.identity &x6) with | left6 right6 end.
  match (Byte.conjunction.identity &x7) with | left7 right7 end.
  match (Byte.conjunction.identity &x8) with | left8 right8 end.
  match (Byte.conjunction.identity &x9) with | left9 right9 end.
  match (Byte.conjunction.identity &x10) with | left10 right10 end.
  match (Byte.conjunction.identity &x11) with | left11 right11 end.
  match (Byte.conjunction.identity &x12) with | left12 right12 end.
  match (Byte.conjunction.identity &x13) with | left13 right13 end.
  match (Byte.conjunction.identity &x14) with | left14 right14 end.
  match (Byte.conjunction.identity &x15) with | left15 right15 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
Qed.

Module endian. (* conjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* conjunction.endian.conversion *)
Theorem conversion
  : forall (x : QWord) (y : QWord) . x &. y = x &. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end;
    simpl and, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* conjunction.endian.little *)

(* conjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.conjunction.commutativity &x7 &y7)
      (Byte.conjunction.commutativity &x8 &y8)
      (Byte.conjunction.commutativity &x9 &y9)
      (Byte.conjunction.commutativity &x10 &y10)
      (Byte.conjunction.commutativity &x11 &y11)
      (Byte.conjunction.commutativity &x12 &y12)
      (Byte.conjunction.commutativity &x13 &y13)
      (Byte.conjunction.commutativity &x14 &y14)
      (Byte.conjunction.commutativity &x15 &y15)).
Qed.

(* conjunction.endian.little.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (and_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* conjunction.endian.little *)

Module big. (* conjunction.endian.big *)

(* conjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.conjunction.commutativity &x7 &y7)
      (Byte.conjunction.commutativity &x8 &y8)
      (Byte.conjunction.commutativity &x9 &y9)
      (Byte.conjunction.commutativity &x10 &y10)
      (Byte.conjunction.commutativity &x11 &y11)
      (Byte.conjunction.commutativity &x12 &y12)
      (Byte.conjunction.commutativity &x13 &y13)
      (Byte.conjunction.commutativity &x14 &y14)
      (Byte.conjunction.commutativity &x15 &y15)).
Qed.

(* conjunction.endian.big.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (and_big_endian x y) = Endian.Big.
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
  match &z with | QWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 end.
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
        (Byte.conjunction.left.distributivity.over.sejunction _ _ _)
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
  match &z with | QWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 end.
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
        (Byte.conjunction.right.distributivity.over.sejunction _ _ _)
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
  match &z with | QWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 end.
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
        (Byte.disjunction.associativity _ _ _)
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
  : forall (x : QWord) . (Zero (endian x) |. x = x) /\ (x |. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match (Byte.disjunction.identity &x0) with | left0 right0 end.
  match (Byte.disjunction.identity &x1) with | left1 right1 end.
  match (Byte.disjunction.identity &x2) with | left2 right2 end.
  match (Byte.disjunction.identity &x3) with | left3 right3 end.
  match (Byte.disjunction.identity &x4) with | left4 right4 end.
  match (Byte.disjunction.identity &x5) with | left5 right5 end.
  match (Byte.disjunction.identity &x6) with | left6 right6 end.
  match (Byte.disjunction.identity &x7) with | left7 right7 end.
  match (Byte.disjunction.identity &x8) with | left8 right8 end.
  match (Byte.disjunction.identity &x9) with | left9 right9 end.
  match (Byte.disjunction.identity &x10) with | left10 right10 end.
  match (Byte.disjunction.identity &x11) with | left11 right11 end.
  match (Byte.disjunction.identity &x12) with | left12 right12 end.
  match (Byte.disjunction.identity &x13) with | left13 right13 end.
  match (Byte.disjunction.identity &x14) with | left14 right14 end.
  match (Byte.disjunction.identity &x15) with | left15 right15 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
Qed.

Module endian. (* disjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* disjunction.endian.conversion *)
Theorem conversion
  : forall (x : QWord) (y : QWord) . x |. y = x |. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end;
    simpl or, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* disjunction.endian.little *)

(* disjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.disjunction.commutativity &x7 &y7)
      (Byte.disjunction.commutativity &x8 &y8)
      (Byte.disjunction.commutativity &x9 &y9)
      (Byte.disjunction.commutativity &x10 &y10)
      (Byte.disjunction.commutativity &x11 &y11)
      (Byte.disjunction.commutativity &x12 &y12)
      (Byte.disjunction.commutativity &x13 &y13)
      (Byte.disjunction.commutativity &x14 &y14)
      (Byte.disjunction.commutativity &x15 &y15)).
Qed.

(* disjunction.endian.little.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (or_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* disjunction.endian.little *)

Module big. (* disjunction.endian.big *)

(* disjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.disjunction.commutativity &x7 &y7)
      (Byte.disjunction.commutativity &x8 &y8)
      (Byte.disjunction.commutativity &x9 &y9)
      (Byte.disjunction.commutativity &x10 &y10)
      (Byte.disjunction.commutativity &x11 &y11)
      (Byte.disjunction.commutativity &x12 &y12)
      (Byte.disjunction.commutativity &x13 &y13)
      (Byte.disjunction.commutativity &x14 &y14)
      (Byte.disjunction.commutativity &x15 &y15)).
Qed.

(* disjunction.endian.big.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (or_big_endian x y) = Endian.Big.
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
  : forall (x : QWord) (y : QWord) (z : QWord) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
  match &z with | QWord_introduction ez z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 end.
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
        (Byte.sejunction.associativity _ _ _)
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
  : forall (x : QWord) . (Zero (endian x) ^. x = x) /\ (x ^. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match (Byte.sejunction.identity &x0) with | left0 right0 end.
  match (Byte.sejunction.identity &x1) with | left1 right1 end.
  match (Byte.sejunction.identity &x2) with | left2 right2 end.
  match (Byte.sejunction.identity &x3) with | left3 right3 end.
  match (Byte.sejunction.identity &x4) with | left4 right4 end.
  match (Byte.sejunction.identity &x5) with | left5 right5 end.
  match (Byte.sejunction.identity &x6) with | left6 right6 end.
  match (Byte.sejunction.identity &x7) with | left7 right7 end.
  match (Byte.sejunction.identity &x8) with | left8 right8 end.
  match (Byte.sejunction.identity &x9) with | left9 right9 end.
  match (Byte.sejunction.identity &x10) with | left10 right10 end.
  match (Byte.sejunction.identity &x11) with | left11 right11 end.
  match (Byte.sejunction.identity &x12) with | left12 right12 end.
  match (Byte.sejunction.identity &x13) with | left13 right13 end.
  match (Byte.sejunction.identity &x14) with | left14 right14 end.
  match (Byte.sejunction.identity &x15) with | left15 right15 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
  - divide et impera.
    + ipso
        (congruence
          &left0 &left1 &left2 &left3 &left4 &left5 &left6 &left7
          &left8 &left9 &left10 &left11 &left12 &left13 &left14 &left15).
    + ipso
        (congruence
          &right0 &right1 &right2 &right3 &right4 &right5 &right6 &right7
          &right8 &right9 &right10 &right11 &right12 &right13 &right14 &right15).
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : QWord) . x ^. x = Zero (endian x).
Proof.
  intros x.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end;
    ipso
      (congruence
        (Byte.sejunction.irreflexivity &x0) (Byte.sejunction.irreflexivity &x1)
        (Byte.sejunction.irreflexivity &x2) (Byte.sejunction.irreflexivity &x3)
        (Byte.sejunction.irreflexivity &x4) (Byte.sejunction.irreflexivity &x5)
        (Byte.sejunction.irreflexivity &x6) (Byte.sejunction.irreflexivity &x7)
        (Byte.sejunction.irreflexivity &x8) (Byte.sejunction.irreflexivity &x9)
        (Byte.sejunction.irreflexivity &x10) (Byte.sejunction.irreflexivity &x11)
        (Byte.sejunction.irreflexivity &x12) (Byte.sejunction.irreflexivity &x13)
        (Byte.sejunction.irreflexivity &x14) (Byte.sejunction.irreflexivity &x15)).
Qed.

Module endian. (* sejunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* sejunction.endian.conversion *)
Theorem conversion
  : forall (x : QWord) (y : QWord) . x ^. y = x ^. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | QWord_introduction e x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &e with | Little | Big end;
    simpl xor, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* sejunction.endian.little *)

(* sejunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.sejunction.commutativity &x7 &y7)
      (Byte.sejunction.commutativity &x8 &y8)
      (Byte.sejunction.commutativity &x9 &y9)
      (Byte.sejunction.commutativity &x10 &y10)
      (Byte.sejunction.commutativity &x11 &y11)
      (Byte.sejunction.commutativity &x12 &y12)
      (Byte.sejunction.commutativity &x13 &y13)
      (Byte.sejunction.commutativity &x14 &y14)
      (Byte.sejunction.commutativity &x15 &y15)).
Qed.

(* sejunction.endian.little.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (xor_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* sejunction.endian.little *)

Module big. (* sejunction.endian.big *)

(* sejunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : QWord) (y : QWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | QWord_introduction ex x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 end.
  match &y with | QWord_introduction ey y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 end.
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
      (Byte.sejunction.commutativity &x7 &y7)
      (Byte.sejunction.commutativity &x8 &y8)
      (Byte.sejunction.commutativity &x9 &y9)
      (Byte.sejunction.commutativity &x10 &y10)
      (Byte.sejunction.commutativity &x11 &y11)
      (Byte.sejunction.commutativity &x12 &y12)
      (Byte.sejunction.commutativity &x13 &y13)
      (Byte.sejunction.commutativity &x14 &y14)
      (Byte.sejunction.commutativity &x15 &y15)).
Qed.

(* sejunction.endian.big.specification *)
Theorem specification
  : forall (x : QWord) (y : QWord) . endian (xor_big_endian x y) = Endian.Big.
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
Theorem period : forall (x : QWord) . rotate_left x 128%n0 = x.
Proof.
  intros x.
  match &x with | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
  match &b0 with | Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0 end.
  match &b1 with | Byte_introduction c7 c6 c5 c4 c3 c2 c1 c0 end.
  match &b2 with | Byte_introduction d7 d6 d5 d4 d3 d2 d1 d0 end.
  match &b3 with | Byte_introduction f7 f6 f5 f4 f3 f2 f1 f0 end.
  match &b4 with | Byte_introduction g7 g6 g5 g4 g3 g2 g1 g0 end.
  match &b5 with | Byte_introduction h7 h6 h5 h4 h3 h2 h1 h0 end.
  match &b6 with | Byte_introduction i7 i6 i5 i4 i3 i2 i1 i0 end.
  match &b7 with | Byte_introduction j7 j6 j5 j4 j3 j2 j1 j0 end.
  match &b8 with | Byte_introduction k7 k6 k5 k4 k3 k2 k1 k0 end.
  match &b9 with | Byte_introduction l7 l6 l5 l4 l3 l2 l1 l0 end.
  match &b10 with | Byte_introduction m7 m6 m5 m4 m3 m2 m1 m0 end.
  match &b11 with | Byte_introduction n7 n6 n5 n4 n3 n2 n1 n0 end.
  match &b12 with | Byte_introduction o7 o6 o5 o4 o3 o2 o1 o0 end.
  match &b13 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b14 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b15 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : QWord) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with
      | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
      match &b0 with | Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0 end.
      match &b1 with | Byte_introduction c7 c6 c5 c4 c3 c2 c1 c0 end.
      match &b2 with | Byte_introduction d7 d6 d5 d4 d3 d2 d1 d0 end.
      match &b3 with | Byte_introduction f7 f6 f5 f4 f3 f2 f1 f0 end.
      match &b4 with | Byte_introduction g7 g6 g5 g4 g3 g2 g1 g0 end.
      match &b5 with | Byte_introduction h7 h6 h5 h4 h3 h2 h1 h0 end.
      match &b6 with | Byte_introduction i7 i6 i5 i4 i3 i2 i1 i0 end.
      match &b7 with | Byte_introduction j7 j6 j5 j4 j3 j2 j1 j0 end.
      match &b8 with | Byte_introduction k7 k6 k5 k4 k3 k2 k1 k0 end.
      match &b9 with | Byte_introduction l7 l6 l5 l4 l3 l2 l1 l0 end.
      match &b10 with | Byte_introduction m7 m6 m5 m4 m3 m2 m1 m0 end.
      match &b11 with | Byte_introduction n7 n6 n5 n4 n3 n2 n1 n0 end.
      match &b12 with | Byte_introduction o7 o6 o5 o4 o3 o2 o1 o0 end.
      match &b13 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b14 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b15 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + intros x.
      match &x with
      | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
      match &e with | Little | Big end.
      * match &b0 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        match &b1 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b2 with | Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b3 with | Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        match &b4 with | Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
        match &b5 with | Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
        match &b6 with | Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
        match &b7 with | Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
        match &b8 with | Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64 end.
        match &b9 with | Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72 end.
        match &b10 with | Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80 end.
        match &b11 with | Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88 end.
        match &b12 with | Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96 end.
        match &b13 with | Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104 end.
        match &b14 with | Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112 end.
        match &b15 with | Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120 end.
        simpl in |- *.
        leibniz
          (&IH
            (QWord_introduction Endian.Little
              (Byte.Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x127)
              (Byte.Byte_introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.Byte_introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.Byte_introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)
              (Byte.Byte_introduction &x38 &x37 &x36 &x35 &x34 &x33 &x32 &x31)
              (Byte.Byte_introduction &x46 &x45 &x44 &x43 &x42 &x41 &x40 &x39)
              (Byte.Byte_introduction &x54 &x53 &x52 &x51 &x50 &x49 &x48 &x47)
              (Byte.Byte_introduction &x62 &x61 &x60 &x59 &x58 &x57 &x56 &x55)
              (Byte.Byte_introduction &x70 &x69 &x68 &x67 &x66 &x65 &x64 &x63)
              (Byte.Byte_introduction &x78 &x77 &x76 &x75 &x74 &x73 &x72 &x71)
              (Byte.Byte_introduction &x86 &x85 &x84 &x83 &x82 &x81 &x80 &x79)
              (Byte.Byte_introduction &x94 &x93 &x92 &x91 &x90 &x89 &x88 &x87)
              (Byte.Byte_introduction &x102 &x101 &x100 &x99 &x98 &x97 &x96 &x95)
              (Byte.Byte_introduction &x110 &x109 &x108 &x107 &x106 &x105 &x104 &x103)
              (Byte.Byte_introduction &x118 &x117 &x116 &x115 &x114 &x113 &x112 &x111)
              (Byte.Byte_introduction &x126 &x125 &x124 &x123 &x122 &x121 &x120 &x119)))
          in |- *.
        simpl in |- *.
        quod idem est.
      * match &b0 with | Byte_introduction x127 x126 x125 x124 x123 x122 x121 x120 end.
        match &b1 with | Byte_introduction x119 x118 x117 x116 x115 x114 x113 x112 end.
        match &b2 with | Byte_introduction x111 x110 x109 x108 x107 x106 x105 x104 end.
        match &b3 with | Byte_introduction x103 x102 x101 x100 x99 x98 x97 x96 end.
        match &b4 with | Byte_introduction x95 x94 x93 x92 x91 x90 x89 x88 end.
        match &b5 with | Byte_introduction x87 x86 x85 x84 x83 x82 x81 x80 end.
        match &b6 with | Byte_introduction x79 x78 x77 x76 x75 x74 x73 x72 end.
        match &b7 with | Byte_introduction x71 x70 x69 x68 x67 x66 x65 x64 end.
        match &b8 with | Byte_introduction x63 x62 x61 x60 x59 x58 x57 x56 end.
        match &b9 with | Byte_introduction x55 x54 x53 x52 x51 x50 x49 x48 end.
        match &b10 with | Byte_introduction x47 x46 x45 x44 x43 x42 x41 x40 end.
        match &b11 with | Byte_introduction x39 x38 x37 x36 x35 x34 x33 x32 end.
        match &b12 with | Byte_introduction x31 x30 x29 x28 x27 x26 x25 x24 end.
        match &b13 with | Byte_introduction x23 x22 x21 x20 x19 x18 x17 x16 end.
        match &b14 with | Byte_introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b15 with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        simpl in |- *.
        leibniz
          (&IH
            (QWord_introduction Endian.Big
              (Byte.Byte_introduction &x126 &x125 &x124 &x123 &x122 &x121 &x120 &x119)
              (Byte.Byte_introduction &x118 &x117 &x116 &x115 &x114 &x113 &x112 &x111)
              (Byte.Byte_introduction &x110 &x109 &x108 &x107 &x106 &x105 &x104 &x103)
              (Byte.Byte_introduction &x102 &x101 &x100 &x99 &x98 &x97 &x96 &x95)
              (Byte.Byte_introduction &x94 &x93 &x92 &x91 &x90 &x89 &x88 &x87)
              (Byte.Byte_introduction &x86 &x85 &x84 &x83 &x82 &x81 &x80 &x79)
              (Byte.Byte_introduction &x78 &x77 &x76 &x75 &x74 &x73 &x72 &x71)
              (Byte.Byte_introduction &x70 &x69 &x68 &x67 &x66 &x65 &x64 &x63)
              (Byte.Byte_introduction &x62 &x61 &x60 &x59 &x58 &x57 &x56 &x55)
              (Byte.Byte_introduction &x54 &x53 &x52 &x51 &x50 &x49 &x48 &x47)
              (Byte.Byte_introduction &x46 &x45 &x44 &x43 &x42 &x41 &x40 &x39)
              (Byte.Byte_introduction &x38 &x37 &x36 &x35 &x34 &x33 &x32 &x31)
              (Byte.Byte_introduction &x30 &x29 &x28 &x27 &x26 &x25 &x24 &x23)
              (Byte.Byte_introduction &x22 &x21 &x20 &x19 &x18 &x17 &x16 &x15)
              (Byte.Byte_introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x127)))
          in |- *.
        simpl in |- *.
        quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : QWord) . rotate_right x 128%n0 = x.
Proof.
  intros x.
  match &x with | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
  match &b0 with | Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0 end.
  match &b1 with | Byte_introduction c7 c6 c5 c4 c3 c2 c1 c0 end.
  match &b2 with | Byte_introduction d7 d6 d5 d4 d3 d2 d1 d0 end.
  match &b3 with | Byte_introduction f7 f6 f5 f4 f3 f2 f1 f0 end.
  match &b4 with | Byte_introduction g7 g6 g5 g4 g3 g2 g1 g0 end.
  match &b5 with | Byte_introduction h7 h6 h5 h4 h3 h2 h1 h0 end.
  match &b6 with | Byte_introduction i7 i6 i5 i4 i3 i2 i1 i0 end.
  match &b7 with | Byte_introduction j7 j6 j5 j4 j3 j2 j1 j0 end.
  match &b8 with | Byte_introduction k7 k6 k5 k4 k3 k2 k1 k0 end.
  match &b9 with | Byte_introduction l7 l6 l5 l4 l3 l2 l1 l0 end.
  match &b10 with | Byte_introduction m7 m6 m5 m4 m3 m2 m1 m0 end.
  match &b11 with | Byte_introduction n7 n6 n5 n4 n3 n2 n1 n0 end.
  match &b12 with | Byte_introduction o7 o6 o5 o4 o3 o2 o1 o0 end.
  match &b13 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b14 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &b15 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : QWord) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with
      | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
      match &b0 with | Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0 end.
      match &b1 with | Byte_introduction c7 c6 c5 c4 c3 c2 c1 c0 end.
      match &b2 with | Byte_introduction d7 d6 d5 d4 d3 d2 d1 d0 end.
      match &b3 with | Byte_introduction f7 f6 f5 f4 f3 f2 f1 f0 end.
      match &b4 with | Byte_introduction g7 g6 g5 g4 g3 g2 g1 g0 end.
      match &b5 with | Byte_introduction h7 h6 h5 h4 h3 h2 h1 h0 end.
      match &b6 with | Byte_introduction i7 i6 i5 i4 i3 i2 i1 i0 end.
      match &b7 with | Byte_introduction j7 j6 j5 j4 j3 j2 j1 j0 end.
      match &b8 with | Byte_introduction k7 k6 k5 k4 k3 k2 k1 k0 end.
      match &b9 with | Byte_introduction l7 l6 l5 l4 l3 l2 l1 l0 end.
      match &b10 with | Byte_introduction m7 m6 m5 m4 m3 m2 m1 m0 end.
      match &b11 with | Byte_introduction n7 n6 n5 n4 n3 n2 n1 n0 end.
      match &b12 with | Byte_introduction o7 o6 o5 o4 o3 o2 o1 o0 end.
      match &b13 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b14 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b15 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with
      | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
      match &b0 with | Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0 end.
      match &b1 with | Byte_introduction c7 c6 c5 c4 c3 c2 c1 c0 end.
      match &b2 with | Byte_introduction d7 d6 d5 d4 d3 d2 d1 d0 end.
      match &b3 with | Byte_introduction f7 f6 f5 f4 f3 f2 f1 f0 end.
      match &b4 with | Byte_introduction g7 g6 g5 g4 g3 g2 g1 g0 end.
      match &b5 with | Byte_introduction h7 h6 h5 h4 h3 h2 h1 h0 end.
      match &b6 with | Byte_introduction i7 i6 i5 i4 i3 i2 i1 i0 end.
      match &b7 with | Byte_introduction j7 j6 j5 j4 j3 j2 j1 j0 end.
      match &b8 with | Byte_introduction k7 k6 k5 k4 k3 k2 k1 k0 end.
      match &b9 with | Byte_introduction l7 l6 l5 l4 l3 l2 l1 l0 end.
      match &b10 with | Byte_introduction m7 m6 m5 m4 m3 m2 m1 m0 end.
      match &b11 with | Byte_introduction n7 n6 n5 n4 n3 n2 n1 n0 end.
      match &b12 with | Byte_introduction o7 o6 o5 o4 o3 o2 o1 o0 end.
      match &b13 with | Byte_introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b14 with | Byte_introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &b15 with | Byte_introduction r7 r6 r5 r4 r3 r2 r1 r0 end.
      match &e with | Little | Big end; ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

Module conversion. (* conversion *)

Module bytes. (* conversion.bytes *)

(* conversion.bytes.retraction *)
Theorem retraction : forall (x : QWord) . from_bytes (endian x) (to_bytes x) = Some x.
Proof.
  intros x.
  match &x with | QWord_introduction e b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 end.
  simpl from_bytes, to_bytes, endian in |- *.
  quod idem est.
Qed.

End bytes. (* conversion.bytes *)

End conversion. (* conversion *)

End QWord. (* QWord *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [QWord], not [QWord.T].
 *)
Abbreviation QWord := QWord.T.

(* Makes the notations declared in [Module QWord] usable in every file that
 * imports this one, as [(x &. y)%qword] or under an opened [jwa_qword_scope].
 *)
Export (notations) QWord.

(* A quadruple word is written in hexadecimal, in up to thirty-two digits
 * under [%qword_little] or [%qword_big] laid out as the key names, and
 * prints back the same way, in thirty-two digits. The plain key reads
 * little-endian and is declared last, so a little-endian quadruple word
 * prints under [%qword].
 *)
Number Notation QWord.T QWord.from_little_numeral QWord.to_little_numeral
  : jwa_qword_little_scope.
Number Notation QWord.T QWord.from_big_numeral QWord.to_big_numeral
  : jwa_qword_big_scope.
Number Notation QWord.T QWord.from_little_numeral QWord.to_little_numeral
  : jwa_qword_scope.

(* Where a [QWord] is expected, a literal or a notation reads in this scope
 * without its [%qword].
 *)
Bind Scope jwa_qword_scope with QWord.T.
