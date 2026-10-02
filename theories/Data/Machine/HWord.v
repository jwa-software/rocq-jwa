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

Module HWord. (* HWord *)

Inductive T : Type :=
  | introduction : Endian -> Byte -> Byte -> T.

Abbreviation HWord := T.

(* [HWord -> Endian] *)
Definition endian := fun (x : HWord) .
  match x with
  | HWord.introduction e _ _ => e
  end.

(* The least significant byte, wherever the endianness lays it. *)
(* [HWord -> Byte] *)
Definition low := fun (x : HWord) .
  match x with
  | HWord.introduction Endian.Little b0 _  => b0
  | HWord.introduction Endian.Big    _  b1 => b1
  end.

(* The most significant byte, wherever the endianness lays it. *)
(* [HWord -> Byte] *)
Definition high := fun (x : HWord) .
  match x with
  | HWord.introduction Endian.Little _  b1 => b1
  | HWord.introduction Endian.Big    b0 _  => b0
  end.

(* The half word of endianness [e] whose least significant byte is [l] and
 * most significant [h], laid out in the order [e] names.
 *)
(* [Endian -> Byte -> Byte -> HWord] *)
Definition make := fun (e : Endian) (l : Byte) (h : Byte) .
  match e with
  | Endian.Little => HWord.introduction Endian.Little l h
  | Endian.Big    => HWord.introduction Endian.Big    h l
  end.

(* The same value, laid out in the order [e] names. *)
(* [Endian -> HWord -> HWord] *)
Definition with_endian := fun (e : Endian) (x : HWord) . make e (low x) (high x).

(* [Endian -> HWord] *)
Definition Zero := fun (e : Endian) . make e Byte.Zero Byte.Zero.

(* [HWord -> HWord] *)
Definition flip := fun (x : HWord) .
  make (endian x) (Byte.flip (low x)) (Byte.flip (high x)).

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_hword_scope.

(* [x] converted to little-endian, then flipped. *)
(* [HWord -> HWord] *)
Definition flip_little_endian := fun (x : HWord) . flip (with_endian Endian.Little x).

(* [x] converted to big-endian, then flipped. *)
(* [HWord -> HWord] *)
Definition flip_big_endian := fun (x : HWord) . flip (with_endian Endian.Big x).

(* [y] converted to the endianness of [x], then combined with it byte by
 * byte: the result takes the endianness of [x].
 *)
(* [HWord -> HWord -> HWord] *)
Definition and := fun (x : HWord) (y : HWord) .
  make (endian x) (Byte.and (low x) (low y)) (Byte.and (high x) (high y)).

Notation "x &. y" := (and x y) (only parsing)
  : jwa_hword_scope.

(* Both operands converted to little-endian, then combined: the result is
 * little-endian whatever theirs.
 *)
(* [HWord -> HWord -> HWord] *)
Definition and_little_endian := fun (x : HWord) (y : HWord) .
  and (with_endian Endian.Little x) y.

(* Both operands converted to big-endian, then combined: the result is
 * big-endian whatever theirs.
 *)
(* [HWord -> HWord -> HWord] *)
Definition and_big_endian := fun (x : HWord) (y : HWord) .
  and (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [HWord -> HWord -> HWord] *)
Definition or := fun (x : HWord) (y : HWord) .
  make (endian x) (Byte.or (low x) (low y)) (Byte.or (high x) (high y)).

Notation "x |. y" := (or x y) (only parsing)
  : jwa_hword_scope.

(* [HWord -> HWord -> HWord] *)
Definition or_little_endian := fun (x : HWord) (y : HWord) .
  or (with_endian Endian.Little x) y.

(* [HWord -> HWord -> HWord] *)
Definition or_big_endian := fun (x : HWord) (y : HWord) .
  or (with_endian Endian.Big x) y.

(* The endianness of [x], as [and]. *)
(* [HWord -> HWord -> HWord] *)
Definition xor := fun (x : HWord) (y : HWord) .
  make (endian x) (Byte.xor (low x) (low y)) (Byte.xor (high x) (high y)).

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_hword_scope.

(* [HWord -> HWord -> HWord] *)
Definition xor_little_endian := fun (x : HWord) (y : HWord) .
  xor (with_endian Endian.Little x) y.

(* [HWord -> HWord -> HWord] *)
Definition xor_big_endian := fun (x : HWord) (y : HWord) .
  xor (with_endian Endian.Big x) y.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1]. The bit leaving the low
 * byte at its top enters the high byte at its bottom, and the result keeps
 * the endianness. Each endianness has its branch, so that a step takes its
 * argument apart once: through [low], [high] and [endian] it would do so
 * three times, and [simpl] would copy the previous step into each.
 *)
(* [HWord -> Nat -> HWord] *)
Fixpoint rotate_left_nat (x : HWord) (k : Nat) : HWord :=
  let y :=
    match x with
    | HWord.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8) =>
        HWord.introduction Endian.Little
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 x15)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
    | HWord.introduction Endian.Big
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        HWord.introduction Endian.Big
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 x15)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [HWord -> Nat -> HWord] *)
Fixpoint rotate_right_nat (x : HWord) (k : Nat) : HWord :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | HWord.introduction Endian.Little
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0)
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8) =>
      HWord.introduction Endian.Little
        (Byte.introduction y8 y7 y6 y5 y4 y3 y2 y1)
        (Byte.introduction y0 y15 y14 y13 y12 y11 y10 y9)
  | HWord.introduction Endian.Big
      (Byte.introduction y15 y14 y13 y12 y11 y10 y9 y8)
      (Byte.introduction y7 y6 y5 y4 y3 y2 y1 y0) =>
      HWord.introduction Endian.Big
        (Byte.introduction y0 y15 y14 y13 y12 y11 y10 y9)
        (Byte.introduction y8 y7 y6 y5 y4 y3 y2 y1)
  end.

(* [HWord -> Nat0 -> HWord] *)
Definition rotate_left := fun (x : HWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [HWord -> Nat0 -> HWord] *)
Definition rotate_right := fun (x : HWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [0] coming in at the
 * other, in the order and the branches of [rotate_left_nat].
 *)
(* [HWord -> Nat -> HWord] *)
Fixpoint shift_left_nat (x : HWord) (k : Nat) : HWord :=
  let y :=
    match x with
    | HWord.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8) =>
        HWord.introduction Endian.Little
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
    | HWord.introduction Endian.Big
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        HWord.introduction Endian.Big
          (Byte.introduction x14 x13 x12 x11 x10 x9 x8 x7)
          (Byte.introduction x6 x5 x4 x3 x2 x1 x0 0)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [k] places toward the least significant end, a [0] coming in at
 * the other; one place first, then [k - 1], as [shift_left_nat].
 *)
(* [HWord -> Nat -> HWord] *)
Fixpoint shift_right_nat (x : HWord) (k : Nat) : HWord :=
  let y :=
    match x with
    | HWord.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8) =>
        HWord.introduction Endian.Little
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
          (Byte.introduction 0 x15 x14 x13 x12 x11 x10 x9)
    | HWord.introduction Endian.Big
        (Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0) =>
        HWord.introduction Endian.Big
          (Byte.introduction 0 x15 x14 x13 x12 x11 x10 x9)
          (Byte.introduction x8 x7 x6 x5 x4 x3 x2 x1)
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_right_nat y k'
  end.

(* [HWord -> Nat0 -> HWord] *)
Definition shift_left := fun (x : HWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [HWord -> Nat0 -> HWord] *)
Definition shift_right := fun (x : HWord) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

(* The two bytes in the order they are laid out. *)
(* [HWord -> List Byte] *)
Definition to_bytes := fun (x : HWord) .
  match x with
  | HWord.introduction _ b0 b1 => List.Cons b0 (List.Cons b1 List.Nil)
  end.

(* The half word of endianness [e] laid out as the bytes of [l], or [None]
 * for a list of any length but two.
 *)
(* [Endian -> List Byte -> Option HWord] *)
Definition from_bytes := fun (e : Endian) (l : List Byte) .
  match l with
  | List.Cons b0 (List.Cons b1 List.Nil) => Some (HWord.introduction e b0 b1)
  | _                                    => None
  end.

(* [x] with the four bits of a hexadecimal digit shifted in at the least
 * significant end, or [None] when that would push a 1 out at the other, so
 * that a literal past four significant digits is refused; one branch per
 * endianness, as [rotate_left_nat].
 *)
(* [Option HWord -> Bit -> Bit -> Bit -> Bit -> Option HWord] *)
Definition append_digit := fun (x : Option HWord) (d3 : Bit) (d2 : Bit) (d1 : Bit) (d0 : Bit) .
  match x with
  | Some
      (HWord.introduction Endian.Little
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)
        (Byte.introduction 0 0 0 0 x11 x10 x9 x8)) =>
      Some
        (HWord.introduction Endian.Little
          (Byte.introduction x3 x2 x1 x0 d3 d2 d1 d0)
          (Byte.introduction x11 x10 x9 x8 x7 x6 x5 x4))
  | Some
      (HWord.introduction Endian.Big
        (Byte.introduction 0 0 0 0 x11 x10 x9 x8)
        (Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0)) =>
      Some
        (HWord.introduction Endian.Big
          (Byte.introduction x11 x10 x9 x8 x7 x6 x5 x4)
          (Byte.introduction x3 x2 x1 x0 d3 d2 d1 d0))
  | _ => None
  end.

(* [x] with the hexadecimal digits [h] appended, most significant first. *)
(* [Option HWord -> Numeral.Hexadecimal.Digits -> Option HWord] *)
Fixpoint from_hexadecimal (x : Option HWord) (h : Numeral.Hexadecimal.Digits) : Option HWord :=
  match h with
  | Numeral.Hexadecimal.Digits.End         =>
      x
  | Numeral.Hexadecimal.Digits.Zero h'     =>
      from_hexadecimal (append_digit x 0 0 0 0) h'
  | Numeral.Hexadecimal.Digits.One h'      =>
      from_hexadecimal (append_digit x 0 0 0 1) h'
  | Numeral.Hexadecimal.Digits.Two h'      =>
      from_hexadecimal (append_digit x 0 0 1 0) h'
  | Numeral.Hexadecimal.Digits.Three h'    =>
      from_hexadecimal (append_digit x 0 0 1 1) h'
  | Numeral.Hexadecimal.Digits.Four h'     =>
      from_hexadecimal (append_digit x 0 1 0 0) h'
  | Numeral.Hexadecimal.Digits.Five h'     =>
      from_hexadecimal (append_digit x 0 1 0 1) h'
  | Numeral.Hexadecimal.Digits.Six h'      =>
      from_hexadecimal (append_digit x 0 1 1 0) h'
  | Numeral.Hexadecimal.Digits.Seven h'    =>
      from_hexadecimal (append_digit x 0 1 1 1) h'
  | Numeral.Hexadecimal.Digits.Eight h'    =>
      from_hexadecimal (append_digit x 1 0 0 0) h'
  | Numeral.Hexadecimal.Digits.Nine h'     =>
      from_hexadecimal (append_digit x 1 0 0 1) h'
  | Numeral.Hexadecimal.Digits.Ten h'      =>
      from_hexadecimal (append_digit x 1 0 1 0) h'
  | Numeral.Hexadecimal.Digits.Eleven h'   =>
      from_hexadecimal (append_digit x 1 0 1 1) h'
  | Numeral.Hexadecimal.Digits.Twelve h'   =>
      from_hexadecimal (append_digit x 1 1 0 0) h'
  | Numeral.Hexadecimal.Digits.Thirteen h' =>
      from_hexadecimal (append_digit x 1 1 0 1) h'
  | Numeral.Hexadecimal.Digits.Fourteen h' =>
      from_hexadecimal (append_digit x 1 1 1 0) h'
  | Numeral.Hexadecimal.Digits.Fifteen h'  =>
      from_hexadecimal (append_digit x 1 1 1 1) h'
  end.

(* A literal in hexadecimal, read as the bits it spells and laid out in the
 * order [e] names; a decimal one is refused, since a half word is bits and
 * not a number.
 *)
(* [Endian -> Numeral.Unsigned -> Option HWord] *)
Definition from_numeral := fun (e : Endian) (u : Numeral.Unsigned) .
  match u with
  | Numeral.Unsigned.Decimal _     => None
  | Numeral.Unsigned.Hexadecimal h => from_hexadecimal (Some (Zero e)) h
  end.

(* [Numeral.Unsigned -> Option HWord] *)
Definition from_little_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Little u.

(* [Numeral.Unsigned -> Option HWord] *)
Definition from_big_numeral := fun (u : Numeral.Unsigned) . from_numeral Endian.Big u.

(* [x] as a literal of four hexadecimal digits, the high byte's first, when
 * its endianness is [e], and [None] otherwise, so that a literal scope
 * prints only the half words it reads back.
 *)
(* [Endian -> HWord -> Option Numeral.Unsigned] *)
Definition to_numeral := fun (e : Endian) (x : HWord) .
  let digits :=
    match low x, high x with
    | Byte.introduction x7 x6 x5 x4 x3 x2 x1 x0,
      Byte.introduction x15 x14 x13 x12 x11 x10 x9 x8 =>
        Numeral.Unsigned.Hexadecimal
          (Byte.hexadecimal_digit x15 x14 x13 x12
            (Byte.hexadecimal_digit x11 x10 x9 x8
              (Byte.hexadecimal_digit x7 x6 x5 x4
                (Byte.hexadecimal_digit x3 x2 x1 x0 Numeral.Hexadecimal.Digits.End))))
    end in
  match e, endian x with
  | Endian.Little, Endian.Little => Some digits
  | Endian.Big, Endian.Big       => Some digits
  | _, _                         => None
  end.

(* [HWord -> Option Numeral.Unsigned] *)
Definition to_little_numeral := fun (x : HWord) . to_numeral Endian.Little x.

(* [HWord -> Option Numeral.Unsigned] *)
Definition to_big_numeral := fun (x : HWord) . to_numeral Endian.Big x.

Local Open Scope jwa_hword_scope.

(* Two equal bytes in each place make equal half words of one endianness;
 * each law below is its [Byte] counterpart taken byte by byte through this.
 *)
(* congruence *)
Lemma congruence
  : forall {e : Endian} {a0 : Byte} {a1 : Byte} {b0 : Byte} {b1 : Byte} .
      a0 = b0 -> a1 = b1 -> HWord.introduction e a0 a1 = HWord.introduction e b0 b1.
Proof.
  intros e a0 a1 b0 b1 e0 e1.
  leibniz &e0, &e1 in |- *.
  quod idem est.
Qed.

Module endianness. (* endianness *)

(* endianness.specification *)
Theorem specification : forall (e : Endian) (x : HWord) . endian (with_endian e x) = e.
Proof.
  intros e x.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.identity *)
Theorem identity : forall (x : HWord) . with_endian (endian x) x = x.
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* endianness.absorption *)
Theorem absorption
  : forall (e : Endian) (f : Endian) (x : HWord) .
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
Theorem involution : forall (x : HWord) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end;
    simpl flip in |- *;
    simpl in |- *;
    ipso (congruence (Byte.flipping.involution &x0) (Byte.flipping.involution &x1)).
Qed.

Module endian. (* flipping.endian *)

Module little. (* flipping.endian.little *)

(* flipping.endian.little.specification *)
Theorem specification : forall (x : HWord) . endian (flip_little_endian x) = Endian.Little.
Proof.
  intros x.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* flipping.endian.little *)

Module big. (* flipping.endian.big *)

(* flipping.endian.big.specification *)
Theorem specification : forall (x : HWord) . endian (flip_big_endian x) = Endian.Big.
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  match &z with | introduction ez z0 z1 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.conjunction.associativity _ _ _)
        (Byte.conjunction.associativity _ _ _)).
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (x : HWord) . (~. Zero (endian x) &. x = x) /\ (x &. ~. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match (Byte.conjunction.identity &x0) with | left0 right0 end.
  match (Byte.conjunction.identity &x1) with | left1 right1 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
Qed.

Module endian. (* conjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* conjunction.endian.conversion *)
Theorem conversion
  : forall (x : HWord) (y : HWord) . x &. y = x &. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end;
    simpl and, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* conjunction.endian.little *)

(* conjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)).
Qed.

(* conjunction.endian.little.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (and_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* conjunction.endian.little *)

Module big. (* conjunction.endian.big *)

(* conjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x &. y = y &. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl and in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.conjunction.commutativity &x0 &y0)
      (Byte.conjunction.commutativity &x1 &y1)).
Qed.

(* conjunction.endian.big.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (and_big_endian x y) = Endian.Big.
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  match &z with | introduction ez z0 z1 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and, xor in |- *;
    simpl in |- *;
    ipso
      (congruence
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  match &z with | introduction ez z0 z1 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl and, xor in |- *;
    simpl in |- *;
    ipso
      (congruence
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  match &z with | introduction ez z0 z1 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl or in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.disjunction.associativity _ _ _)
        (Byte.disjunction.associativity _ _ _)).
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (x : HWord) . (Zero (endian x) |. x = x) /\ (x |. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match (Byte.disjunction.identity &x0) with | left0 right0 end.
  match (Byte.disjunction.identity &x1) with | left1 right1 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
Qed.

Module endian. (* disjunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* disjunction.endian.conversion *)
Theorem conversion
  : forall (x : HWord) (y : HWord) . x |. y = x |. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end;
    simpl or, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* disjunction.endian.little *)

(* disjunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)).
Qed.

(* disjunction.endian.little.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (or_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* disjunction.endian.little *)

Module big. (* disjunction.endian.big *)

(* disjunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x |. y = y |. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl or in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.disjunction.commutativity &x0 &y0)
      (Byte.disjunction.commutativity &x1 &y1)).
Qed.

(* disjunction.endian.big.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (or_big_endian x y) = Endian.Big.
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
  : forall (x : HWord) (y : HWord) (z : HWord) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  match &z with | introduction ez z0 z1 end.
  match &ex with | Little | Big end;
    match &ey with | Little | Big end;
    match &ez with | Little | Big end;
    simpl xor in |- *;
    simpl in |- *;
    ipso
      (congruence
        (Byte.sejunction.associativity _ _ _)
        (Byte.sejunction.associativity _ _ _)).
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (x : HWord) . (Zero (endian x) ^. x = x) /\ (x ^. Zero (endian x) = x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match (Byte.sejunction.identity &x0) with | left0 right0 end.
  match (Byte.sejunction.identity &x1) with | left1 right1 end.
  match &e with | Little | Big end.
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
  - divide et impera.
    + ipso (congruence &left0 &left1).
    + ipso (congruence &right0 &right1).
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : HWord) . x ^. x = Zero (endian x).
Proof.
  intros x.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end;
    ipso
      (congruence
        (Byte.sejunction.irreflexivity &x0) (Byte.sejunction.irreflexivity &x1)).
Qed.

Module endian. (* sejunction.endian *)

(* An operand of the other endianness is converted before the bytes meet. *)
(* sejunction.endian.conversion *)
Theorem conversion
  : forall (x : HWord) (y : HWord) . x ^. y = x ^. with_endian (endian x) y.
Proof.
  intros x y.
  match &x with | introduction e x0 x1 end.
  match &e with | Little | Big end;
    simpl xor, with_endian in |- *;
    simpl in |- *;
    quod idem est.
Qed.

Module little. (* sejunction.endian.little *)

(* sejunction.endian.little.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Little -> endian y = Endian.Little -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)).
Qed.

(* sejunction.endian.little.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (xor_little_endian x y) = Endian.Little.
Proof.
  intros x y.
  simpl in |- *.
  quod idem est.
Qed.

End little. (* sejunction.endian.little *)

Module big. (* sejunction.endian.big *)

(* sejunction.endian.big.commutativity *)
Theorem commutativity
  : forall (x : HWord) (y : HWord) .
      endian x = Endian.Big -> endian y = Endian.Big -> x ^. y = y ^. x.
Proof.
  intros x y hx hy.
  match &x with | introduction ex x0 x1 end.
  match &y with | introduction ey y0 y1 end.
  simpl in &hx, &hy.
  leibniz &hx, &hy in |- *.
  simpl xor in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Byte.sejunction.commutativity &x0 &y0)
      (Byte.sejunction.commutativity &x1 &y1)).
Qed.

(* sejunction.endian.big.specification *)
Theorem specification
  : forall (x : HWord) (y : HWord) . endian (xor_big_endian x y) = Endian.Big.
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
Theorem period : forall (x : HWord) . rotate_left x 16%n0 = x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 end.
  match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : HWord) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with | introduction e b0 b1 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + intros x.
      match &x with | introduction e b0 b1 end.
      match &e with | Little | Big end.
      * match &b0 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        match &b1 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        simpl in |- *.
        leibniz
          (&IH
            (HWord.introduction Endian.Little
              (Byte.introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x15)
              (Byte.introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)))
          in |- *.
        simpl in |- *.
        quod idem est.
      * match &b0 with | introduction x15 x14 x13 x12 x11 x10 x9 x8 end.
        match &b1 with | introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
        simpl in |- *.
        leibniz
          (&IH
            (HWord.introduction Endian.Big
              (Byte.introduction &x14 &x13 &x12 &x11 &x10 &x9 &x8 &x7)
              (Byte.introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x15)))
          in |- *.
        simpl in |- *.
        quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : HWord) . rotate_right x 16%n0 = x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 end.
  match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
  match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
  match &e with | Little | Big end; simpl in |- *; quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : HWord) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with | introduction e b0 b1 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &e with | Little | Big end; simpl in |- *; quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with | introduction e b0 b1 end.
      match &b0 with | introduction p7 p6 p5 p4 p3 p2 p1 p0 end.
      match &b1 with | introduction q7 q6 q5 q4 q3 q2 q1 q0 end.
      match &e with | Little | Big end; ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

Module conversion. (* conversion *)

Module bytes. (* conversion.bytes *)

(* conversion.bytes.section *)
Theorem section : forall (x : HWord) . from_bytes (endian x) (to_bytes x) = Some x.
Proof.
  intros x.
  match &x with | introduction e b0 b1 end.
  simpl from_bytes, to_bytes, endian in |- *.
  quod idem est.
Qed.

End bytes. (* conversion.bytes *)

End conversion. (* conversion *)

End HWord. (* HWord *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [HWord], not [HWord.T].
 *)
Abbreviation HWord := HWord.T.

(* Makes the notations declared in [Module HWord] usable in every file that
 * imports this one, as [(x &. y)%hword] or under an opened [jwa_hword_scope].
 *)
Export (notations) HWord.

(* A half word is written in hexadecimal, [0x1234%hword_little] or
 * [0x1234%hword_big] laid out as the key names, and prints back the same
 * way, in four digits. The plain key reads little-endian and is declared
 * last, so a little-endian half word prints as [0x1234%hword].
 *)
Number Notation HWord.T HWord.from_little_numeral HWord.to_little_numeral
  : jwa_hword_little_scope.
Number Notation HWord.T HWord.from_big_numeral HWord.to_big_numeral
  : jwa_hword_big_scope.
Number Notation HWord.T HWord.from_little_numeral HWord.to_little_numeral
  : jwa_hword_scope.

(* Where an [HWord] is expected, a literal or a notation reads in this scope
 * without its [%hword].
 *)
Bind Scope jwa_hword_scope with HWord.T.
