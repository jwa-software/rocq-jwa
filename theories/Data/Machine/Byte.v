(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.

Module Byte. (* Byte *)

(* Eight bits, the MSB first, as a binary number is written. *)
Inductive T : Type :=
  | Byte_introduction : Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> Bit -> T.

Abbreviation Byte := T.

(* [Byte] *)
Definition Zero :=
  Byte_introduction
    Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero.

(* [Byte -> Byte] *)
Definition flip := fun (x : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      Byte_introduction
        (Bit.flip x7) (Bit.flip x6) (Bit.flip x5) (Bit.flip x4)
        (Bit.flip x3) (Bit.flip x2) (Bit.flip x1) (Bit.flip x0)
  end.

(* The spellings and levels are those of [jwa_bit_scope]; [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "~. x" := (flip x) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition and := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.and x7 y7) (Bit.and x6 y6) (Bit.and x5 y5) (Bit.and x4 y4)
            (Bit.and x3 y3) (Bit.and x2 y2) (Bit.and x1 y1) (Bit.and x0 y0)
      end
  end.

Notation "x &. y" := (and x y) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition or := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.or x7 y7) (Bit.or x6 y6) (Bit.or x5 y5) (Bit.or x4 y4)
            (Bit.or x3 y3) (Bit.or x2 y2) (Bit.or x1 y1) (Bit.or x0 y0)
      end
  end.

Notation "x |. y" := (or x y) (only parsing)
  : jwa_byte_scope.

(* [Byte -> Byte -> Byte] *)
Definition xor := fun (x : Byte) (y : Byte) .
  match x with
  | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
      match y with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
          Byte_introduction
            (Bit.xor x7 y7) (Bit.xor x6 y6) (Bit.xor x5 y5) (Bit.xor x4 y4)
            (Bit.xor x3 y3) (Bit.xor x2 y2) (Bit.xor x1 y1) (Bit.xor x0 y0)
      end
  end.

Notation "x ^. y" := (xor x y) (only parsing)
  : jwa_byte_scope.

(* [k] places toward the most significant end, each bit leaving there coming
 * back at the other; one place first, then [k - 1].
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint rotate_left_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match x with
    | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
        Byte_introduction x6 x5 x4 x3 x2 x1 x0 x7
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => rotate_left_nat y k'
  end.

(* [k] places toward the least significant end, each bit leaving there
 * coming back at the other; [k - 1] places first, then one, the reverse of
 * [rotate_left_nat], so that each undoes the other place by place.
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint rotate_right_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => rotate_right_nat x k'
    end in
  match y with
  | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
      Byte_introduction y0 y7 y6 y5 y4 y3 y2 y1
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition rotate_left := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_left_nat x n
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition rotate_right := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => rotate_right_nat x n
  end.

(* [k] places toward the most significant end, a [Bit.Zero] coming in at the
 * other, in the order of [rotate_left_nat].
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint shift_left_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match x with
    | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 =>
        Byte_introduction x6 x5 x4 x3 x2 x1 x0 Bit.Zero
    end in
  match k with
  | Nat.One          => y
  | Nat.Successor k' => shift_left_nat y k'
  end.

(* [k] places toward the least significant end, a [Bit.Zero] coming in at
 * the other, in the order of [rotate_right_nat].
 *)
(* [Byte -> Nat -> Byte] *)
Fixpoint shift_right_nat (x : Byte) (k : Nat) : Byte :=
  let y :=
    match k with
    | Nat.One          => x
    | Nat.Successor k' => shift_right_nat x k'
    end in
  match y with
  | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 =>
      Byte_introduction Bit.Zero y7 y6 y5 y4 y3 y2 y1
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition shift_left := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_left_nat x n
  end.

(* [Byte -> Nat0 -> Byte] *)
Definition shift_right := fun (x : Byte) (k : Nat0) .
  match k with
  | Nat0.Zero       => x
  | Nat0.Positive n => shift_right_nat x n
  end.

Local Open Scope jwa_byte_scope.

(* Eight equal fields make equal bytes; each law below is its [Bit]
 * counterpart taken field by field through this.
 *)
(* congruence *)
Lemma congruence
  : forall {a7 : Bit} {a6 : Bit} {a5 : Bit} {a4 : Bit}
      {a3 : Bit} {a2 : Bit} {a1 : Bit} {a0 : Bit}
      {b7 : Bit} {b6 : Bit} {b5 : Bit} {b4 : Bit}
      {b3 : Bit} {b2 : Bit} {b1 : Bit} {b0 : Bit} .
      a7 = b7 -> a6 = b6 -> a5 = b5 -> a4 = b4 ->
      a3 = b3 -> a2 = b2 -> a1 = b1 -> a0 = b0 ->
      Byte_introduction a7 a6 a5 a4 a3 a2 a1 a0
        = Byte_introduction b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
  intros e7 e6 e5 e4 e3 e2 e1 e0.
  leibniz &e7, &e6, &e5, &e4, &e3, &e2, &e1, &e0 in |- *.
  quod idem est.
Qed.

Module flipping. (* flipping *)

(* flipping.involution *)
Theorem involution : forall (x : Byte) . ~. ~. x = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.flipping.involution &x7) (Bit.flipping.involution &x6)
      (Bit.flipping.involution &x5) (Bit.flipping.involution &x4)
      (Bit.flipping.involution &x3) (Bit.flipping.involution &x2)
      (Bit.flipping.involution &x1) (Bit.flipping.involution &x0)).
Qed.

End flipping. (* flipping *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x &. y) &. z = x &. (y &. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.associativity &x7 &y7 &z7)
      (Bit.conjunction.associativity &x6 &y6 &z6)
      (Bit.conjunction.associativity &x5 &y5 &z5)
      (Bit.conjunction.associativity &x4 &y4 &z4)
      (Bit.conjunction.associativity &x3 &y3 &z3)
      (Bit.conjunction.associativity &x2 &y2 &z2)
      (Bit.conjunction.associativity &x1 &y1 &z1)
      (Bit.conjunction.associativity &x0 &y0 &z0)).
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x &. y = y &. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.commutativity &x7 &y7)
      (Bit.conjunction.commutativity &x6 &y6)
      (Bit.conjunction.commutativity &x5 &y5)
      (Bit.conjunction.commutativity &x4 &y4)
      (Bit.conjunction.commutativity &x3 &y3)
      (Bit.conjunction.commutativity &x2 &y2)
      (Bit.conjunction.commutativity &x1 &y1)
      (Bit.conjunction.commutativity &x0 &y0)).
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (x : Byte) . (~. Zero &. x = x) /\ (x &. ~. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (conjunction.commutativity &x (~. Zero)) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
      x &. (y ^. z) = (x &. y) ^. (x &. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.left.distributivity.over.sejunction &x7 &y7 &z7)
      (Bit.conjunction.left.distributivity.over.sejunction &x6 &y6 &z6)
      (Bit.conjunction.left.distributivity.over.sejunction &x5 &y5 &z5)
      (Bit.conjunction.left.distributivity.over.sejunction &x4 &y4 &z4)
      (Bit.conjunction.left.distributivity.over.sejunction &x3 &y3 &z3)
      (Bit.conjunction.left.distributivity.over.sejunction &x2 &y2 &z2)
      (Bit.conjunction.left.distributivity.over.sejunction &x1 &y1 &z1)
      (Bit.conjunction.left.distributivity.over.sejunction &x0 &y0 &z0)).
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (y ^. z) &. x = (y &. x) ^. (z &. x).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.conjunction.right.distributivity.over.sejunction &x7 &y7 &z7)
      (Bit.conjunction.right.distributivity.over.sejunction &x6 &y6 &z6)
      (Bit.conjunction.right.distributivity.over.sejunction &x5 &y5 &z5)
      (Bit.conjunction.right.distributivity.over.sejunction &x4 &y4 &z4)
      (Bit.conjunction.right.distributivity.over.sejunction &x3 &y3 &z3)
      (Bit.conjunction.right.distributivity.over.sejunction &x2 &y2 &z2)
      (Bit.conjunction.right.distributivity.over.sejunction &x1 &y1 &z1)
      (Bit.conjunction.right.distributivity.over.sejunction &x0 &y0 &z0)).
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.sejunction *)
Theorem sejunction
  : forall (x : Byte) (y : Byte) (z : Byte) .
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
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x |. y) |. z = x |. (y |. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.disjunction.associativity &x7 &y7 &z7)
      (Bit.disjunction.associativity &x6 &y6 &z6)
      (Bit.disjunction.associativity &x5 &y5 &z5)
      (Bit.disjunction.associativity &x4 &y4 &z4)
      (Bit.disjunction.associativity &x3 &y3 &z3)
      (Bit.disjunction.associativity &x2 &y2 &z2)
      (Bit.disjunction.associativity &x1 &y1 &z1)
      (Bit.disjunction.associativity &x0 &y0 &z0)).
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x |. y = y |. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.disjunction.commutativity &x7 &y7)
      (Bit.disjunction.commutativity &x6 &y6)
      (Bit.disjunction.commutativity &x5 &y5)
      (Bit.disjunction.commutativity &x4 &y4)
      (Bit.disjunction.commutativity &x3 &y3)
      (Bit.disjunction.commutativity &x2 &y2)
      (Bit.disjunction.commutativity &x1 &y1)
      (Bit.disjunction.commutativity &x0 &y0)).
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (x : Byte) . (Zero |. x = x) /\ (x |. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (disjunction.commutativity &x Zero) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.associativity *)
Theorem associativity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x ^. y) ^. z = x ^. (y ^. z).
Proof.
  intros x y z.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  match &z with | Byte_introduction z7 z6 z5 z4 z3 z2 z1 z0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.associativity &x7 &y7 &z7)
      (Bit.sejunction.associativity &x6 &y6 &z6)
      (Bit.sejunction.associativity &x5 &y5 &z5)
      (Bit.sejunction.associativity &x4 &y4 &z4)
      (Bit.sejunction.associativity &x3 &y3 &z3)
      (Bit.sejunction.associativity &x2 &y2 &z2)
      (Bit.sejunction.associativity &x1 &y1 &z1)
      (Bit.sejunction.associativity &x0 &y0 &z0)).
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (x : Byte) (y : Byte) . x ^. y = y ^. x.
Proof.
  intros x y.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  match &y with | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0 end.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.commutativity &x7 &y7)
      (Bit.sejunction.commutativity &x6 &y6)
      (Bit.sejunction.commutativity &x5 &y5)
      (Bit.sejunction.commutativity &x4 &y4)
      (Bit.sejunction.commutativity &x3 &y3)
      (Bit.sejunction.commutativity &x2 &y2)
      (Bit.sejunction.commutativity &x1 &y1)
      (Bit.sejunction.commutativity &x0 &y0)).
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (x : Byte) . (Zero ^. x = x) /\ (x ^. Zero = x).
Proof.
  intros x.
  divide et impera.
  - match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
  - leibniz (sejunction.commutativity &x Zero) in |- *.
    match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
    simpl in |- *.
    quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (x : Byte) . x ^. x = Zero.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl Zero in |- *.
  simpl in |- *.
  ipso
    (congruence
      (Bit.sejunction.irreflexivity &x7) (Bit.sejunction.irreflexivity &x6)
      (Bit.sejunction.irreflexivity &x5) (Bit.sejunction.irreflexivity &x4)
      (Bit.sejunction.irreflexivity &x3) (Bit.sejunction.irreflexivity &x2)
      (Bit.sejunction.irreflexivity &x1) (Bit.sejunction.irreflexivity &x0)).
Qed.

(* sejunction.inverse *)
Theorem inverse
  : forall (x : Byte) . (x ^. x = Zero) /\ (x ^. x = Zero).
Proof.
  intros x.
  divide et impera; ipso (sejunction.irreflexivity &x).
Qed.

End sejunction. (* sejunction *)

Module rotation. (* rotation *)

Module left. (* rotation.left *)

(* rotation.left.period *)
Theorem period : forall (x : Byte) . rotate_left x 8%n0 = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  quod idem est.
Qed.

(* rotation.left.inverse *)
Theorem inverse
  : forall (x : Byte) (k : Nat0) . rotate_right (rotate_left x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    extro &x.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + intros x.
      match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      quod idem est.
    + intros x.
      match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      leibniz (&IH (Byte_introduction &x6 &x5 &x4 &x3 &x2 &x1 &x0 &x7)) in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End left. (* rotation.left *)

Module right. (* rotation.right *)

(* rotation.right.period *)
Theorem period : forall (x : Byte) . rotate_right x 8%n0 = x.
Proof.
  intros x.
  match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
  simpl in |- *.
  quod idem est.
Qed.

(* rotation.right.inverse *)
Theorem inverse
  : forall (x : Byte) (k : Nat0) . rotate_left (rotate_right x k) k = x.
Proof.
  intros x k.
  match &k with | Zero | Positive n end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match n with | One | Successor (n' by IH) end per Nat.induction.
    + match &x with | Byte_introduction x7 x6 x5 x4 x3 x2 x1 x0 end.
      simpl in |- *.
      quod idem est.
    + simpl in |- *.
      match (rotate_right_nat &x &n') with
      | Byte_introduction y7 y6 y5 y4 y3 y2 y1 y0
      end.
      ipso &IH.
Qed.

End right. (* rotation.right *)

End rotation. (* rotation *)

End Byte. (* Byte *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Byte], not [Byte.T].
 *)
Abbreviation Byte := Byte.T.

(* Makes the notations declared in [Module Byte] usable in every file that
 * imports this one, as [(x &. y)%byte] or under an opened [jwa_byte_scope].
 *)
Export (notations) Byte.

(* Where a [Byte] is expected, a notation reads in this scope without its
 * [%byte].
 *)
Bind Scope jwa_byte_scope with Byte.T.

Instance Byte_and_monoid
  : Monoid Byte.and (Byte.flip Byte.Zero) :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.conjunction.associativity |}
  ; Monoid.identity := Byte.conjunction.identity |}.

Instance Byte_or_monoid
  : Monoid Byte.or Byte.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.disjunction.associativity |}
  ; Monoid.identity := Byte.disjunction.identity |}.

Instance Byte_xor_monoid
  : Monoid Byte.xor Byte.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Byte.sejunction.associativity |}
  ; Monoid.identity := Byte.sejunction.identity |}.

Instance Byte_and_commutative
  : Commutative Byte.and :=
  {| Commutative.commutativity := Byte.conjunction.commutativity |}.

Instance Byte_or_commutative
  : Commutative Byte.or :=
  {| Commutative.commutativity := Byte.disjunction.commutativity |}.

Instance Byte_xor_commutative
  : Commutative Byte.xor :=
  {| Commutative.commutativity := Byte.sejunction.commutativity |}.

Instance Byte_xor_group
  : Group Byte.xor Byte.Zero (fun (x : Byte) . x) :=
  {| Group.monoid := Byte_xor_monoid
  ; Group.inverse := Byte.sejunction.inverse |}.

Instance Byte_xor_abelian_group
  : AbelianGroup Byte.xor Byte.Zero (fun (x : Byte) . x) :=
  {| AbelianGroup.group := Byte_xor_group
  ; AbelianGroup.commutative := Byte_xor_commutative |}.

Instance Byte_ring
  : Ring Byte.xor Byte.Zero (fun (x : Byte) . x) Byte.and (Byte.flip Byte.Zero) :=
  {| Ring.abelian_group := Byte_xor_abelian_group
  ; Ring.monoid := Byte_and_monoid
  ; Ring.distributivity := Byte.conjunction.distributivity.over.sejunction |}.
