(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Number.Binary.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [BinaryWithZero.add].
 * The type and its ctors are declared inside it: [NatWithZero] and [Integer]
 * declare [Zero] and [Positive] too, and across files a duplicate ctor name
 * rebinds the bare one silently and with no warning.
 *)
Module BinaryWithZero. (* BinaryWithZero *)

(* [Positive] wraps a [Binary], so the arithmetic here reduces to the
 * [Binary] operation plus the [Zero] cases, as [NatWithZero] does over [Nat].
 *)
Inductive T : Type :=
  | Zero     : T
  | Positive : Binary -> T.

(* The carrier is named [T] so that the type itself reads [BinaryWithZero] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End BinaryWithZero].
 *)
Abbreviation BinaryWithZero := T.

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] is a prefix, apart from the infix [+].
 *)
Local Notation "0" := Zero (only parsing).
Local Notation "+ p" := (Positive p)
  (at level 35, right associativity, only parsing).

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition add := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => + (p + q)%binary
      end
  end.

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition mul := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => + (p * q)%binary
      end
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End BinaryWithZero] a client writes
 * [(m + n)%binary_with_zero]. [only parsing] keeps goals printing the
 * operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_binary_with_zero_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_binary_with_zero_scope.

Local Open Scope jwa_binary_with_zero_scope.

(* [BinaryWithZero -> BinaryWithZero] *)
Definition inc := fun (n : BinaryWithZero) .
  match n with
  | 0   => + Binary.One
  | + p => + (Binary.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_binary_with_zero_scope.

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition power := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match n with
  | 0   => + Binary.One
  | + q =>
      match m with
      | 0   => 0
      | + p => + (p ^ q)%binary
      end
  end.

Notation "m ^ n" := (power m n) (only parsing)
  : jwa_binary_with_zero_scope.

(* [BinaryWithZero -> BinaryWithZero -> Comparison] *)
Definition compare := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match n with
      | 0   => Comparison.Gt
      | + q => Binary.compare p q
      end
  end.

(* [m - n], [None] when [n] is the greater, as [NatWithZero.sub] is. *)
(* [BinaryWithZero -> BinaryWithZero -> Option BinaryWithZero] *)
Definition sub := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Some 0
      | + _ => None
      end
  | + p =>
      match n with
      | 0   => Some (+ p)
      | + q =>
          match Binary.difference p q with
          | Binary.Below   => None
          | Binary.Equal   => Some 0
          | Binary.Above d => Some (+ d)
          end
      end
  end.

(* [m - n], and [0] where [sub] has nothing. *)
(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition saturating_sub := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match sub m n with
  | Some k => k
  | None   => 0
  end.

(* [n] with [bit] written after its lowest bit: [2n], or [2n + 1] when [bit]
 * is [true].
 *)
(* [BinaryWithZero -> Bool -> BinaryWithZero] *)
Definition append_bit := fun (n : BinaryWithZero) (bit : Bool) .
  match n with
  | 0 =>
      match bit with
      | true  => + Binary.One
      | false => 0
      end
  | + p =>
      match bit with
      | true  => + Binary.AppendOne p
      | false => + Binary.AppendZero p
      end
  end.

(* Every number is [0] or a number with a bit appended, so a law holds of
 * every number once it holds of [0] and survives the appending.
 *)
Definition induction
  : forall (P : BinaryWithZero -> Prop) .
      P 0 ->
      (forall (bit : Bool) (n : BinaryWithZero) . P n -> P (append_bit n bit)) ->
      forall (n : BinaryWithZero) . P n
  := fun (P : BinaryWithZero -> Prop)
         (zero : P 0)
         (step : forall (bit : Bool) (n : BinaryWithZero) . P n -> P (append_bit n bit))
         (n : BinaryWithZero) .
       match n with
       | 0   => zero
       | + p =>
           Binary.induction (fun (q : Binary) . P (+ q))
             (step true 0 zero)
             (fun (q : Binary) (h : P (+ q)) . step false (+ q) h)
             (fun (q : Binary) (h : P (+ q)) . step true (+ q) h)
             p
       end.

(* [n] with its lowest bit dropped. *)
(* [BinaryWithZero -> BinaryWithZero] *)
Definition halve := fun (n : BinaryWithZero) .
  match n with
  | 0                     => 0
  | + Binary.One          => 0
  | + Binary.AppendZero p => + p
  | + Binary.AppendOne p  => + p
  end.

(* Bit by bit from the least significant end, a number reading as 0s past
 * its leading 1; the bits of the result may all be 0.
 *)
(* [Binary -> Binary -> BinaryWithZero] *)
Fixpoint and_positive (p : Binary) (q : Binary) : BinaryWithZero :=
  match p, q with
  | Binary.One, Binary.One                     => + Binary.One
  | Binary.One, Binary.AppendZero _            => 0
  | Binary.One, Binary.AppendOne _             => + Binary.One
  | Binary.AppendZero _, Binary.One            => 0
  | Binary.AppendZero p', Binary.AppendZero q' => append_bit (and_positive p' q') false
  | Binary.AppendZero p', Binary.AppendOne q'  => append_bit (and_positive p' q') false
  | Binary.AppendOne _, Binary.One             => + Binary.One
  | Binary.AppendOne p', Binary.AppendZero q'  => append_bit (and_positive p' q') false
  | Binary.AppendOne p', Binary.AppendOne q'   => append_bit (and_positive p' q') true
  end.

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition and := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => and_positive p q
      end
  end.

Notation "m && n" := (and m n) (only parsing)
  : jwa_binary_with_zero_scope.

(* As [and_positive], each bit the disjunction of the two. *)
(* [Binary -> Binary -> BinaryWithZero] *)
Fixpoint or_positive (p : Binary) (q : Binary) : BinaryWithZero :=
  match p, q with
  | Binary.One, Binary.One                     => + Binary.One
  | Binary.One, Binary.AppendZero q'           => + Binary.AppendOne q'
  | Binary.One, Binary.AppendOne q'            => + Binary.AppendOne q'
  | Binary.AppendZero p', Binary.One           => + Binary.AppendOne p'
  | Binary.AppendZero p', Binary.AppendZero q' => append_bit (or_positive p' q') false
  | Binary.AppendZero p', Binary.AppendOne q'  => append_bit (or_positive p' q') true
  | Binary.AppendOne p', Binary.One            => + Binary.AppendOne p'
  | Binary.AppendOne p', Binary.AppendZero q'  => append_bit (or_positive p' q') true
  | Binary.AppendOne p', Binary.AppendOne q'   => append_bit (or_positive p' q') true
  end.

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition or := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => or_positive p q
      end
  end.

Notation "m || n" := (or m n) (only parsing)
  : jwa_binary_with_zero_scope.

(* As [and_positive], each bit the exclusive disjunction of the two. *)
(* [Binary -> Binary -> BinaryWithZero] *)
Fixpoint xor_positive (p : Binary) (q : Binary) : BinaryWithZero :=
  match p, q with
  | Binary.One, Binary.One                     => 0
  | Binary.One, Binary.AppendZero q'           => + Binary.AppendOne q'
  | Binary.One, Binary.AppendOne q'            => + Binary.AppendZero q'
  | Binary.AppendZero p', Binary.One           => + Binary.AppendOne p'
  | Binary.AppendZero p', Binary.AppendZero q' => append_bit (xor_positive p' q') false
  | Binary.AppendZero p', Binary.AppendOne q'  => append_bit (xor_positive p' q') true
  | Binary.AppendOne p', Binary.One            => + Binary.AppendZero p'
  | Binary.AppendOne p', Binary.AppendZero q'  => append_bit (xor_positive p' q') true
  | Binary.AppendOne p', Binary.AppendOne q'   => append_bit (xor_positive p' q') false
  end.

(* [BinaryWithZero -> BinaryWithZero -> BinaryWithZero] *)
Definition xor := fun (m : BinaryWithZero) (n : BinaryWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => xor_positive p q
      end
  end.

Notation "m ^^ n" := (xor m n) (only parsing)
  : jwa_binary_with_zero_scope.

(* [BinaryWithZero -> Nat -> BinaryWithZero] *)
Fixpoint shift_left_nat (n : BinaryWithZero) (k : Nat) : BinaryWithZero :=
  match k with
  | Nat.One          => append_bit n false
  | Nat.Successor k' => append_bit (shift_left_nat n k') false
  end.

(* [n] with [k] 0s appended, [n * 2 ^ k]. *)
(* [BinaryWithZero -> NatWithZero -> BinaryWithZero] *)
Definition shift_left := fun (n : BinaryWithZero) (k : NatWithZero) .
  match k with
  | NatWithZero.Zero        => n
  | NatWithZero.Positive k' => shift_left_nat n k'
  end.

(* [BinaryWithZero -> Nat -> BinaryWithZero] *)
Fixpoint shift_right_nat (n : BinaryWithZero) (k : Nat) : BinaryWithZero :=
  match k with
  | Nat.One          => halve n
  | Nat.Successor k' => shift_right_nat (halve n) k'
  end.

(* [n] with its [k] lowest bits dropped. *)
(* [BinaryWithZero -> NatWithZero -> BinaryWithZero] *)
Definition shift_right := fun (n : BinaryWithZero) (k : NatWithZero) .
  match k with
  | NatWithZero.Zero        => n
  | NatWithZero.Positive k' => shift_right_nat n k'
  end.

(* Bit [i] of [n], [true] for 1, counted from 0 at the lowest bit. *)
(* [BinaryWithZero -> NatWithZero -> Bool] *)
Definition test_bit := fun (n : BinaryWithZero) (i : NatWithZero) .
  match shift_right n i with
  | 0                     => false
  | + Binary.One          => true
  | + Binary.AppendZero _ => false
  | + Binary.AppendOne _  => true
  end.

(* The conversions to and from [NatWithZero], used to state the laws: they
 * go through [Nat], which is unary, so they are for proofs, not for
 * computing.
 *)
(* [BinaryWithZero -> NatWithZero] *)
Definition to_nat_with_zero := fun (n : BinaryWithZero) .
  match n with
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive (Binary.to_nat p)
  end.

(* [NatWithZero -> BinaryWithZero] *)
Definition from_nat_with_zero := fun (n : NatWithZero) .
  match n with
  | NatWithZero.Zero       => 0
  | NatWithZero.Positive p => + Binary.from_nat p
  end.

Module conversion. (* conversion *)

(* conversion.successor *)
Theorem successor
  : forall (n : BinaryWithZero) .
      to_nat_with_zero (++ n) = NatWithZero.inc (to_nat_with_zero n).
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Binary.conversion.successor &p) in |- *.
    simpl Nat.inc in |- *.
    quod idem est.
Qed.

(* conversion.retraction *)
Theorem retraction
  : forall (n : NatWithZero) . to_nat_with_zero (from_nat_with_zero n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Binary.conversion.retraction &p) in |- *.
    quod idem est.
Qed.

(* conversion.section *)
Theorem section
  : forall (n : BinaryWithZero) . from_nat_with_zero (to_nat_with_zero n) = n.
Proof.
  intro n.
  match n with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Binary.conversion.section &p) in |- *.
    quod idem est.
Qed.

(* conversion.addition *)
Theorem addition
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      to_nat_with_zero (m + n)
      = (to_nat_with_zero m + to_nat_with_zero n)%nat_with_zero.
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    let proof e := Binary.conversion.addition &p &q.
    simpl in |- *.
    leibniz &e in |- *.
    quod idem est.
Qed.

(* conversion.multiplication *)
Theorem multiplication
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      to_nat_with_zero (m * n)
      = (to_nat_with_zero m * to_nat_with_zero n)%nat_with_zero.
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Binary.conversion.multiplication &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.power *)
Theorem power
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      to_nat_with_zero (m ^ n)
      = (to_nat_with_zero m ^ to_nat_with_zero n)%nat_with_zero.
Proof.
  intros m n.
  match n with | | q end; match m with | | p end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    leibniz (Binary.conversion.power &p &q) in |- *.
    quod idem est.
Qed.

(* conversion.comparison *)
Theorem comparison
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      compare m n = NatWithZero.compare (to_nat_with_zero m) (to_nat_with_zero n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    ipso (Binary.conversion.comparison &p &q).
Qed.

(* conversion.subtraction *)
Theorem subtraction
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      Option.map to_nat_with_zero (sub m n)
      = NatWithZero.sub (to_nat_with_zero m) (to_nat_with_zero n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    lemma sum
      : (NatWithZero.Zero + NatWithZero.Zero)%nat_with_zero = NatWithZero.Zero.
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (NatWithZero.subtraction.specification
         NatWithZero.Zero NatWithZero.Zero NatWithZero.Zero),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma below
      : (NatWithZero.Zero < NatWithZero.Positive (Binary.to_nat &q))%nat_with_zero.
    {
      simpl NatWithZero.LessThan in |- *.
      exists (Binary.to_nat &q).
      simpl in |- *.
      quod idem est.
    }
    leibniz (NatWithZero.subtraction.truncation &below) in |- *.
    quod idem est.
  -
    simpl in |- *.
    lemma sum
      : (NatWithZero.Zero + NatWithZero.Positive (Binary.to_nat &p))%nat_with_zero
        = NatWithZero.Positive (Binary.to_nat &p).
    {
      simpl in |- *.
      quod idem est.
    }
    modus aequans
      (NatWithZero.subtraction.specification
         (NatWithZero.Positive (Binary.to_nat &p)) NatWithZero.Zero
         (NatWithZero.Positive (Binary.to_nat &p))),
      &sum
    |- e.
    leibniz &e in |- *.
    quod idem est.
  -
    simpl in |- *.
    let proof h := Binary.conversion.difference &p &q.
    extro &h.
    match (Binary.difference &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      lemma below
        : (NatWithZero.Positive (Binary.to_nat &p)
           < NatWithZero.Positive (Binary.to_nat &q))%nat_with_zero.
      {
        simpl NatWithZero.LessThan in |- *.
        simpl Nat.LessThan in &h.
        match &h with | k e end.
        exists &k.
        simpl in |- *.
        leibniz &e in |- *.
        quod idem est.
      }
      leibniz (NatWithZero.subtraction.truncation &below) in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (NatWithZero.Positive (Binary.to_nat &q) + NatWithZero.Zero)%nat_with_zero
          = NatWithZero.Positive (Binary.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (NatWithZero.subtraction.specification
           (NatWithZero.Positive (Binary.to_nat &p))
           (NatWithZero.Positive (Binary.to_nat &q)) NatWithZero.Zero),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      lemma sum
        : (NatWithZero.Positive (Binary.to_nat &q)
           + NatWithZero.Positive (Binary.to_nat &d))%nat_with_zero
          = NatWithZero.Positive (Binary.to_nat &p).
      {
        simpl in |- *.
        leibniz &h in |- *.
        quod idem est.
      }
      modus aequans
        (NatWithZero.subtraction.specification
           (NatWithZero.Positive (Binary.to_nat &p))
           (NatWithZero.Positive (Binary.to_nat &q))
           (NatWithZero.Positive (Binary.to_nat &d))),
        &sum
      |- e.
      leibniz &e in |- *.
      quod idem est.
Qed.

Module subtraction. (* conversion.subtraction *)

(* conversion.subtraction.saturating *)
Theorem saturating
  : forall (m : BinaryWithZero) (n : BinaryWithZero) .
      to_nat_with_zero (saturating_sub m n)
      = NatWithZero.saturating_sub (to_nat_with_zero m) (to_nat_with_zero n).
Proof.
  intros m n.
  match m with | | p end; match n with | | q end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    simpl saturating_sub, sub in |- *.
    let proof h := Binary.conversion.difference &p &q.
    extro &h.
    match (Binary.difference &p &q) with | | | d end.
    +
      intro h.
      simpl in |- *.
      let proof le : (Binary.to_nat &p <= Binary.to_nat &q)%nat := disjoin _, &h.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      let proof le : (Binary.to_nat &p <= Binary.to_nat &q)%nat := disjoin &h, _.
      leibniz (Nat.subtraction.truncation &le) in |- *.
      simpl in |- *.
      quod idem est.
    +
      intro h.
      simpl in |- *.
      leibniz <- &h in |- *.
      leibniz (Nat.addition.commutativity (Binary.to_nat &q) (Binary.to_nat &d)) in |- *.
      leibniz (Nat.subtraction.inversion.of.addition (Binary.to_nat &d) (Binary.to_nat &q))
        in |- *.
      simpl in |- *.
      quod idem est.
Qed.

End subtraction. (* conversion.subtraction *)

(* conversion.appending *)
Theorem appending
  : forall (n : BinaryWithZero) (bit : Bool) .
      to_nat_with_zero (append_bit n bit)
      = match bit with
        | true  => NatWithZero.inc (to_nat_with_zero n + to_nat_with_zero n)%nat_with_zero
        | false => (to_nat_with_zero n + to_nat_with_zero n)%nat_with_zero
        end.
Proof.
  intros n bit.
  match n with | | p end.
  -
    match bit with | | end.
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
  -
    match bit with | | end.
    +
      simpl in |- *.
      simpl Nat.inc in |- *.
      quod idem est.
    +
      simpl in |- *.
      quod idem est.
Qed.

Module left. (* conversion.left *)

(* conversion.left.shift *)
Theorem shift
  : forall (n : BinaryWithZero) (k : NatWithZero) .
      to_nat_with_zero (shift_left n k)
      = (to_nat_with_zero n
         * NatWithZero.Positive (Nat.Successor Nat.One) ^ k)%nat_with_zero.
Proof.
  intros n k.
  match k with | | k' end.
  -
    simpl shift_left, NatWithZero.power in |- *.
    let proof i := NatWithZero.multiplication.identity (to_nat_with_zero &n).
    match &i with | l r end.
    leibniz &r in |- *.
    quod idem est.
  -
    simpl shift_left in |- *.
    match n with | | p end.
    +
      match k' with | | k'' by IH end per Nat.induction.
      *
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl in &IH.
        leibniz (conversion.appending (shift_left_nat 0 &k'') false) in |- *.
        simpl in |- *.
        leibniz &IH in |- *.
        simpl in |- *.
        quod idem est.
    +
      match k' with | | k'' by IH end per Nat.induction.
      *
        simpl in |- *.
        leibniz (Nat.multiplication.commutativity
                   (Binary.to_nat &p) (Nat.Successor Nat.One)) in |- *.
        simpl in |- *.
        quod idem est.
      *
        simpl in |- *.
        simpl in &IH.
        leibniz (conversion.appending (shift_left_nat (+ &p) &k'') false) in |- *.
        simpl in |- *.
        leibniz &IH in |- *.
        simpl in |- *.
        leibniz (Nat.multiplication.left.distributivity.over.addition
                   (Binary.to_nat &p)
                   (Nat.power (Nat.Successor Nat.One) &k'')
                   (Nat.power (Nat.Successor Nat.One) &k'')) in |- *.
        quod idem est.
Qed.

End left. (* conversion.left *)

End conversion. (* conversion *)

Module halving. (* halving *)

(* halving.retraction *)
Theorem retraction
  : forall (n : BinaryWithZero) (bit : Bool) . halve (append_bit n bit) = n.
Proof.
  intros n bit.
  match n with | | p end; match bit with | | end; simpl in |- *; quod idem est.
Qed.

End halving. (* halving *)

Module appending. (* appending *)

Module distributivity. (* appending.distributivity *)

Module over. (* appending.distributivity.over *)

(* appending.distributivity.over.conjunction *)
Theorem conjunction
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (b : Bool) (c : Bool) .
      append_bit (m && n) (b && c)%bool = append_bit m b && append_bit n c.
Proof.
  intros m n b c.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

(* appending.distributivity.over.disjunction *)
Theorem disjunction
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (b : Bool) (c : Bool) .
      append_bit (m || n) (b || c)%bool = append_bit m b || append_bit n c.
Proof.
  intros m n b c.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

(* appending.distributivity.over.sejunction *)
Theorem sejunction
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (b : Bool) (c : Bool) .
      append_bit (m ^^ n) (b ^^ c)%bool = append_bit m b ^^ append_bit n c.
Proof.
  intros m n b c.
  match m with | | p end; match n with | | q end; match b with | | end;
    match c with | | end; simpl in |- *; quod idem est.
Qed.

End over. (* appending.distributivity.over *)

End distributivity. (* appending.distributivity *)

End appending. (* appending *)

Module conjunction. (* conjunction *)

(* conjunction.annihilation *)
Theorem annihilation
  : forall (n : BinaryWithZero) . (0 && n = 0) /\ (n && 0 = 0).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) . m && n = n && m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof a := conjunction.annihilation (append_bit &m' &b).
      match &a with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.conjunction &m' &n' &b &c),
              <- (appending.distributivity.over.conjunction &n' &m' &c &b) in |- *.
      leibniz (&IH &n'), (Bool.conjunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* conjunction.associativity *)
Theorem associativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (o : BinaryWithZero) .
      (m && n) && o = m && (n && o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof a := conjunction.annihilation (append_bit &m' &b).
      match &a with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      leibniz &r in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinaryWithZero.induction.
      *
        let proof a := conjunction.annihilation (append_bit &m' &b && append_bit &n' &c).
        let proof a' := conjunction.annihilation (append_bit &n' &c).
        let proof a'' := conjunction.annihilation (append_bit &m' &b).
        match &a with | l r end.
        match &a' with | l' r' end.
        match &a'' with | l'' r'' end.
        leibniz &r, &r', &r'' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.conjunction &m' &n' &b &c),
                <- (appending.distributivity.over.conjunction (&m' && &n') &o' (&b && &c)%bool &d),
                <- (appending.distributivity.over.conjunction &n' &o' &c &d),
                <- (appending.distributivity.over.conjunction &m' (&n' && &o') &b (&c && &d)%bool)
          in |- *.
        leibniz (&IH &n' &o'), (Bool.conjunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* conjunction.idempotence *)
Theorem idempotence
  : forall (n : BinaryWithZero) . n && n = n.
Proof.
  intro n.
  match n with | | b n' by IH end per BinaryWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.conjunction &n' &n' &b &b) in |- *.
    leibniz &IH in |- *.
    match b with | | end; simpl in |- *; quod idem est.
Qed.

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.identity *)
Theorem identity
  : forall (n : BinaryWithZero) . (0 || n = n) /\ (n || 0 = n).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) . m || n = n || m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof i := disjunction.identity (append_bit &m' &b).
      match &i with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.disjunction &m' &n' &b &c),
              <- (appending.distributivity.over.disjunction &n' &m' &c &b) in |- *.
      leibniz (&IH &n'), (Bool.disjunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* disjunction.associativity *)
Theorem associativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (o : BinaryWithZero) .
      (m || n) || o = m || (n || o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof i := disjunction.identity (append_bit &m' &b).
      match &i with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinaryWithZero.induction.
      *
        let proof i := disjunction.identity (append_bit &m' &b || append_bit &n' &c).
        let proof i' := disjunction.identity (append_bit &n' &c).
        match &i with | l r end.
        match &i' with | l' r' end.
        leibniz &r, &r' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.disjunction &m' &n' &b &c),
                <- (appending.distributivity.over.disjunction (&m' || &n') &o' (&b || &c)%bool &d),
                <- (appending.distributivity.over.disjunction &n' &o' &c &d),
                <- (appending.distributivity.over.disjunction &m' (&n' || &o') &b (&c || &d)%bool)
          in |- *.
        leibniz (&IH &n' &o'), (Bool.disjunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* disjunction.idempotence *)
Theorem idempotence
  : forall (n : BinaryWithZero) . n || n = n.
Proof.
  intro n.
  match n with | | b n' by IH end per BinaryWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.disjunction &n' &n' &b &b) in |- *.
    leibniz &IH in |- *.
    match b with | | end; simpl in |- *; quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.identity *)
Theorem identity
  : forall (n : BinaryWithZero) . (0 ^^ n = n) /\ (n ^^ 0 = n).
Proof.
  intro n.
  divide et impera.
  -
    simpl in |- *.
    quod idem est.
  -
    match n with | | p end; simpl in |- *; quod idem est.
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) . m ^^ n = n ^^ m.
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intro n.
    match n with | | q end; simpl in |- *; quod idem est.
  -
    intro n.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof i := sejunction.identity (append_bit &m' &b).
      match &i with | l r end.
      leibniz &r, &l in |- *.
      quod idem est.
    +
      leibniz <- (appending.distributivity.over.sejunction &m' &n' &b &c),
              <- (appending.distributivity.over.sejunction &n' &m' &c &b) in |- *.
      leibniz (&IH &n'), (Bool.sejunction.commutativity &b &c) in |- *.
      quod idem est.
Qed.

(* sejunction.associativity *)
Theorem associativity
  : forall (m : BinaryWithZero) (n : BinaryWithZero) (o : BinaryWithZero) .
      (m ^^ n) ^^ o = m ^^ (n ^^ o).
Proof.
  intro m.
  match m with | | b m' by IH end per BinaryWithZero.induction.
  -
    intros n o.
    simpl in |- *.
    quod idem est.
  -
    intros n o.
    match n with | | c n' by _ end per BinaryWithZero.induction.
    +
      let proof i := sejunction.identity (append_bit &m' &b).
      match &i with | l r end.
      leibniz &r in |- *.
      simpl in |- *.
      quod idem est.
    +
      match o with | | d o' by _ end per BinaryWithZero.induction.
      *
        let proof i := sejunction.identity (append_bit &m' &b ^^ append_bit &n' &c).
        let proof i' := sejunction.identity (append_bit &n' &c).
        match &i with | l r end.
        match &i' with | l' r' end.
        leibniz &r, &r' in |- *.
        quod idem est.
      *
        leibniz <- (appending.distributivity.over.sejunction &m' &n' &b &c),
                <- (appending.distributivity.over.sejunction (&m' ^^ &n') &o' (&b ^^ &c)%bool &d),
                <- (appending.distributivity.over.sejunction &n' &o' &c &d),
                <- (appending.distributivity.over.sejunction &m' (&n' ^^ &o') &b (&c ^^ &d)%bool)
          in |- *.
        leibniz (&IH &n' &o'), (Bool.sejunction.associativity &b &c &d) in |- *.
        quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity
  : forall (n : BinaryWithZero) . n ^^ n = 0.
Proof.
  intro n.
  match n with | | b n' by IH end per BinaryWithZero.induction.
  -
    simpl in |- *.
    quod idem est.
  -
    leibniz <- (appending.distributivity.over.sejunction &n' &n' &b &b) in |- *.
    leibniz &IH, (Bool.sejunction.irreflexivity &b) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End sejunction. (* sejunction *)

Module shift. (* shift *)

(* shift.retraction *)
Theorem retraction
  : forall (n : BinaryWithZero) (k : NatWithZero) . shift_right (shift_left n k) k = n.
Proof.
  intros n k.
  match k with | | k' end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl shift_left, shift_right in |- *.
    match k' with | | k'' by IH end per Nat.induction.
    +
      simpl in |- *.
      leibniz (halving.retraction &n false) in |- *.
      quod idem est.
    +
      simpl in |- *.
      leibniz (halving.retraction (shift_left_nat &n &k'') false) in |- *.
      ipso &IH.
Qed.

Module right. (* shift.right *)

(* shift.right.successor *)
Theorem successor
  : forall (n : BinaryWithZero) (i : NatWithZero) .
      shift_right n (NatWithZero.inc i) = shift_right (halve n) i.
Proof.
  intros n i.
  match i with | | k end.
  -
    simpl in |- *.
    quod idem est.
  -
    simpl in |- *.
    quod idem est.
Qed.

End right. (* shift.right *)

End shift. (* shift *)

Module bit. (* bit *)

(* bit.absence *)
Theorem absence
  : forall (i : NatWithZero) . test_bit 0 i = false.
Proof.
  intro i.
  simpl test_bit, shift_right in |- *.
  match i with | | k end.
  -
    quod idem est.
  -
    match k with | | k' by IH end per Nat.induction.
    +
      simpl in |- *.
      quod idem est.
    +
      simpl in |- *.
      ipso &IH.
Qed.

(* bit.parity *)
Theorem parity
  : forall (n : BinaryWithZero) (bit : Bool) .
      test_bit (append_bit n bit) NatWithZero.Zero = bit.
Proof.
  intros n bit.
  simpl test_bit, shift_right in |- *.
  match n with | | p end; match bit with | | end; simpl in |- *; quod idem est.
Qed.

(* bit.successor *)
Theorem successor
  : forall (n : BinaryWithZero) (bit : Bool) (i : NatWithZero) .
      test_bit (append_bit n bit) (NatWithZero.inc i) = test_bit n i.
Proof.
  intros n bit i.
  simpl test_bit in |- *.
  leibniz (shift.right.successor (append_bit &n &bit) &i) in |- *.
  leibniz (halving.retraction &n &bit) in |- *.
  quod idem est.
Qed.

End bit. (* bit *)

End BinaryWithZero. (* BinaryWithZero *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinaryWithZero], not [BinaryWithZero.T]. [Zero] and [Positive] name ctors
 * of [NatWithZero] and [Integer] as well, so all three write theirs with the
 * prefix.
 *)
Abbreviation BinaryWithZero := BinaryWithZero.T.

(* Makes the notations declared in [Module BinaryWithZero] usable in every
 * file that imports this one, as [(m + n)%binary_with_zero] or under an
 * opened [jwa_binary_with_zero_scope]. Only the notations are exported:
 * [add] and the laws still need the [BinaryWithZero.] prefix, and the local
 * aliases [0] and [+ p] stay inside the module.
 *)
Export (notations) BinaryWithZero.

(* A [Binary] stands wherever a [BinaryWithZero] is expected, read as its
 * [Positive], and the conversion is printed where it happened.
 *)
Coercion BinaryWithZero.Positive : Binary >-> BinaryWithZero.
Add Printing Coercion BinaryWithZero.Positive.
