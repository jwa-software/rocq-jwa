(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
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

(* [Positive] wraps a [Binary], so an operation here reduces to the [Binary]
 * one plus the [Zero] cases, as [NatWithZero] does over [Nat].
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

End conversion. (* conversion *)

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
