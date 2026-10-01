(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.

(* A bit is a binary digit, a datum, where a [Bool] is a truth value; the two
 * are separate types so that neither stands where the other is meant, and
 * [from_bool] and [to_bool] cross between them.
 *)

Module Bit. (* Bit *)

(* [Zero] first, by value; an [if] would therefore take [Zero] as its [then]
 * branch, so a branch on a bit goes through [to_bool].
 *)
Inductive T : Type :=
  | Zero : T
  | One  : T.

Abbreviation Bit := T.

(* [Bit -> Bit] *)
Definition flip := fun (b : Bit) .
  match b with
  | Zero => One
  | One  => Zero
  end.

(* The levels are reserved in [Core.Notations], and the binary operations
 * take the spellings of [jwa_bool_scope]; [only parsing] keeps goals printing
 * the operations by name.
 *)
Notation "~. b" := (flip b) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition and := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => Zero
  | One  => b2
  end.

Notation "b1 && b2" := (and b1 b2) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition or := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => b2
  | One  => One
  end.

Notation "b1 || b2" := (or b1 b2) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition xor := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => b2
  | One  => flip b2
  end.

Notation "b1 ^^ b2" := (xor b1 b2) (only parsing)
  : jwa_bit_scope.

(* [Bool -> Bit] *)
Definition from_bool := fun (b : Bool) .
  match b with
  | true  => One
  | false => Zero
  end.

(* [Bit -> Bool] *)
Definition to_bool := fun (b : Bit) .
  match b with
  | Zero => false
  | One  => true
  end.

Local Open Scope jwa_bit_scope.

Module distinctness. (* distinctness *)

(* distinctness.forward *)
Theorem forward : ~ (Zero = One).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

(* distinctness.backward *)
Theorem backward : ~ (One = Zero).
Proof.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

End distinctness. (* distinctness *)

(* distinctness *)
Theorem distinctness : ~ (Zero = One) /\ ~ (One = Zero).
Proof.
  divide et impera.
  - ipso distinctness.forward.
  - ipso distinctness.backward.
Qed.

Module flipping. (* flipping *)

(* flipping.involution *)
Theorem involution : forall (b : Bit) . ~. ~. b = b.
Proof.
  intros b.
  match b with | Zero | One end; simpl in |- *; quod idem est.
Qed.

End flipping. (* flipping *)

Module conjunction. (* conjunction *)

(* conjunction.associativity *)
Theorem associativity
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      (b1 && b2) && b3 = b1 && (b2 && b3).
Proof.
  intros b1 b2 b3.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    match b3 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* conjunction.commutativity *)
Theorem commutativity
  : forall (b1 : Bit) (b2 : Bit) . b1 && b2 = b2 && b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (b : Bit) . (One && b = b) /\ (b && One = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (conjunction.commutativity b One) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* conjunction.left *)

Module distributivity. (* conjunction.left.distributivity *)

Module over. (* conjunction.left.distributivity.over *)

(* conjunction.left.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      b1 && (b2 ^^ b3) = (b1 && b2) ^^ (b1 && b3).
Proof.
  intros b1 b2 b3.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    match b3 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* conjunction.left.distributivity.over *)

End distributivity. (* conjunction.left.distributivity *)

End left. (* conjunction.left *)

Module right. (* conjunction.right *)

Module distributivity. (* conjunction.right.distributivity *)

Module over. (* conjunction.right.distributivity.over *)

(* conjunction.right.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      (b2 ^^ b3) && b1 = (b2 && b1) ^^ (b3 && b1).
Proof.
  intros b1 b2 b3.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    match b3 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

End over. (* conjunction.right.distributivity.over *)

End distributivity. (* conjunction.right.distributivity *)

End right. (* conjunction.right *)

Module distributivity. (* conjunction.distributivity *)

Module over. (* conjunction.distributivity.over *)

(* conjunction.distributivity.over.sejunction *)
Theorem sejunction
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      (b1 && (b2 ^^ b3) = (b1 && b2) ^^ (b1 && b3))
    /\ ((b2 ^^ b3) && b1 = (b2 && b1) ^^ (b3 && b1)).
Proof.
  intros b1 b2 b3.
  divide et impera.
  - ipso (conjunction.left.distributivity.over.sejunction  b1 b2 b3).
  - ipso (conjunction.right.distributivity.over.sejunction b1 b2 b3).
Qed.

End over. (* conjunction.distributivity.over *)

End distributivity. (* conjunction.distributivity *)

End conjunction. (* conjunction *)

Module disjunction. (* disjunction *)

(* disjunction.associativity *)
Theorem associativity
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      (b1 || b2) || b3 = b1 || (b2 || b3).
Proof.
  intros b1 b2 b3.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    match b3 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* disjunction.commutativity *)
Theorem commutativity
  : forall (b1 : Bit) (b2 : Bit) . b1 || b2 = b2 || b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (b : Bit) . (Zero || b = b) /\ (b || Zero = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (disjunction.commutativity b Zero) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End disjunction. (* disjunction *)

Module sejunction. (* sejunction *)

(* sejunction.associativity *)
Theorem associativity
  : forall (b1 : Bit) (b2 : Bit) (b3 : Bit) .
      (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3).
Proof.
  intros b1 b2 b3.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    match b3 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* sejunction.commutativity *)
Theorem commutativity
  : forall (b1 : Bit) (b2 : Bit) . b1 ^^ b2 = b2 ^^ b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (b : Bit) . (Zero ^^ b = b) /\ (b ^^ Zero = b).
Proof.
  intros b.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (sejunction.commutativity b Zero) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* sejunction.irreflexivity *)
Theorem irreflexivity : forall (b : Bit) . b ^^ b = Zero.
Proof.
  intros b.
  match b with | Zero | One end; simpl in |- *; quod idem est.
Qed.

(* sejunction.inverse *)
Theorem inverse
  : forall (b : Bit) . (b ^^ b = Zero) /\ (b ^^ b = Zero).
Proof.
  intros b.
  divide et impera; ipso (sejunction.irreflexivity b).
Qed.

End sejunction. (* sejunction *)

Module conversion. (* conversion *)

(* conversion.retraction *)
Theorem retraction
  : forall (b : Bool) . to_bool (from_bool b) = b.
Proof.
  intros b.
  match b with | true | false end; simpl in |- *; quod idem est.
Qed.

(* conversion.section *)
Theorem section
  : forall (b : Bit) . from_bool (to_bool b) = b.
Proof.
  intros b.
  match b with | Zero | One end; simpl in |- *; quod idem est.
Qed.

End conversion. (* conversion *)

End Bit. (* Bit *)

Abbreviation Bit := Bit.T.

Export (notations) Bit.

(* Where a [Bit] is expected, a notation reads in this scope without its
 * [%bit].
 *)
Bind Scope jwa_bit_scope with Bit.T.

Instance Bit_and_monoid
  : Monoid Bit.and Bit.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bit.conjunction.associativity |}
  ; Monoid.identity := Bit.conjunction.identity |}.

Instance Bit_or_monoid
  : Monoid Bit.or Bit.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bit.disjunction.associativity |}
  ; Monoid.identity := Bit.disjunction.identity |}.

Instance Bit_xor_monoid
  : Monoid Bit.xor Bit.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bit.sejunction.associativity |}
  ; Monoid.identity := Bit.sejunction.identity |}.

Instance Bit_and_commutative
  : Commutative Bit.and :=
  {| Commutative.commutativity := Bit.conjunction.commutativity |}.

Instance Bit_or_commutative
  : Commutative Bit.or :=
  {| Commutative.commutativity := Bit.disjunction.commutativity |}.

Instance Bit_xor_commutative
  : Commutative Bit.xor :=
  {| Commutative.commutativity := Bit.sejunction.commutativity |}.

Instance Bit_xor_group
  : Group Bit.xor Bit.Zero (fun (b : Bit) . b) :=
  {| Group.monoid := Bit_xor_monoid
  ; Group.inverse := Bit.sejunction.inverse |}.

Instance Bit_xor_abelian_group
  : AbelianGroup Bit.xor Bit.Zero (fun (b : Bit) . b) :=
  {| AbelianGroup.group := Bit_xor_group
  ; AbelianGroup.commutative := Bit_xor_commutative |}.

Instance Bit_ring
  : Ring Bit.xor Bit.Zero (fun (b : Bit) . b) Bit.and Bit.One :=
  {| Ring.abelian_group := Bit_xor_abelian_group
  ; Ring.monoid := Bit_and_monoid
  ; Ring.distributivity := Bit.conjunction.distributivity.over.sejunction |}.
