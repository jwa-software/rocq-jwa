(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Witness.

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

(* The levels are reserved in [Core.Notations]; [only parsing] keeps goals
 * printing the operations by name.
 *)
Notation "~. b" := (flip b) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition and := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => Zero
  | One  => b2
  end.

Notation "b1 &. b2" := (and b1 b2) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition or := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => b2
  | One  => One
  end.

Notation "b1 |. b2" := (or b1 b2) (only parsing)
  : jwa_bit_scope.

(* [Bit -> Bit -> Bit] *)
Definition xor := fun (b1 : Bit) (b2 : Bit) .
  match b1 with
  | Zero => b2
  | One  => flip b2
  end.

Notation "b1 ^. b2" := (xor b1 b2) (only parsing)
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

(* [Bit -> Nat0] *)
Definition to_nat0 := fun (b : Bit) .
  match b with
  | Zero => 0%n0
  | One  => 1%n0
  end.

(* The carry out and the sum of [carry + a + b], the carry first on both
 * sides, so that adders chain carry to carry.
 *)
(* [Bit -> Bit -> Bit -> Product Bit Bit] *)
Definition add_with_carry := fun (carry : Bit) (a : Bit) (b : Bit) .
  (or (and a b) (and carry (xor a b)), xor (xor a b) carry)%product.

(* The borrow out and the difference of [a - b - borrow], the borrow first
 * on both sides, as for [add_with_carry].
 *)
(* [Bit -> Bit -> Bit -> Product Bit Bit] *)
Definition sub_with_borrow := fun (borrow : Bit) (a : Bit) (b : Bit) .
  (or (and (flip a) b) (and borrow (flip (xor a b))), xor (xor a b) borrow)%product.

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
      (b1 &. b2) &. b3 = b1 &. (b2 &. b3).
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
  : forall (b1 : Bit) (b2 : Bit) . b1 &. b2 = b2 &. b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* conjunction.identity *)
Theorem identity
  : forall (b : Bit) . (One &. b = b) /\ (b &. One = b).
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
      b1 &. (b2 ^. b3) = (b1 &. b2) ^. (b1 &. b3).
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
      (b2 ^. b3) &. b1 = (b2 &. b1) ^. (b3 &. b1).
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
      (b1 &. (b2 ^. b3) = (b1 &. b2) ^. (b1 &. b3))
    /\ ((b2 ^. b3) &. b1 = (b2 &. b1) ^. (b3 &. b1)).
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
      (b1 |. b2) |. b3 = b1 |. (b2 |. b3).
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
  : forall (b1 : Bit) (b2 : Bit) . b1 |. b2 = b2 |. b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* disjunction.identity *)
Theorem identity
  : forall (b : Bit) . (Zero |. b = b) /\ (b |. Zero = b).
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
      (b1 ^. b2) ^. b3 = b1 ^. (b2 ^. b3).
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
  : forall (b1 : Bit) (b2 : Bit) . b1 ^. b2 = b2 ^. b1.
Proof.
  intros b1 b2.
  match b1 with | Zero | One end;
    match b2 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* sejunction.identity *)
Theorem identity
  : forall (b : Bit) . (Zero ^. b = b) /\ (b ^. Zero = b).
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
Theorem irreflexivity : forall (b : Bit) . b ^. b = Zero.
Proof.
  intros b.
  match b with | Zero | One end; simpl in |- *; quod idem est.
Qed.

(* sejunction.inverse *)
Theorem inverse
  : forall (b : Bit) . (b ^. b = Zero) /\ (b ^. b = Zero).
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

(* conversion.carry *)
Theorem carry
  : forall (carry : Bit) (a : Bit) (b : Bit) .
      (to_nat0 carry + to_nat0 a + to_nat0 b
        = 2 * to_nat0 (pi_1 (add_with_carry carry a b))%product
          + to_nat0 (pi_2 (add_with_carry carry a b))%product)%n0.
Proof.
  intros carry a b.
  match &carry with | Zero | One end;
    match &a with | Zero | One end;
    match &b with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

Module carry. (* conversion.carry *)

(* Bits [a] and [b] appended below [x] and [y], whose sum with the carry out
 * of [a + b] is [m * o + s], sum with [carry] to [(2 * m) * o] and the sum
 * bit appended below [s]: an adder of [n + 1] places from one of [n].
 *)
(* conversion.carry.propagation *)
Theorem propagation
  : forall (carry : Bit) (a : Bit) (b : Bit)
      (x : Nat0) (y : Nat0) (m : Nat0) (o : Nat0) (s : Nat0) .
      (to_nat0 (pi_1 (add_with_carry carry a b))%product + x + y = m * o + s)%n0 ->
      (to_nat0 carry + (2 * x + to_nat0 a) + (2 * y + to_nat0 b)
        = (2 * m) * o + (2 * s + to_nat0 (pi_2 (add_with_carry carry a b))%product))%n0.
Proof.
  intros carry a b x y m o s h.
  leibniz
    (Nat0.addition.left.commutativity (to_nat0 &carry) (2 * &x)%n0 (to_nat0 &a)),
    (Nat0.addition.interchange
      (2 * &x)%n0 (to_nat0 &carry + to_nat0 &a)%n0 (2 * &y)%n0 (to_nat0 &b)),
    (conversion.carry &carry &a &b),
    <- (Nat0.addition.associativity
      (2 * &x + 2 * &y)%n0
      (2 * to_nat0 (pi_1 (add_with_carry &carry &a &b))%product)%n0
      (to_nat0 (pi_2 (add_with_carry &carry &a &b))%product)),
    <- (Nat0.multiplication.left.distributivity.over.addition 2%n0 &x &y),
    <- (Nat0.multiplication.left.distributivity.over.addition
      2%n0 (&x + &y)%n0 (to_nat0 (pi_1 (add_with_carry &carry &a &b))%product)),
    (Nat0.addition.commutativity
      (&x + &y)%n0 (to_nat0 (pi_1 (add_with_carry &carry &a &b))%product)),
    <- (Nat0.addition.associativity
      (to_nat0 (pi_1 (add_with_carry &carry &a &b))%product) &x &y),
    &h,
    (Nat0.multiplication.left.distributivity.over.addition 2%n0 (&m * &o)%n0 &s),
    (Nat0.addition.associativity
      (2 * (&m * &o))%n0 (2 * &s)%n0
      (to_nat0 (pi_2 (add_with_carry &carry &a &b))%product)),
    <- (Nat0.multiplication.associativity 2%n0 &m &o)
    in |- *.
  quod idem est.
Qed.

End carry. (* conversion.carry *)

(* conversion.borrow *)
Theorem borrow
  : forall (borrow : Bit) (a : Bit) (b : Bit) .
      (to_nat0 a + 2 * to_nat0 (pi_1 (sub_with_borrow borrow a b))%product
        = to_nat0 b + to_nat0 borrow
          + to_nat0 (pi_2 (sub_with_borrow borrow a b))%product)%n0.
Proof.
  intros borrow a b.
  match &borrow with | Zero | One end;
    match &a with | Zero | One end;
    match &b with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

Module borrow. (* conversion.borrow *)

(* [conversion.carry.propagation] for a subtractor: [a] and [b] appended
 * below [x] and [y], whose difference less the borrow out of [a - b] is
 * [s] with [m * o] borrowed, take [borrow] off to the difference bit
 * appended below [s], with [(2 * m) * o] borrowed.
 *)
(* conversion.borrow.propagation *)
Theorem propagation
  : forall (borrow : Bit) (a : Bit) (b : Bit)
      (x : Nat0) (y : Nat0) (m : Nat0) (o : Nat0) (s : Nat0) .
      (x + m * o = y + to_nat0 (pi_1 (sub_with_borrow borrow a b))%product + s)%n0 ->
      (2 * x + to_nat0 a + (2 * m) * o
        = 2 * y + to_nat0 b + to_nat0 borrow
          + (2 * s + to_nat0 (pi_2 (sub_with_borrow borrow a b))%product))%n0.
Proof.
  intros borrow a b x y m o s h.
  leibniz
    (Nat0.multiplication.associativity 2%n0 &m &o),
    (Nat0.addition.associativity (2 * &x)%n0 (to_nat0 &a) (2 * (&m * &o))%n0),
    (Nat0.addition.commutativity (to_nat0 &a) (2 * (&m * &o))%n0),
    <- (Nat0.addition.associativity (2 * &x)%n0 (2 * (&m * &o))%n0 (to_nat0 &a)),
    <- (Nat0.multiplication.left.distributivity.over.addition 2%n0 &x (&m * &o)%n0),
    &h,
    (Nat0.multiplication.left.distributivity.over.addition
      2%n0 (&y + to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0 &s),
    (Nat0.multiplication.left.distributivity.over.addition
      2%n0 &y (to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)),
    (Nat0.addition.associativity
      (2 * &y)%n0
      (2 * to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0
      (2 * &s)%n0),
    (Nat0.addition.commutativity
      (2 * to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0 (2 * &s)%n0),
    <- (Nat0.addition.associativity
      (2 * &y)%n0 (2 * &s)%n0
      (2 * to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0),
    (Nat0.addition.associativity
      (2 * &y + 2 * &s)%n0
      (2 * to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0
      (to_nat0 &a)),
    (Nat0.addition.commutativity
      (2 * to_nat0 (pi_1 (sub_with_borrow &borrow &a &b))%product)%n0 (to_nat0 &a)),
    (conversion.borrow &borrow &a &b),
    (Nat0.addition.interchange
      (2 * &y)%n0 (2 * &s)%n0 (to_nat0 &b + to_nat0 &borrow)%n0
      (to_nat0 (pi_2 (sub_with_borrow &borrow &a &b))%product)),
    <- (Nat0.addition.associativity (2 * &y)%n0 (to_nat0 &b) (to_nat0 &borrow))
    in |- *.
  quod idem est.
Qed.

End borrow. (* conversion.borrow *)

(* conversion.injectivity *)
Theorem injectivity
  : forall {a : Bit} {b : Bit} . to_nat0 a = to_nat0 b -> a = b.
Proof.
  intros a b e.
  match &a with | Zero | One end;
    match &b with | Zero | One end;
    simpl in &e.
  - quod idem est.
  - ex &e quodlibet.
  - ex &e quodlibet.
  - quod idem est.
Qed.

(* conversion.boundedness *)
Theorem boundedness : forall (b : Bit) . (to_nat0 b < 2)%n0.
Proof.
  intros b.
  simpl Nat0.LessThan in |- *.
  match &b with | Zero | One end.
  - exists (Nat.Successor Nat.One).
    simpl in |- *.
    quod idem est.
  - exists Nat.One.
    simpl in |- *.
    quod idem est.
Qed.

Module boundedness. (* conversion.boundedness *)

(* A bit appended below a number less than [m] gives one less than
 * [2 * m].
 *)
(* conversion.boundedness.propagation *)
Theorem propagation
  : forall (h : Nat0) (m : Nat0) (b : Bit) .
      (h < m -> 2 * h + to_nat0 b < 2 * m)%n0.
Proof.
  intros h m b e.
  simpl Nat0.LessThan in &e.
  match &e with | k ek end.
  lemma bound : (to_nat0 &b < 2 * Nat0.Positive &k)%n0.
  {
    simpl Nat0.LessThan in |- *.
    match &b with | Zero | One end.
    - exists (2 * &k)%n.
      simpl in |- *.
      quod idem est.
    - match &k with | One | Successor k' end.
      + exists Nat.One.
        simpl in |- *.
        quod idem est.
      + exists (&k' + Nat.Successor &k')%n.
        simpl in |- *.
        quod idem est.
  }
  leibniz
    <- &ek,
    (Nat0.multiplication.left.distributivity.over.addition
      2%n0 &h (Nat0.Positive &k))
    in |- *.
  ipso
    (Nat0.addition.order.strict.monotonicity
      (2 * &h)%n0 (to_nat0 &b) (2 * Nat0.Positive &k)%n0 &bound).
Qed.

End boundedness. (* conversion.boundedness *)

(* conversion.halving *)
Theorem halving
  : forall (h : Nat0) (b : Bit) .
      (((2 * h + to_nat0 b) /. 2) = h /\ ((2 * h + to_nat0 b) %. 2) = to_nat0 b)%n0.
Proof.
  intros h b.
  lemma witness
    : (&h * 2 + to_nat0 &b = 2 * &h + to_nat0 &b /\ to_nat0 &b < 2)%n0.
  {
    divide et impera.
    - leibniz (Nat0.multiplication.commutativity &h 2%n0) in |- *.
      quod idem est.
    - ipso (conversion.boundedness &b).
  }
  ipso
    (Nat0.division.uniqueness
      (2 * &h + to_nat0 &b)%n0 2%n &h (to_nat0 &b) &witness).
Qed.

Module halving. (* conversion.halving *)

(* conversion.halving.injectivity *)
Theorem injectivity
  : forall {h : Nat0} {k : Nat0} {a : Bit} {b : Bit} .
      (2 * h + to_nat0 a = 2 * k + to_nat0 b)%n0 -> h = k /\ a = b.
Proof.
  intros h k a b e.
  match (conversion.halving &h &a) with | qa ra end.
  match (conversion.halving &k &b) with | qb rb end.
  divide et impera.
  - leibniz <- &qa, <- &qb, &e in |- *.
    quod idem est.
  - lemma facto : to_nat0 &a = to_nat0 &b.
    {
      leibniz <- &ra, <- &rb, &e in |- *.
      quod idem est.
    }
    ipso (conversion.injectivity &facto).
Qed.

End halving. (* conversion.halving *)

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
