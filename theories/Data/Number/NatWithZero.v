(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianMonoid.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Algebra.Semiring.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Transitive.

(* [Positive] wraps a [Nat], so an operation here reduces to the [Nat] one
 * plus the [Zero] cases.
 *)
Inductive NatWithZero : Type :=
  | Zero     : NatWithZero
  | Positive : Nat -> NatWithZero.

(* A module may carry the type's name; its members read [NatWithZero.add]. *)
Module NatWithZero. (* NatWithZero *)

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] is a prefix, apart from the infix [+].
 *)
Local Notation "0" := Zero (only parsing).
Local Notation "+ p" := (Positive p)
  (at level 35, right associativity, only parsing).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition add := fun (m : NatWithZero) (n : NatWithZero) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => + (Nat.add p q)
      end
  end.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition mul := fun (m : NatWithZero) (n : NatWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => + (Nat.mul p q)
      end
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End NatWithZero] a client writes [(m + n)%nat_with_zero].
 * [only parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_nat_with_zero_scope.

Local Open Scope jwa_nat_with_zero_scope.

(* [NatWithZero -> NatWithZero] *)
Definition inc := fun (n : NatWithZero) .
  match n with
  | 0   => + One
  | + p => + (Nat.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_nat_with_zero_scope.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition power := fun (m : NatWithZero) (n : NatWithZero) .
  match n with
  | 0   => + One
  | + q =>
      match m with
      | 0   => 0
      | + p => + (Nat.power p q)
      end
  end.

(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessThan := fun (m : NatWithZero) (n : NatWithZero) .
  exists (k : Nat) . m + (+ k) = n.

(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessOrEqual := fun (m : NatWithZero) (n : NatWithZero) .
  m = n \/ LessThan m n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_nat_with_zero_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_nat_with_zero_scope.

(* [NatWithZero -> NatWithZero -> Comparison] *)
Definition compare := fun (m : NatWithZero) (n : NatWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Eq
      | + _ => Lt
      end
  | + p =>
      match n with
      | 0   => Gt
      | + q => Nat.compare p q
      end
  end.

(* [NatWithZero -> NatWithZero -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [NatWithZero -> NatWithZero -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Abbreviation min := (Comparable.min compare).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Abbreviation max := (Comparable.max compare).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition saturating_sub := fun (m : NatWithZero) (n : NatWithZero) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => + p
      | + q =>
          match Nat.sub p q with
          | None   => 0
          | Some k => + k
          end
      end
  end.

(* [NatWithZero -> NatWithZero -> Option NatWithZero] *)
Definition sub := fun (m : NatWithZero) (n : NatWithZero) .
  match le n m with
  | true  => Some (saturating_sub m n)
  | false => None
  end.

(* Euclidean division of a positive by a positive, by walking the dividend
 * down: each step adds one to the remainder, and the quotient goes up when
 * the remainder reaches the divisor. The divisor is a [Nat], so it is never
 * zero. The result is the pair of quotient and remainder.
 *)
(* [Nat -> Nat -> Product NatWithZero NatWithZero] *)
Fixpoint division (dividend : Nat) (divisor : Nat) : Product NatWithZero NatWithZero :=
  match dividend with
  | One =>
      match divisor with
      | One         => Product_introduction (+ One) 0
      | Successor _ => Product_introduction 0 (+ One)
      end
  | Successor dividend' =>
      match division dividend' divisor with
      | Product_introduction quotient remainder =>
          match eq (++ remainder) (+ divisor) with
          | true  => Product_introduction (++ quotient) 0
          | false => Product_introduction quotient      (++ remainder)
          end
      end
  end.

Local Open Scope jwa_product_scope.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition divide := fun (n : NatWithZero) (divisor : Nat) .
  match n with
  | 0          => 0
  | + dividend => pi_1 (division dividend divisor)
  end.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition modulo := fun (n : NatWithZero) (divisor : Nat) .
  match n with
  | 0          => 0
  | + dividend => pi_2 (division dividend divisor)
  end.

Local Close Scope jwa_product_scope.

(* [d] divides [n] when some multiple of [d] is [n]. It is a partial order:
 * reflexive with [Positive One], transitive by multiplying the witnesses,
 * antisymmetric since [One] is the only unit.
 *)
(* [NatWithZero -> NatWithZero -> Prop] *)
Definition Divides := fun (d : NatWithZero) (n : NatWithZero) .
  exists (k : NatWithZero) . d * k = n.

(* [NatWithZero -> Prop] *)
Definition Even := fun (n : NatWithZero) . Divides (+ (Successor One)) n.

(* [NatWithZero -> Prop] *)
Definition Odd := fun (n : NatWithZero) .
  exists (k : NatWithZero) . ((+ (Successor One)) * k) + (+ One) = n.

Module positive. (* positive *)

(* positive.injectivity *)
Theorem injectivity
  : forall {m : Nat} {n : Nat} . (+ m) = + n -> m = n.
Proof.
  intros m n e.
  pose proof (Identity.congruence
                (fun (x : NatWithZero) . match x with | 0 => m | + y => y end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

Module order. (* positive.order *)

(* positive.order.embedding *)
Lemma embedding
  : forall (m : Nat) (n : Nat) .
      (+ m) < + n <-> Nat.LessThan m n.
Proof.
  intros m n.
  split.
  - intro h.
    unfold LessThan in h.
    destruct h as [k e].
    simpl in e.
    pose proof (positive.injectivity e) as e'.
    unfold Nat.LessThan in |- *.
    exact (Exists_introduction k e').
  - intro h.
    unfold Nat.LessThan in h.
    destruct h as [k e].
    unfold LessThan in |- *.
    apply (Exists_introduction k).
    simpl in |- *.
    rewrite e in |- *.
    reflexivity.
Qed.

End order. (* positive.order *)

End positive. (* positive *)

Module increment. (* increment *)

(* increment.specification *)
Lemma specification : forall (n : NatWithZero) . (++ n) = (+ One) + n.
Proof.
  intros n.
  destruct n as [| p]; simpl in |- *; reflexivity.
Qed.

End increment. (* increment *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
    (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  destruct l as [| l'].
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + destruct n as [| n'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite Nat.addition.associativity in |- *.
        reflexivity.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : NatWithZero) (n : NatWithZero) . m + n = n + m.
Proof.
  intros m n.
  destruct m as [| m']; destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite Nat.addition.commutativity in |- *.
    reflexivity.
Qed.

(* addition.identity *)
Theorem identity
  : forall (n : NatWithZero) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (addition.commutativity n 0) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Module left. (* addition.left *)

(* addition.left.cancellation *)
Theorem cancellation
  : forall {n : NatWithZero} {m : NatWithZero} {k : NatWithZero} .
      n + m = n + k -> m = k.
Proof.
  intros n m k.
  destruct n as [| n'].
  - simpl in |- *.
    intro e.
    exact e.
  - destruct m as [| m']; destruct k as [| k'].
    + intro e.
      reflexivity.
    + simpl in |- *.
      intro e.
      pose proof (positive.injectivity e) as e'.
      symmetry in e'.
      rewrite (Nat.addition.commutativity n' k') in e'.
      pose proof (Nat.addition.identity.absence k' n') as h.
      unfold Negation in h.
      pose proof (h e') as f.
      contradiction f.
    + simpl in |- *.
      intro e.
      pose proof (positive.injectivity e) as e'.
      rewrite (Nat.addition.commutativity n' m') in e'.
      pose proof (Nat.addition.identity.absence m' n') as h.
      unfold Negation in h.
      pose proof (h e') as f.
      contradiction f.
    + simpl in |- *.
      intro e.
      pose proof (positive.injectivity e) as e'.
      pose proof (Nat.addition.left.cancellation n' m' k' e') as e''.
      rewrite e'' in |- *.
      reflexivity.
Qed.

(* addition.left.commutativity *)
Lemma commutativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  rewrite (addition.commutativity l (m + n)) in |- *.
  rewrite (addition.associativity m n l)     in |- *.
  rewrite (addition.commutativity n l)       in |- *.
  reflexivity.
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.cancellation *)
Theorem cancellation
  : forall {m : NatWithZero} {k : NatWithZero} {n : NatWithZero} .
      m + n = k + n -> m = k.
Proof.
  intros m k n e.
  rewrite (addition.commutativity m n) in e.
  rewrite (addition.commutativity k n) in e.
  exact (addition.left.cancellation e).
Qed.

Module identity. (* addition.right.identity *)

(* addition.right.identity.absence *)
Lemma absence
  : forall (m : NatWithZero) (n : Nat) . ~ (m + (+ n) = 0).
Proof.
  intros m n.
  unfold Negation in |- *.
  destruct m as [| m'].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    discriminate e.
Qed.

End identity. (* addition.right.identity *)

Module order. (* addition.right.order *)

(* addition.right.order.extensivity *)
Theorem extensivity
  : forall (m : NatWithZero) (n : NatWithZero) . n <= m + n.
Proof.
  intros m n.
  unfold LessOrEqual in |- *.
  destruct m as [| m'].
  - simpl in |- *.
    exact (Disjunction.L (Identity.reflexivity n)).
  - apply Disjunction.R.
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    exact (addition.commutativity n (+ m')).
Qed.

(* addition.right.order.positivity *)
Theorem positivity
  : forall (n : NatWithZero) (k : Nat) . 0 < n + (+ k).
Proof.
  intros n k.
  unfold LessThan in |- *.
  destruct n as [| n'].
  - simpl in |- *.
    apply (Exists_introduction k).
    reflexivity.
  - simpl in |- *.
    apply (Exists_introduction (Nat.add n' k)).
    reflexivity.
Qed.

End order. (* addition.right.order *)

End right. (* addition.right *)

(* addition.cancellation *)
Theorem cancellation
  : forall (m : NatWithZero) (n : NatWithZero) (k : NatWithZero) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (@addition.left.cancellation m n k).
  - exact (@addition.right.cancellation m k n).
Qed.

(* addition.interchange *)
Theorem interchange
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero) .
      (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  rewrite (addition.associativity a b (c + d)) in |- *.
  rewrite (addition.left.commutativity b c d)  in |- *.
  rewrite (addition.associativity a c (b + d)) in |- *.
  reflexivity.
Qed.

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* "Strict" names the order preserved, not a direction: a strictly monotone
 * function carries [<] to [<] (equality excluded), a monotone one [<=] to
 * [<=].
 *)
(* addition.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition.associativity k m (+ d)) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* addition.order.strict.cancellation *)
Theorem cancellation
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      k + m < k + n -> m < n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  rewrite (addition.associativity k m (+ d)) in e.
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  exact (addition.left.cancellation e).
Qed.

End strict. (* addition.order.strict *)

(* addition.order.monotonicity *)
Theorem monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      m <= n -> k + m <= k + n.
Proof.
  intros k m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    unfold LessOrEqual in |- *.
    exact (Disjunction.L (Identity.reflexivity (k + n))).
  - unfold LessOrEqual in |- *.
    apply Disjunction.R.
    exact (addition.order.strict.monotonicity k m n lt).
Qed.

End order. (* addition.order *)

End addition. (* addition *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (m : NatWithZero) (n : NatWithZero) . m * n = n * m.
Proof.
  intros m n.
  destruct m as [| m']; destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' n') in |- *.
    reflexivity.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  destruct l as [| l'].
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + destruct n as [| n'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication.associativity l' m' n') in |- *.
        reflexivity.
Qed.

(* multiplication.annihilation *)
Theorem annihilation
  : forall (n : NatWithZero) . (0 * n = 0) /\ (n * 0 = 0).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (multiplication.commutativity n 0) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Lemma identity : forall (n : NatWithZero) . (+ One) * n = n.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  destruct l as [| l'].
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + destruct n as [| n'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication.left.distributivity.over.addition l' m' n') in |- *.
        reflexivity.
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

Module order. (* multiplication.left.order *)

Module strict. (* multiplication.left.order.strict *)

(* multiplication.left.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : Nat) (m : NatWithZero) (n : NatWithZero) .
      m < n -> (+ k) * m < (+ k) * n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  symmetry in e.
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul k d)).
  destruct m as [| m'].
  - simpl in e.
    rewrite e in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in e.
    rewrite e in |- *.
    simpl in |- *.
    rewrite (Nat.multiplication.left.distributivity.over.addition k m' d) in |- *.
    reflexivity.
Qed.

End strict. (* multiplication.left.order.strict *)

End order. (* multiplication.left.order *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
Lemma identity : forall (m : NatWithZero) . m * (+ One) = m.
Proof.
  intros m.
  destruct m as [| m'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  rewrite (multiplication.commutativity (m + n) l) in |- *.
  rewrite (multiplication.left.distributivity.over.addition l m n) in |- *.
  rewrite (multiplication.commutativity l m) in |- *.
  rewrite (multiplication.commutativity l n) in |- *.
  reflexivity.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (n : NatWithZero) . ((+ One) * n = n) /\ (n * (+ One) = n).
Proof.
  intros n.
  split.
  - exact (multiplication.left.identity  n).
  - exact (multiplication.right.identity n).
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : NatWithZero) (y : NatWithZero) (z : NatWithZero) .
      (x * (y + z) = (x * y) + (x * z))
    /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  split.
  - exact (multiplication.left.distributivity.over.addition  x y z).
  - exact (multiplication.right.distributivity.over.addition x y z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module power. (* power *)

Module exponent. (* power.exponent *)

(* power.exponent.absence *)
Lemma absence : forall (m : NatWithZero) . power m 0 = + One.
Proof.
  intros m.
  simpl in |- *.
  reflexivity.
Qed.

(* power.exponent.addition *)
Theorem addition
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero) .
      power m a * power m b = power m (a + b).
Proof.
  intros m a b.
  destruct a as [| a']; destruct b as [| b'].
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m']; simpl in |- *; reflexivity.
  - destruct m as [| m'].
    * simpl in |- *.
      reflexivity.
    * simpl in |- *.
      rewrite (Nat.multiplication.commutativity (Nat.power m' a') One) in |- *.
      simpl in |- *.
      reflexivity.
  - destruct m as [| m'].
    * simpl in |- *.
      reflexivity.
    * simpl in |- *.
      rewrite (Nat.power.exponent.addition m' a' b') in |- *.
      reflexivity.
Qed.

(* power.exponent.multiplication *)
Theorem multiplication
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero) .
      power (power m a) b = power m (a * b).
Proof.
  intros m a b.
  destruct a as [| a']; destruct b as [| b'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.power.annihilation b') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m'].
    * simpl in |- *.
      reflexivity.
    * simpl in |- *.
      rewrite (Nat.power.exponent.multiplication m' a' b') in |- *.
      reflexivity.
Qed.

End exponent. (* power.exponent *)

Module distributivity. (* power.distributivity *)

Module over. (* power.distributivity.over *)

(* power.distributivity.over.multiplication *)
Theorem multiplication
  : forall (m : NatWithZero) (n : NatWithZero) (a : NatWithZero) .
      power (m * n) a = power m a * power n a.
Proof.
  intros m n a.
  destruct a as [| a'].
  - simpl in |- *.
    reflexivity.
  - destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + destruct n as [| n'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.power.distributivity.over.multiplication m' n' a') in |- *.
        reflexivity.
Qed.

End over. (* power.distributivity.over *)

End distributivity. (* power.distributivity *)

End power. (* power *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : NatWithZero) . ~ (n < n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  simpl in e.
  destruct n as [| n'].
  - discriminate e.
  - pose proof (positive.injectivity e) as e'.
    rewrite (Nat.addition.commutativity n' k) in e'.
    pose proof (Nat.addition.identity.absence k n') as i.
    unfold Negation in i.
    pose proof (i e') as f.
    contradiction f.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : NatWithZero} {m : NatWithZero} {n : NatWithZero} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  symmetry in e1, e2.
  rewrite e2 in |- *.
  rewrite e1 in |- *.
  rewrite (addition.associativity l (+ k1) (+ k2)) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End strict. (* order.strict *)

(* Discreteness: nothing sits strictly between [n] and [n + One], so [<] and
 * [<=] determine each other by a step of one.
 *)
(* order.discreteness *)
Theorem discreteness
  : forall (m : NatWithZero) (n : NatWithZero) .
      m < n + (+ One) <-> m <= n.
Proof.
  intros m n.
  split.
  - intro h.
    unfold LessThan    in h.
    unfold LessOrEqual in |- *.
    destruct h as [k e].
    destruct k as [| k'].
    + apply Disjunction.L.
      exact (addition.right.cancellation e).
    + apply Disjunction.R.
      unfold LessThan in |- *.
      apply (Exists_introduction k').
      change (+ (Successor k'))
        with ((+ One) + (+ k'))
        in e.
      rewrite -> (addition.commutativity (+ One) (+ k'))
              in e.
      rewrite <- (addition.associativity m (+ k') (+ One))
              in e.
      exact (addition.right.cancellation e).
  - intro h.
    unfold LessOrEqual in h.
    unfold LessThan    in |- *.
    destruct h as [e | lt].
    + apply (Exists_introduction One).
      rewrite e in |- *.
      reflexivity.
    + unfold LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction (Successor k)).
      change (+ (Successor k))
        with ((+ One) + (+ k))
        in |- *.
      rewrite -> (addition.commutativity (+ One) (+ k))
              in |- *.
      rewrite <- (addition.associativity m (+ k) (+ One))
              in |- *.
      rewrite e
              in |- *.
      reflexivity.
Qed.

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero) .
      compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  destruct m as [| m']; destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (Nat.comparison.antisymmetry m' n').
Qed.

Module strict. (* comparison.strict *)

(* comparison.strict.specification *)
Lemma specification
  : forall (m : NatWithZero) (n : NatWithZero) . compare m n = Lt <-> m < n.
Proof.
  intros m n.
  destruct m as [| m']; destruct n as [| n'].
  - split.
    * simpl in |- *.
      intro e.
      discriminate e.
    * intro h.
      pose proof (order.strict.irreflexivity 0) as i.
      unfold Negation in i.
      pose proof (i h) as f.
      contradiction f.
  - split.
    * intro e.
      unfold LessThan in |- *.
      apply (Exists_introduction n').
      simpl in |- *.
      reflexivity.
    * intro h.
      simpl in |- *.
      reflexivity.
  - split.
    * simpl in |- *.
      intro e.
      discriminate e.
    * intro h.
      unfold LessThan in h.
      destruct h as [k e].
      simpl in e.
      discriminate e.
  - split.
    * simpl in |- *.
      intro e.
      exact (<-elim (positive.order.embedding m' n')
                    (Nat.comparison.strict.forward.specification m' n' e)).
    * intro h.
      simpl in |- *.
      exact (Nat.comparison.strict.backward.specification
              m' n'
              (->elim (positive.order.embedding m' n') h)).
Qed.

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Lemma specification
  : forall (m : NatWithZero) (n : NatWithZero) . compare m n = Eq <-> m = n.
Proof.
  intros m n.
  split.
  - intro e.
    destruct m as [| m']; destruct n as [| n'].
    + reflexivity.
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
    + simpl in e.
      rewrite (Nat.comparison.equality.forward.specification m' n' e) in |- *.
      reflexivity.
  - intro e.
    rewrite e in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (Comparable.comparison.reflexivity n').
Qed.

End equality. (* comparison.equality *)

(* comparison.specification *)
Theorem specification
  : forall (m : NatWithZero) (n : NatWithZero) .
      (compare m n = Lt <-> m < n) /\ (compare m n = Eq <-> m = n).
Proof.
  intros m n.
  split.
  - exact (comparison.strict.specification
            m n).
  - exact (comparison.equality.specification
            m n).
Qed.

End comparison. (* comparison *)

(* The one declaration that cannot be hoisted above the topics: it is built
 * from laws proved in [order] and [comparison], and the generic [min], [max]
 * and [le] laws below take it implicitly, so every topic after this point
 * may use them and no topic before it can.
 *)
Instance comparable
  : Comparable compare LessThan :=
  {| Comparable.transitivity  := @order.strict.transitivity
   ; Comparable.specification := comparison.specification
   ; Comparable.antisymmetry  := comparison.antisymmetry |}.

Module maximum. (* maximum *)

Module left. (* maximum.left *)

(* maximum.left.identity *)
Lemma identity : forall (n : NatWithZero) . max 0 n = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

End left. (* maximum.left *)

Module right. (* maximum.right *)

(* maximum.right.identity *)
Lemma identity : forall (n : NatWithZero) . max n 0 = n.
Proof.
  intros n.
  rewrite (Comparable.maximum.commutativity n 0) in |- *.
  exact (maximum.left.identity n).
Qed.

End right. (* maximum.right *)

(* maximum.identity *)
Theorem identity
  : forall (n : NatWithZero) . (max 0 n = n) /\ (max n 0 = n).
Proof.
  intros n.
  split.
  - exact (maximum.left.identity  n).
  - exact (maximum.right.identity n).
Qed.

End maximum. (* maximum *)

Module minimum. (* minimum *)

Module left. (* minimum.left *)

(* minimum.left.annihilation *)
Lemma annihilation : forall (n : NatWithZero) . min 0 n = 0.
Proof.
  intros n.
  unfold Comparable.min in |- *.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

Module distributivity. (* minimum.left.distributivity *)

Module of. (* minimum.left.distributivity.of *)

(* minimum.left.distributivity.of.addition *)
Theorem addition
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      k + min m n = min (k + m) (k + n).
Proof.
  intros k m n.
  pose proof (Comparable.order.totality m n) as t.
  destruct t as [h | h].
  - rewrite (<-elim (Comparable.minimum.specification m n) h) in |- *.
    rewrite (<-elim (Comparable.minimum.specification (k + m) (k + n))
                    (addition.order.monotonicity k m n h))
                    in |- *.
    reflexivity.
  - rewrite (Comparable.minimum.commutativity m n)             in |- *.
    rewrite (Comparable.minimum.commutativity (k + m) (k + n)) in |- *.
    rewrite (<-elim (Comparable.minimum.specification n m) h)
                    in |- *.
    rewrite (<-elim (Comparable.minimum.specification (k + n) (k + m))
                    (addition.order.monotonicity k n m h))
                    in |- *.
    reflexivity.
Qed.

End of. (* minimum.left.distributivity.of *)

End distributivity. (* minimum.left.distributivity *)

End left. (* minimum.left *)

Module right. (* minimum.right *)

(* minimum.right.annihilation *)
Lemma annihilation : forall (n : NatWithZero) . min n 0 = 0.
Proof.
  intros n.
  rewrite (Comparable.minimum.commutativity n 0) in |- *.
  exact (minimum.left.annihilation n).
Qed.

End right. (* minimum.right *)

(* minimum.annihilation *)
Theorem annihilation
  : forall (n : NatWithZero) . (min 0 n = 0) /\ (min n 0 = 0).
Proof.
  intros n.
  split.
  - exact (minimum.left.annihilation  n).
  - exact (minimum.right.annihilation n).
Qed.

End minimum. (* minimum *)

Module subtraction. (* subtraction *)

Module saturating. (* subtraction.saturating *)

Module inversion. (* subtraction.saturating.inversion *)

Module of. (* subtraction.saturating.inversion.of *)

(* subtraction.saturating.inversion.of.addition *)
Theorem addition
  : forall (m : NatWithZero) (n : NatWithZero) . saturating_sub (m + n) n = m.
Proof.
  intros m n.
  destruct n as [| n']; destruct m as [| m'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.subtraction.truncation n' n' (Comparable.order.reflexivity n')) in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.subtraction.inversion.of.addition m' n') in |- *.
    simpl in |- *.
    reflexivity.
Qed.

End of. (* subtraction.saturating.inversion.of *)

End inversion. (* subtraction.saturating.inversion *)

(* subtraction.saturating.truncation *)
Theorem truncation
  : forall {m : NatWithZero} {n : NatWithZero} . m <= n -> saturating_sub m n = 0.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.subtraction.truncation n' n' (Comparable.order.reflexivity n')) in |- *.
      simpl in |- *.
      reflexivity.
  - unfold LessThan in lt.
    destruct lt as [k e].
    symmetry in e.
    rewrite e in |- *.
    destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.subtraction.truncation
                m' (Nat.add m' k)
                (Disjunction.R (Nat.addition.order.extensivity m' k))) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* subtraction.saturating.specification *)
Theorem specification
  : forall {m : NatWithZero} {n : NatWithZero} .
      n <= m -> n + saturating_sub m n = m.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    rewrite (subtraction.saturating.truncation (Comparable.order.reflexivity m)) in |- *.
    destruct m as [| m']; simpl in |- *; reflexivity.
  - unfold LessThan in lt.
    destruct lt as [k e].
    symmetry in e.
    rewrite e in |- *.
    rewrite (addition.commutativity n (+ k)) in |- *.
    rewrite (subtraction.saturating.inversion.of.addition (+ k) n) in |- *.
    rewrite (addition.commutativity n (+ k)) in |- *.
    reflexivity.
Qed.

Module right. (* subtraction.saturating.right *)

(* subtraction.saturating.right.identity *)
Theorem identity : forall (n : NatWithZero) . saturating_sub n 0 = n.
Proof.
  intros n.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

End right. (* subtraction.saturating.right *)

(* subtraction.saturating.cancellation *)
Theorem cancellation
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      saturating_sub (k + m) (k + n) = saturating_sub m n.
Proof.
  intros k m n.
  destruct k as [| k'].
  - simpl in |- *. reflexivity.
  - destruct m as [| m']; destruct n as [| n'].
    + simpl in |- *.
      rewrite (Nat.subtraction.truncation k' k'
                (Comparable.order.reflexivity k')) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.subtraction.truncation k' (Nat.add k' n')
                 (Disjunction.R (Nat.addition.order.extensivity k' n'))) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.addition.commutativity k' m') in |- *.
      rewrite (Nat.subtraction.inversion.of.addition m' k') in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.subtraction.cancellation k' m' n') in |- *.
      reflexivity.
Qed.

End saturating. (* subtraction.saturating *)

(* subtraction.truncation *)
Theorem truncation
  : forall {m : NatWithZero} {n : NatWithZero} . m < n -> sub m n = None.
Proof.
  intros m n h.
  unfold sub in |- *.
  destruct (le n m) as [|] eqn:c.
  - pose proof (->elim (Comparable.order.reflection n m) c)
      as order.
    unfold Comparable.LessOrEqual in order.
    destruct order as [e | lt].
    + rewrite e in h.
      pose proof (order.strict.irreflexivity m) as i.
      unfold Negation in i.
      pose proof (i h) as f.
      contradiction f.
    + pose proof (Comparable.order.strict.asymmetry m n h) as a.
      unfold Negation in a.
      pose proof (a lt) as f.
      contradiction f.
  - reflexivity.
Qed.

Module inversion. (* subtraction.inversion *)

Module of. (* subtraction.inversion.of *)

(* subtraction.inversion.of.addition *)
Theorem addition
  : forall (m : NatWithZero) (n : NatWithZero) . sub (m + n) n = Some m.
Proof.
  intros m n.
  unfold sub in |- *.
  rewrite (subtraction.saturating.inversion.of.addition m n) in |- *.
  rewrite (<-elim (Comparable.order.reflection n (m + n))
                  (addition.right.order.extensivity m n)) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End of. (* subtraction.inversion.of *)

End inversion. (* subtraction.inversion *)

(* subtraction.specification *)
Theorem specification
  : forall (m : NatWithZero) (n : NatWithZero) (k : NatWithZero) .
      sub m n = Some k <-> n + k = m.
Proof.
  intros m n k.
  split.
  - intro e.
    unfold sub in e.
    destruct (le n m) as [|] eqn:c.
    + pose proof (Option.some.injectivity e) as e'.
      pose proof (->elim (Comparable.order.reflection n m) c) as order.
      rewrite <- e' in |- *.
      exact (subtraction.saturating.specification order).
    + discriminate e.
  - intro e.
    rewrite <- e in |- *.
    rewrite (addition.commutativity n k) in |- *.
    exact (subtraction.inversion.of.addition k n).
Qed.

End subtraction. (* subtraction *)

Module division. (* division *)

Local Open Scope jwa_product_scope.

(* division.invariant *)
Lemma invariant
  : forall (p : Nat) (d : Nat) .
      ((pi_1 (division p d) * (+ d)) + pi_2 (division p d) = + p)
      /\ pi_2 (division p d) < + d.
Proof.
  intros p d.
  induction p as [| p' IH] using Nat_induction.
  - destruct d as [| d']; split; simpl in |- *.
    * reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction One).
      simpl in |- *.
      reflexivity.
    * reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction d').
      simpl in |- *.
      reflexivity.
  - destruct IH as [e lt].
    simpl in |- *.
    destruct (division p' d) as [q r] eqn:D.
    simpl in e.
    simpl in lt.
    destruct (eq (++ r) (+ d)) as [|] eqn:E; split; simpl in |- *.
    * pose proof (->elim (Comparable.comparison.equality.reflection (++ r) (+ d)) E) as full.
      rewrite (increment.specification r) in full.
      rewrite (increment.specification q) in |- *.
      rewrite (multiplication.right.distributivity.over.addition (+ d) (+ One) q)
          in |- *.
      rewrite (multiplication.left.identity (+ d))
          in |- *.
      rewrite (addition.commutativity (+ d) (q * (+ d)))
          in |- *.
      rewrite (addition.commutativity ((q * (+ d)) + (+ d)) 0)
          in |- *.
      simpl in |- *.
      symmetry in full.
      rewrite full in e |- *.
      rewrite (addition.left.commutativity (q * ((+ One) + r)) (+ One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
    * rewrite (increment.specification r) in |- *.
      rewrite (addition.left.commutativity (q * (+ d)) (+ One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in lt.
      destruct lt as [k ek].
      rewrite (increment.specification r) in E.
      rewrite (addition.commutativity (+ One) r) in E.
      rewrite (increment.specification r) in |- *.
      rewrite (addition.commutativity (+ One) r) in |- *.
      destruct k as [| k'].
      { rewrite (<-elim (Comparable.comparison.equality.reflection (r + (+ One)) (+ d)) ek) in E.
        discriminate E. }
      { unfold LessThan in |- *.
        apply (Exists_introduction k').
        rewrite (addition.associativity r (+ One) (+ k')) in |- *.
        simpl in |- *.
        exact ek. }
Qed.

Local Close Scope jwa_product_scope.

(* division.specification *)
Theorem specification
  : forall (n : NatWithZero) (d : Nat) .
      ((divide n d * (+ d)) + modulo n d = n)
      /\ modulo n d < + d.
Proof.
  intros n d.
  destruct n as [| p].
  - simpl in |- *.
    split.
    + reflexivity.
    + unfold LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
  - unfold divide, modulo in |- *.
    exact (division.invariant p d).
Qed.

End division. (* division *)

Module divisibility. (* divisibility *)

(* divisibility.reflexivity *)
Theorem reflexivity : forall (n : NatWithZero) . Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (+ One)).
  exact (multiplication.right.identity n).
Qed.

(* divisibility.transitivity *)
Theorem transitivity
  : forall {l : NatWithZero} {m : NatWithZero} {n : NatWithZero} .
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  unfold Divides in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 * k2)).
  rewrite <- (multiplication.associativity l k1 k2) in |- *.
  rewrite -> e1 in |- *.
  exact e2.
Qed.

(* divisibility.antisymmetry *)
Theorem antisymmetry
  : forall {m : NatWithZero} {n : NatWithZero} . Divides m n -> Divides n m -> m = n.
Proof.
  intros m n h1 h2.
  unfold Divides in h1, h2.
  destruct h1 as [k e1].
  destruct h2 as [j e2].
  destruct m as [| p].
  - simpl in e1.
    exact e1.
  - pose proof (Identity.symmetry e1) as e1'.
    rewrite e1' in e2.
    destruct k as [| k'].
    + simpl in e2.
      discriminate e2.
    + destruct j as [| j'].
      * simpl in e2.
        discriminate e2.
      * simpl in e2.
        pose proof (positive.injectivity e2) as e3.
        rewrite (Nat.multiplication.associativity p k' j') in e3.
        pose proof (Nat.multiplication.commutativity One p) as c.
        simpl in c.
        pose proof (Identity.transitivity e3 c)
                as e4.
        pose proof (Nat.multiplication.left.cancellation p (Nat.mul k' j') One e4)
                as e5.
        pose proof (Nat.multiplication.identity.factorization k' j' e5)
                as f.
        destruct f as [ek ej].
        rewrite ek in e1.
        rewrite (multiplication.right.identity (+ p)) in e1.
        exact e1.
Qed.

(* divisibility.bottom *)
Theorem bottom : forall (n : NatWithZero) . Divides (+ One) n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction n).
  exact (multiplication.left.identity n).
Qed.

(* divisibility.top *)
Theorem top : forall (n : NatWithZero) . Divides n 0.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction 0).
  rewrite (multiplication.commutativity n 0) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Module addition. (* divisibility.addition *)

(* divisibility.addition.closure *)
Theorem closure
  : forall {d : NatWithZero} {m : NatWithZero} {n : NatWithZero} .
      Divides d m -> Divides d n -> Divides d (m + n).
Proof.
  intros d m n h1 h2.
  unfold Divides in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 + k2)).
  rewrite (multiplication.left.distributivity.over.addition d k1 k2) in |- *.
  rewrite e1, e2 in |- *.
  reflexivity.
Qed.

End addition. (* divisibility.addition *)

Module multiplication. (* divisibility.multiplication *)

(* divisibility.multiplication.closure *)
Theorem closure
  : forall (d : NatWithZero) (m : NatWithZero) (n : NatWithZero) .
      Divides d m -> Divides d (m * n).
Proof.
  intros d m n h.
  unfold Divides in h.
  destruct h as [k e].
  unfold Divides in |- *.
  apply (Exists_introduction (k * n)).
  rewrite <- (multiplication.associativity d k n) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

End multiplication. (* divisibility.multiplication *)

End divisibility. (* divisibility *)

Module parity. (* parity *)

(* parity.totality *)
Theorem totality : forall (n : NatWithZero) . Even n \/ Odd n.
Proof.
  intros n.
  destruct n as [| p].
  - apply Disjunction.L.
    unfold Even in |- *.
    unfold Divides in |- *.
    apply (Exists_introduction 0).
    simpl in |- *.
    reflexivity.
  - induction p as [| p' IH] using Nat_induction.
    + apply Disjunction.R.
      unfold Odd in |- *.
      apply (Exists_introduction 0).
      simpl in |- *.
      reflexivity.
    + destruct IH as [even | odd].
      * apply Disjunction.R.
        unfold Even in even.
        unfold Divides in even.
        destruct even as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction k).
        rewrite e in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in odd.
        destruct odd as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction (k + (+ One))).
        rewrite (multiplication.left.distributivity.over.addition
                   (+ (Successor One)) k (+ One)) in |- *.
        change ((+ (Successor One)) * (+ One))
          with ((+ One) + (+ One)) in |- *.
        rewrite <- (addition.associativity
                      ((+ (Successor One)) * k)
                      (+ One) (+ One)) in |- *.
        rewrite e in |- *.
        simpl in |- *.
        rewrite (Nat.addition.commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
Qed.

Module even. (* parity.even *)

Module addition. (* parity.even.addition *)

(* parity.even.addition.closure *)
Theorem closure
  : forall {m : NatWithZero} {n : NatWithZero} . Even m -> Even n -> Even (m + n).
Proof.
  intros m n h1 h2.
  unfold Even in h1, h2 |- *.
  exact (divisibility.addition.closure h1 h2).
Qed.

End addition. (* parity.even.addition *)

End even. (* parity.even *)

Module odd. (* parity.odd *)

Module addition. (* parity.odd.addition *)

(* Two odds meet at an even, not at an odd: the [+ One] each carries pairs
 * off with the other, so the sum is not closed in [Odd].
 *)
(* parity.odd.addition.evenness *)
Theorem evenness
  : forall {m : NatWithZero} {n : NatWithZero} . Odd m -> Odd n -> Even (m + n).
Proof.
  intros m n h1 h2.
  unfold Odd in h1, h2.
  unfold Even in |- *.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction ((k1 + k2) + (+ One))).
  symmetry in e1, e2.
  rewrite e1, e2 in |- *.
  rewrite (multiplication.left.distributivity.over.addition
             (+ (Successor One)) (k1 + k2) (+ One)) in |- *.
  rewrite (multiplication.left.distributivity.over.addition
             (+ (Successor One)) k1 k2) in |- *.
  change ((+ (Successor One)) * (+ One))
    with ((+ One) + (+ One)) in |- *.
  rewrite (addition.interchange
             ((+ (Successor One)) * k1) (+ One)
             ((+ (Successor One)) * k2) (+ One)) in |- *.
  reflexivity.
Qed.

End addition. (* parity.odd.addition *)

End odd. (* parity.odd *)

End parity. (* parity *)

End NatWithZero. (* NatWithZero *)

(* Makes the notations declared in [Module NatWithZero] usable in every file
 * that imports this one, as [(m + n)%nat_with_zero] or under an opened
 * [jwa_nat_with_zero_scope]. Only the notations are exported: [add] and the
 * laws still need the [NatWithZero.] prefix, and the local aliases [0] and
 * [+ p] stay inside the module.
 *)
Export (notations) NatWithZero.

(* Declared inside [Module NatWithZero], whose proofs use it; an instance
 * declared there is dropped at the module's [End], so it is announced again
 * here.
 *)
Existing Instance NatWithZero.comparable.

Instance NatWithZero_add_monoid
  : Monoid NatWithZero.add Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := NatWithZero.addition.associativity |}
  ; Monoid.identity := NatWithZero.addition.identity
  |}.

Instance NatWithZero_add_cancellative
  : Cancellative NatWithZero.add := {|
    Cancellative.cancellation := NatWithZero.addition.cancellation
  |}.

Instance NatWithZero_mul_monoid
  : Monoid NatWithZero.mul (Positive One) := {|
    Monoid.semigroup := {|
      Semigroup.associativity := NatWithZero.multiplication.associativity |}
  ; Monoid.identity := NatWithZero.multiplication.identity |}.

Instance NatWithZero_add_commutative
  : Commutative NatWithZero.add := {|
      Commutative.commutativity := NatWithZero.addition.commutativity
  |}.

Instance NatWithZero_add_abelian_monoid
  : AbelianMonoid NatWithZero.add Zero :=
  {| AbelianMonoid.monoid      := NatWithZero_add_monoid
   ; AbelianMonoid.commutative := NatWithZero_add_commutative |}.

Instance NatWithZero_mul_commutative
  : Commutative NatWithZero.mul := {|
    Commutative.commutativity := NatWithZero.multiplication.commutativity
  |}.

Instance NatWithZero_min_semigroup
  : Semigroup NatWithZero.min :=
  {| Semigroup.associativity := Comparable.minimum.associativity |}.

Instance NatWithZero_max_monoid
  : Monoid NatWithZero.max Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.maximum.associativity |}
   ; Monoid.identity := NatWithZero.maximum.identity |}.

Instance NatWithZero_min_commutative
  : Commutative NatWithZero.min :=
  {| Commutative.commutativity := Comparable.minimum.commutativity |}.

Instance NatWithZero_max_commutative
  : Commutative NatWithZero.max :=
  {| Commutative.commutativity := Comparable.maximum.commutativity |}.

Instance NatWithZero_semiring
  : Semiring NatWithZero.add Zero NatWithZero.mul (Positive One) :=
  {| Semiring.abelian_monoid := NatWithZero_add_abelian_monoid
   ; Semiring.monoid         := NatWithZero_mul_monoid
   ; Semiring.distributivity := NatWithZero.multiplication.distributivity.over.addition
   ; Semiring.annihilation   := NatWithZero.multiplication.annihilation |}.

Instance NatWithZero_divides_partial_order
  : PartialOrder NatWithZero.Divides :=
  {| PartialOrder.reflexivity :=
       {| Reflexive.reflexivity := NatWithZero.divisibility.reflexivity |}
   ; PartialOrder.antisymmetry :=
       {| Antisymmetric.antisymmetry := @NatWithZero.divisibility.antisymmetry |}
   ; PartialOrder.transitivity :=
       {| Transitive.transitivity := @NatWithZero.divisibility.transitivity |} |}.
