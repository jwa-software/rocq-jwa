(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianMonoid.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Algebra.Semiring.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Descent.
From jwa Require Import Relation.Induced.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Transitive.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Modus.

(* A module may carry the type's name; its members read [NatWithZero.add].
 * The type and its ctors are declared inside it: [Integer] declares [Zero]
 * and [Positive] too, and across files a duplicate ctor name rebinds the
 * bare one silently and with no warning.
 *)
Module NatWithZero. (* NatWithZero *)

(* [Positive] wraps a [Nat], so an operation here reduces to the [Nat] one
 * plus the [Zero] cases.
 *)
Inductive T : Type :=
  | Zero     : T
  | Positive : Nat -> T.

(* The carrier is named [T] so that the type itself reads [NatWithZero] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End NatWithZero].
 *)
Abbreviation NatWithZero := T.

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
  | 0   => + Nat.One
  | + p => + (Nat.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_nat_with_zero_scope.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition power := fun (m : NatWithZero) (n : NatWithZero) .
  match n with
  | 0   => + Nat.One
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

Notation "'(<)'" := LessThan (only parsing)
  : jwa_nat_with_zero_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_nat_with_zero_scope.

(* [NatWithZero -> NatWithZero -> Comparison] *)
Definition compare := fun (m : NatWithZero) (n : NatWithZero) .
  match m with
  | 0 =>
      match n with
      | 0   => Comparison.Eq
      | + _ => Comparison.Lt
      end
  | + p =>
      match n with
      | 0   => Comparison.Gt
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
Local Open Scope jwa_product_scope.

Module div. (* div *)

(* [Nat -> Nat -> Product NatWithZero NatWithZero] *)
(* div.nat *)
Fixpoint nat (dividend : Nat) (divisor : Nat) : Product NatWithZero NatWithZero :=
  match dividend with
  | Nat.One =>
      match divisor with
      | Nat.One         => ((+ Nat.One), 0)
      | Nat.Successor _ => (0, (+ Nat.One))
      end
  | Nat.Successor dividend' =>
      match nat dividend' divisor with
      | (quotient, remainder) =>
          match eq (++ remainder) (+ divisor) with
          | true  => ((++ quotient), 0)
          | false => (quotient, (++ remainder))
          end
      end
  end.

End div. (* div *)

(* Zero is the one dividend [div.nat] cannot take, and it is handled here so
 * that [divide] and [modulo] are projections and nothing else.
 *)
(* [NatWithZero -> Nat -> Product NatWithZero NatWithZero] *)
Definition div := fun (n : NatWithZero) (divisor : Nat) .
  match n with
  | 0          => (0, 0)
  | + dividend => div.nat dividend divisor
  end.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition divide := fun (n : NatWithZero) (divisor : Nat) . pi_1 (div n divisor).

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition modulo := fun (n : NatWithZero) (divisor : Nat) . pi_2 (div n divisor).

(* The levels are reserved in [Core.Notations]; only the meanings belong here.
 * Both are always written in parentheses, so the dot that ends the token is
 * never next to the one that ends a command or separates a binder.
 *)
Notation "m /. n" := (divide m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m %. n" := (modulo m n) (only parsing)
  : jwa_nat_with_zero_scope.

Local Close Scope jwa_product_scope.

(* [d] divides [n] when some multiple of [d] is [n]. It is a partial order:
 * reflexive with [Positive Nat.One], transitive by multiplying the witnesses,
 * antisymmetric since [Nat.One] is the only unit.
 *)
(* [NatWithZero -> NatWithZero -> Prop] *)
Definition Divides := fun (d : NatWithZero) (n : NatWithZero) .
  exists (k : NatWithZero) . d * k = n.

(* [NatWithZero -> Prop] *)
Definition Even := fun (n : NatWithZero) . Divides (+ (Nat.Successor Nat.One)) n.

(* [NatWithZero -> Prop] *)
Definition Odd := fun (n : NatWithZero) .
  exists (k : NatWithZero) . (+ Nat.One) + ((+ (Nat.Successor Nat.One)) * k) = n.

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
Lemma specification : forall (n : NatWithZero) . (++ n) = (+ Nat.One) + n.
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
      modus ponens h, e' as f.
      ex f quodlibet.
    + simpl in |- *.
      intro e.
      pose proof (positive.injectivity e) as e'.
      rewrite (Nat.addition.commutativity n' m') in e'.
      pose proof (Nat.addition.identity.absence m' n') as h.
      unfold Negation in h.
      modus ponens h, e' as f.
      ex f quodlibet.
    + simpl in |- *.
      intro e.
      pose proof (positive.injectivity e) as e'.
      pose proof (Nat.addition.left.cancellation e') as e''.
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
Lemma identity : forall (n : NatWithZero) . (+ Nat.One) * n = n.
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
Lemma identity : forall (m : NatWithZero) . m * (+ Nat.One) = m.
Proof.
  intros m.
  destruct m as [| m'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication.commutativity m' Nat.One) in |- *.
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

Module order. (* multiplication.right.order *)

(* multiplication.right.order.extensivity *)
Theorem extensivity
  : forall (k : Nat) (n : NatWithZero) . n <= (+ k) * n.
Proof.
  intros k n.
  unfold LessOrEqual in |- *.
  destruct n as [| p].
  - simpl in |- *.
    exact (Disjunction.L (Identity.reflexivity 0)).
  - destruct k as [| k'].
    + simpl in |- *.
      exact (Disjunction.L (Identity.reflexivity (+ p))).
    + apply Disjunction.R.
      unfold LessThan in |- *.
      apply (Exists_introduction (Nat.mul k' p)).
      simpl in |- *.
      reflexivity.
Qed.

End order. (* multiplication.right.order *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (n : NatWithZero) . ((+ Nat.One) * n = n) /\ (n * (+ Nat.One) = n).
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
Lemma absence : forall (m : NatWithZero) . power m 0 = + Nat.One.
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
      rewrite (Nat.multiplication.commutativity (Nat.power m' a') Nat.One) in |- *.
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
    modus ponens i, e' as f.
    ex f quodlibet.
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

Module zero. (* order.strict.zero *)

(* order.strict.zero.accessibility *)
Lemma accessibility : Accessible LessThan 0.
Proof.
  apply Accessible_introduction.
  intros y h.
  destruct h as [k e].
  destruct y as [| q].
  - simpl in e.
    discriminate e.
  - simpl in e.
    discriminate e.
Qed.

End zero. (* order.strict.zero *)

(* Descending from [n] cannot go on for ever: [0] has nothing below it, and
 * a step down from a positive number lands on a smaller [Nat].
 *)
(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (n : NatWithZero) . Accessible LessThan n.
Proof.
  intros n.
  destruct n as [| p].
  - exact zero.accessibility.
  - induction p as [| p' IH] using Nat.induction.
    + apply Accessible_introduction.
      intros y h.
      destruct h as [k e].
      destruct y as [| q].
      * exact zero.accessibility.
      * simpl in e.
        pose proof (positive.injectivity e) as e'.
        destruct q as [| q'].
        -- simpl in e'.
           discriminate e'.
        -- simpl in e'.
           discriminate e'.
    + apply Accessible_introduction.
      intros y h.
      destruct h as [k e].
      destruct y as [| q].
      * exact zero.accessibility.
      * simpl in e.
        pose proof (positive.injectivity e) as e'.
        rewrite (Nat.addition.commutativity q k) in e'.
        destruct k as [| k'].
        -- simpl in e'.
           pose proof (Nat.successor.injectivity e') as e''.
           rewrite e'' in |- *.
           exact IH.
        -- simpl in e'.
           pose proof (Nat.successor.injectivity e') as e''.
           apply (Accessible.descend IH).
           apply (Exists_introduction k').
           simpl in |- *.
           rewrite (Nat.addition.commutativity q k') in |- *.
           rewrite e'' in |- *.
           reflexivity.
Qed.

End strict. (* order.strict *)

(* Discreteness: nothing sits strictly between [n] and [n + Nat.One], so [<] and
 * [<=] determine each other by a step of one.
 *)
(* order.discreteness *)
Theorem discreteness
  : forall (m : NatWithZero) (n : NatWithZero) .
      m < n + (+ Nat.One) <-> m <= n.
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
      change (+ (Nat.Successor k'))
        with ((+ Nat.One) + (+ k'))
        in e.
      rewrite -> (addition.commutativity (+ Nat.One) (+ k'))
              in e.
      rewrite <- (addition.associativity m (+ k') (+ Nat.One))
              in e.
      exact (addition.right.cancellation e).
  - intro h.
    unfold LessOrEqual in h.
    unfold LessThan    in |- *.
    destruct h as [e | lt].
    + apply (Exists_introduction Nat.One).
      rewrite e in |- *.
      reflexivity.
    + unfold LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction (Nat.Successor k)).
      change (+ (Nat.Successor k))
        with ((+ Nat.One) + (+ k))
        in |- *.
      rewrite -> (addition.commutativity (+ Nat.One) (+ k))
              in |- *.
      rewrite <- (addition.associativity m (+ k) (+ Nat.One))
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
  : forall (m : NatWithZero) (n : NatWithZero) . compare m n = Comparison.Lt <-> m < n.
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
      modus ponens i, h as f.
      ex f quodlibet.
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
      exact (modus aequans (positive.order.embedding m' n'),
                           (Nat.comparison.strict.forward.specification e)).
    * intro h.
      simpl in |- *.
      modus aequans (positive.order.embedding m' n'), h as lt.
      exact (Nat.comparison.strict.backward.specification lt).
Qed.

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Lemma specification
  : forall (m : NatWithZero) (n : NatWithZero) . compare m n = Comparison.Eq <-> m = n.
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
      rewrite (Nat.comparison.equality.forward.specification e) in |- *.
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
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
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
  - modus aequans (Comparable.minimum.specification m n), h as e1.
    rewrite e1 in |- *.
    modus aequans (Comparable.minimum.specification (k + m) (k + n)),
                  (addition.order.monotonicity k m n h) as e2.
    rewrite e2 in |- *.
    reflexivity.
  - rewrite (Comparable.minimum.commutativity m n)             in |- *.
    rewrite (Comparable.minimum.commutativity (k + m) (k + n)) in |- *.
    modus aequans (Comparable.minimum.specification n m), h as e1.
    rewrite e1 in |- *.
    modus aequans (Comparable.minimum.specification (k + n) (k + m)),
                  (addition.order.monotonicity k n m h) as e2.
    rewrite e2 in |- *.
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
    rewrite (Nat.subtraction.truncation (Comparable.order.reflexivity n')) in |- *.
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
      rewrite (Nat.subtraction.truncation (Comparable.order.reflexivity n')) in |- *.
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
      rewrite (Nat.subtraction.truncation
                (Comparable.order.reflexivity k')) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.subtraction.truncation
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
  - modus aequans (Comparable.order.reflection n m), c as order.
    unfold Comparable.LessOrEqual in order.
    destruct order as [e | lt].
    + rewrite e in h.
      pose proof (order.strict.irreflexivity m) as i.
      unfold Negation in i.
      modus ponens i, h as f.
      ex f quodlibet.
    + pose proof (Comparable.order.strict.asymmetry m n h) as a.
      unfold Negation in a.
      modus ponens a, lt as f.
      ex f quodlibet.
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
  modus aequans (Comparable.order.reflection n (m + n)),
                (addition.right.order.extensivity m n) as e.
  rewrite e in |- *.
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
      modus aequans (Comparable.order.reflection n m), c as order.
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

Module nat. (* division.nat *)

(* division.nat.specification *)
Lemma specification
  : forall (p : Nat) (d : Nat) .
      ((((+ p) /. d) * (+ d)) + ((+ p) %. d) = + p)
      /\ ((+ p) %. d) < + d.
Proof.
  intros p d.
  simpl divide, modulo, div in |- *.
  induction p as [| p' IH] using Nat.induction.
  - destruct d as [| d']; split; simpl in |- *.
    * reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction Nat.One).
      simpl in |- *.
      reflexivity.
    * reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction d').
      simpl in |- *.
      reflexivity.
  - destruct IH as [e lt].
    simpl in |- *.
    destruct (div.nat p' d) as [q r] eqn:D.
    simpl in e.
    simpl in lt.
    destruct (eq (++ r) (+ d)) as [|] eqn:E; split; simpl in |- *.
    * modus aequans (Comparable.comparison.equality.reflection (++ r) (+ d)), E as full.
      rewrite (increment.specification r) in full.
      rewrite (increment.specification q) in |- *.
      rewrite (multiplication.right.distributivity.over.addition (+ d) (+ Nat.One) q)
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
      rewrite (addition.left.commutativity (q * ((+ Nat.One) + r)) (+ Nat.One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
    * rewrite (increment.specification r) in |- *.
      rewrite (addition.left.commutativity (q * (+ d)) (+ Nat.One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in lt.
      destruct lt as [k ek].
      rewrite (increment.specification r) in E.
      rewrite (addition.commutativity (+ Nat.One) r) in E.
      rewrite (increment.specification r) in |- *.
      rewrite (addition.commutativity (+ Nat.One) r) in |- *.
      destruct k as [| k'].
      { modus aequans (Comparable.comparison.equality.reflection (r + (+ Nat.One)) (+ d)), ek as full.
        rewrite full in E.
        discriminate E. }
      { unfold LessThan in |- *.
        apply (Exists_introduction k').
        rewrite (addition.associativity r (+ Nat.One) (+ k')) in |- *.
        simpl in |- *.
        exact ek. }
Qed.

Module dividend. (* division.nat.dividend *)

(* division.nat.dividend.reconstruction *)
Theorem reconstruction
  : forall (p : Nat) (d : Nat) . (((+ p) /. d) * (+ d)) + ((+ p) %. d) = + p.
Proof.
  intros p d.
  destruct (division.nat.specification p d) as [h1 h2].
  exact h1.
Qed.

End dividend. (* division.nat.dividend *)

Module remainder. (* division.nat.remainder *)

(* division.nat.remainder.boundedness *)
Theorem boundedness
  : forall (p : Nat) (d : Nat) . ((+ p) %. d) < + d.
Proof.
  intros p d.
  destruct (division.nat.specification p d) as [h1 h2].
  exact h2.
Qed.

End remainder. (* division.nat.remainder *)

Module quotient. (* division.nat.quotient *)

(* division.nat.quotient.positivity *)
Theorem positivity
  : forall (d : Nat) (g : Nat) . Divides (+ g) (+ d) -> ~ ((+ d) /. g = 0).
Proof.
  intros d g h.
  simpl Negation in |- *.
  intro e.
  pose proof (division.nat.dividend.reconstruction d g) as reconstruction.
  rewrite e in reconstruction.
  destruct (multiplication.annihilation (+ g)) as [annihilation _].
  rewrite annihilation in reconstruction.
  destruct (addition.identity ((+ d) %. g)) as [identity _].
  rewrite identity in reconstruction.
  pose proof (division.nat.remainder.boundedness d g) as bound.
  rewrite reconstruction in bound.
  destruct h as [k hk].
  destruct k as [| k'].
  - destruct (multiplication.annihilation (+ g)) as [_ annihilation'].
    rewrite annihilation' in hk.
    discriminate hk.
  - destruct k' as [| k''].
    + rewrite (multiplication.right.identity (+ g)) in hk.
      rewrite hk in bound.
      pose proof (order.strict.irreflexivity (+ d)) as irreflexivity.
      simpl Negation in irreflexivity.
      modus ponens irreflexivity, bound as f.
      ex f quodlibet.
    + change (+ (Nat.Successor k'')) with ((+ Nat.One) + (+ k'')) in hk.
      rewrite (multiplication.left.distributivity.over.addition (+ g) (+ Nat.One) (+ k'')) in hk.
      rewrite (multiplication.right.identity (+ g)) in hk.
      rewrite (addition.commutativity (+ g) ((+ g) * (+ k''))) in hk.
      pose proof (addition.right.order.extensivity ((+ g) * (+ k'')) (+ g)) as extensivity.
      rewrite hk in extensivity.
      simpl LessOrEqual in extensivity.
      destruct extensivity as [equal | less].
      * rewrite equal in bound.
        pose proof (order.strict.irreflexivity (+ d)) as irreflexivity.
        simpl Negation in irreflexivity.
        modus ponens irreflexivity, bound as f.
        ex f quodlibet.
      * pose proof (order.strict.transitivity bound less) as circular.
        pose proof (order.strict.irreflexivity (+ d)) as irreflexivity.
        simpl Negation in irreflexivity.
        modus ponens irreflexivity, circular as f.
        ex f quodlibet.
Qed.

End quotient. (* division.nat.quotient *)

End nat. (* division.nat *)

Local Close Scope jwa_product_scope.

Module dividend. (* division.dividend *)

(* division.dividend.reconstruction *)
Theorem reconstruction
  : forall (n : NatWithZero) (d : Nat) . ((n /. d) * (+ d)) + (n %. d) = n.
Proof.
  intros n d.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - exact (division.nat.dividend.reconstruction p d).
Qed.

End dividend. (* division.dividend *)

Module remainder. (* division.remainder *)

(* division.remainder.boundedness *)
Theorem boundedness : forall (n : NatWithZero) (d : Nat) . (n %. d) < + d.
Proof.
  intros n d.
  destruct n as [| p].
  - simpl LessThan in |- *.
    apply (Exists_introduction d).
    simpl in |- *.
    reflexivity.
  - exact (division.nat.remainder.boundedness p d).
Qed.

End remainder. (* division.remainder *)

(* division.specification *)
Theorem specification
  : forall (n : NatWithZero) (d : Nat) .
      (((n /. d) * (+ d)) + (n %. d) = n)
      /\ (n %. d) < + d.
Proof.
  intros n d.
  split.
  - exact (division.dividend.reconstruction n d).
  - exact (division.remainder.boundedness n d).
Qed.

(* division.uniqueness *)
Theorem uniqueness
  : forall (n : NatWithZero) (d : Nat) (m : NatWithZero) (r : NatWithZero) .
      ((m * (+ d)) + r = n /\ r < (+ d)) -> ((n /. d) = m) /\ ((n %. d) = r).
Proof.
  intros n d m r h.
  destruct h as [e b].
  pose proof (division.dividend.reconstruction n d) as recon.
  pose proof (division.remainder.boundedness n d) as bound.
  assert (quotient : (n /. d) = m).
  { pose proof (Comparable.order.strict.trichotomy (n /. d) m) as t.
    destruct t as [below | [equal | above]].
    - simpl LessThan in below.
      destruct below as [k hk].
      symmetry in hk.
      rewrite hk in e.
      rewrite (multiplication.right.distributivity.over.addition
                 (+ d) (n /. d) (+ k)) in e.
      rewrite (addition.associativity
                 ((n /. d) * (+ d)) ((+ k) * (+ d)) r) in e.
      symmetry in recon.
      pose proof (Identity.transitivity e recon) as chain.
      pose proof (addition.left.cancellation chain) as excess.
      symmetry in excess.
      rewrite excess in bound.
      rewrite (addition.commutativity ((+ k) * (+ d)) r) in bound.
      pose proof (multiplication.right.order.extensivity k (+ d)) as reach.
      pose proof (addition.right.order.extensivity r ((+ k) * (+ d))) as grow.
      pose proof (Comparable.order.transitivity
                    (+ d) ((+ k) * (+ d)) (r + ((+ k) * (+ d)))
                    reach grow) as span.
      pose proof (order.strict.irreflexivity (+ d)) as i.
      unfold Negation    in i.
      unfold LessOrEqual in span.
      destruct span as [s1 | s2].
      + symmetry in s1.
        rewrite s1 in bound.
        modus ponens i, bound as f.
        ex f quodlibet.
      + pose proof (order.strict.transitivity s2 bound) as loop.
        modus ponens i, loop as f.
        ex f quodlibet.
    - exact equal.
    - simpl LessThan in above.
      destruct above as [k hk].
      symmetry in hk.
      rewrite hk in recon.
      rewrite (multiplication.right.distributivity.over.addition
                 (+ d) m (+ k)) in recon.
      rewrite (addition.associativity
                 (m * (+ d)) ((+ k) * (+ d)) (n %. d)) in recon.
      symmetry in e.
      pose proof (Identity.transitivity recon e) as chain.
      pose proof (addition.left.cancellation chain) as excess.
      symmetry in excess.
      rewrite excess in b.
      rewrite (addition.commutativity ((+ k) * (+ d)) (n %. d)) in b.
      pose proof (multiplication.right.order.extensivity k (+ d)) as reach.
      pose proof (addition.right.order.extensivity
                    (n %. d) ((+ k) * (+ d))) as grow.
      pose proof (Comparable.order.transitivity
                    (+ d) ((+ k) * (+ d)) ((n %. d) + ((+ k) * (+ d)))
                    reach grow) as span.
      pose proof (order.strict.irreflexivity (+ d)) as i.
      unfold Negation    in i.
      unfold LessOrEqual in span.
      destruct span as [s1 | s2].
      + symmetry in s1.
        rewrite s1 in b.
        modus ponens i, b as f.
        ex f quodlibet.
      + pose proof (order.strict.transitivity s2 b) as loop.
        modus ponens i, loop as f.
        ex f quodlibet.
  }
  split.
  - exact quotient.
  - rewrite quotient in recon.
    symmetry in e.
    pose proof (Identity.transitivity recon e) as chain.
    exact (addition.left.cancellation chain).
Qed.

(* division.invariance *)
Theorem invariance
  : forall (n : NatWithZero) (d : Nat) (k : Nat) .
      (((+ k) * n) /. (Nat.mul k d)) = n /. d.
Proof.
  intros n d k.

  pose proof (division.dividend.reconstruction n d) as recon.
  pose proof (division.remainder.boundedness n d) as bound.

  assert (witness
          : (((n /. d) * (+ (Nat.mul k d))) + ((+ k) * (n %. d)) = (+ k) * n)
          /\ ((+ k) * (n %. d)) < (+ (Nat.mul k d))).
  {
    split.
    - change (+ (Nat.mul k d)) with ((+ k) * (+ d)) in |- *.
      rewrite (multiplication.commutativity (n /. d) ((+ k) * (+ d))) in |- *.
      rewrite (multiplication.associativity (+ k) (+ d) (n /. d))     in |- *.
      rewrite (multiplication.commutativity (+ d) (n /. d))           in |- *.
      pose proof (Identity.symmetry
                    (multiplication.left.distributivity.over.addition
                       (+ k) ((n /. d) * (+ d)) (n %. d))) as dist.
      rewrite dist  in |- *.
      rewrite recon in |- *.
      reflexivity.
    - change (+ (Nat.mul k d)) with ((+ k) * (+ d)) in |- *.
      exact (multiplication.left.order.strict.monotonicity k (n %. d) (+ d) bound).
  }

  destruct (division.uniqueness ((+ k) * n) (Nat.mul k d)
              (n /. d) ((+ k) * (n %. d)) witness) as [h _].
  exact h.
Qed.

(* division.exactness *)
Theorem exactness
  : forall (n : NatWithZero) (d : Nat) .
      Divides (+ d) n -> (n /. d) * (+ d) = n.
Proof.
  intros n d h.
  simpl Divides in h.
  destruct h as [k hk].

  assert (witness : ((k * (+ d)) + 0 = n) /\ 0 < (+ d)).
  {
    split.
    - destruct (addition.identity (k * (+ d))) as [_ vanishing].
      rewrite vanishing in |- *.
      rewrite (multiplication.commutativity k (+ d)) in |- *.
      exact hk.
    - simpl LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
  }

  destruct (division.uniqueness n d k 0 witness) as [quotient _].
  rewrite quotient in |- *.
  rewrite (multiplication.commutativity k (+ d)) in |- *.
  exact hk.
Qed.

End division. (* division *)

Module divide. (* divide *)

Module nat. (* divide.nat *)

(* [forall (d : Nat) (g : Nat) . Divides (+ g) (+ d) -> Nat] *)
(* divide.nat.safe *)
Definition safe :=
  fun (d : Nat) (g : Nat) (h : Divides (+ g) (+ d)) .
    match (+ d) /. g as q
    with (* the Zero branch is never reachable *)
    | 0    => fun (n : ~ (0 = 0)) . match n (Identity.reflexivity 0) return Nat with end
    | + q' => fun (_ : ~ ((+ q') = 0)) . q'
    end (division.nat.quotient.positivity d g h).

Module safe. (* divide.nat.safe *)

(* divide.nat.safe.specification *)
Theorem specification
  : forall (d : Nat) (g : Nat) (h : Divides (+ g) (+ d)) .
      (+ (divide.nat.safe d g h)) = (+ d) /. g.
Proof.
  intros d g h.
  simpl divide.nat.safe in |- *.
  set (n := division.nat.quotient.positivity d g h).
  generalize dependent n.
  destruct ((+ d) /. g) as [| q'].
  - intro n.
    modus ponens n, (Identity.reflexivity 0) as f.
    ex f quodlibet.
  - intro n.
    simpl in |- *.
    reflexivity.
Qed.

(* divide.nat.safe.congruence *)
Theorem congruence
  : forall (d1 : Nat) (g1 : Nat) (h1 : Divides (+ g1) (+ d1))
      (d2 : Nat) (g2 : Nat) (h2 : Divides (+ g2) (+ d2)) .
      (+ d1) /. g1 = (+ d2) /. g2
      -> divide.nat.safe d1 g1 h1 = divide.nat.safe d2 g2 h2.
Proof.
  intros d1 g1 h1 d2 g2 h2 e.
  pose proof (divide.nat.safe.specification d1 g1 h1) as s1.
  pose proof (divide.nat.safe.specification d2 g2 h2) as s2.
  rewrite e in s1.
  symmetry in s2.
  pose proof (Identity.transitivity s1 s2) as full.
  exact (positive.injectivity full).
Qed.

End safe. (* divide.nat.safe *)

End nat. (* divide.nat *)

End divide. (* divide *)

Module modulo. (* modulo *)

(* modulo.homogeneity *)
Theorem homogeneity
  : forall (n : NatWithZero) (d : Nat) (k : Nat) .
      (((+ k) * n) %. (Nat.mul k d)) = (+ k) * (n %. d).
Proof.
  intros n d k.

  pose proof (division.dividend.reconstruction n d) as recon.
  pose proof (division.remainder.boundedness n d) as bound.

  assert (witness
          : (((n /. d) * (+ (Nat.mul k d))) + ((+ k) * (n %. d)) = (+ k) * n)
            /\ ((+ k) * (n %. d)) < (+ (Nat.mul k d))).
  {
    split.
    - change (+ (Nat.mul k d)) with ((+ k) * (+ d)) in |- *.
      rewrite (multiplication.commutativity (n /. d) ((+ k) * (+ d))) in |- *.
      rewrite (multiplication.associativity (+ k) (+ d) (n /. d))     in |- *.
      rewrite (multiplication.commutativity (+ d) (n /. d))           in |- *.
      pose proof (Identity.symmetry
                    (multiplication.left.distributivity.over.addition
                       (+ k) ((n /. d) * (+ d)) (n %. d))) as dist.
      rewrite dist  in |- *.
      rewrite recon in |- *.
      reflexivity.
    - change (+ (Nat.mul k d)) with ((+ k) * (+ d)) in |- *.
      exact (multiplication.left.order.strict.monotonicity k (n %. d) (+ d) bound).
  }

  destruct (division.uniqueness ((+ k) * n) (Nat.mul k d)
              (n /. d) ((+ k) * (n %. d)) witness) as [_ h].
  exact h.
Qed.

End modulo. (* modulo *)

Local Open Scope jwa_product_scope.

Module euclid. (* euclid *)

(* euclid.well_founded *)
Instance well_founded
  : WellFounded (Induced (<) pi_2) :=
  WellFounded.induced LessThan (@Product.second NatWithZero NatWithZero)
    {| accessibility := order.strict.wellfoundedness |}.

Local Open Scope jwa_type_scope.

(* [forall (x : NatWithZero * NatWithZero) .
 * (forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero) -> NatWithZero]
 *)
(* euclid.step *)
Definition step
  : Descent.Step (Induced (<) pi_2) (fun (_ : NatWithZero * NatWithZero) . NatWithZero)
  :=
  fun (x : NatWithZero * NatWithZero)
    (recurse : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero) .
    match x with
    (* [b = 0] answers [a].
     * [b = + b'] does not answer with the product [((+ b'), (a %. b'))],
     * it calls [recurse] there with it and answers with the number that comes back.
     * The product is where the next question is, not the answer.
     *)
    | (a, b) =>
        match b with
        | 0 =>
            fun (_ : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y (a, 0) -> NatWithZero) . a
        | + b' =>
            fun (recurse : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y (a, + b') -> NatWithZero) .
              (recurse
                ((+ b'), (a %. b'))
                (Induced.introduction (division.remainder.boundedness a b')))
        end
    end recurse.

Local Close Scope jwa_type_scope.

(* euclid.extensionality *)
Lemma extensionality : Descent.Extensional step.
Proof.
  (* [x : NatWithZero * NatWithZero]
   * [f : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero]
   * [g : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero]
   * [h : forall (y : NatWithZero * NatWithZero) (r : Induced (<) pi_2 y x) . f y r = g y r]
   * :
   * [|- step x f = step x g]
   *)
  intros x f g h.

  (* [|- step (a, b) f = step (a, b) g] *)
  destruct x as [a b].

  destruct b as [| b'].

  (* b destructed as 0 : [|- step (a, 0) f = step (a, 0) g] *)
  {
    (* [|- a = a] *)
    simpl in |- *.
    reflexivity.
  }

  (* b destructed as + b' : [|- step (a, + b') f = step (a, + b') g] *)
  {
    (* [|- f ((+ b'), (a %. b')) (Induced.introduction (division.remainder.boundedness a b'))
     *  = g ((+ b'), (a %. b')) (Induced.introduction (division.remainder.boundedness a b'))]
     *)
    simpl step in |- *.

    (* The context gains [bound := division.remainder.boundedness a b'],
     * of type [(a %. b') < + b']
     * :
     * [|- f ((+ b'), (a %. b')) (Induced.introduction bound)
     *  = g ((+ b'), (a %. b')) (Induced.introduction bound)]
     *)
    set (bound := division.remainder.boundedness a b'
                : (a %. b') < + b').

    (* The context gains [y := ((+ b'), (a %. b'))]
     * :
     * [|- f y (Induced.introduction bound)
     *  = g y (Induced.introduction bound)]
     *)
    set (y := ((+ b'), (a %. b'))
            : NatWithZero * NatWithZero).

    (* The context gains [x := (a, + b')], and [f], [g] and [h] fold to it:
     * [f : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero]
     * [g : forall (y : NatWithZero * NatWithZero) . Induced (<) pi_2 y x -> NatWithZero]
     * [h : forall (y : NatWithZero * NatWithZero) (r : Induced (<) pi_2 y x) . f y r = g y r]
     *)
    set (x := (a, + b')) in *.

    (* The context gains [r := Induced.introduction bound],
     * of type [Induced (<) pi_2 y x]
     * :
     * [|- f y r = g y r]
     *)
    set (r := Induced.introduction bound
            : Induced (<) pi_2 y x).

    (* [H : forall (r : Induced (<) pi_2 y x) . f y r = g y r] *)
    pose proof (h y) as H.

    exact (modus ponens H, r).
  }
Qed.

Module nat. (* euclid.nat *)

(* euclid.nat.well_founded *)
Instance well_founded
  : WellFounded (Induced Nat.LessThan (@Product.second NatWithZero Nat)) :=
  WellFounded.induced Nat.LessThan (@Product.second NatWithZero Nat)
    Nat_less_than_well_founded.

(* The inner [return] carries the bound rather than an equation, so the
 * branch for a positive remainder has [(+ r) < + q] already in hand.
 *)
(* [forall (p : Product NatWithZero Nat) .
 *    (forall (s : Product NatWithZero Nat) .
 *       Induced Nat.LessThan (@Product.second NatWithZero Nat) s p -> Nat) ->
 *    Nat]
 *)
(* euclid.nat.step *)
Definition step
  : Descent.Step (Induced Nat.LessThan (@Product.second NatWithZero Nat))
                 (fun (_ : Product NatWithZero Nat) . Nat)
  :=
  fun (p : Product NatWithZero Nat)
    (recurse : forall (s : Product NatWithZero Nat) .
                 Induced Nat.LessThan (@Product.second NatWithZero Nat) s p -> Nat) .
    match p as t
      return ((forall (s : Product NatWithZero Nat) .
                 Induced Nat.LessThan (@Product.second NatWithZero Nat) s t -> Nat) ->
              Nat)
    with
    | (a, q) =>
        fun (descend : forall (s : Product NatWithZero Nat) .
                         Induced Nat.LessThan (@Product.second NatWithZero Nat) s (a, q) ->
                         Nat) .
          match (a %. q) as m return (m < (+ q) -> Nat) with
          | 0 => fun (_ : 0 < (+ q)) . q
          | + r =>
              fun (h : (+ r) < (+ q)) .
                descend ((+ q), r)
                  (Induced.introduction
                     (f := @Product.second NatWithZero Nat) (y := ((+ q), r)) (x := (a, q))
                     (Biconditional.forward.elimination (positive.order.embedding r q) h))
          end (division.remainder.boundedness a q)
    end recurse.

(* euclid.nat.extensionality *)
Lemma extensionality : Descent.Extensional step.
Proof.
  intros p f g h.
  destruct p as [a q].
  simpl step in |- *.
  generalize (division.remainder.boundedness a q).
  destruct (a %. q) as [| r].
  - intros b.
    reflexivity.
  - intros b.
    set (s := Induced.introduction
                (f := @Product.second NatWithZero Nat) (y := ((+ q), r)) (x := (a, q))
                (Biconditional.forward.elimination (positive.order.embedding r q) b)
            : Induced Nat.LessThan (@Product.second NatWithZero Nat) ((+ q), r) (a, q)).
    pose proof (h ((+ q), r)) as H.
    exact (modus ponens H, s).
Qed.

End nat. (* euclid.nat *)

End euclid. (* euclid *)

(* An instance declared inside a submodule is dropped at its [End], so it is
 * announced again here, where [gcd] resolves it.
 *)
Existing Instance euclid.well_founded.

Existing Instance euclid.nat.well_founded.

(* Greatest Common Divisor *)
(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition gcd :=
  fun (a : NatWithZero) (b : NatWithZero) .
    (WellFounded.recursion euclid.step (a, b)).

Local Close Scope jwa_product_scope.

Module divisibility. (* divisibility *)

(* divisibility.reflexivity *)
Theorem reflexivity : forall (n : NatWithZero) . Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (+ Nat.One)).
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
        pose proof (Nat.multiplication.commutativity Nat.One p) as c.
        simpl in c.
        pose proof (Identity.transitivity e3 c)
                as e4.
        pose proof (Nat.multiplication.left.cancellation e4)
                as e5.
        pose proof (Nat.multiplication.identity.factorization e5)
                as f.
        destruct f as [ek ej].
        rewrite ek in e1.
        rewrite (multiplication.right.identity (+ p)) in e1.
        exact e1.
Qed.

(* divisibility.bottom *)
Theorem bottom : forall (n : NatWithZero) . Divides (+ Nat.One) n.
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

(* The quotients are what the subtraction happens on, so the witness is
 * [k2 - k1] and the work is showing that [k1] is not the larger.
 *)
(* divisibility.addition.cancellation *)
Theorem cancellation
  : forall {d : NatWithZero} {m : NatWithZero} {n : NatWithZero} .
      Divides d m -> Divides d (m + n) -> Divides d n.
Proof.
  intros d m n h1 h2.
  simpl Divides in h1, h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  destruct d as [| c].
  - destruct (multiplication.annihilation k1) as [z1 z2].
    rewrite z1 in e1.
    destruct (multiplication.annihilation k2) as [w1 w2].
    rewrite w1 in e2.
    rewrite <- e1 in e2.
    destruct (addition.identity n) as [i1 i2].
    rewrite i1 in e2.
    rewrite <- e2 in |- *.
    exact (divisibility.top 0).
  - destruct (Comparable.order.totality k1 k2) as [le | ge].
    + simpl Divides in |- *.
      apply (Exists_introduction (saturating_sub k2 k1)).
      pose proof (subtraction.saturating.specification le) as s.
      pose proof (multiplication.left.distributivity.over.addition
                    (+ c) k1 (saturating_sub k2 k1)) as dist.
      rewrite s in dist.
      rewrite e1 in dist.
      rewrite e2 in dist.
      symmetry in dist.
      exact (addition.left.cancellation dist).
    + simpl LessOrEqual in ge.
      destruct ge as [eq | lt].
      * rewrite eq in e2.
        rewrite e1 in e2.
        destruct (addition.identity m) as [i1 i2].
        pose proof (Identity.transitivity i2 e2) as e3.
        pose proof (addition.left.cancellation e3) as e4.
        rewrite <- e4 in |- *.
        exact (divisibility.top (+ c)).
      * pose proof (multiplication.left.order.strict.monotonicity c k2 k1 lt) as mono.
        rewrite e1 in mono.
        rewrite e2 in mono.
        simpl LessThan in mono.
        destruct mono as [j ej].
        rewrite (addition.associativity m n (+ j)) in ej.
        destruct (addition.identity m) as [i1 i2].
        symmetry in i2.
        pose proof (Identity.transitivity ej i2) as e3.
        pose proof (addition.left.cancellation e3) as e4.
        pose proof (addition.right.order.positivity n j) as pos.
        rewrite e4 in pos.
        exact (Falsum.elimination (Divides (+ c) n)
                                  (order.strict.irreflexivity 0 pos)).
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


Module gcd. (* gcd *)

Local Open Scope jwa_product_scope.

(* gcd.zero *)
Theorem zero : forall (a : NatWithZero) . gcd a 0 = a.
Proof.
  intros a.
  simpl gcd in |- *.
  rewrite (WellFounded.recursion.unfolding euclid.extensionality (a, 0)) in |- *.
  reflexivity.
Qed.

(* gcd.recurrence *)
Theorem recurrence
  : forall (a : NatWithZero) (q : Nat) . gcd a (+ q) = gcd (+ q) ((a %. q)).
Proof.
  intros a q.
  simpl gcd in |- *.
  rewrite (WellFounded.recursion.unfolding euclid.extensionality (a, + q)) in |- *.
  reflexivity.
Qed.

(* gcd.divisibility *)
Theorem divisibility
  : forall (b : NatWithZero) (a : NatWithZero) .
      Divides (gcd a b) a /\ Divides (gcd a b) b.
Proof.
  intros b.
  apply (Accessible.recursion
           (R := LessThan)
           (P := fun (c : NatWithZero) .
                 forall (a : NatWithZero) .
                   Divides (gcd a c) a /\ Divides (gcd a c) c)).
  - intros c recurse a.
    destruct c as [| q].
    + rewrite (gcd.zero a) in |- *.
      split.
      * exact (divisibility.reflexivity a).
      * exact (divisibility.top a).
    + rewrite (gcd.recurrence a q) in |- *.
      destruct (recurse ((a %. q)) (division.remainder.boundedness a q) (+ q)) as [d1 d2].
      split.
      * destruct (division.specification a q) as [s1 s2].
        pose proof (divisibility.multiplication.closure
                      (gcd (+ q) ((a %. q))) (+ q) ((a /. q)) d1) as hm.
        rewrite (multiplication.commutativity (+ q) ((a /. q))) in hm.
        pose proof (divisibility.addition.closure hm d2) as ha.
        rewrite s1 in ha.
        exact ha.
      * exact d1.
  - exact (order.strict.wellfoundedness b).
Qed.

Module left. (* gcd.left *)

(* gcd.left.divisibility *)
Theorem divisibility
  : forall (a : NatWithZero) (b : NatWithZero) . Divides (gcd a b) a.
Proof.
  intros a b.
  destruct (gcd.divisibility b a) as [h1 h2].
  exact h1.
Qed.

Module distributivity. (* gcd.left.distributivity *)

Module of. (* gcd.left.distributivity.of *)

(* gcd.left.distributivity.of.multiplication *)
Theorem multiplication
  : forall (k : Nat) (b : NatWithZero) (a : NatWithZero) .
      (+ k) * gcd a b = gcd ((+ k) * a) ((+ k) * b).
Proof.
  intros k b.
  apply (Accessible.recursion
           (R := LessThan)
           (P := fun (c : NatWithZero) .
                 forall (a : NatWithZero) .
                   (+ k) * gcd a c = gcd ((+ k) * a) ((+ k) * c))).
  - intros c recurse a.
    destruct c as [| q].
    + rewrite (gcd.zero a) in |- *.
      change ((+ k) * 0) with (0 : NatWithZero) in |- *.
      rewrite (gcd.zero ((+ k) * a)) in |- *.
      reflexivity.
    + rewrite (gcd.recurrence a q) in |- *.
      change ((+ k) * (+ q)) with (+ (Nat.mul k q)) in |- *.
      rewrite (gcd.recurrence ((+ k) * a) (Nat.mul k q)) in |- *.
      rewrite (modulo.homogeneity a q k) in |- *.
      change (+ (Nat.mul k q)) with ((+ k) * (+ q)) in |- *.
      exact (recurse ((a %. q)) (division.remainder.boundedness a q) (+ q)).
  - exact (order.strict.wellfoundedness b).
Qed.

End of. (* gcd.left.distributivity.of *)

End distributivity. (* gcd.left.distributivity *)

End left. (* gcd.left *)

Module right. (* gcd.right *)

(* gcd.right.divisibility *)
Theorem divisibility
  : forall (a : NatWithZero) (b : NatWithZero) . Divides (gcd a b) b.
Proof.
  intros a b.
  destruct (gcd.divisibility b a) as [h1 h2].
  exact h2.
Qed.

End right. (* gcd.right *)

(* gcd.universality *)
Theorem universality
  : forall (b : NatWithZero) (a : NatWithZero) (d : NatWithZero) .
      Divides d a -> Divides d b -> Divides d (gcd a b).
Proof.
  intros b.
  apply (Accessible.recursion
           (R := LessThan)
           (P := fun (c : NatWithZero) .
                 forall (a : NatWithZero) (d : NatWithZero) .
                   Divides d a -> Divides d c -> Divides d (gcd a c))).
  - intros c recurse a d h1 h2.
    destruct c as [| q].
    + rewrite (gcd.zero a) in |- *.
      exact h1.
    + rewrite (gcd.recurrence a q) in |- *.
      assert (remainder : Divides d (a %. q)).
      {
        destruct (division.specification a q) as [s1 s2].
        rewrite <- s1 in h1.
        pose proof (divisibility.multiplication.closure
                      d (+ q) ((a /. q)) h2) as hm.
        rewrite (multiplication.commutativity (+ q) ((a /. q))) in hm.
        exact (divisibility.addition.cancellation hm h1).
      }
      pose proof (recurse ((a %. q)) (division.remainder.boundedness a q) (+ q) d h2)
        as below.
      exact (modus ponens below, remainder).
  - exact (order.strict.wellfoundedness b).
Qed.

(* gcd.commutativity *)
Theorem commutativity
  : forall (a : NatWithZero) (b : NatWithZero) . gcd a b = gcd b a.
Proof.
  intros a b.
  apply divisibility.antisymmetry.
  - exact (gcd.universality
            a b (gcd a b)
            (gcd.right.divisibility a b)
            (gcd.left.divisibility  a b)).
  - exact (gcd.universality
            b a (gcd b a)
            (gcd.right.divisibility b a)
            (gcd.left.divisibility  b a)).
Qed.

Module multiplication. (* gcd.multiplication *)

(* gcd.multiplication.cancellation *)
Theorem cancellation
  : forall (p : NatWithZero) (q : NatWithZero) (r : NatWithZero) .
      Divides p (q * r) -> gcd p q = (+ Nat.One) -> Divides p r.
Proof.
  intros p q r h coprime.
  destruct r as [| s].
  - exact (divisibility.top p).
  - assert (scaled : gcd ((+ s) * p) ((+ s) * q) = (+ s)).
    {
      pose proof (gcd.left.distributivity.of.multiplication s q p) as dist.
      rewrite coprime in dist.
      rewrite (multiplication.right.identity (+ s)) in dist.
      symmetry in dist.
      exact dist.
    }
    pose proof (divisibility.multiplication.closure
                  p p (+ s)
                  (divisibility.reflexivity p))
            as hp.
    rewrite (multiplication.commutativity p (+ s)) in hp.
    rewrite (multiplication.commutativity q (+ s)) in h.
    pose proof (gcd.universality ((+ s) * q) ((+ s) * p) p hp h) as u.
    rewrite scaled in u.
    exact u.
Qed.

End multiplication. (* gcd.multiplication *)

(* [NatWithZero -> Nat -> Nat] *)
(* gcd.nat *)
Definition nat :=
  fun (a : NatWithZero) (q : Nat) .
    (WellFounded.recursion euclid.nat.step (a, q)).

Module nat. (* gcd.nat *)

(* gcd.nat.zero *)
Theorem zero
  : forall (a : NatWithZero) (q : Nat) . (a %. q) = 0 -> gcd.nat a q = q.
Proof.
  intros a q e.
  simpl gcd.nat in |- *.
  rewrite (WellFounded.recursion.unfolding
             euclid.nat.extensionality (a, q)) in |- *.
  simpl euclid.nat.step in |- *.
  generalize (division.remainder.boundedness a q).
  rewrite e in |- *.
  intros b.
  reflexivity.
Qed.

(* gcd.nat.recurrence *)
Theorem recurrence
  : forall (a : NatWithZero) (q : Nat) (r : Nat) .
      (a %. q) = + r -> gcd.nat a q = gcd.nat (+ q) r.
Proof.
  intros a q r e.
  simpl gcd.nat in |- *.
  rewrite (WellFounded.recursion.unfolding
             euclid.nat.extensionality (a, q)) in |- *.
  simpl euclid.nat.step in |- *.
  generalize (division.remainder.boundedness a q).
  rewrite e in |- *.
  intros b.
  reflexivity.
Qed.

(* gcd.nat.specification *)
Theorem specification
  : forall (q : Nat) (a : NatWithZero) . gcd a (+ q) = + (gcd.nat a q).
Proof.
  intros q.
  apply (Accessible.recursion
           (R := Nat.LessThan)
           (P := fun (c : Nat) .
                 forall (a : NatWithZero) . gcd a (+ c) = + (gcd.nat a c))).
  - intros c recurse a.
    rewrite (gcd.recurrence a c) in |- *.
    destruct (a %. c) as [| r] eqn:e.
    + rewrite (gcd.zero (+ c)) in |- *.
      rewrite (gcd.nat.zero a c e) in |- *.
      reflexivity.
    + rewrite (gcd.nat.recurrence a c r e) in |- *.
      pose proof (division.remainder.boundedness a c) as b.
      rewrite e in b.
      modus aequans (positive.order.embedding r c), b as lt.
      exact (recurse r lt (+ c)).
  - exact (accessibility q).
Qed.

Module left. (* gcd.nat.left *)

(* gcd.nat.left.divisibility *)
Theorem divisibility
  : forall (a : NatWithZero) (q : Nat) . Divides (+ (gcd.nat a q)) a.
Proof.
  intros a q.
  pose proof (gcd.left.divisibility a (+ q)) as h.
  rewrite (gcd.nat.specification q a) in h.
  exact h.
Qed.

Module distributivity. (* gcd.nat.left.distributivity *)

Module of. (* gcd.nat.left.distributivity.of *)

(* gcd.nat.left.distributivity.of.multiplication *)
Theorem multiplication
  : forall (k : Nat) (q : Nat) (a : NatWithZero) .
      Nat.mul k (gcd.nat a q) = gcd.nat ((+ k) * a) (Nat.mul k q).
Proof.
  intros k q a.
  pose proof (gcd.left.distributivity.of.multiplication k (+ q) a) as h.
  rewrite (gcd.nat.specification q a) in h.
  change ((+ k) * (+ q)) with (+ (Nat.mul k q)) in h.
  rewrite (gcd.nat.specification (Nat.mul k q) ((+ k) * a)) in h.
  change ((+ k) * (+ (gcd.nat a q)))
    with (+ (Nat.mul k (gcd.nat a q))) in h.
  exact (positive.injectivity h).
Qed.

End of. (* gcd.nat.left.distributivity.of *)

End distributivity. (* gcd.nat.left.distributivity *)

End left. (* gcd.nat.left *)

Module right. (* gcd.nat.right *)

(* gcd.nat.right.divisibility *)
Theorem divisibility
  : forall (a : NatWithZero) (q : Nat) . Divides (+ (gcd.nat a q)) (+ q).
Proof.
  intros a q.
  pose proof (gcd.right.divisibility a (+ q)) as h.
  rewrite (gcd.nat.specification q a) in h.
  exact h.
Qed.

End right. (* gcd.nat.right *)

(* gcd.nat.divisibility *)
Theorem divisibility
  : forall (a : NatWithZero) (q : Nat) .
      Divides (+ (gcd.nat a q)) a /\ Divides (+ (gcd.nat a q)) (+ q).
Proof.
  intros a q.
  split.
  - exact (gcd.nat.left.divisibility  a q).
  - exact (gcd.nat.right.divisibility a q).
Qed.

(* gcd.nat.exhaustiveness *)
Theorem exhaustiveness
  : forall (a : NatWithZero) (q : Nat) .
      gcd.nat
        (a /. (gcd.nat a q))
        (divide.nat.safe
          q (gcd.nat a q)
          (gcd.nat.right.divisibility a q))
      = Nat.One.
Proof.
  intros a q.
  assert (top : (+ (gcd.nat a q)) * (a /. (gcd.nat a q)) = a).
  {
    pose proof (division.exactness a (gcd.nat a q)
                  (gcd.nat.left.divisibility a q)) as e.
    rewrite (multiplication.commutativity
               (+ (gcd.nat a q)) (a /. (gcd.nat a q))) in |- *.
    exact e.
  }
  assert (bottom
          : Nat.mul
              (gcd.nat a q)
              (divide.nat.safe q (gcd.nat a q) (gcd.nat.right.divisibility a q))
          = q).
  {
    pose proof (divide.nat.safe.specification
                  q (gcd.nat a q)
                  (gcd.nat.right.divisibility a q)) as s.
    pose proof (division.exactness
                  (+ q) (gcd.nat a q)
                  (gcd.nat.right.divisibility a q)) as e.
    symmetry in s.
    rewrite s in e.
    pose proof (positive.injectivity e) as e'.
    rewrite (Nat.multiplication.commutativity
               (gcd.nat a q)
               (divide.nat.safe q (gcd.nat a q)
                  (gcd.nat.right.divisibility a q))) in |- *.
    exact e'.
  }
  pose proof (gcd.nat.left.distributivity.of.multiplication
                (gcd.nat a q)
                (divide.nat.safe
                  q (gcd.nat a q)
                  (gcd.nat.right.divisibility a q))
                (a /. (gcd.nat a q))) as dist.
  rewrite top    in dist.
  rewrite bottom in dist.
  destruct (Nat.multiplication.identity (gcd.nat a q)) as [_ unit].
  symmetry in unit.
  pose proof (Identity.transitivity dist unit) as chain.
  destruct (Nat.multiplication.cancellation
              (gcd.nat a q)
              (gcd.nat
                (a /. (gcd.nat a q))
                (divide.nat.safe
                  q (gcd.nat a q)
                  (gcd.nat.right.divisibility a q)))
              Nat.One) as [cancel _].
  exact (cancel chain).
Qed.

End nat. (* gcd.nat *)

Local Close Scope jwa_product_scope.

End gcd. (* gcd *)


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
  - induction p as [| p' IH] using Nat.induction.
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
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in odd.
        destruct odd as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction ((+ Nat.One) + k)).
        rewrite (multiplication.left.distributivity.over.addition
                   (+ (Nat.Successor Nat.One)) (+ Nat.One) k) in |- *.
        change ((+ (Nat.Successor Nat.One)) * (+ Nat.One))
          with ((+ Nat.One) + (+ Nat.One)) in |- *.
        rewrite (addition.associativity
                   (+ Nat.One) (+ Nat.One) ((+ (Nat.Successor Nat.One)) * k)) in |- *.
        rewrite e in |- *.
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
  apply (Exists_introduction ((+ Nat.One) + (k1 + k2))).
  symmetry in e1, e2.
  rewrite e1, e2 in |- *.
  rewrite (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) (+ Nat.One) (k1 + k2)) in |- *.
  rewrite (multiplication.left.distributivity.over.addition
            (+ (Nat.Successor Nat.One)) k1 k2) in |- *.
  change ((+ (Nat.Successor Nat.One)) * (+ Nat.One))
    with ((+ Nat.One) + (+ Nat.One))
      in |- *.
  rewrite (addition.interchange
            (+ Nat.One) ((+ (Nat.Successor Nat.One)) * k1)
            (+ Nat.One) ((+ (Nat.Successor Nat.One)) * k2)) in |- *.
  reflexivity.
Qed.

End addition. (* parity.odd.addition *)

End odd. (* parity.odd *)

End parity. (* parity *)

End NatWithZero. (* NatWithZero *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [NatWithZero], not [NatWithZero.T]. [Zero] and [Positive] name ctors of
 * [Integer] as well, so both types write theirs with the prefix.
 *)
Abbreviation NatWithZero := NatWithZero.T.

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

Instance NatWithZero_less_than_well_founded
  : WellFounded NatWithZero.LessThan :=
  {| accessibility := NatWithZero.order.strict.wellfoundedness |}.

Instance NatWithZero_add_monoid
  : Monoid NatWithZero.add NatWithZero.Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := NatWithZero.addition.associativity |}
  ; Monoid.identity := NatWithZero.addition.identity
  |}.

Instance NatWithZero_add_cancellative
  : Cancellative NatWithZero.add := {|
    Cancellative.cancellation := NatWithZero.addition.cancellation
  |}.

Instance NatWithZero_mul_monoid
  : Monoid NatWithZero.mul (NatWithZero.Positive Nat.One) := {|
    Monoid.semigroup := {|
      Semigroup.associativity := NatWithZero.multiplication.associativity |}
  ; Monoid.identity := NatWithZero.multiplication.identity |}.

Instance NatWithZero_add_commutative
  : Commutative NatWithZero.add := {|
      Commutative.commutativity := NatWithZero.addition.commutativity
  |}.

Instance NatWithZero_add_abelian_monoid
  : AbelianMonoid NatWithZero.add NatWithZero.Zero :=
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
  : Monoid NatWithZero.max NatWithZero.Zero :=
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
  : Semiring NatWithZero.add NatWithZero.Zero NatWithZero.mul
      (NatWithZero.Positive Nat.One) :=
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
