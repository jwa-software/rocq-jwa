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
From jwa Require Import Data.Number.Numeral.
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
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [Nat0.add].
 * The type and its ctors are declared inside it: [Integer] declares [Zero]
 * and [Positive] too, and across files a duplicate ctor name rebinds the
 * bare one silently and with no warning.
 *)
Module Nat0. (* Nat0 *)

(* [Positive] wraps a [Nat], so an operation here reduces to the [Nat] one
 * plus the [Zero] cases.
 *)
Inductive T : Type :=
  | Zero     : T
  | Positive : Nat -> T.

(* The carrier is named [T] so that the type itself reads [Nat0] on
 * both sides of the module: here through this abbreviation, outside through
 * the one that follows [End Nat0].
 *)
Abbreviation Nat0 := T.

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] is a prefix, apart from the infix [+].
 *)
Local Notation "0" := Zero (only parsing).
Local Notation "+ p" := (Positive p)
  (at level 35, right associativity, only parsing).

(* [Nat0 -> Nat0 -> Nat0] *)
Definition add := fun (m : Nat0) (n : Nat0) .
  match m with
  | 0   => n
  | + p =>
      match n with
      | 0   => + p
      | + q => + (p + q)%n
      end
  end.

(* [Nat0 -> Nat0 -> Nat0] *)
Definition mul := fun (m : Nat0) (n : Nat0) .
  match m with
  | 0   => 0
  | + p =>
      match n with
      | 0   => 0
      | + q => + (p * q)%n
      end
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Nat0] a client writes [(m + n)%n0].
 * [only parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_nat0_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_nat0_scope.

Local Open Scope jwa_nat0_scope.

(* [Nat0 -> Nat0] *)
Definition inc := fun (n : Nat0) .
  match n with
  | 0   => + Nat.One
  | + p => + (Nat.inc p)
  end.

Notation "++ n" := (inc n) (only parsing)
  : jwa_nat0_scope.

(* [Nat0 -> Nat0 -> Nat0] *)
Definition power := fun (m : Nat0) (n : Nat0) .
  match n with
  | 0   => + Nat.One
  | + q =>
      match m with
      | 0   => 0
      | + p => + (p ^ q)%n
      end
  end.

Notation "m ^ n" := (power m n) (only parsing)
  : jwa_nat0_scope.

(* [Nat0 -> Nat0 -> Prop] *)
Definition LessThan := fun (m : Nat0) (n : Nat0) .
  forsome (k : Nat) . m + (+ k) = n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_nat0_scope.

(* [Nat0 -> Nat0 -> Prop] *)
Definition LessOrEqual := fun (m : Nat0) (n : Nat0) .
  m = n \/ m < n.

Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_nat0_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_nat0_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_nat0_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_nat0_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_nat0_scope.

(* [Nat0 -> Nat0 -> Comparison] *)
Definition compare := fun (m : Nat0) (n : Nat0) .
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

(* [Nat0 -> Nat0 -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Nat0 -> Nat0 -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [Nat0 -> Nat0 -> Nat0] *)
Abbreviation min := (Comparable.min compare).

(* [Nat0 -> Nat0 -> Nat0] *)
Abbreviation max := (Comparable.max compare).

(* [Nat0 -> Nat0 -> Nat0] *)
Definition saturating_sub := fun (m : Nat0) (n : Nat0) .
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

(* [Nat0 -> Nat0 -> Option Nat0] *)
Definition sub := fun (m : Nat0) (n : Nat0) .
  match le n m with
  | true  => Some (saturating_sub m n)
  | false => None
  end.

(* The conversion down to [Nat], which has no zero: [None] at [0]. *)
(* [Nat0 -> Option Nat] *)
Definition to_nat := fun (n : Nat0) .
  match n with
  | 0   => None
  | + p => Some p
  end.

(* The number a literal spells, in decimal or hexadecimal: what [Nat] reads,
 * and [0] where it reads none.
 *)
(* [Numeral.Unsigned -> Nat0] *)
Definition from_numeral := fun (u : Numeral.Unsigned) .
  match Nat.from_numeral u with
  | Some p => + p
  | None   => 0
  end.

(* [n] as a literal, in decimal. *)
(* [Nat0 -> Numeral.Unsigned] *)
Definition to_numeral := fun (n : Nat0) .
  match n with
  | 0   => Numeral.Unsigned.Decimal (Numeral.Decimal.Digits.Zero Numeral.Decimal.Digits.End)
  | + p => Nat.to_numeral p
  end.

(* Euclidean division of a positive by a positive, by walking the dividend
 * down: each step adds one to the remainder, and the quotient goes up when
 * the remainder reaches the divisor. The divisor is a [Nat], so it is never
 * zero. The result is the pair of quotient and remainder.
 *)
Local Open Scope jwa_product_scope.

Module div. (* div *)

(* [Nat -> Nat -> Product Nat0 Nat0] *)
(* div.nat *)
Fixpoint nat (dividend : Nat) (divisor : Nat) : Product Nat0 Nat0 :=
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
(* [Nat0 -> Nat -> Product Nat0 Nat0] *)
Definition div := fun (n : Nat0) (divisor : Nat) .
  match n with
  | 0          => (0, 0)
  | + dividend => div.nat dividend divisor
  end.

(* [Nat0 -> Nat -> Nat0] *)
Definition divide := fun (n : Nat0) (divisor : Nat) . pi_1 (div n divisor).

(* [Nat0 -> Nat -> Nat0] *)
Definition modulo := fun (n : Nat0) (divisor : Nat) . pi_2 (div n divisor).

(* The levels are reserved in [Core.Notations]; only the meanings belong here.
 * Both are always written in parentheses, so the dot that ends the token is
 * never next to the one that ends a command or separates a binder.
 *)
Notation "m /. n" := (divide m n) (only parsing)
  : jwa_nat0_scope.
Notation "m %. n" := (modulo m n) (only parsing)
  : jwa_nat0_scope.

Local Close Scope jwa_product_scope.

(* [d] divides [n] when some multiple of [d] is [n]. It is a partial order:
 * reflexive with [Positive Nat.One], transitive by multiplying the witnesses,
 * antisymmetric since [Nat.One] is the only unit.
 *)
(* [Nat0 -> Nat0 -> Prop] *)
Definition Divides := fun (d : Nat0) (n : Nat0) .
  forsome (k : Nat0) . d * k = n.

(* [Nat0 -> Prop] *)
Definition Even := fun (n : Nat0) . Divides (+ (Nat.Successor Nat.One)) n.

(* [Nat0 -> Prop] *)
Definition Odd := fun (n : Nat0) .
  forsome (k : Nat0) . (+ Nat.One) + ((+ (Nat.Successor Nat.One)) * k) = n.

Module positive. (* positive *)

(* positive.injectivity *)
Theorem injectivity
  : forall {m : Nat} {n : Nat} . (+ m) = + n -> m = n.
Proof.
  intros m n e.
  congru (fun (x : Nat0) . match x with | 0 => m | + y => y end), e |- e'.
  simpl in e'.
  ipso e'.
Qed.

Module order. (* positive.order *)

(* positive.order.embedding *)
Lemma embedding
  : forall (m : Nat) (n : Nat) .
      (+ m) < + n <-> (m < n)%n.
Proof.
  intros m n.
  divide et impera.
  - intro h.
    simpl ( _ < _ ) in h.
    match h with | k e end.
    simpl in e.
    let proof e' := positive.injectivity e.
    simpl ( _ < _ )%n in |- *.
    exists &k.
    ipso &e'.
  - intro h.
    simpl ( _ < _ )%n in h.
    match h with | k e end.
    simpl ( _ < _ ) in |- *.
    exists k.
    simpl in |- *.
    leibniz e in |- *.
    quod idem est.
Qed.

End order. (* positive.order *)

End positive. (* positive *)

Module increment. (* increment *)

(* increment.specification *)
Lemma specification : forall (n : Nat0) . (++ n) = (+ Nat.One) + n.
Proof.
  intros n.
  match n with | | p end; simpl in |- *.
  - quod idem est.
  - simpl Nat.inc in |- *.
    quod idem est.
Qed.

End increment. (* increment *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : Nat0) (m : Nat0) (n : Nat0) .
    (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  match l with
  |
  | l'
  end.
  - simpl in |- *.
    quod idem est.
  - match m with
    |
    | m'
    end.
    + simpl in |- *.
      quod idem est.
    + match n with
      |
      | n'
      end.
      * simpl in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (Nat.addition.associativity l' m' n') in |- *.
        quod idem est.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (m : Nat0) (n : Nat0) . m + n = n + m.
Proof.
  intros m n.
  match m with | | m' end; match n with | | n' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.addition.commutativity m' n') in |- *.
    quod idem est.
Qed.

(* addition.identity *)
Theorem identity
  : forall (n : Nat0) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intros n.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (addition.commutativity n 0) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* addition.left *)

(* addition.left.cancellation *)
Theorem cancellation
  : forall {n : Nat0} {m : Nat0} {k : Nat0} .
      n + m = n + k -> m = k.
Proof.
  intros n m k.
  match n with | | n' end.
  - simpl in |- *.
    intro e.
    ipso e.
  - match m with | | m' end; match k with | | k' end.
    + intro e.
      quod idem est.
    + simpl in |- *.
      intro e.
      let proof e
        := symm (positive.injectivity e).
      leibniz
        (Nat.addition.commutativity n' k') in e.
      let proof h
        := Nat.addition.identity.absence k' n'.
      simpl (~ _) in h.
      modus ponens h, e |- falso.
      ex falso quodlibet.
    + simpl in |- *.
      intro e.
      let proof e
        := positive.injectivity e.
      leibniz
        (Nat.addition.commutativity n' m') in e.
      let proof h
        := Nat.addition.identity.absence m' n'.
      simpl (~ _) in h.
      modus ponens h, e |- falso.
      ex falso quodlibet.
    + simpl in |- *.
      intro e.
      let proof e
        := positive.injectivity e.
      let proof e
        := Nat.addition.left.cancellation e.
      leibniz e in |- *.
      quod idem est.
Qed.

(* addition.left.commutativity *)
Lemma commutativity
  : forall (l : Nat0) (m : Nat0) (n : Nat0) .
      l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  leibniz (addition.commutativity l (m + n)) in |- *.
  leibniz (addition.associativity m n l)     in |- *.
  leibniz (addition.commutativity n l)       in |- *.
  quod idem est.
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.cancellation *)
Theorem cancellation
  : forall {m : Nat0} {k : Nat0} {n : Nat0} .
      m + n = k + n -> m = k.
Proof.
  intros m k n e.
  leibniz (addition.commutativity m n) in e.
  leibniz (addition.commutativity k n) in e.
  ipso (addition.left.cancellation e).
Qed.

Module identity. (* addition.right.identity *)

(* addition.right.identity.absence *)
Lemma absence
  : forall (m : Nat0) (n : Nat) . ~ (m + (+ n) = 0).
Proof.
  intros m n.
  simpl (~ _) in |- *.
  match m with | | m' end.
  - simpl in |- *.
    intro e.
    ex e quodlibet.
  - simpl in |- *.
    intro e.
    ex e quodlibet.
Qed.

End identity. (* addition.right.identity *)

Module order. (* addition.right.order *)

(* addition.right.order.extensivity *)
Theorem extensivity
  : forall (m : Nat0) (n : Nat0) . n <= m + n.
Proof.
  intros m n.
  simpl ( _ <= _ ) in |- *.
  match m with
  |
  | m'
  end.
  - simpl in |- *.
    ipso (disjoin (Identity.reflexivity n), _).
  - lemma facto : &n < (+ &m') + &n.
    {
      simpl ( _ < _ ) in |- *.
      exists m'.
      ipso (addition.commutativity n (+ m')).
    }
    ipso (disjoin _, facto).
Qed.

(* addition.right.order.positivity *)
Theorem positivity
  : forall (n : Nat0) (k : Nat) . 0 < n + (+ k).
Proof.
  intros n k.
  simpl ( _ < _ ) in |- *.
  match n with
  |
  | n'
  end.
  - simpl in |- *.
    exists k.
    quod idem est.
  - simpl in |- *.
    exists (n' + k)%n.
    quod idem est.
Qed.

End order. (* addition.right.order *)

End right. (* addition.right *)

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Nat0) (n : Nat0) (k : Nat0) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  divide et impera.
  - ipso (@addition.left.cancellation  m n k).
  - ipso (@addition.right.cancellation m k n).
Qed.

(* addition.interchange *)
Theorem interchange
  : forall (a : Nat0) (b : Nat0) (c : Nat0) (d : Nat0) .
      (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  leibniz (addition.associativity a b (c + d)) in |- *.
  leibniz (addition.left.commutativity b c d)  in |- *.
  leibniz (addition.associativity a c (b + d)) in |- *.
  quod idem est.
Qed.

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* "Strict" names the order preserved, not a direction: a strictly monotone
 * function carries [<] to [<] (equality excluded), a monotone one [<=] to
 * [<=].
 *)
(* addition.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : Nat0) (m : Nat0) (n : Nat0) . m < n -> k + m < k + n.
Proof.
  intros k m n h.
  simpl ( _ < _ ) in h.
  match h with | d e end.
  simpl ( _ < _ ) in |- *.
  exists d.
  leibniz (addition.associativity k m (+ d)) in |- *.
  leibniz e in |- *.
  quod idem est.
Qed.

(* addition.order.strict.cancellation *)
Theorem cancellation
  : forall (k : Nat0) (m : Nat0) (n : Nat0) . k + m < k + n -> m < n.
Proof.
  intros k m n h.
  simpl ( _ < _ ) in h.
  match h with | d e end.
  leibniz (addition.associativity k m (+ d)) in e.
  simpl ( _ < _ ) in |- *.
  exists d.
  ipso (addition.left.cancellation e).
Qed.

End strict. (* addition.order.strict *)

(* addition.order.monotonicity *)
Theorem monotonicity
  : forall (k : Nat0) (m : Nat0) (n : Nat0) . m <= n -> k + m <= k + n.
Proof.
  intros k m n h.
  simpl ( _ <= _ ) in h.
  match h with | e | lt end.
  - leibniz e in |- *.
    simpl ( _ <= _ ) in |- *.
    ipso (disjoin (Identity.reflexivity (k + n)), _).
  - simpl ( _ <= _ ) in |- *.
    ipso (disjoin _, (addition.order.strict.monotonicity k m n lt)).
Qed.

End order. (* addition.order *)

End addition. (* addition *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (m : Nat0) (n : Nat0) . m * n = n * m.
Proof.
  intros m n.
  match m with | | m' end; match n with | | n' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' n') in |- *.
    quod idem est.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (l : Nat0) (m : Nat0) (n : Nat0) . (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  match l with | | l' end.
  - simpl in |- *.
    quod idem est.
  - match m with | | m' end.
    + simpl in |- *.
      quod idem est.
    + match n with | | n' end.
      * simpl in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (Nat.multiplication.associativity l' m' n') in |- *.
        quod idem est.
Qed.

(* multiplication.annihilation *)
Theorem annihilation
  : forall (n : Nat0) . (0 * n = 0) /\ (n * 0 = 0).
Proof.
  intros n.
  divide et impera.
  - simpl in |- *.
    quod idem est.
  - leibniz (multiplication.commutativity n 0) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Lemma identity : forall (n : Nat0) . (+ Nat.One) * n = n.
Proof.
  intros n.
  match n with | | n' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
Qed.

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (l : Nat0) (m : Nat0) (n : Nat0) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  match l with
  |
  | l'
  end.
  - simpl in |- *.
    quod idem est.
  - match m with
    |
    | m'
    end.
    + simpl in |- *.
      quod idem est.
    + match n with
      |
      | n'
      end.
      * simpl in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (Nat
          .multiplication
          .left
          .distributivity.over.addition l' m' n') in |- *.
        quod idem est.
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

Module order. (* multiplication.left.order *)

Module strict. (* multiplication.left.order.strict *)

(* multiplication.left.order.strict.monotonicity *)
Theorem monotonicity
  : forall (k : Nat) (m : Nat0) (n : Nat0) .
      m < n -> (+ k) * m < (+ k) * n.
Proof.
  intros k m n h.
  simpl ( _ < _ ) in h.
  match h with | d e end.
  symm in e.
  simpl ( _ < _ ) in |- *.
  exists (k * d)%n.
  match m with
  |
  | m'
  end.
  - simpl in e.
    leibniz e in |- *.
    simpl in |- *.
    quod idem est.
  - simpl in e.
    leibniz e in |- *.
    simpl in |- *.
    leibniz (Nat
      .multiplication
      .left
      .distributivity.over.addition k m' d) in |- *.
    quod idem est.
Qed.

End strict. (* multiplication.left.order.strict *)

End order. (* multiplication.left.order *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
Lemma identity : forall (m : Nat0) . m * (+ Nat.One) = m.
Proof.
  intros m.
  match m with | | m' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (Nat.multiplication.commutativity m' Nat.One) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (l : Nat0) (m : Nat0) (n : Nat0) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  leibniz (multiplication.commutativity (m + n) l) in |- *.
  leibniz (multiplication.left.distributivity.over.addition l m n) in |- *.
  leibniz (multiplication.commutativity l m) in |- *.
  leibniz (multiplication.commutativity l n) in |- *.
  quod idem est.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

Module order. (* multiplication.right.order *)

(* multiplication.right.order.extensivity *)
Theorem extensivity
  : forall (k : Nat) (n : Nat0) . n <= (+ k) * n.
Proof.
  intros k n.
  simpl ( _ <= _ ) in |- *.
  match n with
  |
  | p
  end.
  - simpl in |- *.
    ipso (disjoin (Identity.reflexivity 0), _).
  - match k with
    |
    | k'
    end.
    + simpl in |- *.
      ipso (disjoin (Identity.reflexivity (+ p)), _).
    + lemma facto
      : (+ &p) < (+ Nat.Successor &k') * (+ &p).
      {
        simpl ( _ < _ ) in |- *.
        exists (k' * p)%n.
        simpl in |- *.
        quod idem est.
      }
      ipso (disjoin _, facto).
Qed.

End order. (* multiplication.right.order *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (n : Nat0) . ((+ Nat.One) * n = n) /\ (n * (+ Nat.One) = n).
Proof.
  intros n.
  divide et impera.
  - ipso (multiplication.left.identity  n).
  - ipso (multiplication.right.identity n).
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : Nat0) (y : Nat0) (z : Nat0) .
      (x * (y + z) = (x * y) + (x * z)) /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (multiplication
            .left
            .distributivity.over.addition x y z).
  - ipso (multiplication
            .right
            .distributivity.over.addition x y z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module power. (* power *)

Module exponent. (* power.exponent *)

(* power.exponent.absence *)
Lemma absence : forall (m : Nat0) . m ^ 0 = + Nat.One.
Proof.
  intros m.
  simpl in |- *.
  quod idem est.
Qed.

(* power.exponent.addition *)
Theorem addition
  : forall (m : Nat0) (a : Nat0) (b : Nat0) . m ^ a * m ^ b = m ^ (a + b).
Proof.
  intros m a b.
  match a with | | a' end; match b with | | b' end.
  - simpl in |- *.
    quod idem est.
  - match m with | | m' end; simpl in |- *; quod idem est.
  - match m with | | m' end.
    * simpl in |- *.
      quod idem est.
    * simpl in |- *.
      leibniz
        (Nat.multiplication.commutativity (m' ^ a')%n Nat.One) in |- *.
      simpl in |- *.
      quod idem est.
  - match m with | | m' end.
    * simpl in |- *.
      quod idem est.
    * simpl in |- *.
      leibniz
        (Nat.power.exponent.addition m' a' b') in |- *.
      quod idem est.
Qed.

(* power.exponent.multiplication *)
Theorem multiplication
  : forall (m : Nat0) (a : Nat0) (b : Nat0) .
      (m ^ a) ^ b = m ^ (a * b).
Proof.
  intros m a b.
  match a with | | a' end; match b with | | b' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz
      (Nat.power.annihilation b') in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - match m with
    |
    | m'
    end.
    * simpl in |- *.
      quod idem est.
    * simpl in |- *.
      leibniz
        (Nat.power.exponent.multiplication m' a' b') in |- *.
      quod idem est.
Qed.

End exponent. (* power.exponent *)

Module distributivity. (* power.distributivity *)

Module over. (* power.distributivity.over *)

(* power.distributivity.over.multiplication *)
Theorem multiplication
  : forall (m : Nat0) (n : Nat0) (a : Nat0) .
      (m * n) ^ a = m ^ a * n ^ a.
Proof.
  intros m n a.
  match a with
  |
  | a'
  end.
  - simpl in |- *.
    quod idem est.
  - match m with
    |
    | m'
    end.
    + simpl in |- *.
      quod idem est.
    + match n with
      |
      | n'
      end.
      * simpl in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz
          (Nat.power.distributivity.over.multiplication m' n' a') in |- *.
        quod idem est.
Qed.

End over. (* power.distributivity.over *)

End distributivity. (* power.distributivity *)

End power. (* power *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : Nat0) . ~ (n < n).
Proof.
  intros n.
  simpl (~ _) in |- *.
  intro h.
  simpl ( _ < _ ) in h.
  match h with | k e end.
  match n with | | n' end; simpl in e.
  - ex e quodlibet.
  - let proof e
      := positive.injectivity e.
    leibniz
      (Nat.addition.commutativity n' k) in e.
    let proof i
      := Nat.addition.identity.absence k n'.
    simpl (~ _) in i.
    modus ponens i, e |- falso.
    ex falso quodlibet.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : Nat0} {m : Nat0} {n : Nat0} . l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  simpl ( _ < _ ) in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl ( _ < _ ) in |- *.
  exists (k1 + k2)%n.
  symm in e1, e2.
  leibniz e2, e1 in |- *.
  leibniz (addition.associativity l (+ k1) (+ k2)) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

Module zero. (* order.strict.zero *)

(* order.strict.zero.accessibility *)
Lemma accessibility : Accessible (<) 0.
Proof.
  lemma below
  : forall (y : Nat0) . (y < 0) -> Accessible (<) y.
  {
    intros y h.
    match h with | k e end.
    match y with
    |
    | q
    end; simpl in e; ex e quodlibet.
  }
  ipso (Accessible.introduction &below).
Qed.

End zero. (* order.strict.zero *)

(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (n : Nat0) . Accessible (<) n.
Proof.
  intros n.
  match n with
  |
  | p
  end.
  - ipso order.strict.zero.accessibility.
  - match p with
    |
    | p' by IH
    end per Nat.induction.
    + lemma below
      : forall (y : Nat0) . (y < (+ Nat.One)) -> Accessible (<) y.
      {
        intros y h.
        match h with | k e end.
        match y with
        |
        | q end.
        * ipso order.strict.zero.accessibility.
        * simpl in e.
          let proof falso := positive.injectivity e.
          match q with
          |
          | q' end
          ; simpl in falso
          ; ex falso quodlibet.
      }
      ipso (Accessible.introduction &below).
    + lemma below
        : forall (y : Nat0) . y < (+ Nat.Successor &p') -> Accessible (<) y.
      {
        intros y h.
        match h with | k e end.
        match y with | | q end.
        * ipso order.strict.zero.accessibility.
        * simpl in e.
          let proof e := positive.injectivity e.
          leibniz (Nat.addition.commutativity q k) in e.
          match k with
          |
          | k' end
          ; simpl in e
          ; let proof e := Nat.successor.injectivity e.
          --
             leibniz e in |- *.
             ipso IH.
          --
             lemma smaller : (+ &q) < (+ &p').
             {
               simpl ( _ < _ ) in |- *.
               exists k'.
               simpl in |- *.
               leibniz (Nat.addition.commutativity q k') in |- *.
               leibniz e in |- *.
               quod idem est.
             }
             ipso (Accessible.descend &IH &smaller).
      }
      ipso (Accessible.introduction &below).
Qed.

End strict. (* order.strict *)

(* order.discreteness *)
Theorem discreteness
  : forall (m : Nat0) (n : Nat0) .
      m < n + (+ Nat.One) <-> m <= n.
Proof.
  intros m n.
  divide et impera.
  - intro h.
    simpl ( _ < _ )  in h.
    simpl ( _ <= _ ) in |- *.
    match h with | k e end.
    match k with | | k' end.
    + ipso (disjoin (addition.right.cancellation e), _).
    + lemma facto : &m < &n.
      {
        simpl ( _ < _ ) in |- *.
        exists k'.
        let proof e : m + ((+ Nat.One) + (+ k')) = n + (+ Nat.One) := &e.
        leibniz
          -> (addition.commutativity (+ Nat.One) (+ k'))
          in e.
        leibniz
          <- (addition.associativity m (+ k') (+ Nat.One))
          in e.
        ipso (addition.right.cancellation e).
      }
      ipso (disjoin _, facto).
  - intro h.
    simpl ( _ <= _ ) in h.
    simpl ( _ < _ )  in |- *.
    match h with | e | lt end.
    + exists Nat.One.
      leibniz e in |- *.
      quod idem est.
    + simpl ( _ < _ ) in lt.
      match lt with
      | k e
      end.
      exists (Nat.Successor k).
      lemma facto
      : &m + ((+ Nat.One) + (+ &k)) = &n + (+ Nat.One).
      {
        leibniz
          -> (addition.commutativity (+ Nat.One) (+ k))
          in |- *.
        leibniz
          <- (addition.associativity m (+ k) (+ Nat.One))
          in |- *.
        leibniz
          -> e
          in |- *.
        quod idem est.
      }
      ipso facto.
Qed.

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : Nat0) (n : Nat0) .
      compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  match m with | | m' end; match n with | | n' end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (Nat.comparison.antisymmetry m' n').
Qed.

Module strict. (* comparison.strict *)

(* comparison.strict.specification *)
Lemma specification
  : forall (m : Nat0) (n : Nat0) . compare m n = Comparison.Lt <-> m < n.
Proof.
  intros m n.
  match m with | | m' end; match n with | | n' end; divide et impera.

  - simpl in |- *.
    intro e.
    ex e quodlibet.

  - intro h.
    let proof i := order.strict.irreflexivity 0.
    simpl (~ _) in i.
    modus ponens i, h |- f.
    ex f quodlibet.

  - intro e.
    simpl ( _ < _ ) in |- *.
    exists n'.
    simpl in |- *.
    quod idem est.

  - intro h.
    simpl in |- *.
    quod idem est.

  - simpl in |- *.
    intro e.
    ex e quodlibet.

  - intro h.
    simpl ( _ < _ ) in h.
    match h with | k e end.
    simpl in e.
    ex e quodlibet.

  - simpl in |- *.
    intro e.
    ipso (modus aequans
            (positive.order.embedding m' n'),
            (Nat.comparison.strict.forward.specification e)).

  - intro h.
    simpl in |- *.
    modus aequans (positive.order.embedding m' n'), h |- lt.
    let proof facto
      := Nat.comparison.strict.backward.specification lt.
    ipso facto.
Qed.

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Lemma specification
  : forall (m : Nat0) (n : Nat0) . (compare m n = Comparison.Eq) <-> m = n.
Proof.
  intros m n.
  divide et impera.
  - intro e.
    match m with | | m' end ; match n with | | n' end.
    + quod idem est.
    + simpl in e. ex e quodlibet.
    + simpl in e. ex e quodlibet.
    + simpl in e.
      leibniz
        -> (Nat.comparison.equality.forward.specification e)
        in |- *.
      quod idem est.
  - intro e.
    leibniz e in |- *.
    match n with
    |
    | n' end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      ipso (Comparable.comparison.reflexivity n').
Qed.

End equality. (* comparison.equality *)

(* comparison.specification *)
Theorem specification
  : forall (m : Nat0) (n : Nat0) .
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
Proof.
  intros m n.
  divide et impera.
  - ipso (comparison.strict.specification
            m n).
  - ipso (comparison.equality.specification
            m n).
Qed.

End comparison. (* comparison *)

Instance comparable
  : Comparable compare (<) :=
  {| Comparable.transitivity  := @order.strict.transitivity
   ; Comparable.specification := comparison.specification
   ; Comparable.antisymmetry  := comparison.antisymmetry |}.

Module maximum. (* maximum *)

Module left. (* maximum.left *)

(* maximum.left.identity *)
Lemma identity : forall (n : Nat0) . max 0 n = n.
Proof.
  intros n.
  simpl Comparable.max in |- *.
  match n with | | n' end; simpl in |- *; quod idem est.
Qed.

End left. (* maximum.left *)

Module right. (* maximum.right *)

(* maximum.right.identity *)
Lemma identity : forall (n : Nat0) . max n 0 = n.
Proof.
  intros n.
  leibniz
    -> (Comparable.maximum.commutativity n 0)
    in |- *.
  ipso (maximum.left.identity n).
Qed.

End right. (* maximum.right *)

(* maximum.identity *)
Theorem identity
  : forall (n : Nat0) . (max 0 n = n) /\ (max n 0 = n).
Proof.
  intros n.
  divide et impera.
  - ipso (maximum.left.identity  n).
  - ipso (maximum.right.identity n).
Qed.

End maximum. (* maximum *)

Module minimum. (* minimum *)

Module left. (* minimum.left *)

(* minimum.left.annihilation *)
Lemma annihilation : forall (n : Nat0) . min 0 n = 0.
Proof.
  intros n.
  simpl Comparable.min in |- *.
  match n with | | n' end; simpl in |- *; quod idem est.
Qed.

Module distributivity. (* minimum.left.distributivity *)

Module of. (* minimum.left.distributivity.of *)

(* minimum.left.distributivity.of.addition *)
Theorem addition
  : forall (k : Nat0) (m : Nat0) (n : Nat0) .
      k + min m n = min (k + m) (k + n).
Proof.
  intros k m n.
  let proof spec
    := Comparable.minimum.specification.
  let proof totality
    := Comparable.order.totality m n.
  match &totality with
  | h
  | h
  end.
  -
    let proof s := spec m n.
    modus aequans s, h |- e1.
    leibniz e1 in |- *.

    modus aequans
      (Comparable.minimum.specification (k + m) (k + n)),
      (addition.order.monotonicity k m n h)
    |- e2.
    leibniz e2 in |- *.

    quod idem est.
  -
    let proof comm := Comparable.minimum.commutativity.
    leibniz (comm m n) in |- *.
    leibniz (comm (k + m) (k + n)) in |- *.

    modus aequans (spec n m), h |- e1.
    leibniz e1 in |- *.

    modus aequans
      (Comparable.minimum.specification (k + n) (k + m)),
      (addition.order.monotonicity k n m h)
    |- e2.
    leibniz e2 in |- *.

    quod idem est.
Qed.

End of. (* minimum.left.distributivity.of *)

End distributivity. (* minimum.left.distributivity *)

End left. (* minimum.left *)

Module right. (* minimum.right *)

(* minimum.right.annihilation *)
Lemma annihilation : forall (n : Nat0) . min n 0 = 0.
Proof.
  intros n.
  leibniz (Comparable.minimum.commutativity n 0) in |- *.
  ipso (minimum.left.annihilation n).
Qed.

End right. (* minimum.right *)

(* minimum.annihilation *)
Theorem annihilation
  : forall (n : Nat0) . (min 0 n = 0) /\ (min n 0 = 0).
Proof.
  intros n.
  divide et impera.
  - ipso (minimum.left.annihilation  n).
  - ipso (minimum.right.annihilation n).
Qed.

End minimum. (* minimum *)

Module subtraction. (* subtraction *)

Module saturating. (* subtraction.saturating *)

Module inversion. (* subtraction.saturating.inversion *)

Module of. (* subtraction.saturating.inversion.of *)

(* subtraction.saturating.inversion.of.addition *)
Theorem addition
  : forall (m : Nat0) (n : Nat0) . saturating_sub (m + n) n = m.
Proof.
  intros m n.
  match n with
  |
  | n'
  end
  ; match m with
  |
  | m'
  end.

  - simpl in |- *. quod idem est.

  - simpl in |- *. quod idem est.

  - simpl in |- *.
    leibniz (Nat
              .subtraction
              .truncation (Comparable.order.reflexivity n')) in |- *.
    simpl in |- *.
    quod idem est.

  - simpl in |- *.
    leibniz (Nat
              .subtraction
              .inversion.of.addition m' n') in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End of. (* subtraction.saturating.inversion.of *)

End inversion. (* subtraction.saturating.inversion *)

(* subtraction.saturating.truncation *)
Theorem truncation
  : forall {m : Nat0} {n : Nat0} . m <= n -> saturating_sub m n = 0.
Proof.
  intros m n h.
  simpl ( _ <= _ ) in h.
  match h with
  | e
  | lt
  end.

  -
    leibniz e in |- *.
    match n with
    |
    | n'
    end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (Nat.subtraction.truncation (Comparable.order.reflexivity n')) in |- *.
      simpl in |- *.
      quod idem est.

  -
    simpl ( _ < _ ) in lt.
    match lt with
    | k e
    end.
    leibniz (symm e) in |- *.
    match m with
    |
    | m'
    end.
    + simpl in |- *. quod idem est.
    + simpl in |- *.
      leibniz (Nat
                .subtraction
                .truncation (disjoin
                              _,
                              (Nat.addition.order.extensivity m' k))) in |- *.
      simpl in |- *.
      quod idem est.
Qed.

(* subtraction.saturating.specification *)
Theorem specification
  : forall {m : Nat0} {n : Nat0} .
      n <= m -> n + saturating_sub m n = m.
Proof.
  intros m n h.
  simpl ( _ <= _ ) in h.
  match h with
  | e
  | lt
  end.
  -
    leibniz e in |- *.
    leibniz (subtraction
              .saturating
              .truncation (Comparable.order.reflexivity m)) in |- *.
    match m with | | m' end; simpl in |- *; quod idem est.
  -
    simpl ( _ < _ ) in lt.
    match lt with
    | k e
    end.
    leibniz (symm e) in |- *.
    leibniz (addition.commutativity n (+ k)) in |- *.
    leibniz (subtraction.saturating.inversion.of.addition (+ k) n) in |- *.
    leibniz (addition.commutativity n (+ k)) in |- *.
    quod idem est.
Qed.

Module right. (* subtraction.saturating.right *)

(* subtraction.saturating.right.identity *)
Theorem identity : forall (n : Nat0) . saturating_sub n 0 = n.
Proof.
  intros n.
  match n with | | n' end; simpl in |- *; quod idem est.
Qed.

End right. (* subtraction.saturating.right *)

(* subtraction.saturating.cancellation *)
Theorem cancellation
  : forall (k : Nat0) (m : Nat0) (n : Nat0) .
      saturating_sub (k + m) (k + n) = saturating_sub m n.
Proof.
  intros k m n.
  match k with | | k' end.
  - simpl in |- *. quod idem est.
  - match m with | | m' end; match n with | | n' end.
    + simpl in |- *.
      leibniz (Nat
                .subtraction
                .truncation
                  (Comparable.order.reflexivity k')) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (Nat
                .subtraction
                .truncation
                  (disjoin _, (Nat.addition.order.extensivity k' n'))) in |- *.
      simpl in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (Nat
                .addition.commutativity k' m') in |- *.
      leibniz (Nat
                .subtraction
                .inversion.of.addition m' k') in |- *.
      simpl in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (Nat
                .subtraction
                .cancellation k' m' n') in |- *.
      quod idem est.
Qed.

End saturating. (* subtraction.saturating *)

(* subtraction.truncation *)
Theorem truncation
  : forall {m : Nat0} {n : Nat0} . m < n -> sub m n = None.
Proof.
  intros m n h.
  simpl sub in |- *.
  match (le n m) with | | end |- c.
  - modus aequans
      (Comparable.order.reflection n m),
      c
    |- order.
    simpl Comparable.LessOrEqual in order.
    match order with
    | e
    | lt
    end.
    + leibniz e in h.
      let proof i := order.strict.irreflexivity m.
      simpl (~ _) in i.
      modus ponens i, h |- falso.
      ex falso quodlibet.
    + let proof a := Comparable.order.strict.asymmetry m n h.
      simpl (~ _) in a.
      modus ponens a, lt |- falso.
      ex falso quodlibet.
  - quod idem est.
Qed.

Module inversion. (* subtraction.inversion *)

Module of. (* subtraction.inversion.of *)

(* subtraction.inversion.of.addition *)
Theorem addition
  : forall (m : Nat0) (n : Nat0) . sub (m + n) n = Some m.
Proof.
  intros m n.
  simpl sub in |- *.
  leibniz (subtraction.saturating
            .inversion.of.addition m n) in |- *.
  modus aequans
    (Comparable.order.reflection n (m + n)),
    (addition.right.order.extensivity m n)
  |- e.
  leibniz e in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End of. (* subtraction.inversion.of *)

End inversion. (* subtraction.inversion *)

(* subtraction.specification *)
Theorem specification
  : forall (m : Nat0) (n : Nat0) (k : Nat0) .
      sub m n = Some k <-> n + k = m.
Proof.
  intros m n k.
  divide et impera.

  - intro e.
    symm in e.
    simpl sub in e.
    match (le n m) with | | end |- c.
    + let proof e' := Option.some.injectivity e.
      modus aequans
        (Comparable.order.reflection n m),
        c
      |- order.
      leibniz e' in |- *.
      ipso (subtraction.saturating.specification order).
    + ex e quodlibet.

  - intro e.
    symm in e.
    leibniz e in |- *.
    leibniz (addition.commutativity n k) in |- *.
    ipso (subtraction.inversion.of.addition k n).
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
  match p with | | p' by IH end per Nat.induction.
  - match d with | | d' end; divide et impera; simpl in |- *.
    * quod idem est.
    * simpl ( _ < _ ) in |- *.
      exists Nat.One.
      simpl in |- *.
      quod idem est.
    * quod idem est.
    * simpl ( _ < _ ) in |- *.
      exists d'.
      simpl in |- *.
      quod idem est.
  - match IH with | e lt end.
    simpl in |- *.
    match (div.nat p' d) with | q r end |- D.
    simpl in e.
    simpl in lt.
    match (eq (++ r) (+ d)) with | | end |- E; divide et impera; simpl in |- *.
    * modus aequans
        (Comparable.comparison.equality.reflection (++ r) (+ d)),
        E
      |- full.
      leibniz (increment.specification r) in full.
      leibniz (increment.specification q) in |- *.
      leibniz (multiplication
                  .right
                  .distributivity.over.addition (+ d) (+ Nat.One) q) in |- *.
      leibniz (multiplication
                  .left
                  .identity (+ d)) in |- *.
      leibniz (addition.commutativity
                (+ d)
                (q * (+ d)))
      in |- *.
      leibniz (addition.commutativity
                ((q * (+ d)) + (+ d))
                0)
      in |- *.
      simpl in |- *.
      leibniz (symm full) in e |- *.
      leibniz (addition.left.commutativity
                (q * ((+ Nat.One) + r))
                (+ Nat.One)
                r)
      in |- *.
      leibniz e in |- *.
      simpl in |- *.
      quod idem est.
    * simpl ( _ < _ ) in |- *.
      exists d.
      simpl in |- *.
      quod idem est.
    * leibniz (increment.specification r) in |- *.
      leibniz (addition.left.commutativity (q * (+ d)) (+ Nat.One) r) in |- *.
      leibniz e in |- *.
      simpl in |- *.
      quod idem est.
    * simpl ( _ < _ ) in lt.
      match lt with | k ek end.
      leibniz (increment.specification r) in E.
      leibniz (addition.commutativity (+ Nat.One) r) in E.
      leibniz (increment.specification r) in |- *.
      leibniz (addition.commutativity (+ Nat.One) r) in |- *.
      match k with | | k' end.
      {
        modus aequans
          (Comparable.comparison.equality.reflection (r + (+ Nat.One)) (+ d)),
          ek
        |- full.
        leibniz full in E.
        ex E quodlibet.
      }
      {
        simpl ( _ < _ ) in |- *.
        exists k'.
        leibniz (addition.associativity r (+ Nat.One) (+ k')) in |- *.
        simpl in |- *.
        ipso ek.
      }
Qed.

Module dividend. (* division.nat.dividend *)

(* division.nat.dividend.reconstruction *)
Theorem reconstruction
  : forall (p : Nat) (d : Nat) . (((+ p) /. d) * (+ d)) + ((+ p) %. d) = + p.
Proof.
  intros p d.
  match (division.nat.specification p d) with | h1 h2 end.
  ipso h1.
Qed.

End dividend. (* division.nat.dividend *)

Module remainder. (* division.nat.remainder *)

(* division.nat.remainder.boundedness *)
Theorem boundedness
  : forall (p : Nat) (d : Nat) . ((+ p) %. d) < + d.
Proof.
  intros p d.
  match (division.nat.specification p d) with | h1 h2 end.
  ipso h2.
Qed.

End remainder. (* division.nat.remainder *)

Module quotient. (* division.nat.quotient *)

(* division.nat.quotient.positivity *)
Theorem positivity
  : forall (d : Nat) (g : Nat) . Divides (+ g) (+ d) -> ~ ((+ d) /. g = 0).
Proof.
  intros d g h.
  simpl (~ _) in |- *.
  intro e.
  let proof reconstruction := division.nat.dividend.reconstruction d g.
  leibniz e in reconstruction.
  match (multiplication.annihilation (+ g)) with | annihilation _ end.
  leibniz &annihilation in reconstruction.
  match (addition.identity ((+ d) %. g)) with | identity _ end.
  leibniz &identity in reconstruction.
  let proof bound := division.nat.remainder.boundedness d g.
  leibniz reconstruction in bound.
  match h with | k hk end.
  match k with
  |
  | k'
  end.
  - match (multiplication.annihilation (+ g)) with | _ annihilation' end.
    leibniz annihilation' in hk.
    ex hk quodlibet.
  - match k' with
    |
    | k''
    end.
    +
      leibniz (multiplication.right.identity (+ g)) in hk.
      leibniz hk in bound.
      let proof irreflexivity
        := order.strict.irreflexivity (+ d).
      simpl (~ _) in irreflexivity.
      modus ponens irreflexivity, bound |- falso.
      ex falso quodlibet.
    +
      let proof hk
        : (+ &g) * ((+ Nat.One) + (+ &k'')) = (+ &d)
        := &hk.
      leibniz (multiplication
                  .left
                  .distributivity.over.addition (+ g) (+ Nat.One) (+ k'')) in hk.
      leibniz (multiplication
                  .right
                  .identity (+ g)) in hk.
      leibniz (addition
                  .commutativity
                  (+ g)
                  ((+ g) * (+ k''))) in hk.
      let proof extensivity
        := addition.right.order.extensivity ((+ g) * (+ k'')) (+ g).
      leibniz hk in extensivity.
      simpl ( _ <= _ ) in extensivity.
      match extensivity with
      | equal
      | less
      end.
      *
        leibniz equal in bound.
        let proof irreflexivity
          := order.strict.irreflexivity (+ d).
        simpl (~ _) in irreflexivity.
        modus ponens irreflexivity, bound |- falso.
        ex falso quodlibet.
      *
        let proof circular
          := order.strict.transitivity bound less.
        let proof irreflexivity
          := order.strict.irreflexivity (+ d).
        simpl (~ _) in irreflexivity.
        modus ponens irreflexivity, circular |- falso.
        ex falso quodlibet.
Qed.

End quotient. (* division.nat.quotient *)

End nat. (* division.nat *)

Local Close Scope jwa_product_scope.

Module dividend. (* division.dividend *)

(* division.dividend.reconstruction *)
Theorem reconstruction
  : forall (n : Nat0) (d : Nat) . ((n /. d) * (+ d)) + (n %. d) = n.
Proof.
  intros n d.
  match n with | | p end.
  - simpl divide, modulo, div in |- *.
    simpl in |- *.
    quod idem est.
  - ipso (division.nat.dividend.reconstruction p d).
Qed.

End dividend. (* division.dividend *)

Module remainder. (* division.remainder *)

(* division.remainder.boundedness *)
Theorem boundedness : forall (n : Nat0) (d : Nat) . (n %. d) < + d.
Proof.
  intros n d.
  match n with | | p end.
  - simpl ( _ < _ ) in |- *.
    exists d.
    simpl in |- *.
    quod idem est.
  - ipso (division.nat.remainder.boundedness p d).
Qed.

End remainder. (* division.remainder *)

(* division.specification *)
Theorem specification
  : forall (n : Nat0) (d : Nat) .
      (((n /. d) * (+ d)) + (n %. d) = n)
      /\ (n %. d) < + d.
Proof.
  intros n d.
  divide et impera.
  - ipso (division.dividend.reconstruction n d).
  - ipso (division.remainder.boundedness n d).
Qed.

(* division.uniqueness *)
Theorem uniqueness
  : forall (n : Nat0) (d : Nat) (m : Nat0) (r : Nat0) .
      ((m * (+ d)) + r = n /\ r < (+ d)) -> ((n /. d) = m) /\ ((n %. d) = r).
Proof.
  intros n d m r h.
  match h with | e b end.
  let proof recon
    := division.dividend.reconstruction n d.
  let proof bound
    := division.remainder.boundedness n d.
  lemma quotient : (n /. d) = m.
  {
    let proof t
      := Comparable.order.strict.trichotomy (n /. d) m.
    match t with
    | below
    | rest
    end.
    - simpl ( _ < _ ) in below.
      match below with | k hk end.
      symm in hk.
      leibniz hk in e.
      leibniz (multiplication.right.distributivity.over.addition
                  (+ d) (n /. d) (+ k)) in e.
      leibniz (addition.associativity
                  ((n /. d) * (+ d)) ((+ k) * (+ d)) r) in e.
      symm in recon.
      let proof chain
        := Identity.transitivity e recon.
      let proof excess
        := addition.left.cancellation chain.
      symm in excess.
      leibniz excess in bound.
      leibniz (addition.commutativity ((+ k) * (+ d)) r) in bound.
      let proof reach
        := multiplication.right.order.extensivity k (+ d).
      let proof grow
        := addition.right.order.extensivity r ((+ k) * (+ d)).
      let proof span
        := Comparable.order.transitivity
              (+ d)
              ((+ k) * (+ d))
              (r + ((+ k) * (+ d)))
              reach
              grow.
      let proof i
        := order.strict.irreflexivity (+ d).
      simpl (~ _) in i.
      simpl Comparable.LessOrEqual in span.
      match span with
      | s1
      | s2
      end.
      +
        leibniz (symm s1) in bound.
        modus ponens i, bound |- falso.
        ex falso quodlibet.
      +
        let proof loop := order.strict.transitivity s2 bound.
        modus ponens i, loop |- falso.
        ex falso quodlibet.
    - match rest with
      | equal
      | above
      end.
      + ipso equal.
      + simpl ( _ < _ ) in above.
        match above with | k hk end.
        leibniz (symm hk) in recon.
        leibniz (multiplication.right.distributivity.over.addition
                    (+ d)
                    m
                    (+ k)) in recon.
        leibniz (addition.associativity
                    (m * (+ d))
                    ((+ k) * (+ d))
                    (n %. d)) in recon.
        let proof chain
          := Identity.transitivity recon (symm e).
        let proof excess
          := addition.left.cancellation chain.
        leibniz (symm excess) in b.
        leibniz (addition.commutativity
                    ((+ k) * (+ d))
                    (n %. d)) in b.
        let proof reach
          := multiplication.right.order.extensivity k (+ d).
        let proof grow
          := addition.right.order.extensivity
                (n %. d)
                ((+ k) * (+ d)).
        let proof span
          := Comparable.order.transitivity
                (+ d)
                ((+ k) * (+ d))
                ((n %. d) + ((+ k) * (+ d)))
                reach
                grow.
        let proof i
          := order.strict.irreflexivity (+ d).
        simpl (~ _) in i.
        simpl Comparable.LessOrEqual in span.
        match span with
        | s1
        | s2
        end.
        * leibniz (symm s1) in b.
          modus ponens i, b |- falso.
          ex falso quodlibet.
        * let proof loop := order.strict.transitivity s2 b.
          modus ponens i, loop |- falso.
          ex falso quodlibet.
  }
  divide et impera.
  -
    ipso quotient.
  -
    leibniz quotient in recon.
    let proof chain := Identity.transitivity recon (symm e).
    ipso (addition.left.cancellation chain).
Qed.

(* division.invariance *)
Theorem invariance
  : forall (n : Nat0) (d : Nat) (k : Nat) .
      (((+ k) * n) /. (k * d)%n) = n /. d.
Proof.
  intros n d k.

  let proof recon
    := division.dividend.reconstruction n d.
  let proof bound
    := division.remainder.boundedness n d.

  lemma witness
  : (((n /. d) * (+ (k * d)%n)) + ((+ k) * (n %. d)) = (+ k) * n)
  /\ ((+ k) * (n %. d)) < (+ (k * d)%n).
  {
    divide et impera.
    -
      lemma facto
      : ((n /. d) * ((+ k) * (+ d))) + ((+ k) * (n %. d)) = (+ k) * n.
      {
        leibniz (multiplication.commutativity (n /. d) ((+ k) * (+ d))) in |- *.
        leibniz (multiplication.associativity (+ k) (+ d) (n /. d))     in |- *.
        leibniz (multiplication.commutativity (+ d) (n /. d))           in |- *.
        let proof dist
          := Identity.symmetry
                (multiplication.left.distributivity.over.addition
                    (+ k)
                    ((n /. d) * (+ d))
                    (n %. d)).
        leibniz dist, recon  in |- *.
        quod idem est.
      }
      ipso facto.
    -
      lemma facto
      : ((+ &k) * (&n %. &d)) < (+ &k) * (+ &d).
      {
        ipso (multiplication.left.order.strict.monotonicity
                k
                (n %. d)
                (+ d)
                bound).
      }
      ipso facto.
  }

  match (division.uniqueness
          ((+ k) * n)
          (k * d)%n
          (n /. d)
          ((+ k) * (n %. d))
          witness)
  with | facto _ end.
  ipso facto.
Qed.

(* division.exactness *)
Theorem exactness
  : forall (n : Nat0) (d : Nat) . Divides (+ d) n -> (n /. d) * (+ d) = n.
Proof.
  intros n d h.
  simpl Divides in h.
  match h with | k hk end.

  lemma witness
  : ((k * (+ d)) + 0 = n) /\ 0 < (+ d).
  {
    divide et impera.
    - match (addition.identity (k * (+ d))) with | _ vanishing end.
      leibniz vanishing in |- *.
      leibniz (multiplication.commutativity k (+ d)) in |- *.
      ipso hk.
    - simpl ( _ < _ ) in |- *.
      exists d.
      simpl in |- *.
      quod idem est.
  }

  match (division.uniqueness n d k 0 witness) with | quotient _ end.
  leibniz quotient in |- *.
  leibniz (multiplication.commutativity k (+ d)) in |- *.
  ipso hk.
Qed.

(* division.iteration *)
Theorem iteration
  : forall (n : Nat0) (a : Nat) (b : Nat) .
      ((n /. a) /. b) = (n /. (a * b)%n).
Proof.
  intros n a b.
  match (division.specification &n &a) with | e1 bound1 end.
  match (division.specification (&n /. &a) &b) with | e2 bound2 end.
  lemma product : (+ (&b * &a)%n) = (+ &b) * (+ &a).
  {
    simpl in |- *.
    quod idem est.
  }
  lemma reconstruction
    : (((&n /. &a) /. &b) * (+ (&a * &b)%n))
      + ((((&n /. &a) %. &b) * (+ &a)) + (&n %. &a))
      = &n.
  {
    leibniz (Nat.multiplication.commutativity &a &b), &product in |- *.
    leibniz <- (multiplication.associativity ((&n /. &a) /. &b) (+ &b) (+ &a)) in |- *.
    leibniz <- (addition.associativity
      ((((&n /. &a) /. &b) * (+ &b)) * (+ &a))
      (((&n /. &a) %. &b) * (+ &a))
      (&n %. &a)) in |- *.
    leibniz <- (multiplication.right.distributivity.over.addition
      (+ &a) (((&n /. &a) /. &b) * (+ &b)) ((&n /. &a) %. &b)) in |- *.
    leibniz &e2 in |- *.
    ipso &e1.
  }
  lemma bound
    : ((((&n /. &a) %. &b) * (+ &a)) + (&n %. &a)) < (+ (&a * &b)%n).
  {
    simpl ( _ < _ ) in &bound2.
    match &bound2 with | k ek end.
    lemma small : (&n %. &a) < (+ &k) * (+ &a).
    {
      let proof extension := multiplication.right.order.extensivity &k (+ &a).
      simpl ( _ <= _ ) in &extension.
      match &extension with | same | larger end.
      -
        leibniz <- &same in |- *.
        ipso &bound1.
      -
        ipso (order.strict.transitivity &bound1 &larger).
    }
    leibniz (Nat.multiplication.commutativity &a &b), &product in |- *.
    leibniz <- &ek in |- *.
    leibniz (multiplication.right.distributivity.over.addition
      (+ &a) ((&n /. &a) %. &b) (+ &k)) in |- *.
    ipso (addition.order.strict.monotonicity
      (((&n /. &a) %. &b) * (+ &a)) (&n %. &a) ((+ &k) * (+ &a)) &small).
  }
  match (division.uniqueness &n (&a * &b)%n ((&n /. &a) /. &b)
      ((((&n /. &a) %. &b) * (+ &a)) + (&n %. &a))
      (conjoin &reconstruction, &bound))
    with | quotient _ end.
  ipso (symm &quotient).
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
  let n
    := division.nat.quotient.positivity d g h in |- *.
  let proof n
    := &n.
  extro &n.
  match ((+ d) /. g) with | | q' end.
  - intro n.
    modus ponens n, (Identity.reflexivity 0) |- f.
    ex f quodlibet.
  - intro n.
    quod idem est.
Qed.

(* divide.nat.safe.congruence *)
Theorem congruence
  : forall (d1 : Nat) (g1 : Nat) (h1 : Divides (+ g1) (+ d1))
      (d2 : Nat) (g2 : Nat) (h2 : Divides (+ g2) (+ d2)) .
      (+ d1) /. g1 = (+ d2) /. g2
      -> divide.nat.safe d1 g1 h1 = divide.nat.safe d2 g2 h2.
Proof.
  intros d1 g1 h1 d2 g2 h2 e.
  let proof s1 := divide.nat.safe.specification d1 g1 h1.
  let proof s2 := divide.nat.safe.specification d2 g2 h2.
  leibniz e in s1.
  symm in s2.
  let proof full := Identity.transitivity s1 s2.
  ipso (positive.injectivity full).
Qed.

End safe. (* divide.nat.safe *)

End nat. (* divide.nat *)

End divide. (* divide *)

Module modulo. (* modulo *)

(* modulo.homogeneity *)
Theorem homogeneity
  : forall (n : Nat0) (d : Nat) (k : Nat) .
      (((+ k) * n) %. (k * d)%n) = (+ k) * (n %. d).
Proof.
  intros n d k.

  let proof recon
    := division.dividend.reconstruction n d.
  let proof bound
    := division.remainder.boundedness n d.

  lemma witness
  : (((n /. d) * (+ (k * d)%n)) + ((+ k) * (n %. d)) = (+ k) * n)
  /\ ((+ k) * (n %. d)) < (+ (k * d)%n).
  {
    divide et impera.
    - lemma facto
      : ((&n /. &d) * ((+ &k) * (+ &d))) + ((+ &k) * (&n %. &d)) = (+ &k) * &n.
      {
        leibniz (multiplication.commutativity (n /. d) ((+ k) * (+ d))) in |- *.
        leibniz (multiplication.associativity (+ k) (+ d) (n /. d))     in |- *.
        leibniz (multiplication.commutativity (+ d) (n /. d))           in |- *.
        let proof dist := symm (multiplication
                                  .left
                                  .distributivity.over.addition
                                    (+ k)
                                    ((n /. d) * (+ d))
                                    (n %. d)).
        leibniz dist  in |- *.
        leibniz recon in |- *.
        quod idem est.
      }
      ipso facto.
    - lemma facto
      : ((+ &k) * (&n %. &d)) < (+ &k) * (+ &d).
      {
        ipso (multiplication.left.order.strict.monotonicity k (n %. d) (+ d) bound).
      }
      ipso facto.
  }

  match (division.uniqueness
          ((+ k) * n)
          (k * d)%n
          (n /. d)
          ((+ k) * (n %. d))
          witness)
  with | _ facto end.
  ipso facto.
Qed.

(* modulo.identity *)
Theorem identity : forall (n : Nat0) (d : Nat) . n < + d -> n %. d = n.
Proof.
  intros n d h.
  lemma witness : (0 * (+ &d)) + &n = &n /\ &n < + &d.
  {
    divide et impera.
    - simpl in |- *.
      quod idem est.
    - ipso &h.
  }
  match (division.uniqueness &n &d 0 &n &witness) with | _ facto end.
  ipso facto.
Qed.

Module sum. (* modulo.sum *)

Module left. (* modulo.sum.left *)

(* modulo.sum.left.absorption *)
Theorem absorption
  : forall (a : Nat0) (b : Nat0) (d : Nat) . ((a %. d) + b) %. d = (a + b) %. d.
Proof.
  intros a b d.
  lemma witness
    : ((&a /. &d + (&a %. &d + &b) /. &d) * (+ &d)) + (&a %. &d + &b) %. &d = &a + &b
      /\ (&a %. &d + &b) %. &d < + &d.
  {
    divide et impera.
    - leibniz
        (multiplication.right.distributivity.over.addition
          (+ &d) (&a /. &d) ((&a %. &d + &b) /. &d)),
        (addition.associativity
          ((&a /. &d) * (+ &d)) (((&a %. &d + &b) /. &d) * (+ &d))
          ((&a %. &d + &b) %. &d)),
        (division.dividend.reconstruction (&a %. &d + &b) &d),
        <- (addition.associativity ((&a /. &d) * (+ &d)) (&a %. &d) &b),
        (division.dividend.reconstruction &a &d)
        in |- *.
      quod idem est.
    - ipso (division.remainder.boundedness (&a %. &d + &b) &d).
  }
  match (division.uniqueness
          (&a + &b) &d (&a /. &d + (&a %. &d + &b) /. &d) ((&a %. &d + &b) %. &d)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

End left. (* modulo.sum.left *)

Module right. (* modulo.sum.right *)

(* modulo.sum.right.absorption *)
Theorem absorption
  : forall (a : Nat0) (b : Nat0) (d : Nat) . (a + (b %. d)) %. d = (a + b) %. d.
Proof.
  intros a b d.
  leibniz
    (addition.commutativity &a (&b %. &d)),
    (modulo.sum.left.absorption &b &a &d),
    (addition.commutativity &b &a)
    in |- *.
  quod idem est.
Qed.

End right. (* modulo.sum.right *)

End sum. (* modulo.sum *)

Module product. (* modulo.product *)

Module left. (* modulo.product.left *)

(* modulo.product.left.absorption *)
Theorem absorption
  : forall (a : Nat0) (b : Nat0) (d : Nat) . ((a %. d) * b) %. d = (a * b) %. d.
Proof.
  intros a b d.
  lemma witness
    : ((&a /. &d * &b + (&a %. &d * &b) /. &d) * (+ &d)) + (&a %. &d * &b) %. &d = &a * &b
      /\ (&a %. &d * &b) %. &d < + &d.
  {
    divide et impera.
    - leibniz
        (multiplication.right.distributivity.over.addition
          (+ &d) (&a /. &d * &b) ((&a %. &d * &b) /. &d)),
        (addition.associativity
          ((&a /. &d * &b) * (+ &d)) (((&a %. &d * &b) /. &d) * (+ &d))
          ((&a %. &d * &b) %. &d)),
        (division.dividend.reconstruction (&a %. &d * &b) &d),
        (multiplication.associativity (&a /. &d) &b (+ &d)),
        (multiplication.commutativity &b (+ &d)),
        <- (multiplication.associativity (&a /. &d) (+ &d) &b),
        <- (multiplication.right.distributivity.over.addition
          &b ((&a /. &d) * (+ &d)) (&a %. &d)),
        (division.dividend.reconstruction &a &d)
        in |- *.
      quod idem est.
    - ipso (division.remainder.boundedness (&a %. &d * &b) &d).
  }
  match (division.uniqueness
          (&a * &b) &d (&a /. &d * &b + (&a %. &d * &b) /. &d) ((&a %. &d * &b) %. &d)
          &witness)
  with | _ facto end.
  ipso (symm &facto).
Qed.

End left. (* modulo.product.left *)

Module right. (* modulo.product.right *)

(* modulo.product.right.absorption *)
Theorem absorption
  : forall (a : Nat0) (b : Nat0) (d : Nat) . (a * (b %. d)) %. d = (a * b) %. d.
Proof.
  intros a b d.
  leibniz
    (multiplication.commutativity &a (&b %. &d)),
    (modulo.product.left.absorption &b &a &d),
    (multiplication.commutativity &b &a)
    in |- *.
  quod idem est.
Qed.

End right. (* modulo.product.right *)

End product. (* modulo.product *)

End modulo. (* modulo *)

Local Open Scope jwa_product_scope.

Module euclid. (* euclid *)

(* euclid.well_founded *)
Instance well_founded
  : WellFounded (Induced (<) pi_2) :=
  WellFounded.induced (<) (@Product.second Nat0 Nat0)
    {| accessibility := order.strict.wellfoundedness |}.

Local Open Scope jwa_type_scope.

(* [forall (x : Nat0 * Nat0) .
 * (forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0) -> Nat0]
 *)
(* euclid.step *)
Definition step
  : Descent.Step (Induced (<) pi_2) (fun (_ : Nat0 * Nat0) . Nat0)
  :=
  fun (x : Nat0 * Nat0)
    (recurse : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0) .
    match x with
    (* [b = 0] answers [a].
     * [b = + b'] does not answer with the product [((+ b'), (a %. b'))],
     * it calls [recurse] there with it and answers with the number that comes back.
     * The product is where the next question is, not the answer.
     *)
    | (a, b) =>
        match b with
        | 0 =>
            fun (_ : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y (a, 0) -> Nat0) . a
        | + b' =>
            fun (recurse : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y (a, + b') -> Nat0) .
              (recurse
                ((+ b'), (a %. b'))
                (Induced.introduction (division.remainder.boundedness a b')))
        end
    end recurse.

(* euclid.extensionality *)
Lemma extensionality : Descent.Extensional euclid.step.
Proof.
  (* [x : Nat0 * Nat0]
   * [f : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0]
   * [g : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0]
   * [h : forall (y : Nat0 * Nat0) (r : Induced (<) pi_2 y x) . f y r = g y r]
   * :
   * [|- step x f = step x g]
   *)
  intros x f g h.

  (* [|- step (a, b) f = step (a, b) g] *)
  match x with | a b end.

  match b with | | b' end.

  (* b destructed as 0 : [|- step (a, 0) f = step (a, 0) g] *)
  {
    (* [|- a = a] *)
    simpl in |- *.
    quod idem est.
  }

  (* b destructed as + b' : [|- step (a, + b') f = step (a, + b') g] *)
  {
    (* [|- f ((+ b'), (a %. b')) (Induced.introduction (division.remainder.boundedness a b'))
     *  = g ((+ b'), (a %. b')) (Induced.introduction (division.remainder.boundedness a b'))]
     *)
    simpl euclid.step in |- *.

    (* The context gains [bound := division.remainder.boundedness a b'],
     * of type [(a %. b') < + b']
     * :
     * [|- f ((+ b'), (a %. b')) (Induced.introduction bound)
     *  = g ((+ b'), (a %. b')) (Induced.introduction bound)]
     *)
    let bound
      : (a %. b') < + b'
      := division.remainder.boundedness a b'
      in |- *.

    (* The context gains [y := ((+ b'), (a %. b'))]
     * :
     * [|- f y (Induced.introduction bound)
     *  = g y (Induced.introduction bound)]
     *)
    let y
      : Nat0 * Nat0
      := ((+ b'), (a %. b'))
      in |- *.

    (* The context gains [x := (a, + b')], and [f], [g] and [h] fold to it:
     * [f : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0]
     * [g : forall (y : Nat0 * Nat0) . Induced (<) pi_2 y x -> Nat0]
     * [h : forall (y : Nat0 * Nat0) (r : Induced (<) pi_2 y x) . f y r = g y r]
     *)
    let x := (a, + b') in *.

    (* The context gains [r := Induced.introduction bound],
     * of type [Induced (<) pi_2 y x]
     * :
     * [|- f y r = g y r]
     *)
    let r
      : Induced (<) pi_2 y x
      := Induced.introduction bound
      in |- *.

    (* [H : forall (r : Induced (<) pi_2 y x) . f y r = g y r] *)
    let proof H := h y.

    ipso (modus ponens H, r).
  }
Qed.

Local Close Scope jwa_type_scope.

Module nat. (* euclid.nat *)

(* euclid.nat.well_founded *)
Instance well_founded
  : WellFounded (Induced (<)%n (@Product.second Nat0 Nat)) :=
  WellFounded.induced (<)%n (@Product.second Nat0 Nat)
    Nat_less_than_well_founded.

(* The inner [return] carries the bound rather than an equation, so the
 * branch for a positive remainder has [(+ r) < + q] already in hand.
 *)
(* [forall (p : Product Nat0 Nat) .
 *    (forall (s : Product Nat0 Nat) .
 *       Induced (<)%n (@Product.second Nat0 Nat) s p -> Nat) ->
 *    Nat]
 *)
(* euclid.nat.step *)
Definition step
  : Descent.Step
      (Induced (<)%n (@Product.second Nat0 Nat))
      (fun (_ : Product Nat0 Nat) . Nat)
  :=
  fun (p : Product Nat0 Nat)
    (recurse : forall (s : Product Nat0 Nat) .
                 Induced (<)%n (@Product.second Nat0 Nat) s p -> Nat) .
    match p as t
      return ((forall (s : Product Nat0 Nat) .
                 Induced (<)%n (@Product.second Nat0 Nat) s t -> Nat) -> Nat)
    with
    | (a, q) =>
        fun (descend : forall (s : Product Nat0 Nat) .
                       Induced (<)%n (@Product.second Nat0 Nat) s (a, q) -> Nat) .
          match (a %. q) as m
          return (m < (+ q) -> Nat)
          with
          | 0 => fun (_ : 0 < (+ q)) . q
          | + r =>
              fun (h : (+ r) < (+ q)) .
                descend ((+ q), r)
                  (Induced.introduction
                    (f := @Product.second Nat0 Nat) (y := ((+ q), r)) (x := (a, q))
                    (Biconditional.forward.elimination (positive.order.embedding r q) h))
          end (division.remainder.boundedness a q)
    end recurse.

(* euclid.nat.extensionality *)
Lemma extensionality : Descent.Extensional euclid.nat.step.
Proof.
  intros p f g h.
  match p with | a q end.
  simpl euclid.nat.step in |- *.
  let b := division.remainder.boundedness a q in |- *.
  let proof b := &b.
  extro &b.
  match (a %. q) with
  |
  | r
  end.
  - intros b.
    quod idem est.
  - intros b.
    let s
      : Induced
          (<)%n
          (@Product.second Nat0 Nat)
          ((+ q), r)
          (a, q)
      := Induced.introduction
          (f := @Product.second Nat0 Nat) (y := ((+ q), r)) (x := (a, q))
          (Biconditional.forward.elimination (positive.order.embedding r q) b)
      in |- *.
    let proof H := h ((+ q), r).
    ipso (modus ponens H, s).
Qed.

End nat. (* euclid.nat *)

End euclid. (* euclid *)

Existing Instance euclid.well_founded.

Existing Instance euclid.nat.well_founded.

(* Greatest Common Divisor *)
(* [Nat0 -> Nat0 -> Nat0] *)
Definition gcd :=
  fun (a : Nat0) (b : Nat0) .
    (WellFounded.recursion euclid.step (a, b)).

Local Close Scope jwa_product_scope.

Module divisibility. (* divisibility *)

(* divisibility.reflexivity *)
Theorem reflexivity : forall (n : Nat0) . Divides n n.
Proof.
  intros n.
  simpl Divides in |- *.
  exists (+ Nat.One).
  ipso (multiplication.right.identity n).
Qed.

(* divisibility.transitivity *)
Theorem transitivity
  : forall {l : Nat0} {m : Nat0} {n : Nat0} .
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Divides in |- *.
  exists (k1 * k2).
  leibniz <- (multiplication.associativity l k1 k2) in |- *.
  leibniz -> e1 in |- *.
  ipso e2.
Qed.

(* divisibility.antisymmetry *)
Theorem antisymmetry
  : forall {m : Nat0} {n : Nat0} . Divides m n -> Divides n m -> m = n.
Proof.
  intros m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k e1 end.
  match h2 with | j e2 end.
  match m with | | p end.
  - simpl in e1.
    ipso e1.
  - let proof e1' := Identity.symmetry e1.
    leibniz e1' in e2.
    match k with
    |
    | k'
    end.
    + simpl in e2.
      ex e2 quodlibet.
    + match j with
      |
      | j'
      end.
      * simpl in e2.
        ex e2 quodlibet.
      * simpl in e2.

        let proof e3
          := positive.injectivity e2.
        leibniz (Nat.multiplication.associativity p k' j') in e3.

        let proof c
          := Nat.multiplication.commutativity Nat.One p.
        simpl in c.

        let proof e4
          := Identity.transitivity e3 c.

        let proof e5
          := Nat.multiplication.left.cancellation e4.

        let proof f
          := Nat.multiplication.identity.factorization e5.
        match f with
        | ek ej
        end.

        leibniz ek in e1.
        leibniz (multiplication.right.identity (+ p)) in e1.

        ipso e1.
Qed.

(* divisibility.bottom *)
Theorem bottom : forall (n : Nat0) . Divides (+ Nat.One) n.
Proof.
  intros n.
  simpl Divides in |- *.
  exists n.
  ipso (multiplication.left.identity n).
Qed.

(* divisibility.top *)
Theorem top : forall (n : Nat0) . Divides n 0.
Proof.
  intros n.
  simpl Divides in |- *.
  exists 0.
  leibniz (multiplication.commutativity n 0) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

Module addition. (* divisibility.addition *)

(* divisibility.addition.closure *)
Theorem closure
  : forall {d : Nat0} {m : Nat0} {n : Nat0} .
      Divides d m -> Divides d n -> Divides d (m + n).
Proof.
  intros d m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Divides in |- *.
  exists (k1 + k2).
  leibniz (multiplication.left.distributivity.over.addition d k1 k2) in |- *.
  leibniz e1 in |- *.
  leibniz e2 in |- *.
  quod idem est.
Qed.

(* The quotients are what the subtraction happens on, so the witness is
 * [k2 - k1] and the work is showing that [k1] is not the larger.
 *)
(* divisibility.addition.cancellation *)
Theorem cancellation
  : forall {d : Nat0} {m : Nat0} {n : Nat0} .
      Divides d m -> Divides d (m + n) -> Divides d n.
Proof.
  intros d m n h1 h2.
  simpl Divides in h1, h2.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  match d with
  |
  | c
  end.
  - match (multiplication.annihilation k1) with | z1 z2 end.
    leibniz z1 in e1.
    match (multiplication.annihilation k2) with | w1 w2 end.
    leibniz w1 in e2.
    leibniz <- e1 in e2.
    match (addition.identity n) with | i1 i2 end.
    leibniz i1 in e2.
    leibniz <- e2 in |- *.
    ipso (divisibility.top 0).
  - match (Comparable.order.totality k1 k2) with
    | le
    | ge
    end.
    + simpl Divides in |- *.
      exists (saturating_sub k2 k1).
      let proof s
        := subtraction.saturating.specification &le.
      let proof dist
        := multiplication
            .left
            .distributivity.over.addition
                (+ c) k1 (saturating_sub k2 k1).
      leibniz s, e1, e2 in dist.
      symm in dist.
      ipso (addition.left.cancellation dist).
    + simpl Comparable.LessOrEqual in ge.
      match ge with
      | eq
      | lt
      end.
      * leibniz &eq in e2.
        leibniz &e1 in e2.
        match (addition.identity m) with | i1 i2 end.
        let proof e3
          := Identity.transitivity i2 e2.
        let proof e4
          := addition.left.cancellation e3.
        leibniz <- e4 in |- *.
        ipso (divisibility.top (+ c)).
      * let proof mono
          := multiplication
              .left
              .order.strict.monotonicity c k2 k1 lt.
        leibniz e1, e2 in mono.
        simpl ( _ < _ ) in mono.
        match mono with | j ej end.
        leibniz (addition.associativity m n (+ j)) in ej.
        match (addition.identity m) with | i1 i2 end.
        symm in i2.
        let proof e3
          := Identity.transitivity ej i2.
        let proof e4
          := addition.left.cancellation e3.
        let proof pos
          := addition.right.order.positivity n j.
        leibniz e4 in pos.
        ipso (Falsum.elimination
                (Divides (+ c) n)
                (order.strict.irreflexivity 0 pos)).
Qed.

End addition. (* divisibility.addition *)

Module multiplication. (* divisibility.multiplication *)

(* divisibility.multiplication.closure *)
Theorem closure
  : forall (d : Nat0) (m : Nat0) (n : Nat0) .
      Divides d m -> Divides d (m * n).
Proof.
  intros d m n h.
  simpl Divides in h.
  match h with | k e end.
  simpl Divides in |- *.
  exists (k * n).
  leibniz <- (multiplication.associativity d k n) in |- *.
  leibniz e in |- *.
  quod idem est.
Qed.

End multiplication. (* divisibility.multiplication *)

End divisibility. (* divisibility *)


Module gcd. (* gcd *)

Local Open Scope jwa_product_scope.

(* gcd.zero *)
Theorem zero : forall (a : Nat0) . gcd a 0 = a.
Proof.
  intros a.
  simpl gcd in |- *.
  leibniz (WellFounded.recursion.unfolding euclid.extensionality (a, 0)) in |- *.
  simpl euclid.step in |- *.
  quod idem est.
Qed.

(* gcd.recurrence *)
Theorem recurrence
  : forall (a : Nat0) (q : Nat) . gcd a (+ q) = gcd (+ q) ((a %. q)).
Proof.
  intros a q.
  simpl gcd in |- *.
  leibniz (WellFounded.recursion.unfolding euclid.extensionality (a, + q)) in |- *.
  simpl euclid.step in |- *.
  quod idem est.
Qed.

(* gcd.divisibility *)
Theorem divisibility
  : forall (b : Nat0) (a : Nat0) .
      Divides (gcd a b) a /\ Divides (gcd a b) b.
Proof.
  intros b.
  lemma descent
  : Descent.Step
      (<)
      (fun (c : Nat0) . forall (a : Nat0) . Divides (gcd a c) a /\ Divides (gcd a c) c).
  {
    intros c recurse a.
    match c with
    |
    | q
    end.
    + leibniz (gcd.zero a) in |- *.
      divide et impera.
      * ipso (divisibility.reflexivity a).
      * ipso (divisibility.top a).
    + leibniz (gcd.recurrence a q) in |- *.
      match (recurse
              ((a %. q))
              (division.remainder.boundedness a q) (+ q))
      with
      | d1 d2
      end.
      divide et impera.
      * match (division.specification a q)
        with
        | s1 s2
        end.
        let proof hm
          := divisibility.multiplication.closure
                (gcd (+ q) ((a %. q)))
                (+ q)
                ((a /. q))
                d1.
        leibniz (multiplication.commutativity (+ q) ((a /. q))) in hm.
        let proof ha
          := divisibility.addition.closure hm d2.
        leibniz s1 in ha.
        ipso ha.
      * ipso d1.
  }
  ipso (Accessible.recursion &descent &b (order.strict.wellfoundedness &b)).
Qed.

Module left. (* gcd.left *)

(* gcd.left.divisibility *)
Theorem divisibility
  : forall (a : Nat0) (b : Nat0) . Divides (gcd a b) a.
Proof.
  intros a b.
  match (gcd.divisibility b a) with | h1 h2 end.
  ipso h1.
Qed.

Module distributivity. (* gcd.left.distributivity *)

Module of. (* gcd.left.distributivity.of *)

(* gcd.left.distributivity.of.multiplication *)
Theorem multiplication
  : forall (k : Nat) (b : Nat0) (a : Nat0) .
      (+ k) * gcd a b = gcd ((+ k) * a) ((+ k) * b).
Proof.
  intros k b.
  lemma descent
    : Descent.Step
        (<)
        (fun (c : Nat0) . forall (a : Nat0) . (+ &k) * gcd a c = gcd ((+ &k) * a) ((+ &k) * c)).
  {
    intros c recurse a.
    match c with
    |
    | q
    end.
    + leibniz (gcd.zero a) in |- *.
      lemma facto
      : (+ &k) * &a = gcd ((+ &k) * &a) 0.
      {
        leibniz (gcd.zero ((+ k) * a)) in |- *.
        quod idem est.
      }
      ipso facto.
    + leibniz (gcd.recurrence a q) in |- *.
      lemma facto
      : (+ &k) * gcd (+ &q) (&a %. &q) = gcd ((+ &k) * &a) (+ (&k * &q)%n).
      {
        leibniz (gcd.recurrence ((+ k) * a) (k * q)%n) in |- *.
        leibniz (modulo.homogeneity a q k) in |- *.
        lemma facto
        : (+ &k) * gcd (+ &q) (&a %. &q)
        = gcd ((+ &k) * (+ &q)) ((+ &k) * (&a %. &q)).
        {
          ipso (recurse ((a %. q)) (division.remainder.boundedness a q) (+ q)).
        }
        ipso facto.
      }
      ipso facto.
  }
  ipso (Accessible.recursion &descent &b (order.strict.wellfoundedness &b)).
Qed.

End of. (* gcd.left.distributivity.of *)

End distributivity. (* gcd.left.distributivity *)

End left. (* gcd.left *)

Module right. (* gcd.right *)

(* gcd.right.divisibility *)
Theorem divisibility
  : forall (a : Nat0) (b : Nat0) . Divides (gcd a b) b.
Proof.
  intros a b.
  match (gcd.divisibility b a) with | h1 h2 end.
  ipso h2.
Qed.

End right. (* gcd.right *)

(* gcd.universality *)
Theorem universality
  : forall (b : Nat0) (a : Nat0) (d : Nat0) .
      Divides d a -> Divides d b -> Divides d (gcd a b).
Proof.
  intros b.
  lemma descent
    : Descent.Step
        (<)
        (fun (c : Nat0) . forall (a : Nat0) (d : Nat0) . Divides d a -> Divides d c -> Divides d (gcd a c)).
  {
    intros c recurse a d h1 h2.
    match c with
    |
    | q
    end.
    + leibniz (gcd.zero a) in |- *.
      ipso h1.
    + leibniz (gcd.recurrence a q) in |- *.
      lemma remainder : Divides d (a %. q).
      {
        match (division.specification a q) with | s1 s2 end.
        leibniz (symm s1) in h1.
        let proof hm
          := divisibility.multiplication.closure
                d
                (+ q)
                ((a /. q))
                h2.
        leibniz (multiplication.commutativity (+ q) ((a /. q))) in hm.
        ipso (divisibility.addition.cancellation hm h1).
      }
      let proof below
        := recurse
            ((a %. q))
            (division.remainder.boundedness a q)
            (+ q)
            d
            h2.
      ipso (modus ponens below, remainder).
  }
  ipso (Accessible.recursion &descent &b (order.strict.wellfoundedness &b)).
Qed.

(* gcd.commutativity *)
Theorem commutativity
  : forall (a : Nat0) (b : Nat0) . gcd a b = gcd b a.
Proof.
  intros a b.
  ipso (divisibility.antisymmetry
          (gcd.universality
            a b
            (gcd a b)
            (gcd
              .right.divisibility a b)
            (gcd
              .left.divisibility  a b))
          (gcd.universality
            b a
            (gcd b a)
            (gcd
              .right.divisibility b a)
            (gcd
              .left.divisibility  b a))).
Qed.

Module multiplication. (* gcd.multiplication *)

(* gcd.multiplication.cancellation *)
Theorem cancellation
  : forall (p : Nat0) (q : Nat0) (r : Nat0) .
      Divides p (q * r) -> gcd p q = (+ Nat.One) -> Divides p r.
Proof.
  intros p q r h coprime.
  match r with
  |
  | s
  end.
  - ipso (divisibility.top p).
  - lemma scaled
    : gcd ((+ s) * p) ((+ s) * q) = (+ s).
    {
      let proof dist
        := gcd.left.distributivity.of.multiplication s q p.
      leibniz coprime in dist.
      leibniz (multiplication.right.identity (+ s)) in dist.
      symm in dist.
      ipso dist.
    }
    let proof hp
      := divisibility.multiplication.closure
            p p (+ s)
            (divisibility.reflexivity p).
    leibniz (multiplication.commutativity p (+ s)) in hp.
    leibniz (multiplication.commutativity q (+ s)) in h.
    let proof u
      := gcd.universality
            ((+ s) * q)
            ((+ s) * p)
            p hp h.
    leibniz scaled in u.
    ipso u.
Qed.

End multiplication. (* gcd.multiplication *)

(* [Nat0 -> Nat -> Nat] *)
(* gcd.nat *)
Definition nat :=
  fun (a : Nat0) (q : Nat) .
    (WellFounded.recursion euclid.nat.step (a, q)).

Module nat. (* gcd.nat *)

(* gcd.nat.zero *)
Theorem zero
  : forall (a : Nat0) (q : Nat) . (a %. q) = 0 -> gcd.nat a q = q.
Proof.
  intros a q e.
  simpl gcd.nat in |- *.
  leibniz (WellFounded.recursion.unfolding
             euclid.nat.extensionality (a, q)) in |- *.
  simpl euclid.nat.step in |- *.
  let b := division.remainder.boundedness a q in |- *.
  let proof b := &b.
  extro &b.
  leibniz e in |- *.
  intros b.
  simpl in |- *.
  quod idem est.
Qed.

(* gcd.nat.recurrence *)
Theorem recurrence
  : forall (a : Nat0) (q : Nat) (r : Nat) .
      (a %. q) = + r -> gcd.nat a q = gcd.nat (+ q) r.
Proof.
  intros a q r e.
  simpl gcd.nat in |- *.
  leibniz (WellFounded.recursion.unfolding euclid.nat.extensionality (a, q)) in |- *.
  simpl euclid.nat.step in |- *.
  let b
    := division.remainder.boundedness a q in |- *.
  let proof b
    := &b.
  extro &b.
  leibniz e in |- *.
  intros b.
  simpl in |- *.
  quod idem est.
Qed.

(* gcd.nat.specification *)
Theorem specification
  : forall (q : Nat) (a : Nat0) . gcd a (+ q) = + (gcd.nat a q).
Proof.
  intros q.
  lemma descent
  : Descent.Step
    (<)%n
    (fun (c : Nat) . forall (a : Nat0) . gcd a (+ c) = + (gcd.nat a c)).
  {
    intros c recurse a.
    leibniz (gcd.recurrence a c) in |- *.
    match (a %. c) with
    |
    | r
    end |- e.
    + leibniz (gcd.zero (+ c)) in |- *.
      leibniz (gcd.nat.zero a c e) in |- *.
      quod idem est.
    + leibniz (gcd.nat.recurrence a c r e) in |- *.
      let proof b
        := division.remainder.boundedness a c.
      leibniz e in b.
      modus aequans
        (positive.order.embedding r c),
        b
      |- lt.
      ipso (recurse r lt (+ c)).
  }
  ipso (Accessible.recursion &descent &q (accessibility &q)).
Qed.

Module left. (* gcd.nat.left *)

(* gcd.nat.left.divisibility *)
Theorem divisibility
  : forall (a : Nat0) (q : Nat) . Divides (+ (gcd.nat a q)) a.
Proof.
  intros a q.
  let proof h := gcd.left.divisibility a (+ q).
  leibniz (gcd.nat.specification q a) in h.
  ipso h.
Qed.

Module distributivity. (* gcd.nat.left.distributivity *)

Module of. (* gcd.nat.left.distributivity.of *)

(* gcd.nat.left.distributivity.of.multiplication *)
Theorem multiplication
  : forall (k : Nat) (q : Nat) (a : Nat0) .
      (k * gcd.nat a q)%n = gcd.nat ((+ k) * a) (k * q)%n.
Proof.
  intros k q a.
  let proof h
    := gcd.left.distributivity.of.multiplication k (+ q) a.
  leibniz (gcd.nat.specification q a) in h.
  let proof h
    : (+ k) * (+ (gcd.nat a q)) = gcd ((+ k) * a) (+ (k * q)%n)
    := &h.
  leibniz (gcd.nat.specification (k * q)%n ((+ k) * a)) in h.
  let proof h
    : (+ (k * gcd.nat a q)%n) = (+ (gcd.nat ((+ k) * a) (k * q)%n))
    := &h.
  ipso (positive.injectivity h).
Qed.

End of. (* gcd.nat.left.distributivity.of *)

End distributivity. (* gcd.nat.left.distributivity *)

End left. (* gcd.nat.left *)

Module right. (* gcd.nat.right *)

(* gcd.nat.right.divisibility *)
Theorem divisibility
  : forall (a : Nat0) (q : Nat) . Divides (+ (gcd.nat a q)) (+ q).
Proof.
  intros a q.
  let proof h := gcd.right.divisibility a (+ q).
  leibniz (gcd.nat.specification q a) in h.
  ipso h.
Qed.

(* gcd.nat.right.annihilation *)
Theorem annihilation
  : forall (a : Nat0) . gcd.nat a Nat.One = Nat.One.
Proof.
  intro a.
  let proof down := gcd.nat.right.divisibility a Nat.One.
  let proof up := divisibility.bottom (+ (gcd.nat a Nat.One)).
  let proof e := divisibility.antisymmetry down up.
  ipso (positive.injectivity e).
Qed.

End right. (* gcd.nat.right *)

(* gcd.nat.divisibility *)
Theorem divisibility
  : forall (a : Nat0) (q : Nat) .
      Divides (+ (gcd.nat a q)) a /\ Divides (+ (gcd.nat a q)) (+ q).
Proof.
  intros a q.
  divide et impera.
  - ipso (gcd.nat.left.divisibility  a q).
  - ipso (gcd.nat.right.divisibility a q).
Qed.

(* gcd.nat.exhaustiveness *)
Theorem exhaustiveness
  : forall (a : Nat0) (q : Nat) .
      gcd.nat
        (a /. (gcd.nat a q))
        (divide.nat.safe
          q (gcd.nat a q)
          (gcd.nat.right.divisibility a q))
      = Nat.One.
Proof.
  intros a q.
  lemma top
  : (+ (gcd.nat a q)) * (a /. (gcd.nat a q)) = a.
  {
    let proof e
      := division.exactness
            a (gcd.nat a q)
            (gcd.nat.left.divisibility a q).
    leibniz (multiplication.commutativity
                (+ (gcd.nat a q))
                (a /. (gcd.nat a q))) in |- *.
    ipso e.
  }
  lemma bottom
  : (gcd.nat a q * divide.nat.safe q (gcd.nat a q) (gcd.nat.right.divisibility a q))%n
  = q.
  {
    let proof s
      := divide.nat.safe.specification
            q (gcd.nat a q)
            (gcd.nat.right.divisibility a q).
    let proof e
      := division.exactness
            (+ q) (gcd.nat a q)
            (gcd.nat.right.divisibility a q).
    leibniz (symm s) in e.
    let proof e
      := positive.injectivity e.
    leibniz
      (Nat.multiplication.commutativity
          (gcd.nat a q)
          (divide.nat.safe q (gcd.nat a q) (gcd.nat.right.divisibility a q))) in |- *.
    ipso e.
  }
  let proof dist
    := gcd.nat.left.distributivity.of.multiplication
          (gcd.nat a q)
          (divide.nat.safe q (gcd.nat a q) (gcd.nat.right.divisibility a q))
          (a /. (gcd.nat a q)).
  leibniz top, bottom    in dist.
  match (Nat
    .multiplication
    .identity (gcd.nat a q))
  with
  | _ unit
  end.
  let proof chain := trans dist, (symm unit).
  match (Nat
    .multiplication.cancellation
        (gcd.nat a q)
        (gcd.nat
            (a /. (gcd.nat a q))
            (divide.nat.safe
                q (gcd.nat a q)
                (gcd.nat.right.divisibility a q)))
        Nat.One)
  with
  | cancel _
  end.
  ipso (cancel chain).
Qed.

End nat. (* gcd.nat *)

Local Close Scope jwa_product_scope.

End gcd. (* gcd *)


Module parity. (* parity *)

(* parity.totality *)
Theorem totality : forall (n : Nat0) . Even n \/ Odd n.
Proof.
  intros n.
  match n with | | p end.
  - lemma side : Even 0.
    {
      simpl Even, Divides in |- *.
      exists 0.
      simpl in |- *.
      quod idem est.
    }
    ipso (disjoin &side, _).
  - match p with | | p' by IH end per Nat.induction.
    + lemma side : Odd (+ Nat.One).
      {
        simpl Odd in |- *.
        exists 0.
        simpl in |- *.
        quod idem est.
      }
      ipso (disjoin _, &side).
    + match IH with | even | odd end.
      * lemma side : Odd (+ Nat.Successor &p').
        {
          simpl Even, Divides in even.
          match even with | k e end.
          simpl Odd in |- *.
          exists k.
          leibniz e in |- *.
          simpl in |- *.
          quod idem est.
        }
        ipso (disjoin _, &side).
      * lemma side : Even (+ Nat.Successor &p').
        {
          simpl Odd in odd.
          match odd with | k e end.
          simpl Even in |- *.
          simpl Divides in |- *.
          exists ((+ Nat.One) + k).
          leibniz
            (multiplication.left.distributivity.over.addition
                (+ (Nat.Successor Nat.One))
                (+ Nat.One)
                k) in |- *.
          lemma facto
          : ((+ Nat.One) + (+ Nat.One)) + ((+ (Nat.Successor Nat.One)) * &k)
          = (+ (Nat.Successor &p')).
          {
            leibniz (addition.associativity
                        (+ Nat.One)
                        (+ Nat.One)
                        ((+ (Nat.Successor Nat.One)) * k)) in |- *.
            leibniz e in |- *.
            simpl in |- *.
            quod idem est.
          }
          ipso facto.
        }
        ipso (disjoin &side, _).
Qed.

Module even. (* parity.even *)

Module addition. (* parity.even.addition *)

(* parity.even.addition.closure *)
Theorem closure
  : forall {m : Nat0} {n : Nat0} . Even m -> Even n -> Even (m + n).
Proof.
  intros m n h1 h2.
  simpl Even in h1, h2 |- *.
  ipso (divisibility.addition.closure h1 h2).
Qed.

End addition. (* parity.even.addition *)

End even. (* parity.even *)

Module odd. (* parity.odd *)

Module addition. (* parity.odd.addition *)

(* parity.odd.addition.evenness *)
Theorem evenness
  : forall {m : Nat0} {n : Nat0} . Odd m -> Odd n -> Even (m + n).
Proof.
  intros m n h1 h2.
  simpl Odd in h1, h2.
  simpl Even in |- *.
  match h1 with | k1 e1 end.
  match h2 with | k2 e2 end.
  simpl Divides in |- *.
  exists ((+ Nat.One) + (k1 + k2)).
  symm in e1, e2.
  leibniz e1, e2 in |- *.
  leibniz (multiplication.left.distributivity.over.addition
              (+ (Nat.Successor Nat.One))
              (+ Nat.One)
              (k1 + k2)) in |- *.
  leibniz (multiplication.left.distributivity.over.addition
              (+ (Nat.Successor Nat.One))
              k1
              k2) in |- *.
  lemma facto
  : ((+ Nat.One) + (+ Nat.One)) + (((+ (Nat.Successor Nat.One)) * &k1) + ((+ (Nat.Successor Nat.One)) * &k2))
  = ((+ Nat.One) + ((+ (Nat.Successor Nat.One)) * &k1)) + ((+ Nat.One) + ((+ (Nat.Successor Nat.One)) * &k2)).
  {
    leibniz (addition.interchange
                (+ Nat.One) ((+ (Nat.Successor Nat.One)) * k1)
                (+ Nat.One) ((+ (Nat.Successor Nat.One)) * k2)) in |- *.
    quod idem est.
  }
  ipso facto.
Qed.

End addition. (* parity.odd.addition *)

End odd. (* parity.odd *)

End parity. (* parity *)

Module narrowing. (* narrowing *)

Module nat. (* narrowing.nat *)

(* narrowing.nat.retraction *)
Theorem retraction
  : forall (p : Nat) . to_nat (+ p) = Some p.
Proof.
  intro p.
  simpl to_nat in |- *.
  quod idem est.
Qed.

(* narrowing.nat.specification *)
Theorem specification
  : forall (n : Nat0) (p : Nat) . to_nat n = Some p <-> n = + p.
Proof.
  intros n p.
  divide et impera.
  - intro e.
    match n with | Zero | Positive q end.
    + simpl to_nat in e.
      ex e quodlibet.
    + simpl to_nat in e.
      let proof f := Option.some.injectivity e.
      leibniz f in |- *.
      quod idem est.
  - intro e.
    leibniz e in |- *.
    ipso (narrowing.nat.retraction p).
Qed.

(* narrowing.nat.failure *)
Theorem failure
  : forall (n : Nat0) . to_nat n = None <-> n = 0.
Proof.
  intro n.
  divide et impera.
  - intro e.
    match n with | Zero | Positive q end.
    + quod idem est.
    + simpl to_nat in e.
      ex e quodlibet.
  - intro e.
    leibniz e in |- *.
    simpl to_nat in |- *.
    quod idem est.
Qed.

End nat. (* narrowing.nat *)

End narrowing. (* narrowing *)

End Nat0. (* Nat0 *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Nat0], not [Nat0.T]. [Zero] and [Positive] name ctors of
 * [Integer] as well, so both types write theirs with the prefix.
 *)
Abbreviation Nat0 := Nat0.T.

(* Makes the notations declared in [Module Nat0] usable in every file
 * that imports this one, as [(m + n)%n0] or under an opened
 * [jwa_nat0_scope]. Only the notations are exported: [add] and the
 * laws still need the [Nat0.] prefix, and the local aliases [0] and
 * [+ p] stay inside the module.
 *)
Export (notations) Nat0.

(* A number of the type is written in decimal or hexadecimal under its scope,
 * [3%n0] or [0x1F%n0], and a closed one prints in decimal. One of 5000 or
 * more stays the call [Nat0.from_numeral] on its digits, not 5000 ctors,
 * until something computes it.
 *)
Number Notation Nat0.T Nat0.from_numeral Nat0.to_numeral (abstract after 5000)
  : jwa_nat0_scope.

(* Where a [Nat0] is expected, a literal or a notation reads in this scope
 * without its [%n0].
 *)
Bind Scope jwa_nat0_scope with Nat0.T.

(* A [Nat] stands wherever a [Nat0] is expected, read as its
 * [Positive], and the conversion is printed where it happened.
 *)
Coercion Nat0.Positive : Nat >-> Nat0.
Add Printing Coercion Nat0.Positive.

(* Declared inside [Module Nat0], whose proofs use it; an instance
 * declared there is dropped at the module's [End], so it is announced again
 * here.
 *)
Existing Instance Nat0.comparable.

Instance Nat0_less_than_well_founded
  : WellFounded (<)%n0 :=
  {| accessibility := Nat0.order.strict.wellfoundedness |}.

Instance Nat0_add_monoid
  : Monoid Nat0.add Nat0.Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := Nat0.addition.associativity |}
  ; Monoid.identity := Nat0.addition.identity
  |}.

Instance Nat0_add_cancellative
  : Cancellative Nat0.add := {|
    Cancellative.cancellation := Nat0.addition.cancellation
  |}.

Instance Nat0_mul_monoid
  : Monoid Nat0.mul Nat.One := {|
    Monoid.semigroup := {|
      Semigroup.associativity := Nat0.multiplication.associativity |}
  ; Monoid.identity := Nat0.multiplication.identity |}.

Instance Nat0_add_commutative
  : Commutative Nat0.add := {|
      Commutative.commutativity := Nat0.addition.commutativity
  |}.

Instance Nat0_add_abelian_monoid
  : AbelianMonoid Nat0.add Nat0.Zero :=
  {| AbelianMonoid.monoid      := Nat0_add_monoid
   ; AbelianMonoid.commutative := Nat0_add_commutative |}.

Instance Nat0_mul_commutative
  : Commutative Nat0.mul := {|
    Commutative.commutativity := Nat0.multiplication.commutativity
  |}.

Instance Nat0_min_semigroup
  : Semigroup Nat0.min :=
  {| Semigroup.associativity := Comparable.minimum.associativity |}.

Instance Nat0_max_monoid
  : Monoid Nat0.max Nat0.Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.maximum.associativity |}
   ; Monoid.identity := Nat0.maximum.identity |}.

Instance Nat0_min_commutative
  : Commutative Nat0.min :=
  {| Commutative.commutativity := Comparable.minimum.commutativity |}.

Instance Nat0_max_commutative
  : Commutative Nat0.max :=
  {| Commutative.commutativity := Comparable.maximum.commutativity |}.

Instance Nat0_semiring
  : Semiring Nat0.add Nat0.Zero Nat0.mul
      Nat.One :=
  {| Semiring.abelian_monoid := Nat0_add_abelian_monoid
   ; Semiring.monoid         := Nat0_mul_monoid
   ; Semiring.distributivity := Nat0.multiplication.distributivity.over.addition
   ; Semiring.annihilation   := Nat0.multiplication.annihilation |}.

Instance Nat0_divides_partial_order
  : PartialOrder Nat0.Divides :=
  {| PartialOrder.reflexivity :=
       {| Reflexive.reflexivity := Nat0.divisibility.reflexivity |}
   ; PartialOrder.antisymmetry :=
       {| Antisymmetric.antisymmetry := @Nat0.divisibility.antisymmetry |}
   ; PartialOrder.transitivity :=
       {| Transitive.transitivity := @Nat0.divisibility.transitivity |} |}.
