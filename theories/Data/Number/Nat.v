(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Option.
From jwa Require Import Relation.Accessible.
From jwa Require Import Relation.WellFounded.
From jwa Require Import Tactics.Modus.

(* A module may carry the type's name; its members read [Nat.add]. The type
 * and its ctors are declared inside it: a ctor at the top level is rebound
 * by any later file declaring the same name, silently and with no warning.
 *)
Module Nat. (* Nat *)

(* Zero is not a [Nat]; [One] is the smallest.
 * [Data.Number.NatWithZero] is the type that has it.
 *)
Inductive T : Type :=
  | One       : T
  | Successor : T -> T.

(* The carrier is named [T] so that the type itself reads [Nat] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Nat].
 *)
Abbreviation Nat := T.

Definition induction
  : forall (P : Nat -> Prop) .
      P One ->
      (forall (n : Nat) . P n -> P (Successor n)) ->
      forall (n : Nat) . P n
  := fun (P : Nat -> Prop)
         (base : P One)
         (step : forall (n : Nat) . P n -> P (Successor n)) .
       fix go (n : Nat) : P n :=
         match n with
         | One          => base
         | Successor n' => step n' (go n')
         end.

(* Short spellings for this module only: [Local] keeps them out of the
 * [Export (notations) Nat] after [End Nat].
 *)
Local Notation "1" := One (only parsing).
Local Abbreviation S := Successor (only parsing).

(* Every operation stands above the topic modules, so that each of them may
 * use any of them: a module cannot be reopened, so a definition placed
 * inside one topic would be out of reach of the next.
 *)

(* [Nat -> Nat -> Nat] *)
Fixpoint add (m : Nat) (n : Nat) : Nat :=
  match m with
  | 1    => S n
  | S m' => S (add m' n)
  end.

(* [Nat -> Nat -> Nat] *)
Fixpoint mul (m : Nat) (n : Nat) : Nat :=
  match m with
  | 1    => n
  | S m' => add n (mul m' n)
  end.

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Nat] a client writes [(m + n)%nat]. [only parsing]
 * keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_nat_scope.
Notation "m * n" := (mul m n) (only parsing)
  : jwa_nat_scope.

Local Open Scope jwa_nat_scope.

(* [Nat -> Nat] *)
Definition inc := fun (n : Nat) . S n.

Notation "++ n" := (inc n) (only parsing)
  : jwa_nat_scope.

(* [Nat -> Nat -> Prop] *)
Definition LessThan := fun (m : Nat) (n : Nat) . exists (k : Nat) . m + k = n.

(* [Nat -> Nat -> Prop] *)
Definition LessOrEqual := fun (m : Nat) (n : Nat) . m = n \/ LessThan m n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_nat_scope.
Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_nat_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_nat_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_nat_scope.

(* [Nat -> Nat -> Nat] *)
Fixpoint power (m : Nat) (n : Nat) : Nat :=
  match n with
  | 1    => m
  | S n' => m * power m n'
  end.

(* [Nat -> Nat -> Comparison] *)
Fixpoint compare (m : Nat) (n : Nat) : Comparison :=
  match m, n with
  | 1, 1       => Comparison.Eq
  | 1, S _     => Comparison.Lt
  | S _, 1     => Comparison.Gt
  | S m', S n' => compare m' n'
  end.

(* [Nat -> Nat -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Nat -> Nat -> Nat] *)
Abbreviation min := (Comparable.min compare).

(* [Nat -> Nat -> Nat] *)
Abbreviation max := (Comparable.max compare).

(* [Nat -> Nat -> Option Nat] *)
Fixpoint sub (m : Nat) (n : Nat) : Option Nat :=
  match m with
  | 1 => None
  | S m' =>
      match n with
      | 1    => Some m'
      | S n' => sub m' n'
      end
  end.

(* [Nat -> Nat -> Nat] *)
Definition saturating_sub := fun (m : Nat) (n : Nat) .
  match sub m n with
  | Some k => k
  | None   => 1
  end.

Module successor. (* successor *)

(* successor.injectivity *)
Lemma injectivity
  : forall {m : Nat} {n : Nat} . S m = S n -> m = n.
Proof.
  intros m n e.
  pose (f := (fun (x : Nat) . match x with | 1 => m | S y => y end)).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

Module order. (* successor.order *)

(* "Strict" names the order preserved, not a direction: a strictly monotone
 * function carries [<] to [<] (equality excluded), a monotone one [<=] to
 * [<=]. The reversed [>] is [<] read from the other side and needs no law
 * of its own.
 *)
(* successor.order.monotonicity *)
Theorem monotonicity
  : forall {m : Nat} {n : Nat} .
      m < n -> S m < S n.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  unfold LessThan in |- *.
  apply (Exists_introduction k).
  simpl in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

Module monotonicity. (* successor.order.monotonicity *)

(* successor.order.monotonicity.inversion *)
Lemma inversion
  : forall {m : Nat} {n : Nat} . S m < S n -> m < n.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  simpl in e.
  pose proof (successor.injectivity e)
          as e'.
  unfold LessThan in |- *.
  exact (Exists_introduction k e').
Qed.

End monotonicity. (* successor.order.monotonicity *)

End order. (* successor.order *)

End successor. (* successor *)

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat.induction.
  -
    simpl in |- *.
    reflexivity.
  -
    simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* addition.commutativity *)
Theorem commutativity : forall (m : Nat) (n : Nat) . m + n = n + m.
Proof.
  intros m n.
  induction m as [| m' IH]
      using Nat.induction;
      simpl in |- *.
  -
    induction n as [| n' IH2]
        using Nat.induction;
        simpl in |- *.
    +
      reflexivity.
    +
      pose proof (Identity.symmetry IH2)
              as IH2'.
      rewrite IH2'
              in |- *.
      reflexivity.
  -
    rewrite IH in |- *.
    clear IH.
    induction n as [| n' IH2]
        using Nat.induction;
        simpl in |- *.
    +
      reflexivity.
    +
      symmetry in IH2.
      rewrite IH2 in |- *.
      reflexivity.
Qed.

Module identity. (* addition.identity *)

(* addition.identity.absence *)
Theorem absence : forall (k : Nat) (n : Nat) . ~ (k + n = n).
Proof.
  intros k n.
  induction n as [| n' IH] using Nat.induction.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition.commutativity k 1)
            in e.
    simpl in e.
    discriminate e.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition.commutativity k (S n'))
            in e.
    simpl in e.
    pose proof (successor.injectivity e)
            as e'.
    rewrite (addition.commutativity n' k)
            in e'.
    unfold Negation in IH.
    modus ponens IH, e'.
Qed.

End identity. (* addition.identity *)

Module left. (* addition.left *)

(* addition.left.cancellation *)
Theorem cancellation
  : forall {m : Nat} {n : Nat} {k : Nat} . m + n = m + k -> n = k.
Proof.
  intros m n k.
  induction m as [| m' IH] using Nat.induction.
  - simpl in |- *.
    intro e.
    exact (successor.injectivity e).
  - simpl in |- *.
    intro e.
    pose proof (successor.injectivity e)
            as e'.
    modus ponens IH, e'.
Qed.

(* addition.left.commutativity *)
Lemma commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . l + (m + n) = m + (l + n).
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
  : forall {m : Nat} {n : Nat} {k : Nat} . m + n = k + n -> m = k.
Proof.
  intros m n k e.
  rewrite (addition.commutativity k n) in e.
  rewrite (addition.commutativity m n) in e.
  exact (addition.left.cancellation e).
Qed.

(* addition.right.commutativity *)
Lemma commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l + m) + n = (l + n) + m.
Proof.
  intros l m n.
  rewrite (addition.associativity l m n) in |- *.
  rewrite (addition.associativity l n m) in |- *.
  rewrite (addition.commutativity m n)   in |- *.
  reflexivity.
Qed.

End right. (* addition.right *)

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (@addition.left.cancellation  m n k).
  - exact (@addition.right.cancellation m n k).
Qed.

Module order. (* addition.order *)

(* addition.order.extensivity *)
Theorem extensivity : forall (m : Nat) (k : Nat) . m < m + k.
Proof.
  intros m k.
  unfold LessThan in |- *.
  apply (Exists_introduction k).
  reflexivity.
Qed.

(* addition.order.monotonicity *)
Theorem monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition.associativity k m d)
          in |- *.
  rewrite e
          in |- *.
  reflexivity.
Qed.

End order. (* addition.order *)

End addition. (* addition *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity : forall (n : Nat) . ~ (n < n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  rewrite (addition.commutativity n k)
          in e.
  pose proof (addition.identity.absence k n)
          as i.
  unfold Negation in i.
  modus ponens i, e as f.
  contradiction f.
Qed.

(* order.strict.transitivity *)
Theorem transitivity
  : forall {l : Nat} {m : Nat} {n : Nat} .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (k1 + k2)).
  pose proof (Identity.symmetry (addition.associativity l k1 k2))
          as a.
  rewrite a  in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

(* Trichotomy, "cut in three": for any [m] and [n], exactly one of
 * [m < n], [m = n], [n < m] holds. This theorem is the "at
 * least one" half; "at most one" is [order.strict.irreflexivity] with
 * [Comparable.order.strict.asymmetry].
 *)
(* order.strict.trichotomy *)
Theorem trichotomy
  : forall (m : Nat) (n : Nat) . (m < n) \/ (m = n) \/ (n < m).
Proof.
  intro m.
  induction m as [| m' IH]
      using Nat.induction;
  intro n; destruct n as [| n'].
  -
    pose proof (Identity.reflexivity 1)
            as id.
    exact (Disjunction.R (Disjunction.L id)).
  -
    apply Disjunction.L.
    unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  -
    apply Disjunction.R.
    apply Disjunction.R.
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    simpl in |- *.
    reflexivity.
  -
    pose proof (IH n') as t.
    destruct t as [lt | rest].
    +
      apply Disjunction.L.
      exact (successor.order.monotonicity lt).
    +
      destruct rest as [eq | gt].
      *
        apply Disjunction.R.
        apply Disjunction.L.
        rewrite eq in |- *.
        reflexivity.
      *
        apply Disjunction.R.
        apply Disjunction.R.
        exact (successor.order.monotonicity gt).
Qed.

(* Descending from [n] cannot go on for ever, since [One] has nothing below
 * it and each step down lands on a smaller [Nat].
 *)
(* order.strict.wellfoundedness *)
Theorem wellfoundedness : forall (n : Nat) . Accessible LessThan n.
Proof.
  intros n.
  induction n as [| n' IH] using Nat.induction.
  - apply Accessible_introduction.
    intros y h.
    destruct h as [k e].
    destruct y as [| y'].
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
  - apply Accessible_introduction.
    intros y h.
    destruct h as [k e].
    rewrite (addition.commutativity y k) in e.
    destruct k as [| k'].
    + simpl in e.
      pose proof (successor.injectivity e) as e'.
      rewrite e' in |- *.
      exact IH.
    + simpl in e.
      pose proof (successor.injectivity e) as e'.
      apply (Accessible.descend IH).
      apply (Exists_introduction k').
      rewrite (addition.commutativity y k') in |- *.
      exact e'.
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity : forall (m : Nat) (n : Nat) . m * n = n * m.
Proof.
  intros m n.
  induction m as [| m' IH]
      using Nat.induction;
      simpl in |- *.
  -
    induction n as [| n' IH2]
        using Nat.induction;
        simpl in |- *.
    +
      reflexivity.
    +
      pose proof (Identity.symmetry IH2)
              as IH2'.
      rewrite IH2'
              in |- *.
      reflexivity.
  -
    rewrite IH in |- *.
    clear IH.
    induction n as [| n' IH2]
        using Nat.induction;
        simpl in |- *.
    +
      reflexivity.
    +
      symmetry in IH2.
      rewrite IH2
           in |- *.
      rewrite (addition.left.commutativity n' m' (n' * m'))
           in |- *.
      reflexivity.
Qed.

Module left. (* multiplication.left *)

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (l : Nat) (m : Nat) (n : Nat) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat.induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (addition.associativity m n ((l' * m) + (l' * n))) in |- *.
    rewrite (addition.left.commutativity n (l' * m) (l' * n))  in |- *.
    rewrite (addition.associativity m (l' * m) (n + (l' * n))) in |- *.
    reflexivity.
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

(* multiplication.left.commutativity *)
Lemma commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . l * (m * n) = m * (l * n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat.induction; simpl in |- *.
  - reflexivity.
  - rewrite IH in |- *.
    rewrite (multiplication.left.distributivity.over.addition m n (l' * n)) in |- *.
    reflexivity.
Qed.

Module order. (* multiplication.left.order *)

(* multiplication.left.order.monotonicity *)
Theorem monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat) .
      m < n -> k * m < k * n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (k * d)).
  pose proof (Identity.symmetry
                (multiplication.left.distributivity.over.addition k m d))
          as dist.
  rewrite dist in |- *.
  rewrite e    in |- *.
  reflexivity.
Qed.

End order. (* multiplication.left.order *)

(* multiplication.left.cancellation *)
Theorem cancellation
  : forall {m : Nat} {n : Nat} {k : Nat} . m * n = m * k -> n = k.
Proof.
  intros m n k e.
  pose proof (order.strict.trichotomy n k) as t.
  destruct t as [lt | rest].
  - pose proof (multiplication.left.order.monotonicity m n k lt)
            as lt'.
    rewrite e
            in lt'.
    pose proof (order.strict.irreflexivity (m * k))
            as i.
    unfold Negation in i.
    modus ponens i, lt' as f.
    contradiction f.
  - destruct rest as [eq | gt].
    + exact eq.
    + pose proof (multiplication.left.order.monotonicity m k n gt)
              as gt'.
      rewrite e
              in gt'.
      pose proof (order.strict.irreflexivity (m * k))
              as i.
      unfold Negation in i.
      modus ponens i, gt' as f.
      contradiction f.
Qed.

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (l : Nat) (m : Nat) (n : Nat) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  rewrite (multiplication.commutativity (m + n) l)                 in |- *.
  rewrite (multiplication.left.distributivity.over.addition l m n) in |- *.
  rewrite (multiplication.commutativity l m)                       in |- *.
  rewrite (multiplication.commutativity l n)                       in |- *.
  reflexivity.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

(* multiplication.right.cancellation *)
Theorem cancellation
  : forall {m : Nat} {n : Nat} {k : Nat} . m * n = k * n -> m = k.
Proof.
  intros m n k e.
  rewrite (multiplication.commutativity m n) in e.
  rewrite (multiplication.commutativity k n) in e.
  exact (multiplication.left.cancellation e).
Qed.

(* multiplication.right.commutativity *)
Lemma commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l * m) * n = (l * n) * m.
Proof.
  intros l m n.
  rewrite (multiplication.commutativity (l * m) n)  in |- *.
  rewrite (multiplication.commutativity (l * n) m)  in |- *.
  rewrite (multiplication.left.commutativity n l m) in |- *.
  rewrite (multiplication.left.commutativity m l n) in |- *.
  rewrite (multiplication.commutativity n m)        in |- *.
  reflexivity.
Qed.

End right. (* multiplication.right *)

(* multiplication.associativity *)
Theorem associativity
  : forall (l : Nat) (m : Nat) (n : Nat) .
    (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat.induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite (multiplication.right.distributivity.over.addition n m (l' * m))
            in |- *.
    rewrite IH
            in |- *.
    reflexivity.
Qed.

(* multiplication.identity *)
Theorem identity
  : forall (n : Nat) . (1 * n = n) /\ (n * 1 = n).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (multiplication.commutativity n 1) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Module identity. (* multiplication.identity *)

(* multiplication.identity.factorization *)
Theorem factorization
  : forall {k : Nat} {j : Nat} . k * j = 1 -> k = 1 /\ j = 1.
Proof.
  intros k j e.
  destruct k as [| k']; simpl in e.
  -
    split.
    + reflexivity.
    + exact e.
  -
    destruct j as [| j'].
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
Qed.

End identity. (* multiplication.identity *)

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (a : Nat) (b : Nat) (c : Nat) (d : Nat) .
      (a + b) * (c + d) = ((a * c) + (a * d)) + ((b * c) + (b * d)).
Proof.
  intros a b c d.
  rewrite (multiplication.right.distributivity.over.addition (c + d) a b) in |- *.
  rewrite (multiplication.left.distributivity.over.addition a c d)        in |- *.
  rewrite (multiplication.left.distributivity.over.addition b c d)        in |- *.
  reflexivity.
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

(* multiplication.cancellation *)
Theorem cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) .
      (m * n = m * k -> n = k)
    /\ (m * n = k * n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (@multiplication.left.cancellation  m n k).
  - exact (@multiplication.right.cancellation m n k).
Qed.

End multiplication. (* multiplication *)

Module power. (* power *)

(* power.identity *)
Lemma identity : forall (m : Nat) . power m 1 = m.
Proof.
  intros m. simpl in |- *. reflexivity.
Qed.

(* power.annihilation *)
Lemma annihilation : forall (n : Nat) . power 1 n = 1.
Proof.
  intros n.
  induction n as [| n' IH] using Nat.induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Module exponent. (* power.exponent *)

(* power.exponent.addition *)
Theorem addition
  : forall (m : Nat) (a : Nat) (b : Nat) .
      power m a * power m b = power m (a + b).
Proof.
  intros m a b.
  induction a as [| a' IH]
      using Nat.induction;
      simpl in |- *.
  -
    reflexivity.
  -
    rewrite (multiplication.associativity m (power m a') (power m b)) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* power.exponent.multiplication *)
Theorem multiplication
  : forall (m : Nat) (a : Nat) (b : Nat) .
      power (power m a) b = power m (a * b).
Proof.
  intros m a b.
  induction b as [| b' IH] using Nat.induction.
  -
    rewrite -> (multiplication.commutativity a 1)
            in |- *.
    simpl   in |- *.
    reflexivity.
  -
    rewrite -> (multiplication.commutativity a (S b'))
            in |- *.
    simpl   in |- *.
    rewrite -> (multiplication.commutativity b' a)
            in |- *.
    rewrite <- (power.exponent.addition m a (a * b'))
            in |- *.
    rewrite -> IH
            in |- *.
    reflexivity.
Qed.

End exponent. (* power.exponent *)

Module distributivity. (* power.distributivity *)

Module over. (* power.distributivity.over *)

(* power.distributivity.over.multiplication *)
Theorem multiplication
  : forall (m : Nat) (n : Nat) (a : Nat) .
      power (m * n) a = power m a * power n a.
Proof.
  intros m n a.
  induction a as [| a' IH] using Nat.induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (multiplication.associativity m n (power m a' * power n a'))    in |- *.
    rewrite (multiplication.left.commutativity n (power m a') (power n a')) in |- *.
    rewrite (multiplication.associativity m (power m a') (n * power n a'))  in |- *.
    reflexivity.
Qed.

End over. (* power.distributivity.over *)

End distributivity. (* power.distributivity *)

End power. (* power *)

Module comparison. (* comparison *)

Module strict. (* comparison.strict *)

Module forward. (* comparison.strict.forward *)

(* comparison.strict.forward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} . compare m n = Comparison.Lt -> m < n.
Proof.
  intros m.
  induction m as [| m' IH]
      using Nat.induction;
      intro n;
  destruct n as [| n'];
      simpl in |- *;
      intro e.
  -
    discriminate e.
  -
    unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  -
    discriminate e.
  -
    exact (successor.order.monotonicity (IH n' e)).
Qed.

End forward. (* comparison.strict.forward *)

Module backward. (* comparison.strict.backward *)

(* comparison.strict.backward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} . m < n -> compare m n = Comparison.Lt.
Proof.
  intros m.
  induction m as [| m' IH]
      using Nat.induction;
      intro n;
  destruct n as [| n'];
      intro h;
      simpl in |- *.
  +
    pose proof (order.strict.irreflexivity 1) as i.
    unfold Negation in i.
    modus ponens i, h as f.
    contradiction f.
  +
    reflexivity.
  +
    unfold LessThan in h.
    destruct h as [k e].
    simpl in e.
    discriminate e.
  +
    exact (IH n' (successor.order.monotonicity.inversion h)).
Qed.

End backward. (* comparison.strict.backward *)

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

Module forward. (* comparison.equality.forward *)

(* comparison.equality.forward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} . compare m n = Comparison.Eq -> m = n.
Proof.
  intros m.
  induction m as [| m' IH]
      using Nat.induction;
      intro n;
  destruct n as [| n'];
      intro e;
      simpl in |- *.
  + reflexivity.
  + discriminate e.
  + discriminate e.
  + rewrite (IH n' e) in |- *.
    reflexivity.
Qed.

End forward. (* comparison.equality.forward *)

Module backward. (* comparison.equality.backward *)

(* comparison.equality.backward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} . m = n -> compare m n = Comparison.Eq.
Proof.
  intros m n e.
  rewrite e in |- *.
  clear e.
  induction n as [| n' IH] using Nat.induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

End backward. (* comparison.equality.backward *)

End equality. (* comparison.equality *)

(* comparison.specification *)
Theorem specification
  : forall (m : Nat) (n : Nat) .
      (compare m n = Comparison.Lt <-> m < n) /\ (compare m n = Comparison.Eq <-> m = n).
Proof.
  intros m n.
  split; split.
  - exact (@comparison.strict.forward.specification    m n).
  - exact (@comparison.strict.backward.specification   m n).
  - exact (@comparison.equality.forward.specification  m n).
  - exact (@comparison.equality.backward.specification m n).
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (m : Nat) (n : Nat) . compare m n = Comparison.transpose (compare n m).
Proof.
  intros m.
  induction m as [| m' IH]
      using Nat.induction;
      intros n;
  destruct n as [| n'];
      simpl in |- *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (IH n').
Qed.

Module maximum. (* comparison.maximum *)

Module right. (* comparison.maximum.right *)

(* comparison.maximum.right.identity *)
Lemma identity : forall (n : Nat) . max n 1 = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct (compare n 1) as [| |] eqn:c.
  - pose proof (comparison.strict.forward.specification c)
            as lt.
    unfold LessThan in lt.
    destruct lt as [k e].
    destruct n as [| n'];
        simpl in e;
        discriminate e.
  - reflexivity.
  - reflexivity.
Qed.

End right. (* comparison.maximum.right *)

Module left. (* comparison.maximum.left *)

(* comparison.maximum.left.identity *)
Lemma identity : forall (n : Nat) . max 1 n = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

End left. (* comparison.maximum.left *)

(* comparison.maximum.identity *)
Theorem identity
  : forall (n : Nat) . (max 1 n = n) /\ (max n 1 = n).
Proof.
  intros n.
  split.
  - exact (comparison.maximum.left.identity  n).
  - exact (comparison.maximum.right.identity n).
Qed.

End maximum. (* comparison.maximum *)

End comparison. (* comparison *)

Module subtraction. (* subtraction *)

(* subtraction.truncation *)
Theorem truncation
  : forall {m : Nat} {n : Nat} . m <= n -> sub m n = None.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  -
    rewrite e in |- *.
    clear e.
    induction n as [| n' IH]
        using Nat.induction;
        simpl in |- *.
    + reflexivity.
    + exact IH.
  -
    unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    clear e e'.
    induction m as [| m' IH]
        using Nat.induction;
        simpl in |- *.
    + reflexivity.
    + exact IH.
Qed.

Module inversion. (* subtraction.inversion *)

Module of. (* subtraction.inversion.of *)

(* subtraction.inversion.of.addition *)
Theorem addition
  : forall (m : Nat) (n : Nat) . sub (m + n) n = Some m.
Proof.
  intros m n.
  induction n as [| n' IH] using Nat.induction.
  - rewrite (addition.commutativity m 1) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (addition.commutativity m (S n')) in |- *.
    simpl in |- *.
    rewrite (addition.commutativity n' m) in |- *.
    exact IH.
Qed.

End of. (* subtraction.inversion.of *)

End inversion. (* subtraction.inversion *)

(* subtraction.cancellation *)
Theorem cancellation
  : forall (k : Nat) (m : Nat) (n : Nat) . sub (k + m) (k + n) = sub m n.
Proof.
  intros k m n.
  induction k as [| k' IH] using Nat.induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Module forward. (* subtraction.forward *)

(* subtraction.forward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} {k : Nat} . sub m n = Some k -> n + k = m.
Proof.
  intros m.
  induction m as [| m' IH] using Nat.induction.
  -
    intros n k e.
    simpl in e.
    discriminate e.
  -
    intros n k.
    destruct n as [| n'];
        simpl in |- *;
        intro e.
    +
      pose proof (Option.some.injectivity e) as e'.
      rewrite e' in |- *.
      reflexivity.
    +
      rewrite (IH n' k e) in |- *.
      reflexivity.
Qed.

End forward. (* subtraction.forward *)

Module backward. (* subtraction.backward *)

(* subtraction.backward.specification *)
Lemma specification
  : forall {m : Nat} {n : Nat} {k : Nat} . n + k = m -> sub m n = Some k.
Proof.
  intros m n k e.
  symmetry in e.
  rewrite e in |- *.
  rewrite (addition.commutativity n k) in |- *.
  exact (subtraction.inversion.of.addition k n).
Qed.

End backward. (* subtraction.backward *)

(* subtraction.specification *)
Theorem specification
  : forall (m : Nat) (n : Nat) (k : Nat) . sub m n = Some k <-> n + k = m.
Proof.
  intros m n k.
  split.
  - exact (@subtraction.forward.specification  m n k).
  - exact (@subtraction.backward.specification m n k).
Qed.

Module saturating. (* subtraction.saturating *)

(* subtraction.saturating.truncation *)
Theorem truncation
  : forall {m : Nat} {n : Nat} . m <= n -> saturating_sub m n = 1.
Proof.
  intros m n h.
  unfold saturating_sub in |- *.
  rewrite (subtraction.truncation h) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Module inversion. (* subtraction.saturating.inversion *)

Module of. (* subtraction.saturating.inversion.of *)

(* subtraction.saturating.inversion.of.addition *)
Theorem addition
  : forall (m : Nat) (n : Nat) . saturating_sub (m + n) n = m.
Proof.
  intros m n.
  unfold saturating_sub in |- *.
  rewrite (subtraction.inversion.of.addition m n) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End of. (* subtraction.saturating.inversion.of *)

End inversion. (* subtraction.saturating.inversion *)

(* subtraction.saturating.specification *)
Theorem specification
  : forall {m : Nat} {n : Nat} . n < m -> n + saturating_sub m n = m.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  unfold saturating_sub in |- *.
  rewrite (subtraction.backward.specification e) in |- *.
  simpl in |- *.
  exact e.
Qed.

End saturating. (* subtraction.saturating *)

End subtraction. (* subtraction *)

End Nat. (* Nat *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Nat], not [Nat.T]. The two ctors keep the prefix: [Nat.One] and
 * [Nat.Successor]
 * are exactly the short names another numeral type would want.
 *)
Abbreviation Nat := Nat.T.

(* Makes the notations declared in [Module Nat] usable in every file that
 * imports this one, as [(m + n)%nat] or under an opened [jwa_nat_scope].
 * Only the notations are exported: [add] and the laws still need the
 * [Nat.] prefix, and the local aliases [1] and [S] stay inside the module.
 *)
Export (notations) Nat.

Instance Nat_less_than_well_founded
  : WellFounded Nat.LessThan :=
  {| accessibility := Nat.order.strict.wellfoundedness |}.

Instance Nat_comparable
  : Comparable Nat.compare Nat.LessThan :=
  {| Comparable.transitivity  := @Nat.order.strict.transitivity
   ; Comparable.specification := Nat.comparison.specification
   ; Comparable.antisymmetry  := Nat.comparison.antisymmetry |}.

Instance Nat_add_semigroup
  : Semigroup Nat.add :=
  {| Semigroup.associativity := Nat.addition.associativity |}.

Instance Nat_add_cancellative
  : Cancellative Nat.add :=
  {| Cancellative.cancellation := Nat.addition.cancellation |}.

Instance Nat_mul_cancellative
  : Cancellative Nat.mul :=
  {| Cancellative.cancellation := Nat.multiplication.cancellation |}.

Instance Nat_mul_monoid
  : Monoid Nat.mul Nat.One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.multiplication.associativity |}
   ; Monoid.identity := Nat.multiplication.identity |}.

Instance Nat_add_commutative
  : Commutative Nat.add :=
  {| Commutative.commutativity := Nat.addition.commutativity |}.

Instance Nat_mul_commutative
  : Commutative Nat.mul :=
  {| Commutative.commutativity := Nat.multiplication.commutativity |}.

Instance Nat_min_semigroup
  : Semigroup Nat.min :=
  {| Semigroup.associativity := Comparable.minimum.associativity |}.

Instance Nat_max_monoid
  : Monoid Nat.max Nat.One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.maximum.associativity |}
   ; Monoid.identity := Nat.comparison.maximum.identity |}.

Instance Nat_min_commutative
  : Commutative Nat.min :=
  {| Commutative.commutativity := Comparable.minimum.commutativity |}.

Instance Nat_max_commutative
  : Commutative Nat.max :=
  {| Commutative.commutativity := Comparable.maximum.commutativity |}.
