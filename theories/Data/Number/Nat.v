(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Option.

(* Zero is not a [Nat]; [One] is the smallest.
 * [Data.Number.NatWithZero] is the type that has it.
 *)
Inductive Nat : Type :=
  | One       : Nat
  | Successor : Nat -> Nat.

Definition Nat_induction
  : forall (P : Nat -> Prop) .
      P One ->
      (forall (n : Nat) . P n -> P (Successor n)) ->
      forall (n : Nat) . P n
  := fun (P : Nat -> Prop)
         (base : P One)
         (step : forall (n : Nat) . P n -> P (Successor n)) =>
       fix go (n : Nat) : P n :=
         match n with
         | One          => base
         | Successor n' => step n' (go n')
         end.

(* A module may carry the type's name; its members read [Nat.add]. *)
Module Nat.

(* Short spellings for this module only: [Local] keeps them out of the
 * [Export (notations) Nat] after [End Nat].
 *)
Local Notation "1" := One (only parsing).
Local Abbreviation S := Successor (only parsing).

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
Definition inc := fun (n : Nat) => S n.

Notation "++ n" := (inc n) (only parsing)
  : jwa_nat_scope.

(* Addition *)

Theorem addition_associativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat_induction.
  -
    simpl in |- *.
    reflexivity.
  -
    simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem addition_commutativity : forall (m : Nat) (n : Nat) . m + n = n + m.
Proof.
  intros m n.
  induction m as [| m' IH] using Nat_induction; simpl in |- *.
  - induction n as [| n' IH2] using Nat_induction; simpl in |- *.
    + reflexivity.
    + pose proof (Identity.symmetry IH2) as IH2'.
      rewrite IH2' in |- *.
      reflexivity.
  - rewrite IH in |- *.
    clear IH.
    induction n as [| n' IH2] using Nat_induction; simpl in |- *.
    + reflexivity.
    + pose proof (Identity.symmetry IH2) as IH2'.
      rewrite IH2' in |- *.
      reflexivity.
Qed.

Lemma suc_injectivity
  : forall (m : Nat) (n : Nat) . S m = S n -> m = n.
Proof.
  intros m n e.
  pose (f := (fun (x : Nat) => match x with | 1 => m | S y => y end)).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem addition_identity_absence : forall (k : Nat) (n : Nat) . ~ (k + n = n).
Proof.
  intros k n.
  induction n as [| n' IH] using Nat_induction.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition_commutativity k 1) in e.
    simpl in e.
    discriminate e.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition_commutativity k (S n')) in e.
    simpl in e.
    pose proof (suc_injectivity (n' + k) n' e) as e'.
    rewrite (addition_commutativity n' k) in e'.
    unfold Negation in IH.
    exact (IH e').
Qed.

Theorem add_l_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) . m + n = m + k -> n = k.
Proof.
  intros m n k.
  induction m as [| m' IH] using Nat_induction.
  - simpl in |- *.
    intro e.
    exact (suc_injectivity n k e).
  - simpl in |- *.
    intro e.
    pose proof (suc_injectivity (m' + n) (m' + k) e) as e'.
    exact (IH e').
Qed.

Theorem add_r_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) . m + n = k + n -> m = k.
Proof.
  intros m n k e.
  rewrite (addition_commutativity k n) in e.
  rewrite (addition_commutativity m n) in e.
  exact (add_l_cancellation n m k e).
Qed.

Theorem addition_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (add_l_cancellation m n k).
  - exact (add_r_cancellation m n k).
Qed.

Lemma add_l_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  rewrite (addition_commutativity l (m + n)) in |- *.
  rewrite (addition_associativity m n l)     in |- *.
  rewrite (addition_commutativity n l)       in |- *.
  reflexivity.
Qed.

Lemma add_r_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l + m) + n = (l + n) + m.
Proof.
  intros l m n.
  rewrite (addition_associativity l m n) in |- *.
  rewrite (addition_associativity l n m) in |- *.
  rewrite (addition_commutativity m n)   in |- *.
  reflexivity.
Qed.

(* Multiplication *)

Theorem multiplication_commutativity : forall (m : Nat) (n : Nat) . m * n = n * m.
Proof.
  intros m n.
  induction m as [| m' IH] using Nat_induction; simpl in |- *.
  -
    induction n as [| n' IH2] using Nat_induction; simpl in |- *.
    + reflexivity.
    + pose proof (Identity.symmetry IH2) as IH2'.
      rewrite IH2' in |- *.
      reflexivity.
  -
    rewrite IH in |- *.
    clear IH.
    induction n as [| n' IH2] using Nat_induction; simpl in |- *.
    + reflexivity.
    + pose proof (Identity.symmetry IH2) as IH2'.
      rewrite IH2' in |- *.
      rewrite (add_l_commutativity n' m' (n' * m')) in |- *.
      reflexivity.
Qed.

Theorem mul_l_distributivity_over_addition
  : forall (l : Nat) (m : Nat) (n : Nat) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (addition_associativity m n ((l' * m) + (l' * n))) in |- *.
    rewrite (add_l_commutativity n (l' * m) (l' * n))          in |- *.
    rewrite (addition_associativity m (l' * m) (n + (l' * n))) in |- *.
    reflexivity.
Qed.

Theorem mul_r_distributivity_over_addition
  : forall (l : Nat) (m : Nat) (n : Nat) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity (m + n) l)   in |- *.
  rewrite (mul_l_distributivity_over_addition l m n) in |- *.
  rewrite (multiplication_commutativity l m)         in |- *.
  rewrite (multiplication_commutativity l n)         in |- *.
  reflexivity.
Qed.

Theorem multiplication_distributivity_over_addition
  : forall (a : Nat) (b : Nat) (c : Nat) (d : Nat) .
      (a + b) * (c + d) = ((a * c) + (a * d)) + ((b * c) + (b * d)).
Proof.
  intros a b c d.
  rewrite (mul_r_distributivity_over_addition (c + d) a b) in |- *.
  rewrite (mul_l_distributivity_over_addition a c d)       in |- *.
  rewrite (mul_l_distributivity_over_addition b c d)       in |- *.
  reflexivity.
Qed.

Theorem multiplication_associativity
  : forall (l : Nat) (m : Nat) (n : Nat) .
    (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite (mul_r_distributivity_over_addition n m (l' * m)) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem multiplication_identity
  : forall (n : Nat) . (1 * n = n) /\ (n * 1 = n).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (multiplication_commutativity n 1) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Lemma mul_l_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . l * (m * n) = m * (l * n).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity l (m * n)) in |- *.
  rewrite (multiplication_associativity m n l)     in |- *.
  rewrite (multiplication_commutativity n l)       in |- *.
  reflexivity.
Qed.

Lemma mul_r_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat) . (l * m) * n = (l * n) * m.
Proof.
  intros l m n.
  rewrite (multiplication_associativity l m n) in |- *.
  rewrite (multiplication_associativity l n m) in |- *.
  rewrite (multiplication_commutativity m n)   in |- *.
  reflexivity.
Qed.

Theorem multiplication_identity_factorization
  : forall (k : Nat) (j : Nat) . k * j = 1 -> k = 1 /\ j = 1.
Proof.
  intros k j e.
  destruct k as [| k']; simpl in e.
  -
    rewrite e in |- *.
    exact (Conjunction_introduction
             (Identity.reflexivity 1) (Identity.reflexivity 1)).
  -
    destruct j as [| j'].
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
Qed.

(* Power *)

(* [Nat -> Nat -> Nat] *)
Fixpoint power (m : Nat) (n : Nat) : Nat :=
  match n with
  | 1    => m
  | S n' => m * power m n'
  end.

Lemma power_identity : forall (m : Nat) . power m 1 = m.
Proof.
  intros m. simpl in |- *. reflexivity.
Qed.

Lemma power_annihilation : forall (n : Nat) . power 1 n = 1.
Proof.
  intros n.
  induction n as [| n' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Theorem product_of_powers
  : forall (m : Nat) (a : Nat) (b : Nat) .
      power m a * power m b = power m (a + b).
Proof.
  intros m a b.
  induction a as [| a' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - rewrite (multiplication_associativity m (power m a') (power m b)) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem power_of_a_power
  : forall (m : Nat) (a : Nat) (b : Nat) .
      power (power m a) b = power m (a * b).
Proof.
  intros m a b.
  induction b as [| b' IH] using Nat_induction.
  - rewrite (multiplication_commutativity a 1) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (multiplication_commutativity a (S b')) in |- *.
    simpl in |- *.
    rewrite (multiplication_commutativity b' a) in |- *.
    rewrite <- (product_of_powers m a (a * b')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem power_distributivity_over_multiplication
  : forall (m : Nat) (n : Nat) (a : Nat) .
      power (m * n) a = power m a * power n a.
Proof.
  intros m n a.
  induction a as [| a' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (multiplication_associativity m n (power m a' * power n a'))   in |- *.
    rewrite (mul_l_commutativity n (power m a') (power n a'))              in |- *.
    rewrite (multiplication_associativity m (power m a') (n * power n a')) in |- *.
    reflexivity.
Qed.

(* Order *)

(* [Nat -> Nat -> Prop] *)
Definition LessThan := fun (m : Nat) (n : Nat) => exists (k : Nat) . m + k = n.

(* [Nat -> Nat -> Prop] *)
Definition LessOrEqual := fun (m : Nat) (n : Nat) => m = n \/ LessThan m n.

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

Theorem lt_irreflexivity : forall (n : Nat) . ~ (n < n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  rewrite (addition_commutativity n k) in e.
  pose proof (addition_identity_absence k n) as i.
  unfold Negation in i.
  pose proof (i e) as f.
  contradiction f.
Qed.

Theorem lt_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat) .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (k1 + k2)).
  pose proof (Identity.symmetry (addition_associativity l k1 k2)) as a.
  rewrite a  in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

Lemma lt_suc : forall (n : Nat) . n < S n.
Proof.
  intros n.
  unfold LessThan in |- *.
  apply (Exists_introduction 1).
  rewrite (addition_commutativity n 1) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem addition_left_extensivity : forall (m : Nat) (k : Nat) . m < m + k.
Proof.
  intros m k.
  unfold LessThan in |- *.
  apply (Exists_introduction k).
  reflexivity.
Qed.

(* "Strict" names the order preserved, not a direction: a strictly monotone
 * function carries [<] to [<] (equality excluded), a monotone one [<=] to
 * [<=]. The reversed [>] is [<] read from the other side and needs no law
 * of its own.
 *)
Theorem successor_strict_monotonicity
  : forall (m : Nat) (n : Nat) .
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

Lemma successor_strict_monotonicity_inversion
  : forall (m : Nat) (n : Nat) .
      S m < S n -> m < n.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  simpl in e.
  pose proof (suc_injectivity (m + k) n e) as e'.
  unfold LessThan in |- *.
  exact (Exists_introduction k e').
Qed.

Theorem addition_strict_monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition_associativity k m d) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

Theorem multiplication_strict_monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat) .
      m < n -> k * m < k * n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (k * d)).
  pose proof (Identity.symmetry (mul_l_distributivity_over_addition k m d)) as dist.
  rewrite dist in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Trichotomy, "cut in three": for any [m] and [n], exactly one of
 * [m < n], [m = n], [n < m] holds. This theorem is the "at
 * least one" half; "at most one" is [lt_irreflexivity] with
 * [Comparable.lt_asymmetry].
 *)
Theorem lt_trichotomy
  : forall (m : Nat) (n : Nat) . (m < n) \/ (m = n) \/ (n < m).
Proof.
  intro m.
  induction m as [| m' IH] using Nat_induction;
  intro n;
  destruct n as [| n'].
  +
    pose proof (Identity.reflexivity 1) as id.
    exact (Disjunction.R (Disjunction.L id)).
  +
    apply Disjunction.L.
    unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  +
    apply Disjunction.R.
    apply Disjunction.R.
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    simpl in |- *.
    reflexivity.
  +
    pose proof (IH n') as t.
    destruct t as [lt | rest].
    *
      apply Disjunction.L.
      exact (successor_strict_monotonicity m' n' lt).
    * destruct rest as [eq | gt].
      { apply Disjunction.R.
        apply Disjunction.L.
        rewrite eq in |- *.
        reflexivity. }
      { apply Disjunction.R.
        apply Disjunction.R.
        exact (successor_strict_monotonicity n' m' gt). }
Qed.

Theorem mul_l_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) . m * n = m * k -> n = k.
Proof.
  intros m n k e.
  pose proof (lt_trichotomy n k) as t.
  destruct t as [lt | rest].
  - pose proof (multiplication_strict_monotonicity m n k lt) as lt'.
    rewrite e in lt'.
    pose proof (lt_irreflexivity (m * k)) as i.
    unfold Negation in i.
    pose proof (i lt') as f.
    contradiction f.
  - destruct rest as [eq | gt].
    + exact eq.
    + pose proof (multiplication_strict_monotonicity m k n gt) as gt'.
      rewrite e in gt'.
      pose proof (lt_irreflexivity (m * k)) as i.
      unfold Negation in i.
      pose proof (i gt') as f.
      contradiction f.
Qed.

Theorem mul_r_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) . m * n = k * n -> m = k.
Proof.
  intros m n k e.
  rewrite (multiplication_commutativity m n) in e.
  rewrite (multiplication_commutativity k n) in e.
  exact (mul_l_cancellation n m k e).
Qed.

Theorem multiplication_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat) .
      (m * n = m * k -> n = k)
    /\ (m * n = k * n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (mul_l_cancellation m n k).
  - exact (mul_r_cancellation m n k).
Qed.

(* Comparison *)

(* [Nat -> Nat -> Comparison] *)
Fixpoint compare (m : Nat) (n : Nat) : Comparison :=
  match m, n with
  | 1, 1       => Eq
  | 1, S _     => Lt
  | S _, 1     => Gt
  | S m', S n' => compare m' n'
  end.

Lemma lt_specification_forward
  : forall (m : Nat) (n : Nat) . compare m n = Lt -> m < n.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intro n;
  destruct n as [| n'];
    simpl in |- *;
    intro e.
  + discriminate e.
  + unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  + discriminate e.
  + exact (successor_strict_monotonicity m' n' (IH n' e)).
Qed.

Lemma lt_specification_backward
  : forall (m : Nat) (n : Nat) . m < n -> compare m n = Lt.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intro n;
  destruct n as [| n'];
    intro h;
    simpl in |- *.
  +
    pose proof (lt_irreflexivity 1) as i.
    unfold Negation in i.
    pose proof (i h) as f.
    contradiction f.
  +
    reflexivity.
  +
    unfold LessThan in h.
    destruct h as [k e].
    simpl in e.
    discriminate e.
  +
    exact (IH n' (successor_strict_monotonicity_inversion m' n' h)).
Qed.

Lemma eq_specification_forward
  : forall (m : Nat) (n : Nat) . compare m n = Eq -> m = n.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
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

Lemma eq_specification_backward
  : forall (m : Nat) (n : Nat) . m = n -> compare m n = Eq.
Proof.
  intros m n e.
  rewrite e in |- *.
  clear e.
  induction n as [| n' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Theorem comparison_specification
  : forall (m : Nat) (n : Nat) .
      (compare m n = Lt <-> m < n) /\ (compare m n = Eq <-> m = n).
Proof.
  intros m n.
  split.
  - split.
    + exact (lt_specification_forward  m n).
    + exact (lt_specification_backward m n).
  - split.
    + exact (eq_specification_forward  m n).
    + exact (eq_specification_backward m n).
Qed.

Theorem comparison_antisymmetry
  : forall (m : Nat) (n : Nat) . compare m n = Comparison.transpose (compare n m).
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intros n;
  destruct n as [| n'];
    simpl in |- *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + exact (IH n').
Qed.

(* [Nat -> Nat -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [Nat -> Nat -> Nat] *)
Abbreviation min := (Comparable.min compare).

(* [Nat -> Nat -> Nat] *)
Abbreviation max := (Comparable.max compare).

Lemma max_r_identity : forall (n : Nat) . max n 1 = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct (compare n 1) as [| |] eqn:c.
  - pose proof (lt_specification_forward n 1 c) as lt.
    unfold LessThan in lt.
    destruct lt as [k e].
    destruct n as [| n']; simpl in e; discriminate e.
  - reflexivity.
  - reflexivity.
Qed.

Lemma max_l_identity : forall (n : Nat) . max 1 n = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem max_identity
  : forall (n : Nat) . (max 1 n = n) /\ (max n 1 = n).
Proof.
  intros n.
  split.
  - exact (max_l_identity n).
  - exact (max_r_identity n).
Qed.

(* Subtraction *)

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

Theorem sub_truncation
  : forall (m : Nat) (n : Nat) . m <= n -> sub m n = None.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    clear e.
    induction n as [| n' IH] using Nat_induction; simpl in |- *.
    + reflexivity.
    + exact IH.
  - unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    clear e e'.
    induction m as [| m' IH] using Nat_induction; simpl in |- *.
    + reflexivity.
    + exact IH.
Qed.

Theorem subtraction_inversion_of_addition
  : forall (m : Nat) (n : Nat) . sub (m + n) n = Some m.
Proof.
  intros m n.
  induction n as [| n' IH] using Nat_induction.
  - rewrite (addition_commutativity m 1) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (addition_commutativity m (S n')) in |- *.
    simpl in |- *.
    rewrite (addition_commutativity n' m) in |- *.
    exact IH.
Qed.

Theorem sub_cancellation
  : forall (k : Nat) (m : Nat) (n : Nat) . sub (k + m) (k + n) = sub m n.
Proof.
  intros k m n.
  induction k as [| k' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Lemma sub_specification_forward
  : forall (m : Nat) (n : Nat) (k : Nat) . sub m n = Some k -> n + k = m.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction.
  -
    intros n k e.
    simpl in e.
    discriminate e.
  - intros n k.
    destruct n as [| n']; simpl in |- *; intro e.
    +
      pose proof (Option.some_injectivity Nat m' k e) as e'.
      rewrite e' in |- *.
      reflexivity.
    +
      rewrite (IH n' k e) in |- *.
      reflexivity.
Qed.

Lemma sub_specification_backward
  : forall (m : Nat) (n : Nat) (k : Nat) . n + k = m -> sub m n = Some k.
Proof.
  intros m n k e.
  pose proof (Identity.symmetry e) as e'.
  rewrite e' in |- *.
  rewrite (addition_commutativity n k) in |- *.
  exact (subtraction_inversion_of_addition k n).
Qed.

Theorem subtraction_specification
  : forall (m : Nat) (n : Nat) (k : Nat) . sub m n = Some k <-> n + k = m.
Proof.
  intros m n k.
  split.
  - exact (sub_specification_forward  m n k).
  - exact (sub_specification_backward m n k).
Qed.

(* [Nat -> Nat -> Nat] *)
Definition saturating_sub := fun (m : Nat) (n : Nat) =>
  match sub m n with
  | Some k => k
  | None   => 1
  end.

Theorem saturating_sub_truncation
  : forall (m : Nat) (n : Nat) . m <= n -> saturating_sub m n = 1.
Proof.
  intros m n h.
  unfold saturating_sub in |- *.
  rewrite (sub_truncation m n h) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem saturating_subtraction_inversion_of_addition
  : forall (m : Nat) (n : Nat) . saturating_sub (m + n) n = m.
Proof.
  intros m n.
  unfold saturating_sub in |- *.
  rewrite (subtraction_inversion_of_addition m n) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem saturating_subtraction_specification
  : forall (m : Nat) (n : Nat) . n < m -> n + saturating_sub m n = m.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  unfold saturating_sub in |- *.
  rewrite (sub_specification_backward m n k e) in |- *.
  simpl in |- *.
  exact e.
Qed.

End Nat.

(* Makes the notations declared in [Module Nat] usable in every file that
 * imports this one, as [(m + n)%nat] or under an opened [jwa_nat_scope].
 * Only the notations are exported: [add] and the laws still need the
 * [Nat.] prefix, and the local aliases [1] and [S] stay inside the module.
 *)
Export (notations) Nat.

Instance Nat_comparable
  : Comparable Nat.compare Nat.LessThan :=
  {| Comparable.transitivity  := Nat.lt_transitivity
   ; Comparable.specification := Nat.comparison_specification
   ; Comparable.antisymmetry  := Nat.comparison_antisymmetry |}.

Instance Nat_add_semigroup
  : Semigroup Nat.add :=
  {| Semigroup.associativity := Nat.addition_associativity |}.

Instance Nat_add_cancellative
  : Cancellative Nat.add :=
  {| Cancellative.cancellation := Nat.addition_cancellation |}.

Instance Nat_mul_cancellative
  : Cancellative Nat.mul :=
  {| Cancellative.cancellation := Nat.multiplication_cancellation |}.

Instance Nat_mul_monoid
  : Monoid Nat.mul One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.multiplication_associativity |}
   ; Monoid.identity := Nat.multiplication_identity |}.

Instance Nat_add_commutative
  : Commutative Nat.add :=
  {| Commutative.commutativity := Nat.addition_commutativity |}.

Instance Nat_mul_commutative
  : Commutative Nat.mul :=
  {| Commutative.commutativity := Nat.multiplication_commutativity |}.

Instance Nat_min_semigroup
  : Semigroup Nat.min :=
  {| Semigroup.associativity := Comparable.min_associativity |}.

Instance Nat_max_monoid
  : Monoid Nat.max One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.max_associativity |}
   ; Monoid.identity := Nat.max_identity |}.

Instance Nat_min_commutative
  : Commutative Nat.min :=
  {| Commutative.commutativity := Comparable.min_commutativity |}.

Instance Nat_max_commutative
  : Commutative Nat.max :=
  {| Commutative.commutativity := Comparable.max_commutativity |}.
