(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Option.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Order.StrictOrder.
From jwa Require Import Relation.Order.TotalOrder.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Total.
From jwa Require Import Relation.Transitive.

(* Zero is not a [Nat]; [One] is the smallest.
 * [Data.Number.NatWithZero] is the type that has it.
 *)
Inductive Nat : Type :=
  | One       : Nat
  | Successor : Nat -> Nat.

Definition Nat_induction
  : forall (P : Nat -> Prop),
      P One ->
      (forall (n : Nat), P n -> P (Successor n)) ->
      forall (n : Nat), P n
  := fun (P : Nat -> Prop)
         (base : P One)
         (step : forall (n : Nat), P n -> P (Successor n)) =>
       fix go (n : Nat) : P n :=
         match n with
         | One          => base
         | Successor n' => step n' (go n')
         end.

(* A module may carry the type's name; its members read [Nat.add]. *)
Module Nat.

Fixpoint add (m : Nat) (n : Nat) : Nat :=
  match m with
  | One          => Successor n
  | Successor m' => Successor (add m' n)
  end.

Theorem addition_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), add (add l m) n = add l (add m n).
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

Theorem addition_commutativity : forall (m : Nat) (n : Nat), add m n = add n m.
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
  : forall (m : Nat) (n : Nat), Successor m = Successor n -> m = n.
Proof.
  intros m n e.
  pose (f := (fun (x : Nat) => match x with | One => m | Successor y => y end)).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem addition_identity_absence : forall (k : Nat) (n : Nat), ~ (add k n = n).
Proof.
  intros k n.
  induction n as [| n' IH] using Nat_induction.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition_commutativity k One) in e.
    simpl in e.
    discriminate.
  -
    unfold Negation in |- *.
    intro e.
    rewrite (addition_commutativity k (Successor n')) in e.
    simpl in e.
    pose proof (suc_injectivity (add n' k) n' e) as e'.
    rewrite (addition_commutativity n' k) in e'.
    unfold Negation in IH.
    exact (IH e').
Qed.

Theorem add_l_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat), add m n = add m k -> n = k.
Proof.
  intros m n k.
  induction m as [| m' IH] using Nat_induction.
  - simpl in |- *.
    intro e.
    exact (suc_injectivity n k e).
  - simpl in |- *.
    intro e.
    pose proof (suc_injectivity (add m' n) (add m' k) e) as e'.
    exact (IH e').
Qed.

Theorem add_r_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat), add m n = add k n -> m = k.
Proof.
  intros m n k e.
  rewrite (addition_commutativity k n) in e.
  rewrite (addition_commutativity m n) in e.
  exact (add_l_cancellation n m k e).
Qed.

Theorem addition_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat),
    (add m n = add m k -> n = k) /\ (add m n = add k n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (add_l_cancellation m n k).
  - exact (add_r_cancellation m n k).
Qed.

Lemma add_l_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), add l (add m n) = add m (add l n).
Proof.
  intros l m n.
  rewrite (addition_commutativity l (add m n)) in |- *.
  rewrite (addition_associativity m n l)       in |- *.
  rewrite (addition_commutativity n l)         in |- *.
  reflexivity.
Qed.

Lemma add_r_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), add (add l m) n = add (add l n) m.
Proof.
  intros l m n.
  rewrite (addition_associativity l m n) in |- *.
  rewrite (addition_associativity l n m) in |- *.
  rewrite (addition_commutativity m n)   in |- *.
  reflexivity.
Qed.

Fixpoint mul (m : Nat) (n : Nat) : Nat :=
  match m with
  | One          => n
  | Successor m' => add n (mul m' n)
  end.

Theorem multiplication_commutativity : forall (m : Nat) (n : Nat), mul m n = mul n m.
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
      rewrite (add_l_commutativity n' m' (mul n' m')) in |- *.
      reflexivity.
Qed.

Theorem mul_l_distributivity_over_addition
  : forall (l : Nat) (m : Nat) (n : Nat),
      mul l (add m n) = add (mul l m) (mul l n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (addition_associativity m n (add (mul l' m) (mul l' n))) in |- *.
    rewrite (add_l_commutativity n (mul l' m) (mul l' n))            in |- *.
    rewrite (addition_associativity m (mul l' m) (add n (mul l' n))) in |- *.
    reflexivity.
Qed.

Theorem mul_r_distributivity_over_addition
  : forall (l : Nat) (m : Nat) (n : Nat),
      mul (add m n) l = add (mul m l) (mul n l).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity (add m n) l) in |- *.
  rewrite (mul_l_distributivity_over_addition l m n) in |- *.
  rewrite (multiplication_commutativity l m)         in |- *.
  rewrite (multiplication_commutativity l n)         in |- *.
  reflexivity.
Qed.

Theorem multiplication_distributivity_over_addition
  : forall (a : Nat) (b : Nat) (c : Nat) (d : Nat),
      mul (add a b) (add c d)
    = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d)).
Proof.
  intros a b c d.
  rewrite (mul_r_distributivity_over_addition (add c d) a b) in |- *.
  rewrite (mul_l_distributivity_over_addition a c d)         in |- *.
  rewrite (mul_l_distributivity_over_addition b c d)         in |- *.
  reflexivity.
Qed.

Theorem multiplication_associativity
  : forall (l : Nat) (m : Nat) (n : Nat),
    mul (mul l m) n = mul l (mul m n).
Proof.
  intros l m n.
  induction l as [| l' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite (mul_r_distributivity_over_addition n m (mul l' m)) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem multiplication_identity
  : forall (n : Nat), (mul One n = n) /\ (mul n One = n).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (multiplication_commutativity n One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Lemma mul_l_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), mul l (mul m n) = mul m (mul l n).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity l (mul m n)) in |- *.
  rewrite (multiplication_associativity m n l)       in |- *.
  rewrite (multiplication_commutativity n l)         in |- *.
  reflexivity.
Qed.

Lemma mul_r_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), mul (mul l m) n = mul (mul l n) m.
Proof.
  intros l m n.
  rewrite (multiplication_associativity l m n) in |- *.
  rewrite (multiplication_associativity l n m) in |- *.
  rewrite (multiplication_commutativity m n)   in |- *.
  reflexivity.
Qed.

(* [Nat -> Nat -> Nat] *)
Fixpoint power (m : Nat) (n : Nat) : Nat :=
  match n with
  | One          => m
  | Successor n' => mul m (power m n')
  end.

Lemma power_identity : forall (m : Nat), power m One = m.
Proof.
  intros m. simpl in |- *. reflexivity.
Qed.

Lemma power_annihilation : forall (n : Nat), power One n = One.
Proof.
  intros n.
  induction n as [| n' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Theorem product_of_powers
  : forall (m : Nat) (a : Nat) (b : Nat),
      mul (power m a) (power m b) = power m (add a b).
Proof.
  intros m a b.
  induction a as [| a' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - rewrite (multiplication_associativity m (power m a') (power m b)) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem power_of_a_power
  : forall (m : Nat) (a : Nat) (b : Nat),
      power (power m a) b = power m (mul a b).
Proof.
  intros m a b.
  induction b as [| b' IH] using Nat_induction.
  - rewrite (multiplication_commutativity a One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (multiplication_commutativity a (Successor b')) in |- *.
    simpl in |- *.
    rewrite (multiplication_commutativity b' a) in |- *.
    rewrite <- (product_of_powers m a (mul a b')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem power_distributivity_over_multiplication
  : forall (m : Nat) (n : Nat) (a : Nat),
      power (mul m n) a = mul (power m a) (power n a).
Proof.
  intros m n a.
  induction a as [| a' IH] using Nat_induction; simpl in |- *.
  -
    reflexivity.
  -
    rewrite IH in |- *.
    rewrite (multiplication_associativity m n (mul (power m a') (power n a'))) in |- *.
    rewrite (mul_l_commutativity n (power m a') (power n a'))                  in |- *.
    rewrite (multiplication_associativity m (power m a') (mul n (power n a'))) in |- *.
    reflexivity.
Qed.

(* [Nat -> Nat -> Prop] *)
Definition LessThan := fun (m : Nat) (n : Nat) => exists (k : Nat), add m k = n.

(* [Nat -> Nat -> Prop] *)
Definition LessOrEqual := fun (m : Nat) (n : Nat) => m = n \/ LessThan m n.

Theorem lt_irreflexivity : forall (n : Nat), ~ (LessThan n n).
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
  contradiction.
Qed.

Theorem lt_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (add k1 k2)).
  pose proof (Identity.symmetry (addition_associativity l k1 k2)) as a.
  rewrite a  in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

Theorem lt_asymmetry
  : forall (m : Nat) (n : Nat), LessThan m n -> ~ (LessThan n m).
Proof.
  intros m n h1.
  unfold LessThan in h1.
  destruct h1 as [k1 e1].
  unfold Negation in |- *.
  intro h2.
  unfold LessThan in h2.
  destruct h2 as [k2 e2].
  pose proof (Identity.symmetry e1) as e1'.
  rewrite e1' in e2.
  rewrite (addition_associativity m k1 k2)       in e2.
  rewrite (addition_commutativity m (add k1 k2)) in e2.
  pose proof (addition_identity_absence (add k1 k2) m) as i.
  unfold Negation in i.
  pose proof (i e2) as f.
  contradiction.
Qed.

Lemma lt_suc : forall (n : Nat), LessThan n (Successor n).
Proof.
  intros n.
  unfold LessThan in |- *.
  apply (Exists_introduction One).
  rewrite (addition_commutativity n One) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem addition_left_inflation : forall (m : Nat) (k : Nat), LessThan m (add m k).
Proof.
  intros m k.
  unfold LessThan in |- *.
  apply (Exists_introduction k).
  reflexivity.
Qed.

(* "Strict" says which order is preserved, not which direction: a strictly
   monotone function carries [<] to [<] (equality excluded), a monotone one
   carries [<=] to [<=]. Both go the same way; the reversed relation [>] is
   [<] read from the other side and needs no law of its own. *)
Theorem successor_strict_monotonicity
  : forall (m : Nat) (n : Nat),
      LessThan m n -> LessThan (Successor m) (Successor n).
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
  : forall (m : Nat) (n : Nat),
      LessThan (Successor m) (Successor n) -> LessThan m n.
Proof.
  intros m n h.
  unfold LessThan in h.
  destruct h as [k e].
  simpl in e.
  pose proof (suc_injectivity (add m k) n e) as e'.
  unfold LessThan in |- *.
  exact (Exists_introduction k e').
Qed.

Theorem addition_strict_monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessThan m n -> LessThan (add k m) (add k n).
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
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessThan m n -> LessThan (mul k m) (mul k n).
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (mul k d)).
  pose proof (Identity.symmetry (mul_l_distributivity_over_addition k m d)) as dist.
  rewrite dist in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Trichotomy, "cut in three": whichever two numbers [m] and [n] are taken,
   exactly one of `[m] is below [n]`, `[m] is [n]`, `[n] is below [m]` is the case.
   This theorem is the "at least one" half;
   "at most one" is [lt_irreflexivity] and [lt_asymmetry]. *)
Theorem lt_trichotomy
  : forall (m : Nat) (n : Nat), (LessThan m n) \/ (m = n) \/ (LessThan n m).
Proof.
  intro m.
  induction m as [| m' IH] using Nat_induction;
  intro n;
  destruct n as [| n'].
  +
    pose proof (Identity.reflexivity One) as id.
    exact (Disjunction.r (Disjunction.l id)).
  +
    apply Disjunction.l.
    unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  +
    apply Disjunction.r.
    apply Disjunction.r.
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    simpl in |- *.
    reflexivity.
  +
    pose proof (IH n') as t.
    destruct t as [lt | rest].
    *
      apply Disjunction.l.
      exact (successor_strict_monotonicity m' n' lt).
    * destruct rest as [eq | gt].
      { apply Disjunction.r.
        apply Disjunction.l.
        rewrite eq in |- *.
        reflexivity. }
      { apply Disjunction.r.
        apply Disjunction.r.
        exact (successor_strict_monotonicity n' m' gt). }
Qed.

Theorem mul_l_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat), mul m n = mul m k -> n = k.
Proof.
  intros m n k e.
  pose proof (lt_trichotomy n k) as t.
  destruct t as [lt | rest].
  - pose proof (multiplication_strict_monotonicity m n k lt) as lt'.
    rewrite e in lt'.
    pose proof (lt_irreflexivity (mul m k)) as i.
    unfold Negation in i.
    pose proof (i lt') as f.
    contradiction.
  - destruct rest as [eq | gt].
    + exact eq.
    + pose proof (multiplication_strict_monotonicity m k n gt) as gt'.
      rewrite e in gt'.
      pose proof (lt_irreflexivity (mul m k)) as i.
      unfold Negation in i.
      pose proof (i gt') as f.
      contradiction.
Qed.

Theorem mul_r_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat), mul m n = mul k n -> m = k.
Proof.
  intros m n k e.
  rewrite (multiplication_commutativity m n) in e.
  rewrite (multiplication_commutativity k n) in e.
  exact (mul_l_cancellation n m k e).
Qed.

Theorem multiplication_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat),
      (mul m n = mul m k -> n = k)
    /\ (mul m n = mul k n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (mul_l_cancellation m n k).
  - exact (mul_r_cancellation m n k).
Qed.

Theorem multiplication_identity_factorization
  : forall (k : Nat) (j : Nat), mul k j = One -> k = One /\ j = One.
Proof.
  intros k j e.
  destruct k as [| k']; simpl in e.
  -
    rewrite e in |- *.
    exact (Conjunction_introduction
             (Identity.reflexivity One) (Identity.reflexivity One)).
  -
    destruct j as [| j'].
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
Qed.

Theorem le_reflexivity : forall (n : Nat), LessOrEqual n n.
Proof.
  intros n.
  unfold LessOrEqual in |- *.
  exact (Disjunction.l (Identity.reflexivity n)).
Qed.

Theorem le_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat),
      LessOrEqual l m -> LessOrEqual m n -> LessOrEqual l n.
Proof.
  intros l m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  unfold LessOrEqual in |- *.
  destruct h1 as [e1 | lt1].
  - rewrite e1 in |- *.
    exact h2.
  - destruct h2 as [e2 | lt2].
    + rewrite e2 in lt1.
      exact (Disjunction.r lt1).
    + exact (Disjunction.r (lt_transitivity l m n lt1 lt2)).
Qed.

Theorem le_antisymmetry
  : forall (m : Nat) (n : Nat), LessOrEqual m n -> LessOrEqual n m -> m = n.
Proof.
  intros m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  destruct h1 as [e1 | lt1].
  - exact e1.
  - destruct h2 as [e2 | lt2].
    + exact (Identity.symmetry e2).
    + pose proof (lt_asymmetry m n lt1) as h.
      unfold Negation in h.
      pose proof (h lt2) as f.
      contradiction.
Qed.

Theorem le_totality
  : forall (m : Nat) (n : Nat), (LessOrEqual m n) \/ (LessOrEqual n m).
Proof.
  intros m n.
  pose proof (lt_trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt | rest].
  - exact (Disjunction.l (Disjunction.r lt)).
  - destruct rest as [eq | gt].
    + exact (Disjunction.l  (Disjunction.l  eq)).
    + exact (Disjunction.r (Disjunction.r gt)).
Qed.

Fixpoint compare (m : Nat) (n : Nat) : Comparison :=
  match m, n with
  | One, One                   => Eq
  | One, Successor _           => Lt
  | Successor _, One           => Gt
  | Successor m', Successor n' => compare m' n'
  end.

Lemma comparison_reflexivity : forall (n : Nat), compare n n = Eq.
Proof.
  intros n.
  induction n as [| n' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Lemma comparison_lt_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Lt -> LessThan m n.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intro n;
  destruct n as [| n'];
    simpl in |- *;
    intro e.
  + discriminate.
  + unfold LessThan in |- *.
    apply (Exists_introduction n').
    simpl in |- *.
    reflexivity.
  + discriminate.
  + exact (successor_strict_monotonicity m' n' (IH n' e)).
Qed.

Lemma comparison_lt_specification_backward
  : forall (m : Nat) (n : Nat), LessThan m n -> compare m n = Lt.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intro n;
  destruct n as [| n'];
    intro h;
    simpl in |- *.
  +
    pose proof (lt_irreflexivity One) as i.
    unfold Negation in i.
    pose proof (i h) as f.
    contradiction.
  +
    reflexivity.
  +
    unfold LessThan in h.
    destruct h as [k e].
    simpl in e.
    discriminate.
  +
    exact (IH n' (successor_strict_monotonicity_inversion m' n' h)).
Qed.

Theorem comparison_lt_specification
  : forall (m : Nat) (n : Nat), compare m n = Lt <-> LessThan m n.
Proof.
  intros m n.
  split.
  - exact (comparison_lt_specification_forward  m n).
  - exact (comparison_lt_specification_backward m n).
Qed.

Lemma comparison_eq_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Eq -> m = n.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction;
    intro n;
  destruct n as [| n'];
    intro e;
    simpl in |- *.
  + reflexivity.
  + discriminate.
  + discriminate.
  + rewrite (IH n' e) in |- *.
    reflexivity.
Qed.

Lemma comparison_eq_specification_backward
  : forall (m : Nat) (n : Nat), m = n -> compare m n = Eq.
Proof.
  intros m n e.
  rewrite e in |- *.
  exact (comparison_reflexivity n).
Qed.

Theorem comparison_eq_specification
  : forall (m : Nat) (n : Nat), compare m n = Eq <-> m = n.
Proof.
  intros m n.
  split.
  - exact (comparison_eq_specification_forward  m n).
  - exact (comparison_eq_specification_backward m n).
Qed.

Theorem comparison_antisymmetry
  : forall (m : Nat) (n : Nat), compare m n = Comparison.transpose (compare n m).
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

Lemma comparison_gt_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Gt -> LessThan n m.
Proof.
  intros m n e.
  rewrite (comparison_antisymmetry m n) in e.
  destruct (compare n m) as [| |] eqn:c; simpl in e.
  - exact (comparison_lt_specification_forward n m c).
  - discriminate.
  - discriminate.
Qed.

Lemma comparison_gt_specification_backward
  : forall (m : Nat) (n : Nat), LessThan n m -> compare m n = Gt.
Proof.
  intros m n h.
  rewrite (comparison_antisymmetry m n) in |- *.
  rewrite (comparison_lt_specification_backward n m h) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem comparison_gt_specification
  : forall (m : Nat) (n : Nat), compare m n = Gt <-> LessThan n m.
Proof.
  intros m n.
  split.
  - exact (comparison_gt_specification_forward  m n).
  - exact (comparison_gt_specification_backward m n).
Qed.

(* [Nat -> Nat -> Bool] *)
Definition equal := fun (m : Nat) (n : Nat) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

Lemma eq_specification_forward
  : forall (m : Nat) (n : Nat), equal m n = true -> m = n.
Proof.
  intros m n e.
  unfold equal in e.
  destruct (compare m n) as [| |] eqn:c.
  - discriminate.
  - exact (comparison_eq_specification_forward m n c).
  - discriminate.
Qed.

Lemma eq_specification_backward
  : forall (m : Nat) (n : Nat), m = n -> equal m n = true.
Proof.
  intros m n e.
  unfold equal in |- *.
  rewrite (comparison_eq_specification_backward m n e) in |- *.
  reflexivity.
Qed.

Theorem eq_specification
  : forall (m : Nat) (n : Nat), equal m n = true <-> m = n.
Proof.
  intros m n.
  split.
  - exact (eq_specification_forward  m n).
  - exact (eq_specification_backward m n).
Qed.

(* [Nat -> Nat -> Nat] *)
Definition min := fun (m : Nat) (n : Nat) =>
  match compare m n with
  | Lt => m
  | Eq => m
  | Gt => n
  end.

(* [Nat -> Nat -> Nat] *)
Definition max := fun (m : Nat) (n : Nat) =>
  match compare m n with
  | Lt => n
  | Eq => m
  | Gt => m
  end.

Theorem min_specification
  : forall (m : Nat) (n : Nat), min m n = m <-> LessOrEqual m n.
Proof.
  intros m n.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    +
      apply Disjunction.r.
      exact (Biimplication.forward_elimination
               (compare m n = Lt) (LessThan m n)
               (comparison_lt_specification m n) c).
    +
      apply Disjunction.l.
      exact (Biimplication.forward_elimination
               (compare m n = Eq) (m = n) (comparison_eq_specification m n) c).
    +
      apply Disjunction.l.
      exact (Identity.symmetry e).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + pose proof (Biimplication.forward_elimination
                    (compare m n = Gt) (LessThan n m)
                    (comparison_gt_specification m n) c) as gt.
      destruct h as [e | lt].
      *
        rewrite e in gt.
        pose proof (lt_irreflexivity n) as i.
        unfold Negation in i.
        pose proof (i gt) as f.
        contradiction.
      *
        pose proof (lt_asymmetry m n lt) as a.
        unfold Negation in a.
        pose proof (a gt) as f.
        contradiction.
Qed.

Theorem max_specification
  : forall (m : Nat) (n : Nat), max m n = m <-> LessOrEqual n m.
Proof.
  intros m n.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.l.
      exact e.
    + apply Disjunction.l.
      exact (Identity.symmetry
               (Biimplication.forward_elimination
                  (compare m n = Eq) (m = n) (comparison_eq_specification m n) c)).
    + apply Disjunction.r.
      exact (Biimplication.forward_elimination
               (compare m n = Gt) (LessThan n m)
               (comparison_gt_specification m n) c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + pose proof (Biimplication.forward_elimination
                    (compare m n = Lt) (LessThan m n)
                    (comparison_lt_specification m n) c) as lt.
      destruct h as [e | gt].
      * rewrite e in lt.
        pose proof (lt_irreflexivity m) as i.
        unfold Negation in i.
        pose proof (i lt) as f.
        contradiction.
      * pose proof (lt_asymmetry m n lt) as a.
        unfold Negation in a.
        pose proof (a gt) as f.
        contradiction.
    + reflexivity.
    + reflexivity.
Qed.

Lemma min_left_projection : forall (l : Nat) (r : Nat), LessOrEqual (min l r) l.
Proof.
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Gt) (LessThan r l)
             (comparison_gt_specification l r) c).
Qed.

Lemma min_right_projection : forall (l : Nat) (r : Nat), LessOrEqual (min l r) r.
Proof.
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Lt) (LessThan l r)
             (comparison_lt_specification l r) c).
  - apply Disjunction.l.
    exact (Biimplication.forward_elimination
             (compare l r = Eq) (l = r) (comparison_eq_specification l r) c).
  - exact (Disjunction.l (Identity.reflexivity r)).
Qed.

Lemma min_universality
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessOrEqual k m -> LessOrEqual k n -> LessOrEqual k (min m n).
Proof.
  intros k m n h1 h2.
  unfold min in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h1.
  - exact h1.
  - exact h2.
Qed.

Lemma max_left_injection : forall (l : Nat) (r : Nat), LessOrEqual l (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Lt) (LessThan l r)
             (comparison_lt_specification l r) c).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
Qed.

Lemma max_right_injection : forall (l : Nat) (r : Nat), LessOrEqual r (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity r)).
  - apply Disjunction.l.
    exact (Identity.symmetry
             (Biimplication.forward_elimination
                (compare l r = Eq) (l = r) (comparison_eq_specification l r) c)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Gt) (LessThan r l)
             (comparison_gt_specification l r) c).
Qed.

Lemma max_universality
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessOrEqual m k -> LessOrEqual n k -> LessOrEqual (max m n) k.
Proof.
  intros k m n h1 h2.
  unfold max in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h2.
  - exact h1.
  - exact h1.
Qed.

Theorem min_commutativity : forall (m : Nat) (n : Nat), min m n = min n m.
Proof.
  intros m n.
  apply (le_antisymmetry (min m n) (min n m)).
  - exact (min_universality (min m n) n m
            (min_right_projection m n) (min_left_projection m n)).
  - exact (min_universality (min n m) m n
            (min_right_projection n m) (min_left_projection n m)).
Qed.

Theorem max_commutativity : forall (m : Nat) (n : Nat), max m n = max n m.
Proof.
  intros m n.
  apply (le_antisymmetry (max m n) (max n m)).
  - exact (max_universality (max n m) m n
            (max_right_injection n m) (max_left_injection n m)).
  - exact (max_universality (max m n) n m
            (max_right_injection m n) (max_left_injection m n)).
Qed.

Theorem min_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), min (min l m) n = min l (min m n).
Proof.
  intros l m n.
  apply (le_antisymmetry (min (min l m) n) (min l (min m n))).
  - apply (min_universality (min (min l m) n) l (min m n)).
    + exact (le_transitivity (min (min l m) n) (min l m) l
              (min_left_projection (min l m) n) (min_left_projection l m)).
    + apply (min_universality (min (min l m) n) m n).
      * exact (le_transitivity (min (min l m) n) (min l m) m
                (min_left_projection (min l m) n) (min_right_projection l m)).
      * exact (min_right_projection (min l m) n).
  - apply (min_universality (min l (min m n)) (min l m) n).
    + apply (min_universality (min l (min m n)) l m).
      * exact (min_left_projection l (min m n)).
      * exact (le_transitivity (min l (min m n)) (min m n) m
                (min_right_projection l (min m n)) (min_left_projection m n)).
    + exact (le_transitivity (min l (min m n)) (min m n) n
              (min_right_projection l (min m n)) (min_right_projection m n)).
Qed.

Theorem max_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), max (max l m) n = max l (max m n).
Proof.
  intros l m n.
  apply (le_antisymmetry (max (max l m) n) (max l (max m n))).
  - apply (max_universality (max l (max m n)) (max l m) n).
    + apply (max_universality (max l (max m n)) l m).
      * exact (max_left_injection l (max m n)).
      * exact (le_transitivity m (max m n) (max l (max m n))
                (max_left_injection m n) (max_right_injection l (max m n))).
    + exact (le_transitivity n (max m n) (max l (max m n))
              (max_right_injection m n) (max_right_injection l (max m n))).
  - apply (max_universality (max (max l m) n) l (max m n)).
    + exact (le_transitivity l (max l m) (max (max l m) n)
              (max_left_injection l m) (max_left_injection (max l m) n)).
    + apply (max_universality (max (max l m) n) m n).
      * exact (le_transitivity m (max l m) (max (max l m) n)
                (max_right_injection l m) (max_left_injection (max l m) n)).
      * exact (max_right_injection (max l m) n).
Qed.

Theorem min_idempotence : forall (n : Nat), min n n = n.
Proof.
  intros n.
  unfold min in |- *.
  rewrite (comparison_reflexivity n) in |- *.
  reflexivity.
Qed.

Theorem max_idempotence : forall (n : Nat), max n n = n.
Proof.
  intros n.
  unfold max in |- *.
  rewrite (comparison_reflexivity n) in |- *.
  reflexivity.
Qed.

Lemma max_r_identity : forall (n : Nat), max n One = n.
Proof.
  intros n.
  unfold max in |- *.
  destruct (compare n One) as [| |] eqn:c.
  - pose proof (comparison_lt_specification_forward n One c) as lt.
    unfold LessThan in lt.
    destruct lt as [k e].
    destruct n as [| n']; simpl in e; discriminate.
  - reflexivity.
  - reflexivity.
Qed.

Lemma max_l_identity : forall (n : Nat), max One n = n.
Proof.
  intros n.
  rewrite (max_commutativity One n) in |- *.
  exact (max_r_identity n).
Qed.

Theorem max_identity
  : forall (n : Nat), (max One n = n) /\ (max n One = n).
Proof.
  intros n.
  split.
  - exact (max_l_identity n).
  - exact (max_r_identity n).
Qed.

(* [Nat -> Nat -> Option Nat] *)
Fixpoint subtract (m : Nat) (n : Nat) : Option Nat :=
  match m with
  | One => None
  | Successor m' =>
      match n with
      | One          => Some m'
      | Successor n' => subtract m' n'
      end
  end.

Theorem subtract_truncation
  : forall (m : Nat) (n : Nat), LessOrEqual m n -> subtract m n = None.
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

Theorem subtract_inversion_of_add
  : forall (m : Nat) (n : Nat), subtract (add m n) n = Some m.
Proof.
  intros m n.
  induction n as [| n' IH] using Nat_induction.
  - rewrite (addition_commutativity m One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (addition_commutativity m (Successor n')) in |- *.
    simpl in |- *.
    rewrite (addition_commutativity n' m) in |- *.
    exact IH.
Qed.

Theorem subtract_translation_invariance
  : forall (k : Nat) (m : Nat) (n : Nat), subtract (add k m) (add k n) = subtract m n.
Proof.
  intros k m n.
  induction k as [| k' IH] using Nat_induction; simpl in |- *.
  - reflexivity.
  - exact IH.
Qed.

Lemma subtract_specification_forward
  : forall (m : Nat) (n : Nat) (k : Nat), subtract m n = Some k -> add n k = m.
Proof.
  intros m.
  induction m as [| m' IH] using Nat_induction.
  -
    intros n k e.
    simpl in e.
    discriminate.
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

Lemma subtract_specification_backward
  : forall (m : Nat) (n : Nat) (k : Nat), add n k = m -> subtract m n = Some k.
Proof.
  intros m n k e.
  pose proof (Identity.symmetry e) as e'.
  rewrite e' in |- *.
  rewrite (addition_commutativity n k) in |- *.
  exact (subtract_inversion_of_add k n).
Qed.

Theorem subtract_specification
  : forall (m : Nat) (n : Nat) (k : Nat), subtract m n = Some k <-> add n k = m.
Proof.
  intros m n k.
  split.
  - exact (subtract_specification_forward  m n k).
  - exact (subtract_specification_backward m n k).
Qed.

End Nat.

(* The scope is declared in [Core.Notations] and never opened: a client
   writes [(m + n)%nat]. [only parsing] keeps the operations printed by
   name. *)
Notation "m + n" := (Nat.add m n) (only parsing)
  : jwa_nat_scope.
Notation "m * n" := (Nat.mul m n) (only parsing)
  : jwa_nat_scope.
Notation "m < n" := (Nat.LessThan m n) (only parsing)
  : jwa_nat_scope.
Notation "m <= n" := (Nat.LessOrEqual m n) (only parsing)
  : jwa_nat_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
   arguments the other way round, so no law is stated for them. *)
Notation "m > n" := (Nat.LessThan n m) (only parsing)
  : jwa_nat_scope.
Notation "m >= n" := (Nat.LessOrEqual n m) (only parsing)
  : jwa_nat_scope.

Instance Nat_add_semigroup : Semigroup Nat.add :=
  {| Semigroup.associativity := Nat.addition_associativity |}.

Instance Nat_add_cancellative : Cancellative Nat.add :=
  {| Cancellative.cancellation :=
       fun (x : Nat) (y : Nat) (z : Nat) =>
           (Nat.addition_cancellation x y z) |}.

Instance Nat_mul_cancellative
  : Cancellative Nat.mul :=
  {| Cancellative.cancellation := Nat.multiplication_cancellation |}.

Instance Nat_mul_monoid : Monoid Nat.mul One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.multiplication_associativity |}
   ; Monoid.identity := Nat.multiplication_identity |}.

Instance Nat_add_commutative : Commutative Nat.add :=
  {| Commutative.commutativity := Nat.addition_commutativity |}.

Instance Nat_mul_commutative : Commutative Nat.mul :=
  {| Commutative.commutativity := Nat.multiplication_commutativity |}.

Instance Nat_less_than_strict_order : StrictOrder Nat.LessThan :=
  {| StrictOrder.irreflexivity :=
       {| Irreflexive.irreflexivity := Nat.lt_irreflexivity |}
   ; StrictOrder.transitivity :=
       {| Transitive.transitivity   := Nat.lt_transitivity |} |}.

Instance Nat_less_or_eq_total_order : TotalOrder Nat.LessOrEqual :=
  {| TotalOrder.partial_order :=
       {| PartialOrder.reflexivity :=
            {| Reflexive.reflexivity      := Nat.le_reflexivity |}
        ; PartialOrder.antisymmetry :=
            {| Antisymmetric.antisymmetry := Nat.le_antisymmetry |}
        ; PartialOrder.transitivity :=
            {| Transitive.transitivity    := Nat.le_transitivity |} |}
   ; TotalOrder.totality :=
       {| Total.totality := Nat.le_totality |} |}.

Instance Nat_min_semigroup : Semigroup Nat.min :=
  {| Semigroup.associativity := Nat.min_associativity |}.

Instance Nat_max_monoid : Monoid Nat.max One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.max_associativity |}
   ; Monoid.identity := Nat.max_identity |}.

Instance Nat_min_commutative : Commutative Nat.min :=
  {| Commutative.commutativity := Nat.min_commutativity |}.

Instance Nat_max_commutative : Commutative Nat.max :=
  {| Commutative.commutativity := Nat.max_commutativity |}.
