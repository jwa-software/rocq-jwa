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
Module NatWithZero.

(* No recursion here: [Zero] is the identity on both sides and the remaining
 * case is [Nat.add] under [Positive].
 *)
(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition add := fun (m : NatWithZero) (n : NatWithZero) =>
  match m with
  | Zero       => n
  | Positive p =>
      match n with
      | Zero       => Positive p
      | Positive q => Positive (Nat.add p q)
      end
  end.

(* [NatWithZero -> NatWithZero] *)
Definition inc := fun (n : NatWithZero) =>
  match n with
  | Zero       => Positive One
  | Positive p => Positive (Nat.inc p)
  end.

Lemma inc_specification : forall (n : NatWithZero), inc n = add (Positive One) n.
Proof.
  intros n.
  destruct n as [| p]; simpl in |- *; reflexivity.
Qed.

Theorem addition_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
    add (add l m) n = add l (add m n).
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
        rewrite Nat.addition_associativity in |- *.
        reflexivity.
Qed.

Theorem addition_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), add m n = add n m.
Proof.
  intros m n.
  destruct m as [| m'].
  - simpl in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite Nat.addition_commutativity in |- *.
      reflexivity.
Qed.

Theorem addition_identity
  : forall (n : NatWithZero), (add Zero n = n) /\ (add n Zero = n).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (addition_commutativity n Zero) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem positive_injectivity
  : forall (m : Nat) (n : Nat), Positive m = Positive n -> m = n.
Proof.
  intros m n e.
  pose proof (Identity.congruence
                (fun (x : NatWithZero) => match x with | Zero => m | Positive y => y end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

Lemma addition_positive_refutes_zero
  : forall (m : NatWithZero) (n : Nat), ~ (add m (Positive n) = Zero).
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

Theorem add_l_cancellation
  : forall (n : NatWithZero) (m : NatWithZero) (k : NatWithZero),
      add n m = add n k -> m = k.
Proof.
  intros n m k.
  destruct n as [| n'].
  - simpl in |- *.
    intro e.
    exact e.
  - destruct m as [| m'].
    + destruct k as [| k'].
      * intro e.
        reflexivity.
      * simpl in |- *.
        intro e.
        pose proof (positive_injectivity n' (Nat.add n' k') e) as e'.
        pose proof (Identity.symmetry e') as e''.
        rewrite (Nat.addition_commutativity n' k') in e''.
        pose proof (Nat.addition_identity_absence k' n') as h.
        unfold Negation in h.
        pose proof (h e'') as f.
        contradiction f.
    + destruct k as [| k'].
      * simpl in |- *.
        intro e.
        pose proof (positive_injectivity (Nat.add n' m') n' e) as e'.
        rewrite (Nat.addition_commutativity n' m') in e'.
        pose proof (Nat.addition_identity_absence m' n') as h.
        unfold Negation in h.
        pose proof (h e') as f.
        contradiction f.
      * simpl in |- *.
        intro e.
        pose proof (positive_injectivity (Nat.add n' m') (Nat.add n' k') e)
          as e'.
        pose proof (Nat.add_l_cancellation n' m' k' e') as e''.
        rewrite e'' in |- *.
        reflexivity.
Qed.

Theorem add_r_cancellation
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      add m n = add k n -> m = k.
Proof.
  intros m k n e.
  rewrite (addition_commutativity m n) in e.
  rewrite (addition_commutativity k n) in e.
  exact (add_l_cancellation n m k e).
Qed.

Theorem addition_cancellation
  : forall (m : NatWithZero) (n : NatWithZero) (k : NatWithZero),
    (add m n = add m k -> n = k) /\ (add m n = add k n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (add_l_cancellation m n k).
  - exact (add_r_cancellation m k n).
Qed.

Lemma add_l_commutativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      add l (add m n) = add m (add l n).
Proof.
  intros l m n.
  rewrite (addition_commutativity l (add m n)) in |- *.
  rewrite (addition_associativity m n l) in |- *.
  rewrite (addition_commutativity n l) in |- *.
  reflexivity.
Qed.

Theorem addition_interchange
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      add (add a b) (add c d) = add (add a c) (add b d).
Proof.
  intros a b c d.
  rewrite (addition_associativity a b (add c d)) in |- *.
  rewrite (add_l_commutativity b c d) in |- *.
  rewrite (addition_associativity a c (add b d)) in |- *.
  reflexivity.
Qed.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition mul := fun (m : NatWithZero) (n : NatWithZero) =>
  match m with
  | Zero       => Zero
  | Positive p =>
      match n with
      | Zero       => Zero
      | Positive q => Positive (Nat.mul p q)
      end
  end.

Lemma mul_l_identity : forall (n : NatWithZero), mul (Positive One) n = n.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma mul_r_identity : forall (m : NatWithZero), mul m (Positive One) = m.
Proof.
  intros m.
  destruct m as [| m'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication_commutativity m' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem multiplication_identity
  : forall (n : NatWithZero), (mul (Positive One) n = n) /\ (mul n (Positive One) = n).
Proof.
  intros n.
  split.
  - exact (mul_l_identity n).
  - exact (mul_r_identity n).
Qed.

Theorem multiplication_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), mul m n = mul n m.
Proof.
  intros m n.
  destruct m as [| m'].
  - simpl in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.multiplication_commutativity m' n') in |- *.
      reflexivity.
Qed.

Theorem multiplication_annihilation
  : forall (n : NatWithZero), (mul Zero n = Zero) /\ (mul n Zero = Zero).
Proof.
  intros n.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (multiplication_commutativity n Zero) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem multiplication_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul (mul l m) n = mul l (mul m n).
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
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
Qed.

Theorem mul_l_distributivity_over_addition
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul l (add m n) = add (mul l m) (mul l n).
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
        rewrite (Nat.mul_l_distributivity_over_addition l' m' n') in |- *.
        reflexivity.
Qed.

Theorem mul_r_distributivity_over_addition
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul (add m n) l = add (mul m l) (mul n l).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity (add m n) l) in |- *.
  rewrite (mul_l_distributivity_over_addition l m n) in |- *.
  rewrite (multiplication_commutativity l m) in |- *.
  rewrite (multiplication_commutativity l n) in |- *.
  reflexivity.
Qed.

Theorem multiplication_distributivity_over_addition
  : forall (x : NatWithZero) (y : NatWithZero) (z : NatWithZero),
      (mul x (add y z) = add (mul x y) (mul x z))
    /\ (mul (add y z) x = add (mul y x) (mul z x)).
Proof.
  intros x y z.
  split.
  - exact (mul_l_distributivity_over_addition x y z).
  - exact (mul_r_distributivity_over_addition x y z).
Qed.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition power := fun (m : NatWithZero) (n : NatWithZero) =>
  match n with
  | Zero       => Positive One
  | Positive q =>
      match m with
      | Zero       => Zero
      | Positive p => Positive (Nat.power p q)
      end
  end.

Lemma power_identity : forall (m : NatWithZero), power m Zero = Positive One.
Proof.
  intros m.
  simpl in |- *.
  reflexivity.
Qed.

Theorem product_of_powers
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero),
      mul (power m a) (power m b) = power m (add a b).
Proof.
  intros m a b.
  destruct a as [| a'].
  - destruct b as [| b'].
    + simpl in |- *.
      reflexivity.
    + destruct m as [| m'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
  - destruct b as [| b'].
    + destruct m as [| m'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication_commutativity (Nat.power m' a') One) in |- *.
        simpl in |- *.
        reflexivity.
    + destruct m as [| m'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.product_of_powers m' a' b') in |- *.
        reflexivity.
Qed.

Theorem power_of_a_power
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero),
      power (power m a) b = power m (mul a b).
Proof.
  intros m a b.
  destruct a as [| a'].
  - destruct b as [| b'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.power_annihilation b') in |- *.
      reflexivity.
  - destruct b as [| b'].
    + simpl in |- *.
      reflexivity.
    + destruct m as [| m'].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.power_of_a_power m' a' b') in |- *.
        reflexivity.
Qed.

Theorem power_distributivity_over_multiplication
  : forall (m : NatWithZero) (n : NatWithZero) (a : NatWithZero),
      power (mul m n) a = mul (power m a) (power n a).
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
        rewrite (Nat.power_distributivity_over_multiplication m' n' a') in |- *.
        reflexivity.
Qed.

(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessThan := fun (m : NatWithZero) (n : NatWithZero) =>
  exists (k : Nat), add m (Positive k) = n.

(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessOrEqual := fun (m : NatWithZero) (n : NatWithZero) =>
  m = n \/ LessThan m n.

Lemma lt_positive_embedding
  : forall (m : Nat) (n : Nat),
      LessThan (Positive m) (Positive n) <-> Nat.LessThan m n.
Proof.
  intros m n.
  split.
  - intro h.
    unfold LessThan in h.
    destruct h as [k e].
    simpl in e.
    pose proof (positive_injectivity (Nat.add m k) n e) as e'.
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

Theorem lt_irreflexivity : forall (n : NatWithZero), ~ (LessThan n n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  destruct n as [| n'].
  - simpl in e.
    discriminate e.
  - simpl in e.
    pose proof (positive_injectivity (Nat.add n' k) n' e) as e'.
    rewrite (Nat.addition_commutativity n' k) in e'.
    pose proof (Nat.addition_identity_absence k n') as i.
    unfold Negation in i.
    pose proof (i e') as f.
    contradiction f.
Qed.

Theorem lt_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  pose proof (Identity.symmetry e2) as e2'.
  rewrite e2' in |- *.
  pose proof (Identity.symmetry e1) as e1'.
  rewrite e1' in |- *.
  rewrite (addition_associativity l (Positive k1) (Positive k2)) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem addition_strict_monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessThan m n -> LessThan (add k m) (add k n).
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition_associativity k m (Positive d)) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

Theorem multiplication_strict_monotonicity
  : forall (k : Nat) (m : NatWithZero) (n : NatWithZero),
      LessThan m n -> LessThan (mul (Positive k) m) (mul (Positive k) n).
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul k d)).
  destruct m as [| m'].
  - simpl in e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    simpl in |- *.
    rewrite (Nat.mul_l_distributivity_over_addition k m' d) in |- *.
    reflexivity.
Qed.

Theorem addition_monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessOrEqual m n -> LessOrEqual (add k m) (add k n).
Proof.
  intros k m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    unfold LessOrEqual in |- *.
    exact (Disjunction.L (Identity.reflexivity (add k n))).
  - unfold LessOrEqual in |- *.
    apply Disjunction.R.
    exact (addition_strict_monotonicity k m n lt).
Qed.

Theorem addition_strict_cancellation
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessThan (add k m) (add k n) -> LessThan m n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  rewrite (addition_associativity k m (Positive d)) in e.
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  exact (add_l_cancellation k (add m (Positive d)) n e).
Qed.

Theorem addition_right_extensivity
  : forall (m : NatWithZero) (n : NatWithZero), LessOrEqual n (add m n).
Proof.
  intros m n.
  unfold LessOrEqual in |- *.
  destruct m as [| m'].
  - simpl in |- *.
    exact (Disjunction.L (Identity.reflexivity n)).
  - apply Disjunction.R.
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    exact (addition_commutativity n (Positive m')).
Qed.

Theorem addition_right_positivity
  : forall (n : NatWithZero) (k : Nat), LessThan Zero (add n (Positive k)).
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

Theorem lt_add_one_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      LessThan m (add n (Positive One)) <-> LessOrEqual m n.
Proof.
  intros m n.
  split.
  - intro h.
    unfold LessThan in h.
    destruct h as [k e].
    unfold LessOrEqual in |- *.
    destruct k as [| k'].
    + apply Disjunction.L.
      exact (add_r_cancellation m n (Positive One) e).
    + apply Disjunction.R.
      unfold LessThan in |- *.
      apply (Exists_introduction k').
      change (Positive (Successor k')) with (add (Positive One) (Positive k')) in e.
      rewrite (addition_commutativity (Positive One) (Positive k')) in e.
      pose proof (Identity.symmetry (addition_associativity m (Positive k') (Positive One)))
        as a.
      rewrite a in e.
      exact (add_r_cancellation (add m (Positive k')) n (Positive One) e).
  - intro h.
    unfold LessOrEqual in h.
    unfold LessThan in |- *.
    destruct h as [e | lt].
    + apply (Exists_introduction One).
      rewrite e in |- *.
      reflexivity.
    + unfold LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction (Successor k)).
      change (Positive (Successor k)) with (add (Positive One) (Positive k)) in |- *.
      rewrite (addition_commutativity (Positive One) (Positive k)) in |- *.
      pose proof (Identity.symmetry (addition_associativity m (Positive k) (Positive One))) as a.
      rewrite a in |- *.
      rewrite e in |- *.
      reflexivity.
Qed.

(* [NatWithZero -> NatWithZero -> Comparison] *)
Definition compare := fun (m : NatWithZero) (n : NatWithZero) =>
  match m with
  | Zero =>
      match n with
      | Zero       => Eq
      | Positive _ => Lt
      end
  | Positive p =>
      match n with
      | Zero       => Gt
      | Positive q => Nat.compare p q
      end
  end.

Theorem comparison_antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero),
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
    exact (Nat.comparison_antisymmetry m' n').
Qed.

Lemma lt_specification
  : forall (m : NatWithZero) (n : NatWithZero), compare m n = Lt <-> LessThan m n.
Proof.
  intros m n.
  destruct m as [| m']; destruct n as [| n'].
  - split.
    * simpl in |- *.
      intro e.
      discriminate e.
    * intro h.
      pose proof (lt_irreflexivity Zero) as i.
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
      exact (Biimplication.backward_elimination
               (lt_positive_embedding m' n')
               (Nat.lt_specification_forward m' n' e)).
    * intro h.
      simpl in |- *.
      exact (Nat.lt_specification_backward
              m'
              n'
              (Biimplication.forward_elimination
                (lt_positive_embedding m' n') h)).
Qed.

Lemma eq_specification
  : forall (m : NatWithZero) (n : NatWithZero), compare m n = Eq <-> m = n.
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
      rewrite (Nat.eq_specification_forward m' n' e) in |- *.
      reflexivity.
  - intro e.
    rewrite e in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (Comparable.reflexivity n').
Qed.

Theorem comparison_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      (compare m n = Lt <-> LessThan m n) /\ (compare m n = Eq <-> m = n).
Proof.
  intros m n.
  split.
  - exact (lt_specification m n).
  - exact (eq_specification m n).
Qed.

Instance comparable
  : Comparable compare LessThan :=
  {| Comparable.transitivity  := lt_transitivity
   ; Comparable.specification := comparison_specification
   ; Comparable.antisymmetry  := comparison_antisymmetry |}.

(* [NatWithZero -> NatWithZero -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* [NatWithZero -> NatWithZero -> Bool] *)
Abbreviation le := (Comparable.le compare).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Abbreviation min := (Comparable.min compare).

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Abbreviation max := (Comparable.max compare).

Lemma max_l_identity : forall (n : NatWithZero), max Zero n = n.
Proof.
  intros n.
  unfold Comparable.max in |- *.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma max_r_identity : forall (n : NatWithZero), max n Zero = n.
Proof.
  intros n.
  rewrite (Comparable.max_commutativity n Zero) in |- *.
  exact (max_l_identity n).
Qed.

Theorem max_identity
  : forall (n : NatWithZero), (max Zero n = n) /\ (max n Zero = n).
Proof.
  intros n.
  split.
  - exact (max_l_identity n).
  - exact (max_r_identity n).
Qed.

Lemma min_left_annihilation : forall (n : NatWithZero), min Zero n = Zero.
Proof.
  intros n.
  unfold Comparable.min in |- *.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

Lemma min_right_annihilation : forall (n : NatWithZero), min n Zero = Zero.
Proof.
  intros n.
  rewrite (Comparable.min_commutativity n Zero) in |- *.
  exact (min_left_annihilation n).
Qed.

Theorem min_annihilation
  : forall (n : NatWithZero), (min Zero n = Zero) /\ (min n Zero = Zero).
Proof.
  intros n.
  split.
  - exact (min_left_annihilation n).
  - exact (min_right_annihilation n).
Qed.

Theorem addition_left_distributivity_over_min
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      add k (min m n) = min (add k m) (add k n).
Proof.
  intros k m n.
  pose proof (Comparable.le_totality m n) as t.
  destruct t as [h | h].
  - rewrite (Biimplication.backward_elimination
              (Comparable.min_specification m n)
              h) in |- *.
    rewrite (Biimplication.backward_elimination
               (Comparable.min_specification (add k m) (add k n))
               (addition_monotonicity k m n h)) in |- *.
    reflexivity.
  - rewrite (Comparable.min_commutativity m n) in |- *.
    rewrite (Comparable.min_commutativity
              (add k m)
              (add k n)) in |- *.
    rewrite (Biimplication.backward_elimination
              (Comparable.min_specification n m)
              h) in |- *.
    rewrite (Biimplication.backward_elimination
               (Comparable.min_specification (add k n) (add k m))
               (addition_monotonicity k n m h)) in |- *.
    reflexivity.
Qed.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition saturating_sub := fun (m : NatWithZero) (n : NatWithZero) =>
  match m with
  | Zero       => Zero
  | Positive p =>
      match n with
      | Zero       => Positive p
      | Positive q =>
          match Nat.sub p q with
          | None   => Zero
          | Some k => Positive k
          end
      end
  end.

Theorem saturating_subtraction_inversion_of_addition
  : forall (m : NatWithZero) (n : NatWithZero), saturating_sub (add m n) n = m.
Proof.
  intros m n.
  destruct n as [| n']; destruct m as [| m'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.sub_truncation n' n' (Comparable.le_reflexivity n')) in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.subtraction_inversion_of_addition m' n') in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem saturating_sub_truncation
  : forall (m : NatWithZero) (n : NatWithZero), LessOrEqual m n -> saturating_sub m n = Zero.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.sub_truncation n' n' (Comparable.le_reflexivity n')) in |- *.
      simpl in |- *.
      reflexivity.
  - unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.sub_truncation
                m' (Nat.add m' k)
                (Disjunction.R (Nat.addition_left_extensivity m' k))) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

Theorem saturating_subtraction_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      LessOrEqual n m -> add n (saturating_sub m n) = m.
Proof.
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - rewrite e in |- *.
    rewrite (saturating_sub_truncation m m (Comparable.le_reflexivity m)) in |- *.
    destruct m as [| m']; simpl in |- *; reflexivity.
  - unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (addition_commutativity n (Positive k)) in |- *.
    rewrite (saturating_subtraction_inversion_of_addition (Positive k) n) in |- *.
    rewrite (addition_commutativity n (Positive k)) in |- *.
    reflexivity.
Qed.

Theorem saturating_sub_r_identity : forall (n : NatWithZero), saturating_sub n Zero = n.
Proof.
  intros n.
  destruct n as [| n']; simpl in |- *; reflexivity.
Qed.

Theorem saturating_sub_cancellation
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      saturating_sub (add k m) (add k n) = saturating_sub m n.
Proof.
  intros k m n.
  destruct k as [| k'].
  - simpl in |- *. reflexivity.
  - destruct m as [| m']; destruct n as [| n'].
    + simpl in |- *.
      rewrite (Nat.sub_truncation k' k'
                (Comparable.le_reflexivity k')) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.sub_truncation k' (Nat.add k' n')
                 (Disjunction.R (Nat.addition_left_extensivity k' n'))) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.addition_commutativity k' m') in |- *.
      rewrite (Nat.subtraction_inversion_of_addition m' k') in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.sub_cancellation k' m' n') in |- *.
      reflexivity.
Qed.

(* [NatWithZero -> NatWithZero -> Option NatWithZero] *)
Definition sub := fun (m : NatWithZero) (n : NatWithZero) =>
  match le n m with
  | true  => Some (saturating_sub m n)
  | false => None
  end.

Theorem sub_truncation
  : forall (m : NatWithZero) (n : NatWithZero), LessThan m n -> sub m n = None.
Proof.
  intros m n h.
  unfold sub in |- *.
  destruct (le n m) as [|] eqn:c.
  - pose proof (Biimplication.forward_elimination (Comparable.le_reflection n m) c)
      as order.
    unfold Comparable.LessOrEqual in order.
    destruct order as [e | lt].
    + rewrite e in h.
      pose proof (lt_irreflexivity m) as i.
      unfold Negation in i.
      pose proof (i h) as f.
      contradiction f.
    + pose proof (Comparable.lt_asymmetry m n h) as a.
      unfold Negation in a.
      pose proof (a lt) as f.
      contradiction f.
  - reflexivity.
Qed.

Theorem subtraction_inversion_of_addition
  : forall (m : NatWithZero) (n : NatWithZero), sub (add m n) n = Some m.
Proof.
  intros m n.
  unfold sub in |- *.
  rewrite (saturating_subtraction_inversion_of_addition m n) in |- *.
  rewrite (Biimplication.backward_elimination
            (Comparable.le_reflection n (add m n))
            (addition_right_extensivity m n)) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem subtraction_specification
  : forall (m : NatWithZero) (n : NatWithZero) (k : NatWithZero),
      sub m n = Some k <-> add n k = m.
Proof.
  intros m n k.
  split.
  - intro e.
    unfold sub in e.
    destruct (le n m) as [|] eqn:c.
    + pose proof (Option.some_injectivity NatWithZero (saturating_sub m n) k e) as e'.
      pose proof (Biimplication.forward_elimination (Comparable.le_reflection n m) c) as order.
      rewrite <- e' in |- *.
      exact (saturating_subtraction_specification m n order).
    + discriminate e.
  - intro e.
    rewrite <- e in |- *.
    rewrite (addition_commutativity n k) in |- *.
    exact (subtraction_inversion_of_addition k n).
Qed.

(* Euclidean division of a positive by a positive, by walking the dividend
 * down: each step adds one to the remainder, and the quotient goes up when
 * the remainder reaches the divisor. The divisor is a [Nat], so it is never
 * zero. The result is the pair of quotient and remainder.
 *)
Fixpoint division (dividend : Nat) (divisor : Nat) : Product NatWithZero NatWithZero :=
  match dividend with
  | One =>
      match divisor with
      | One         => Product_introduction (Positive One) Zero
      | Successor _ => Product_introduction Zero (Positive One)
      end
  | Successor dividend' =>
      match division dividend' divisor with
      | Product_introduction quotient remainder =>
          match eq (inc remainder) (Positive divisor) with
          | true  => Product_introduction (inc quotient) Zero
          | false => Product_introduction quotient       (inc remainder)
          end
      end
  end.

Local Open Scope jwa_product_scope.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition divide := fun (n : NatWithZero) (divisor : Nat) =>
  match n with
  | Zero              => Zero
  | Positive dividend => pi_1 (division dividend divisor)
  end.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition modulo := fun (n : NatWithZero) (divisor : Nat) =>
  match n with
  | Zero              => Zero
  | Positive dividend => pi_2 (division dividend divisor)
  end.

Lemma division_invariant
  : forall (p : Nat) (d : Nat),
      (add (mul (pi_1 (division p d)) (Positive d)) (pi_2 (division p d))
      = Positive p)
      /\ LessThan (pi_2 (division p d)) (Positive d).
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
    destruct (eq (inc r) (Positive d)) as [|] eqn:E; split; simpl in |- *.
    * pose proof (Biimplication.forward_elimination
                    (Comparable.eq_reflection (inc r) (Positive d))
                    E) as full.
      rewrite (inc_specification r) in full.
      rewrite (inc_specification q) in |- *.
      rewrite (mul_r_distributivity_over_addition (Positive d) (Positive One) q) in |- *.
      rewrite (mul_l_identity (Positive d)) in |- *.
      rewrite (addition_commutativity (Positive d) (mul q (Positive d))) in |- *.
      rewrite (addition_commutativity
                 (add (mul q (Positive d)) (Positive d))
                 Zero) in |- *.
      simpl in |- *.
      pose proof (Identity.symmetry full) as full'.
      rewrite full' in |- *.
      rewrite full' in e.
      rewrite (add_l_commutativity
                 (mul q (add (Positive One) r)) (Positive One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
    * rewrite (inc_specification r) in |- *.
      rewrite (add_l_commutativity (mul q (Positive d)) (Positive One) r) in |- *.
      rewrite e in |- *.
      simpl in |- *.
      reflexivity.
    * unfold LessThan in lt.
      destruct lt as [k ek].
      rewrite (inc_specification r) in E.
      rewrite (addition_commutativity (Positive One) r) in E.
      rewrite (inc_specification r) in |- *.
      rewrite (addition_commutativity (Positive One) r) in |- *.
      destruct k as [| k'].
      { rewrite (Biimplication.backward_elimination
                   (Comparable.eq_reflection (add r (Positive One)) (Positive d))
                   ek) in E.
        discriminate E. }
      { unfold LessThan in |- *.
        apply (Exists_introduction k').
        rewrite (addition_associativity r (Positive One) (Positive k')) in |- *.
        simpl in |- *.
        exact ek. }
Qed.

(* Quotient and remainder as the two halves of the invariant; a [Zero]
 * dividend has both [Zero].
 *)
Theorem division_specification
  : forall (n : NatWithZero) (d : Nat),
      (add (mul (divide n d) (Positive d)) (modulo n d) = n)
      /\ LessThan (modulo n d) (Positive d).
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
  - unfold divide in |- *.
    unfold modulo in |- *.
    exact (division_invariant p d).
Qed.

(* Divisibility: [d] divides [n] when some multiple of [d] is [n]. It is a
 * partial order: reflexive with [Positive One], transitive by multiplying
 * the witnesses, antisymmetric since [One] is the only unit.
 *)
(* [NatWithZero -> NatWithZero -> Prop] *)
Definition Divides := fun (d : NatWithZero) (n : NatWithZero) =>
  exists (k : NatWithZero), mul d k = n.

Theorem divides_reflexivity : forall (n : NatWithZero), Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (Positive One)).
  exact (mul_r_identity n).
Qed.

Theorem divides_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (mul k1 k2)).
  pose proof (Identity.symmetry (multiplication_associativity l k1 k2)) as a.
  rewrite a in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

Theorem divides_antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero), Divides m n -> Divides n m -> m = n.
Proof.
  intros m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
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
        pose proof (positive_injectivity (Nat.mul (Nat.mul p k') j') p e2) as e3.
        rewrite (Nat.multiplication_associativity p k' j') in e3.
        pose proof (Nat.multiplication_commutativity One p) as c.
        simpl in c.
        pose proof (Identity.transitivity e3 c) as e4.
        pose proof (Nat.mul_l_cancellation p (Nat.mul k' j') One e4) as e5.
        pose proof (Nat.multiplication_identity_factorization k' j' e5) as f.
        destruct f as [ek ej].
        rewrite ek in e1.
        rewrite (mul_r_identity (Positive p)) in e1.
        exact e1.
Qed.

Theorem divides_addition_closure
  : forall (d : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides d m -> Divides d n -> Divides d (add m n).
Proof.
  intros d m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (add k1 k2)).
  rewrite (mul_l_distributivity_over_addition d k1 k2) in |- *.
  rewrite e1 in |- *.
  rewrite e2 in |- *.
  reflexivity.
Qed.

Theorem divides_multiplication_closure
  : forall (d : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides d m -> Divides d (mul m n).
Proof.
  intros d m n h.
  unfold Divides in h.
  destruct h as [k e].
  unfold Divides in |- *.
  apply (Exists_introduction (mul k n)).
  pose proof (Identity.symmetry (multiplication_associativity d k n)) as a.
  rewrite a in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

Theorem divides_bottom : forall (n : NatWithZero), Divides (Positive One) n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction n).
  exact (mul_l_identity n).
Qed.

Theorem divides_top : forall (n : NatWithZero), Divides n Zero.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction Zero).
  rewrite (multiplication_commutativity n Zero) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

(* [NatWithZero -> Prop] *)
Definition Even := fun (n : NatWithZero) => Divides (Positive (Successor One)) n.

(* [NatWithZero -> Prop] *)
Definition Odd := fun (n : NatWithZero) =>
  exists (k : NatWithZero), add (mul (Positive (Successor One)) k) (Positive One) = n.

Theorem even_or_odd : forall (n : NatWithZero), Even n \/ Odd n.
Proof.
  intros n.
  destruct n as [| p].
  - apply Disjunction.L.
    unfold Even in |- *.
    unfold Divides in |- *.
    apply (Exists_introduction Zero).
    simpl in |- *.
    reflexivity.
  - induction p as [| p' IH] using Nat_induction.
    + apply Disjunction.R.
      unfold Odd in |- *.
      apply (Exists_introduction Zero).
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
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in odd.
        destruct odd as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction (add k (Positive One))).
        rewrite (mul_l_distributivity_over_addition
                   (Positive (Successor One)) k (Positive One)) in |- *.
        change (mul (Positive (Successor One)) (Positive One))
          with (add (Positive One) (Positive One)) in |- *.
        pose proof (Identity.symmetry
                      (addition_associativity
                         (mul (Positive (Successor One)) k)
                         (Positive One) (Positive One))) as a.
        rewrite a in |- *.
        rewrite e in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
Qed.

Theorem even_add_even
  : forall (m : NatWithZero) (n : NatWithZero), Even m -> Even n -> Even (add m n).
Proof.
  intros m n h1 h2.
  unfold Even in h1.
  unfold Even in h2.
  unfold Even in |- *.
  exact (divides_addition_closure (Positive (Successor One)) m n h1 h2).
Qed.

Theorem odd_add_odd
  : forall (m : NatWithZero) (n : NatWithZero), Odd m -> Odd n -> Even (add m n).
Proof.
  intros m n h1 h2.
  unfold Odd in h1.
  unfold Odd in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Even in |- *.
  unfold Divides in |- *.
  apply (Exists_introduction (add (add k1 k2) (Positive One))).
  pose proof (Identity.symmetry e1) as e1'.
  pose proof (Identity.symmetry e2) as e2'.
  rewrite e1' in |- *.
  rewrite e2' in |- *.
  rewrite (mul_l_distributivity_over_addition
             (Positive (Successor One)) (add k1 k2) (Positive One)) in |- *.
  rewrite (mul_l_distributivity_over_addition (Positive (Successor One)) k1 k2) in |- *.
  change (mul (Positive (Successor One)) (Positive One))
    with (add (Positive One) (Positive One)) in |- *.
  rewrite (addition_interchange
             (mul (Positive (Successor One)) k1) (Positive One)
             (mul (Positive (Successor One)) k2) (Positive One)) in |- *.
  reflexivity.
Qed.

End NatWithZero.

(* The scope is declared in [Core.Notations] and never opened: a client
 * writes [(m + n)%nat_with_zero]. [only parsing] keeps the operations
 * printed by name.
 *)
Notation "m + n" := (NatWithZero.add m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m * n" := (NatWithZero.mul m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m < n" := (NatWithZero.LessThan m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m <= n" := (NatWithZero.LessOrEqual m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m > n" := (NatWithZero.LessThan n m) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m >= n" := (NatWithZero.LessOrEqual n m) (only parsing)
  : jwa_nat_with_zero_scope.

(* Declared inside [Module NatWithZero], whose proofs use it; an instance
 * declared there is dropped at the module's [End], so it is announced again
 * here.
 *)
Existing Instance NatWithZero.comparable.

Instance NatWithZero_add_monoid
  : Monoid NatWithZero.add Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := NatWithZero.addition_associativity |}
  ; Monoid.identity := NatWithZero.addition_identity
  |}.

(* Both cancellation laws were already proved above, so the instance only
 * hands them over.
 *)
Instance NatWithZero_add_cancellative
  : Cancellative NatWithZero.add := {|
    Cancellative.cancellation := NatWithZero.addition_cancellation
  |}.

(* [Positive One] leaves its argument alone under [mul]. *)
Instance NatWithZero_mul_monoid
  : Monoid NatWithZero.mul (Positive One) := {|
    Monoid.semigroup := {|
      Semigroup.associativity := NatWithZero.multiplication_associativity |}
  ; Monoid.identity := NatWithZero.multiplication_identity |}.

Instance NatWithZero_add_commutative
  : Commutative NatWithZero.add := {|
      Commutative.commutativity := NatWithZero.addition_commutativity
  |}.

Instance NatWithZero_add_abelian_monoid
  : AbelianMonoid NatWithZero.add Zero :=
  {| AbelianMonoid.monoid      := NatWithZero_add_monoid
   ; AbelianMonoid.commutative := NatWithZero_add_commutative |}.

Instance NatWithZero_mul_commutative
  : Commutative NatWithZero.mul := {|
    Commutative.commutativity := NatWithZero.multiplication_commutativity
  |}.

Instance NatWithZero_min_semigroup
  : Semigroup NatWithZero.min :=
  {| Semigroup.associativity := Comparable.min_associativity |}.

Instance NatWithZero_max_monoid
  : Monoid NatWithZero.max Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Comparable.max_associativity |}
   ; Monoid.identity := NatWithZero.max_identity |}.

Instance NatWithZero_min_commutative
  : Commutative NatWithZero.min :=
  {| Commutative.commutativity := Comparable.min_commutativity |}.

Instance NatWithZero_max_commutative
  : Commutative NatWithZero.max :=
  {| Commutative.commutativity := Comparable.max_commutativity |}.

Instance NatWithZero_semiring
  : Semiring NatWithZero.add Zero NatWithZero.mul (Positive One) :=
  {| Semiring.abelian_monoid := NatWithZero_add_abelian_monoid
   ; Semiring.monoid         := NatWithZero_mul_monoid
   ; Semiring.distributivity := NatWithZero.multiplication_distributivity_over_addition
   ; Semiring.annihilation   := NatWithZero.multiplication_annihilation |}.

Instance NatWithZero_divides_partial_order
  : PartialOrder NatWithZero.Divides :=
  {| PartialOrder.reflexivity :=
       {| Reflexive.reflexivity := NatWithZero.divides_reflexivity |}
   ; PartialOrder.antisymmetry :=
       {| Antisymmetric.antisymmetry := NatWithZero.divides_antisymmetry |}
   ; PartialOrder.transitivity :=
       {| Transitive.transitivity := NatWithZero.divides_transitivity |} |}.
