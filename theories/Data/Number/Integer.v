(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.

Inductive Integer : Type :=
  | Negative : Nat -> Integer
  | Zero     : Integer
  | Positive : Nat -> Integer.

(* The eliminator behind [destruct], written out: no recursion, since no
 * ctor carries an [Integer].
 *)
Definition Integer_induction
  : forall (P : Integer -> Prop) .
      (forall (p : Nat) . P (Negative p)) ->
      P Zero ->
      (forall (p : Nat) . P (Positive p)) ->
      forall (x : Integer) . P x
  := fun (P : Integer -> Prop)
         (negative : forall (p : Nat) . P (Negative p))
         (zero : P Zero)
         (positive : forall (p : Nat) . P (Positive p))
         (x : Integer) =>
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* A module may carry the type's name; its members read [Integer.add]. *)
Module Integer.

(* Short spellings for this module only: [Local] keeps them out of every
 * file that imports this one. [+ p] and [- p] are prefixes, apart from the
 * infix [+]; the ctors of [NatWithZero] keep their qualified names.
 *)
Local Notation "0" := Zero (only parsing).
Local Notation "+ p" := (Positive p) (at level 35, right associativity, only parsing).
Local Notation "- p" := (Negative p) (at level 35, right associativity, only parsing).

Lemma negative_injectivity
  : forall (p : Nat) (q : Nat) . (- p) = - q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) =>
                   match x with | - r => r | 0 => p | + _ => p end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

Lemma positive_injectivity
  : forall (p : Nat) (q : Nat) . (+ p) = + q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) =>
                   match x with | - _ => p | 0 => p | + r => r end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem magnitude_injectivity
  : forall (p : Nat) (q : Nat) .
      (- p = - q -> p = q) /\ (+ p = + q -> p = q).
Proof.
  intros p q.
  split.
  - exact (negative_injectivity p q).
  - exact (positive_injectivity p q).
Qed.

(* [Integer -> Integer] *)
Definition negate := fun (x : Integer) =>
  match x with
  | - p => + p
  | 0   => 0
  | + p => - p
  end.

Theorem negate_involution : forall (x : Integer) . negate (negate x) = x.
Proof.
  intros x.
  destruct x as [p | | n]; simpl in |- *; reflexivity.
Qed.

(* [Integer -> NatWithZero] *)
Definition abs := fun (x : Integer) =>
  match x with
  | - p => NatWithZero.Positive p
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive p
  end.

(* The bars of the magnitude, in parentheses: a bare [| x |] would be read
 * as the opening of a [match] arm, and [|| x ||] would take the [||] of
 * [Bool.or] away, both of them everywhere and not only where this scope is
 * open.
 *)
Notation "(| x |)" := (abs x) (only parsing)
  : jwa_integer_scope.

(* [Nat -> Integer] *)
Definition from_nat := fun (n : Nat) => + n.

(* [NatWithZero -> Integer] *)
Definition from_nat_with_zero := fun (n : NatWithZero) =>
  match n return Integer with
  | NatWithZero.Zero       => 0
  | NatWithZero.Positive p => + p
  end.

Theorem from_nat_with_zero_injectivity
  : forall (m : NatWithZero) (n : NatWithZero) .
      from_nat_with_zero m = from_nat_with_zero n -> m = n.
Proof.
  intros m n e.
  destruct m as [| p]; destruct n as [| q].
  - reflexivity.
  - simpl in e.
    discriminate e.
  - simpl in e.
    discriminate e.
  - simpl in e.
    pose proof (positive_injectivity p q e) as e'.
    rewrite e' in |- *.
    reflexivity.
Qed.

(* [Integer -> NatWithZero] *)
Definition ramp := fun (x : Integer) =>
  match x with
  | - _ => NatWithZero.Zero
  | 0   => NatWithZero.Zero
  | + p => NatWithZero.Positive p
  end.

(* Difference *)

(* [Nat -> Nat -> Integer] *)
Fixpoint nat_difference (p : Nat) (q : Nat) : Integer :=
  match p, q with
  | One, One                   => 0
  | One, Successor q'          => - q'
  | Successor p', One          => + p'
  | Successor p', Successor q' => nat_difference p' q'
  end.

Lemma nat_difference_reflexivity : forall (n : Nat) . nat_difference n n = 0.
Proof.
  intros n.
  induction n as [| n' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact IH.
Qed.

Lemma nat_difference_l_inversion_of_addition
  : forall (k : Nat) (p : Nat) . nat_difference (Nat.add k p) p = + k.
Proof.
  intros k p.
  induction p as [| p' IH] using Nat_induction.
  - rewrite (Nat.addition_commutativity k One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (Nat.addition_commutativity k (Successor p')) in |- *.
    simpl in |- *.
    rewrite (Nat.addition_commutativity p' k) in |- *.
    exact IH.
Qed.

Lemma nat_difference_r_inversion_of_addition
  : forall (k : Nat) (p : Nat) . nat_difference p (Nat.add k p) = - k.
Proof.
  intros k p.
  induction p as [| p' IH] using Nat_induction.
  - rewrite (Nat.addition_commutativity k One) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (Nat.addition_commutativity k (Successor p')) in |- *.
    simpl in |- *.
    rewrite (Nat.addition_commutativity p' k) in |- *.
    exact IH.
Qed.

Lemma nat_difference_well_definedness
  : forall (p : Nat) (q : Nat) (r : Nat) (s : Nat) .
      Nat.add p s = Nat.add r q -> nat_difference p q = nat_difference r s.
Proof.
  intros p q r s h.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in h |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (nat_difference_r_inversion_of_addition k p) in |- *.
    rewrite (Nat.add_l_commutativity r p k) in h.
    pose proof (Nat.add_l_cancellation p s (Nat.add r k) h) as e''.
    rewrite e'' in |- *.
    rewrite (Nat.addition_commutativity r k) in |- *.
    rewrite (nat_difference_r_inversion_of_addition k r) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in h |- *.
      rewrite (nat_difference_reflexivity q) in |- *.
      rewrite (Nat.addition_commutativity r q) in h.
      pose proof (Nat.add_l_cancellation q s r h) as e.
      rewrite e in |- *.
      rewrite (nat_difference_reflexivity r) in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in h |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (nat_difference_l_inversion_of_addition k q) in |- *.
      rewrite (Nat.addition_associativity q k s) in h.
      rewrite (Nat.addition_commutativity r q) in h.
      pose proof (Nat.add_l_cancellation q (Nat.add k s) r h) as e''.
      pose proof (Identity.symmetry e'') as e'''.
      rewrite e''' in |- *.
      rewrite (nat_difference_l_inversion_of_addition k s) in |- *.
      reflexivity.
Qed.

Lemma nat_difference_negation
  : forall (p : Nat) (q : Nat) . negate (nat_difference p q) = nat_difference q p.
Proof.
  intros p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (nat_difference_r_inversion_of_addition k p) in |- *.
    rewrite (nat_difference_l_inversion_of_addition k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (nat_difference_reflexivity q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (nat_difference_l_inversion_of_addition k q) in |- *.
      rewrite (nat_difference_r_inversion_of_addition k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

Lemma nat_difference_specification
  : forall (p : Nat) (q : Nat) .
      NatWithZero.add (ramp (nat_difference p q)) (NatWithZero.Positive q)
    = NatWithZero.add (ramp (negate (nat_difference p q))) (NatWithZero.Positive p).
Proof.
  intros p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (nat_difference_r_inversion_of_addition k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (nat_difference_reflexivity q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (nat_difference_l_inversion_of_addition k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

Lemma nat_difference_negative_specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = - k <-> Nat.add p k = q.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (nat_difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q (Nat.add k p) s) as e'.
    rewrite (Nat.addition_commutativity p k) in |- *.
    exact (Identity.symmetry e').
  - intro e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    exact (nat_difference_r_inversion_of_addition k p).
Qed.

Lemma nat_difference_zero_specification
  : forall (p : Nat) (q : Nat) . nat_difference p q = 0 <-> p = q.
Proof.
  intros p q.
  split.
  - intro e.
    pose proof (nat_difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q p s) as e'.
    exact (Identity.symmetry e').
  - intro e.
    rewrite e in |- *.
    exact (nat_difference_reflexivity q).
Qed.

Lemma nat_difference_positive_specification
  : forall (p : Nat) (q : Nat) (k : Nat) . nat_difference p q = + k <-> Nat.add q k = p.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (nat_difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity (Nat.add k q) p s) as e'.
    rewrite (Nat.addition_commutativity q k) in |- *.
    exact e'.
  - intro e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity q k) in |- *.
    exact (nat_difference_l_inversion_of_addition k q).
Qed.

(* [NatWithZero -> NatWithZero -> Integer] *)
Definition nat_with_zero_difference := fun (a : NatWithZero) (b : NatWithZero) =>
  match a, b with
  | NatWithZero.Zero, NatWithZero.Zero             => 0
  | NatWithZero.Zero, NatWithZero.Positive q       => - q
  | NatWithZero.Positive p, NatWithZero.Zero       => + p
  | NatWithZero.Positive p, NatWithZero.Positive q => nat_difference p q
  end.

Lemma nat_with_zero_difference_reflexivity
  : forall (n : NatWithZero) . nat_with_zero_difference n n = 0.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (nat_difference_reflexivity p).
Qed.

Lemma nat_with_zero_difference_l_inversion_of_addition
  : forall (k : Nat) (a : NatWithZero) .
      nat_with_zero_difference (NatWithZero.add (NatWithZero.Positive k) a) a = + k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (nat_difference_l_inversion_of_addition k q).
Qed.

Lemma nat_with_zero_difference_r_inversion_of_addition
  : forall (k : Nat) (a : NatWithZero) .
      nat_with_zero_difference a (NatWithZero.add (NatWithZero.Positive k) a) = - k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (nat_difference_r_inversion_of_addition k q).
Qed.

Lemma nat_with_zero_difference_specification
  : forall (a : NatWithZero) (b : NatWithZero) .
      NatWithZero.add (ramp (nat_with_zero_difference a b)) b
      = NatWithZero.add (ramp (negate (nat_with_zero_difference a b))) a.
Proof.
  intros a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (nat_difference_specification p q).
Qed.

Lemma nat_with_zero_difference_well_definedness
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero) .
      NatWithZero.add a d = NatWithZero.add c b ->
      nat_with_zero_difference a b = nat_with_zero_difference c d.
Proof.
  intros a b c d h.
  destruct a as [| p]; destruct b as [| q].
  - simpl in h.
    rewrite (NatWithZero.addition_commutativity c NatWithZero.Zero) in h.
    simpl in h.
    rewrite h in |- *.
    rewrite (nat_with_zero_difference_reflexivity c) in |- *.
    simpl in |- *.
    reflexivity.
  - simpl in h.
    rewrite h in |- *.
    rewrite (NatWithZero.addition_commutativity c (NatWithZero.Positive q)) in |- *.
    rewrite (nat_with_zero_difference_r_inversion_of_addition q c) in |- *.
    simpl in |- *.
    reflexivity.
  - rewrite (NatWithZero.addition_commutativity c NatWithZero.Zero) in h.
    change (NatWithZero.add NatWithZero.Zero c) with c in h.
    pose proof (Identity.symmetry h) as h'.
    rewrite h' in |- *.
    rewrite (nat_with_zero_difference_l_inversion_of_addition p d) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct c as [| r]; destruct d as [| s].
    + simpl in h.
      pose proof (NatWithZero.positive_injectivity p q h) as e.
      rewrite e in |- *.
      simpl in |- *.
      rewrite (nat_difference_reflexivity q) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive_injectivity (Nat.add p s) q h) as e.
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      simpl in |- *.
      rewrite (Nat.addition_commutativity p s) in |- *.
      rewrite (nat_difference_r_inversion_of_addition s p) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive_injectivity p (Nat.add r q) h) as e.
      rewrite e in |- *.
      simpl in |- *.
      rewrite (nat_difference_l_inversion_of_addition r q) in |- *.
      reflexivity.
    + simpl in h.
      pose proof (NatWithZero.positive_injectivity (Nat.add p s) (Nat.add r q) h) as e.
      simpl in |- *.
      exact (nat_difference_well_definedness p q r s e).
Qed.

Lemma nat_with_zero_difference_negation
  : forall (a : NatWithZero) (b : NatWithZero) .
      negate (nat_with_zero_difference a b) = nat_with_zero_difference b a.
Proof.
  intros a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (nat_difference_negation p q).
Qed.

(* Addition *)

(* [Integer -> Integer -> Integer] *)
Definition add := fun (m : Integer) (n : Integer) =>
  nat_with_zero_difference (NatWithZero.add (ramp m) (ramp n))
                           (NatWithZero.add (ramp (negate m)) (ramp (negate n))).

(* The scope is declared in [Core.Notations] and opened only inside this
 * module; after [End Integer] a client writes [(m + n)%integer]. [only
 * parsing] keeps goals printing the operations by name.
 *)
Notation "m + n" := (add m n) (only parsing)
  : jwa_integer_scope.

Local Open Scope jwa_integer_scope.

Theorem nat_with_zero_difference_additivity
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero) .
      nat_with_zero_difference a b + nat_with_zero_difference c d
      = nat_with_zero_difference (NatWithZero.add a c) (NatWithZero.add b d).
Proof.
  intros a b c d.
  unfold add in |- *.
  apply (nat_with_zero_difference_well_definedness
           (NatWithZero.add (ramp (nat_with_zero_difference a b))
                            (ramp (nat_with_zero_difference c d)))
           (NatWithZero.add (ramp (negate (nat_with_zero_difference a b)))
                            (ramp (negate (nat_with_zero_difference c d))))
           (NatWithZero.add a c) (NatWithZero.add b d)).
  rewrite (NatWithZero.addition_interchange
             (ramp (nat_with_zero_difference a b)) (ramp (nat_with_zero_difference c d))
             b d) in |- *.
  rewrite (nat_with_zero_difference_specification a b) in |- *.
  rewrite (nat_with_zero_difference_specification c d) in |- *.
  rewrite (NatWithZero.addition_interchange
             (ramp (negate (nat_with_zero_difference a b))) a
             (ramp (negate (nat_with_zero_difference c d))) c) in |- *.
  rewrite (NatWithZero.addition_commutativity
             (NatWithZero.add (ramp (negate (nat_with_zero_difference a b)))
                              (ramp (negate (nat_with_zero_difference c d))))
             (NatWithZero.add a c)) in |- *.
  reflexivity.
Qed.

Theorem add_l_identity : forall (n : Integer) . 0 + n = n.
Proof.
  intros n.
  destruct n as [n' | | n']; unfold add in |- *; simpl in |- *; reflexivity.
Qed.

Theorem addition_associativity
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (l + m) + n = l + (m + n).
Proof.
  intros l m n.
  pose proof (Identity.symmetry (add_l_identity l)) as el.
  pose proof (Identity.symmetry (add_l_identity m)) as em.
  pose proof (Identity.symmetry (add_l_identity n)) as en.
  change (0 + l) with (nat_with_zero_difference (ramp l) (ramp (negate l))) in el.
  change (0 + m) with (nat_with_zero_difference (ramp m) (ramp (negate m))) in em.
  change (0 + n) with (nat_with_zero_difference (ramp n) (ramp (negate n))) in en.
  rewrite el, em, en in |- *.
  rewrite (nat_with_zero_difference_additivity
             (ramp l) (ramp (negate l)) (ramp m) (ramp (negate m))) in |- *.
  rewrite (nat_with_zero_difference_additivity
             (NatWithZero.add (ramp l) (ramp m))
             (NatWithZero.add (ramp (negate l)) (ramp (negate m)))
             (ramp n) (ramp (negate n))) in |- *.
  rewrite (nat_with_zero_difference_additivity
             (ramp m) (ramp (negate m)) (ramp n) (ramp (negate n))) in |- *.
  rewrite (nat_with_zero_difference_additivity
             (ramp l) (ramp (negate l))
             (NatWithZero.add (ramp m) (ramp n))
             (NatWithZero.add (ramp (negate m)) (ramp (negate n)))) in |- *.
  rewrite (NatWithZero.addition_associativity
             (ramp l)
             (ramp m)
             (ramp n)) in |- *.
  rewrite (NatWithZero.addition_associativity
             (ramp (negate l))
             (ramp (negate m))
             (ramp (negate n))) in |- *.
  reflexivity.
Qed.

Theorem addition_commutativity
  : forall (m : Integer) (n : Integer) . m + n = n + m.
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (NatWithZero.addition_commutativity
            (ramp m)
            (ramp n)) in |- *.
  rewrite (NatWithZero.addition_commutativity
            (ramp (negate m))
            (ramp (negate n))) in |- *.
  reflexivity.
Qed.

Lemma addition_left_commutativity
  : forall (l : Integer) (m : Integer) (n : Integer) . l + (m + n) = m + (l + n).
Proof.
  intros l m n.
  rewrite (addition_commutativity l (m + n)) in |- *.
  rewrite (addition_associativity m n l)     in |- *.
  rewrite (addition_commutativity n l)       in |- *.
  reflexivity.
Qed.

Theorem addition_interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer) .
      (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  rewrite (addition_associativity a b (c + d)) in |- *.
  rewrite (addition_left_commutativity b c d)  in |- *.
  rewrite (addition_associativity a c (b + d)) in |- *.
  reflexivity.
Qed.

Theorem add_r_identity : forall (n : Integer) . n + 0 = n.
Proof.
  intros n.
  rewrite (addition_commutativity n 0) in |- *.
  exact (add_l_identity n).
Qed.

Theorem addition_identity
  : forall (n : Integer) . (0 + n = n) /\ (n + 0 = n).
Proof.
  intros n.
  split.
  - exact (add_l_identity n).
  - exact (add_r_identity n).
Qed.

Theorem add_l_inverse : forall (n : Integer) . negate n + n = 0.
Proof.
  intros n.
  destruct n as [p | | p].
  - unfold add in |- *.
    simpl in |- *.
    exact (nat_difference_reflexivity p).
  - unfold add in |- *.
    simpl in |- *.
    reflexivity.
  - unfold add in |- *.
    simpl in |- *.
    exact (nat_difference_reflexivity p).
Qed.

Theorem add_r_inverse : forall (n : Integer) . n + negate n = 0.
Proof.
  intros n.
  rewrite (addition_commutativity n (negate n)) in |- *.
  exact (add_l_inverse n).
Qed.

Theorem addition_inverse
  : forall (n : Integer) . (negate n + n = 0) /\ (n + negate n = 0).
Proof.
  intros n.
  split.
  - exact (add_l_inverse n).
  - exact (add_r_inverse n).
Qed.

Theorem add_l_cancellation
  : forall (k : Integer) (m : Integer) (n : Integer) . k + m = k + n -> m = n.
Proof.
  intros k m n h.
  pose proof (Identity.congruence (add (negate k)) h) as h'.
  pose proof (Identity.symmetry (addition_associativity (negate k) k m)) as a1.
  rewrite a1 in h'.
  pose proof (Identity.symmetry (addition_associativity (negate k) k n)) as a2.
  rewrite a2 in h'.
  rewrite (add_l_inverse k) in h'.
  rewrite (add_l_identity m) in h'.
  rewrite (add_l_identity n) in h'.
  exact h'.
Qed.

Theorem add_r_cancellation
  : forall (m : Integer) (n : Integer) (k : Integer) . m + k = n + k -> m = n.
Proof.
  intros m n k h.
  rewrite (addition_commutativity m k) in h.
  rewrite (addition_commutativity n k) in h.
  exact (add_l_cancellation k m n h).
Qed.

Theorem addition_cancellation
  : forall (m : Integer) (n : Integer) (k : Integer) .
    (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (add_l_cancellation m n k).
  - exact (add_r_cancellation m k n).
Qed.

Theorem negate_additivity
  : forall (m : Integer) (n : Integer) . negate (m + n) = negate m + negate n.
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (nat_with_zero_difference_negation
             (NatWithZero.add (ramp m) (ramp n))
             (NatWithZero.add (ramp (negate m)) (ramp (negate n)))) in |- *.
  rewrite (negate_involution m) in |- *.
  rewrite (negate_involution n) in |- *.
  reflexivity.
Qed.

(* Subtraction *)

(* [Integer -> Integer -> Integer] *)
Definition sub := fun (m : Integer) (n : Integer) => m + negate n.

Theorem subtraction_inversion_of_addition
  : forall (m : Integer) (n : Integer) . sub (m + n) n = m.
Proof.
  intros m n.
  unfold sub in |- *.
  rewrite (addition_associativity m n (negate n)) in |- *.
  rewrite (add_r_inverse n) in |- *.
  exact (add_r_identity m).
Qed.

(* Multiplication *)

(* [Integer -> Integer -> Integer] *)
Definition mul := fun (m : Integer) (n : Integer) =>
  match m with
  | - p =>
      match n with
      | - q => + (Nat.mul p q)
      | 0   => 0
      | + q => - (Nat.mul p q)
      end
  | 0 => 0
  | + p =>
      match n with
      | - q => - (Nat.mul p q)
      | 0   => 0
      | + q => + (Nat.mul p q)
      end
  end.

Notation "m * n" := (mul m n) (only parsing)
  : jwa_integer_scope.

Theorem multiplication_commutativity
  : forall (m : Integer) (n : Integer) . m * n = n * m.
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    rewrite (Nat.multiplication_commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication_commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication_commutativity m' n') in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (Nat.multiplication_commutativity m' n') in |- *.
    reflexivity.
Qed.

Theorem multiplication_associativity
  : forall (l : Integer) (m : Integer) (n : Integer) . (l * m) * n = l * (m * n).
Proof.
  intros l m n.
  destruct l as [l' | | l'].
  - destruct m as [m' | | m'].
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *.
        reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
    + simpl in |- *. reflexivity.
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
  - simpl in |- *. reflexivity.
  - destruct m as [m' | | m'].
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
    + simpl in |- *. reflexivity.
    + destruct n as [n' | | n'].
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
      *
        simpl in |- *. reflexivity.
      *
        simpl in |- *.
        rewrite (Nat.multiplication_associativity l' m' n') in |- *.
        reflexivity.
Qed.

Theorem mul_l_identity : forall (n : Integer) . (+ One) * n = n.
Proof.
  intros n.
  destruct n as [n' | | n']; simpl in |- *; reflexivity.
Qed.

Theorem mul_r_identity : forall (n : Integer) . n * (+ One) = n.
Proof.
  intros n.
  rewrite (multiplication_commutativity n (+ One)) in |- *.
  exact (mul_l_identity n).
Qed.

Theorem multiplication_identity
  : forall (n : Integer) . ((+ One) * n = n) /\ (n * (+ One) = n).
Proof.
  intros n.
  split.
  - exact (mul_l_identity n).
  - exact (mul_r_identity n).
Qed.

Theorem multiplication_left_absorption : forall (n : Integer) . 0 * n = 0.
Proof.
  intros n.
  simpl in |- *.
  reflexivity.
Qed.

Theorem multiplication_right_absorption : forall (n : Integer) . n * 0 = 0.
Proof.
  intros n.
  rewrite (multiplication_commutativity n 0) in |- *.
  exact (multiplication_left_absorption n).
Qed.

(* Negating a factor negates the product: the signs say so under every
 * ctor pair.
 *)
Theorem multiplication_left_negation
  : forall (m : Integer) (n : Integer) . negate m * n = negate (m * n).
Proof.
  intros m n.
  destruct m as [m' | | m'].
  - destruct n as [n' | | n']; simpl in |- *; reflexivity.
  - simpl in |- *. reflexivity.
  - destruct n as [n' | | n']; simpl in |- *; reflexivity.
Qed.

Theorem multiplication_right_negation
  : forall (m : Integer) (n : Integer) . m * negate n = negate (m * n).
Proof.
  intros m n.
  rewrite (multiplication_commutativity m (negate n)) in |- *.
  rewrite (multiplication_left_negation n m) in |- *.
  rewrite (multiplication_commutativity n m) in |- *.
  reflexivity.
Qed.

Lemma nat_difference_scaling
  : forall (k : Nat) (p : Nat) (q : Nat) .
      (+ k) * nat_difference p q = nat_difference (Nat.mul k p) (Nat.mul k q).
Proof.
  intros k p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [j e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p j) in |- *.
    rewrite (nat_difference_r_inversion_of_addition j p) in |- *.
    simpl in |- *.
    rewrite (Nat.mul_l_distributivity_over_addition k j p) in |- *.
    rewrite (nat_difference_r_inversion_of_addition (Nat.mul k j) (Nat.mul k p)) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (nat_difference_reflexivity q) in |- *.
      rewrite (nat_difference_reflexivity (Nat.mul k q)) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [j e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q j) in |- *.
      rewrite (nat_difference_l_inversion_of_addition j q) in |- *.
      simpl in |- *.
      rewrite (Nat.mul_l_distributivity_over_addition k j q) in |- *.
      rewrite (nat_difference_l_inversion_of_addition (Nat.mul k j) (Nat.mul k q)) in |- *.
      reflexivity.
Qed.

Lemma nat_with_zero_difference_scaling
  : forall (k : Nat) (a : NatWithZero) (b : NatWithZero) .
      (+ k) * nat_with_zero_difference a b
      = nat_with_zero_difference (NatWithZero.mul (NatWithZero.Positive k) a)
                                 (NatWithZero.mul (NatWithZero.Positive k) b).
Proof.
  intros k a b.
  destruct a as [| p]; destruct b as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - change (nat_with_zero_difference
              (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive p))
              (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive q)))
      with (nat_difference (Nat.mul k p) (Nat.mul k q))
      in |- *.
    change (nat_with_zero_difference
              (NatWithZero.Positive p)
              (NatWithZero.Positive q))
      with (nat_difference p q)
      in |- *.
    exact (nat_difference_scaling k p q).
Qed.

Lemma ramp_scaling
  : forall (k : Nat) (x : Integer) .
      ramp ((+ k) * x) = NatWithZero.mul (NatWithZero.Positive k) (ramp x).
Proof.
  intros k x.
  destruct x as [x' | | x']; simpl in |- *; reflexivity.
Qed.

Lemma multiplication_positive_left_distributivity_over_add
  : forall (k : Nat) (m : Integer) (n : Integer) .
      (+ k) * (m + n) = ((+ k) * m) + ((+ k) * n).
Proof.
  intros k m n.
  unfold add in |- *.
  rewrite (nat_with_zero_difference_scaling k
             (NatWithZero.add (ramp m) (ramp n))
             (NatWithZero.add (ramp (negate m)) (ramp (negate n)))) in |- *.
  rewrite (NatWithZero.mul_l_distributivity_over_addition
             (NatWithZero.Positive k) (ramp m) (ramp n)) in |- *.
  rewrite (NatWithZero.mul_l_distributivity_over_addition
             (NatWithZero.Positive k) (ramp (negate m)) (ramp (negate n))) in |- *.
  rewrite (ramp_scaling k m) in |- *.
  rewrite (ramp_scaling k n) in |- *.
  pose proof (Identity.symmetry (multiplication_right_negation (+ k) m)) as nm.
  pose proof (Identity.symmetry (multiplication_right_negation (+ k) n)) as nn.
  rewrite nm in |- *.
  rewrite nn in |- *.
  rewrite (ramp_scaling k (negate m)) in |- *.
  rewrite (ramp_scaling k (negate n)) in |- *.
  reflexivity.
Qed.

Theorem mul_l_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer) .
      l * (m + n) = (l * m) + (l * n).
Proof.
  intros l m n.
  destruct l as [p | | p].
  - change (- p) with (negate (+ p)) in |- *.
    rewrite (multiplication_left_negation (+ p) (m + n)) in |- *.
    rewrite (multiplication_left_negation (+ p) m) in |- *.
    rewrite (multiplication_left_negation (+ p) n) in |- *.
    pose proof (Identity.symmetry
                  (negate_additivity ((+ p) * m) ((+ p) * n))) as e.
    rewrite e in |- *.
    rewrite (multiplication_positive_left_distributivity_over_add p m n) in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (add_l_identity 0) in |- *.
    reflexivity.
  - exact (multiplication_positive_left_distributivity_over_add p m n).
Qed.

Theorem mul_r_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer) .
      (m + n) * l = (m * l) + (n * l).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity (m + n) l) in |- *.
  rewrite (mul_l_distributivity_over_add l m n) in |- *.
  rewrite (multiplication_commutativity l m) in |- *.
  rewrite (multiplication_commutativity l n) in |- *.
  reflexivity.
Qed.

Theorem multiplication_distributivity_over_addition
  : forall (x : Integer) (y : Integer) (z : Integer) .
      (x * (y + z) = (x * y) + (x * z))
    /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  split.
  - exact (mul_l_distributivity_over_add x y z).
  - exact (mul_r_distributivity_over_add x y z).
Qed.

(* Order *)

(* [Integer -> Integer -> Prop] *)
Definition LessThan := fun (m : Integer) (n : Integer) =>
  exists (k : Nat) . m + (+ k) = n.

(* [Integer -> Integer -> Prop] *)
Definition LessOrEqual := fun (m : Integer) (n : Integer) => m = n \/ LessThan m n.

Notation "m < n" := (LessThan m n) (only parsing)
  : jwa_integer_scope.
Notation "m <= n" := (LessOrEqual m n) (only parsing)
  : jwa_integer_scope.

(* The reversed spellings name no new relation: [m > n] is [n < m] with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "m > n" := (LessThan n m) (only parsing)
  : jwa_integer_scope.
Notation "m >= n" := (LessOrEqual n m) (only parsing)
  : jwa_integer_scope.

Theorem lt_irreflexivity : forall (n : Integer) . ~ (n < n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  pose proof (Identity.transitivity e (Identity.symmetry (add_r_identity n)))
    as e'.
  pose proof (add_l_cancellation n (+ k) 0 e') as f.
  discriminate f.
Qed.

Theorem lt_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer) .
      l < m -> m < n -> l < n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  change (+ (Nat.add k1 k2)) with ((+ k1) + (+ k2)) in |- *.
  pose proof (Identity.symmetry (addition_associativity l (+ k1) (+ k2))) as a.
  rewrite a in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

Theorem addition_strict_monotonicity
  : forall (k : Integer) (m : Integer) (n : Integer) .
      m < n -> k + m < k + n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (addition_associativity k m (+ d)) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

Theorem multiplication_strict_monotonicity
  : forall (p : Nat) (m : Integer) (n : Integer) .
      m < n -> (+ p) * m < (+ p) * n.
Proof.
  intros p m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul p d)).
  change (+ (Nat.mul p d)) with ((+ p) * (+ d)) in |- *.
  pose proof (Identity.symmetry
                (mul_l_distributivity_over_add (+ p) m (+ d))) as dist.
  rewrite dist in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Comparison *)

(* [Integer -> Integer -> Comparison] *)
Definition compare := fun (m : Integer) (n : Integer) =>
  match m with
  | - p =>
      match n with
      | - q => Nat.compare q p
      | 0   => Lt
      | + _ => Lt
      end
  | 0 =>
      match n with
      | - _ => Gt
      | 0   => Eq
      | + _ => Lt
      end
  | + p =>
      match n with
      | - _ => Gt
      | 0   => Gt
      | + q => Nat.compare p q
      end
  end.

Theorem comparison_antisymmetry
  : forall (m : Integer) (n : Integer) . compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    exact (Nat.comparison_antisymmetry n' m').
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
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
  : forall (m : Integer) (n : Integer) . compare m n = Lt <-> m < n.
Proof.
  intros m n.
  unfold LessThan in |- *.
  unfold add in |- *.
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    split.
    * intro c.
      pose proof (Nat.lt_specification_forward n' m' c) as lt.
      unfold Nat.LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction k).
      rewrite (Nat.addition_commutativity n' k) in e.
      exact (<-elim (nat_difference_negative_specification k m' n') e).
    * intro h.
      destruct h as [k e].
      pose proof (->elim (nat_difference_negative_specification k m' n') e) as e'.
      apply (Nat.lt_specification_backward n' m').
      unfold Nat.LessThan in |- *.
      apply (Exists_introduction k).
      rewrite (Nat.addition_commutativity n' k) in |- *.
      exact e'.
  - simpl in |- *.
    split.
    * intro c.
      apply (Exists_introduction m').
      exact (nat_difference_reflexivity m').
    * intro h.
      reflexivity.
  - simpl in |- *.
    split.
    * intro c.
      apply (Exists_introduction (Nat.add n' m')).
      exact (nat_difference_l_inversion_of_addition n' m').
    * intro h.
      reflexivity.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro h.
      destruct h as [k e].
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro h.
      destruct h as [k e].
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      apply (Exists_introduction n').
      reflexivity.
    * intro h.
      reflexivity.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro h.
      destruct h as [k e].
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro h.
      destruct h as [k e].
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      pose proof (Nat.lt_specification_forward m' n' c) as lt.
      unfold Nat.LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction k).
      rewrite e in |- *.
      reflexivity.
    * intro h.
      destruct h as [k e].
      pose proof (positive_injectivity (Nat.add m' k) n' e) as e'.
      apply (Nat.lt_specification_backward m' n').
      unfold Nat.LessThan in |- *.
      apply (Exists_introduction k).
      exact e'.
Qed.

Lemma eq_specification
  : forall (m : Integer) (n : Integer) . compare m n = Eq <-> m = n.
Proof.
  intros m n.
  destruct m as [m' | | m']; destruct n as [n' | | n'].
  - simpl in |- *.
    split.
    * intro c.
      pose proof (Nat.eq_specification_forward n' m' c) as e.
      rewrite e in |- *.
      reflexivity.
    * intro e.
      pose proof (negative_injectivity m' n' e) as e'.
      rewrite e' in |- *.
      exact (Comparable.reflexivity n').
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      reflexivity.
    * intro e.
      reflexivity.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      discriminate c.
    * intro e.
      discriminate e.
  - simpl in |- *.
    split.
    * intro c.
      pose proof (Nat.eq_specification_forward m' n' c) as e.
      rewrite e in |- *.
      reflexivity.
    * intro e.
      pose proof (positive_injectivity m' n' e) as e'.
      rewrite e' in |- *.
      exact (Comparable.reflexivity n').
Qed.

Theorem comparison_specification
  : forall (m : Integer) (n : Integer) .
      (compare m n = Lt <-> m < n) /\ (compare m n = Eq <-> m = n).
Proof.
  intros m n.
  split.
  - exact (lt_specification m n).
  - exact (eq_specification m n).
Qed.

(* [Integer -> Integer -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* Divisibility *)

(* [Integer -> Integer -> Prop] *)
Definition Divides := fun (d : Integer) (n : Integer) => exists (k : Integer) . d * k = n.

Theorem divides_reflexivity : forall (n : Integer) . Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (+ One)).
  exact (mul_r_identity n).
Qed.

Theorem divides_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer) .
      Divides l m -> Divides m n -> Divides l n.
Proof.
  intros l m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 * k2)).
  pose proof (Identity.symmetry (multiplication_associativity l k1 k2)) as a.
  rewrite a in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

Theorem divides_addition_closure
  : forall (d : Integer) (m : Integer) (n : Integer) .
      Divides d m -> Divides d n -> Divides d (m + n).
Proof.
  intros d m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (k1 + k2)).
  rewrite (mul_l_distributivity_over_add d k1 k2) in |- *.
  rewrite e1 in |- *.
  rewrite e2 in |- *.
  reflexivity.
Qed.

Theorem divides_multiplication_closure
  : forall (d : Integer) (m : Integer) (n : Integer) . Divides d m -> Divides d (m * n).
Proof.
  intros d m n h.
  unfold Divides in h.
  destruct h as [k e].
  unfold Divides in |- *.
  apply (Exists_introduction (k * n)).
  pose proof (Identity.symmetry (multiplication_associativity d k n)) as a.
  rewrite a in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Parity *)

(* [Integer -> Prop] *)
Definition Even := fun (n : Integer) => Divides (+ (Successor One)) n.

(* [Integer -> Prop] *)
Definition Odd := fun (n : Integer) =>
  exists (k : Integer) . ((+ (Successor One)) * k) + (+ One) = n.

Theorem even_or_odd : forall (n : Integer) . Even n \/ Odd n.
Proof.
  intros n.
  destruct n as [p | | p].
  - induction p as [| p' IH] using Nat_induction.
    + apply Disjunction.R.
      unfold Odd in |- *.
      apply (Exists_introduction (- One)).
      unfold add in |- *.
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.R.
        unfold Even in ev.
        unfold Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction (k + (- One))).
        rewrite (mul_l_distributivity_over_add
                   (+ (Successor One)) k (- One)) in |- *.
        change ((+ (Successor One)) * (- One))
          with (- (Successor One)) in |- *.
        rewrite e in |- *.
        rewrite (addition_associativity (- p') (- (Successor One)) (+ One))
          in |- *.
        change ((- (Successor One)) + (+ One)) with (- One) in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction k).
        pose proof (Identity.congruence (fun (x : Integer) => x + (- One)) e)
          as e'.
        change ((((+ (Successor One)) * k) + (+ One)) + (- One)
                = (- p') + (- One)) in e'.
        rewrite (addition_associativity
                   ((+ (Successor One)) * k) (+ One) (- One)) in e'.
        change ((+ One) + (- One)) with 0 in e'.
        rewrite (add_r_identity ((+ (Successor One)) * k)) in e'.
        rewrite e' in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
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
      unfold add in |- *.
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.R.
        unfold Even in ev.
        unfold Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction k).
        rewrite e in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.L.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction (k + (+ One))).
        rewrite (mul_l_distributivity_over_add
                   (+ (Successor One)) k (+ One)) in |- *.
        change ((+ (Successor One)) * (+ One))
          with ((+ One) + (+ One)) in |- *.
        pose proof (Identity.symmetry
                      (addition_associativity
                         ((+ (Successor One)) * k) (+ One) (+ One)))
          as a.
        rewrite a in |- *.
        rewrite e in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
Qed.

Theorem even_addition_even
  : forall (m : Integer) (n : Integer) . Even m -> Even n -> Even (m + n).
Proof.
  intros m n h1 h2.
  unfold Even in h1.
  unfold Even in h2.
  unfold Even in |- *.
  exact (divides_addition_closure (+ (Successor One)) m n h1 h2).
Qed.

Theorem odd_addition_odd
  : forall (m : Integer) (n : Integer) . Odd m -> Odd n -> Even (m + n).
Proof.
  intros m n h1 h2.
  unfold Odd in h1.
  unfold Odd in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Even in |- *.
  unfold Divides in |- *.
  apply (Exists_introduction ((k1 + k2) + (+ One))).
  pose proof (Identity.symmetry e1) as e1'.
  pose proof (Identity.symmetry e2) as e2'.
  rewrite e1' in |- *.
  rewrite e2' in |- *.
  rewrite (mul_l_distributivity_over_add
             (+ (Successor One)) (k1 + k2) (+ One)) in |- *.
  rewrite (mul_l_distributivity_over_add (+ (Successor One)) k1 k2) in |- *.
  change ((+ (Successor One)) * (+ One))
    with ((+ One) + (+ One)) in |- *.
  rewrite (addition_interchange
             ((+ (Successor One)) * k1) (+ One)
             ((+ (Successor One)) * k2) (+ One)) in |- *.
  reflexivity.
Qed.

End Integer.

(* Makes the notations declared in [Module Integer] usable in every file that
 * imports this one, as [(m + n)%integer] or under an opened
 * [jwa_integer_scope]. Only the notations are exported: [add] and the laws
 * still need the [Integer.] prefix, and the local aliases [0], [+ p] and
 * [- p] stay inside the module.
 *)
Export (notations) Integer.

Instance Integer_comparable
  : Comparable Integer.compare Integer.LessThan :=
  {| Comparable.transitivity  := Integer.lt_transitivity
   ; Comparable.specification := Integer.comparison_specification
   ; Comparable.antisymmetry  := Integer.comparison_antisymmetry |}.

Instance Integer_add_monoid : Monoid Integer.add Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.addition_associativity |}
   ; Monoid.identity := Integer.addition_identity |}.

Instance Integer_add_cancellative : Cancellative Integer.add :=
  {| Cancellative.cancellation := Integer.addition_cancellation |}.

Instance Integer_add_commutative : Commutative Integer.add :=
  {| Commutative.commutativity := Integer.addition_commutativity |}.

Instance Integer_mul_monoid : Monoid Integer.mul (Positive One) :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.multiplication_associativity |}
   ; Monoid.identity := Integer.multiplication_identity |}.

Instance Integer_mul_commutative : Commutative Integer.mul :=
  {| Commutative.commutativity := Integer.multiplication_commutativity |}.

Instance Integer_add_group
  : Group Integer.add Zero Integer.negate :=
  {| Group.monoid  := Integer_add_monoid
   ; Group.inverse := Integer.addition_inverse |}.

Instance Integer_add_abelian_group
  : AbelianGroup Integer.add Zero Integer.negate :=
  {| AbelianGroup.group       := Integer_add_group
   ; AbelianGroup.commutative := Integer_add_commutative |}.

Instance Integer_ring
  : Ring Integer.add Zero Integer.negate Integer.mul (Positive One) :=
  {| Ring.abelian_group  := Integer_add_abelian_group
   ; Ring.monoid         := Integer_mul_monoid
   ; Ring.distributivity := Integer.multiplication_distributivity_over_addition |}.
