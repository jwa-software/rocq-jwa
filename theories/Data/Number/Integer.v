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
  : forall (P : Integer -> Prop),
      (forall (p : Nat), P (Negative p)) ->
      P Zero ->
      (forall (p : Nat), P (Positive p)) ->
      forall (x : Integer), P x
  := fun (P : Integer -> Prop)
         (negative : forall (p : Nat), P (Negative p))
         (zero : P Zero)
         (positive : forall (p : Nat), P (Positive p))
         (x : Integer) =>
       match x with
       | Negative p => negative p
       | Zero       => zero
       | Positive p => positive p
       end.

(* A module may carry the type's name; its members read [Integer.add]. *)
Module Integer.

(* The two magnitude ctors are injective, as [NatWithZero.Positive] is:
 * a function that reads the magnitude back is applied to both sides.
 *)

Theorem negative_injectivity
  : forall (p : Nat) (q : Nat), Negative p = Negative q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) =>
                   match x with | Negative r => r | Zero => p | Positive _ => p end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem positive_injectivity
  : forall (p : Nat) (q : Nat), Positive p = Positive q -> p = q.
Proof.
  intros p q e.
  pose proof (Identity.congruence
                (fun (x : Integer) =>
                   match x with | Negative _ => p | Zero => p | Positive r => r end)
                e) as e'.
  simpl in e'.
  exact e'.
Qed.

(* Negation swaps the two magnitude ctors and fixes [Zero]. *)
(* [Integer -> Integer] *)
Definition negate := fun (x : Integer) =>
  match x with
  | Negative p => Positive p
  | Zero       => Zero
  | Positive p => Negative p
  end.

Theorem negate_involution : forall (x : Integer), negate (negate x) = x.
Proof.
  intros x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

(* The magnitude with its sign dropped. *)
(* [Integer -> NatWithZero] *)
Definition absolute := fun (x : Integer) =>
  match x with
  | Negative p => NatWithZero.Positive p
  | Zero       => NatWithZero.Zero
  | Positive p => NatWithZero.Positive p
  end.

(* The embedding of the numbers with zero: [Zero] to [Zero], a positive to
 * the positive of the same magnitude.
 *)
(* [NatWithZero -> Integer] *)
Definition from_nat_with_zero := fun (n : NatWithZero) =>
  match n return Integer with
  | NatWithZero.Zero       => Zero
  | NatWithZero.Positive p => Positive p
  end.

Theorem from_nat_with_zero_injectivity
  : forall (m : NatWithZero) (n : NatWithZero),
      from_nat_with_zero m = from_nat_with_zero n -> m = n.
Proof.
  intros m n e.
  destruct m as [| p].
  - destruct n as [| q].
    + reflexivity.
    + simpl in e.
      discriminate e.
  - destruct n as [| q].
    + simpl in e.
      discriminate e.
    + simpl in e.
      pose proof (positive_injectivity p q e) as e'.
      rewrite e' in |- *.
      reflexivity.
Qed.

(* The positive part and the negative part: the magnitude on that side,
 * [Zero] on the other. An integer is its positive part less its negative
 * part, which is what [from_difference] below reads back.
 *)

(* [Integer -> NatWithZero] *)
Definition positive_part := fun (x : Integer) =>
  match x with
  | Negative _ => NatWithZero.Zero
  | Zero       => NatWithZero.Zero
  | Positive p => NatWithZero.Positive p
  end.

(* [Integer -> NatWithZero] *)
Definition negative_part := fun (x : Integer) =>
  match x with
  | Negative p => NatWithZero.Positive p
  | Zero       => NatWithZero.Zero
  | Positive _ => NatWithZero.Zero
  end.

Lemma positive_part_negation
  : forall (x : Integer), positive_part (negate x) = negative_part x.
Proof.
  intros x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma negative_part_negation
  : forall (x : Integer), negative_part (negate x) = positive_part x.
Proof.
  intros x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

(* The difference of two positives, walking both down together: the one
 * left standing gives the sign, and what is left of it the magnitude.
 *)
(* [Nat -> Nat -> Integer] *)
Fixpoint difference (p : Nat) (q : Nat) : Integer :=
  match p, q with
  | One, One                   => Zero
  | One, Successor q'          => Negative q'
  | Successor p', One          => Positive p'
  | Successor p', Successor q' => difference p' q'
  end.

Lemma difference_diagonal : forall (n : Nat), difference n n = Zero.
Proof.
  intros n.
  induction n as [| n' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact IH.
Qed.

(* Taking one summand of a sum away leaves the other, with the sign of the
 * side the sum stood on.
 *)

Lemma difference_of_sum_left
  : forall (k : Nat) (p : Nat), difference (Nat.add k p) p = Positive k.
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

Lemma difference_of_sum_right
  : forall (k : Nat) (p : Nat), difference p (Nat.add k p) = Negative k.
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

(* Two pairs with the same cross sums have the same difference: the
 * quotient's well-definedness, proved by placing [p] against [q] with
 * trichotomy and reading the other pair off the cross sums.
 *)
Lemma difference_well_definedness
  : forall (p : Nat) (q : Nat) (r : Nat) (s : Nat),
      Nat.add p s = Nat.add r q -> difference p q = difference r s.
Proof.
  intros p q r s h.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in h.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    rewrite (Nat.add_l_commutativity r p k) in h.
    pose proof (Nat.add_l_cancellation p s (Nat.add r k) h) as e''.
    rewrite e'' in |- *.
    rewrite (Nat.addition_commutativity r k) in |- *.
    rewrite (difference_of_sum_right k r) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in h.
      rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      rewrite (Nat.addition_commutativity r q) in h.
      pose proof (Nat.add_l_cancellation q s r h) as e.
      rewrite e in |- *.
      rewrite (difference_diagonal r) in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in h.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      rewrite (Nat.addition_associativity q k s) in h.
      rewrite (Nat.addition_commutativity r q) in h.
      pose proof (Nat.add_l_cancellation q (Nat.add k s) r h) as e''.
      pose proof (Identity.symmetry e'') as e'''.
      rewrite e''' in |- *.
      rewrite (difference_of_sum_left k s) in |- *.
      reflexivity.
Qed.

(* Swapping the two positives negates the difference. *)
Lemma difference_negation
  : forall (p : Nat) (q : Nat), negate (difference p q) = difference q p.
Proof.
  intros p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    rewrite (difference_of_sum_left k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      rewrite (difference_of_sum_right k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* The parts of a difference recover it: the positive part plus [q] is the
 * negative part plus [p], whichever side was larger.
 *)
Lemma difference_specification
  : forall (p : Nat) (q : Nat),
      NatWithZero.add (positive_part (difference p q)) (NatWithZero.Positive q)
      = NatWithZero.add (negative_part (difference p q)) (NatWithZero.Positive p).
Proof.
  intros p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* Each ctor a difference can answer with, read as an equation on the two
 * positives: the forward halves come off the specification with the answer
 * put in, the backward halves off the sum laws.
 *)

Lemma difference_negative_specification
  : forall (p : Nat) (q : Nat) (k : Nat), difference p q = Negative k <-> Nat.add p k = q.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q (Nat.add k p) s) as e'.
    rewrite (Nat.addition_commutativity p k) in |- *.
    exact (Identity.symmetry e').
  - intro e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p k) in |- *.
    exact (difference_of_sum_right k p).
Qed.

Lemma difference_zero_specification
  : forall (p : Nat) (q : Nat), difference p q = Zero <-> p = q.
Proof.
  intros p q.
  split.
  - intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q p s) as e'.
    exact (Identity.symmetry e').
  - intro e.
    rewrite e in |- *.
    exact (difference_diagonal q).
Qed.

Lemma difference_positive_specification
  : forall (p : Nat) (q : Nat) (k : Nat), difference p q = Positive k <-> Nat.add q k = p.
Proof.
  intros p q k.
  split.
  - intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity (Nat.add k q) p s) as e'.
    rewrite (Nat.addition_commutativity q k) in |- *.
    exact e'.
  - intro e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity q k) in |- *.
    exact (difference_of_sum_left k q).
Qed.

(* The integer [a] less [b], for two numbers with zero: a [Zero] on either
 * side is settled without recursion, two positives fall to [difference].
 *)
(* [NatWithZero -> NatWithZero -> Integer] *)
Definition from_difference := fun (a : NatWithZero) (b : NatWithZero) =>
  match a, b with
  | NatWithZero.Zero, NatWithZero.Zero             => Zero
  | NatWithZero.Zero, NatWithZero.Positive q       => Negative q
  | NatWithZero.Positive p, NatWithZero.Zero       => Positive p
  | NatWithZero.Positive p, NatWithZero.Positive q => difference p q
  end.

Lemma from_difference_parts_identity
  : forall (x : Integer), from_difference (positive_part x) (negative_part x) = x.
Proof.
  intros x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma from_difference_diagonal
  : forall (n : NatWithZero), from_difference n n = Zero.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference_diagonal p).
Qed.

Lemma from_difference_of_sum_left
  : forall (k : Nat) (a : NatWithZero),
      from_difference (NatWithZero.add (NatWithZero.Positive k) a) a = Positive k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference_of_sum_left k q).
Qed.

Lemma from_difference_of_sum_right
  : forall (k : Nat) (a : NatWithZero),
      from_difference a (NatWithZero.add (NatWithZero.Positive k) a) = Negative k.
Proof.
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (difference_of_sum_right k q).
Qed.

(* The parts of a difference recover it, lifted from [difference]. *)
Lemma from_difference_specification
  : forall (a : NatWithZero) (b : NatWithZero),
      NatWithZero.add (positive_part (from_difference a b)) b
      = NatWithZero.add (negative_part (from_difference a b)) a.
Proof.
  intros a b.
  destruct a as [| p].
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (difference_specification p q).
Qed.

(* Two pairs with the same cross sums have the same difference, lifted from
 * [difference]: a [Zero] on either side of one pair reads the other pair
 * off the cross sums, and four positives fall to the [Nat] law.
 *)
Lemma from_difference_well_definedness
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      NatWithZero.add a d = NatWithZero.add c b -> from_difference a b = from_difference c d.
Proof.
  intros a b c d h.
  destruct a as [| p].
  - destruct b as [| q].
    + simpl in h.
      rewrite (NatWithZero.addition_commutativity c NatWithZero.Zero) in h.
      simpl in h.
      rewrite h in |- *.
      rewrite (from_difference_diagonal c) in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in h.
      rewrite h in |- *.
      rewrite (NatWithZero.addition_commutativity c (NatWithZero.Positive q)) in |- *.
      rewrite (from_difference_of_sum_right q c) in |- *.
      simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + rewrite (NatWithZero.addition_commutativity c NatWithZero.Zero) in h.
      change (NatWithZero.add NatWithZero.Zero c) with c in h.
      pose proof (Identity.symmetry h) as h'.
      rewrite h' in |- *.
      rewrite (from_difference_of_sum_left p d) in |- *.
      simpl in |- *.
      reflexivity.
    + destruct c as [| r].
      * destruct d as [| s].
        { simpl in h.
          pose proof (NatWithZero.positive_injectivity p q h) as e.
          rewrite e in |- *.
          simpl in |- *.
          rewrite (difference_diagonal q) in |- *.
          reflexivity. }
        { simpl in h.
          pose proof (NatWithZero.positive_injectivity (Nat.add p s) q h) as e.
          pose proof (Identity.symmetry e) as e'.
          rewrite e' in |- *.
          simpl in |- *.
          rewrite (Nat.addition_commutativity p s) in |- *.
          rewrite (difference_of_sum_right s p) in |- *.
          reflexivity. }
      * destruct d as [| s].
        { simpl in h.
          pose proof (NatWithZero.positive_injectivity p (Nat.add r q) h) as e.
          rewrite e in |- *.
          simpl in |- *.
          rewrite (difference_of_sum_left r q) in |- *.
          reflexivity. }
        { simpl in h.
          pose proof (NatWithZero.positive_injectivity (Nat.add p s) (Nat.add r q) h)
            as e.
          simpl in |- *.
          exact (difference_well_definedness p q r s e). }
Qed.

Lemma from_difference_negation
  : forall (a : NatWithZero) (b : NatWithZero),
      negate (from_difference a b) = from_difference b a.
Proof.
  intros a b.
  destruct a as [| p].
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (difference_negation p q).
Qed.

(* Addition: an integer is its positive part less its negative part, and
 * two of them add part by part. The definition computes on ctors, so
 * [add (Positive p) (Positive q)] is [Positive (Nat.add p q)] and
 * [add (Positive p) (Negative q)] is [difference p q].
 *)
(* [Integer -> Integer -> Integer] *)
Definition add := fun (m : Integer) (n : Integer) =>
  from_difference (NatWithZero.add (positive_part m) (positive_part n))
                  (NatWithZero.add (negative_part m) (negative_part n)).

(* [from_difference] is additive: the sum of two differences is the
 * difference of the sums. [add] opens into the parts of the two
 * differences, which their specifications relate to [a], [b], [c] and [d];
 * the interchange law pairs them up for well-definedness.
 *)
Theorem from_difference_additivity
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      add (from_difference a b) (from_difference c d)
      = from_difference (NatWithZero.add a c) (NatWithZero.add b d).
Proof.
  intros a b c d.
  unfold add in |- *.
  apply (from_difference_well_definedness
           (NatWithZero.add (positive_part (from_difference a b))
                            (positive_part (from_difference c d)))
           (NatWithZero.add (negative_part (from_difference a b))
                            (negative_part (from_difference c d)))
           (NatWithZero.add a c) (NatWithZero.add b d)).
  rewrite (NatWithZero.addition_interchange
             (positive_part (from_difference a b)) (positive_part (from_difference c d))
             b d) in |- *.
  rewrite (from_difference_specification a b) in |- *.
  rewrite (from_difference_specification c d) in |- *.
  rewrite (NatWithZero.addition_interchange
             (negative_part (from_difference a b)) a
             (negative_part (from_difference c d)) c) in |- *.
  rewrite (NatWithZero.addition_commutativity
             (NatWithZero.add (negative_part (from_difference a b))
                              (negative_part (from_difference c d)))
             (NatWithZero.add a c)) in |- *.
  reflexivity.
Qed.

(* Associativity: each summand is the difference of its parts, additivity
 * folds each sum into one difference, and the components associate as
 * numbers with zero.
 *)
Theorem addition_associativity
  : forall (l : Integer) (m : Integer) (n : Integer),
      add (add l m) n = add l (add m n).
Proof.
  intros l m n.
  pose proof (Identity.symmetry (from_difference_parts_identity l)) as el.
  pose proof (Identity.symmetry (from_difference_parts_identity m)) as em.
  pose proof (Identity.symmetry (from_difference_parts_identity n)) as en.
  rewrite el in |- *.
  rewrite em in |- *.
  rewrite en in |- *.
  rewrite (from_difference_additivity
             (positive_part l) (negative_part l) (positive_part m) (negative_part m))
    in |- *.
  rewrite (from_difference_additivity
             (NatWithZero.add (positive_part l) (positive_part m))
             (NatWithZero.add (negative_part l) (negative_part m))
             (positive_part n) (negative_part n)) in |- *.
  rewrite (from_difference_additivity
             (positive_part m) (negative_part m) (positive_part n) (negative_part n))
    in |- *.
  rewrite (from_difference_additivity
             (positive_part l) (negative_part l)
             (NatWithZero.add (positive_part m) (positive_part n))
             (NatWithZero.add (negative_part m) (negative_part n))) in |- *.
  rewrite (NatWithZero.addition_associativity
             (positive_part l) (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.addition_associativity
             (negative_part l) (negative_part m) (negative_part n)) in |- *.
  reflexivity.
Qed.

Theorem addition_commutativity
  : forall (m : Integer) (n : Integer), add m n = add n m.
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (NatWithZero.addition_commutativity (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.addition_commutativity (negative_part m) (negative_part n)) in |- *.
  reflexivity.
Qed.

Lemma addition_left_commutativity
  : forall (l : Integer) (m : Integer) (n : Integer), add l (add m n) = add m (add l n).
Proof.
  intros l m n.
  rewrite (addition_commutativity l (add m n)) in |- *.
  rewrite (addition_associativity m n l) in |- *.
  rewrite (addition_commutativity n l) in |- *.
  reflexivity.
Qed.

(* The interchange law: two sums of two can be added pairwise across. *)
Theorem addition_interchange
  : forall (a : Integer) (b : Integer) (c : Integer) (d : Integer),
      add (add a b) (add c d) = add (add a c) (add b d).
Proof.
  intros a b c d.
  rewrite (addition_associativity a b (add c d)) in |- *.
  rewrite (addition_left_commutativity b c d) in |- *.
  rewrite (addition_associativity a c (add b d)) in |- *.
  reflexivity.
Qed.

(* [Zero] has no parts, so adding it adds nothing; the parts of [n] then
 * rebuild it.
 *)
Theorem addition_left_identity : forall (n : Integer), add Zero n = n.
Proof.
  intros n.
  unfold add in |- *.
  simpl in |- *.
  exact (from_difference_parts_identity n).
Qed.

Theorem addition_right_identity : forall (n : Integer), add n Zero = n.
Proof.
  intros n.
  rewrite (addition_commutativity n Zero) in |- *.
  exact (addition_left_identity n).
Qed.

Theorem addition_identity
  : forall (n : Integer), (add Zero n = n) /\ (add n Zero = n).
Proof.
  intros n.
  split.
  - exact (addition_left_identity n).
  - exact (addition_right_identity n).
Qed.

(* Negation is the inverse: the parts of [n] and of [negate n] add to the
 * same number on both sides, a difference on the diagonal.
 *)
Theorem addition_left_inverse : forall (n : Integer), add (negate n) n = Zero.
Proof.
  intros n.
  destruct n as [p | | p].
  - unfold add in |- *.
    simpl in |- *.
    exact (difference_diagonal p).
  - unfold add in |- *.
    simpl in |- *.
    reflexivity.
  - unfold add in |- *.
    simpl in |- *.
    exact (difference_diagonal p).
Qed.

Theorem addition_right_inverse : forall (n : Integer), add n (negate n) = Zero.
Proof.
  intros n.
  rewrite (addition_commutativity n (negate n)) in |- *.
  exact (addition_left_inverse n).
Qed.

Theorem addition_inverse
  : forall (n : Integer), (add (negate n) n = Zero) /\ (add n (negate n) = Zero).
Proof.
  intros n.
  split.
  - exact (addition_left_inverse n).
  - exact (addition_right_inverse n).
Qed.

(* Cancellation: [negate k] added in front of both sides of the equation
 * cancels [k], by associativity, the inverse and the identity.
 *)
Theorem addition_left_cancellation
  : forall (k : Integer) (m : Integer) (n : Integer), add k m = add k n -> m = n.
Proof.
  intros k m n h.
  pose proof (Identity.congruence (add (negate k)) h) as h'.
  pose proof (Identity.symmetry (addition_associativity (negate k) k m)) as a1.
  rewrite a1 in h'.
  pose proof (Identity.symmetry (addition_associativity (negate k) k n)) as a2.
  rewrite a2 in h'.
  rewrite (addition_left_inverse k) in h'.
  rewrite (addition_left_identity m) in h'.
  rewrite (addition_left_identity n) in h'.
  exact h'.
Qed.

Theorem addition_right_cancellation
  : forall (m : Integer) (n : Integer) (k : Integer), add m k = add n k -> m = n.
Proof.
  intros m n k h.
  rewrite (addition_commutativity m k) in h.
  rewrite (addition_commutativity n k) in h.
  exact (addition_left_cancellation k m n h).
Qed.

Theorem addition_cancellation
  : forall (m : Integer) (n : Integer) (k : Integer),
    (add m n = add m k -> n = k) /\ (add m n = add k n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (addition_left_cancellation m n k).
  - exact (addition_right_cancellation m k n).
Qed.

(* Negation is additive: it swaps the parts, and swapping the parts of a
 * sum swaps the parts of the summands.
 *)
Theorem negate_additivity
  : forall (m : Integer) (n : Integer), negate (add m n) = add (negate m) (negate n).
Proof.
  intros m n.
  unfold add in |- *.
  rewrite (from_difference_negation
             (NatWithZero.add (positive_part m) (positive_part n))
             (NatWithZero.add (negative_part m) (negative_part n))) in |- *.
  rewrite (positive_part_negation m) in |- *.
  rewrite (positive_part_negation n) in |- *.
  rewrite (negative_part_negation m) in |- *.
  rewrite (negative_part_negation n) in |- *.
  reflexivity.
Qed.

(* Subtraction adds the negation. *)
(* [Integer -> Integer -> Integer] *)
Definition subtract := fun (m : Integer) (n : Integer) => add m (negate n).

(* Taking away what was added gives the rest back: associativity puts [n]
 * against its negation, and the identity is left.
 *)
Theorem subtract_inversion_of_add
  : forall (m : Integer) (n : Integer), subtract (add m n) n = m.
Proof.
  intros m n.
  unfold subtract in |- *.
  rewrite (addition_associativity m n (negate n)) in |- *.
  rewrite (addition_right_inverse n) in |- *.
  exact (addition_right_identity m).
Qed.

(* Multiplication: signs multiply, magnitudes fall to [Nat.mul], and [Zero]
 * absorbs on either side.
 *)
(* [Integer -> Integer -> Integer] *)
Definition mul := fun (m : Integer) (n : Integer) =>
  match m with
  | Negative p =>
      match n with
      | Negative q => Positive (Nat.mul p q)
      | Zero       => Zero
      | Positive q => Negative (Nat.mul p q)
      end
  | Zero => Zero
  | Positive p =>
      match n with
      | Negative q => Negative (Nat.mul p q)
      | Zero       => Zero
      | Positive q => Positive (Nat.mul p q)
      end
  end.

Theorem multiplication_commutativity
  : forall (m : Integer) (n : Integer), mul m n = mul n m.
Proof.
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      rewrite (Nat.multiplication_commutativity p q) in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.multiplication_commutativity p q) in |- *.
      reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      rewrite (Nat.multiplication_commutativity p q) in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.multiplication_commutativity p q) in |- *.
      reflexivity.
Qed.

Theorem multiplication_associativity
  : forall (l : Integer) (m : Integer) (n : Integer), mul (mul l m) n = mul l (mul m n).
Proof.
  intros l m n.
  destruct l as [p | | p].
  - destruct m as [q | | q].
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
    + simpl in |- *.
      reflexivity.
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
  - simpl in |- *.
    reflexivity.
  - destruct m as [q | | q].
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
    + simpl in |- *.
      reflexivity.
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.multiplication_associativity p q r) in |- *.
        reflexivity.
Qed.

(* [Positive One] is the identity: [Nat.mul One q] computes to [q] under
 * either sign.
 *)
Theorem multiplication_left_identity : forall (n : Integer), mul (Positive One) n = n.
Proof.
  intros n.
  destruct n as [q | | q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem multiplication_right_identity : forall (n : Integer), mul n (Positive One) = n.
Proof.
  intros n.
  rewrite (multiplication_commutativity n (Positive One)) in |- *.
  exact (multiplication_left_identity n).
Qed.

Theorem multiplication_identity
  : forall (n : Integer), (mul (Positive One) n = n) /\ (mul n (Positive One) = n).
Proof.
  intros n.
  split.
  - exact (multiplication_left_identity n).
  - exact (multiplication_right_identity n).
Qed.

(* [Zero] absorbs: on the left by computation, on the right through
 * commutativity.
 *)
Theorem multiplication_left_absorption : forall (n : Integer), mul Zero n = Zero.
Proof.
  intros n.
  simpl in |- *.
  reflexivity.
Qed.

Theorem multiplication_right_absorption : forall (n : Integer), mul n Zero = Zero.
Proof.
  intros n.
  rewrite (multiplication_commutativity n Zero) in |- *.
  exact (multiplication_left_absorption n).
Qed.

(* Negating a factor negates the product: the signs say so under every
 * ctor pair.
 *)
Theorem multiplication_left_negation
  : forall (m : Integer) (n : Integer), mul (negate m) n = negate (mul m n).
Proof.
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - simpl in |- *.
    reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
Qed.

Theorem multiplication_right_negation
  : forall (m : Integer) (n : Integer), mul m (negate n) = negate (mul m n).
Proof.
  intros m n.
  rewrite (multiplication_commutativity m (negate n)) in |- *.
  rewrite (multiplication_left_negation n m) in |- *.
  rewrite (multiplication_commutativity n m) in |- *.
  reflexivity.
Qed.

(* A positive factor scales a difference: [Nat.mul] distributes over the
 * sum that trichotomy exposes, and the difference of the scaled sum is the
 * scaled remainder under the same sign.
 *)
Lemma difference_scaling
  : forall (k : Nat) (p : Nat) (q : Nat),
      mul (Positive k) (difference p q) = difference (Nat.mul k p) (Nat.mul k q).
Proof.
  intros k p q.
  pose proof (Nat.lt_trichotomy p q) as t.
  destruct t as [lt | rest].
  - unfold Nat.LessThan in lt.
    destruct lt as [j e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.addition_commutativity p j) in |- *.
    rewrite (difference_of_sum_right j p) in |- *.
    simpl in |- *.
    rewrite (Nat.mul_l_distributivity_over_addition k j p) in |- *.
    rewrite (difference_of_sum_right (Nat.mul k j) (Nat.mul k p)) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      rewrite (difference_diagonal (Nat.mul k q)) in |- *.
      simpl in |- *.
      reflexivity.
    + unfold Nat.LessThan in gt.
      destruct gt as [j e].
      pose proof (Identity.symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.addition_commutativity q j) in |- *.
      rewrite (difference_of_sum_left j q) in |- *.
      simpl in |- *.
      rewrite (Nat.mul_l_distributivity_over_addition k j q) in |- *.
      rewrite (difference_of_sum_left (Nat.mul k j) (Nat.mul k q)) in |- *.
      reflexivity.
Qed.

Lemma from_difference_scaling
  : forall (k : Nat) (a : NatWithZero) (b : NatWithZero),
      mul (Positive k) (from_difference a b)
      = from_difference (NatWithZero.mul (NatWithZero.Positive k) a)
                        (NatWithZero.mul (NatWithZero.Positive k) b).
Proof.
  intros k a b.
  destruct a as [| p].
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + change (from_difference
                (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive p))
                (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive q)))
        with (difference (Nat.mul k p) (Nat.mul k q)) in |- *.
      change (from_difference (NatWithZero.Positive p) (NatWithZero.Positive q))
        with (difference p q) in |- *.
      exact (difference_scaling k p q).
Qed.

(* The parts of a product by a positive are the scaled parts. *)

Lemma positive_part_scaling
  : forall (k : Nat) (x : Integer),
      positive_part (mul (Positive k) x)
      = NatWithZero.mul (NatWithZero.Positive k) (positive_part x).
Proof.
  intros k x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma negative_part_scaling
  : forall (k : Nat) (x : Integer),
      negative_part (mul (Positive k) x)
      = NatWithZero.mul (NatWithZero.Positive k) (negative_part x).
Proof.
  intros k x.
  destruct x as [p | | p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

(* Distributivity by a positive: the sum opens into the difference of its
 * parts, the factor scales that difference, and [NatWithZero.mul]
 * distributes on each component.
 *)
Lemma multiplication_positive_left_distributivity_over_add
  : forall (k : Nat) (m : Integer) (n : Integer),
      mul (Positive k) (add m n) = add (mul (Positive k) m) (mul (Positive k) n).
Proof.
  intros k m n.
  unfold add in |- *.
  rewrite (from_difference_scaling k
             (NatWithZero.add (positive_part m) (positive_part n))
             (NatWithZero.add (negative_part m) (negative_part n))) in |- *.
  rewrite (NatWithZero.mul_l_distributivity_over_addition
             (NatWithZero.Positive k) (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.mul_l_distributivity_over_addition
             (NatWithZero.Positive k) (negative_part m) (negative_part n)) in |- *.
  rewrite (positive_part_scaling k m) in |- *.
  rewrite (positive_part_scaling k n) in |- *.
  rewrite (negative_part_scaling k m) in |- *.
  rewrite (negative_part_scaling k n) in |- *.
  reflexivity.
Qed.

Theorem multiplication_left_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer),
      mul l (add m n) = add (mul l m) (mul l n).
Proof.
  intros l m n.
  destruct l as [p | | p].
  - change (Negative p) with (negate (Positive p)) in |- *.
    rewrite (multiplication_left_negation (Positive p) (add m n)) in |- *.
    rewrite (multiplication_left_negation (Positive p) m) in |- *.
    rewrite (multiplication_left_negation (Positive p) n) in |- *.
    pose proof (Identity.symmetry
                  (negate_additivity (mul (Positive p) m) (mul (Positive p) n))) as e.
    rewrite e in |- *.
    rewrite (multiplication_positive_left_distributivity_over_add p m n) in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (addition_left_identity Zero) in |- *.
    reflexivity.
  - exact (multiplication_positive_left_distributivity_over_add p m n).
Qed.

Theorem multiplication_right_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer),
      mul (add m n) l = add (mul m l) (mul n l).
Proof.
  intros l m n.
  rewrite (multiplication_commutativity (add m n) l) in |- *.
  rewrite (multiplication_left_distributivity_over_add l m n) in |- *.
  rewrite (multiplication_commutativity l m) in |- *.
  rewrite (multiplication_commutativity l n) in |- *.
  reflexivity.
Qed.

Theorem multiplication_distributivity_over_add
  : forall (x : Integer) (y : Integer) (z : Integer),
      (mul x (add y z) = add (mul x y) (mul x z))
    /\ (mul (add y z) x = add (mul y x) (mul z x)).
Proof.
  intros x y z.
  split.
  - exact (multiplication_left_distributivity_over_add x y z).
  - exact (multiplication_right_distributivity_over_add x y z).
Qed.

(* The strict order: [m] is below [n] when a positive amount reaches [n]
 * from [m]; [LessOrEqual] adds equality on top, as on the numbers.
 *)
(* [Integer -> Integer -> Prop] *)
Definition LessThan := fun (m : Integer) (n : Integer) =>
  exists (k : Nat), add m (Positive k) = n.

(* [Integer -> Integer -> Prop] *)
Definition LessOrEqual := fun (m : Integer) (n : Integer) => m = n \/ LessThan m n.

(* The order laws come off the group laws, with no case analysis: a witness
 * is cancelled, or two witnesses are added.
 *)

Theorem lt_irreflexivity : forall (n : Integer), ~ (LessThan n n).
Proof.
  intros n.
  unfold Negation in |- *.
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  pose proof (Identity.transitivity e (Identity.symmetry (addition_right_identity n)))
    as e'.
  pose proof (addition_left_cancellation n (Positive k) Zero e') as f.
  discriminate f.
Qed.

Theorem lt_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  change (Positive (Nat.add k1 k2)) with (add (Positive k1) (Positive k2)) in |- *.
  pose proof (Identity.symmetry (addition_associativity l (Positive k1) (Positive k2))) as a.
  rewrite a in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

(* Three-way comparison: every negative is below [Zero], which is below
 * every positive; two negatives fall to [Nat.compare] with the arguments
 * swapped, two positives to [Nat.compare] as they stand.
 *)
(* [Integer -> Integer -> Comparison] *)
Definition compare := fun (m : Integer) (n : Integer) =>
  match m with
  | Negative p =>
      match n with
      | Negative q => Nat.compare q p
      | Zero       => Lt
      | Positive _ => Lt
      end
  | Zero =>
      match n with
      | Negative _ => Gt
      | Zero       => Eq
      | Positive _ => Lt
      end
  | Positive p =>
      match n with
      | Negative _ => Gt
      | Zero       => Gt
      | Positive q => Nat.compare p q
      end
  end.

Theorem comparison_antisymmetry
  : forall (m : Integer) (n : Integer), compare m n = Comparison.transpose (compare n m).
Proof.
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      exact (Nat.comparison_antisymmetry q p).
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (Nat.comparison_antisymmetry p q).
Qed.

(* [compare] answers [Lt] and [Eq] exactly when the order says so; [Gt]
 * follows by [Comparable.gt_specification]. [LessThan] and [add]
 * are opened so that the witness equation computes under each ctor pair:
 * [add (Negative p) (Positive k)] to [difference k p], [add Zero (Positive k)]
 * to [Positive k], and [add (Positive p) (Positive k)] to
 * [Positive (Nat.add p k)].
 *)

Lemma lt_specification
  : forall (m : Integer) (n : Integer), compare m n = Lt <-> LessThan m n.
Proof.
  intros m n.
  unfold LessThan in |- *.
  unfold add in |- *.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.lt_specification_forward q p c) as lt.
        unfold Nat.LessThan in lt.
        destruct lt as [k e].
        apply (Exists_introduction k).
        rewrite (Nat.addition_commutativity q k) in e.
        exact (Biimplication.backward_elimination
                 (difference_negative_specification k p q) e).
      * intro h.
        destruct h as [k e].
        pose proof (Biimplication.forward_elimination
                      (difference_negative_specification k p q) e) as e'.
        apply (Nat.lt_specification_backward q p).
        unfold Nat.LessThan in |- *.
        apply (Exists_introduction k).
        rewrite (Nat.addition_commutativity q k) in |- *.
        exact e'.
    + simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction p).
        exact (difference_diagonal p).
      * intro h.
        reflexivity.
    + simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction (Nat.add q p)).
        exact (difference_of_sum_left q p).
      * intro h.
        reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro h.
        destruct h as [k e].
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro h.
        destruct h as [k e].
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction q).
        reflexivity.
      * intro h.
        reflexivity.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro h.
        destruct h as [k e].
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro h.
        destruct h as [k e].
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.lt_specification_forward p q c) as lt.
        unfold Nat.LessThan in lt.
        destruct lt as [k e].
        apply (Exists_introduction k).
        rewrite e in |- *.
        reflexivity.
      * intro h.
        destruct h as [k e].
        pose proof (positive_injectivity (Nat.add p k) q e) as e'.
        apply (Nat.lt_specification_backward p q).
        unfold Nat.LessThan in |- *.
        apply (Exists_introduction k).
        exact e'.
Qed.

Lemma eq_specification
  : forall (m : Integer) (n : Integer), compare m n = Eq <-> m = n.
Proof.
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.eq_specification_forward q p c) as e.
        rewrite e in |- *.
        reflexivity.
      * intro e.
        pose proof (negative_injectivity p q e) as e'.
        rewrite e' in |- *.
        exact (Comparable.reflexivity q).
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        reflexivity.
      * intro e.
        reflexivity.
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        discriminate c.
      * intro e.
        discriminate e.
    + simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.eq_specification_forward p q c) as e.
        rewrite e in |- *.
        reflexivity.
      * intro e.
        pose proof (positive_injectivity p q e) as e'.
        rewrite e' in |- *.
        exact (Comparable.reflexivity q).
Qed.

Theorem comparison_specification
  : forall (m : Integer) (n : Integer),
      (compare m n = Lt <-> LessThan m n) /\ (compare m n = Eq <-> m = n).
Proof.
  intros m n.
  split.
  - exact (lt_specification m n).
  - exact (eq_specification m n).
Qed.

(* The generic operation at [compare]; its laws are [Comparable]'s. *)

(* [Integer -> Integer -> Bool] *)
Abbreviation eq := (Comparable.eq compare).

(* Adding the same integer on the left keeps a strict step, with the same
 * witness once the sum is regrouped.
 *)
Theorem addition_strict_monotonicity
  : forall (k : Integer) (m : Integer) (n : Integer),
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

(* Multiplying by a positive keeps a strict step: the witness is scaled,
 * and distributivity puts the scaled sum back together.
 *)
Theorem multiplication_strict_monotonicity
  : forall (p : Nat) (m : Integer) (n : Integer),
      LessThan m n -> LessThan (mul (Positive p) m) (mul (Positive p) n).
Proof.
  intros p m n h.
  unfold LessThan in h.
  destruct h as [d e].
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul p d)).
  change (Positive (Nat.mul p d)) with (mul (Positive p) (Positive d)) in |- *.
  pose proof (Identity.symmetry
                (multiplication_left_distributivity_over_add (Positive p) m (Positive d))) as dist.
  rewrite dist in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Divisibility: [d] divides [n] when some multiple of [d] is [n]. It is
 * reflexive and transitive, but not antisymmetric: [Positive One] and
 * [Negative One] divide each other.
 *)
(* [Integer -> Integer -> Prop] *)
Definition Divides := fun (d : Integer) (n : Integer) => exists (k : Integer), mul d k = n.

Theorem divides_reflexivity : forall (n : Integer), Divides n n.
Proof.
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (Positive One)).
  exact (multiplication_right_identity n).
Qed.

Theorem divides_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer),
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

(* The multiples of [d] are closed under addition, by distributivity, and
 * under multiplication by anything, by associativity.
 *)

Theorem divides_addition_closure
  : forall (d : Integer) (m : Integer) (n : Integer),
      Divides d m -> Divides d n -> Divides d (add m n).
Proof.
  intros d m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (add k1 k2)).
  rewrite (multiplication_left_distributivity_over_add d k1 k2) in |- *.
  rewrite e1 in |- *.
  rewrite e2 in |- *.
  reflexivity.
Qed.

Theorem divides_multiplication_closure
  : forall (d : Integer) (m : Integer) (n : Integer), Divides d m -> Divides d (mul m n).
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

(* Parity: even is divisible by two, odd is one more than an even number,
 * on the negative side as well.
 *)

(* [Integer -> Prop] *)
Definition Even := fun (n : Integer) => Divides (Positive (Successor One)) n.

(* [Integer -> Prop] *)
Definition Odd := fun (n : Integer) =>
  exists (k : Integer), add (mul (Positive (Successor One)) k) (Positive One) = n.

(* Every integer is even or odd. [Zero] is even; on the positive side each
 * step up swaps the parity as on the numbers, on the negative side each
 * step down does, the odd witness one less than the even one. [simpl] is
 * kept away from [mul two k] on a variable [k], which it would open into
 * a [match]; the products on ctors are computed by [change].
 *)
Theorem even_or_odd : forall (n : Integer), Even n \/ Odd n.
Proof.
  intros n.
  destruct n as [p | | p].
  - induction p as [| p' IH] using Nat_induction.
    + apply Disjunction.r.
      unfold Odd in |- *.
      apply (Exists_introduction (Negative One)).
      unfold add in |- *.
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.r.
        unfold Even in ev.
        unfold Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction (add k (Negative One))).
        rewrite (multiplication_left_distributivity_over_add
                   (Positive (Successor One)) k (Negative One)) in |- *.
        change (mul (Positive (Successor One)) (Negative One))
          with (Negative (Successor One)) in |- *.
        rewrite e in |- *.
        rewrite (addition_associativity (Negative p') (Negative (Successor One)) (Positive One))
          in |- *.
        change (add (Negative (Successor One)) (Positive One)) with (Negative One) in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * apply Disjunction.l.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction k).
        pose proof (Identity.congruence (fun (x : Integer) => add x (Negative One)) e)
          as e'.
        change (add (add (mul (Positive (Successor One)) k) (Positive One)) (Negative One)
                = add (Negative p') (Negative One)) in e'.
        rewrite (addition_associativity
                   (mul (Positive (Successor One)) k) (Positive One) (Negative One)) in e'.
        change (add (Positive One) (Negative One)) with Zero in e'.
        rewrite (addition_right_identity (mul (Positive (Successor One)) k)) in e'.
        rewrite e' in |- *.
        unfold add in |- *.
        simpl in |- *.
        rewrite (Nat.addition_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
  - apply Disjunction.l.
    unfold Even in |- *.
    unfold Divides in |- *.
    apply (Exists_introduction Zero).
    simpl in |- *.
    reflexivity.
  - induction p as [| p' IH] using Nat_induction.
    + apply Disjunction.r.
      unfold Odd in |- *.
      apply (Exists_introduction Zero).
      unfold add in |- *.
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * apply Disjunction.r.
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
      * apply Disjunction.l.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction (add k (Positive One))).
        rewrite (multiplication_left_distributivity_over_add
                   (Positive (Successor One)) k (Positive One)) in |- *.
        change (mul (Positive (Successor One)) (Positive One))
          with (add (Positive One) (Positive One)) in |- *.
        pose proof (Identity.symmetry
                      (addition_associativity
                         (mul (Positive (Successor One)) k) (Positive One) (Positive One)))
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
  : forall (m : Integer) (n : Integer), Even m -> Even n -> Even (add m n).
Proof.
  intros m n h1 h2.
  unfold Even in h1.
  unfold Even in h2.
  unfold Even in |- *.
  exact (divides_addition_closure (Positive (Successor One)) m n h1 h2).
Qed.

(* Two odd integers add to an even one: the two ones make a two, which
 * distributivity absorbs into the witness.
 *)
Theorem odd_addition_odd
  : forall (m : Integer) (n : Integer), Odd m -> Odd n -> Even (add m n).
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
  rewrite (multiplication_left_distributivity_over_add
             (Positive (Successor One)) (add k1 k2) (Positive One)) in |- *.
  rewrite (multiplication_left_distributivity_over_add (Positive (Successor One)) k1 k2) in |- *.
  change (mul (Positive (Successor One)) (Positive One))
    with (add (Positive One) (Positive One)) in |- *.
  rewrite (addition_interchange
             (mul (Positive (Successor One)) k1) (Positive One)
             (mul (Positive (Successor One)) k2) (Positive One)) in |- *.
  reflexivity.
Qed.

End Integer.

(* The scope is declared in [Core.Notations] and never opened: a client
 * writes [(m + n)%integer]. [only parsing] keeps the operations printed by
 * name; the reversed spellings name no new relation.
 *)
Notation "m + n" := (Integer.add m n) (only parsing)
  : jwa_integer_scope.
Notation "m * n" := (Integer.mul m n) (only parsing)
  : jwa_integer_scope.
Notation "m < n" := (Integer.LessThan m n) (only parsing)
  : jwa_integer_scope.
Notation "m <= n" := (Integer.LessOrEqual m n) (only parsing)
  : jwa_integer_scope.
Notation "m > n" := (Integer.LessThan n m) (only parsing)
  : jwa_integer_scope.
Notation "m >= n" := (Integer.LessOrEqual n m) (only parsing)
  : jwa_integer_scope.

Instance Integer_comparable
  : Comparable Integer.compare Integer.LessThan :=
  {| Comparable.transitivity  := Integer.lt_transitivity
   ; Comparable.specification := Integer.comparison_specification
   ; Comparable.antisymmetry  := Integer.comparison_antisymmetry |}.

(* Addition is a commutative monoid with cancellation, [Zero] the identity;
 * the laws were already proved above, so each instance only hands them
 * over.
 *)
Instance Integer_add_monoid : Monoid Integer.add Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.addition_associativity |}
   ; Monoid.identity := Integer.addition_identity |}.

Instance Integer_add_cancellative : Cancellative Integer.add :=
  {| Cancellative.cancellation := Integer.addition_cancellation |}.

Instance Integer_add_commutative : Commutative Integer.add :=
  {| Commutative.commutativity := Integer.addition_commutativity |}.

(* Multiplication is a commutative monoid, [Positive One] the identity. *)
Instance Integer_mul_monoid : Monoid Integer.mul (Positive One) :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.multiplication_associativity |}
   ; Monoid.identity := Integer.multiplication_identity |}.

Instance Integer_mul_commutative : Commutative Integer.mul :=
  {| Commutative.commutativity := Integer.multiplication_commutativity |}.

(* Addition is an abelian group, negation the inverse; with [mul] it is a
 * ring. Each instance only hands over the laws and instances above.
 *)
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
   ; Ring.distributivity := Integer.multiplication_distributivity_over_add |}.
