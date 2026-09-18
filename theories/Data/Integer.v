(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Nat.
From jwa Require Import Data.NatWithZero.
From jwa Require Import Relations.Antisymmetric.
From jwa Require Import Relations.Irreflexive.
From jwa Require Import Relations.PartialOrder.
From jwa Require Import Relations.Reflexive.
From jwa Require Import Relations.StrictOrder.
From jwa Require Import Relations.Total.
From jwa Require Import Relations.TotalOrder.
From jwa Require Import Relations.Transitive.
From jwa Require Import Structures.Cancellative.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Semigroup.

Inductive Integer : Type :=
  | Negative : Nat -> Integer
  | Zero     : Integer
  | Positive : Nat -> Integer.

(* The eliminator behind [destruct], written out: no recursion, since no
   ctor carries an [Integer]. *)
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
   a function that reads the magnitude back is applied to both sides. *)

Theorem negative_injectivity
  : forall (p : Nat) (q : Nat), Negative p = Negative q -> p = q.
Proof.
  (* The context gains [p], [q] and [e : Negative p = Negative q]: [|- p = q] *)
  intros p q e.
  pose proof (Equijunction_congruence
                (fun (x : Integer) =>
                   match x with | Negative r => r | Zero => p | Positive _ => p end)
                e) as e'.
  (* Both applications compute: [e' : p = q] *)
  simpl in e'.
  exact e'.
Qed.

Theorem positive_injectivity
  : forall (p : Nat) (q : Nat), Positive p = Positive q -> p = q.
Proof.
  (* The context gains [p], [q] and [e : Positive p = Positive q]: [|- p = q] *)
  intros p q e.
  pose proof (Equijunction_congruence
                (fun (x : Integer) =>
                   match x with | Negative _ => p | Zero => p | Positive r => r end)
                e) as e'.
  (* Both applications compute: [e' : p = q] *)
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
  (* The context gains [x]; one goal per ctor, each computing to itself. *)
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
   the positive of the same magnitude. *)
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
  (* The context gains [m], [n] and [e]; one goal per ctor pair. *)
  intros m n e.
  destruct m as [| p].
  - destruct n as [| q].
    + reflexivity.
    + (* [e] computes to [Zero = Positive q], two distinct ctors. *)
      simpl in e.
      discriminate.
  - destruct n as [| q].
    + (* [e] computes to [Positive p = Zero], two distinct ctors. *)
      simpl in e.
      discriminate.
    + (* [e] computes to [Positive p = Positive q]; injectivity strips the
         ctors: [e' : p = q] *)
      simpl in e.
      pose proof (positive_injectivity p q e) as e'.
      rewrite e' in |- *.
      reflexivity.
Qed.

(* The positive part and the negative part: the magnitude on that side,
   [Zero] on the other. An integer is its positive part less its negative
   part, which is what [from_difference] below reads back. *)

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
  (* The context gains [x]; one goal per ctor, each computing to itself. *)
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
  (* The context gains [x]; one goal per ctor, each computing to itself. *)
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
   left standing gives the sign, and what is left of it the magnitude. *)
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
  (* The context gains [n]: [|- difference n n = Zero] *)
  intros n.
  (* [n] is either [One] or [Successor n']: one goal per ctor, and the
     second has [n'] and [IH : difference n' n' = Zero] in its context. *)
  induction n as [| n' IH] using Nat_induction.
  - (* [difference One One] computes: [|- Zero = Zero] *)
    simpl in |- *.
    reflexivity.
  - (* One step: [|- difference n' n' = Zero] *)
    simpl in |- *.
    exact IH.
Qed.

(* Taking one summand of a sum away leaves the other, with the sign of the
   side the sum stood on. *)

Lemma difference_of_sum_left
  : forall (k : Nat) (p : Nat), difference (Nat.add k p) p = Positive k.
Proof.
  (* The context gains [k] and [p]. *)
  intros k p.
  (* [p] is either [One] or [Successor p']: one goal per ctor, and the
     second has [p'] and [IH : difference (Nat.add k p') p' = Positive k]
     in its context. Each case turns the sum round so that it computes. *)
  induction p as [| p' IH] using Nat_induction.
  - (* [Nat.add One k] computes to [Successor k], and one step of
       [difference]: [|- Positive k = Positive k] *)
    rewrite (Nat.add_commutativity k One) in |- *.
    simpl in |- *.
    reflexivity.
  - (* The sum computes to [Successor (Nat.add p' k)], and one step of
       [difference]: [|- difference (Nat.add p' k) p' = Positive k] *)
    rewrite (Nat.add_commutativity k (Successor p')) in |- *.
    simpl in |- *.
    (* Commutativity turns the sum back to [IH]'s shape. *)
    rewrite (Nat.add_commutativity p' k) in |- *.
    exact IH.
Qed.

Lemma difference_of_sum_right
  : forall (k : Nat) (p : Nat), difference p (Nat.add k p) = Negative k.
Proof.
  (* The context gains [k] and [p]. *)
  intros k p.
  (* [p] is either [One] or [Successor p']: one goal per ctor, and the
     second has [p'] and [IH : difference p' (Nat.add k p') = Negative k]
     in its context. Each case turns the sum round so that it computes. *)
  induction p as [| p' IH] using Nat_induction.
  - (* [Nat.add One k] computes to [Successor k], and one step of
       [difference]: [|- Negative k = Negative k] *)
    rewrite (Nat.add_commutativity k One) in |- *.
    simpl in |- *.
    reflexivity.
  - (* The sum computes to [Successor (Nat.add p' k)], and one step of
       [difference]: [|- difference p' (Nat.add p' k) = Negative k] *)
    rewrite (Nat.add_commutativity k (Successor p')) in |- *.
    simpl in |- *.
    (* Commutativity turns the sum back to [IH]'s shape. *)
    rewrite (Nat.add_commutativity p' k) in |- *.
    exact IH.
Qed.

(* Two pairs with the same cross sums have the same difference: the
   quotient's well-definedness, proved by placing [p] against [q] with
   trichotomy and reading the other pair off the cross sums. *)
Lemma difference_well_definedness
  : forall (p : Nat) (q : Nat) (r : Nat) (s : Nat),
      Nat.add p s = Nat.add r q -> difference p q = difference r s.
Proof.
  (* The context gains [p], [q], [r], [s] and [h]; one goal per side of
     trichotomy. *)
  intros p q r s h.
  pose proof (Nat.less_than_trichotomy p q) as t.
  destruct t as [lt | rest].
  - (* [lt] opens into [k] and [e : Nat.add p k = q]; turned round, [e]
       replaces [q] in [h] and in the goal. *)
    unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in h.
    rewrite e' in |- *.
    (* The left side is a difference of a sum on the right:
       [|- Negative k = difference r s] *)
    rewrite (Nat.add_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    (* In [h : Nat.add p s = Nat.add r (Nat.add p k)], [p] moves to the front
       on the right and cancels: [e'' : s = Nat.add r k] *)
    rewrite (Nat.add_left_commutativity r p k) in h.
    pose proof (Nat.add_left_cancellation p s (Nat.add r k) h) as e''.
    (* [e''] replaces [s]: the right side is the same shape. *)
    rewrite e'' in |- *.
    rewrite (Nat.add_commutativity r k) in |- *.
    rewrite (difference_of_sum_right k r) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + (* [eq : p = q] replaces [p]: the left side is on the diagonal. *)
      rewrite eq in h.
      rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      (* In [h : Nat.add q s = Nat.add r q], the right side turned round,
         [q] cancels: [e : s = r] *)
      rewrite (Nat.add_commutativity r q) in h.
      pose proof (Nat.add_left_cancellation q s r h) as e.
      rewrite e in |- *.
      rewrite (difference_diagonal r) in |- *.
      reflexivity.
    + (* [gt] opens into [k] and [e : Nat.add q k = p]; turned round, [e]
         replaces [p] in [h] and in the goal. *)
      unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Equijunction_symmetry e) as e'.
      rewrite e' in h.
      rewrite e' in |- *.
      (* The left side is a difference of a sum on the left:
         [|- Positive k = difference r s] *)
      rewrite (Nat.add_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      (* In [h : Nat.add (Nat.add q k) s = Nat.add r q], the left side is
         regrouped, the right side turned round, and [q] cancels:
         [e'' : Nat.add k s = r] *)
      rewrite (Nat.add_associativity q k s) in h.
      rewrite (Nat.add_commutativity r q) in h.
      pose proof (Nat.add_left_cancellation q (Nat.add k s) r h) as e''.
      (* [e''] turned round replaces [r]: the right side is the same shape. *)
      pose proof (Equijunction_symmetry e'') as e'''.
      rewrite e''' in |- *.
      rewrite (difference_of_sum_left k s) in |- *.
      reflexivity.
Qed.

(* Swapping the two positives negates the difference. *)
Lemma difference_negation
  : forall (p : Nat) (q : Nat), negate (difference p q) = difference q p.
Proof.
  (* The context gains [p] and [q]; one goal per side of trichotomy. *)
  intros p q.
  pose proof (Nat.less_than_trichotomy p q) as t.
  destruct t as [lt | rest].
  - (* [lt] opens into [k] and [e : Nat.add p k = q]; turned round, [e]
       replaces [q]; both differences are of that sum. *)
    unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.add_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    rewrite (difference_of_sum_left k p) in |- *.
    (* [negate (Negative k)] computes: [|- Positive k = Positive k] *)
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + (* [eq : p = q] replaces [p]: both sides are on the diagonal. *)
      rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      simpl in |- *.
      reflexivity.
    + (* The mirror of the first case, with [e : Nat.add q k = p]. *)
      unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Equijunction_symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.add_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      rewrite (difference_of_sum_right k q) in |- *.
      (* [negate (Positive k)] computes: [|- Negative k = Negative k] *)
      simpl in |- *.
      reflexivity.
Qed.

(* The parts of a difference recover it: the positive part plus [q] is the
   negative part plus [p], whichever side was larger. *)
Lemma difference_specification
  : forall (p : Nat) (q : Nat),
      NatWithZero.add (positive_part (difference p q)) (NatWithZero.Positive q)
      = NatWithZero.add (negative_part (difference p q)) (NatWithZero.Positive p).
Proof.
  (* The context gains [p] and [q]; one goal per side of trichotomy. *)
  intros p q.
  pose proof (Nat.less_than_trichotomy p q) as t.
  destruct t as [lt | rest].
  - (* [lt] opens into [k] and [e : Nat.add p k = q]; turned round, [e]
       replaces [q]; the difference is [Negative k]. *)
    unfold Nat.LessThan in lt.
    destruct lt as [k e].
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.add_commutativity p k) in |- *.
    rewrite (difference_of_sum_right k p) in |- *.
    (* The parts and both sums compute:
       [|- NatWithZero.Positive (Nat.add k p) = NatWithZero.Positive (Nat.add k p)] *)
    simpl in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + (* [eq : p = q] replaces [p]: the difference is [Zero], and both
         sides compute to [NatWithZero.Positive q]. *)
      rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      simpl in |- *.
      reflexivity.
    + (* The mirror, with [e : Nat.add q k = p]: the difference is
         [Positive k]. *)
      unfold Nat.LessThan in gt.
      destruct gt as [k e].
      pose proof (Equijunction_symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.add_commutativity q k) in |- *.
      rewrite (difference_of_sum_left k q) in |- *.
      (* The parts and both sums compute:
         [|- NatWithZero.Positive (Nat.add k q) = NatWithZero.Positive (Nat.add k q)] *)
      simpl in |- *.
      reflexivity.
Qed.

(* Each ctor a difference can answer with, read as an equation on the two
   positives: the forward halves come off the specification with the answer
   put in, the backward halves off the sum laws. *)

Lemma difference_negative_specification
  : forall (p : Nat) (q : Nat) (k : Nat), difference p q = Negative k <-> Nat.add p k = q.
Proof.
  (* The context gains [p], [q] and [k]. *)
  intros p q k.
  split.
  - (* [e] put into the specification, whose parts and sums then compute:
       [s : NatWithZero.Positive q = NatWithZero.Positive (Nat.add k p)] *)
    intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q (Nat.add k p) s) as e'.
    (* Commutativity turns the sum round: [|- Nat.add k p = q] *)
    rewrite (Nat.add_commutativity p k) in |- *.
    exact (Equijunction_symmetry e').
  - (* [e] turned round replaces [q]: a difference of a sum on the right. *)
    intro e.
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.add_commutativity p k) in |- *.
    exact (difference_of_sum_right k p).
Qed.

Lemma difference_zero_specification
  : forall (p : Nat) (q : Nat), difference p q = Zero <-> p = q.
Proof.
  (* The context gains [p] and [q]. *)
  intros p q.
  split.
  - (* [e] put into the specification, whose parts and sums then compute:
       [s : NatWithZero.Positive q = NatWithZero.Positive p] *)
    intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity q p s) as e'.
    exact (Equijunction_symmetry e').
  - (* [e : p = q] replaces [p]: the diagonal. *)
    intro e.
    rewrite e in |- *.
    exact (difference_diagonal q).
Qed.

Lemma difference_positive_specification
  : forall (p : Nat) (q : Nat) (k : Nat), difference p q = Positive k <-> Nat.add q k = p.
Proof.
  (* The context gains [p], [q] and [k]. *)
  intros p q k.
  split.
  - (* [e] put into the specification, whose parts and sums then compute:
       [s : NatWithZero.Positive (Nat.add k q) = NatWithZero.Positive p] *)
    intro e.
    pose proof (difference_specification p q) as s.
    rewrite e in s.
    simpl in s.
    pose proof (NatWithZero.positive_injectivity (Nat.add k q) p s) as e'.
    (* Commutativity turns the sum round: [|- Nat.add k q = p] *)
    rewrite (Nat.add_commutativity q k) in |- *.
    exact e'.
  - (* [e] turned round replaces [p]: a difference of a sum on the left. *)
    intro e.
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.add_commutativity q k) in |- *.
    exact (difference_of_sum_left k q).
Qed.

(* The integer [a] less [b], for two numbers with zero: a [Zero] on either
   side is settled without recursion, two positives fall to [difference]. *)
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
  (* The context gains [x]; one goal per ctor, each computing to itself. *)
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
  (* The context gains [n]; one goal per ctor. *)
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - (* [|- difference p p = Zero] after computing *)
    simpl in |- *.
    exact (difference_diagonal p).
Qed.

Lemma from_difference_of_sum_left
  : forall (k : Nat) (a : NatWithZero),
      from_difference (NatWithZero.add (NatWithZero.Positive k) a) a = Positive k.
Proof.
  (* The context gains [k] and [a]; one goal per ctor of [a]. *)
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - (* [|- difference (Nat.add k q) q = Positive k] after computing *)
    simpl in |- *.
    exact (difference_of_sum_left k q).
Qed.

Lemma from_difference_of_sum_right
  : forall (k : Nat) (a : NatWithZero),
      from_difference a (NatWithZero.add (NatWithZero.Positive k) a) = Negative k.
Proof.
  (* The context gains [k] and [a]; one goal per ctor of [a]. *)
  intros k a.
  destruct a as [| q].
  - simpl in |- *.
    reflexivity.
  - (* [|- difference q (Nat.add k q) = Negative k] after computing *)
    simpl in |- *.
    exact (difference_of_sum_right k q).
Qed.

(* The parts of a difference recover it, lifted from [difference]. *)
Lemma from_difference_specification
  : forall (a : NatWithZero) (b : NatWithZero),
      NatWithZero.add (positive_part (from_difference a b)) b
      = NatWithZero.add (negative_part (from_difference a b)) a.
Proof.
  (* The context gains [a] and [b]; one goal per ctor pair. *)
  intros a b.
  destruct a as [| p].
  - destruct b as [| q].
    + simpl in |- *.
      reflexivity.
    + (* The difference is [Negative q]; both sides compute to
         [NatWithZero.Positive q]. *)
      simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + (* The difference is [Positive p]; both sides compute to
         [NatWithZero.Positive p]. *)
      simpl in |- *.
      reflexivity.
    + (* The difference is [difference p q], whose specification this is. *)
      simpl in |- *.
      exact (difference_specification p q).
Qed.

(* Two pairs with the same cross sums have the same difference, lifted from
   [difference]: a [Zero] on either side of one pair reads the other pair
   off the cross sums, and four positives fall to the [Nat] law. *)
Lemma from_difference_well_definedness
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      NatWithZero.add a d = NatWithZero.add c b -> from_difference a b = from_difference c d.
Proof.
  (* The context gains [a], [b], [c], [d] and [h]; one goal per ctor pair of
     [a] and [b]. *)
  intros a b c d h.
  destruct a as [| p].
  - destruct b as [| q].
    + (* [h] computes on the left to [d = NatWithZero.add c NatWithZero.Zero],
         and the right side turned round computes too: [h : d = c] *)
      simpl in h.
      rewrite (NatWithZero.add_commutativity c NatWithZero.Zero) in h.
      simpl in h.
      (* [h] replaces [d]: both sides are on the diagonal. *)
      rewrite h in |- *.
      rewrite (from_difference_diagonal c) in |- *.
      simpl in |- *.
      reflexivity.
    + (* [h] computes on the left to [d = NatWithZero.add c (NatWithZero.Positive q)],
         which replaces [d]: the right side is a difference of a sum on the
         right. *)
      simpl in h.
      rewrite h in |- *.
      rewrite (NatWithZero.add_commutativity c (NatWithZero.Positive q)) in |- *.
      rewrite (from_difference_of_sum_right q c) in |- *.
      simpl in |- *.
      reflexivity.
  - destruct b as [| q].
    + (* The right side of [h] turned round is [NatWithZero.add NatWithZero.Zero c],
         which is [c] by computation; [h] turned round replaces [c]: the
         right side is a difference of a sum on the left. *)
      rewrite (NatWithZero.add_commutativity c NatWithZero.Zero) in h.
      change (NatWithZero.add NatWithZero.Zero c) with c in h.
      pose proof (Equijunction_symmetry h) as h'.
      rewrite h' in |- *.
      rewrite (from_difference_of_sum_left p d) in |- *.
      simpl in |- *.
      reflexivity.
    + (* One goal per ctor pair of [c] and [d]. *)
      destruct c as [| r].
      * destruct d as [| s].
        { (* [h] computes to [NatWithZero.Positive p = NatWithZero.Positive q]:
             [p] is [q], and both sides are on the diagonal. *)
          simpl in h.
          pose proof (NatWithZero.positive_injectivity p q h) as e.
          rewrite e in |- *.
          simpl in |- *.
          rewrite (difference_diagonal q) in |- *.
          reflexivity. }
        { (* [h] computes to
             [NatWithZero.Positive (Nat.add p s) = NatWithZero.Positive q]:
             [q] is the sum, so the left side is a difference of a sum on
             the right. *)
          simpl in h.
          pose proof (NatWithZero.positive_injectivity (Nat.add p s) q h) as e.
          pose proof (Equijunction_symmetry e) as e'.
          rewrite e' in |- *.
          simpl in |- *.
          rewrite (Nat.add_commutativity p s) in |- *.
          rewrite (difference_of_sum_right s p) in |- *.
          reflexivity. }
      * destruct d as [| s].
        { (* [h] computes to
             [NatWithZero.Positive p = NatWithZero.Positive (Nat.add r q)]:
             [p] is the sum, so the left side is a difference of a sum on
             the left. *)
          simpl in h.
          pose proof (NatWithZero.positive_injectivity p (Nat.add r q) h) as e.
          rewrite e in |- *.
          simpl in |- *.
          rewrite (difference_of_sum_left r q) in |- *.
          reflexivity. }
        { (* [h] computes to
             [NatWithZero.Positive (Nat.add p s)
                = NatWithZero.Positive (Nat.add r q)],
             and the [Nat] law settles the two differences. *)
          simpl in h.
          pose proof (NatWithZero.positive_injectivity (Nat.add p s) (Nat.add r q) h)
            as e.
          simpl in |- *.
          exact (difference_well_definedness p q r s e). }
Qed.

Lemma from_difference_negation
  : forall (a : NatWithZero) (b : NatWithZero),
      negate (from_difference a b) = from_difference b a.
Proof.
  (* The context gains [a] and [b]; one goal per ctor pair. *)
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
    + (* [|- negate (difference p q) = difference q p] after computing *)
      simpl in |- *.
      exact (difference_negation p q).
Qed.

(* Addition: an integer is its positive part less its negative part, and
   two of them add part by part. The definition computes on ctors, so
   [add (Positive p) (Positive q)] is [Positive (Nat.add p q)] and
   [add (Positive p) (Negative q)] is [difference p q]. *)
(* [Integer -> Integer -> Integer] *)
Definition add := fun (m : Integer) (n : Integer) =>
  from_difference (NatWithZero.add (positive_part m) (positive_part n))
                  (NatWithZero.add (negative_part m) (negative_part n)).

(* [from_difference] is additive: the sum of two differences is the
   difference of the sums. [add] opens into the parts of the two
   differences, which their specifications relate to [a], [b], [c] and [d];
   the interchange law pairs them up for well-definedness. *)
Theorem from_difference_additivity
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      add (from_difference a b) (from_difference c d)
      = from_difference (NatWithZero.add a c) (NatWithZero.add b d).
Proof.
  (* The context gains [a], [b], [c] and [d]; [add] opens into its parts. *)
  intros a b c d.
  unfold add in |- *.
  (* Well-definedness reduces the goal to its cross sums:
     [|- NatWithZero.add (NatWithZero.add (positive_part (from_difference a b))
                                          (positive_part (from_difference c d)))
                         (NatWithZero.add b d)
         = NatWithZero.add (NatWithZero.add a c)
                           (NatWithZero.add (negative_part (from_difference a b))
                                            (negative_part (from_difference c d)))] *)
  apply (from_difference_well_definedness
           (NatWithZero.add (positive_part (from_difference a b))
                            (positive_part (from_difference c d)))
           (NatWithZero.add (negative_part (from_difference a b))
                            (negative_part (from_difference c d)))
           (NatWithZero.add a c) (NatWithZero.add b d)).
  (* Interchange pairs each positive part with its own [b] or [d]. *)
  rewrite (NatWithZero.add_interchange
             (positive_part (from_difference a b)) (positive_part (from_difference c d))
             b d) in |- *.
  (* Each pair is the specification's left side. *)
  rewrite (from_difference_specification a b) in |- *.
  rewrite (from_difference_specification c d) in |- *.
  (* Interchange again, and commutativity: both sides are the same term. *)
  rewrite (NatWithZero.add_interchange
             (negative_part (from_difference a b)) a
             (negative_part (from_difference c d)) c) in |- *.
  rewrite (NatWithZero.add_commutativity
             (NatWithZero.add (negative_part (from_difference a b))
                              (negative_part (from_difference c d)))
             (NatWithZero.add a c)) in |- *.
  reflexivity.
Qed.

(* Associativity: each summand is the difference of its parts, additivity
   folds each sum into one difference, and the components associate as
   numbers with zero. *)
Theorem add_associativity
  : forall (l : Integer) (m : Integer) (n : Integer),
      add (add l m) n = add l (add m n).
Proof.
  (* The context gains [l], [m] and [n]; the parts identity is read right to
     left so that it can replace each of them. *)
  intros l m n.
  pose proof (Equijunction_symmetry (from_difference_parts_identity l)) as el.
  pose proof (Equijunction_symmetry (from_difference_parts_identity m)) as em.
  pose proof (Equijunction_symmetry (from_difference_parts_identity n)) as en.
  rewrite el in |- *.
  rewrite em in |- *.
  rewrite en in |- *.
  (* Additivity folds the sums, inside out on each side. *)
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
  (* Associativity of the components: both sides are the same term. *)
  rewrite (NatWithZero.add_associativity
             (positive_part l) (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.add_associativity
             (negative_part l) (negative_part m) (negative_part n)) in |- *.
  reflexivity.
Qed.

Theorem add_commutativity
  : forall (m : Integer) (n : Integer), add m n = add n m.
Proof.
  (* The context gains [m] and [n]; [add] opens into its parts, which
     commute as numbers with zero. *)
  intros m n.
  unfold add in |- *.
  rewrite (NatWithZero.add_commutativity (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.add_commutativity (negative_part m) (negative_part n)) in |- *.
  reflexivity.
Qed.

(* [Zero] has no parts, so adding it adds nothing; the parts of [n] then
   rebuild it. *)
Theorem add_left_identity : forall (n : Integer), add Zero n = n.
Proof.
  (* The context gains [n]: [|- add Zero n = n] *)
  intros n.
  unfold add in |- *.
  (* The parts of [Zero] compute to [NatWithZero.Zero], which
     [NatWithZero.add] drops:
     [|- from_difference (positive_part n) (negative_part n) = n] *)
  simpl in |- *.
  exact (from_difference_parts_identity n).
Qed.

Theorem add_right_identity : forall (n : Integer), add n Zero = n.
Proof.
  (* Commutativity brings it to the left law. *)
  intros n.
  rewrite (add_commutativity n Zero) in |- *.
  exact (add_left_identity n).
Qed.

(* Negation is the inverse: the parts of [n] and of [negate n] add to the
   same number on both sides, a difference on the diagonal. *)
Theorem add_left_inverse : forall (n : Integer), add (negate n) n = Zero.
Proof.
  (* The context gains [n]; one goal per ctor. *)
  intros n.
  destruct n as [p | | p].
  - (* Both sides of the difference compute to [NatWithZero.Positive p]:
       [|- difference p p = Zero] *)
    unfold add in |- *.
    simpl in |- *.
    exact (difference_diagonal p).
  - unfold add in |- *.
    simpl in |- *.
    reflexivity.
  - (* As in the first case. *)
    unfold add in |- *.
    simpl in |- *.
    exact (difference_diagonal p).
Qed.

Theorem add_right_inverse : forall (n : Integer), add n (negate n) = Zero.
Proof.
  (* Commutativity brings it to the left law. *)
  intros n.
  rewrite (add_commutativity n (negate n)) in |- *.
  exact (add_left_inverse n).
Qed.

(* Cancellation: [negate k] added in front of both sides of the equation
   cancels [k], by associativity, the inverse and the identity. *)
Theorem add_left_cancellation
  : forall (k : Integer) (m : Integer) (n : Integer), add k m = add k n -> m = n.
Proof.
  (* The context gains [k], [m], [n] and [h]:
     [h' : add (negate k) (add k m) = add (negate k) (add k n)] *)
  intros k m n h.
  pose proof (Equijunction_congruence (add (negate k)) h) as h'.
  (* Associativity read right to left regroups each side. *)
  pose proof (Equijunction_symmetry (add_associativity (negate k) k m)) as a1.
  rewrite a1 in h'.
  pose proof (Equijunction_symmetry (add_associativity (negate k) k n)) as a2.
  rewrite a2 in h'.
  (* The inverse and the identity strip [k]: [h' : m = n] *)
  rewrite (add_left_inverse k) in h'.
  rewrite (add_left_identity m) in h'.
  rewrite (add_left_identity n) in h'.
  exact h'.
Qed.

Theorem add_right_cancellation
  : forall (m : Integer) (n : Integer) (k : Integer), add m k = add n k -> m = n.
Proof.
  (* Commutativity on both sides brings it to the left law. *)
  intros m n k h.
  rewrite (add_commutativity m k) in h.
  rewrite (add_commutativity n k) in h.
  exact (add_left_cancellation k m n h).
Qed.

(* Negation is additive: it swaps the parts, and swapping the parts of a
   sum swaps the parts of the summands. *)
Theorem negate_additivity
  : forall (m : Integer) (n : Integer), negate (add m n) = add (negate m) (negate n).
Proof.
  (* The context gains [m] and [n]; both [add]s open into their parts. *)
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
   against its negation, and the identity is left. *)
Theorem subtract_inversion_of_add
  : forall (m : Integer) (n : Integer), subtract (add m n) n = m.
Proof.
  (* The context gains [m] and [n]: [|- add (add m n) (negate n) = m] once
     [subtract] opens. *)
  intros m n.
  unfold subtract in |- *.
  rewrite (add_associativity m n (negate n)) in |- *.
  rewrite (add_right_inverse n) in |- *.
  exact (add_right_identity m).
Qed.

(* Multiplication: signs multiply, magnitudes fall to [Nat.mul], and [Zero]
   absorbs on either side. *)
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

Theorem mul_commutativity
  : forall (m : Integer) (n : Integer), mul m n = mul n m.
Proof.
  (* The context gains [m] and [n]; one goal per ctor pair, each computing
     to [Nat.mul]'s commutativity under the sign, or to [Zero]. *)
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      rewrite (Nat.mul_commutativity p q) in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.mul_commutativity p q) in |- *.
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
      rewrite (Nat.mul_commutativity p q) in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (Nat.mul_commutativity p q) in |- *.
      reflexivity.
Qed.

Theorem mul_associativity
  : forall (l : Integer) (m : Integer) (n : Integer), mul (mul l m) n = mul l (mul m n).
Proof.
  (* The context gains [l], [m] and [n]; one goal per ctor of [l], then of
     [m] where [l] is not [Zero], then of [n] where neither is: a [Zero]
     absorbs on both sides by computation, and the rest is [Nat.mul]'s
     associativity under the sign the three signs multiply to. *)
  intros l m n.
  destruct l as [p | | p].
  - destruct m as [q | | q].
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
    + simpl in |- *.
      reflexivity.
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
  - simpl in |- *.
    reflexivity.
  - destruct m as [q | | q].
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
    + simpl in |- *.
      reflexivity.
    + destruct n as [r | | r].
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (Nat.mul_associativity p q r) in |- *.
        reflexivity.
Qed.

(* [Positive One] is the identity: [Nat.mul One q] computes to [q] under
   either sign. *)
Theorem mul_left_identity : forall (n : Integer), mul (Positive One) n = n.
Proof.
  (* The context gains [n]; one goal per ctor. *)
  intros n.
  destruct n as [q | | q].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem mul_right_identity : forall (n : Integer), mul n (Positive One) = n.
Proof.
  (* Commutativity brings it to the left law. *)
  intros n.
  rewrite (mul_commutativity n (Positive One)) in |- *.
  exact (mul_left_identity n).
Qed.

(* [Zero] absorbs: on the left by computation, on the right through
   commutativity. *)
Theorem mul_left_absorption : forall (n : Integer), mul Zero n = Zero.
Proof.
  intros n.
  simpl in |- *.
  reflexivity.
Qed.

Theorem mul_right_absorption : forall (n : Integer), mul n Zero = Zero.
Proof.
  intros n.
  rewrite (mul_commutativity n Zero) in |- *.
  exact (mul_left_absorption n).
Qed.

(* Negating a factor negates the product: the signs say so under every
   ctor pair. *)
Theorem mul_left_negation
  : forall (m : Integer) (n : Integer), mul (negate m) n = negate (mul m n).
Proof.
  (* The context gains [m] and [n]; one goal per ctor of [m], then of [n]
     where [m] is not [Zero], each computing to itself. *)
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

Theorem mul_right_negation
  : forall (m : Integer) (n : Integer), mul m (negate n) = negate (mul m n).
Proof.
  (* Commutativity on both sides brings it to the left law. *)
  intros m n.
  rewrite (mul_commutativity m (negate n)) in |- *.
  rewrite (mul_left_negation n m) in |- *.
  rewrite (mul_commutativity n m) in |- *.
  reflexivity.
Qed.

(* A positive factor scales a difference: [Nat.mul] distributes over the
   sum that trichotomy exposes, and the difference of the scaled sum is the
   scaled remainder under the same sign. *)
Lemma difference_scaling
  : forall (k : Nat) (p : Nat) (q : Nat),
      mul (Positive k) (difference p q) = difference (Nat.mul k p) (Nat.mul k q).
Proof.
  (* The context gains [k], [p] and [q]; one goal per side of trichotomy. *)
  intros k p q.
  pose proof (Nat.less_than_trichotomy p q) as t.
  destruct t as [lt | rest].
  - (* [lt] opens into [j] and [e : Nat.add p j = q]; turned round, [e]
       replaces [q]; the difference is [Negative j] and the product computes. *)
    unfold Nat.LessThan in lt.
    destruct lt as [j e].
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    rewrite (Nat.add_commutativity p j) in |- *.
    rewrite (difference_of_sum_right j p) in |- *.
    simpl in |- *.
    (* On the right, [Nat.mul] distributes, and the scaled sum is again a
       sum on the right: [|- Negative (Nat.mul k j) = Negative (Nat.mul k j)] *)
    rewrite (Nat.mul_left_distributivity_over_add k j p) in |- *.
    rewrite (difference_of_sum_right (Nat.mul k j) (Nat.mul k p)) in |- *.
    reflexivity.
  - destruct rest as [eq | gt].
    + (* [eq : p = q] replaces [p]: both differences are on the diagonal,
         and [mul _ Zero] computes to [Zero]. *)
      rewrite eq in |- *.
      rewrite (difference_diagonal q) in |- *.
      rewrite (difference_diagonal (Nat.mul k q)) in |- *.
      simpl in |- *.
      reflexivity.
    + (* The mirror, with [e : Nat.add q j = p]: the difference is
         [Positive j]. *)
      unfold Nat.LessThan in gt.
      destruct gt as [j e].
      pose proof (Equijunction_symmetry e) as e'.
      rewrite e' in |- *.
      rewrite (Nat.add_commutativity q j) in |- *.
      rewrite (difference_of_sum_left j q) in |- *.
      simpl in |- *.
      rewrite (Nat.mul_left_distributivity_over_add k j q) in |- *.
      rewrite (difference_of_sum_left (Nat.mul k j) (Nat.mul k q)) in |- *.
      reflexivity.
Qed.

Lemma from_difference_scaling
  : forall (k : Nat) (a : NatWithZero) (b : NatWithZero),
      mul (Positive k) (from_difference a b)
      = from_difference (NatWithZero.mul (NatWithZero.Positive k) a)
                        (NatWithZero.mul (NatWithZero.Positive k) b).
Proof.
  (* The context gains [k], [a] and [b]; one goal per ctor pair. *)
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
    + (* The right side computes to [difference (Nat.mul k p) (Nat.mul k q)];
         the left is not opened by [simpl], since [mul (Positive k) _] on a
         stuck argument would become a [match] on it. *)
      change (from_difference
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
  (* The context gains [k] and [x]; one goal per ctor, each computing to
     itself. *)
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
  (* The context gains [k] and [x]; one goal per ctor, each computing to
     itself. *)
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
   parts, the factor scales that difference, and [NatWithZero.mul]
   distributes on each component. *)
Lemma mul_positive_left_distributivity_over_add
  : forall (k : Nat) (m : Integer) (n : Integer),
      mul (Positive k) (add m n) = add (mul (Positive k) m) (mul (Positive k) n).
Proof.
  (* The context gains [k], [m] and [n]; both [add]s open into their
     parts. *)
  intros k m n.
  unfold add in |- *.
  rewrite (from_difference_scaling k
             (NatWithZero.add (positive_part m) (positive_part n))
             (NatWithZero.add (negative_part m) (negative_part n))) in |- *.
  rewrite (NatWithZero.mul_left_distributivity_over_add
             (NatWithZero.Positive k) (positive_part m) (positive_part n)) in |- *.
  rewrite (NatWithZero.mul_left_distributivity_over_add
             (NatWithZero.Positive k) (negative_part m) (negative_part n)) in |- *.
  (* The parts of the right side are the scaled parts: both sides are the
     same term. *)
  rewrite (positive_part_scaling k m) in |- *.
  rewrite (positive_part_scaling k n) in |- *.
  rewrite (negative_part_scaling k m) in |- *.
  rewrite (negative_part_scaling k n) in |- *.
  reflexivity.
Qed.

Theorem mul_left_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer),
      mul l (add m n) = add (mul l m) (mul l n).
Proof.
  (* The context gains [l], [m] and [n]; one goal per ctor of [l]. *)
  intros l m n.
  destruct l as [p | | p].
  - (* [Negative p] is [negate (Positive p)] by computation; negation comes
       out of each product, then out of the sum, and the positive law
       remains. *)
    change (Negative p) with (negate (Positive p)) in |- *.
    rewrite (mul_left_negation (Positive p) (add m n)) in |- *.
    rewrite (mul_left_negation (Positive p) m) in |- *.
    rewrite (mul_left_negation (Positive p) n) in |- *.
    pose proof (Equijunction_symmetry
                  (negate_additivity (mul (Positive p) m) (mul (Positive p) n))) as e.
    rewrite e in |- *.
    rewrite (mul_positive_left_distributivity_over_add p m n) in |- *.
    reflexivity.
  - (* [mul Zero] computes to [Zero] on both sides; the sum of two [Zero]s
       is [Zero] by the identity. *)
    simpl in |- *.
    rewrite (add_left_identity Zero) in |- *.
    reflexivity.
  - exact (mul_positive_left_distributivity_over_add p m n).
Qed.

Theorem mul_right_distributivity_over_add
  : forall (l : Integer) (m : Integer) (n : Integer),
      mul (add m n) l = add (mul m l) (mul n l).
Proof.
  (* Commutativity on every product brings it to the left law. *)
  intros l m n.
  rewrite (mul_commutativity (add m n) l) in |- *.
  rewrite (mul_left_distributivity_over_add l m n) in |- *.
  rewrite (mul_commutativity l m) in |- *.
  rewrite (mul_commutativity l n) in |- *.
  reflexivity.
Qed.

(* The strict order: [m] is below [n] when a positive amount reaches [n]
   from [m]; [LessOrEqual] adds equality on top, as on the numbers. *)
(* [Integer -> Integer -> Prop] *)
Definition LessThan := fun (m : Integer) (n : Integer) =>
  exists (k : Nat), add m (Positive k) = n.

(* [Integer -> Integer -> Prop] *)
Definition LessOrEqual := fun (m : Integer) (n : Integer) => m = n \/ LessThan m n.

(* The order laws come off the group laws, with no case analysis: a witness
   is cancelled, or two witnesses are added. *)

Theorem less_than_irreflexivity : forall (n : Integer), ~ (LessThan n n).
Proof.
  (* The context gains [n]: [|- ~ (LessThan n n)] *)
  intros n.
  unfold Unjunction in |- *.
  (* The context gains [h]; it opens into [k] and [e : add n (Positive k) = n]. *)
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  (* [n] on the right of [e] is [add n Zero] by the identity, so cancellation
     leaves [f : Positive k = Zero], two distinct ctors. *)
  pose proof (Equijunction_transitivity e (Equijunction_symmetry (add_right_identity n)))
    as e'.
  pose proof (add_left_cancellation n (Positive k) Zero e') as f.
  discriminate.
Qed.

Theorem less_than_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]; they open into [k1],
     [e1 : add l (Positive k1) = m], [k2] and [e2 : add m (Positive k2) = n]. *)
  intros l m n h1 h2.
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  (* The witness is the sum of the two: [|- add l (Positive (Nat.add k1 k2)) = n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  (* That positive is the sum of the two positives by computation, which
     associativity read right to left regroups: [|- add (add l (Positive k1)) (Positive k2) = n] *)
  change (Positive (Nat.add k1 k2)) with (add (Positive k1) (Positive k2)) in |- *.
  pose proof (Equijunction_symmetry (add_associativity l (Positive k1) (Positive k2))) as a.
  rewrite a in |- *.
  (* [e1] then [e2] close it. *)
  rewrite e1 in |- *.
  exact e2.
Qed.

Theorem less_than_asymmetry
  : forall (m : Integer) (n : Integer), LessThan m n -> ~ (LessThan n m).
Proof.
  (* The context gains [m], [n], [h1] and, once unfolded, [h2]; the two
     compose to [LessThan m m], which irreflexivity refutes. *)
  intros m n h1.
  unfold Unjunction in |- *.
  intro h2.
  pose proof (less_than_transitivity m n m h1 h2) as h.
  pose proof (less_than_irreflexivity m) as i.
  unfold Unjunction in i.
  pose proof (i h) as f.
  contradiction.
Qed.

(* Three-way comparison: every negative is below [Zero], which is below
   every positive; two negatives fall to [Nat.compare] with the arguments
   swapped, two positives to [Nat.compare] as they stand. *)
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

Lemma compare_reflexivity : forall (n : Integer), compare n n = Eq.
Proof.
  (* The context gains [n]; one goal per ctor, the magnitudes falling to
     [Nat]'s law. *)
  intros n.
  destruct n as [p | | p].
  - simpl in |- *.
    exact (Nat.compare_reflexivity p).
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (Nat.compare_reflexivity p).
Qed.

Theorem compare_antisymmetry
  : forall (m : Integer) (n : Integer), compare m n = Comparison.converse (compare n m).
Proof.
  (* The context gains [m] and [n]; one goal per ctor pair, the two
     same-sign pairs falling to [Nat]'s law and the rest computing. *)
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + simpl in |- *.
      exact (Nat.compare_antisymmetry q p).
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
      exact (Nat.compare_antisymmetry p q).
Qed.

(* [compare] answers each of its three ways exactly when the order says so.
   [LessThan] and [add] are opened so that the witness equation computes
   under each ctor pair: [add (Negative p) (Positive k)] to
   [difference k p], [add Zero (Positive k)] to [Positive k], and
   [add (Positive p) (Positive k)] to [Positive (Nat.add p k)]. *)

Theorem compare_lt_specification
  : forall (m : Integer) (n : Integer), compare m n = Lt <-> LessThan m n.
Proof.
  (* The context gains [m] and [n]; one goal per ctor pair, each split into
     its two halves. *)
  intros m n.
  unfold LessThan in |- *.
  unfold add in |- *.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + (* [|- Nat.compare q p = Lt <-> exists (k : Nat), difference k p = Negative q] *)
      simpl in |- *.
      split.
      * (* [c] says [q] is below [p]: [e : Nat.add q k = p]; the same witness
           serves, [difference k p] being [Negative q] by its specification. *)
        intro c.
        pose proof (Nat.compare_lt_specification_forward q p c) as lt.
        unfold Nat.LessThan in lt.
        destruct lt as [k e].
        apply (Exists_introduction k).
        rewrite (Nat.add_commutativity q k) in e.
        exact (Bijunction_elimination_backward
                 (difference k p = Negative q) (Nat.add k q = p)
                 (difference_negative_specification k p q) e).
      * (* [h] opens into [k] and [e : difference k p = Negative q], which
           the specification reads as [Nat.add k q = p]: [q] is below [p]. *)
        intro h.
        destruct h as [k e].
        pose proof (Bijunction_elimination_forward
                      (difference k p = Negative q) (Nat.add k q = p)
                      (difference_negative_specification k p q) e) as e'.
        apply (Nat.compare_lt_specification_backward q p).
        unfold Nat.LessThan in |- *.
        apply (Exists_introduction k).
        rewrite (Nat.add_commutativity q k) in |- *.
        exact e'.
    + (* [|- Lt = Lt <-> exists (k : Nat), difference k p = Zero]: the witness
         is [p] itself, the diagonal. *)
      simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction p).
        exact (difference_diagonal p).
      * intro h.
        reflexivity.
    + (* [|- Lt = Lt <-> exists (k : Nat), difference k p = Positive q]: the
         witness is [Nat.add q p], a sum on the left. *)
      simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction (Nat.add q p)).
        exact (difference_of_sum_left q p).
      * intro h.
        reflexivity.
  - destruct n as [q | | q].
    + (* [|- Gt = Lt <-> exists (k : Nat), Positive k = Negative q]: both sides
         equate distinct ctors. *)
      simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro h.
        destruct h as [k e].
        discriminate.
    + (* [|- Eq = Lt <-> exists (k : Nat), Positive k = Zero] *)
      simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro h.
        destruct h as [k e].
        discriminate.
    + (* [|- Lt = Lt <-> exists (k : Nat), Positive k = Positive q]: the witness
         is [q]. *)
      simpl in |- *.
      split.
      * intro c.
        apply (Exists_introduction q).
        reflexivity.
      * intro h.
        reflexivity.
  - destruct n as [q | | q].
    + (* [|- Gt = Lt <-> exists (k : Nat), Positive (Nat.add p k) = Negative q] *)
      simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro h.
        destruct h as [k e].
        discriminate.
    + (* [|- Gt = Lt <-> exists (k : Nat), Positive (Nat.add p k) = Zero] *)
      simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro h.
        destruct h as [k e].
        discriminate.
    + (* [|- Nat.compare p q = Lt
           <-> exists (k : Nat), Positive (Nat.add p k) = Positive q]:
         [Nat]'s specification with the same witness under [Positive]. *)
      simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.compare_lt_specification_forward p q c) as lt.
        unfold Nat.LessThan in lt.
        destruct lt as [k e].
        apply (Exists_introduction k).
        rewrite e in |- *.
        reflexivity.
      * intro h.
        destruct h as [k e].
        pose proof (positive_injectivity (Nat.add p k) q e) as e'.
        apply (Nat.compare_lt_specification_backward p q).
        unfold Nat.LessThan in |- *.
        apply (Exists_introduction k).
        exact e'.
Qed.

Theorem compare_eq_specification
  : forall (m : Integer) (n : Integer), compare m n = Eq <-> m = n.
Proof.
  (* The context gains [m] and [n]; one goal per ctor pair, each split into
     its two halves: the same-sign pairs fall to [Nat]'s specification and
     injectivity, the rest equate distinct ctors on both sides. *)
  intros m n.
  destruct m as [p | | p].
  - destruct n as [q | | q].
    + (* [|- Nat.compare q p = Eq <-> Negative p = Negative q] *)
      simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.compare_eq_specification_forward q p c) as e.
        rewrite e in |- *.
        reflexivity.
      * intro e.
        pose proof (negative_injectivity p q e) as e'.
        rewrite e' in |- *.
        exact (Nat.compare_reflexivity q).
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
    + (* [|- Eq = Eq <-> Zero = Zero] *)
      simpl in |- *.
      split.
      * intro c.
        reflexivity.
      * intro e.
        reflexivity.
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
  - destruct n as [q | | q].
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
    + simpl in |- *.
      split.
      * intro c.
        discriminate.
      * intro e.
        discriminate.
    + (* [|- Nat.compare p q = Eq <-> Positive p = Positive q] *)
      simpl in |- *.
      split.
      * intro c.
        pose proof (Nat.compare_eq_specification_forward p q c) as e.
        rewrite e in |- *.
        reflexivity.
      * intro e.
        pose proof (positive_injectivity p q e) as e'.
        rewrite e' in |- *.
        exact (Nat.compare_reflexivity q).
Qed.

Theorem compare_gt_specification
  : forall (m : Integer) (n : Integer), compare m n = Gt <-> LessThan n m.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  split.
  - (* The context gains [e]; [compare_antisymmetry] turns it into
       [e : Comparison.converse (compare n m) = Gt], and only [Lt] has
       [Gt] as its converse. *)
    intro e.
    rewrite (compare_antisymmetry m n) in e.
    destruct (compare n m) as [| |] eqn:c.
    + exact (Bijunction_elimination_forward
               (compare n m = Lt) (LessThan n m) (compare_lt_specification n m) c).
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
  - (* The context gains [h : LessThan n m]; [compare n m] is [Lt] by the
       first specification, and its converse computes to [Gt]. *)
    intro h.
    rewrite (compare_antisymmetry m n) in |- *.
    rewrite (Bijunction_elimination_backward
               (compare n m = Lt) (LessThan n m) (compare_lt_specification n m) h)
      in |- *.
    simpl in |- *.
    reflexivity.
Qed.

(* Any two integers stand in exactly one of three relations, read off
   [compare] through its three specifications. *)
Theorem less_than_trichotomy
  : forall (m : Integer) (n : Integer), LessThan m n \/ m = n \/ LessThan n m.
Proof.
  (* The context gains [m] and [n]; one goal per answer of [compare m n]. *)
  intros m n.
  destruct (compare m n) as [| |] eqn:c.
  - exact (Disjunction_left
             (Bijunction_elimination_forward
                (compare m n = Lt) (LessThan m n) (compare_lt_specification m n) c)).
  - exact (Disjunction_right
             (Disjunction_left
                (Bijunction_elimination_forward
                   (compare m n = Eq) (m = n) (compare_eq_specification m n) c))).
  - exact (Disjunction_right
             (Disjunction_right
                (Bijunction_elimination_forward
                   (compare m n = Gt) (LessThan n m) (compare_gt_specification m n) c))).
Qed.

Theorem less_or_equal_reflexivity : forall (n : Integer), LessOrEqual n n.
Proof.
  (* The context gains [n]: [|- n = n \/ LessThan n n], and the left side
     holds. *)
  intros n.
  unfold LessOrEqual in |- *.
  exact (Disjunction_left (Equijunction_reflexivity n)).
Qed.

Theorem less_or_equal_transitivity
  : forall (l : Integer) (m : Integer) (n : Integer),
      LessOrEqual l m -> LessOrEqual m n -> LessOrEqual l n.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]; each side is an equality
     or a strict step. *)
  intros l m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  unfold LessOrEqual in |- *.
  destruct h1 as [e1 | lt1].
  - (* [e1 : l = m] replaces [l], and [h2] is the goal. *)
    rewrite e1 in |- *.
    exact h2.
  - destruct h2 as [e2 | lt2].
    + (* [e2 : m = n] replaces [m] in [lt1]. *)
      rewrite e2 in lt1.
      exact (Disjunction_right lt1).
    + (* Two strict steps compose. *)
      exact (Disjunction_right (less_than_transitivity l m n lt1 lt2)).
Qed.

Theorem less_or_equal_antisymmetry
  : forall (m : Integer) (n : Integer), LessOrEqual m n -> LessOrEqual n m -> m = n.
Proof.
  (* The context gains [m], [n], [h1] and [h2]: [|- m = n] *)
  intros m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  destruct h1 as [e1 | lt1].
  - exact e1.
  - destruct h2 as [e2 | lt2].
    + exact (Equijunction_symmetry e2).
    + (* Two strict steps in opposite directions contradict asymmetry. *)
      pose proof (less_than_asymmetry m n lt1) as h.
      unfold Unjunction in h.
      pose proof (h lt2) as f.
      contradiction.
Qed.

Theorem less_or_equal_totality
  : forall (m : Integer) (n : Integer), LessOrEqual m n \/ LessOrEqual n m.
Proof.
  (* The context gains [m] and [n]; trichotomy gives the three cases, each
     landing on one side. *)
  intros m n.
  pose proof (less_than_trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt | rest].
  - exact (Disjunction_left (Disjunction_right lt)).
  - destruct rest as [eq | gt].
    + exact (Disjunction_left (Disjunction_left eq)).
    + exact (Disjunction_right (Disjunction_right gt)).
Qed.

(* Decidable equality, read off [compare]. *)
(* [Integer -> Integer -> Bool] *)
Definition equal := fun (m : Integer) (n : Integer) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

Theorem equal_specification
  : forall (m : Integer) (n : Integer), equal m n = true <-> m = n.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  split.
  - (* The context gains [e : equal m n = true], a [match] on [compare m n];
       one goal per answer. *)
    intro e.
    unfold equal in e.
    destruct (compare m n) as [| |] eqn:c.
    + discriminate.
    + exact (Bijunction_elimination_forward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) c).
    + discriminate.
  - (* The context gains [e : m = n]; [compare m n] is [Eq]: [|- true = true] *)
    intro e.
    unfold equal in |- *.
    rewrite (Bijunction_elimination_backward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) e) in |- *.
    reflexivity.
Qed.

Theorem equal_refutation
  : forall (m : Integer) (n : Integer), equal m n = false -> ~ (m = n).
Proof.
  (* The context gains [m], [n] and [e : equal m n = false]: [|- ~ (m = n)] *)
  intros m n e.
  unfold Unjunction in |- *.
  intro h.
  (* [equal_specification] turns [h] into [equal m n = true], which replaces
     the left side of [e]: [e : true = false] *)
  rewrite (Bijunction_elimination_backward
             (equal m n = true) (m = n) (equal_specification m n) h) in e.
  discriminate.
Qed.

(* Adding the same integer on the left keeps a strict step, with the same
   witness once the sum is regrouped. *)
Theorem add_strict_monotonicity
  : forall (k : Integer) (m : Integer) (n : Integer),
      LessThan m n -> LessThan (add k m) (add k n).
Proof.
  (* The context gains [k], [m], [n] and [h]; [h] opens into [d] and
     [e : add m (Positive d) = n]. *)
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  (* The same witness serves: [|- add (add k m) (Positive d) = add k n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  rewrite (add_associativity k m (Positive d)) in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* Multiplying by a positive keeps a strict step: the witness is scaled,
   and distributivity puts the scaled sum back together. *)
Theorem mul_strict_monotonicity
  : forall (p : Nat) (m : Integer) (n : Integer),
      LessThan m n -> LessThan (mul (Positive p) m) (mul (Positive p) n).
Proof.
  (* The context gains [p], [m], [n] and [h]; [h] opens into [d] and
     [e : add m (Positive d) = n]. *)
  intros p m n h.
  unfold LessThan in h.
  destruct h as [d e].
  (* The witness is [Nat.mul p d], which is [mul (Positive p) (Positive d)]
     by computation: [|- add (mul (Positive p) m) (mul (Positive p) (Positive d))
                         = mul (Positive p) n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul p d)).
  change (Positive (Nat.mul p d)) with (mul (Positive p) (Positive d)) in |- *.
  (* Distributivity read right to left folds the sum, and [e] closes it. *)
  pose proof (Equijunction_symmetry
                (mul_left_distributivity_over_add (Positive p) m (Positive d))) as dist.
  rewrite dist in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

End Integer.

(* The scope is declared in [Core.Notations] and never opened: a client
   writes [(m + n)%integer]. [only parsing] keeps the operations printed by
   name; the reversed spellings name no new relation. *)
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

(* Addition is a commutative monoid with cancellation, [Zero] the identity;
   the laws were already proved above, so each instance only hands them
   over. *)
Instance Integer_add_monoid : Monoid.T Integer Integer.add Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.add_associativity |}
   ; Monoid.left_identity  := Integer.add_left_identity
   ; Monoid.right_identity := Integer.add_right_identity |}.

Instance Integer_add_cancellative : Cancellative.T Integer Integer.add :=
  {| Cancellative.left_cancellation  := Integer.add_left_cancellation
   ; Cancellative.right_cancellation := Integer.add_right_cancellation |}.

Instance Integer_add_commutative : Commutative.T Integer Integer.add :=
  {| Commutative.commutativity := Integer.add_commutativity |}.

(* Multiplication is a commutative monoid, [Positive One] the identity. *)
Instance Integer_mul_monoid : Monoid.T Integer Integer.mul (Positive One) :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Integer.mul_associativity |}
   ; Monoid.left_identity  := Integer.mul_left_identity
   ; Monoid.right_identity := Integer.mul_right_identity |}.

Instance Integer_mul_commutative : Commutative.T Integer Integer.mul :=
  {| Commutative.commutativity := Integer.mul_commutativity |}.

(* The two orders as instances of the [Relations] classes, the nested
   records filling the [::] fields one class at a time. *)
Instance Integer_less_than_strict_order : StrictOrder.R Integer Integer.LessThan :=
  {| StrictOrder.irreflexive :=
       {| Irreflexive.irreflexivity := Integer.less_than_irreflexivity |}
   ; StrictOrder.transitive :=
       {| Transitive.transitivity := Integer.less_than_transitivity |} |}.

Instance Integer_less_or_equal_total_order : TotalOrder.R Integer Integer.LessOrEqual :=
  {| TotalOrder.partial_order :=
       {| PartialOrder.reflexive :=
            {| Reflexive.reflexivity := Integer.less_or_equal_reflexivity |}
        ; PartialOrder.antisymmetric :=
            {| Antisymmetric.antisymmetry := Integer.less_or_equal_antisymmetry |}
        ; PartialOrder.transitive :=
            {| Transitive.transitivity := Integer.less_or_equal_transitivity |} |}
   ; TotalOrder.total :=
       {| Total.totality := Integer.less_or_equal_totality |} |}.
