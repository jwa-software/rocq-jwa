(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->], [=], [~], [/\], [\/] and [exists]; [Data.Nat] is
   the type [Positive] wraps and the source of every law under [Positive];
   [Structures.Semigroup], [Structures.Monoid], [Structures.Commutative],
   [Structures.Cancellative] and the [Relation] order classes are what the
   instances at the bottom fill; [Data.Comparison] is what [compare] answers
   in, [Data.Bool] what [equal] answers in, [Data.Pair] what [division]
   answers in, and [Data.Option] what [Nat.subtract] answers in. *)
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Data.Pair.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Order.StrictOrder.
From jwa Require Import Relation.Order.TotalOrder.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Total.
From jwa Require Import Relation.Transitive.
From jwa Require Import Structures.Cancellative.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Semiring.

(* [Positive] wraps a [Nat], so an operation here reduces to the [Nat] one
   plus the [Zero] cases. *)
Inductive NatWithZero : Type :=
  | Zero     : NatWithZero
  | Positive : Nat -> NatWithZero.

(* A module may carry the type's name; its members read [NatWithZero.add]. *)
Module NatWithZero.

(* No recursion here: [Zero] is the identity on both sides and the remaining
   case is [Nat.add] under [Positive]. *)
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

Theorem add_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
    add (add l m) n = add l (add m n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- add (add l m) n = add l (add m n)] *)
  intros l m n.
  (* [l] is either [Zero] or [Positive l']: one goal per ctor. *)
  destruct l as [| l'].
  - (* [|- add (add Zero m) n = add Zero (add m n)] *)
    (* [add Zero] is the identity on both sides: [|- add m n = add m n] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (add (Positive l') m) n = add (Positive l') (add m n)] *)
    (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
    destruct m as [| m'].
    + (* [|- add (add (Positive l') Zero) n = add (Positive l') (add Zero n)] *)
      (* [add _ Zero] and [add Zero _] both drop out, and [simpl] unfolds what
         is left into the same [match] on [n] on each side. *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [|- add (add (Positive l') (Positive m')) n
             = add (Positive l') (add (Positive m') n)] *)
      (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
      destruct n as [| n'].
      * (* [|- add (add (Positive l') (Positive m')) Zero
               = add (Positive l') (add (Positive m') Zero)] *)
        (* [add _ Zero] drops out on both sides:
           [|- Positive (Nat.add l' m') = Positive (Nat.add l' m')] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* [|- add (add (Positive l') (Positive m')) (Positive n')
               = add (Positive l') (add (Positive m') (Positive n'))] *)
        (* Every case is [Positive]:
           [|- Positive (Nat.add (Nat.add l' m') n')
               = Positive (Nat.add l' (Nat.add m' n'))] *)
        simpl in |- *.
        (* This is the whole proof: the [Nat] law carries the [NatWithZero]
           one. [|- Positive (Nat.add l' (Nat.add m' n'))
                   = Positive (Nat.add l' (Nat.add m' n'))] *)
        rewrite Nat.add_associativity in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem add_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), add m n = add n m.
Proof.
  (* The context gains [m] and [n]: [|- add m n = add n m] *)
  intros m n.
  (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
  destruct m as [| m'].
  - (* [add Zero n] computes; [add n Zero] cannot until [n] is a ctor:
       [|- n = add n Zero] *)
    simpl in |- *.
    (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* Both matches reduce: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* The inner match on [Zero] returns the first argument:
         [|- Positive n' = Positive n'] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* [|- add (Positive m') n = add n (Positive m')] *)
    (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* Both sides compute to the first argument:
         [|- Positive m' = Positive m'] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [|- add (Positive m') (Positive n')
             = add (Positive n') (Positive m')] *)
      (* Both sides reduce to [Nat.add] under [Positive]:
         [|- Positive (Nat.add m' n') = Positive (Nat.add n' m')] *)
      simpl in |- *.
      (* This is the whole proof: the [Nat] law carries the [NatWithZero] one.
         [|- Positive (Nat.add n' m') = Positive (Nat.add n' m')] *)
      rewrite Nat.add_commutativity in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

Theorem positive_injectivity
  : forall (m : Nat) (n : Nat), Positive m = Positive n -> m = n.
Proof.
  (* The context gains [m], [n] and [e : Positive m = Positive n]:
     [|- m = n] *)
  intros m n e.
  (* The context gains
     [e' : (fun x => match x with | Zero => m | Positive y => y end)
             (Positive m)
         = (fun x => match x with | Zero => m | Positive y => y end)
             (Positive n)]. *)
  pose proof (Identity.congruence
                (fun (x : NatWithZero) => match x with | Zero => m | Positive y => y end)
                e) as e'.
  (* Both applications compute: [e' : m = n] *)
  simpl in e'.
  (* [e'] is a proof of the goal as it stands. *)
  exact e'.
Qed.

Lemma add_positive_refutes_zero
  : forall (m : NatWithZero) (n : Nat), ~ (add m (Positive n) = Zero).
Proof.
  (* The context gains [m] and [n]: [|- ~ (add m (Positive n) = Zero)] *)
  intros m n.
  (* [|- add m (Positive n) = Zero -> Falsum] *)
  unfold Negation in |- *.
  (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
  destruct m as [| m'].
  - (* [add Zero] is the identity: [|- Positive n = Zero -> Falsum] *)
    simpl in |- *.
    (* The context gains [e : Positive n = Zero]: [|- Falsum] *)
    intro e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
  - (* Both summands positive, so [add] computes to [Positive]:
       [|- Positive (Nat.add m' n) = Zero -> Falsum] *)
    simpl in |- *.
    (* The context gains [e : Positive (Nat.add m' n) = Zero]: [|- Falsum] *)
    intro e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
Qed.

Theorem add_left_cancellation
  : forall (n : NatWithZero) (m : NatWithZero) (k : NatWithZero),
      add n m = add n k -> m = k.
Proof.
  (* The context gains [n], [m] and [k]: [|- add n m = add n k -> m = k] *)
  intros n m k.
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* Both [add Zero]s compute: [|- m = k -> m = k] *)
    simpl in |- *.
    (* The context gains [e : m = k]: [|- m = k] *)
    intro e.
    (* [e] is a proof of the goal as it stands. *)
    exact e.
  - (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
    destruct m as [| m'].
    + (* [k] is either [Zero] or [Positive k']: one goal per ctor. *)
      destruct k as [| k'].
      * (* The context gains [e]: [|- Zero = Zero] *)
        intro e.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Both [add]s compute:
           [|- Positive n' = Positive (Nat.add n' k') -> Zero = Positive k'] *)
        simpl in |- *.
        (* The context gains [e : Positive n' = Positive (Nat.add n' k')]:
           [|- Zero = Positive k'] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s:
           [e' : n' = Nat.add n' k'] *)
        pose proof (positive_injectivity n' (Nat.add n' k') e) as e'.
        (* Turned round, then commutativity: [e'' : Nat.add k' n' = n'] *)
        pose proof (Identity.symmetry e') as e''.
        rewrite (Nat.add_commutativity n' k') in e''.
        (* [h : Nat.add k' n' = n' -> Falsum], once unfolded *)
        pose proof (Nat.add_identity_absence k' n') as h.
        unfold Negation in h.
        (* [f : Falsum] *)
        pose proof (h e'') as f.
        (* [f : Falsum], which is what [contradiction] looks for. *)
        contradiction.
    + (* [k] is either [Zero] or [Positive k']: one goal per ctor. *)
      destruct k as [| k'].
      * (* Both [add]s compute:
           [|- Positive (Nat.add n' m') = Positive n' -> Positive m' = Zero] *)
        simpl in |- *.
        (* The context gains [e : Positive (Nat.add n' m') = Positive n']:
           [|- Positive m' = Zero] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s, commutativity
           turns the sum round: [e' : Nat.add m' n' = n'] *)
        pose proof (positive_injectivity (Nat.add n' m') n' e) as e'.
        rewrite (Nat.add_commutativity n' m') in e'.
        (* [h : Nat.add m' n' = n' -> Falsum], once unfolded *)
        pose proof (Nat.add_identity_absence m' n') as h.
        unfold Negation in h.
        (* [f : Falsum] *)
        pose proof (h e') as f.
        (* [f : Falsum], which is what [contradiction] looks for. *)
        contradiction.
      * (* Both [add]s compute:
           [|- Positive (Nat.add n' m') = Positive (Nat.add n' k')
               -> Positive m' = Positive k'] *)
        simpl in |- *.
        (* The context gains
           [e : Positive (Nat.add n' m') = Positive (Nat.add n' k')]:
           [|- Positive m' = Positive k'] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s:
           [e' : Nat.add n' m' = Nat.add n' k'] *)
        pose proof (positive_injectivity (Nat.add n' m') (Nat.add n' k') e)
          as e'.
        (* [Nat.add_left_cancellation] strips the [n']s: [e'' : m' = k'] *)
        pose proof (Nat.add_left_cancellation n' m' k' e') as e''.
        (* [e''] replaces [m']: [|- Positive k' = Positive k'] *)
        rewrite e'' in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

(* The right summand cancels too, by commuting both sums into the left
   form. *)
Theorem add_right_cancellation
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      add m n = add k n -> m = k.
Proof.
  (* The context gains [m], [k], [n] and [e : add m n = add k n]:
     [|- m = k] *)
  intros m k n e.
  (* [add_commutativity] turns each side round: [e : add n m = add n k] *)
  rewrite (add_commutativity m n) in e.
  rewrite (add_commutativity k n) in e.
  (* [add_left_cancellation n m k e] is a proof of the goal as it stands. *)
  exact (add_left_cancellation n m k e).
Qed.

Lemma add_left_commutativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      add l (add m n) = add m (add l n).
Proof.
  intros l m n.
  rewrite (add_commutativity l (add m n)) in |- *.
  rewrite (add_associativity m n l) in |- *.
  rewrite (add_commutativity n l) in |- *.
  reflexivity.
Qed.

(* The interchange law: two sums of two can be added pairwise across. *)
Theorem add_interchange
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero) (d : NatWithZero),
      add (add a b) (add c d) = add (add a c) (add b d).
Proof.
  intros a b c d.
  rewrite (add_associativity a b (add c d)) in |- *.
  rewrite (add_left_commutativity b c d) in |- *.
  rewrite (add_associativity a c (add b d)) in |- *.
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

(* [Positive One] is the identity on both sides; [Zero] absorbs, which is
   case analysis and [simpl] wherever it is needed. *)

Lemma mul_left_identity : forall (n : NatWithZero), mul (Positive One) n = n.
Proof.
  (* The context gains [n]: [|- mul (Positive One) n = n] *)
  intros n.
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* Both matches reduce: [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Both matches reduce and [Nat.mul One n'] computes:
       [|- Positive n' = Positive n'] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma mul_right_identity : forall (m : NatWithZero), mul m (Positive One) = m.
Proof.
  (* The context gains [m]: [|- mul m (Positive One) = m] *)
  intros m.
  (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
  destruct m as [| m'].
  - (* The outer match reduces: [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Both matches reduce; [Nat.mul m' One] does not, since [Nat.mul]
       recurses on its first argument:
       [|- Positive (Nat.mul m' One) = Positive m'] *)
    simpl in |- *.
    (* Commutativity turns the product round:
       [|- Positive (Nat.mul One m') = Positive m'] *)
    rewrite (Nat.mul_commutativity m' One) in |- *.
    (* [Nat.mul One m'] computes: [|- Positive m' = Positive m'] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem mul_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), mul m n = mul n m.
Proof.
  (* The context gains [m] and [n]: [|- mul m n = mul n m] *)
  intros m n.
  (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
  destruct m as [| m'].
  - (* [mul Zero n] computes; [mul n Zero] cannot until [n] is a ctor:
       [|- Zero = mul n Zero] *)
    simpl in |- *.
    (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* Both matches reduce: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* The inner match on [Zero] answers [Zero]: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* Both sides reduce to [Zero]: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* Both sides reduce to [Nat.mul] under [Positive]:
         [|- Positive (Nat.mul m' n') = Positive (Nat.mul n' m')] *)
      simpl in |- *.
      (* The [Nat] law carries the [NatWithZero] one:
         [|- Positive (Nat.mul n' m') = Positive (Nat.mul n' m')] *)
      rewrite (Nat.mul_commutativity m' n') in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

Theorem mul_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul (mul l m) n = mul l (mul m n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul (mul l m) n = mul l (mul m n)] *)
  intros l m n.
  (* [l] is either [Zero] or [Positive l']: one goal per ctor. *)
  destruct l as [| l'].
  - (* [mul Zero] absorbs on both sides: [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
    destruct m as [| m'].
    + (* [mul _ Zero] and [mul Zero _] both absorb: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
      destruct n as [| n'].
      * (* [mul _ Zero] absorbs on both sides: [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Every case is [Positive]:
           [|- Positive (Nat.mul (Nat.mul l' m') n')
               = Positive (Nat.mul l' (Nat.mul m' n'))] *)
        simpl in |- *.
        (* The [Nat] law carries the [NatWithZero] one:
           [|- Positive (Nat.mul l' (Nat.mul m' n'))
               = Positive (Nat.mul l' (Nat.mul m' n'))] *)
        rewrite (Nat.mul_associativity l' m' n') in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem mul_left_distributivity_over_add
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul l (add m n) = add (mul l m) (mul l n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul l (add m n) = add (mul l m) (mul l n)] *)
  intros l m n.
  (* [l] is either [Zero] or [Positive l']: one goal per ctor. *)
  destruct l as [| l'].
  - (* [mul Zero] absorbs everywhere and [add Zero Zero] computes:
       [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
    destruct m as [| m'].
    + (* [add Zero n] is [n] and [mul _ Zero] drops out of the sum, and
         [simpl] unfolds what is left into the same [match] on [n] on each
         side. *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
      destruct n as [| n'].
      * (* [add _ Zero] drops out on both sides:
           [|- Positive (Nat.mul l' m') = Positive (Nat.mul l' m')] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Every case is [Positive]:
           [|- Positive (Nat.mul l' (Nat.add m' n'))
               = Positive (Nat.add (Nat.mul l' m') (Nat.mul l' n'))] *)
        simpl in |- *.
        (* The [Nat] law carries the [NatWithZero] one:
           [|- Positive (Nat.add (Nat.mul l' m') (Nat.mul l' n'))
               = Positive (Nat.add (Nat.mul l' m') (Nat.mul l' n'))] *)
        rewrite (Nat.mul_left_distributivity_over_add l' m' n') in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem mul_right_distributivity_over_add
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      mul (add m n) l = add (mul m l) (mul n l).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul (add m n) l = add (mul m l) (mul n l)] *)
  intros l m n.
  (* [|- mul l (add m n) = add (mul m l) (mul n l)] *)
  rewrite (mul_commutativity (add m n) l) in |- *.
  (* [|- add (mul l m) (mul l n) = add (mul m l) (mul n l)] *)
  rewrite (mul_left_distributivity_over_add l m n) in |- *.
  (* [|- add (mul m l) (mul l n) = add (mul m l) (mul n l)] *)
  rewrite (mul_commutativity l m) in |- *.
  (* [|- add (mul m l) (mul n l) = add (mul m l) (mul n l)] *)
  rewrite (mul_commutativity l n) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem mul_distributivity_over_add
  : forall (a : NatWithZero) (b : NatWithZero) (c : NatWithZero)
      (d : NatWithZero),
      mul (add a b) (add c d)
      = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d)).
Proof.
  (* The context gains [a], [b], [c] and [d]:
     [|- mul (add a b) (add c d)
         = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))] *)
  intros a b c d.
  (* The right law splits the left sum:
     [|- add (mul a (add c d)) (mul b (add c d))
         = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))] *)
  rewrite (mul_right_distributivity_over_add (add c d) a b) in |- *.
  (* The left law splits each half:
     [|- add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))
         = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))] *)
  rewrite (mul_left_distributivity_over_add a c d) in |- *.
  rewrite (mul_left_distributivity_over_add b c d) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
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

(* The three exponent laws take the exponents apart by ctor; a [Zero]
   exponent is settled by [power_identity] and the identity of [mul], and
   the all-[Positive] case is the [Nat] law under [Positive]. *)

Theorem product_of_powers
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero),
      mul (power m a) (power m b) = power m (add a b).
Proof.
  (* The context gains [m], [a] and [b]:
     [|- mul (power m a) (power m b) = power m (add a b)] *)
  intros m a b.
  (* [a] is either [Zero] or [Positive a']: one goal per ctor. *)
  destruct a as [| a'].
  - (* [b] is either [Zero] or [Positive b']: one goal per ctor. *)
    destruct b as [| b'].
    + (* Everything computes, [Nat.mul One One] included:
         [|- Positive One = Positive One] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
      destruct m as [| m'].
      * (* [Zero] to a positive power is [Zero], and [mul _ Zero] absorbs:
           [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Everything computes, [Nat.mul One _] included:
           [|- Positive (Nat.power m' b') = Positive (Nat.power m' b')] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
  - (* [b] is either [Zero] or [Positive b']: one goal per ctor. *)
    destruct b as [| b'].
    + (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
      destruct m as [| m'].
      * (* [Zero] to a positive power is [Zero], and [mul Zero _] absorbs:
           [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Everything computes but [Nat.mul _ One], which is stuck on its
           first argument:
           [|- Positive (Nat.mul (Nat.power m' a') One)
               = Positive (Nat.power m' a')] *)
        simpl in |- *.
        (* Commutativity turns the product round, and [Nat.mul One _]
           computes: [|- Positive (Nat.power m' a') = Positive (Nat.power m' a')] *)
        rewrite (Nat.mul_commutativity (Nat.power m' a') One) in |- *.
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
    + (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
      destruct m as [| m'].
      * (* [Zero] to a positive power is [Zero] on both sides: [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Every case is [Positive]:
           [|- Positive (Nat.mul (Nat.power m' a') (Nat.power m' b'))
               = Positive (Nat.power m' (Nat.add a' b'))] *)
        simpl in |- *.
        (* The [Nat] law carries the [NatWithZero] one. *)
        rewrite (Nat.product_of_powers m' a' b') in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem power_of_a_power
  : forall (m : NatWithZero) (a : NatWithZero) (b : NatWithZero),
      power (power m a) b = power m (mul a b).
Proof.
  (* The context gains [m], [a] and [b]:
     [|- power (power m a) b = power m (mul a b)] *)
  intros m a b.
  (* [a] is either [Zero] or [Positive a']: one goal per ctor. *)
  destruct a as [| a'].
  - (* [b] is either [Zero] or [Positive b']: one goal per ctor. *)
    destruct b as [| b'].
    + (* [mul Zero Zero] and every [power _ Zero] compute:
         [|- Positive One = Positive One] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [power m Zero] is [Positive One], [power (Positive One) (Positive b')]
         computes to [Positive (Nat.power One b')], and [mul Zero _] absorbs
         in the exponent on the right:
         [|- Positive (Nat.power One b') = Positive One] *)
      simpl in |- *.
      (* [Nat.power_absorption] finishes it: [|- Positive One = Positive One] *)
      rewrite (Nat.power_absorption b') in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* [b] is either [Zero] or [Positive b']: one goal per ctor. *)
    destruct b as [| b'].
    + (* [mul _ Zero] absorbs and both [power _ Zero]s compute:
         [|- Positive One = Positive One] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
      destruct m as [| m'].
      * (* [Zero] to a positive power is [Zero], twice on the left:
           [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Every case is [Positive]:
           [|- Positive (Nat.power (Nat.power m' a') b')
               = Positive (Nat.power m' (Nat.mul a' b'))] *)
        simpl in |- *.
        (* The [Nat] law carries the [NatWithZero] one. *)
        rewrite (Nat.power_of_a_power m' a' b') in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem power_distributivity_over_mul
  : forall (m : NatWithZero) (n : NatWithZero) (a : NatWithZero),
      power (mul m n) a = mul (power m a) (power n a).
Proof.
  (* The context gains [m], [n] and [a]:
     [|- power (mul m n) a = mul (power m a) (power n a)] *)
  intros m n a.
  (* [a] is either [Zero] or [Positive a']: one goal per ctor. *)
  destruct a as [| a'].
  - (* All three [power _ Zero]s answer [Positive One] and
       [Nat.mul One One] computes: [|- Positive One = Positive One] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
    destruct m as [| m'].
    + (* [mul Zero n] is [Zero], and [Zero] to a positive power is [Zero]
         on both sides: [|- Zero = Zero] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
      destruct n as [| n'].
      * (* [mul _ Zero] is [Zero] on the left, [mul _ Zero] on the right:
           [|- Zero = Zero] *)
        simpl in |- *.
        (* Both sides are the same term. *)
        reflexivity.
      * (* Every case is [Positive]:
           [|- Positive (Nat.power (Nat.mul m' n') a')
               = Positive (Nat.mul (Nat.power m' a') (Nat.power n' a'))] *)
        simpl in |- *.
        (* The [Nat] law carries the [NatWithZero] one. *)
        rewrite (Nat.power_distributivity_over_mul m' n' a') in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

(* The strict order, as on [Nat]: [m] is below [n] when a positive amount
   reaches [n] from [m]. [LessOrEqual] adds equality on top. *)
(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessThan := fun (m : NatWithZero) (n : NatWithZero) =>
  exists (k : Nat), add m (Positive k) = n.

(* [NatWithZero -> NatWithZero -> Prop] *)
Definition LessOrEqual := fun (m : NatWithZero) (n : NatWithZero) =>
  m = n \/ LessThan m n.

(* Under [Positive] the order is [Nat]'s, with the same witness. *)
Lemma less_than_positive_embedding
  : forall (m : Nat) (n : Nat),
      LessThan (Positive m) (Positive n) <-> Nat.LessThan m n.
Proof.
  (* The context gains [m] and [n]:
     [|- LessThan (Positive m) (Positive n) <-> Nat.LessThan m n] *)
  intros m n.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* The context gains [h]; it opens into [k] and
       [e : add (Positive m) (Positive k) = Positive n]. *)
    intro h.
    unfold LessThan in h.
    destruct h as [k e].
    (* [add] computes under [Positive]: [e : Positive (Nat.add m k) = Positive n] *)
    simpl in e.
    (* [positive_injectivity] strips the [Positive]s: [e' : Nat.add m k = n] *)
    pose proof (positive_injectivity (Nat.add m k) n e) as e'.
    (* The same witness serves. *)
    unfold Nat.LessThan in |- *.
    exact (Exists_introduction k e').
  - (* The context gains [h]; it opens into [k] and [e : Nat.add m k = n]. *)
    intro h.
    unfold Nat.LessThan in h.
    destruct h as [k e].
    (* The same witness serves:
       [|- add (Positive m) (Positive k) = Positive n] *)
    unfold LessThan in |- *.
    apply (Exists_introduction k).
    (* [add] computes under [Positive]: [|- Positive (Nat.add m k) = Positive n] *)
    simpl in |- *.
    (* [e] replaces [Nat.add m k]: [|- Positive n = Positive n] *)
    rewrite e in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem less_than_irreflexivity : forall (n : NatWithZero), ~ (LessThan n n).
Proof.
  (* The context gains [n]: [|- ~ (LessThan n n)] *)
  intros n.
  (* [|- LessThan n n -> Falsum] *)
  unfold Negation in |- *.
  (* The context gains [h]; it opens into [k] and [e : add n (Positive k) = n]. *)
  intro h.
  unfold LessThan in h.
  destruct h as [k e].
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* [add Zero] computes: [e : Positive k = Zero] *)
    simpl in e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
  - (* [add] computes under [Positive]:
       [e : Positive (Nat.add n' k) = Positive n'] *)
    simpl in e.
    (* [positive_injectivity] strips the [Positive]s, commutativity turns
       the sum round: [e' : Nat.add k n' = n'] *)
    pose proof (positive_injectivity (Nat.add n' k) n' e) as e'.
    rewrite (Nat.add_commutativity n' k) in e'.
    (* [i : Nat.add k n' = n' -> Falsum], once unfolded *)
    pose proof (Nat.add_identity_absence k n') as i.
    unfold Negation in i.
    (* [f : Falsum] *)
    pose proof (i e') as f.
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
Qed.

Theorem less_than_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]: [|- LessThan l n] *)
  intros l m n h1 h2.
  (* Each hypothesis opens into a witness and an equation:
     [e1 : add l (Positive k1) = m], [e2 : add m (Positive k2) = n]. *)
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  (* The witness is the sum of the two:
     [|- add l (Positive (Nat.add k1 k2)) = n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.add k1 k2)).
  (* [e2] turned round replaces [n], then [e1] turned round replaces [m]:
     [|- add l (Positive (Nat.add k1 k2))
         = add (add l (Positive k1)) (Positive k2)] *)
  pose proof (Identity.symmetry e2) as e2'.
  rewrite e2' in |- *.
  pose proof (Identity.symmetry e1) as e1'.
  rewrite e1' in |- *.
  (* Associativity opens the right side:
     [|- add l (Positive (Nat.add k1 k2))
         = add l (add (Positive k1) (Positive k2))] *)
  rewrite (add_associativity l (Positive k1) (Positive k2)) in |- *.
  (* The inner [add] computes under [Positive], the outer one is stuck on
     [l] and stays:
     [|- add l (Positive (Nat.add k1 k2)) = add l (Positive (Nat.add k1 k2))] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem less_than_asymmetry
  : forall (m : NatWithZero) (n : NatWithZero), LessThan m n -> ~ (LessThan n m).
Proof.
  (* The context gains [m], [n] and [h1 : LessThan m n]:
     [|- ~ (LessThan n m)] *)
  intros m n h1.
  (* [|- LessThan n m -> Falsum] *)
  unfold Negation in |- *.
  (* The context gains [h2 : LessThan n m]: [|- Falsum] *)
  intro h2.
  (* The two compose into [h : LessThan m m], against irreflexivity. *)
  pose proof (less_than_transitivity m n m h1 h2) as h.
  pose proof (less_than_irreflexivity m) as i.
  unfold Negation in i.
  pose proof (i h) as f.
  (* [f : Falsum], which is what [contradiction] looks for. *)
  contradiction.
Qed.

(* Any two numbers compare one of three ways: the [Zero] cases are direct,
   and two [Positive]s fall to [Nat]'s trichotomy through
   [less_than_positive_embedding]. *)
Theorem less_than_trichotomy
  : forall (m : NatWithZero) (n : NatWithZero),
      LessThan m n \/ m = n \/ LessThan n m.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  (* [m] is either [Zero] or [Positive m']: one goal per ctor. *)
  destruct m as [| m'].
  - (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* Equal. *)
      exact (Disjunction.right (Disjunction.left (Identity.reflexivity Zero))).
    + (* [Zero] is below, with [n'] as the witness:
         [|- add Zero (Positive n') = Positive n'] *)
      apply Disjunction.left.
      unfold LessThan in |- *.
      apply (Exists_introduction n').
      simpl in |- *.
      reflexivity.
  - (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* The mirror: [|- add Zero (Positive m') = Positive m'] *)
      apply Disjunction.right.
      apply Disjunction.right.
      unfold LessThan in |- *.
      apply (Exists_introduction m').
      simpl in |- *.
      reflexivity.
    + (* [Nat]'s trichotomy on [m'] and [n'], each case lifted under
         [Positive]. *)
      pose proof (Nat.less_than_trichotomy m' n') as t.
      destruct t as [lt | rest].
      * apply Disjunction.left.
        exact (Biimplication.elimination_backward
                 (LessThan (Positive m') (Positive n')) (Nat.LessThan m' n')
                 (less_than_positive_embedding m' n') lt).
      * destruct rest as [eq | gt].
        { (* [eq : m' = n'] replaces [m']. *)
          apply Disjunction.right.
          apply Disjunction.left.
          rewrite eq in |- *.
          reflexivity. }
        { apply Disjunction.right.
          apply Disjunction.right.
          exact (Biimplication.elimination_backward
                   (LessThan (Positive n') (Positive m')) (Nat.LessThan n' m')
                   (less_than_positive_embedding n' m') gt). }
Qed.

Theorem add_strict_monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
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
  (* Associativity opens the left side: [|- add k (add m (Positive d)) = add k n] *)
  rewrite (add_associativity k m (Positive d)) in |- *.
  (* [e] replaces [add m (Positive d)]: [|- add k n = add k n] *)
  rewrite e in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* Scaling by a positive number keeps a strict step strict; by [Zero] it
   would not, so the factor is a [Nat]. *)
Theorem mul_strict_monotonicity
  : forall (k : Nat) (m : NatWithZero) (n : NatWithZero),
      LessThan m n -> LessThan (mul (Positive k) m) (mul (Positive k) n).
Proof.
  (* The context gains [k], [m], [n] and [h]; [h] opens into [d] and
     [e : add m (Positive d) = n]. *)
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  (* The witness is [d] scaled by [k]:
     [|- add (mul (Positive k) m) (Positive (Nat.mul k d)) = mul (Positive k) n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction (Nat.mul k d)).
  (* [m] is either [Zero] or [Positive m']: one goal per ctor, and in each
     [e] computes and, turned round, replaces [n]. *)
  destruct m as [| m'].
  - (* [e : Positive d = n] *)
    simpl in e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    (* Everything computes: [|- Positive (Nat.mul k d) = Positive (Nat.mul k d)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [e : Positive (Nat.add m' d) = n] *)
    simpl in e.
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    (* Everything computes under [Positive]:
       [|- Positive (Nat.add (Nat.mul k m') (Nat.mul k d))
           = Positive (Nat.mul k (Nat.add m' d))] *)
    simpl in |- *.
    (* [Nat]'s left distributivity opens the right side. *)
    rewrite (Nat.mul_left_distributivity_over_add k m' d) in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* The non-strict law: equality is carried to equality,
 * a strict step to the strict law above.
 *)
Theorem add_monotonicity
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessOrEqual m n -> LessOrEqual (add k m) (add k n).
Proof.
  intros k m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - (* [e : m = n] replaces [m]. *)
    rewrite e in |- *.
    unfold LessOrEqual in |- *.
    exact (Disjunction.left (Identity.reflexivity (add k n))).
  - unfold LessOrEqual in |- *.
    apply Disjunction.right.
    exact (add_strict_monotonicity k m n lt).
Qed.

(* The converse of [add_strict_monotonicity]:
 * a shared summand cancels from a strict comparison,
 * the witness carrying over once the sum is regrouped.
 *)
Theorem add_strict_cancellation
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessThan (add k m) (add k n) -> LessThan m n.
Proof.
  intros k m n h.
  unfold LessThan in h.
  destruct h as [d e].
  rewrite (add_associativity k m (Positive d)) in e.
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  exact (add_left_cancellation k (add m (Positive d)) n e).
Qed.

(* A summand is at most the sum;
 * equal to it when the other summand is [Zero], below it otherwise.
 *)
Theorem add_right_inflation
  : forall (m : NatWithZero) (n : NatWithZero), LessOrEqual n (add m n).
Proof.
  (* The context gains [m] and [n]: [|- LessOrEqual n (add m n)] *)
  intros m n.
  unfold LessOrEqual in |- *.
  destruct m as [| m'].
  - (* [add Zero n] computes: [|- n = n \/ LessThan n n] *)
    simpl in |- *.
    exact (Disjunction.left (Identity.reflexivity n)).
  - apply Disjunction.right.
    (* [|- exists (k : Nat), add n (Positive k) = add (Positive m') n] *)
    unfold LessThan in |- *.
    apply (Exists_introduction m').
    exact (add_commutativity n (Positive m')).
Qed.

(* A sum with a positive summand is positive: [Zero] is below it, the sum's
   own magnitude being the witness. *)
Theorem add_positive_positivity
  : forall (n : NatWithZero) (k : Nat), LessThan Zero (add n (Positive k)).
Proof.
  (* The context gains [n] and [k]: [|- LessThan Zero (add n (Positive k))] *)
  intros n k.
  unfold LessThan in |- *.
  destruct n as [| n'].
  - (* Both sums compute: [|- exists (j : Nat), Positive j = Positive k] *)
    simpl in |- *.
    apply (Exists_introduction k).
    reflexivity.
  - (* Both sums compute:
       [|- exists (j : Nat), Positive j = Positive (Nat.add n' k)] *)
    simpl in |- *.
    apply (Exists_introduction (Nat.add n' k)).
    reflexivity.
Qed.

Theorem less_or_equal_reflexivity : forall (n : NatWithZero), LessOrEqual n n.
Proof.
  (* The context gains [n]: [|- LessOrEqual n n] *)
  intros n.
  (* [|- n = n \/ LessThan n n], and the left side holds. *)
  unfold LessOrEqual in |- *.
  exact (Disjunction.left (Identity.reflexivity n)).
Qed.

Theorem less_or_equal_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessOrEqual l m -> LessOrEqual m n -> LessOrEqual l n.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]: [|- LessOrEqual l n] *)
  intros l m n h1 h2.
  (* Each side is an equality or a strict step. *)
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
      exact (Disjunction.right lt1).
    + (* Two strict steps compose. *)
      exact (Disjunction.right (less_than_transitivity l m n lt1 lt2)).
Qed.

Theorem less_or_equal_antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero),
      LessOrEqual m n -> LessOrEqual n m -> m = n.
Proof.
  (* The context gains [m], [n], [h1] and [h2]: [|- m = n] *)
  intros m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  destruct h1 as [e1 | lt1].
  - (* [e1] is the goal as it stands. *)
    exact e1.
  - destruct h2 as [e2 | lt2].
    + (* [e2 : n = m] turned round. *)
      exact (Identity.symmetry e2).
    + (* Two strict steps in opposite directions contradict asymmetry. *)
      pose proof (less_than_asymmetry m n lt1) as h.
      unfold Negation in h.
      pose proof (h lt2) as f.
      (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
Qed.

Theorem less_or_equal_totality
  : forall (m : NatWithZero) (n : NatWithZero),
      LessOrEqual m n \/ LessOrEqual n m.
Proof.
  (* The context gains [m] and [n]; trichotomy gives the three cases, each
     landing on one side. *)
  intros m n.
  pose proof (less_than_trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt | rest].
  - exact (Disjunction.left (Disjunction.right lt)).
  - destruct rest as [eq | gt].
    + exact (Disjunction.left (Disjunction.left eq)).
    + exact (Disjunction.right (Disjunction.right gt)).
Qed.

(* Strictly below [n] plus one is at most [n]: a witness of [One] is
 * equality by cancellation, a larger one a strict step with the rest as
 * witness, and back.
 *)
Theorem less_than_successor_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      LessThan m (add n (Positive One)) <-> LessOrEqual m n.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  split.
  - (* [h] opens into [k] and [e : add m (Positive k) = add n (Positive One)];
     * one goal per ctor of [k].
     *)
    intro h.
    unfold LessThan in h.
    destruct h as [k e].
    unfold LessOrEqual in |- *.
    destruct k as [| k'].
    + (* The shared step cancels on the right: [m = n]. *)
      apply Disjunction.left.
      exact (add_right_cancellation m n (Positive One) e).
    + (* [Positive (Successor k')] is [add (Positive One) (Positive k')] by
       * computation; turned round and regrouped, [e] puts the step last on
       * both sides, where it cancels: [|- add m (Positive k') = n]
       *)
      apply Disjunction.right.
      unfold LessThan in |- *.
      apply (Exists_introduction k').
      change (Positive (Successor k')) with (add (Positive One) (Positive k')) in e.
      rewrite (add_commutativity (Positive One) (Positive k')) in e.
      pose proof (Identity.symmetry (add_associativity m (Positive k') (Positive One)))
        as a.
      rewrite a in e.
      exact (add_right_cancellation (add m (Positive k')) n (Positive One) e).
  - (* [h] is an equality or a strict step; the witness is [One] or one more
     * than the step's.
     *)
    intro h.
    unfold LessOrEqual in h.
    unfold LessThan in |- *.
    destruct h as [e | lt].
    + apply (Exists_introduction One).
      rewrite e in |- *.
      reflexivity.
    + unfold LessThan in lt.
      destruct lt as [k e].
      apply (Exists_introduction (Successor k)).
      (* [Positive (Successor k)] is [add (Positive One) (Positive k)] by
       * computation; turned round and regrouped, the inner sum is [e]:
       * [|- add (add m (Positive k)) (Positive One) = add n (Positive One)]
       *)
      change (Positive (Successor k)) with (add (Positive One) (Positive k)) in |- *.
      rewrite (add_commutativity (Positive One) (Positive k)) in |- *.
      pose proof (Identity.symmetry (add_associativity m (Positive k) (Positive One)))
        as a.
      rewrite a in |- *.
      rewrite e in |- *.
      reflexivity.
Qed.

(* Three-way comparison: [Zero] is below every [Positive], and two
   [Positive]s fall to [Nat.compare]. *)
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

Lemma compare_reflexivity : forall (n : NatWithZero), compare n n = Eq.
Proof.
  (* The context gains [n]: [|- compare n n = Eq] *)
  intros n.
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* [compare Zero Zero] computes: [|- Eq = Eq] *)
    simpl in |- *.
    reflexivity.
  - (* [compare] computes to [Nat.compare n' n']. *)
    simpl in |- *.
    exact (Nat.compare_reflexivity n').
Qed.

(* Swapping the arguments swaps the answer. *)
Theorem compare_antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero),
      compare m n = Comparison.transpose (compare n m).
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  (* One goal per ctor pair; the three with a [Zero] compute, the last is
     [Nat]'s law. *)
  destruct m as [| m'].
  - destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      exact (Nat.compare_antisymmetry m' n').
Qed.

(* [compare] answers each of its three ways exactly when the order says so;
   the [Positive] pair falls to [Nat]'s specification through
   [less_than_positive_embedding]. *)

Theorem compare_lt_specification
  : forall (m : NatWithZero) (n : NatWithZero), compare m n = Lt <-> LessThan m n.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  (* One goal per ctor pair, each split into its two halves. *)
  destruct m as [| m'].
  - destruct n as [| n'].
    + split.
      * (* [|- Eq = Lt -> LessThan Zero Zero] after computing *)
        simpl in |- *.
        intro e.
        discriminate.
      * (* [LessThan Zero Zero] contradicts irreflexivity. *)
        intro h.
        pose proof (less_than_irreflexivity Zero) as i.
        unfold Negation in i.
        pose proof (i h) as f.
        contradiction.
    + split.
      * (* [Zero] is below, with [n'] as the witness. *)
        intro e.
        unfold LessThan in |- *.
        apply (Exists_introduction n').
        simpl in |- *.
        reflexivity.
      * (* [compare Zero (Positive n')] computes: [|- Lt = Lt] *)
        intro h.
        simpl in |- *.
        reflexivity.
  - destruct n as [| n'].
    + split.
      * (* [|- Gt = Lt -> ...] after computing *)
        simpl in |- *.
        intro e.
        discriminate.
      * (* Nothing is below [Zero]: the witness equation computes to a
           [Positive] against [Zero]. *)
        intro h.
        unfold LessThan in h.
        destruct h as [k e].
        simpl in e.
        discriminate.
    + split.
      * (* [compare] computes to [Nat.compare m' n']. *)
        simpl in |- *.
        intro e.
        exact (Biimplication.elimination_backward
                 (LessThan (Positive m') (Positive n')) (Nat.LessThan m' n')
                 (less_than_positive_embedding m' n')
                 (Nat.compare_lt_specification_forward m' n' e)).
      * intro h.
        simpl in |- *.
        exact (Nat.compare_lt_specification_backward
                m'
                n'
                (Biimplication.elimination_forward
                  (LessThan (Positive m') (Positive n'))
                  (Nat.LessThan m' n')
                  (less_than_positive_embedding m' n')
                  h)).
Qed.

Theorem compare_eq_specification
  : forall (m : NatWithZero) (n : NatWithZero), compare m n = Eq <-> m = n.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  split.
  - (* The context gains [e : compare m n = Eq]; one goal per ctor
       pair. *)
    intro e.
    destruct m as [| m'].
    + destruct n as [| n'].
      * reflexivity.
      * (* [e : Lt = Eq] after computing *)
        simpl in e.
        discriminate.
    + destruct n as [| n'].
      * (* [e : Gt = Eq] after computing *)
        simpl in e.
        discriminate.
      * (* [e : Nat.compare m' n' = Eq], so [m' = n'] replaces [m']. *)
        simpl in e.
        rewrite (Nat.compare_eq_specification_forward m' n' e) in |- *.
        reflexivity.
  - (* The context gains [e : m = n], which replaces [m]. *)
    intro e.
    rewrite e in |- *.
    exact (compare_reflexivity n).
Qed.

Theorem compare_gt_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      compare m n = Gt <-> LessThan n m.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  split.
  - (* The context gains [e]; [compare_antisymmetry] turns it into
       [e : Comparison.transpose (compare n m) = Gt], and only [Lt] has
       [Gt] as its transpose. *)
    intro e.
    rewrite (compare_antisymmetry m n) in e.
    destruct (compare n m) as [| |] eqn:c.
    + exact (Biimplication.elimination_forward
               (compare n m = Lt) (LessThan n m)
               (compare_lt_specification n m) c).
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
  - (* The context gains [h : LessThan n m]; [compare n m] is [Lt] by the
       first specification, and its transpose computes to [Gt]. *)
    intro h.
    rewrite (compare_antisymmetry m n) in |- *.
    rewrite (Biimplication.elimination_backward
               (compare n m = Lt) (LessThan n m)
               (compare_lt_specification n m) h) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

(* Decidable equality, read off [compare]. *)
(* [NatWithZero -> NatWithZero -> Bool] *)
Definition equal := fun (m : NatWithZero) (n : NatWithZero) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

Theorem equal_specification
  : forall (m : NatWithZero) (n : NatWithZero), equal m n = true <-> m = n.
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
    + exact (Biimplication.elimination_forward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) c).
    + discriminate.
  - (* The context gains [e : m = n]; [compare m n] is [Eq]:
       [|- true = true] *)
    intro e.
    unfold equal in |- *.
    rewrite (Biimplication.elimination_backward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) e)
      in |- *.
    reflexivity.
Qed.

(* The [false] answer refutes equality: were the two equal, the answer
   would be [true]. *)
Theorem equal_refutation
  : forall (m : NatWithZero) (n : NatWithZero), equal m n = false -> ~ (m = n).
Proof.
  (* The context gains [m], [n] and [e : equal m n = false]: [|- ~ (m = n)] *)
  intros m n e.
  (* [|- m = n -> Falsum] *)
  unfold Negation in |- *.
  (* The context gains [h : m = n]: [|- Falsum] *)
  intro h.
  (* [equal_specification] turns [h] into [equal m n = true], which
     replaces the left side of [e]: [e : true = false] *)
  rewrite (Biimplication.elimination_backward
             (equal m n = true) (m = n) (equal_specification m n) h) in e.
  (* [e] equates two distinct ctors, which closes any goal. *)
  discriminate.
Qed.

(* [LessOrEqual] decided: [compare] answers [Gt] exactly when it fails. *)
(* [NatWithZero -> NatWithZero -> Bool] *)
Definition at_most := fun (m : NatWithZero) (n : NatWithZero) =>
  match compare m n with
  | Lt => true
  | Eq => true
  | Gt => false
  end.

Theorem at_most_specification
  : forall (m : NatWithZero) (n : NatWithZero), at_most m n = true <-> LessOrEqual m n.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  unfold at_most in |- *.
  (* One goal per answer of [compare m n], each split into its two halves
     once the [match] has computed. *)
  destruct (compare m n) as [| |] eqn:c.
  - (* [|- true = true <-> LessOrEqual m n] *)
    simpl in |- *.
    split.
    + (* [c] says [m] is below [n]. *)
      intro e.
      unfold LessOrEqual in |- *.
      apply Disjunction.right.
      exact (Biimplication.elimination_forward
               (compare m n = Lt) (LessThan m n) (compare_lt_specification m n) c).
    + intro h.
      reflexivity.
  - (* [|- true = true <-> LessOrEqual m n] *)
    simpl in |- *.
    split.
    + (* [c] says [m] is [n]. *)
      intro e.
      unfold LessOrEqual in |- *.
      apply Disjunction.left.
      exact (Biimplication.elimination_forward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) c).
    + intro h.
      reflexivity.
  - (* [|- false = true <-> LessOrEqual m n] *)
    simpl in |- *.
    split.
    + (* [e] equates two distinct ctors, which closes any goal. *)
      intro e.
      discriminate.
    + (* [c] says [n] is below [m], which neither half of [h] allows. *)
      intro h.
      pose proof (Biimplication.elimination_forward
                    (compare m n = Gt) (LessThan n m) (compare_gt_specification m n) c)
        as gt.
      unfold LessOrEqual in h.
      destruct h as [e | lt].
      * (* [e : m = n] replaces [m]: [gt : LessThan n n] contradicts
           irreflexivity. *)
        rewrite e in gt.
        pose proof (less_than_irreflexivity n) as i.
        unfold Negation in i.
        pose proof (i gt) as f.
        contradiction.
      * (* [lt] and [gt] contradict asymmetry. *)
        pose proof (less_than_asymmetry m n lt) as a.
        unfold Negation in a.
        pose proof (a gt) as f.
        contradiction.
Qed.

(* The two laws a sorting comparison needs, read off the order. *)

Theorem at_most_totality
  : forall (m : NatWithZero) (n : NatWithZero), at_most m n = true \/ at_most n m = true.
Proof.
  (* The context gains [m] and [n]; one goal per side of totality. *)
  intros m n.
  pose proof (less_or_equal_totality m n) as t.
  destruct t as [h | h].
  - apply Disjunction.left.
    exact (Biimplication.elimination_backward
             (at_most m n = true) (LessOrEqual m n) (at_most_specification m n) h).
  - apply Disjunction.right.
    exact (Biimplication.elimination_backward
             (at_most n m = true) (LessOrEqual n m) (at_most_specification n m) h).
Qed.

Theorem at_most_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      at_most l m = true -> at_most m n = true -> at_most l n = true.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]; each answer is read as
     the order it decides: [le1 : LessOrEqual l m], [le2 : LessOrEqual m n]. *)
  intros l m n h1 h2.
  pose proof (Biimplication.elimination_forward
                (at_most l m = true) (LessOrEqual l m) (at_most_specification l m) h1)
    as le1.
  pose proof (Biimplication.elimination_forward
                (at_most m n = true) (LessOrEqual m n) (at_most_specification m n) h2)
    as le2.
  (* Transitivity of the order, read back as an answer. *)
  exact (Biimplication.elimination_backward
           (at_most l n = true) (LessOrEqual l n) (at_most_specification l n)
           (less_or_equal_transitivity l m n le1 le2)).
Qed.

(* The smaller and the larger of two, read off [compare]; every law below
   is case analysis on the answer and the order laws, and associativity is
   antisymmetry applied to the bounds. *)

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition min := fun (m : NatWithZero) (n : NatWithZero) =>
  match compare m n with
  | Lt => m
  | Eq => m
  | Gt => n
  end.

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition max := fun (m : NatWithZero) (n : NatWithZero) =>
  match compare m n with
  | Lt => n
  | Eq => m
  | Gt => m
  end.

Theorem min_specification
  : forall (m : NatWithZero) (n : NatWithZero), min m n = m <-> LessOrEqual m n.
Proof.
  (* The context gains [m] and [n]; both sides open into their cases. *)
  intros m n.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  split.
  - (* The context gains [e]; one goal per answer of [compare m n]. *)
    intro e.
    destruct (compare m n) as [| |] eqn:c.
    + (* [Lt]: the strict step, by the specification. *)
      apply Disjunction.right.
      exact (Biimplication.elimination_forward
              (compare m n = Lt)
              (LessThan m n)
              (compare_lt_specification m n)
              c).
    + (* [Eq]: the equality, by the specification. *)
      apply Disjunction.left.
      exact (Biimplication.elimination_forward
              (compare m n = Eq)
              (m = n)
              (compare_eq_specification m n)
              c).
    + (* [Gt]: then [e : n = m], turned round. *)
      apply Disjunction.left.
      exact (Identity.symmetry e).
  - (* The context gains [h]; the first two answers give [m] outright, and
       [Gt] contradicts [h] either way. *)
    intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + pose proof (Biimplication.elimination_forward
                    (compare m n = Gt)
                    (LessThan n m)
                    (compare_gt_specification m n)
                    c) as gt.
      destruct h as [e | lt].
      * (* [e : m = n] makes [gt : LessThan n n], against irreflexivity. *)
        rewrite e in gt.
        pose proof (less_than_irreflexivity n) as i.
        unfold Negation in i.
        pose proof (i gt) as f.
        contradiction.
      * (* [lt] and [gt] run opposite ways, against asymmetry. *)
        pose proof (less_than_asymmetry m n lt) as a.
        unfold Negation in a.
        pose proof (a gt) as f.
        contradiction.
Qed.

Theorem max_specification
  : forall (m : NatWithZero) (n : NatWithZero), max m n = m <-> LessOrEqual n m.
Proof.
  (* The mirror of [min_specification]: [Lt] is now the case that
     contradicts. *)
  intros m n.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.left.
      exact e.
    + apply Disjunction.left.
      exact (Identity.symmetry
              (Biimplication.elimination_forward
                (compare m n = Eq)
                (m = n)
                (compare_eq_specification m n)
                c)).
    + apply Disjunction.right.
      exact (Biimplication.elimination_forward
              (compare m n = Gt)
              (LessThan n m)
              (compare_gt_specification m n)
              c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + pose proof (Biimplication.elimination_forward
                    (compare m n = Lt)
                    (LessThan m n)
                    (compare_lt_specification m n)
                    c) as lt.
      destruct h as [e | gt].
      * rewrite e in lt.
        pose proof (less_than_irreflexivity m) as i.
        unfold Negation in i.
        pose proof (i lt) as f.
        contradiction.
      * pose proof (less_than_asymmetry m n lt) as a.
        unfold Negation in a.
        pose proof (a gt) as f.
        contradiction.
    + reflexivity.
    + reflexivity.
Qed.

(* [min l r] is the meet of [l] and [r], the product in the order read as a
   category: the two projections say it lies below each argument, and the
   universal property says anything below both lies below it. *)

Lemma min_left_projection
  : forall (l : NatWithZero) (r : NatWithZero), LessOrEqual (min l r) l.
Proof.
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.left (Identity.reflexivity l)).
  - exact (Disjunction.left (Identity.reflexivity l)).
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
            (compare l r = Gt)
            (LessThan r l)
            (compare_gt_specification l r)
            c).
Qed.

Lemma min_right_projection
  : forall (l : NatWithZero) (r : NatWithZero), LessOrEqual (min l r) r.
Proof.
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
            (compare l r = Lt)
            (LessThan l r)
            (compare_lt_specification l r)
            c).
  - apply Disjunction.left.
    exact (Biimplication.elimination_forward
            (compare l r = Eq)
            (l = r)
            (compare_eq_specification l r)
            c).
  - exact (Disjunction.left (Identity.reflexivity r)).
Qed.

Lemma min_universality
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessOrEqual k m -> LessOrEqual k n -> LessOrEqual k (min m n).
Proof.
  (* Whichever of [m] and [n] the smaller is, [k] is below it. *)
  intros k m n h1 h2.
  unfold min in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h1.
  - exact h1.
  - exact h2.
Qed.

(* [max l r] is the join, the coproduct: the two injections say each argument
   lies below it, and the universal property says it lies below anything
   above both. *)

Lemma max_left_injection
  : forall (l : NatWithZero) (r : NatWithZero), LessOrEqual l (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
            (compare l r = Lt)
            (LessThan l r)
            (compare_lt_specification l r)
            c).
  - exact (Disjunction.left (Identity.reflexivity l)).
  - exact (Disjunction.left (Identity.reflexivity l)).
Qed.

Lemma max_right_injection
  : forall (l : NatWithZero) (r : NatWithZero), LessOrEqual r (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.left (Identity.reflexivity r)).
  - apply Disjunction.left.
    exact (Identity.symmetry
             (Biimplication.elimination_forward
                (compare l r = Eq)
                (l = r)
                (compare_eq_specification l r)
                c)).
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
             (compare l r = Gt) (LessThan r l)
             (compare_gt_specification l r) c).
Qed.

Lemma max_universality
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      LessOrEqual m k -> LessOrEqual n k -> LessOrEqual (max m n) k.
Proof.
  intros k m n h1 h2.
  unfold max in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h2.
  - exact h1.
  - exact h1.
Qed.

(* Two greatest lower bounds of the same pair are equal, by antisymmetry;
   the same for the least upper bounds. *)

Theorem min_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), min m n = min n m.
Proof.
  (* Each side is below both [m] and [n], hence below the other. *)
  intros m n.
  apply (less_or_equal_antisymmetry (min m n) (min n m)).
  - exact (min_universality (min m n)
            n
            m
            (min_right_projection m n)
            (min_left_projection m n)).
  - exact (min_universality (min n m)
            m
            n
            (min_right_projection n m)
            (min_left_projection n m)).
Qed.

Theorem max_commutativity
  : forall (m : NatWithZero) (n : NatWithZero), max m n = max n m.
Proof.
  (* Each side is above both [m] and [n], hence above the other. *)
  intros m n.
  apply (less_or_equal_antisymmetry (max m n) (max n m)).
  - exact (max_universality (max n m)
            m
            n
            (max_right_injection n m)
            (max_left_injection n m)).
  - exact (max_universality (max m n)
            n
            m
            (max_right_injection m n)
            (max_left_injection m n)).
Qed.

Theorem min_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      min (min l m) n = min l (min m n).
Proof.
  intros l m n.
  apply (less_or_equal_antisymmetry (min (min l m) n) (min l (min m n))).
  - apply (min_universality
            (min (min l m) n) l (min m n)).
    + exact (less_or_equal_transitivity
              (min (min l m) n)  (min l m) l
              (min_left_projection (min l m) n) (min_left_projection l m)).
    + apply (min_universality (min (min l m) n) m n).
      * exact (less_or_equal_transitivity (min (min l m) n) (min l m) m
                (min_left_projection (min l m) n) (min_right_projection l m)).
      * exact (min_right_projection (min l m) n).
  - apply (min_universality (min l (min m n)) (min l m) n).
    + apply (min_universality (min l (min m n)) l m).
      * exact (min_left_projection l (min m n)).
      * exact (less_or_equal_transitivity (min l (min m n)) (min m n) m
                (min_right_projection l (min m n)) (min_left_projection m n)).
    + exact (less_or_equal_transitivity (min l (min m n)) (min m n) n
               (min_right_projection l (min m n)) (min_right_projection m n)).
Qed.

Theorem max_associativity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      max (max l m) n = max l (max m n).
Proof.
  intros l m n.

  apply (less_or_equal_antisymmetry
          (max (max l m) n)
          (max l (max m n))).

  - apply (max_universality
            (max l (max m n))
            (max l m)
            n).

    + apply (max_universality
              (max l (max m n))
              l
              m).

      * exact (max_left_injection
                l
                (max m n)).

      * exact (less_or_equal_transitivity
                m
                (max m n)
                (max l (max m n))
                (max_left_injection m n)
                (max_right_injection l (max m n))).

    + exact (less_or_equal_transitivity
              n
              (max m n)
              (max l (max m n))
              (max_right_injection m n)
              (max_right_injection l (max m n))).

  - apply (max_universality
            (max (max l m) n)
            l
            (max m n)).

    + exact (less_or_equal_transitivity
              l
              (max l m)
              (max (max l m) n)
              (max_left_injection l m)
              (max_left_injection (max l m) n)).

    + apply (max_universality
              (max (max l m) n)
              m
              n).

      * exact (less_or_equal_transitivity
                m
                (max l m)
                (max (max l m) n)
                (max_right_injection l m)
                (max_left_injection (max l m) n)).

      * exact (max_right_injection
                (max l m)
                n).
Qed.

Theorem min_idempotence : forall (n : NatWithZero), min n n = n.
Proof.
  intros n.
  unfold min in |- *.
  rewrite (compare_reflexivity n) in |- *.
  reflexivity.
Qed.

Theorem max_idempotence : forall (n : NatWithZero), max n n = n.
Proof.
  intros n.
  unfold max in |- *.
  rewrite (compare_reflexivity n) in |- *.
  reflexivity.
Qed.

Lemma max_left_identity : forall (n : NatWithZero), max Zero n = n.
Proof.
  intros n.
  unfold max in |- *.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Lemma max_right_identity : forall (n : NatWithZero), max n Zero = n.
Proof.
  intros n.
  rewrite (max_commutativity n Zero) in |- *.
  exact (max_left_identity n).
Qed.

(* [Zero] absorbs under [min], being the least element. *)
Theorem min_left_absorption : forall (n : NatWithZero), min Zero n = Zero.
Proof.
  (* The context gains [n]: [|- min Zero n = Zero] *)
  intros n.
  unfold min in |- *.
  (* [compare Zero n] computes once [n] is a ctor, to [Eq] or [Lt]; both
     branches answer [Zero]. *)
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem min_right_absorption : forall (n : NatWithZero), min n Zero = Zero.
Proof.
  (* Commutativity brings it to the left law. *)
  intros n.
  rewrite (min_commutativity n Zero) in |- *.
  exact (min_left_absorption n).
Qed.

(* Addition distributes over [min]: shifting both candidates by [k] shifts
   the smaller one. Whichever candidate is below, [min] picks it on both
   sides, by its specification and monotonicity. *)
Theorem add_left_distributivity_over_min
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      add k (min m n) = min (add k m) (add k n).
Proof.
  (* The context gains [k], [m] and [n]; one goal per side of totality. *)
  intros k m n.
  pose proof (less_or_equal_totality m n) as t.
  destruct t as [h | h].
  - (* [h : LessOrEqual m n]: both [min]s pick the left candidate:
       [|- add k m = add k m] *)
    rewrite (Biimplication.elimination_backward
               (min m n = m) (LessOrEqual m n) (min_specification m n) h) in |- *.
    rewrite (Biimplication.elimination_backward
               (min (add k m) (add k n) = add k m) (LessOrEqual (add k m) (add k n))
               (min_specification (add k m) (add k n)) (add_monotonicity k m n h))
      in |- *.
    reflexivity.
  - (* [h : LessOrEqual n m]: commutativity turns both [min]s round, and
       they pick the right candidate: [|- add k n = add k n] *)
    rewrite (min_commutativity m n) in |- *.
    rewrite (min_commutativity (add k m) (add k n)) in |- *.
    rewrite (Biimplication.elimination_backward
               (min n m = n) (LessOrEqual n m) (min_specification n m) h) in |- *.
    rewrite (Biimplication.elimination_backward
               (min (add k n) (add k m) = add k n) (LessOrEqual (add k n) (add k m))
               (min_specification (add k n) (add k m)) (add_monotonicity k n m h))
      in |- *.
    reflexivity.
Qed.

(* Truncated subtraction. A [Zero] on either side is settled without
   recursion; two positives fall to [Nat.subtract], whose [None] is the
   truncation. *)

(* [NatWithZero -> NatWithZero -> NatWithZero] *)
Definition subtract := fun (m : NatWithZero) (n : NatWithZero) =>
  match m with
  | Zero       => Zero
  | Positive p =>
      match n with
      | Zero       => Positive p
      | Positive q =>
          match Nat.subtract p q with
          | None   => Zero
          | Some k => Positive k
          end
      end
  end.

(* Taking away what was added gives the rest back: subtraction inverts
   addition. *)
Theorem subtract_inversion_of_add
  : forall (m : NatWithZero) (n : NatWithZero), subtract (add m n) n = m.
Proof.
  (* The context gains [m] and [n]; one goal per ctor pair. *)
  intros m n.
  destruct n as [| n'].
  - destruct m as [| m'].
    + (* Everything computes: [|- Zero = Zero] *)
      simpl in |- *.
      reflexivity.
    + (* [add _ Zero] and [subtract _ Zero] compute:
         [|- Positive m' = Positive m'] *)
      simpl in |- *.
      reflexivity.
  - destruct m as [| m'].
    + (* [|- match Nat.subtract n' n' with ... end = Zero] after computing *)
      simpl in |- *.
      (* Truncation on the diagonal answers [None], whose branch computes:
         [|- Zero = Zero] *)
      rewrite (Nat.subtract_truncation n' n' (Nat.less_or_equal_reflexivity n')) in |- *.
      simpl in |- *.
      reflexivity.
    + (* [|- match Nat.subtract (Nat.add m' n') n' with ... end = Positive m']
         after computing *)
      simpl in |- *.
      (* The inversion answers [Some m'], whose branch computes:
         [|- Positive m' = Positive m'] *)
      rewrite (Nat.subtract_inversion_of_add m' n') in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* Below or equal, the difference is [Zero]. *)
Theorem subtract_truncation
  : forall (m : NatWithZero) (n : NatWithZero), LessOrEqual m n -> subtract m n = Zero.
Proof.
  (* The context gains [m], [n] and [h], an equality or a strict step. *)
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - (* [e : m = n] replaces [m]: [|- subtract n n = Zero], one goal per
       ctor of [n]. *)
    rewrite e in |- *.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + (* [|- match Nat.subtract n' n' with ... end = Zero] after computing *)
      simpl in |- *.
      (* Truncation on the diagonal answers [None], whose branch computes:
         [|- Zero = Zero] *)
      rewrite (Nat.subtract_truncation n' n' (Nat.less_or_equal_reflexivity n')) in |- *.
      simpl in |- *.
      reflexivity.
  - (* [lt] opens into [k] and [e : add m (Positive k) = n]; turned round it
       replaces [n]: [|- subtract m (add m (Positive k)) = Zero] *)
    unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    (* One goal per ctor of [m]. *)
    destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + (* [|- match Nat.subtract m' (Nat.add m' k) with ... end = Zero] after
         computing *)
      simpl in |- *.
      (* [m'] is below the sum, so truncation answers [None], whose branch
         computes: [|- Zero = Zero] *)
      rewrite (Nat.subtract_truncation m' (Nat.add m' k)
                 (Disjunction.right (Nat.add_left_inflation m' k))) in |- *.
      simpl in |- *.
      reflexivity.
Qed.

(* Above or equal, the difference put back gives the number: subtraction
   inverts addition where it is not truncated. *)
Theorem subtract_specification
  : forall (m : NatWithZero) (n : NatWithZero),
      LessOrEqual n m -> add n (subtract m n) = m.
Proof.
  (* The context gains [m], [n] and [h], an equality or a strict step. *)
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - (* [e : n = m] replaces [n]; [subtract m m] is [Zero] by truncation,
       and [add m Zero] computes once [m] is a ctor. *)
    rewrite e in |- *.
    rewrite (subtract_truncation m m (less_or_equal_reflexivity m)) in |- *.
    destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
  - (* [lt] opens into [k] and [e : add n (Positive k) = m]; turned round it
       replaces [m]: [|- add n (subtract (add n (Positive k)) n) = add n (Positive k)] *)
    unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    (* Commutativity puts the sum into the inversion's shape, and the
       inversion strips it: [|- add n (Positive k) = add (Positive k) n] *)
    rewrite (add_commutativity n (Positive k)) in |- *.
    rewrite (subtract_inversion_of_add (Positive k) n) in |- *.
    (* Commutativity once more: both sides are the same term. *)
    rewrite (add_commutativity n (Positive k)) in |- *.
    reflexivity.
Qed.

(* [Zero] is a right identity of subtraction: nothing is taken away. *)
Theorem subtract_right_identity : forall (n : NatWithZero), subtract n Zero = n.
Proof.
  (* The context gains [n]; [subtract] computes once [n] is a ctor. *)
  intros n.
  destruct n as [| n'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

(* Shifting both numbers by the same amount leaves the difference alone. *)
Theorem subtract_translation_invariance
  : forall (k : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      subtract (add k m) (add k n) = subtract m n.
Proof.
  (* The context gains [k], [m] and [n]. *)
  intros k m n.
  destruct k as [| k'].
  - (* [add Zero] returns its second argument: both sides are the same
       term. *)
    simpl in |- *.
    reflexivity.
  - (* One goal per ctor pair of [m] and [n]. *)
    destruct m as [| m'].
    + destruct n as [| n'].
      * (* Both sums compute to [Positive k'] and the subtraction opens on
           [Nat.subtract k' k']:
           [|- match Nat.subtract k' k' with ... end = Zero] *)
        simpl in |- *.
        (* Truncation on the diagonal answers [None], whose branch computes:
           [|- Zero = Zero] *)
        rewrite (Nat.subtract_truncation k' k' (Nat.less_or_equal_reflexivity k'))
          in |- *.
        simpl in |- *.
        reflexivity.
      * (* [|- match Nat.subtract k' (Nat.add k' n') with ... end = Zero] after
           computing *)
        simpl in |- *.
        (* [k'] is below the sum, so truncation answers [None], whose branch
           computes: [|- Zero = Zero] *)
        rewrite (Nat.subtract_truncation k' (Nat.add k' n')
                   (Disjunction.right (Nat.add_left_inflation k' n'))) in |- *.
        simpl in |- *.
        reflexivity.
    + destruct n as [| n'].
      * (* [|- match Nat.subtract (Nat.add k' m') k' with ... end = Positive m']
           after computing *)
        simpl in |- *.
        (* Commutativity puts the sum into the inversion's shape; the
           inversion answers [Some m'], whose branch computes:
           [|- Positive m' = Positive m'] *)
        rewrite (Nat.add_commutativity k' m') in |- *.
        rewrite (Nat.subtract_inversion_of_add m' k') in |- *.
        simpl in |- *.
        reflexivity.
      * (* [|- match Nat.subtract (Nat.add k' m') (Nat.add k' n') with ... end
              = match Nat.subtract m' n' with ... end] after computing *)
        simpl in |- *.
        (* The shift cancels on [Nat]: both sides are the same term. *)
        rewrite (Nat.subtract_translation_invariance k' m' n') in |- *.
        reflexivity.
Qed.

(* Euclidean division of a positive by a positive, by walking the dividend
   down: each step adds one to the remainder, and the quotient goes up when
   the remainder reaches the divisor. The divisor is a [Nat], so it is never
   zero. The result is the pair of quotient and remainder. *)
Fixpoint division (p : Nat) (d : Nat) : Pair NatWithZero NatWithZero :=
  match p with
  | One =>
      match d with
      | One         => Pair_introduction (Positive One) Zero
      | Successor _ => Pair_introduction Zero (Positive One)
      end
  | Successor p' =>
      match division p' d with
      | Pair_introduction q r =>
          match equal (add r (Positive One)) (Positive d) with
          | true  => Pair_introduction (add q (Positive One)) Zero
          | false => Pair_introduction q (add r (Positive One))
          end
      end
  end.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition divide := fun (n : NatWithZero) (d : Nat) =>
  match n with
  | Zero       => Zero
  | Positive p => Pair.first (division p d)
  end.

(* [NatWithZero -> Nat -> NatWithZero] *)
Definition modulo := fun (n : NatWithZero) (d : Nat) =>
  match n with
  | Zero       => Zero
  | Positive p => Pair.second (division p d)
  end.

(* The invariant of the walk: the dividend is quotient times divisor plus
   remainder, and the remainder stays below the divisor. Induction on the
   dividend; the step opens the pair of the previous step and follows the
   [equal] test both ways. *)
Lemma division_invariant
  : forall (p : Nat) (d : Nat),
      Positive p
      = add (mul (Pair.first (division p d)) (Positive d))
            (Pair.second (division p d))
      /\ LessThan (Pair.second (division p d)) (Positive d).
Proof.
  (* The context gains [p] and [d]. *)
  intros p d.
  (* [p] is either [One] or [Successor p']: one goal per ctor, and the
     second has [p'] and the invariant for [p'] as [IH] in its context. *)
  induction p as [| p' IH] using Nat_induction.
  - (* [d] is either [One] or [Successor d']: one goal per ctor. *)
    destruct d as [| d'].
    + (* The pair is [(Positive One, Zero)] and everything computes:
         [|- Positive One = Positive One /\ LessThan Zero (Positive One)] *)
      simpl in |- *.
      split.
      * reflexivity.
      * (* The witness is [One]: [|- add Zero (Positive One) = Positive One] *)
        unfold LessThan in |- *.
        apply (Exists_introduction One).
        simpl in |- *.
        reflexivity.
    + (* The pair is [(Zero, Positive One)] and everything computes:
         [|- Positive One = Positive One
             /\ LessThan (Positive One) (Positive (Successor d'))] *)
      simpl in |- *.
      split.
      * reflexivity.
      * (* The witness is [d']: [|- add (Positive One) (Positive d')
                                    = Positive (Successor d')] *)
        unfold LessThan in |- *.
        apply (Exists_introduction d').
        simpl in |- *.
        reflexivity.
  - (* [IH] opens into [e], the equation, and [lt], the bound. *)
    destruct IH as [e lt].
    (* One [division] step opens into a [match] on the previous pair. *)
    simpl in |- *.
    (* The previous pair is [(q, r)], with [D] recording it; [e] and [lt]
       compute to speak of [q] and [r]. *)
    destruct (division p' d) as [q r] eqn:D.
    simpl in e.
    simpl in lt.
    (* The [equal] test is [true] or [false], with [E] recording it. *)
    destruct (equal (add r (Positive One)) (Positive d)) as [|] eqn:E.
    + (* The new pair is [(add q (Positive One), Zero)]:
         [|- Positive (Successor p')
             = add (mul (add q (Positive One)) (Positive d)) Zero
             /\ LessThan Zero (Positive d)] *)
      simpl in |- *.
      split.
      * (* [E] says the remainder plus one reached the divisor:
           [full : add r (Positive One) = Positive d] *)
        pose proof (Biimplication.elimination_forward
                      (equal (add r (Positive One)) (Positive d) = true)
                      (add r (Positive One) = Positive d)
                      (equal_specification (add r (Positive One)) (Positive d))
                      E) as full.
        (* The right distributivity law, the identity of [mul] and the
           identity of [add] bring the right side to
           [add (mul q (Positive d)) (Positive d)]. *)
        rewrite (mul_right_distributivity_over_add (Positive d) q (Positive One))
          in |- *.
        rewrite (mul_left_identity (Positive d)) in |- *.
        rewrite (add_commutativity
                   (add (mul q (Positive d)) (Positive d)) Zero) in |- *.
        simpl in |- *.
        (* [full] turned round replaces [Positive d] everywhere, in the goal
           and in [e]: [|- Positive (Successor p')
                            = add (mul q (add r (Positive One)))
                                  (add r (Positive One))],
           [e : Positive p' = add (mul q (add r (Positive One))) r] *)
        pose proof (Identity.symmetry full) as full'.
        rewrite full' in |- *.
        rewrite full' in e.
        (* Associativity read right to left groups the right side:
           [|- ... = add (add (mul q (add r (Positive One))) r) (Positive One)] *)
        pose proof (Identity.symmetry
                      (add_associativity
                         (mul q (add r (Positive One))) r (Positive One))) as a.
        rewrite a in |- *.
        (* [e] turned round folds the inner sum into [Positive p']:
           [|- Positive (Successor p') = add (Positive p') (Positive One)] *)
        pose proof (Identity.symmetry e) as e'.
        rewrite e' in |- *.
        (* The right side computes to [Positive (Nat.add p' One)], which
           commutativity and one more computation turn into
           [Positive (Successor p')]. *)
        simpl in |- *.
        rewrite (Nat.add_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * (* [Zero] is below the divisor, with [d] as the witness. *)
        unfold LessThan in |- *.
        apply (Exists_introduction d).
        simpl in |- *.
        reflexivity.
    + (* The new pair is [(q, add r (Positive One))]:
         [|- Positive (Successor p')
             = add (mul q (Positive d)) (add r (Positive One))
             /\ LessThan (add r (Positive One)) (Positive d)] *)
      simpl in |- *.
      split.
      * (* Associativity read right to left groups the right side, [e]
           turned round folds the inner sum into [Positive p'], and the
           rest computes as in the other branch. *)
        pose proof (Identity.symmetry
                      (add_associativity (mul q (Positive d)) r (Positive One))) as a.
        rewrite a in |- *.
        pose proof (Identity.symmetry e) as e'.
        rewrite e' in |- *.
        simpl in |- *.
        rewrite (Nat.add_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * (* [lt] opens into [k] and [ek : add r (Positive k) = Positive d];
           [k] is either [One] or [Successor k']. *)
        unfold LessThan in lt.
        destruct lt as [k ek].
        destruct k as [| k'].
        { (* [k = One] makes [ek] the equality [E] refutes. *)
          pose proof (equal_refutation (add r (Positive One)) (Positive d) E) as ne.
          unfold Negation in ne.
          pose proof (ne ek) as f.
          contradiction. }
        { (* [k'] is the new witness: associativity opens the left side and
             the inner sum computes to [Positive (Successor k')], which is
             [ek]. *)
          unfold LessThan in |- *.
          apply (Exists_introduction k').
          rewrite (add_associativity r (Positive One) (Positive k')) in |- *.
          simpl in |- *.
          exact ek. }
Qed.

(* Quotient and remainder as the two halves of the invariant; a [Zero]
   dividend has both [Zero]. *)
Theorem division_specification
  : forall (n : NatWithZero) (d : Nat),
      n = add (mul (divide n d) (Positive d)) (modulo n d)
      /\ LessThan (modulo n d) (Positive d).
Proof.
  (* The context gains [n] and [d]; [n] is either [Zero] or [Positive p]. *)
  intros n d.
  destruct n as [| p].
  - (* Everything computes: [|- Zero = Zero /\ LessThan Zero (Positive d)] *)
    simpl in |- *.
    split.
    + reflexivity.
    + unfold LessThan in |- *.
      apply (Exists_introduction d).
      simpl in |- *.
      reflexivity.
  - (* [divide] and [modulo] open into the two projections of [division]. *)
    unfold divide in |- *.
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
  (* The context gains [n]; the witness is [Positive One]. *)
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction (Positive One)).
  exact (mul_right_identity n).
Qed.

Theorem divides_transitivity
  : forall (l : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides l m -> Divides m n -> Divides l n.
Proof.
  (* The context gains [l], [m], [n], [h1] and [h2]; they open into [k1],
   * [e1 : mul l k1 = m], [k2] and [e2 : mul m k2 = n]; the witness is the
   * product of the two.
   *)
  intros l m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (mul k1 k2)).
  (* Associativity read right to left regroups, and [e1] then [e2] close
   * it: [|- mul (mul l k1) k2 = n]
   *)
  pose proof (Identity.symmetry (mul_associativity l k1 k2)) as a.
  rewrite a in |- *.
  rewrite e1 in |- *.
  exact e2.
Qed.

(* Antisymmetry: with [m] a positive, the two witnesses multiply to a unit
 * of [Nat], which factors only as [One] times [One].
 *)
Theorem divides_antisymmetry
  : forall (m : NatWithZero) (n : NatWithZero), Divides m n -> Divides n m -> m = n.
Proof.
  (* The context gains [m], [n], [h1] and [h2]; they open into [k],
   * [e1 : mul m k = n], [j] and [e2 : mul n j = m].
   *)
  intros m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k e1].
  destruct h2 as [j e2].
  destruct m as [| p].
  - (* [mul Zero k] computes: [e1 : Zero = n] is the goal. *)
    simpl in e1.
    exact e1.
  - (* [e1] turned round puts [n] into [e2]:
     * [e2 : mul (mul (Positive p) k) j = Positive p]; one goal per ctor of
     * [k] and [j], a [Zero] making the product [Zero].
     *)
    pose proof (Identity.symmetry e1) as e1'.
    rewrite e1' in e2.
    destruct k as [| k'].
    + simpl in e2.
      discriminate.
    + destruct j as [| j'].
      * simpl in e2.
        discriminate.
      * (* [e2] computes to
         * [Positive (Nat.mul (Nat.mul p k') j') = Positive p]; injectivity
         * and associativity give [e3], and [Nat.mul One p] is [p] by
         * computation, so [e4 : Nat.mul p (Nat.mul k' j') = Nat.mul p One];
         * cancellation and the factorization of [One] leave [ek : k' = One].
         *)
        simpl in e2.
        pose proof (positive_injectivity (Nat.mul (Nat.mul p k') j') p e2) as e3.
        rewrite (Nat.mul_associativity p k' j') in e3.
        pose proof (Nat.mul_commutativity One p) as c.
        simpl in c.
        pose proof (Identity.transitivity e3 c) as e4.
        pose proof (Nat.mul_left_cancellation p (Nat.mul k' j') One e4) as e5.
        pose proof (Nat.mul_identity_factorization k' j' e5) as f.
        destruct f as [ek ej].
        (* [ek] replaces [k'] in [e1], where [mul (Positive p) (Positive One)]
         * is [Positive p] by the identity: [e1] is the goal.
         *)
        rewrite ek in e1.
        rewrite (mul_right_identity (Positive p)) in e1.
        exact e1.
Qed.

(* The multiples of [d] are closed under addition, by distributivity, and
 * under multiplication by anything, by associativity.
 *)

Theorem divides_add_closure
  : forall (d : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides d m -> Divides d n -> Divides d (add m n).
Proof.
  (* The context gains [d], [m], [n], [h1] and [h2]; they open into [k1],
   * [e1 : mul d k1 = m], [k2] and [e2 : mul d k2 = n]; the witness is the
   * sum of the two.
   *)
  intros d m n h1 h2.
  unfold Divides in h1.
  unfold Divides in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Divides in |- *.
  apply (Exists_introduction (add k1 k2)).
  (* Distributivity opens the product, and [e1] then [e2] close it. *)
  rewrite (mul_left_distributivity_over_add d k1 k2) in |- *.
  rewrite e1 in |- *.
  rewrite e2 in |- *.
  reflexivity.
Qed.

Theorem divides_mul_closure
  : forall (d : NatWithZero) (m : NatWithZero) (n : NatWithZero),
      Divides d m -> Divides d (mul m n).
Proof.
  (* The context gains [d], [m], [n] and [h]; [h] opens into [k] and
   * [e : mul d k = m]; the witness is [mul k n].
   *)
  intros d m n h.
  unfold Divides in h.
  destruct h as [k e].
  unfold Divides in |- *.
  apply (Exists_introduction (mul k n)).
  (* Associativity read right to left regroups, and [e] closes it. *)
  pose proof (Identity.symmetry (mul_associativity d k n)) as a.
  rewrite a in |- *.
  rewrite e in |- *.
  reflexivity.
Qed.

(* [Positive One] is the least element of divisibility and [Zero] the
 * greatest: everything is a multiple of the first, the second a multiple
 * of everything.
 *)

Theorem divides_least : forall (n : NatWithZero), Divides (Positive One) n.
Proof.
  (* The context gains [n]; the witness is [n] itself. *)
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction n).
  exact (mul_left_identity n).
Qed.

Theorem divides_greatest : forall (n : NatWithZero), Divides n Zero.
Proof.
  (* The context gains [n]; the witness is [Zero], and commutativity turns
   * the product round to compute.
   *)
  intros n.
  unfold Divides in |- *.
  apply (Exists_introduction Zero).
  rewrite (mul_commutativity n Zero) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

(* Parity: even is divisible by two, odd is one more than an even number. *)

(* [NatWithZero -> Prop] *)
Definition Even := fun (n : NatWithZero) => Divides (Positive (Successor One)) n.

(* [NatWithZero -> Prop] *)
Definition Odd := fun (n : NatWithZero) =>
  exists (k : NatWithZero), add (mul (Positive (Successor One)) k) (Positive One) = n.

(* Every number is even or odd: [Zero] is even, and each step from a
 * number swaps its parity, the odd witness being the even one and the
 * even witness one more than the odd one.
 *)
Theorem even_or_odd : forall (n : NatWithZero), Even n \/ Odd n.
Proof.
  (* The context gains [n]; one goal per ctor. *)
  intros n.
  destruct n as [| p].
  - (* [Zero] is twice [Zero]. *)
    apply Disjunction.left.
    unfold Even in |- *.
    unfold Divides in |- *.
    apply (Exists_introduction Zero).
    simpl in |- *.
    reflexivity.
  - (* [p] is either [One] or [Successor p']: one goal per ctor, and the
     * second has [IH : Even (Positive p') \/ Odd (Positive p')] in its
     * context.
     *)
    induction p as [| p' IH] using Nat_induction.
    + (* [Positive One] is one more than twice [Zero]. *)
      apply Disjunction.right.
      unfold Odd in |- *.
      apply (Exists_introduction Zero).
      simpl in |- *.
      reflexivity.
    + destruct IH as [ev | od].
      * (* [ev] opens into [k] and [e : mul two k = Positive p']; the same
         * witness makes the next number odd: [e] replaces the product, and
         * [add (Positive p') (Positive One)] computes to
         * [Positive (Nat.add p' One)], the sum turned round.
         *)
        apply Disjunction.right.
        unfold Even in ev.
        unfold Divides in ev.
        destruct ev as [k e].
        unfold Odd in |- *.
        apply (Exists_introduction k).
        rewrite e in |- *.
        simpl in |- *.
        rewrite (Nat.add_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
      * (* [od] opens into [k] and
         * [e : add (mul two k) (Positive One) = Positive p']; one more than
         * [k] makes the next number even: distributivity opens the product,
         * [mul two (Positive One)] is [add (Positive One) (Positive One)] by
         * computation, and regrouping puts [e] back together.
         *)
        apply Disjunction.left.
        unfold Odd in od.
        destruct od as [k e].
        unfold Even in |- *.
        unfold Divides in |- *.
        apply (Exists_introduction (add k (Positive One))).
        rewrite (mul_left_distributivity_over_add
                   (Positive (Successor One)) k (Positive One)) in |- *.
        change (mul (Positive (Successor One)) (Positive One))
          with (add (Positive One) (Positive One)) in |- *.
        pose proof (Identity.symmetry
                      (add_associativity
                         (mul (Positive (Successor One)) k) (Positive One) (Positive One)))
          as a.
        rewrite a in |- *.
        rewrite e in |- *.
        (* [add (Positive p') (Positive One)] computes to
         * [Positive (Nat.add p' One)], the sum turned round.
         *)
        simpl in |- *.
        rewrite (Nat.add_commutativity p' One) in |- *.
        simpl in |- *.
        reflexivity.
Qed.

Theorem even_add_even
  : forall (m : NatWithZero) (n : NatWithZero), Even m -> Even n -> Even (add m n).
Proof.
  (* Closure of the multiples of two under addition. *)
  intros m n h1 h2.
  unfold Even in h1.
  unfold Even in h2.
  unfold Even in |- *.
  exact (divides_add_closure (Positive (Successor One)) m n h1 h2).
Qed.

(* Two odd numbers add to an even one: the two ones make a two, which
 * distributivity absorbs into the witness.
 *)
Theorem odd_add_odd
  : forall (m : NatWithZero) (n : NatWithZero), Odd m -> Odd n -> Even (add m n).
Proof.
  (* The context gains [m], [n], [h1] and [h2]; they open into [k1], [e1],
   * [k2] and [e2]; the witness is [add (add k1 k2) (Positive One)].
   *)
  intros m n h1 h2.
  unfold Odd in h1.
  unfold Odd in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  unfold Even in |- *.
  unfold Divides in |- *.
  apply (Exists_introduction (add (add k1 k2) (Positive One))).
  (* [e1] and [e2] turned round replace [m] and [n]; distributivity opens
   * the product twice, [mul two (Positive One)] is
   * [add (Positive One) (Positive One)] by computation, and the interchange
   * law pairs the right side the same way.
   *)
  pose proof (Identity.symmetry e1) as e1'.
  pose proof (Identity.symmetry e2) as e2'.
  rewrite e1' in |- *.
  rewrite e2' in |- *.
  rewrite (mul_left_distributivity_over_add
             (Positive (Successor One)) (add k1 k2) (Positive One)) in |- *.
  rewrite (mul_left_distributivity_over_add (Positive (Successor One)) k1 k2) in |- *.
  change (mul (Positive (Successor One)) (Positive One))
    with (add (Positive One) (Positive One)) in |- *.
  rewrite (add_interchange
             (mul (Positive (Successor One)) k1) (Positive One)
             (mul (Positive (Successor One)) k2) (Positive One)) in |- *.
  reflexivity.
Qed.

End NatWithZero.

(* The scope is declared in [Core.Notations] and never opened: a client
   writes [(m + n)%nat_with_zero]. [only parsing] keeps the operations
   printed by name. *)
Notation "m + n" := (NatWithZero.add m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m * n" := (NatWithZero.mul m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m < n" := (NatWithZero.LessThan m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m <= n" := (NatWithZero.LessOrEqual m n) (only parsing)
  : jwa_nat_with_zero_scope.

(* The reversed spellings name no new relation, as for [Nat]. *)
Notation "m > n" := (NatWithZero.LessThan n m) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m >= n" := (NatWithZero.LessOrEqual n m) (only parsing)
  : jwa_nat_with_zero_scope.

(* [Zero] is exactly what [Nat] lacks, so this one reaches monoid. The
   [semigroup] field is filled inline rather than by a second instance:
   [Monoid.semigroup] is declared with [::], so resolution already finds a
   [Semigroup.T NatWithZero add] through it. *)
Instance NatWithZero_add_monoid
  : Monoid.T NatWithZero NatWithZero.add Zero := {|
    Monoid.semigroup :=
      {| Semigroup.associativity := NatWithZero.add_associativity |}
  ; Monoid.left_identity  :=
      fun (n : NatWithZero) => Identity.reflexivity (NatWithZero.add Zero n)
  ; Monoid.right_identity :=
      fun (n : NatWithZero) => NatWithZero.add_commutativity n Zero
  |}.

(* Both cancellation laws were already proved above, so the instance only
   hands them over. *)
Instance NatWithZero_add_cancellative
  : Cancellative.T NatWithZero NatWithZero.add := {|
    Cancellative.left_cancellation  := NatWithZero.add_left_cancellation
  ; Cancellative.right_cancellation := NatWithZero.add_right_cancellation
  |}.

(* [Positive One] leaves its argument alone under [mul]. *)
Instance NatWithZero_mul_monoid
  : Monoid.T NatWithZero NatWithZero.mul (Positive One) := {|
    Monoid.semigroup      := {| Semigroup.associativity := NatWithZero.mul_associativity |}
  ; Monoid.left_identity  := NatWithZero.mul_left_identity
  ; Monoid.right_identity := NatWithZero.mul_right_identity
  |}.

Instance NatWithZero_add_commutative
  : Commutative.T NatWithZero NatWithZero.add := {|
      Commutative.commutativity := NatWithZero.add_commutativity
  |}.

Instance NatWithZero_mul_commutative
  : Commutative.T NatWithZero NatWithZero.mul := {|
    Commutative.commutativity := NatWithZero.mul_commutativity
  |}.

(* The two orders as instances of the [Relation] classes, as for [Nat]. *)
Instance NatWithZero_less_than_strict_order
  : StrictOrder NatWithZero.LessThan :=
  {| StrictOrder.irreflexivity :=
       {| Irreflexive.irreflexivity := NatWithZero.less_than_irreflexivity |}
   ; StrictOrder.transitivity :=
       {| Transitive.transitivity := NatWithZero.less_than_transitivity |} |}.

Instance NatWithZero_less_or_equal_total_order
  : TotalOrder NatWithZero.LessOrEqual :=
  {| TotalOrder.partial_order :=
      {| PartialOrder.reflexivity :=
          {| Reflexive.reflexivity := NatWithZero.less_or_equal_reflexivity |}
       ; PartialOrder.antisymmetry :=
          {| Antisymmetric.antisymmetry := NatWithZero.less_or_equal_antisymmetry |}
       ; PartialOrder.transitivity :=
          {| Transitive.transitivity := NatWithZero.less_or_equal_transitivity |} |}
   ; TotalOrder.totality :=
      {| Total.totality := NatWithZero.less_or_equal_totality |} |}.

(* [min] has no identity, since [Zero] absorbs it; [max] has [Zero].
   Both commute. *)
Instance NatWithZero_min_semigroup
  : Semigroup.T NatWithZero NatWithZero.min :=
  {| Semigroup.associativity := NatWithZero.min_associativity |}.

Instance NatWithZero_max_monoid
  : Monoid.T NatWithZero NatWithZero.max Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := NatWithZero.max_associativity |}
   ; Monoid.left_identity  := NatWithZero.max_left_identity
   ; Monoid.right_identity := NatWithZero.max_right_identity |}.

Instance NatWithZero_min_commutative
  : Commutative.T NatWithZero NatWithZero.min :=
  {| Commutative.commutativity := NatWithZero.min_commutativity |}.

Instance NatWithZero_max_commutative
  : Commutative.T NatWithZero NatWithZero.max :=
  {| Commutative.commutativity := NatWithZero.max_commutativity |}.

(* With [add] and [mul] together, [NatWithZero] is a semiring: the two
 * monoids above, distributivity, and [Zero] absorbing under [mul], which
 * computes on the left and is commutativity on the right.
 *)
Instance NatWithZero_semiring
  : Semiring.T NatWithZero NatWithZero.add Zero NatWithZero.mul (Positive One) :=
  {| Semiring.add_monoid           := NatWithZero_add_monoid
   ; Semiring.add_commutative      := NatWithZero_add_commutative
   ; Semiring.mul_monoid           := NatWithZero_mul_monoid
   ; Semiring.left_distributivity  := NatWithZero.mul_left_distributivity_over_add
   ; Semiring.right_distributivity := NatWithZero.mul_right_distributivity_over_add
   ; Semiring.left_absorption      :=
       fun (n : NatWithZero) => Identity.reflexivity (NatWithZero.mul Zero n)
   ; Semiring.right_absorption     :=
       fun (n : NatWithZero) => NatWithZero.mul_commutativity n Zero |}.

(* Divisibility as an instance of the partial order class. *)
Instance NatWithZero_divides_partial_order
  : PartialOrder NatWithZero.Divides :=
  {| PartialOrder.reflexivity :=
       {| Reflexive.reflexivity := NatWithZero.divides_reflexivity |}
   ; PartialOrder.antisymmetry :=
       {| Antisymmetric.antisymmetry := NatWithZero.divides_antisymmetry |}
   ; PartialOrder.transitivity :=
       {| Transitive.transitivity := NatWithZero.divides_transitivity |} |}.
