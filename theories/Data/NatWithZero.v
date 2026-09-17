(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->], [=], [~], [/\], [\/] and [exists]; [Data.Nat] is
   the type [Positive] wraps and the source of every law under [Positive];
   [Structures.Semigroup], [Structures.Monoid], [Structures.Commutative],
   [Structures.Cancellative] and the [Relations] order classes are what the
   instances at the bottom fill; [Data.Comparison] is what [compare] answers
   in, [Data.Bool] what [equal] answers in, [Data.Pair] what [division]
   answers in, and [Data.Option] what [Nat.subtract] answers in. *)
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparison.
From jwa Require Import Data.Nat.
From jwa Require Import Data.Option.
From jwa Require Import Data.Pair.
From jwa Require Import Relations.Antisymmetric.
From jwa Require Import Relations.Irreflexive.
From jwa Require Import Relations.PartialOrder.
From jwa Require Import Relations.Reflexive.
From jwa Require Import Relations.StrictOrder.
From jwa Require Import Relations.Total.
From jwa Require Import Relations.TotalOrder.
From jwa Require Import Relations.Transitive.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Cancellative.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Semigroup.

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
  pose proof (Equijunction_congruence
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
  unfold Unjunction in |- *.
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
        pose proof (Equijunction_symmetry e') as e''.
        rewrite (Nat.add_commutativity n' k') in e''.
        (* [h : Nat.add k' n' = n' -> Falsum], once unfolded *)
        pose proof (Nat.add_identity_absence k' n') as h.
        unfold Unjunction in h.
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
        unfold Unjunction in h.
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  unfold Unjunction in |- *.
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
    unfold Unjunction in i.
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
  pose proof (Equijunction_symmetry e2) as e2'.
  rewrite e2' in |- *.
  pose proof (Equijunction_symmetry e1) as e1'.
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
  unfold Unjunction in |- *.
  (* The context gains [h2 : LessThan n m]: [|- Falsum] *)
  intro h2.
  (* The two compose into [h : LessThan m m], against irreflexivity. *)
  pose proof (less_than_transitivity m n m h1 h2) as h.
  pose proof (less_than_irreflexivity m) as i.
  unfold Unjunction in i.
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
      exact (Disjunction_right (Disjunction_left (Equijunction_reflexivity Zero))).
    + (* [Zero] is below, with [n'] as the witness:
         [|- add Zero (Positive n') = Positive n'] *)
      apply Disjunction_left.
      unfold LessThan in |- *.
      apply (Exists_introduction n').
      simpl in |- *.
      reflexivity.
  - (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* The mirror: [|- add Zero (Positive m') = Positive m'] *)
      apply Disjunction_right.
      apply Disjunction_right.
      unfold LessThan in |- *.
      apply (Exists_introduction m').
      simpl in |- *.
      reflexivity.
    + (* [Nat]'s trichotomy on [m'] and [n'], each case lifted under
         [Positive]. *)
      pose proof (Nat.less_than_trichotomy m' n') as t.
      destruct t as [lt | rest].
      * apply Disjunction_left.
        exact (Bijunction_elimination_backward
                 (LessThan (Positive m') (Positive n')) (Nat.LessThan m' n')
                 (less_than_positive_embedding m' n') lt).
      * destruct rest as [eq | gt].
        { (* [eq : m' = n'] replaces [m']. *)
          apply Disjunction_right.
          apply Disjunction_left.
          rewrite eq in |- *.
          reflexivity. }
        { apply Disjunction_right.
          apply Disjunction_right.
          exact (Bijunction_elimination_backward
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
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    (* Everything computes: [|- Positive (Nat.mul k d) = Positive (Nat.mul k d)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [e : Positive (Nat.add m' d) = n] *)
    simpl in e.
    pose proof (Equijunction_symmetry e) as e'.
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

Theorem less_or_equal_reflexivity : forall (n : NatWithZero), LessOrEqual n n.
Proof.
  (* The context gains [n]: [|- LessOrEqual n n] *)
  intros n.
  (* [|- n = n \/ LessThan n n], and the left side holds. *)
  unfold LessOrEqual in |- *.
  exact (Disjunction_left (Equijunction_reflexivity n)).
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
      exact (Disjunction_right lt1).
    + (* Two strict steps compose. *)
      exact (Disjunction_right (less_than_transitivity l m n lt1 lt2)).
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
      exact (Equijunction_symmetry e2).
    + (* Two strict steps in opposite directions contradict asymmetry. *)
      pose proof (less_than_asymmetry m n lt1) as h.
      unfold Unjunction in h.
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
  - exact (Disjunction_left (Disjunction_right lt)).
  - destruct rest as [eq | gt].
    + exact (Disjunction_left (Disjunction_left eq)).
    + exact (Disjunction_right (Disjunction_right gt)).
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
      compare m n = Comparison.converse (compare n m).
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
        unfold Unjunction in i.
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
        exact (Bijunction_elimination_backward
                 (LessThan (Positive m') (Positive n')) (Nat.LessThan m' n')
                 (less_than_positive_embedding m' n')
                 (Nat.compare_lt_specification_forward m' n' e)).
      * intro h.
        simpl in |- *.
        exact (Nat.compare_lt_specification_backward
                m'
                n'
                (Bijunction_elimination_forward
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
       [e : Comparison.converse (compare n m) = Gt], and only [Lt] has
       [Gt] as its converse. *)
    intro e.
    rewrite (compare_antisymmetry m n) in e.
    destruct (compare n m) as [| |] eqn:c.
    + exact (Bijunction_elimination_forward
               (compare n m = Lt) (LessThan n m)
               (compare_lt_specification n m) c).
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
  - (* The context gains [h : LessThan n m]; [compare n m] is [Lt] by the
       first specification, and its converse computes to [Gt]. *)
    intro h.
    rewrite (compare_antisymmetry m n) in |- *.
    rewrite (Bijunction_elimination_backward
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
    + exact (Bijunction_elimination_forward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) c).
    + discriminate.
  - (* The context gains [e : m = n]; [compare m n] is [Eq]:
       [|- true = true] *)
    intro e.
    unfold equal in |- *.
    rewrite (Bijunction_elimination_backward
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
  unfold Unjunction in |- *.
  (* The context gains [h : m = n]: [|- Falsum] *)
  intro h.
  (* [equal_specification] turns [h] into [equal m n = true], which
     replaces the left side of [e]: [e : true = false] *)
  rewrite (Bijunction_elimination_backward
             (equal m n = true) (m = n) (equal_specification m n) h) in e.
  (* [e] equates two distinct ctors, which closes any goal. *)
  discriminate.
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
      apply Disjunction_right.
      exact (Bijunction_elimination_forward
              (compare m n = Lt)
              (LessThan m n)
              (compare_lt_specification m n)
              c).
    + (* [Eq]: the equality, by the specification. *)
      apply Disjunction_left.
      exact (Bijunction_elimination_forward
              (compare m n = Eq)
              (m = n)
              (compare_eq_specification m n)
              c).
    + (* [Gt]: then [e : n = m], turned round. *)
      apply Disjunction_left.
      exact (Equijunction_symmetry e).
  - (* The context gains [h]; the first two answers give [m] outright, and
       [Gt] contradicts [h] either way. *)
    intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + pose proof (Bijunction_elimination_forward
                    (compare m n = Gt)
                    (LessThan n m)
                    (compare_gt_specification m n)
                    c) as gt.
      destruct h as [e | lt].
      * (* [e : m = n] makes [gt : LessThan n n], against irreflexivity. *)
        rewrite e in gt.
        pose proof (less_than_irreflexivity n) as i.
        unfold Unjunction in i.
        pose proof (i gt) as f.
        contradiction.
      * (* [lt] and [gt] run opposite ways, against asymmetry. *)
        pose proof (less_than_asymmetry m n lt) as a.
        unfold Unjunction in a.
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
    + apply Disjunction_left.
      exact e.
    + apply Disjunction_left.
      exact (Equijunction_symmetry
              (Bijunction_elimination_forward
                (compare m n = Eq)
                (m = n)
                (compare_eq_specification m n)
                c)).
    + apply Disjunction_right.
      exact (Bijunction_elimination_forward
              (compare m n = Gt)
              (LessThan n m)
              (compare_gt_specification m n)
              c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + pose proof (Bijunction_elimination_forward
                    (compare m n = Lt)
                    (LessThan m n)
                    (compare_lt_specification m n)
                    c) as lt.
      destruct h as [e | gt].
      * rewrite e in lt.
        pose proof (less_than_irreflexivity m) as i.
        unfold Unjunction in i.
        pose proof (i lt) as f.
        contradiction.
      * pose proof (less_than_asymmetry m n lt) as a.
        unfold Unjunction in a.
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
  - exact (Disjunction_left (Equijunction_reflexivity l)).
  - exact (Disjunction_left (Equijunction_reflexivity l)).
  - apply Disjunction_right.
    exact (Bijunction_elimination_forward
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
  - apply Disjunction_right.
    exact (Bijunction_elimination_forward
            (compare l r = Lt)
            (LessThan l r)
            (compare_lt_specification l r)
            c).
  - apply Disjunction_left.
    exact (Bijunction_elimination_forward
            (compare l r = Eq)
            (l = r)
            (compare_eq_specification l r)
            c).
  - exact (Disjunction_left (Equijunction_reflexivity r)).
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
  - apply Disjunction_right.
    exact (Bijunction_elimination_forward
            (compare l r = Lt)
            (LessThan l r)
            (compare_lt_specification l r)
            c).
  - exact (Disjunction_left (Equijunction_reflexivity l)).
  - exact (Disjunction_left (Equijunction_reflexivity l)).
Qed.

Lemma max_right_injection
  : forall (l : NatWithZero) (r : NatWithZero), LessOrEqual r (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction_left (Equijunction_reflexivity r)).
  - apply Disjunction_left.
    exact (Equijunction_symmetry
             (Bijunction_elimination_forward
                (compare l r = Eq)
                (l = r)
                (compare_eq_specification l r)
                c)).
  - apply Disjunction_right.
    exact (Bijunction_elimination_forward
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
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    (* One goal per ctor of [m]. *)
    destruct m as [| m'].
    + simpl in |- *.
      reflexivity.
    + (* [m'] is below [Nat.add m' k] with [k] as the witness; the claim
         comes first, then the goal with [h : Nat.LessOrEqual m' (Nat.add m' k)]. *)
      assert (h : Nat.LessOrEqual m' (Nat.add m' k)).
      * unfold Nat.LessOrEqual in |- *.
        apply Disjunction_right.
        unfold Nat.LessThan in |- *.
        apply (Exists_introduction k).
        (* [|- Nat.add m' k = Nat.add m' k] *)
        reflexivity.
      * (* [|- match Nat.subtract m' (Nat.add m' k) with ... end = Zero] after
           computing *)
        simpl in |- *.
        (* Truncation answers [None], whose branch computes: [|- Zero = Zero] *)
        rewrite (Nat.subtract_truncation m' (Nat.add m' k) h) in |- *.
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
    pose proof (Equijunction_symmetry e) as e'.
    rewrite e' in |- *.
    (* Commutativity puts the sum into the inversion's shape, and the
       inversion strips it: [|- add n (Positive k) = add (Positive k) n] *)
    rewrite (add_commutativity n (Positive k)) in |- *.
    rewrite (subtract_inversion_of_add (Positive k) n) in |- *.
    (* Commutativity once more: both sides are the same term. *)
    rewrite (add_commutativity n (Positive k)) in |- *.
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
        pose proof (Bijunction_elimination_forward
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
        pose proof (Equijunction_symmetry full) as full'.
        rewrite full' in |- *.
        rewrite full' in e.
        (* Associativity read right to left groups the right side:
           [|- ... = add (add (mul q (add r (Positive One))) r) (Positive One)] *)
        pose proof (Equijunction_symmetry
                      (add_associativity
                         (mul q (add r (Positive One))) r (Positive One))) as a.
        rewrite a in |- *.
        (* [e] turned round folds the inner sum into [Positive p']:
           [|- Positive (Successor p') = add (Positive p') (Positive One)] *)
        pose proof (Equijunction_symmetry e) as e'.
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
        pose proof (Equijunction_symmetry
                      (add_associativity (mul q (Positive d)) r (Positive One))) as a.
        rewrite a in |- *.
        pose proof (Equijunction_symmetry e) as e'.
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
          unfold Unjunction in ne.
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
      fun (n : NatWithZero) => Equijunction_reflexivity (NatWithZero.add Zero n)
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

(* The two orders as instances of the [Relations] classes, as for [Nat]. *)
Instance NatWithZero_less_than_strict_order
  : StrictOrder.R NatWithZero NatWithZero.LessThan :=
  {| StrictOrder.irreflexive :=
       {| Irreflexive.irreflexivity := NatWithZero.less_than_irreflexivity |}
   ; StrictOrder.transitive :=
       {| Transitive.transitivity := NatWithZero.less_than_transitivity |} |}.

Instance NatWithZero_less_or_equal_total_order
  : TotalOrder.R NatWithZero NatWithZero.LessOrEqual :=
  {| TotalOrder.partial_order :=
      {| PartialOrder.reflexive :=
          {| Reflexive.reflexivity := NatWithZero.less_or_equal_reflexivity |}
       ; PartialOrder.antisymmetric :=
          {| Antisymmetric.antisymmetry := NatWithZero.less_or_equal_antisymmetry |}
       ; PartialOrder.transitive :=
          {| Transitive.transitivity := NatWithZero.less_or_equal_transitivity |} |}
   ; TotalOrder.total :=
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
