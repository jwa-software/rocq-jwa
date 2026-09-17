(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]; [Data.Nat] is the type [Positive] wraps;
   [Structures.Semigroup], [Structures.Monoid], [Structures.Commutative] and
   [Structures.Cancellative] are the classes the instances at the bottom
   fill. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Cancellative.
From jwa Require Import Data.Nat.

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

Theorem add_right_cancellation
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      add m n = add k n -> m = k.
Proof.
  (* The context gains [m], [k] and [n]: [|- add m n = add k n -> m = k] *)
  intros m k n.
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* Commutativity turns each sum round:
       [|- add Zero m = add Zero k -> m = k] *)
    rewrite (add_commutativity m Zero) in |- *.
    rewrite (add_commutativity k Zero) in |- *.
    (* Both compute: [|- m = k -> m = k] *)
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
           [|- Positive n' = Positive (Nat.add k' n') -> Zero = Positive k'] *)
        simpl in |- *.
        (* The context gains [e : Positive n' = Positive (Nat.add k' n')]:
           [|- Zero = Positive k'] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s:
           [e' : n' = Nat.add k' n'] *)
        pose proof (positive_injectivity n' (Nat.add k' n') e) as e'.
        (* Turned round: [e'' : Nat.add k' n' = n'] *)
        pose proof (Equijunction_symmetry e') as e''.
        (* [h : ~ (Nat.add k' n' = n')] *)
        pose proof (Nat.add_identity_absence k' n') as h.
        (* [h : Nat.add k' n' = n' -> Falsum] *)
        unfold Unjunction in h.
        (* [f : Falsum] *)
        pose proof (h e'') as f.
        (* [f : Falsum], which is what [contradiction] looks for. *)
        contradiction.
    + (* [k] is either [Zero] or [Positive k']: one goal per ctor. *)
      destruct k as [| k'].
      * (* Both [add]s compute:
           [|- Positive (Nat.add m' n') = Positive n' -> Positive m' = Zero] *)
        simpl in |- *.
        (* The context gains [e : Positive (Nat.add m' n') = Positive n']:
           [|- Positive m' = Zero] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s:
           [e' : Nat.add m' n' = n'] *)
        pose proof (positive_injectivity (Nat.add m' n') n' e) as e'.
        (* [h : ~ (Nat.add m' n' = n')] *)
        pose proof (Nat.add_identity_absence m' n') as h.
        (* [h : Nat.add m' n' = n' -> Falsum] *)
        unfold Unjunction in h.
        (* [f : Falsum] *)
        pose proof (h e') as f.
        (* [f : Falsum], which is what [contradiction] looks for. *)
        contradiction.
      * (* Both [add]s compute:
           [|- Positive (Nat.add m' n') = Positive (Nat.add k' n')
               -> Positive m' = Positive k'] *)
        simpl in |- *.
        (* The context gains
           [e : Positive (Nat.add m' n') = Positive (Nat.add k' n')]:
           [|- Positive m' = Positive k'] *)
        intro e.
        (* [positive_injectivity] strips the [Positive]s:
           [e' : Nat.add m' n' = Nat.add k' n'] *)
        pose proof (positive_injectivity (Nat.add m' n') (Nat.add k' n') e)
          as e'.
        (* [Nat.add_right_cancellation] strips the [n']s: [e'' : m' = k'] *)
        pose proof (Nat.add_right_cancellation m' k' n' e') as e''.
        (* [e''] replaces [m']: [|- Positive k' = Positive k'] *)
        rewrite e'' in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

Theorem add_left_cancellation
  : forall (n : NatWithZero) (m : NatWithZero) (k : NatWithZero),
      add n m = add n k -> m = k.
Proof.
  (* The context gains [n], [m], [k] and [e : add n m = add n k]:
     [|- m = k] *)
  intros n m k e.
  (* [add_commutativity] turns each side round: [e : add m n = add k n] *)
  rewrite (add_commutativity n m) in e.
  rewrite (add_commutativity n k) in e.
  (* [add_right_cancellation m k n e] is a proof of the goal as it stands. *)
  exact (add_right_cancellation m k n e).
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

End NatWithZero.

(* The scope is declared in [Core.Notations] and never opened: a client
   writes [(m + n)%nat_with_zero]. [only parsing] keeps the operations
   printed by name. *)
Notation "m + n" := (NatWithZero.add m n) (only parsing)
  : jwa_nat_with_zero_scope.
Notation "m * n" := (NatWithZero.mul m n) (only parsing)
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
