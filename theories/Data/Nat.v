(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->], [=], [~], [\/] and [exists]:
 * with [-noinit] a file has only what it requires.
 *)
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
From jwa Require Import Structures.Cancellative.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Semigroup.

(* Zero is not a [Nat]; [One] is the smallest.
 * [Data.NatWithZero] is the type that has it.
 *)
Inductive Nat : Type :=
  | One       : Nat
  | Successor : Nat -> Nat.

(* The eliminator behind [induction], written out. Its content is the [fix]:
   the proof for [Successor n] is built from the proof for [n], and following
   [n] down to [One] is what terminates. *)
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

(* The base case is [One] and not zero, so it already adds one: [add One n]
   is [Successor n]. Recursion is on [m], which is what makes [add] reduce
   whenever its first argument is a ctor. *)
Fixpoint add (m : Nat) (n : Nat) : Nat :=
  match m with
  | One          => Successor n
  | Successor m' => Successor (add m' n)
  end.

Theorem add_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), add (add l m) n = add l (add m n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- add (add l m) n = add l (add m n)] *)
  intros l m n.
  (* [l] is either [One] or [Successor l']: one goal per ctor, and the second
     has [l'] and [IH : add (add l' m) n = add l' (add m n)] in its context. *)
  induction l as [| l' IH] using Nat_induction.
  - (* [|- add (add One m) n = add One (add m n)] *)
    (* Both [add]s on the left compute:
       [|- Successor (add m n) = Successor (add m n)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (add (Successor l') m) n = add (Successor l') (add m n)] *)
    (* One [add] step on each side:
       [|- Successor (add (add l' m) n) = Successor (add l' (add m n))] *)
    simpl in |- *.
    (* [IH] replaces the left side:
       [|- Successor (add l' (add m n)) = Successor (add l' (add m n))] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem add_commutativity : forall (m : Nat) (n : Nat), add m n = add n m.
Proof.
  (* The context gains [m] and [n]: [|- add m n = add n m] *)
  intros m n.
  (* [m] is either [One] or [Successor m']: one goal per ctor, and the second
     has [m'] and [IH : add m' n = add n m'] in its context. *)
  induction m as [| m' IH] using Nat_induction.
  - (* The left side computes: [|- Successor n = add n One] *)
    simpl in |- *.
    (* [n] is either [One] or [Successor n']: one goal per ctor, and the
       second has [n'] and [IH2 : Successor n' = add n' One] in its
       context. *)
    induction n as [| n' IH2] using Nat_induction.
    + (* [add One One] computes: [|- Successor One = Successor One] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* One [add] step on the right:
         [|- Successor (Successor n') = Successor (add n' One)] *)
      simpl in |- *.
      (* Turned round: [IH2' : add n' One = Successor n'] *)
      pose proof (Identity.symmetry IH2) as IH2'.
      (* [IH2'] replaces [add n' One]:
         [|- Successor (Successor n') = Successor (Successor n')] *)
      rewrite IH2' in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* The left side computes:
       [|- Successor (add m' n) = add n (Successor m')] *)
    simpl in |- *.
    (* [IH] swaps the arguments under the [Successor]:
       [|- Successor (add n m') = add n (Successor m')] *)
    rewrite IH in |- *.
    (* [IH] mentions [n], so it would be folded into the motive of the next
       induction; the context loses it. *)
    clear IH.
    (* [n] is either [One] or [Successor n']: one goal per ctor, and the
       second has [n'] and
       [IH2 : Successor (add n' m') = add n' (Successor m')] in its
       context. *)
    induction n as [| n' IH2] using Nat_induction.
    + (* Both sides compute:
         [|- Successor (Successor m') = Successor (Successor m')] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* One [add] step on each side:
         [|- Successor (Successor (add n' m'))
             = Successor (add n' (Successor m'))] *)
      simpl in |- *.
      (* Turned round: [IH2' : add n' (Successor m') = Successor (add n' m')] *)
      pose proof (Identity.symmetry IH2) as IH2'.
      (* [IH2'] replaces [add n' (Successor m')]:
         [|- Successor (Successor (add n' m'))
             = Successor (Successor (add n' m'))] *)
      rewrite IH2' in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

(* [Successor] is injective: a function that unwraps it, applied to both
   sides of the equation, computes to the equation between the
   predecessors. The [One] branch never fires; it returns [m] only to have a
   value of the right type. *)
Theorem successor_injectivity
  : forall (m : Nat) (n : Nat), Successor m = Successor n -> m = n.
Proof.
  (* The context gains [m], [n] and [e : Successor m = Successor n]: [|- m = n] *)
  intros m n e.
  (* [e' : f (Successor m) = f (Successor n)]. *)
  pose proof (Identity.congruence
                (fun (x : Nat) => match x with | One => m | Successor y => y end)
                e) as e'.
  (* Both applications compute: [e' : m = n] *)
  simpl in e'.
  (* [e'] is a proof of the goal as it stands. *)
  exact e'.
Qed.

(* No [k] is an identity for [add], not even at a single [n]: without a
   zero, [add k n] is at least [Successor n]. Induction on [n]; each case
   turns the sum round by commutativity so that [simpl] can step it on
   [n]. *)
Theorem add_identity_absence : forall (k : Nat) (n : Nat), ~ (add k n = n).
Proof.
  (* The context gains [k] and [n]: [|- ~ (add k n = n)] *)
  intros k n.
  (* [n] is either [One] or [Successor n']: one goal per ctor, and the
     second has [n'] and [IH : ~ (add k n' = n')] in its context. *)
  induction n as [| n' IH] using Nat_induction.
  - (* [|- add k One = One -> Falsum] *)
    unfold Negation in |- *.
    (* The context gains [e : add k One = One]: [|- Falsum] *)
    intro e.
    (* Commutativity turns the sum round: [e : add One k = One] *)
    rewrite (add_commutativity k One) in e.
    (* [add One k] computes: [e : Successor k = One] *)
    simpl in e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
  - (* [|- add k (Successor n') = Successor n' -> Falsum] *)
    unfold Negation in |- *.
    (* The context gains [e : add k (Successor n') = Successor n']:
       [|- Falsum] *)
    intro e.
    (* Commutativity turns the sum round:
       [e : add (Successor n') k = Successor n'] *)
    rewrite (add_commutativity k (Successor n')) in e.
    (* One [add] step: [e : Successor (add n' k) = Successor n'] *)
    simpl in e.
    (* [successor_injectivity] strips the [Successor]s: [e' : add n' k = n'] *)
    pose proof (successor_injectivity (add n' k) n' e) as e'.
    (* Commutativity turns it back to [IH]'s shape: [e' : add k n' = n'] *)
    rewrite (add_commutativity n' k) in e'.
    (* [IH : add k n' = n' -> Falsum] *)
    unfold Negation in IH.
    (* [IH e'] is a proof of the goal as it stands. *)
    exact (IH e').
Qed.

Theorem add_left_cancellation
  : forall (n : Nat) (m : Nat) (k : Nat), add n m = add n k -> m = k.
Proof.
  intros n m k.
  induction n as [| n' IH] using Nat_induction.
  - simpl in |- *.
    intro e.
    exact (successor_injectivity m k e).
  - simpl in |- *.
    intro e.
    pose proof (successor_injectivity (add n' m) (add n' k) e) as e'.
    exact (IH e').
Qed.

Theorem add_right_cancellation
  : forall (m : Nat) (k : Nat) (n : Nat), add m n = add k n -> m = k.
Proof.
  intros m k n e.
  rewrite (add_commutativity m n) in e.
  rewrite (add_commutativity k n) in e.
  exact (add_left_cancellation n m k e).
Qed.

Lemma add_left_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), add l (add m n) = add m (add l n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- add l (add m n) = add m (add l n)] *)
  intros l m n.
  (* Commutativity turns the left side round:
     [|- add (add m n) l = add m (add l n)] *)
  rewrite (add_commutativity l (add m n)) in |- *.
  (* Associativity opens it: [|- add m (add n l) = add m (add l n)] *)
  rewrite (add_associativity m n l) in |- *.
  (* Commutativity swaps the inner pair:
     [|- add m (add l n) = add m (add l n)] *)
  rewrite (add_commutativity n l) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma add_right_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), add (add l m) n = add (add l n) m.
Proof.
  (* The context gains [l], [m] and [n]:
     [|- add (add l m) n = add (add l n) m] *)
  intros l m n.
  (* Associativity opens the left side:
     [|- add l (add m n) = add (add l n) m] *)
  rewrite (add_associativity l m n) in |- *.
  (* Associativity opens the right side:
     [|- add l (add m n) = add l (add n m)] *)
  rewrite (add_associativity l n m) in |- *.
  (* Commutativity swaps the inner pair on the left:
     [|- add l (add n m) = add l (add n m)] *)
  rewrite (add_commutativity m n) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Fixpoint mul (m : Nat) (n : Nat) : Nat :=
  match m with
  | One          => n
  | Successor m' => add n (mul m' n)
  end.

Theorem mul_commutativity : forall (m : Nat) (n : Nat), mul m n = mul n m.
Proof.
  (* The context gains [m] and [n]: [|- mul m n = mul n m] *)
  intros m n.
  (* [m] is either [One] or [Successor m']: one goal per ctor, and the second
     has [m'] and [IH : mul m' n = mul n m'] in its context. *)
  induction m as [| m' IH] using Nat_induction.
  - (* The left side computes: [|- n = mul n One] *)
    simpl in |- *.
    (* [n] is either [One] or [Successor n']: one goal per ctor, and the
       second has [n'] and [IH2 : n' = mul n' One] in its context. *)
    induction n as [| n' IH2] using Nat_induction.
    + (* [mul One One] computes: [|- One = One] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* One [mul] step, then [add One] computes:
         [|- Successor n' = Successor (mul n' One)] *)
      simpl in |- *.
      (* Turned round: [IH2' : mul n' One = n'] *)
      pose proof (Identity.symmetry IH2) as IH2'.
      (* [IH2'] replaces [mul n' One]: [|- Successor n' = Successor n'] *)
      rewrite IH2' in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* The left side computes:
       [|- add n (mul m' n) = mul n (Successor m')] *)
    simpl in |- *.
    (* [IH] swaps the arguments under the [add]:
       [|- add n (mul n m') = mul n (Successor m')] *)
    rewrite IH in |- *.
    (* [IH] mentions [n], so it would be folded into the motive of the next
       induction; the context loses it. *)
    clear IH.
    (* [n] is either [One] or [Successor n']: one goal per ctor, and the
       second has [n'] and
       [IH2 : add n' (mul n' m') = mul n' (Successor m')] in its context. *)
    induction n as [| n' IH2] using Nat_induction.
    + (* Both sides compute: [|- Successor m' = Successor m'] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* One [add] and one [mul] step on the left, one [mul] and one [add]
         step on the right:
         [|- Successor (add n' (add m' (mul n' m')))
             = Successor (add m' (mul n' (Successor m')))] *)
      simpl in |- *.
      (* Turned round: [IH2' : mul n' (Successor m') = add n' (mul n' m')] *)
      pose proof (Identity.symmetry IH2) as IH2'.
      (* [IH2'] replaces [mul n' (Successor m')]:
         [|- Successor (add n' (add m' (mul n' m')))
             = Successor (add m' (add n' (mul n' m')))] *)
      rewrite IH2' in |- *.
      (* [add_left_commutativity] brings [m'] to the front on the left:
         [|- Successor (add m' (add n' (mul n' m')))
             = Successor (add m' (add n' (mul n' m')))] *)
      rewrite (add_left_commutativity n' m' (mul n' m')) in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

Theorem mul_left_distributivity_over_add
  : forall (l : Nat) (m : Nat) (n : Nat),
      mul l (add m n) = add (mul l m) (mul l n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul l (add m n) = add (mul l m) (mul l n)] *)
  intros l m n.
  (* [l] is either [One] or [Successor l']: one goal per ctor, and the second
     has [l'] and [IH : mul l' (add m n) = add (mul l' m) (mul l' n)] in its
     context. *)
  induction l as [| l' IH] using Nat_induction.
  - (* All three [mul One]s compute: [|- add m n = add m n] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each [mul]:
       [|- add (add m n) (mul l' (add m n))
           = add (add m (mul l' m)) (add n (mul l' n))] *)
    simpl in |- *.
    (* [IH] replaces [mul l' (add m n)]:
       [|- add (add m n) (add (mul l' m) (mul l' n))
           = add (add m (mul l' m)) (add n (mul l' n))] *)
    rewrite IH in |- *.
    (* Associativity opens the left side:
       [|- add m (add n (add (mul l' m) (mul l' n)))
           = add (add m (mul l' m)) (add n (mul l' n))] *)
    rewrite (add_associativity m n (add (mul l' m) (mul l' n))) in |- *.
    (* [add_left_commutativity] moves [mul l' m] in front of [n]:
       [|- add m (add (mul l' m) (add n (mul l' n)))
           = add (add m (mul l' m)) (add n (mul l' n))] *)
    rewrite (add_left_commutativity n (mul l' m) (mul l' n)) in |- *.
    (* Associativity opens the right side into the same shape:
       [|- add m (add (mul l' m) (add n (mul l' n)))
           = add m (add (mul l' m) (add n (mul l' n)))] *)
    rewrite (add_associativity m (mul l' m) (add n (mul l' n))) in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem mul_right_distributivity_over_add
  : forall (l : Nat) (m : Nat) (n : Nat),
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
  : forall (a : Nat) (b : Nat) (c : Nat) (d : Nat),
      mul (add a b) (add c d)
      = add (add (mul a c) (mul a d)) (add (mul b c) (mul b d)).
Proof.
  intros a b c d.
  rewrite (mul_right_distributivity_over_add (add c d) a b) in |- *.
  rewrite (mul_left_distributivity_over_add a c d) in |- *.
  rewrite (mul_left_distributivity_over_add b c d) in |- *.
  reflexivity.
Qed.

Theorem mul_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), mul (mul l m) n = mul l (mul m n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul (mul l m) n = mul l (mul m n)] *)
  intros l m n.
  (* [l] is either [One] or [Successor l']: one goal per ctor, and the second
     has [l'] and [IH : mul (mul l' m) n = mul l' (mul m n)] in its context. *)
  induction l as [| l' IH] using Nat_induction.
  - (* Both [mul One]s compute: [|- mul m n = mul m n] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One [mul] step on each side:
       [|- mul (add m (mul l' m)) n = add (mul m n) (mul l' (mul m n))] *)
    simpl in |- *.
    (* The right distributivity law splits the left side:
       [|- add (mul m n) (mul (mul l' m) n)
           = add (mul m n) (mul l' (mul m n))] *)
    rewrite (mul_right_distributivity_over_add n m (mul l' m)) in |- *.
    (* [IH] replaces [mul (mul l' m) n]:
       [|- add (mul m n) (mul l' (mul m n))
           = add (mul m n) (mul l' (mul m n))] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma mul_left_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), mul l (mul m n) = mul m (mul l n).
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul l (mul m n) = mul m (mul l n)] *)
  intros l m n.
  (* [|- mul (mul m n) l = mul m (mul l n)] *)
  rewrite (mul_commutativity l (mul m n)) in |- *.
  (* [|- mul m (mul n l) = mul m (mul l n)] *)
  rewrite (mul_associativity m n l) in |- *.
  (* [|- mul m (mul l n) = mul m (mul l n)] *)
  rewrite (mul_commutativity n l) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma mul_right_commutativity
  : forall (l : Nat) (m : Nat) (n : Nat), mul (mul l m) n = mul (mul l n) m.
Proof.
  (* The context gains [l], [m] and [n]:
     [|- mul (mul l m) n = mul (mul l n) m] *)
  intros l m n.
  (* [|- mul l (mul m n) = mul (mul l n) m] *)
  rewrite (mul_associativity l m n) in |- *.
  (* [|- mul l (mul m n) = mul l (mul n m)] *)
  rewrite (mul_associativity l n m) in |- *.
  (* [|- mul l (mul n m) = mul l (mul n m)] *)
  rewrite (mul_commutativity m n) in |- *.
  (* Both sides are the same term. *)
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
  (* The context gains [m]: [|- power m One = m] *)
  intros m.
  (* [power m One] computes: [|- m = m] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma power_absorption : forall (n : Nat), power One n = One.
Proof.
  (* The context gains [n : Nat]: [|- power One n = One] *)
  intros n.
  (* [n] is either [One] or [Successor n']: one goal per ctor, and the second
     has [n'] and [IH : power One n' = One] in its context. *)
  induction n as [| n' IH] using Nat_induction.
  - (* [power One One] computes: [|- One = One] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One [power] step, then [mul One] computes: [|- power One n' = One] *)
    simpl in |- *.
    (* [IH] is the goal as it stands, so [rewrite] closes the left side:
       [|- One = One] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem product_of_powers
  : forall (m : Nat) (a : Nat) (b : Nat),
      mul (power m a) (power m b) = power m (add a b).
Proof.
  (* The context gains [m], [a] and [b]:
     [|- mul (power m a) (power m b) = power m (add a b)] *)
  intros m a b.
  (* [a] is either [One] or [Successor a']: one goal per ctor, and the second
     has [a'] and [IH : mul (power m a') (power m b) = power m (add a' b)]
     in its context. *)
  induction a as [| a' IH] using Nat_induction.
  - (* [power m One] is [m] and [add One b] is [Successor b], so both sides
       compute to [mul m (power m b)]:
       [|- mul m (power m b) = mul m (power m b)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One [power] step on the left, one [add] step and one [power] step on
       the right:
       [|- mul (mul m (power m a')) (power m b) = mul m (power m (add a' b))] *)
    simpl in |- *.
    (* Associativity opens the left side:
       [|- mul m (mul (power m a') (power m b)) = mul m (power m (add a' b))] *)
    rewrite (mul_associativity m (power m a') (power m b)) in |- *.
    (* [IH] replaces the inner product:
       [|- mul m (power m (add a' b)) = mul m (power m (add a' b))] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem power_of_a_power
  : forall (m : Nat) (a : Nat) (b : Nat),
      power (power m a) b = power m (mul a b).
Proof.
  (* The context gains [m], [a] and [b]:
     [|- power (power m a) b = power m (mul a b)] *)
  intros m a b.
  (* [b] is either [One] or [Successor b']: one goal per ctor, and the second
     has [b'] and [IH : power (power m a) b' = power m (mul a b')] in its
     context. *)
  induction b as [| b' IH] using Nat_induction.
  - (* [|- power (power m a) One = power m (mul One a)] *)
    rewrite (mul_commutativity a One) in |- *.
    (* [power _ One] and [mul One a] compute: [|- power m a = power m a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- power (power m a) (Successor b') = power m (mul (Successor b') a)] *)
    rewrite (mul_commutativity a (Successor b')) in |- *.
    (* One [power] step on the left, one [mul] step in the exponent:
       [|- mul (power m a) (power (power m a) b') = power m (add a (mul b' a))] *)
    simpl in |- *.
    (* Commutativity turns the inner product back:
       [|- mul (power m a) (power (power m a) b') = power m (add a (mul a b'))] *)
    rewrite (mul_commutativity b' a) in |- *.
    (* [product_of_powers] read right to left splits the right side:
       [|- mul (power m a) (power (power m a) b')
           = mul (power m a) (power m (mul a b'))] *)
    rewrite <- (product_of_powers m a (mul a b')) in |- *.
    (* [IH] replaces [power (power m a) b']:
       [|- mul (power m a) (power m (mul a b'))
           = mul (power m a) (power m (mul a b'))] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem power_distributivity_over_mul
  : forall (m : Nat) (n : Nat) (a : Nat),
      power (mul m n) a = mul (power m a) (power n a).
Proof.
  (* The context gains [m], [n] and [a]:
     [|- power (mul m n) a = mul (power m a) (power n a)] *)
  intros m n a.
  (* [a] is either [One] or [Successor a']: one goal per ctor, and the second
     has [a'] and [IH : power (mul m n) a' = mul (power m a') (power n a')]
     in its context. *)
  induction a as [| a' IH] using Nat_induction.
  - (* All three [power _ One]s compute: [|- mul m n = mul m n] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One [power] step on each:
       [|- mul (mul m n) (power (mul m n) a')
           = mul (mul m (power m a')) (mul n (power n a'))] *)
    simpl in |- *.
    (* [IH] replaces [power (mul m n) a']:
       [|- mul (mul m n) (mul (power m a') (power n a'))
           = mul (mul m (power m a')) (mul n (power n a'))] *)
    rewrite IH in |- *.
    (* The same three rearrangements as in
       [mul_left_distributivity_over_add], for [mul]:
       [|- mul m (mul n (mul (power m a') (power n a'))) = ...] *)
    rewrite (mul_associativity m n (mul (power m a') (power n a'))) in |- *.
    (* [|- mul m (mul (power m a') (mul n (power n a'))) = ...] *)
    rewrite (mul_left_commutativity n (power m a') (power n a')) in |- *.
    (* Associativity opens the right side into the same shape:
       [|- mul m (mul (power m a') (mul n (power n a')))
           = mul m (mul (power m a') (mul n (power n a')))] *)
    rewrite (mul_associativity m (power m a') (mul n (power n a'))) in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* [Nat -> Nat -> Prop] *)
Definition LessThan := fun (m : Nat) (n : Nat) => exists (k : Nat), add m k = n.

(* [Nat -> Nat -> Prop] *)
Definition LessOrEqual := fun (m : Nat) (n : Nat) => m = n \/ LessThan m n.

Theorem less_than_irreflexivity : forall (n : Nat), ~ (LessThan n n).
Proof.
  (* The context gains [n]: [|- ~ (LessThan n n)] *)
  intros n.
  (* [|- LessThan n n -> Falsum] *)
  unfold Negation in |- *.
  (* The context gains [h : LessThan n n]: [|- Falsum] *)
  intro h.
  (* [h : exists (k : Nat), add n k = n] *)
  unfold LessThan in h.
  (* [h] opens into a witness [k : Nat] and [e : add n k = n]. *)
  destruct h as [k e].
  (* Commutativity turns the sum round: [e : add k n = n] *)
  rewrite (add_commutativity n k) in e.
  (* [i : add k n = n -> Falsum], once unfolded *)
  pose proof (add_identity_absence k n) as i.
  unfold Negation in i.
  (* [f : Falsum] *)
  pose proof (i e) as f.
  (* [f : Falsum], which is what [contradiction] looks for. *)
  contradiction.
Qed.

Theorem less_than_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat),
      LessThan l m -> LessThan m n -> LessThan l n.
Proof.
  (* The context gains [l], [m], [n], [h1 : LessThan l m] and
     [h2 : LessThan m n]: [|- LessThan l n] *)
  intros l m n h1 h2.
  (* Each hypothesis opens into a witness and an equation:
     [e1 : add l k1 = m], [e2 : add m k2 = n]. *)
  unfold LessThan in h1.
  unfold LessThan in h2.
  destruct h1 as [k1 e1].
  destruct h2 as [k2 e2].
  (* [|- exists (k : Nat), add l k = n] *)
  unfold LessThan in |- *.
  (* The witness is the sum of the two: [|- add l (add k1 k2) = n] *)
  apply (Exists_introduction (add k1 k2)).
  (* Associativity read right to left groups the left side:
     [|- add (add l k1) k2 = n] *)
  pose proof (Identity.symmetry (add_associativity l k1 k2)) as a.
  rewrite a in |- *.
  (* [e1] replaces [add l k1]: [|- add m k2 = n] *)
  rewrite e1 in |- *.
  (* [e2] is a proof of the goal as it stands. *)
  exact e2.
Qed.

Theorem less_than_asymmetry
  : forall (m : Nat) (n : Nat), LessThan m n -> ~ (LessThan n m).
Proof.
  (* The context gains [m], [n] and [h1 : LessThan m n]:
     [|- ~ (LessThan n m)] *)
  intros m n h1.
  (* [h1] opens into [k1] and [e1 : add m k1 = n]. *)
  unfold LessThan in h1.
  destruct h1 as [k1 e1].
  (* [|- LessThan n m -> Falsum] *)
  unfold Negation in |- *.
  (* The context gains [h2 : LessThan n m]: [|- Falsum] *)
  intro h2.
  (* [h2] opens into [k2] and [e2 : add n k2 = m]. *)
  unfold LessThan in h2.
  destruct h2 as [k2 e2].
  (* [e1] turned round replaces [n] in [e2]: [e2 : add (add m k1) k2 = m] *)
  pose proof (Identity.symmetry e1) as e1'.
  rewrite e1' in e2.
  (* Associativity, then commutativity: [e2 : add (add k1 k2) m = m] *)
  rewrite (add_associativity m k1 k2) in e2.
  rewrite (add_commutativity m (add k1 k2)) in e2.
  (* [i : add (add k1 k2) m = m -> Falsum], once unfolded *)
  pose proof (add_identity_absence (add k1 k2) m) as i.
  unfold Negation in i.
  (* [f : Falsum] *)
  pose proof (i e2) as f.
  (* [f : Falsum], which is what [contradiction] looks for. *)
  contradiction.
Qed.

Theorem less_than_successor : forall (n : Nat), LessThan n (Successor n).
Proof.
  (* The context gains [n]: [|- LessThan n (Successor n)] *)
  intros n.
  (* [|- exists (k : Nat), add n k = Successor n] *)
  unfold LessThan in |- *.
  (* The witness is [One]: [|- add n One = Successor n] *)
  apply (Exists_introduction One).
  (* Commutativity turns the sum round, and [add One n] computes:
     [|- Successor n = Successor n] *)
  rewrite (add_commutativity n One) in |- *.
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem add_left_inflation : forall (m : Nat) (k : Nat), LessThan m (add m k).
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
  (* The context gains [m], [n] and [h : LessThan m n]:
     [|- LessThan (Successor m) (Successor n)] *)
  intros m n h.
  (* [h] opens into [k] and [e : add m k = n]. *)
  unfold LessThan in h.
  destruct h as [k e].
  (* The same witness serves: [|- add (Successor m) k = Successor n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction k).
  (* One [add] step: [|- Successor (add m k) = Successor n] *)
  simpl in |- *.
  (* [e] replaces [add m k]: [|- Successor n = Successor n] *)
  rewrite e in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma less_than_successor_cancellation
  : forall (m : Nat) (n : Nat),
      LessThan (Successor m) (Successor n) -> LessThan m n.
Proof.
  (* The context gains [m], [n] and [h]:
     [|- LessThan m n] *)
  intros m n h.
  (* [h] opens into [k] and [e : add (Successor m) k = Successor n]. *)
  unfold LessThan in h.
  destruct h as [k e].
  (* One [add] step: [e : Successor (add m k) = Successor n] *)
  simpl in e.
  (* [successor_injectivity] strips the [Successor]s: [e' : add m k = n] *)
  pose proof (successor_injectivity (add m k) n e) as e'.
  (* The same witness serves. *)
  unfold LessThan in |- *.
  exact (Exists_introduction k e').
Qed.

Theorem add_strict_monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessThan m n -> LessThan (add k m) (add k n).
Proof.
  (* The context gains [k], [m], [n] and [h : LessThan m n]:
     [|- LessThan (add k m) (add k n)] *)
  intros k m n h.
  (* [h] opens into [d] and [e : add m d = n]. *)
  unfold LessThan in h.
  destruct h as [d e].
  (* The same witness serves: [|- add (add k m) d = add k n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction d).
  (* Associativity opens the left side: [|- add k (add m d) = add k n] *)
  rewrite (add_associativity k m d) in |- *.
  (* [e] replaces [add m d]: [|- add k n = add k n] *)
  rewrite e in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem mul_strict_monotonicity
  : forall (k : Nat) (m : Nat) (n : Nat),
      LessThan m n -> LessThan (mul k m) (mul k n).
Proof.
  (* The context gains [k], [m], [n] and [h : LessThan m n]:
     [|- LessThan (mul k m) (mul k n)] *)
  intros k m n h.
  (* [h] opens into [d] and [e : add m d = n]. *)
  unfold LessThan in h.
  destruct h as [d e].
  (* The witness is [d] scaled by [k]:
     [|- add (mul k m) (mul k d) = mul k n] *)
  unfold LessThan in |- *.
  apply (Exists_introduction (mul k d)).
  (* The left distributivity law read right to left folds the left side:
     [|- mul k (add m d) = mul k n] *)
  pose proof (Identity.symmetry (mul_left_distributivity_over_add k m d)) as dist.
  rewrite dist in |- *.
  (* [e] replaces [add m d]: [|- mul k n = mul k n] *)
  rewrite e in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* Trichotomy, "cut in three": whichever two numbers [m] and [n] are taken,
   exactly one of `[m] is below [n]`, `[m] is [n]`, `[n] is below [m]` is the case.
   This theorem is the "at least one" half;
   "at most one" is [less_than_irreflexivity] and [less_than_asymmetry]. *)
Theorem less_than_trichotomy
  : forall (m : Nat) (n : Nat), (LessThan m n) \/ (m = n) \/ (LessThan n m).
Proof.
  (* The context gains [m]:
     [|- forall (n : Nat), LessThan m n \/ m = n \/ LessThan n m] *)
  intros m.
  (* [m] is either [One] or [Successor m']: one goal per ctor, and the
     second has [m'] and [IH : forall n, LessThan m' n \/ m' = n \/ LessThan n m']
     in its context. *)
  induction m as [| m' IH] using Nat_induction.
  - (* The context gains [n]. *)
    intros n.
    (* [n] is either [One] or [Successor n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* The middle case holds by reflexivity. *)
      exact (Disjunction.right (Disjunction.left (Identity.reflexivity One))).
    + (* [One] is below any [Successor], the witness being what follows:
         [|- add One n' = Successor n'] after choosing it *)
      apply Disjunction.left.
      unfold LessThan in |- *.
      apply (Exists_introduction n').
      (* [add One n'] computes: [|- Successor n' = Successor n'] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
  - (* The context gains [n]. *)
    intros n.
    (* [n] is either [One] or [Successor n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* The mirror of the case above: [|- add One m' = Successor m'] after
         choosing the witness *)
      apply Disjunction.right.
      apply Disjunction.right.
      unfold LessThan in |- *.
      apply (Exists_introduction m').
      (* [add One m'] computes: [|- Successor m' = Successor m'] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [IH] at [n'] gives the three cases one level down. *)
      pose proof (IH n') as t.
      destruct t as [lt | rest].
      * (* [lt : LessThan m' n'] lifts through the [Successor]s. *)
        apply Disjunction.left.
        exact (successor_strict_monotonicity m' n' lt).
      * destruct rest as [eq | gt].
        { (* [eq : m' = n'] replaces [m']:
             [|- Successor n' = Successor n'] *)
          apply Disjunction.right.
          apply Disjunction.left.
          rewrite eq in |- *.
          reflexivity. }
        { (* [gt : LessThan n' m'] lifts through the [Successor]s. *)
          apply Disjunction.right.
          apply Disjunction.right.
          exact (successor_strict_monotonicity n' m' gt). }
Qed.

(* Multiplication cancels: a strict step between the factors would be
 * carried to a strict step between the products, which the equation turns
 * into a step from a product to itself, refuted by irreflexivity; so
 * trichotomy leaves equality.
 *)
Theorem mul_left_cancellation
  : forall (k : Nat) (m : Nat) (n : Nat), mul k m = mul k n -> m = n.
Proof.
  (* The context gains [k], [m], [n] and [e]; one goal per side of
   * trichotomy.
   *)
  intros k m n e.
  pose proof (less_than_trichotomy m n) as t.
  destruct t as [lt | rest].
  - (* [lt] lifts to the products; [e] turns it into
     * [lt' : LessThan (mul k n) (mul k n)].
     *)
    pose proof (mul_strict_monotonicity k m n lt) as lt'.
    rewrite e in lt'.
    pose proof (less_than_irreflexivity (mul k n)) as i.
    unfold Negation in i.
    pose proof (i lt') as f.
    contradiction.
  - destruct rest as [eq | gt].
    + exact eq.
    + (* The mirror, with [gt' : LessThan (mul k n) (mul k n)] after [e]. *)
      pose proof (mul_strict_monotonicity k n m gt) as gt'.
      rewrite e in gt'.
      pose proof (less_than_irreflexivity (mul k n)) as i.
      unfold Negation in i.
      pose proof (i gt') as f.
      contradiction.
Qed.

Theorem mul_right_cancellation
  : forall (m : Nat) (n : Nat) (k : Nat), mul m k = mul n k -> m = n.
Proof.
  (* Commutativity on both sides brings it to the left law. *)
  intros m n k e.
  rewrite (mul_commutativity m k) in e.
  rewrite (mul_commutativity n k) in e.
  exact (mul_left_cancellation k m n e).
Qed.

(* [One] factors only as [One] times [One]: any other first factor makes
 * the product a sum, which is a [Successor] whichever ctor the second
 * factor is.
 *)
Theorem mul_identity_factorization
  : forall (k : Nat) (j : Nat), mul k j = One -> k = One /\ j = One.
Proof.
  (* The context gains [k], [j] and [e]; one goal per ctor of [k]. *)
  intros k j e.
  destruct k as [| k'].
  - (* [mul One j] computes to [j]: [e : j = One] replaces [j]. *)
    simpl in e.
    rewrite e in |- *.
    exact (Conjunction_introduction
             (Identity.reflexivity One) (Identity.reflexivity One)).
  - (* [mul (Successor k') j] computes to [add j (mul k' j)], a [Successor]
     * once [j] is a ctor: [e] equates it with [One].
     *)
    simpl in e.
    destruct j as [| j'].
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
Qed.

Theorem less_or_equal_reflexivity : forall (n : Nat), LessOrEqual n n.
Proof.
  (* The context gains [n]: [|- LessOrEqual n n] *)
  intros n.
  (* [|- n = n \/ LessThan n n], and the left side holds. *)
  unfold LessOrEqual in |- *.
  exact (Disjunction.left (Identity.reflexivity n)).
Qed.

Theorem less_or_equal_transitivity
  : forall (l : Nat) (m : Nat) (n : Nat),
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
    + (* [e2 : m = n] replaces [m] in [lt1 : LessThan l m]. *)
      rewrite e2 in lt1.
      exact (Disjunction.right lt1).
    + (* Two strict steps compose. *)
      exact (Disjunction.right (less_than_transitivity l m n lt1 lt2)).
Qed.

Theorem less_or_equal_antisymmetry
  : forall (m : Nat) (n : Nat), LessOrEqual m n -> LessOrEqual n m -> m = n.
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
  : forall (m : Nat) (n : Nat), (LessOrEqual m n) \/ (LessOrEqual n m).
Proof.
  (* The context gains [m] and [n]: [|- LessOrEqual m n \/ LessOrEqual n m] *)
  intros m n.
  (* Trichotomy gives the three cases; each lands on one side. *)
  pose proof (less_than_trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt | rest].
  - exact (Disjunction.left (Disjunction.right lt)).
  - destruct rest as [eq | gt].
    + exact (Disjunction.left (Disjunction.left eq)).
    + exact (Disjunction.right (Disjunction.right gt)).
Qed.

(* Three-way comparison, by walking both numbers down together: the one
   that reaches [One] first is the smaller. *)
Fixpoint compare (m : Nat) (n : Nat) : Comparison :=
  match m, n with
  | One, One                   => Eq
  | One, Successor _           => Lt
  | Successor _, One           => Gt
  | Successor m', Successor n' => compare m' n'
  end.

Lemma compare_reflexivity : forall (n : Nat), compare n n = Eq.
Proof.
  (* The context gains [n]: [|- compare n n = Eq] *)
  intros n.
  (* [n] is either [One] or [Successor n']: one goal per ctor, and the
     second has [n'] and [IH : compare n' n' = Eq] in its context. *)
  induction n as [| n' IH] using Nat_induction.
  - (* [compare One One] computes: [|- Eq = Eq] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One [compare] step: [|- compare n' n' = Eq] *)
    simpl in |- *.
    (* [IH] is a proof of the goal as it stands. *)
    exact IH.
Qed.

(* [compare] answers each of its three ways exactly when the order says so.
   Each specification is induction on [m] with [n] kept in the motive, one
   case per ctor pair; the base cases compute and the step case peels a
   [Successor] from both sides. *)

Lemma compare_lt_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Lt -> LessThan m n.
Proof.
  (* The context gains [m]. *)
  intros m.
  induction m as [| m' IH] using Nat_induction.
  - intros n.
    destruct n as [| n'].
    + (* [compare One One] computes: [|- Eq = Lt -> LessThan One One] *)
      simpl in |- *.
      intro e.
      (* [e] equates two distinct ctors, which closes any goal. *)
      discriminate.
    + (* [One] is below any [Successor], the witness being what follows. *)
      intro e.
      unfold LessThan in |- *.
      apply (Exists_introduction n').
      (* [add One n'] computes: [|- Successor n' = Successor n'] *)
      simpl in |- *.
      reflexivity.
  - intros n.
    destruct n as [| n'].
    + (* [|- Gt = Lt -> LessThan (Successor m') One] *)
      simpl in |- *.
      intro e.
      (* [e] equates two distinct ctors, which closes any goal. *)
      discriminate.
    + (* One [compare] step: [|- compare m' n' = Lt -> ...] *)
      simpl in |- *.
      intro e.
      (* [IH] one level down, lifted through the [Successor]s. *)
      exact (successor_strict_monotonicity m' n' (IH n' e)).
Qed.

Lemma compare_lt_specification_backward
  : forall (m : Nat) (n : Nat), LessThan m n -> compare m n = Lt.
Proof.
  (* The context gains [m]. *)
  intros m.
  induction m as [| m' IH] using Nat_induction.
  - intros n.
    destruct n as [| n'].
    + (* [LessThan One One] contradicts irreflexivity. *)
      intro h.
      pose proof (less_than_irreflexivity One) as i.
      unfold Negation in i.
      pose proof (i h) as f.
      (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [compare One (Successor n')] computes: [|- Lt = Lt] *)
      intro h.
      simpl in |- *.
      reflexivity.
  - intros n.
    destruct n as [| n'].
    + (* Nothing is below [One]: the witness equation
         [e : add (Successor m') k = One] computes to a [Successor] against
         [One]. *)
      intro h.
      unfold LessThan in h.
      destruct h as [k e].
      simpl in e.
      (* [e] equates two distinct ctors, which closes any goal. *)
      discriminate.
    + (* One [compare] step: [|- compare m' n' = Lt] *)
      intro h.
      simpl in |- *.
      (* [IH] one level down, on the hypothesis with its [Successor]s
         peeled. *)
      exact (IH n' (less_than_successor_cancellation m' n' h)).
Qed.

Theorem compare_lt_specification
  : forall (m : Nat) (n : Nat), compare m n = Lt <-> LessThan m n.
Proof.
  (* The context gains [m] and [n]:
     [|- compare m n = Lt <-> LessThan m n] *)
  intros m n.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (compare_lt_specification_forward  m n).
  - exact (compare_lt_specification_backward m n).
Qed.

Lemma compare_eq_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Eq -> m = n.
Proof.
  (* The context gains [m]. *)
  intros m.
  induction m as [| m' IH] using Nat_induction.
  - intros n.
    destruct n as [| n'].
    + (* [|- compare One One = Eq -> One = One] *)
      intro e.
      reflexivity.
    + (* [|- Lt = Eq -> One = Successor n'] *)
      simpl in |- *.
      intro e.
      (* [e] equates two distinct ctors, which closes any goal. *)
      discriminate.
  - intros n.
    destruct n as [| n'].
    + (* [|- Gt = Eq -> Successor m' = One] *)
      simpl in |- *.
      intro e.
      (* [e] equates two distinct ctors, which closes any goal. *)
      discriminate.
    + (* One [compare] step: [|- compare m' n' = Eq -> ...] *)
      simpl in |- *.
      intro e.
      (* [IH n' e : m' = n'] replaces [m']:
         [|- Successor n' = Successor n'] *)
      rewrite (IH n' e) in |- *.
      reflexivity.
Qed.

Lemma compare_eq_specification_backward
  : forall (m : Nat) (n : Nat), m = n -> compare m n = Eq.
Proof.
  (* The context gains [m], [n] and [e : m = n]: [|- compare m n = Eq] *)
  intros m n e.
  (* [e] replaces [m]: [|- compare n n = Eq] *)
  rewrite e in |- *.
  (* [compare_reflexivity n] is a proof of the goal as it stands. *)
  exact (compare_reflexivity n).
Qed.

Theorem compare_eq_specification
  : forall (m : Nat) (n : Nat), compare m n = Eq <-> m = n.
Proof.
  (* The context gains [m] and [n]: [|- compare m n = Eq <-> m = n] *)
  intros m n.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (compare_eq_specification_forward m n).
  - exact (compare_eq_specification_backward m n).
Qed.

Theorem compare_antisymmetry
  : forall (m : Nat) (n : Nat), compare m n = Comparison.transpose (compare n m).
Proof.
  (* The context gains [m]. *)
  intros m.
  induction m as [| m' IH] using Nat_induction.
  - intros n.
    destruct n as [| n'].
    + (* Both sides compute: [|- Eq = Eq] *)
      simpl in |- *.
      reflexivity.
    + (* Both sides compute: [|- Lt = Lt] *)
      simpl in |- *.
      reflexivity.
  - intros n.
    destruct n as [| n'].
    + (* Both sides compute: [|- Gt = Gt] *)
      simpl in |- *.
      reflexivity.
    + (* One [compare] step on each side:
         [|- compare m' n' = Comparison.transpose (compare n' m')] *)
      simpl in |- *.
      (* [IH n'] is a proof of the goal as it stands. *)
      exact (IH n').
Qed.

(* The third answer follows from the first by [compare_antisymmetry]. *)

Lemma compare_gt_specification_forward
  : forall (m : Nat) (n : Nat), compare m n = Gt -> LessThan n m.
Proof.
  (* The context gains [m], [n] and [e : compare m n = Gt]:
     [|- LessThan n m] *)
  intros m n e.
  (* [e : Comparison.transpose (compare n m) = Gt] *)
  rewrite (compare_antisymmetry m n) in e.
  (* [compare n m] is one of three answers; only [Lt] has [Gt] as
     its transpose. *)
  destruct (compare n m) as [| |] eqn:c.
  - (* [c : compare n m = Lt] is the case that holds. *)
    exact (compare_lt_specification_forward n m c).
  - (* [e : Eq = Gt] after computing. *)
    simpl in e.
    discriminate.
  - (* [e : Lt = Gt] after computing. *)
    simpl in e.
    discriminate.
Qed.

Lemma compare_gt_specification_backward
  : forall (m : Nat) (n : Nat), LessThan n m -> compare m n = Gt.
Proof.
  (* The context gains [m], [n] and [h : LessThan n m]:
     [|- compare m n = Gt] *)
  intros m n h.
  (* [|- Comparison.transpose (compare n m) = Gt] *)
  rewrite (compare_antisymmetry m n) in |- *.
  (* [compare n m] is [Lt] by the first specification:
     [|- Comparison.transpose Lt = Gt] *)
  rewrite (compare_lt_specification_backward n m h) in |- *.
  (* [Comparison.transpose Lt] computes: [|- Gt = Gt] *)
  simpl in |- *.
  reflexivity.
Qed.

Theorem compare_gt_specification
  : forall (m : Nat) (n : Nat), compare m n = Gt <-> LessThan n m.
Proof.
  (* The context gains [m] and [n]:
     [|- compare m n = Gt <-> LessThan n m] *)
  intros m n.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (compare_gt_specification_forward m n).
  - exact (compare_gt_specification_backward m n).
Qed.

(* [Nat -> Nat -> Bool] *)
Definition equal := fun (m : Nat) (n : Nat) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

Lemma equal_specification_forward
  : forall (m : Nat) (n : Nat), equal m n = true -> m = n.
Proof.
  (* The context gains [m], [n] and [e : equal m n = true]: [|- m = n] *)
  intros m n e.
  (* [e] is a [match] on [compare m n]; one goal per answer. *)
  unfold equal in e.
  destruct (compare m n) as [| |] eqn:c.
  - (* [e : false = true] *)
    discriminate.
  - (* [c : compare m n = Eq] is the case that holds. *)
    exact (compare_eq_specification_forward m n c).
  - (* [e : false = true] *)
    discriminate.
Qed.

Lemma equal_specification_backward
  : forall (m : Nat) (n : Nat), m = n -> equal m n = true.
Proof.
  (* The context gains [m], [n] and [e : m = n]: [|- equal m n = true] *)
  intros m n e.
  (* [|- match compare m n with ... end = true] *)
  unfold equal in |- *.
  (* [compare m n] is [Eq]: [|- true = true] *)
  rewrite (compare_eq_specification_backward m n e) in |- *.
  reflexivity.
Qed.

Theorem equal_specification
  : forall (m : Nat) (n : Nat), equal m n = true <-> m = n.
Proof.
  (* The context gains [m] and [n]: [|- equal m n = true <-> m = n] *)
  intros m n.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (equal_specification_forward m n).
  - exact (equal_specification_backward m n).
Qed.

(* The smaller and the larger of two, read off [compare]; every law below
   is case analysis on the answer and the order laws, and associativity is
   antisymmetry applied to the bounds. *)

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
               (compare m n = Lt) (LessThan m n)
               (compare_lt_specification m n) c).
    + (* [Eq]: the equality, by the specification. *)
      apply Disjunction.left.
      exact (Biimplication.elimination_forward
               (compare m n = Eq) (m = n) (compare_eq_specification m n) c).
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
                    (compare m n = Gt) (LessThan n m)
                    (compare_gt_specification m n) c) as gt.
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
  : forall (m : Nat) (n : Nat), max m n = m <-> LessOrEqual n m.
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
                  (compare m n = Eq) (m = n) (compare_eq_specification m n) c)).
    + apply Disjunction.right.
      exact (Biimplication.elimination_forward
               (compare m n = Gt) (LessThan n m)
               (compare_gt_specification m n) c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + pose proof (Biimplication.elimination_forward
                    (compare m n = Lt) (LessThan m n)
                    (compare_lt_specification m n) c) as lt.
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

Lemma min_left_projection : forall (l : Nat) (r : Nat), LessOrEqual (min l r) l.
Proof.
  (* One goal per answer of [compare l r]: the first two give [l] itself,
     the third gives [r], which is below [l] by the specification. *)
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.left (Identity.reflexivity l)).
  - exact (Disjunction.left (Identity.reflexivity l)).
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
             (compare l r = Gt) (LessThan r l)
             (compare_gt_specification l r) c).
Qed.

Lemma min_right_projection : forall (l : Nat) (r : Nat), LessOrEqual (min l r) r.
Proof.
  (* One goal per answer: [Lt] and [Eq] give [l], which is below or
     equal to [r] by the specifications; [Gt] gives [r] itself. *)
  intros l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
             (compare l r = Lt) (LessThan l r)
             (compare_lt_specification l r) c).
  - apply Disjunction.left.
    exact (Biimplication.elimination_forward
             (compare l r = Eq) (l = r) (compare_eq_specification l r) c).
  - exact (Disjunction.left (Identity.reflexivity r)).
Qed.

Lemma min_universality
  : forall (k : Nat) (m : Nat) (n : Nat),
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

Lemma max_left_injection : forall (l : Nat) (r : Nat), LessOrEqual l (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
             (compare l r = Lt) (LessThan l r)
             (compare_lt_specification l r) c).
  - exact (Disjunction.left (Identity.reflexivity l)).
  - exact (Disjunction.left (Identity.reflexivity l)).
Qed.

Lemma max_right_injection : forall (l : Nat) (r : Nat), LessOrEqual r (max l r).
Proof.
  intros l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.left (Identity.reflexivity r)).
  - apply Disjunction.left.
    exact (Identity.symmetry
             (Biimplication.elimination_forward
                (compare l r = Eq) (l = r) (compare_eq_specification l r) c)).
  - apply Disjunction.right.
    exact (Biimplication.elimination_forward
             (compare l r = Gt) (LessThan r l)
             (compare_gt_specification l r) c).
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

(* Two greatest lower bounds of the same pair are equal, by antisymmetry;
   the same for the least upper bounds. *)

Theorem min_commutativity : forall (m : Nat) (n : Nat), min m n = min n m.
Proof.
  (* Each side is below both [m] and [n], hence below the other. *)
  intros m n.
  apply (less_or_equal_antisymmetry (min m n) (min n m)).
  - exact (min_universality (min m n) n m
            (min_right_projection m n) (min_left_projection m n)).
  - exact (min_universality (min n m) m n
            (min_right_projection n m) (min_left_projection n m)).
Qed.

Theorem max_commutativity : forall (m : Nat) (n : Nat), max m n = max n m.
Proof.
  (* Each side is above both [m] and [n], hence above the other. *)
  intros m n.
  apply (less_or_equal_antisymmetry (max m n) (max n m)).
  - exact (max_universality (max n m) m n
            (max_right_injection n m) (max_left_injection n m)).
  - exact (max_universality (max m n) n m
            (max_right_injection m n) (max_left_injection m n)).
Qed.

Theorem min_associativity
  : forall (l : Nat) (m : Nat) (n : Nat), min (min l m) n = min l (min m n).
Proof.
  (* Both sides are below each of [l], [m] and [n], the inner bound
     reached through transitivity, so each is below the other. *)
  intros l m n.
  apply (less_or_equal_antisymmetry (min (min l m) n) (min l (min m n))).
  - apply (min_universality (min (min l m) n) l (min m n)).
    + exact (less_or_equal_transitivity (min (min l m) n) (min l m) l
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
  : forall (l : Nat) (m : Nat) (n : Nat), max (max l m) n = max l (max m n).
Proof.
  (* The mirror of [min_associativity]. *)
  intros l m n.
  apply (less_or_equal_antisymmetry (max (max l m) n) (max l (max m n))).
  - apply (max_universality (max l (max m n)) (max l m) n).
    + apply (max_universality (max l (max m n)) l m).
      * exact (max_left_injection l (max m n)).
      * exact (less_or_equal_transitivity m (max m n) (max l (max m n))
                (max_left_injection m n) (max_right_injection l (max m n))).
    + exact (less_or_equal_transitivity n (max m n) (max l (max m n))
              (max_right_injection m n) (max_right_injection l (max m n))).
  - apply (max_universality (max (max l m) n) l (max m n)).
    + exact (less_or_equal_transitivity l (max l m) (max (max l m) n)
              (max_left_injection l m) (max_left_injection (max l m) n)).
    + apply (max_universality (max (max l m) n) m n).
      * exact (less_or_equal_transitivity m (max l m) (max (max l m) n)
                (max_right_injection l m) (max_left_injection (max l m) n)).
      * exact (max_right_injection (max l m) n).
Qed.

Theorem min_idempotence : forall (n : Nat), min n n = n.
Proof.
  (* [compare n n] is [Eq], whose branch answers [n]. *)
  intros n.
  unfold min in |- *.
  rewrite (compare_reflexivity n) in |- *.
  reflexivity.
Qed.

Theorem max_idempotence : forall (n : Nat), max n n = n.
Proof.
  (* [compare n n] is [Eq], whose branch answers [n]. *)
  intros n.
  unfold max in |- *.
  rewrite (compare_reflexivity n) in |- *.
  reflexivity.
Qed.

(* Nothing is below [One], so [One] is the identity of [max]. *)

Lemma max_right_identity : forall (n : Nat), max n One = n.
Proof.
  (* The context gains [n]: [|- max n One = n] *)
  intros n.
  (* One goal per answer of [compare n One]; [Eq] and [Gt] answer [n], and
     [Lt] cannot happen. *)
  unfold max in |- *.
  destruct (compare n One) as [| |] eqn:c.
  - (* [c] would put [n] below [One]: [lt] opens into [k] and
       [e : add n k = One], which computes to a [Successor] against [One]
       whichever ctor [n] is. *)
    pose proof (compare_lt_specification_forward n One c) as lt.
    unfold LessThan in lt.
    destruct lt as [k e].
    destruct n as [| n'].
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
  - reflexivity.
  - reflexivity.
Qed.

Lemma max_left_identity : forall (n : Nat), max One n = n.
Proof.
  (* Commutativity brings it to the right law. *)
  intros n.
  rewrite (max_commutativity One n) in |- *.
  exact (max_right_identity n).
Qed.

(* Subtraction. The recursion walks both numbers down together; the
   difference may vanish or go below, which [Nat] cannot express, so the
   answer is an [Option]: [None] exactly when [n] is not below [m]. *)

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

(* Below or equal, there is nothing left in Nat -- its subtraction truncates. *)
Theorem subtract_truncation
  : forall (m : Nat) (n : Nat), LessOrEqual m n -> subtract m n = None.
Proof.
  (* The context gains [m], [n] and [h], an equality or a strict step. *)
  intros m n h.
  unfold LessOrEqual in h.
  destruct h as [e | lt].
  - (* [e : m = n] replaces [m]: [|- subtract n n = None] *)
    rewrite e in |- *.
    (* [e] mentions [n], so it would be folded into the motive of the
       induction; the context loses it. *)
    clear e.
    (* [n] is either [One] or [Successor n']: one goal per ctor, and the
       second has [n'] and [IH : subtract n' n' = None] in its context. *)
    induction n as [| n' IH] using Nat_induction.
    + (* [subtract One One] computes: [|- None = None] *)
      simpl in |- *.
      reflexivity.
    + (* One step: [|- subtract n' n' = None] *)
      simpl in |- *.
      exact IH.
  - (* [lt] opens into [k] and [e : add m k = n]; turned round it replaces
       [n]: [|- subtract m (add m k) = None] *)
    unfold LessThan in lt.
    destruct lt as [k e].
    pose proof (Identity.symmetry e) as e'.
    rewrite e' in |- *.
    (* [e] and [e'] mention [m], so they would be folded into the motive of
       the induction; the context loses them. *)
    clear e e'.
    (* [m] is either [One] or [Successor m']: one goal per ctor, and the
       second has [m'] and [IH : subtract m' (add m' k) = None] in its
       context. *)
    induction m as [| m' IH] using Nat_induction.
    + (* [add One k] is [Successor k] and the subtraction computes:
         [|- None = None] *)
      simpl in |- *.
      reflexivity.
    + (* One [add] step and one subtraction step:
         [|- subtract m' (add m' k) = None] *)
      simpl in |- *.
      exact IH.
Qed.

(* Taking away what was added gives the rest back: subtraction inverts addition. *)
Theorem subtract_inversion_of_add
  : forall (m : Nat) (n : Nat), subtract (add m n) n = Some m.
Proof.
  (* The context gains [m] and [n]. *)
  intros m n.
  (* [n] is either [One] or [Successor n']: one goal per ctor, and the
     second has [n'] and [IH : subtract (add m n') n' = Some m] in its
     context. Each case turns the sum round so that it computes. *)
  induction n as [| n' IH] using Nat_induction.
  - (* [|- subtract (add One m) One = Some m] *)
    rewrite (add_commutativity m One) in |- *.
    (* Both compute: [|- Some m = Some m] *)
    simpl in |- *.
    reflexivity.
  - (* [|- subtract (add (Successor n') m) (Successor n') = Some m] *)
    rewrite (add_commutativity m (Successor n')) in |- *.
    (* One step each: [|- subtract (add n' m) n' = Some m] *)
    simpl in |- *.
    (* Commutativity turns the sum back to [IH]'s shape. *)
    rewrite (add_commutativity n' m) in |- *.
    exact IH.
Qed.

(* Shifting both numbers by the same amount leaves the difference alone. *)
Theorem subtract_translation_invariance
  : forall (k : Nat) (m : Nat) (n : Nat), subtract (add k m) (add k n) = subtract m n.
Proof.
  intros k m n.
  (* [k] is either [One] or [Successor k']: one goal per ctor,
   * and the second has [k']
   * and [IH : subtract (add k' m) (add k' n) = subtract m n] in its context.
   *)
  induction k as [| k' IH] using Nat_induction.
  - (* [|- subtract m n = subtract m n] *)
    simpl in |- *.
    reflexivity.
  - (* [|- subtract (add k' m) (add k' n) = subtract m n] *)
    simpl in |- *.
    exact IH.
Qed.

(* [subtract] inverts [add] exactly where it answers: [Some k] says [k] is
   what [n] needs to be [m]. *)

Lemma subtract_specification_forward
  : forall (m : Nat) (n : Nat) (k : Nat), subtract m n = Some k -> add n k = m.
Proof.
  (* The context gains [m]. *)
  intros m.
  induction m as [| m' IH] using Nat_induction.
  - (* [subtract One n] computes to [None] whatever [n] is: [e] equates two
       distinct ctors, which closes any goal. *)
    intros n k e.
    simpl in e.
    discriminate.
  - intros n k.
    destruct n as [| n'].
    + (* [subtract (Successor m') One] and [add One k] compute:
         [|- Some m' = Some k -> Successor k = Successor m'] *)
      simpl in |- *.
      intro e.
      (* [Some] is injective: [e' : m' = k] *)
      pose proof (Option.some_injectivity Nat m' k e) as e'.
      (* [e'] replaces [m']: [|- Successor k = Successor k] *)
      rewrite e' in |- *.
      reflexivity.
    + (* One step each:
         [|- subtract m' n' = Some k -> Successor (add n' k) = Successor m'] *)
      simpl in |- *.
      intro e.
      (* [IH] one level down replaces the sum: [|- Successor m' = Successor m'] *)
      rewrite (IH n' k e) in |- *.
      reflexivity.
Qed.

Lemma subtract_specification_backward
  : forall (m : Nat) (n : Nat) (k : Nat), add n k = m -> subtract m n = Some k.
Proof.
  (* The context gains [m], [n], [k] and [e]; turned round, [e] replaces [m]:
     [|- subtract (add n k) n = Some k] *)
  intros m n k e.
  pose proof (Identity.symmetry e) as e'.
  rewrite e' in |- *.
  (* Commutativity puts the sum into the inversion's shape. *)
  rewrite (add_commutativity n k) in |- *.
  exact (subtract_inversion_of_add k n).
Qed.

Theorem subtract_specification
  : forall (m : Nat) (n : Nat) (k : Nat), subtract m n = Some k <-> add n k = m.
Proof.
  (* The context gains [m], [n] and [k]:
     [|- subtract m n = Some k <-> add n k = m] *)
  intros m n k.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
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

(* A semigroup and no more: a monoid needs an identity, and [Nat] has no
   element that leaves its argument alone under [add]. *)
Instance Nat_add_semigroup : Semigroup.T Nat Nat.add :=
  {| Semigroup.associativity := Nat.add_associativity |}.

(* Both cancellation laws were already proved above, so the instance only
   hands them over. *)
Instance Nat_add_cancellative : Cancellative.T Nat Nat.add :=
  {| Cancellative.left_cancellation  := Nat.add_left_cancellation
   ; Cancellative.right_cancellation := Nat.add_right_cancellation |}.

(* Both cancellation laws of [mul] were already proved above as well. *)
Instance Nat_mul_cancellative
  : Cancellative.T Nat Nat.mul :=
  {| Cancellative.left_cancellation  := Nat.mul_left_cancellation
   ; Cancellative.right_cancellation := Nat.mul_right_cancellation |}.

(* [One] leaves its argument alone under [mul], so multiplication reaches
   monoid where addition stopped at semigroup. [mul One n] computes to [n],
   so the left law is reflexivity stated on the reduced term; the right law
   is commutativity at [One], whose right side computes the same way. *)
Instance Nat_mul_monoid : Monoid.T Nat Nat.mul One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.mul_associativity |}
   ; Monoid.left_identity  :=
       fun (n : Nat) => Identity.reflexivity (Nat.mul One n)
   ; Monoid.right_identity := fun (m : Nat) => Nat.mul_commutativity m One |}.

Instance Nat_add_commutative : Commutative.T Nat Nat.add :=
  {| Commutative.commutativity := Nat.add_commutativity |}.

Instance Nat_mul_commutative : Commutative.T Nat Nat.mul :=
  {| Commutative.commutativity := Nat.mul_commutativity |}.

(* The two orders as instances of the [Relation] classes. The laws were
   already proved above, so each instance only hands them over; the nested
   records fill the [::] fields one class at a time. *)
Instance Nat_less_than_strict_order : StrictOrder Nat.LessThan :=
  {| StrictOrder.irreflexivity :=
       {| Irreflexive.irreflexivity := Nat.less_than_irreflexivity |}
   ; StrictOrder.transitivity :=
       {| Transitive.transitivity := Nat.less_than_transitivity |} |}.

Instance Nat_less_or_equal_total_order : TotalOrder Nat.LessOrEqual :=
  {| TotalOrder.partial_order :=
       {| PartialOrder.reflexivity :=
            {| Reflexive.reflexivity := Nat.less_or_equal_reflexivity |}
        ; PartialOrder.antisymmetry :=
            {| Antisymmetric.antisymmetry := Nat.less_or_equal_antisymmetry |}
        ; PartialOrder.transitivity :=
            {| Transitive.transitivity := Nat.less_or_equal_transitivity |} |}
   ; TotalOrder.totality :=
       {| Total.totality := Nat.less_or_equal_totality |} |}.

(* [min] is a commutative semigroup with no identity, since [Nat] has no
   greatest element; [max] reaches monoid, [One] being the least. *)
Instance Nat_min_semigroup : Semigroup.T Nat Nat.min :=
  {| Semigroup.associativity := Nat.min_associativity |}.

Instance Nat_max_monoid : Monoid.T Nat Nat.max One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.max_associativity |}
   ; Monoid.left_identity  := Nat.max_left_identity
   ; Monoid.right_identity := Nat.max_right_identity |}.

Instance Nat_min_commutative : Commutative.T Nat Nat.min :=
  {| Commutative.commutativity := Nat.min_commutativity |}.

Instance Nat_max_commutative : Commutative.T Nat Nat.max :=
  {| Commutative.commutativity := Nat.max_commutativity |}.
