(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires.
   [Structures.Semigroup], [Structures.Monoid], [Structures.Commutative] and
   [Structures.Cancellative] are the classes the instances at the bottom
   fill. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.Cancellative.

(* Zero is not a [Nat]; [One] is the smallest. [Data.NatWithZero] is the type
   that has it. *)
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
      pose proof (Equijunction_symmetry IH2) as IH2'.
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
      pose proof (Equijunction_symmetry IH2) as IH2'.
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
  pose proof (Equijunction_congruence
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
    unfold Unjunction in |- *.
    (* The context gains [e : add k One = One]: [|- Falsum] *)
    intro e.
    (* Commutativity turns the sum round: [e : add One k = One] *)
    rewrite (add_commutativity k One) in e.
    (* [add One k] computes: [e : Successor k = One] *)
    simpl in e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
  - (* [|- add k (Successor n') = Successor n' -> Falsum] *)
    unfold Unjunction in |- *.
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
    unfold Unjunction in IH.
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
      pose proof (Equijunction_symmetry IH2) as IH2'.
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
      pose proof (Equijunction_symmetry IH2) as IH2'.
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
End Nat.

(* The scope is declared in [Core.Notations] and never opened: a client
   writes [(m + n)%nat]. [only parsing] keeps the operations printed by
   name. *)
Notation "m + n" := (Nat.add m n) (only parsing) : jwa_nat_scope.
Notation "m * n" := (Nat.mul m n) (only parsing) : jwa_nat_scope.

(* A semigroup and no more: a monoid needs an identity, and [Nat] has no
   element that leaves its argument alone under [add]. *)
Instance Nat_add_semigroup : Semigroup.T Nat Nat.add :=
  {| Semigroup.associativity := Nat.add_associativity |}.

(* Both cancellation laws were already proved above, so the instance only
   hands them over. *)
Instance Nat_add_cancellative : Cancellative.T Nat Nat.add :=
  {| Cancellative.left_cancellation  := Nat.add_left_cancellation
   ; Cancellative.right_cancellation := Nat.add_right_cancellation |}.

(* [One] leaves its argument alone under [mul], so multiplication reaches
   monoid where addition stopped at semigroup. [mul One n] computes to [n],
   so the left law is reflexivity stated on the reduced term; the right law
   is commutativity at [One], whose right side computes the same way. *)
Instance Nat_mul_monoid : Monoid.T Nat Nat.mul One :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Nat.mul_associativity |}
   ; Monoid.left_identity  :=
       fun (n : Nat) => Equijunction_reflexivity (Nat.mul One n)
   ; Monoid.right_identity := fun (m : Nat) => Nat.mul_commutativity m One |}.

Instance Nat_add_commutative : Commutative.T Nat Nat.add :=
  {| Commutative.commutativity := Nat.add_commutativity |}.

Instance Nat_mul_commutative : Commutative.T Nat Nat.mul :=
  {| Commutative.commutativity := Nat.mul_commutativity |}.
