(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]; [Data.Nat] is the type [Positive] wraps;
   [Structures.Semigroup], [Structures.Monoid] and [Structures.Cancellative]
   are the classes the instances at the bottom fill. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
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

(* [Zero] is the identity on both sides. With associativity above, these two
   are what make [(NatWithZero, add, Zero)] a monoid where [(Nat, add)] is
   only a semigroup. *)

Lemma add_zero_left : forall (n : NatWithZero), add Zero n = n.
Proof.
  (* The context gains [n]: [|- add Zero n = n] *)
  intros n.
  (* [add] matches its first argument, and [Zero] returns the second
     unchanged: [|- n = n] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma add_zero_right : forall (n : NatWithZero), add n Zero = n.
Proof.
  (* The context gains [n]: [|- add n Zero = n] *)
  intros n.
  (* Nothing reduces until [n] is a ctor, since [add] matches it first.
     [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* [|- add Zero Zero = Zero] *)
    (* Both matches reduce: [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (Positive n') Zero = Positive n'] *)
    (* The inner match on [Zero] returns the first argument:
       [|- Positive n' = Positive n'] *)
    simpl in |- *.
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
  - (* [|- add Zero n = add n Zero] *)
    (* [add_zero_left] turns the left side: [|- n = add n Zero] *)
    rewrite add_zero_left in |- *.
    (* [add_zero_right] turns the right side: [|- n = n] *)
    rewrite add_zero_right in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (Positive m') n = add n (Positive m')] *)
    (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
    destruct n as [| n'].
    + (* [|- add (Positive m') Zero = add Zero (Positive m')] *)
      (* [add_zero_left] turns the right side:
         [|- add (Positive m') Zero = Positive m'] *)
      rewrite add_zero_left in |- *.
      (* [add_zero_right] turns the left side:
         [|- Positive m' = Positive m'] *)
      rewrite add_zero_right in |- *.
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

(* [Positive] is injective: a function that unwraps it, applied to both
   sides of the equation, computes to the equation between the [Nat]s. The
   [Zero] branch never fires; it returns [m] only to have a value of the
   right type. *)
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

(* A sum with a positive right summand is never [Zero]: both cases of the
   left summand compute to a [Positive]. *)
Theorem add_positive_refutes_zero
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

(* The right summand cancels. [n] at [Zero] drops out by the identity law;
   at [Positive n'] the four ctor combinations of [m] and [k] are taken
   apart: both [Zero] is immediate, both [Positive] is [Nat]'s
   cancellation, and a [Zero] against a [Positive] contradicts
   [Nat.add_no_fixed_point]. *)
Theorem add_cancellation_right
  : forall (m : NatWithZero) (k : NatWithZero) (n : NatWithZero),
      add m n = add k n -> m = k.
Proof.
  (* The context gains [m], [k] and [n]: [|- add m n = add k n -> m = k] *)
  intros m k n.
  (* [n] is either [Zero] or [Positive n']: one goal per ctor. *)
  destruct n as [| n'].
  - (* [add_zero_right] rewrites each side: [|- m = k -> m = k] *)
    rewrite (add_zero_right m) in |- *.
    rewrite (add_zero_right k) in |- *.
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
        pose proof (Nat.add_no_fixed_point k' n') as h.
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
        pose proof (Nat.add_no_fixed_point m' n') as h.
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
        (* [Nat.add_cancellation_right] strips the [n']s: [e'' : m' = k'] *)
        pose proof (Nat.add_cancellation_right m' k' n' e') as e''.
        (* [e''] replaces [m']: [|- Positive k' = Positive k'] *)
        rewrite e'' in |- *.
        (* Both sides are the same term. *)
        reflexivity.
Qed.

(* The left summand cancels too, by commuting both sides into the right form. *)
Theorem add_cancellation_left
  : forall (n : NatWithZero) (m : NatWithZero) (k : NatWithZero),
      add n m = add n k -> m = k.
Proof.
  (* The context gains [n], [m], [k] and [e : add n m = add n k]:
     [|- m = k] *)
  intros n m k e.
  (* [add_commutativity] turns each side round: [e : add m n = add k n] *)
  rewrite (add_commutativity n m) in e.
  rewrite (add_commutativity n k) in e.
  (* [add_cancellation_right m k n e] is a proof of the goal as it stands. *)
  exact (add_cancellation_right m k n e).
Qed.

End NatWithZero.

(* [Zero] is exactly what [Nat] lacks, so this one reaches monoid. The
   [semigroup] field is filled inline rather than by a second instance:
   [Monoid.semigroup] is declared with [::], so resolution already finds a
   [Semigroup.T NatWithZero add] through it. *)
Instance NatWithZero_add_monoid : Monoid.T NatWithZero NatWithZero.add Zero :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := NatWithZero.add_associativity |}
   ; Monoid.identity_left  := NatWithZero.add_zero_left
   ; Monoid.identity_right := NatWithZero.add_zero_right |}.

(* Both cancellation laws were already proved above, so the instance only
   hands them over. *)
Instance NatWithZero_add_cancellative : Cancellative.T NatWithZero NatWithZero.add :=
  {| Cancellative.cancellation_left  := NatWithZero.add_cancellation_left
   ; Cancellative.cancellation_right := NatWithZero.add_cancellation_right |}.
