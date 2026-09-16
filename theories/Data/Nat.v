(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires.
   [Structures.Semigroup] is the class the instance at the bottom fills. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.

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

(* [add] recurses on its first argument, so [add One n] and
   [add (Successor m) n] reduce while their mirrors on the right do not.
   These two prove the mirrors, and commutativity needs both. *)

Lemma add_one_right : forall (m : Nat), add m One = Successor m.
Proof.
  (* The context gains [m]: [|- add m One = Successor m] *)
  intros m.
  (* [m] is either [One] or [Successor m']: one goal per ctor, and the second
     has [m'] and [IH : add m' One = Successor m'] in its context. *)
  induction m as [| m' IH] using Nat_induction.
  - (* [|- add One One = Successor One] *)
    (* The left side computes: [|- Successor One = Successor One] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (Successor m') One = Successor (Successor m')] *)
    (* One [add] step on the left:
       [|- Successor (add m' One) = Successor (Successor m')] *)
    simpl in |- *.
    (* [IH] replaces the left side:
       [|- Successor (Successor m') = Successor (Successor m')] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma add_successor_right
  : forall (m : Nat) (n : Nat), add m (Successor n) = Successor (add m n).
Proof.
  (* The context gains [m] and [n]:
     [|- add m (Successor n) = Successor (add m n)] *)
  intros m n.
  (* [m] is either [One] or [Successor m']: one goal per ctor, and the second
     has [m'] and [IH : add m' (Successor n) = Successor (add m' n)] in its
     context. *)
  induction m as [| m' IH] using Nat_induction.
  - (* [|- add One (Successor n) = Successor (add One n)] *)
    (* Both sides compute:
       [|- Successor (Successor n) = Successor (Successor n)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (Successor m') (Successor n)
           = Successor (add (Successor m') n)] *)
    (* One [add] step on each side:
       [|- Successor (add m' (Successor n))
           = Successor (Successor (add m' n))] *)
    simpl in |- *.
    (* [IH] replaces the left side:
       [|- Successor (Successor (add m' n))
           = Successor (Successor (add m' n))] *)
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
  - (* [|- add One n = add n One] *)
    (* The left side computes; the right cannot, since [add] recurses on its
       first argument: [|- Successor n = add n One] *)
    simpl in |- *.
    (* [add_one_right] is what turns the right side:
       [|- Successor n = Successor n] *)
    rewrite add_one_right in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- add (Successor m') n = add n (Successor m')] *)
    (* The left side computes:
       [|- Successor (add m' n) = add n (Successor m')] *)
    simpl in |- *.
    (* [IH] swaps the arguments under the [Successor]:
       [|- Successor (add n m') = add n (Successor m')] *)
    rewrite IH in |- *.
    (* [add_successor_right] pulls the [Successor] out of the right side:
       [|- Successor (add n m') = Successor (add n m')] *)
    rewrite add_successor_right in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

End Nat.

(* A semigroup and no more: a monoid needs an identity, and [Nat] has no
   element that leaves its argument alone under [add]. *)
Instance Nat_add_semigroup : Semigroup Nat Nat.add :=
  {| Semigroup_associativity := Nat.add_associativity |}.
