(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires. *)
From jwa Require Import Core.All.

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
     has [l'] and [IH : add (add l' m) n = add l' (add m n)] in its context.
     [using] names the eliminator instead of leaving [induction] to pick the
     generated [Nat_ind]. *)
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

End Nat.
