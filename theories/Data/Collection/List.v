(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Collection.Membership.
From jwa Require Import Data.Collection.Sized.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Tactics.Modus.

(* A list is empty, or one element in front of a list. [A] is a parameter:
 * every element has the one type.
 *)
Inductive List (A : Type) : Type :=
  | Nil  : List A
  | Cons : A -> List A -> List A.

(* [A] is inferred from the element or, for [Nil], from the expected type; a
 * use that has neither needs [@Nil A].
 *)
Arguments Nil  {A}.
Arguments Cons {A} a l.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * Both ctors are declared outside [Module List], so their notations are
 * too, and a client reaches them through [Require Export]. Every list
 * notation lives in [jwa_list_scope], which [Core.Notations] declares
 * without opening: a client writes [(a :: l)%list] or opens the scope.
 *)
(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil
  : jwa_list_scope.

(* [a :: l] puts one element in front; with [[]] it spells a list out:
 * [a :: b :: []].
 *)
Notation "a :: l" := (Cons a l)
  : jwa_list_scope.

(* The eliminator behind [induction], written out. Its content is the [fix]:
 * the proof for [Cons a l] is built from the proof for [l], and following
 * [l] down to [Nil] is what terminates.
 *)
Definition List_induction
  : forall (A : Type) (P : List A -> Prop) .
      P Nil ->
      (forall (a : A) (l : List A) . P l -> P (Cons a l)) ->
      forall (l : List A) . P l
  := fun (A : Type) (P : List A -> Prop)
       (base : P Nil)
       (step : forall (a : A) (l : List A) . P l -> P (Cons a l)) .
       fix go (l : List A) : P l :=
         match l with
         | Nil       => base
         | Cons a l' => step a l' (go l')
         end.

(* A module may carry the type's name; its members read [List.concat]. *)
Module List. (* List *)

(* The ctor notations [[]] and [::] are declared above this module; opening
 * their scope here lets every definition and law below use them.
 *)
Local Open Scope jwa_list_scope.

(* Lengths and counts are [NatWithZero]s, so its scope is opened here too:
 * [length l1 + length l2], [i < length l]. [Nat]'s scope stays closed and
 * its few uses keep the [Nat.] prefix, so [+] is never ambiguous. Inside
 * this module [*] is [NatWithZero.mul]; a product type still parses where
 * a type is expected, as in [List A * List A].
 *)
Local Open Scope jwa_nat_with_zero_scope.

(* [Bool]'s scope is opened for the [!] of [partition]. The [||] it also
 * carries is the infix [Bool.or] and does not disturb [(|| l ||)], whose
 * delimiters are tokens of their own.
 *)
Local Open Scope jwa_bool_scope.

(* Recursion is on the first list: [concat Nil l2] is [l2], and each [Cons]
 * of [l1] is put back in front of the result.
 *)
(* [forall {A : Type} . List A -> List A -> List A] *)
Fixpoint concat {A : Type} (l1 : List A) (l2 : List A) : List A :=
  match l1 with
  | []       => l2
  | a :: l1' => a :: concat l1' l2
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * After [End List] a client writes [(l1 ++ l2)%list] or opens
 * [jwa_list_scope].
 *)
Notation "l1 ++ l2" := (concat l1 l2)
  : jwa_list_scope.

(* The other end from [Cons]: [append l a] puts [a] after everything in
 * [l]. Concatenation with a one-element list rather than a recursion of
 * its own, so [appending.specification] holds by reflexivity and every
 * law of [concat] carries over by unfolding.
 *)
(* [forall {A : Type} . List A -> A -> List A] *)
Definition append := fun {A : Type} (l : List A) (a : A) . l ++ (a :: []).

(* [forall {A : Type} . List A -> NatWithZero] *)
Fixpoint length {A : Type} (l : List A) : NatWithZero :=
  match l with
  | []      => Zero
  | _ :: l' => ++ length l'
  end.

(* The bars of the norm, in parentheses: a bare [|| l ||] would take the
 * [||] of [Bool.or] away and [[| l |]] would break every [as [| ... ]],
 * both of them everywhere and not only where this scope is open. The
 * parentheses belong to the notation, so an argument needs none of its
 * own.
 *)
Notation "(|| l ||)" := (length l) (only parsing)
  : jwa_list_scope.

(* [map] applies [f] to every element and keeps the shape. *)
(* [forall {A : Type} {B : Type} . (A -> B) -> List A -> List B] *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | []      => []
  | a :: l' => f a :: map f l'
  end.

(* [reverse] moves each element to the end of the reversed rest. Quadratic,
 * and the simplest shape for the proofs below; an accumulator version can
 * come with a proof that it agrees.
 *)
(* [forall {A : Type} . List A -> List A] *)
Fixpoint reverse {A : Type} (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' => append (reverse l') a
  end.

(* [fold_right f z] replaces every [Cons] by [f] and the final [Nil] by [z],
 * working from the right: [Cons a (Cons b Nil)] becomes [f a (f b z)].
 *)
(* [forall {A : Type} {B : Type} . (A -> B -> B) -> B -> List A -> B] *)
Fixpoint fold_right {A : Type} {B : Type} (f : A -> B -> B) (z : B)
                    (l : List A) : B :=
  match l with
  | []      => z
  | a :: l' => f a (fold_right f z l')
  end.

(* Membership, defined by recursion into [Prop]: [Contains a Nil] computes
 * to [Falsum] and [Contains a (Cons b l)] to [a = b \/ Contains a l], so
 * [simpl] exposes the cases and every proof below is a case analysis.
 *)
(* [forall {A : Type} . A -> List A -> Prop] *)
Fixpoint Contains {A : Type} (a : A) (l : List A) : Prop :=
  match l with
  | []      => Falsum
  | b :: l' => a = b \/ Contains a l'
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * The two [belongs_to] spellings are the same proposition with the
 * arguments the other way round, so no law is stated for them.
 *)
Notation "l 'contains_member' a" := (Contains a l)
  : jwa_list_scope.

Notation "a 'belongs_to' l" := (Contains a l) (only parsing)
  : jwa_list_scope.

Notation "l 'does_not_contain_member' a" := (~ (Contains a l))
  : jwa_list_scope.
Notation "a 'does_not_belong_to' l" := (~ (Contains a l)) (only parsing)
  : jwa_list_scope.

(* [filter p] keeps the elements [p] answers [true] on, in their order. *)
(* [forall {A : Type} . (A -> Bool) -> List A -> List A] *)
Fixpoint filter {A : Type} (p : A -> Bool) (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' =>
      match p a with
      | true  => a :: filter p l'
      | false => filter p l'
      end
  end.

(* [All P] holds when every element satisfies [P], [Any P] when some
 * element does. Both recurse into [Prop] as [Contains] does: [Nil] gives
 * the neutral proposition, [Cons] a conjunction or a disjunction.
 *)

(* [forall {A : Type} . (A -> Prop) -> List A -> Prop] *)
Fixpoint All {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | []      => Verum
  | a :: l' => P a /\ All P l'
  end.

(* [forall {A : Type} . (A -> Prop) -> List A -> Prop] *)
Fixpoint Any {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | []      => Falsum
  | a :: l' => P a \/ Any P l'
  end.

(* [forall {A : Type} . List A -> Option A] *)
Definition head := fun {A : Type} (l : List A) .
  match l with
  | []     => None
  | a :: _ => Some a
  end.

(* [forall {A : Type} . List A -> Option (List A)] *)
Definition tail := fun {A : Type} (l : List A) .
  match l with
  | []      => None
  | _ :: l' => Some l'
  end.

(* [forall {A : Type} . List A -> Option A] *)
Definition last := fun {A : Type} (l : List A) . head (reverse l).

(* [forall {A : Type} . List A -> Option (List A)] *)
Definition initial := fun {A : Type} (l : List A) . Option.map reverse (tail (reverse l)).

(* [head] and [tail] in one answer: [None] on the empty list, else the
 * first element paired with the rest.
 *)
(* [forall {A : Type} . List A -> Option (A * List A)] *)
Definition pop := fun {A : Type} (l : List A) .
  match l return Option (A * List A) with
  | []      => None
  | a :: l' => Some (Product_introduction a l')
  end.

(* [forall {A : Type} {B : Type} . List A -> List B -> List (A * B)] *)
Fixpoint zip {A : Type} {B : Type} (l1 : List A) (l2 : List B)
  : List (A * B) :=
  match l1, l2 with
  | a :: l1', b :: l2' => Product_introduction a b :: zip l1' l2'
  | [], []             => []
  | [], _ :: _         => []
  | _ :: _, []         => []
  end.

(* The two projections mapped over the list, so the laws of [map] carry
 * over.
 *)
(* [forall {A : Type} {B : Type} . List (A * B) -> List A * List B] *)
Definition unzip := fun {A : Type} {B : Type} (l : List (A * B)) .
  Product_introduction (map Product.first l) (map Product.second l).

(* Splits a list into the elements [p] accepts and the ones it rejects, in
 * one pass; the recursive result is opened by a [match] so both halves
 * are extended in place.
 *)
(* [forall {A : Type} . (A -> Bool) -> List A -> List A * List A] *)
Fixpoint partition {A : Type} (p : A -> Bool) (l : List A)
  : List A * List A :=
  match l with
  | []      => Product_introduction [] []
  | a :: l' =>
      match partition p l' with
      | Product_introduction yes no =>
          match p a with
          | true  => Product_introduction (a :: yes) no
          | false => Product_introduction yes (a :: no)
          end
      end
  end.

(* Indexing from [Zero]: [nth l i] is the element [i] places from the front,
 * [None] past the end. Recursion is on the list; the index is peeled by
 * one alongside, [Positive One] being the last step before [Zero].
 *)
(* [forall {A : Type} . List A -> NatWithZero -> Option A] *)
Fixpoint nth {A : Type} (l : List A) (i : NatWithZero) : Option A :=
  match l with
  | []      => None
  | a :: l' =>
      match i with
      | Zero                    => Some a
      | Positive One            => nth l' Zero
      | Positive (Successor i') => nth l' (Positive i')
      end
  end.

(* [take n l] is the first [n] elements, all of [l] when there are fewer;
 * [drop n l] is what is left. Both recurse on the list, peeling the count
 * alongside as [nth] does.
 *)
(* [forall {A : Type} . NatWithZero -> List A -> List A] *)
Fixpoint take {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' =>
      match n with
      | Zero                    => []
      | Positive One            => a :: []
      | Positive (Successor n') => a :: take (Positive n') l'
      end
  end.

(* [forall {A : Type} . NatWithZero -> List A -> List A] *)
Fixpoint drop {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' =>
      match n with
      | Zero                    => a :: l'
      | Positive One            => l'
      | Positive (Successor n') => drop (Positive n') l'
      end
  end.

(* [forall {A : Type} . NatWithZero -> List A -> List A * List A] *)
Definition split_at := fun {A : Type} (n : NatWithZero) (l : List A) .
  Product_introduction (take n l) (drop n l).

(* [replicate n a] is [a] repeated [n] times. A count of [Zero] gives [Nil];
 * a positive count recurses on its [Nat], one element per step, since a
 * [NatWithZero] has no step of its own to recurse on.
 *)
(* [forall {A : Type} . Nat -> A -> List A] *)
Fixpoint replicate_positive {A : Type} (k : Nat) (a : A) : List A :=
  match k with
  | One          => a :: []
  | Successor k' => a :: replicate_positive k' a
  end.

(* [forall {A : Type} . NatWithZero -> A -> List A] *)
Definition replicate := fun {A : Type} (n : NatWithZero) (a : A) .
  match n with
  | Zero       => []
  | Positive k => replicate_positive k a
  end.

(* [List NatWithZero -> NatWithZero] *)
Definition sum := fun (l : List NatWithZero) . fold_right NatWithZero.add Zero l.

(* [List NatWithZero -> NatWithZero] *)
Definition product := fun (l : List NatWithZero) .
  fold_right NatWithZero.mul (Positive One) l.

(* [count p l] is how many elements [p] answers [true] on. *)
(* [forall {A : Type} . (A -> Bool) -> List A -> NatWithZero] *)
Fixpoint count {A : Type} (p : A -> Bool) (l : List A) : NatWithZero :=
  match l with
  | []      => Zero
  | a :: l' =>
      match p a with
      | true  => ++ count p l'
      | false => count p l'
      end
  end.

(* Insertion sort, relative to a comparison [le] that answers [true] when
 * its first argument may come first. [insert] walks past every element
 * that may precede [a] and puts [a] in front of the first that may not.
 *)
(* [forall {A : Type} . (A -> A -> Bool) -> A -> List A -> List A] *)
Fixpoint insert {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) : List A :=
  match l with
  | []      => a :: []
  | b :: l' =>
      match le a b with
      | true  => a :: b :: l'
      | false => b :: insert le a l'
      end
  end.

(* [forall {A : Type} . (A -> A -> Bool) -> List A -> List A] *)
Fixpoint insertion_sort {A : Type} (le : A -> A -> Bool) (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' => insert le a (insertion_sort le l')
  end.

(* Sortedness: every element may precede all that follow it. Stated with
 * [All] rather than on neighbours, so that [insert] is checked one element
 * at a time.
 *)
(* [forall {A : Type} . (A -> A -> Bool) -> List A -> Prop] *)
Fixpoint Sorted {A : Type} (le : A -> A -> Bool) (l : List A) : Prop :=
  match l with
  | []      => Verum
  | a :: l' => All (fun (b : A) . le a b = true) l' /\ Sorted le l'
  end.

(* [Nat -> List NatWithZero] *)
Fixpoint range_positive (p : Nat) : List NatWithZero :=
  match p with
  | One          => Zero :: []
  | Successor p' => append (range_positive p') (Positive p')
  end.

(* [NatWithZero -> List NatWithZero] *)
Definition range := fun (n : NatWithZero) .
  match n with
  | Zero       => []
  | Positive p => range_positive p
  end.

(* [List NatWithZero -> NatWithZero] *)
Definition maximum_of := fun (l : List NatWithZero) . fold_right NatWithZero.max Zero l.

(* [List NatWithZero -> Option NatWithZero] *)
Fixpoint minimum_of (l : List NatWithZero) : Option NatWithZero :=
  match l with
  | []      => None
  | a :: l' =>
      match minimum_of l' with
      | None   => Some a
      | Some m => Some (NatWithZero.min a m)
      end
  end.

(* A law of the type itself rather than of any operation, so it belongs to
 * no topic below.
 *)
Theorem distinctness
  : forall {A : Type} (a : A) (l : List A) . ~ (a :: l = []).
Proof.
  intros A a l.
  unfold Negation in |- *.
  intro e.
  discriminate e.
Qed.

Module concatenation. (* concatenation *)

(* concatenation.associativity *)
Theorem associativity
  : forall {A : Type} (l1 : List A) (l2 : List A) (l3 : List A) .
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module left. (* concatenation.left *)

(* concatenation.left.identity *)
Lemma identity : forall {A : Type} (l : List A) . [] ++ l = l.
Proof.
  intros A l.
  simpl in |- *.
  reflexivity.
Qed.

End left. (* concatenation.left *)

Module right. (* concatenation.right *)

(* concatenation.right.identity *)
Lemma identity : forall {A : Type} (l : List A) . l ++ [] = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End right. (* concatenation.right *)

(* concatenation.identity *)
Theorem identity
  : forall {A : Type} (l : List A) . ([] ++ l = l) /\ (l ++ [] = l).
Proof.
  intros A l.
  split.
  - exact (concatenation.left.identity  l).
  - exact (concatenation.right.identity l).
Qed.

(* concatenation.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (l1 : List A) (l2 : List A) .
      l1 ++ l2 = fold_right Cons l2 l1.
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End concatenation. (* concatenation *)

Module length. (* length *)

(* length.additivity.over.concatenation *)
Module additivity. (* length.additivity *)

Module over. (* length.additivity.over *)

(* length.additivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (l1 : List A) (l2 : List A) .
      (|| l1 ++ l2 ||) = (|| l1 ||) + (|| l2 ||).
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.increment.specification ((|| l1' ||) + (|| l2 ||)))
      in |- *.
    rewrite (NatWithZero.increment.specification (|| l1' ||))
      in |- *.
    rewrite (NatWithZero.addition.associativity (Positive One) (|| l1' ||) (|| l2 ||))
      in |- *.
    reflexivity.
Qed.

End over. (* length.additivity.over *)

End additivity. (* length.additivity *)

(* length.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (l : List A) .
      (|| l ||)
      = fold_right (fun (_ : A) (n : NatWithZero) . (++ n))
                   Zero
                   l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End length. (* length *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall {A : Type} (l : List A) . map (fun a . a) l = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* mapping.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C)
      (l : List A) .
    map g (map f l) = map (fun a . g (f a)) l.
Proof.
  intros A B C f g l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module distributivity. (* mapping.distributivity *)

Module over. (* mapping.distributivity.over *)

(* mapping.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} {B : Type} (f : A -> B) (l1 : List A) (l2 : List A) .
      map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros A B f l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End over. (* mapping.distributivity.over *)

End distributivity. (* mapping.distributivity *)

(* mapping.catamorphism *)
Theorem catamorphism
  : forall {A : Type} {B : Type} (f : A -> B) (l : List A) .
      map f l
      = fold_right (fun (a : A) (mapped : List B) . f a :: mapped)
                   []
                   l.
Proof.
  intros A B f l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module preservation. (* mapping.preservation *)

Module of. (* mapping.preservation.of *)

(* [map] carries membership along: an element of [l] has its image in
 * [map f l].
 *)
(* mapping.preservation.of.membership *)
Theorem membership
  : forall {A : Type} {B : Type} (f : A -> B) (a : A) (l : List A) .
      l contains_member a -> map f l contains_member f a.
Proof.
  intros A B f a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro g.
    exact g.
  - simpl in |- *.
    intro h.
    destruct h as [e | h'].
    + apply Disjunction.L.
      rewrite e in |- *.
      reflexivity.
    + apply Disjunction.R.
      apply IH.
      exact h'.
Qed.

End of. (* mapping.preservation.of *)

End preservation. (* mapping.preservation *)

End mapping. (* mapping *)

Module folding. (* folding *)

Module composition. (* folding.composition *)

Module over. (* folding.composition.over *)

(* folding.composition.over.concatenation *)
Theorem concatenation
  : forall {A : Type} {B : Type} (f : A -> B -> B) (z : B) (l1 : List A) (l2 : List A) .
      fold_right f z (l1 ++ l2) = fold_right f (fold_right f z l2) l1.
Proof.
  intros A B f z l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End over. (* folding.composition.over *)

End composition. (* folding.composition *)

End folding. (* folding *)

Module membership. (* membership *)

(* Nothing belongs to the empty list, so its membership is vacuously false. *)
(* membership.vacuity *)
Theorem vacuity
  : forall {A : Type} (a : A) . [] does_not_contain_member a.
Proof.
  intros A a.
  unfold Negation in |- *.
  simpl in |- *.
  intro f.
  exact f.
Qed.

Module forward. (* membership.forward *)

Module distributivity. (* membership.forward.distributivity *)

Module over. (* membership.forward.distributivity.over *)

(* membership.forward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {a : A} {l1 : List A} {l2 : List A} .
      l1 ++ l2 contains_member a -> l1 contains_member a \/ l2 contains_member a.
Proof.
  intros A a l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact (Disjunction.R h).
  - simpl in |- *.
    intro h.
    destruct h as [e | h'].
    + exact (Disjunction.L (Disjunction.L e)).
    + destruct (IH h') as [h1 | h2].
      * exact (Disjunction.L (Disjunction.R h1)).
      * exact (Disjunction.R h2).
Qed.

End over. (* membership.forward.distributivity.over *)

End distributivity. (* membership.forward.distributivity *)

End forward. (* membership.forward *)

Module backward. (* membership.backward *)

Module distributivity. (* membership.backward.distributivity *)

Module over. (* membership.backward.distributivity.over *)

(* membership.backward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {a : A} {l1 : List A} {l2 : List A} .
      l1 contains_member a \/ l2 contains_member a -> l1 ++ l2 contains_member a.
Proof.
  intros A a l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    destruct h as [f | h2].
    + contradiction f.
    + exact h2.
  - simpl in |- *.
    intro h.
    destruct h as [h1 | h2].
    + destruct h1 as [e | h1'].
      * exact (Disjunction.L e).
      * apply Disjunction.R.
        apply IH.
        exact (Disjunction.L h1').
    + apply Disjunction.R.
      apply IH.
      exact (Disjunction.R h2).
Qed.

End over. (* membership.backward.distributivity.over *)

End distributivity. (* membership.backward.distributivity *)

End backward. (* membership.backward *)

Module distributivity. (* membership.distributivity *)

Module over. (* membership.distributivity.over *)

(* membership.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (a : A) (l1 : List A) (l2 : List A) .
      l1 ++ l2 contains_member a <-> l1 contains_member a \/ l2 contains_member a.
Proof.
  intros A a l1 l2.
  split.
  - exact (@membership.forward.distributivity.over.concatenation  A a l1 l2).
  - exact (@membership.backward.distributivity.over.concatenation A a l1 l2).
Qed.

End over. (* membership.distributivity.over *)

End distributivity. (* membership.distributivity *)

(* membership.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (a : A) (l : List A) .
      (l contains_member a)
      = fold_right (fun (b : A) (rest : Prop) . a = b \/ rest) Falsum l.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End membership. (* membership *)

Module reversal. (* reversal *)

Module antidistributivity. (* reversal.antidistributivity *)

Module over. (* reversal.antidistributivity.over *)

(* reversal.antidistributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (l1 : List A) (l2 : List A) .
      reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    rewrite concatenation.right.identity in |- *.
    reflexivity.
  - simpl in |- *.
    unfold append in |- *.
    rewrite IH in |- *.
    rewrite concatenation.associativity in |- *.
    reflexivity.
Qed.

End over. (* reversal.antidistributivity.over *)

End antidistributivity. (* reversal.antidistributivity *)

(* reversal.involution *)
Theorem involution
  : forall {A : Type} (l : List A) . reverse (reverse l) = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    unfold append in |- *.
    rewrite reversal.antidistributivity.over.concatenation in |- *.
    simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module forward. (* reversal.forward *)

Module preservation. (* reversal.forward.preservation *)

Module of. (* reversal.forward.preservation.of *)

(* reversal.forward.preservation.of.membership *)
Lemma membership
  : forall {A : Type} {a : A} {l : List A} .
      reverse l contains_member a -> l contains_member a.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    exact f.
  - simpl in |- *.
    intro h.
    destruct (membership.forward.distributivity.over.concatenation h) as [h1 | h2].
    + apply Disjunction.R.
      apply IH.
      exact h1.
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.L e).
      * contradiction f.
Qed.

End of. (* reversal.forward.preservation.of *)

End preservation. (* reversal.forward.preservation *)

End forward. (* reversal.forward *)

Module backward. (* reversal.backward *)

Module preservation. (* reversal.backward.preservation *)

Module of. (* reversal.backward.preservation.of *)

(* reversal.backward.preservation.of.membership *)
Lemma membership
  : forall {A : Type} {a : A} {l : List A} .
      l contains_member a -> reverse l contains_member a.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    exact f.
  - simpl in |- *.
    intro h.
    apply membership.backward.distributivity.over.concatenation.
    destruct h as [e | h'].
    + apply Disjunction.R.
      simpl in |- *.
      exact (Disjunction.L e).
    + apply Disjunction.L.
      apply IH.
      exact h'.
Qed.

End of. (* reversal.backward.preservation.of *)

End preservation. (* reversal.backward.preservation *)

End backward. (* reversal.backward *)

Module preservation. (* reversal.preservation *)

Module of. (* reversal.preservation.of *)

(* reversal.preservation.of.membership *)
Theorem membership
  : forall {A : Type} (a : A) (l : List A) .
      reverse l contains_member a <-> l contains_member a.
Proof.
  intros A a l.
  split.
  - exact (@reversal.forward.preservation.of.membership  A a l).
  - exact (@reversal.backward.preservation.of.membership A a l).
Qed.

End of. (* reversal.preservation.of *)

End preservation. (* reversal.preservation *)

End reversal. (* reversal *)

Module appending. (* appending *)

(* appending.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (a : A) . append l a = l ++ (a :: []).
Proof.
  intros A l a.
  unfold append in |- *.
  reflexivity.
Qed.

(* appending.length *)
Theorem length
  : forall {A : Type} (l : List A) (a : A) . (|| append l a ||) = ++ (|| l ||).
Proof.
  intros A l a.
  rewrite (appending.specification l a) in |- *.
  rewrite (length.additivity.over.concatenation l (a :: [])) in |- *.
  simpl in |- *.
  rewrite (NatWithZero.increment.specification (|| l ||)) in |- *.
  rewrite (NatWithZero.addition.commutativity (Positive One) (|| l ||)) in |- *.
  reflexivity.
Qed.

(* appending.membership *)
Theorem membership
  : forall {A : Type} (l : List A) (a : A) (b : A) .
      append l a contains_member b <-> b = a \/ l contains_member b.
Proof.
  intros A l a b.
  rewrite (appending.specification l a) in |- *.
  split.
  - intro h.
    destruct (membership.forward.distributivity.over.concatenation h) as [h1 | h2].
    + exact (Disjunction.R h1).
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.L e).
      * contradiction f.
  - intro h.
    apply membership.backward.distributivity.over.concatenation.
    destruct h as [e | h'].
    + apply Disjunction.R.
      simpl in |- *.
      exact (Disjunction.L e).
    + exact (Disjunction.L h').
Qed.

(* The mirror of [reverse]'s own step: its definition turns a [Cons] into
 * an [append], and this turns an [append] back into a [Cons].
 *)
(* appending.reversal *)
Theorem reversal
  : forall {A : Type} (l : List A) (a : A) . reverse (append l a) = a :: reverse l.
Proof.
  intros A l a.
  rewrite (appending.specification l a) in |- *.
  rewrite (reversal.antidistributivity.over.concatenation l (a :: [])) in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End appending. (* appending *)

Module filtering. (* filtering *)

Module distributivity. (* filtering.distributivity *)

Module over. (* filtering.distributivity.over *)

(* filtering.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (p : A -> Bool) (l1 : List A) (l2 : List A) .
      filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  intros A p l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    destruct (p b) as [|].
    + simpl in |- *.
      rewrite IH in |- *.
      reflexivity.
    + simpl in |- *.
      exact IH.
Qed.

End over. (* filtering.distributivity.over *)

End distributivity. (* filtering.distributivity *)

(* [filter] is a catamorphism too: [Cons] becomes a conditional [Cons]. *)
(* filtering.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      filter p l
      = fold_right (fun (a : A) (rest : List A) .
                      match p a with
                      | true  => a :: rest
                      | false => rest
                      end)
                    []
                    l.
Proof.
  intros A p l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module forward. (* filtering.forward *)

(* filtering.forward.specification *)
Lemma specification
  : forall {A : Type} {p : A -> Bool} {a : A} {l : List A} .
      filter p l contains_member a -> l contains_member a /\ p a = true.
Proof.
  intros A p a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    contradiction f.
  - simpl in |- *.
    destruct (p b) as [|] eqn:pb.
    + simpl in |- *.
      intro h.
      destruct h as [e | h'].
      * split.
        -- exact (Disjunction.L e).
        -- rewrite e in |- *.
           exact pb.
      * destruct (IH h') as [hl pa].
        split.
        -- exact (Disjunction.R hl).
        -- exact pa.
    + simpl in |- *.
      intro h'.
      destruct (IH h') as [hl pa].
      split.
      * exact (Disjunction.R hl).
      * exact pa.
Qed.

End forward. (* filtering.forward *)

Module backward. (* filtering.backward *)

(* filtering.backward.specification *)
Lemma specification
  : forall {A : Type} {p : A -> Bool} {a : A} {l : List A} .
      l contains_member a /\ p a = true -> filter p l contains_member a.
Proof.
  intros A p a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    destruct h as [f _].
    contradiction f.
  - simpl in |- *.
    intro h.
    destruct h as [h1 pa].
    destruct h1 as [e | h'].
    + rewrite e in pa.
      rewrite pa in |- *.
      simpl in |- *.
      exact (Disjunction.L e).
    + destruct (p b) as [|].
      * simpl in |- *.
        apply Disjunction.R.
        apply IH.
        split.
        -- exact h'.
        -- exact pa.
      * simpl in |- *.
        apply IH.
        split.
        -- exact h'.
        -- exact pa.
Qed.

End backward. (* filtering.backward *)

(* filtering.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (a : A) (l : List A) .
      filter p l contains_member a <-> l contains_member a /\ p a = true.
Proof.
  intros A p a l.
  split.
  - exact (@filtering.forward.specification  A p a l).
  - exact (@filtering.backward.specification A p a l).
Qed.

End filtering. (* filtering *)

Module quantification. (* quantification *)

Module all. (* quantification.all *)

Module forward. (* quantification.all.forward *)

Module distributivity. (* quantification.all.forward.distributivity *)

Module over. (* quantification.all.forward.distributivity.over *)

(* [All] over a concatenation is [All] over each half. *)
(* quantification.all.forward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {P : A -> Prop} {l1 : List A} {l2 : List A} .
      All P (l1 ++ l2) -> All P l1 /\ All P l2.
Proof.
  intros A P l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    split.
    + exact I.
    + exact h.
  - simpl in |- *.
    intro h.
    destruct h as [pb h'].
    destruct (IH h') as [h1 h2].
    split.
    + split.
      * exact pb.
      * exact h1.
    + exact h2.
Qed.

End over. (* quantification.all.forward.distributivity.over *)

End distributivity. (* quantification.all.forward.distributivity *)

(* quantification.all.forward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      All P l -> forall (a : A) . l contains_member a -> P a.
Proof.
  intros A P l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intros v a f.
    contradiction f.
  - simpl in |- *.
    intro h.
    destruct h as [pb h'].
    intros a ha.
    destruct ha as [e | ha'].
    + rewrite e in |- *.
      exact pb.
    + apply (IH h').
      exact ha'.
Qed.

End forward. (* quantification.all.forward *)

Module backward. (* quantification.all.backward *)

Module distributivity. (* quantification.all.backward.distributivity *)

Module over. (* quantification.all.backward.distributivity.over *)

(* quantification.all.backward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {P : A -> Prop} {l1 : List A} {l2 : List A} .
      All P l1 /\ All P l2 -> All P (l1 ++ l2).
Proof.
  intros A P l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    destruct h as [_ h2].
    exact h2.
  - simpl in |- *.
    intro h.
    destruct h as [h1 h2].
    destruct h1 as [pb h1'].
    split.
    + exact pb.
    + apply IH.
      split.
      * exact h1'.
      * exact h2.
Qed.

End over. (* quantification.all.backward.distributivity.over *)

End distributivity. (* quantification.all.backward.distributivity *)

(* quantification.all.backward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      (forall (a : A) . l contains_member a -> P a) -> All P l.
Proof.
  intros A P l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact I.
  - simpl in |- *.
    intro h.
    split.
    + apply (h b).
      exact (Disjunction.L (Identity.reflexivity b)).
    + apply IH.
      intros a ha.
      apply (h a).
      exact (Disjunction.R ha).
Qed.

End backward. (* quantification.all.backward *)

Module distributivity. (* quantification.all.distributivity *)

Module over. (* quantification.all.distributivity.over *)

(* quantification.all.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
      All P (l1 ++ l2) <-> All P l1 /\ All P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (@quantification.all.forward.distributivity.over.concatenation  A P l1 l2).
  - exact (@quantification.all.backward.distributivity.over.concatenation A P l1 l2).
Qed.

End over. (* quantification.all.distributivity.over *)

End distributivity. (* quantification.all.distributivity *)

(* quantification.all.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      All P l <-> (forall (a : A) . l contains_member a -> P a).
Proof.
  intros A P l.
  split.
  - exact (@quantification.all.forward.specification  A P l).
  - exact (@quantification.all.backward.specification A P l).
Qed.

(* quantification.all.monotonicity *)
Lemma monotonicity
  : forall {A : Type} {P : A -> Prop} {Q : A -> Prop} {l : List A} .
      (forall (a : A) . P a -> Q a) -> All P l -> All Q l.
Proof.
  intros A P Q l h.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro v.
    exact v.
  - simpl in |- *.
    intro c.
    destruct c as [pb all'].
    exact (Conjunction_introduction (h b pb) (IH all')).
Qed.

(* quantification.all.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      All P l = fold_right (fun (a : A) (rest : Prop) . P a /\ rest) Verum l.
Proof.
  intros A P l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End all. (* quantification.all *)

Module any. (* quantification.any *)

Module forward. (* quantification.any.forward *)

Module distributivity. (* quantification.any.forward.distributivity *)

Module over. (* quantification.any.forward.distributivity.over *)

(* [Any] over a concatenation is [Any] over either half. *)
(* quantification.any.forward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {P : A -> Prop} {l1 : List A} {l2 : List A} .
      Any P (l1 ++ l2) -> Any P l1 \/ Any P l2.
Proof.
  intros A P l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact (Disjunction.R h).
  - simpl in |- *.
    intro h.
    destruct h as [pb | h'].
    + exact (Disjunction.L (Disjunction.L pb)).
    + destruct (IH h') as [h1 | h2].
      * exact (Disjunction.L (Disjunction.R h1)).
      * exact (Disjunction.R h2).
Qed.

End over. (* quantification.any.forward.distributivity.over *)

End distributivity. (* quantification.any.forward.distributivity *)

(* quantification.any.forward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      Any P l -> exists (a : A) . l contains_member a /\ P a.
Proof.
  intros A P l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    contradiction f.
  - simpl in |- *.
    intro h.
    destruct h as [pb | h'].
    + apply (Exists_introduction b).
      split.
      * exact (Disjunction.L (Identity.reflexivity b)).
      * exact pb.
    + destruct (IH h') as [a ha].
      destruct ha as [ha' pa].
      apply (Exists_introduction a).
      split.
      * exact (Disjunction.R ha').
      * exact pa.
Qed.

End forward. (* quantification.any.forward *)

Module backward. (* quantification.any.backward *)

Module distributivity. (* quantification.any.backward.distributivity *)

Module over. (* quantification.any.backward.distributivity.over *)

(* quantification.any.backward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {P : A -> Prop} {l1 : List A} {l2 : List A} .
      Any P l1 \/ Any P l2 -> Any P (l1 ++ l2).
Proof.
  intros A P l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    destruct h as [f | h2].
    + contradiction f.
    + exact h2.
  - simpl in |- *.
    intro h.
    destruct h as [h1 | h2].
    + destruct h1 as [pb | h1'].
      * exact (Disjunction.L pb).
      * apply Disjunction.R.
        apply IH.
        exact (Disjunction.L h1').
    + apply Disjunction.R.
      apply IH.
      exact (Disjunction.R h2).
Qed.

End over. (* quantification.any.backward.distributivity.over *)

End distributivity. (* quantification.any.backward.distributivity *)

(* quantification.any.backward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      (exists (a : A) . l contains_member a /\ P a) -> Any P l.
Proof.
  intros A P l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    destruct h as [a ha].
    destruct ha as [f _].
    contradiction f.
  - simpl in |- *.
    intro h.
    destruct h as [a ha].
    destruct ha as [ha' pa].
    destruct ha' as [e | ha''].
    + rewrite e in pa.
      exact (Disjunction.L pa).
    + apply Disjunction.R.
      apply IH.
      apply (Exists_introduction a).
      split.
      * exact ha''.
      * exact pa.
Qed.

End backward. (* quantification.any.backward *)

Module distributivity. (* quantification.any.distributivity *)

Module over. (* quantification.any.distributivity.over *)

(* quantification.any.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
      Any P (l1 ++ l2) <-> Any P l1 \/ Any P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (@quantification.any.forward.distributivity.over.concatenation  A P l1 l2).
  - exact (@quantification.any.backward.distributivity.over.concatenation A P l1 l2).
Qed.

End over. (* quantification.any.distributivity.over *)

End distributivity. (* quantification.any.distributivity *)

(* quantification.any.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      Any P l <-> (exists (a : A) . l contains_member a /\ P a).
Proof.
  intros A P l.
  split.
  - exact (@quantification.any.forward.specification  A P l).
  - exact (@quantification.any.backward.specification A P l).
Qed.

(* quantification.any.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      Any P l = fold_right (fun (a : A) (rest : Prop) . P a \/ rest) Falsum l.
Proof.
  intros A P l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End any. (* quantification.any *)

End quantification. (* quantification *)

Module head. (* head *)

Module forward. (* head.forward *)

(* head.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      head l = Some a -> exists (l' : List A) . l = a :: l'.
Proof.
  intros A a l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity e) as e'.
    apply (Exists_introduction rest).
    rewrite e' in |- *.
    reflexivity.
Qed.

End forward. (* head.forward *)

Module backward. (* head.backward *)

(* head.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      (exists (l' : List A) . l = a :: l') -> head l = Some a.
Proof.
  intros A a l.
  intro h.
  destruct h as [l' e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End backward. (* head.backward *)

(* head.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l : List A) .
      head l = Some a <-> (exists (l' : List A) . l = a :: l').
Proof.
  intros A a l.
  split.
  - exact (@head.forward.specification  A a l).
  - exact (@head.backward.specification A a l).
Qed.

End head. (* head *)

Module tail. (* tail *)

Module forward. (* tail.forward *)

(* tail.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      tail l = Some l' -> exists (a : A) . l = a :: l'.
Proof.
  intros A l l'.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity e) as e'.
    apply (Exists_introduction b).
    rewrite e' in |- *.
    reflexivity.
Qed.

End forward. (* tail.forward *)

Module backward. (* tail.backward *)

(* tail.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      (exists (a : A) . l = a :: l') -> tail l = Some l'.
Proof.
  intros A l l'.
  intro h.
  destruct h as [a e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End backward. (* tail.backward *)

(* tail.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (l' : List A) .
      tail l = Some l' <-> (exists (a : A) . l = a :: l').
Proof.
  intros A l l'.
  split.
  - exact (@tail.forward.specification  A l l').
  - exact (@tail.backward.specification A l l').
Qed.

End tail. (* tail *)

Module last. (* last *)

Module forward. (* last.forward *)

(* last.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      last l = Some a -> exists (l' : List A) . l = append l' a.
Proof.
  intros A a l.
  unfold last in |- *.
  intro h.
  destruct (head.forward.specification h) as [r e].
  apply (Exists_introduction (reverse r)).
  pose proof (Identity.congruence reverse e) as e'.
  rewrite reversal.involution in e'.
  simpl in e'.
  exact e'.
Qed.

End forward. (* last.forward *)

Module backward. (* last.backward *)

(* last.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      (exists (l' : List A) . l = append l' a) -> last l = Some a.
Proof.
  intros A a l.
  intro h.
  destruct h as [l' e].
  unfold last in |- *.
  rewrite e in |- *.
  rewrite appending.reversal in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End backward. (* last.backward *)

(* last.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l : List A) .
      last l = Some a <-> (exists (l' : List A) . l = append l' a).
Proof.
  intros A a l.
  split.
  - exact (@last.forward.specification  A a l).
  - exact (@last.backward.specification A a l).
Qed.

End last. (* last *)

Module initial. (* initial *)

Module forward. (* initial.forward *)

(* initial.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      initial l = Some l' -> exists (a : A) . l = append l' a.
Proof.
  intros A l l'.
  unfold initial in |- *.
  destruct (reverse l) as [| b r] eqn:er.
  - simpl in |- *.
    intro h.
    discriminate h.
  - simpl in |- *.
    intro h.
    pose proof (Option.some.injectivity h) as e'.
    apply (Exists_introduction b).
    pose proof (Identity.congruence reverse er) as er'.
    rewrite reversal.involution in er'.
    simpl in er'.
    rewrite e' in er'.
    exact er'.
Qed.

End forward. (* initial.forward *)

Module backward. (* initial.backward *)

(* initial.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      (exists (a : A) . l = append l' a) -> initial l = Some l'.
Proof.
  intros A l l'.
  intro h.
  destruct h as [a e].
  unfold initial in |- *.
  rewrite e in |- *.
  rewrite appending.reversal in |- *.
  simpl in |- *.
  rewrite reversal.involution in |- *.
  reflexivity.
Qed.

End backward. (* initial.backward *)

(* initial.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (l' : List A) .
      initial l = Some l' <-> (exists (a : A) . l = append l' a).
Proof.
  intros A l l'.
  split.
  - exact (@initial.forward.specification  A l l').
  - exact (@initial.backward.specification A l l').
Qed.

End initial. (* initial *)

Module popping. (* popping *)

Module forward. (* popping.forward *)

(* popping.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l' : List A} {l : List A} .
      pop l = Some (Product_introduction a l') -> l = a :: l'.
Proof.
  intros A a l' l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity e) as e'.
    pose proof (Product.introduction.injectivity e') as e''.
    destruct e'' as [eb erest].
    rewrite eb, erest in |- *.
    reflexivity.
Qed.

End forward. (* popping.forward *)

Module backward. (* popping.backward *)

(* popping.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l' : List A} {l : List A} .
      l = a :: l' -> pop l = Some (Product_introduction a l').
Proof.
  intros A a l' l e.
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End backward. (* popping.backward *)

(* [pop] answers [Some (a , l')] exactly on [Cons a l']. *)
(* popping.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l' : List A) (l : List A) .
      pop l = Some (Product_introduction a l') <-> l = a :: l'.
Proof.
  intros A a l' l.
  split.
  - exact (@popping.forward.specification  A a l' l).
  - exact (@popping.backward.specification A a l' l).
Qed.

(* Projecting a [pop] gives back [head] and [tail]. *)

Module head. (* popping.head *)

(* popping.head.projection *)
Theorem projection
  : forall {A : Type} (l : List A) . Option.map Product.first (pop l) = head l.
Proof.
  intros A l.
  destruct l as [| a l']; simpl in |- *; reflexivity.
Qed.

End head. (* popping.head *)

Module tail. (* popping.tail *)

(* popping.tail.projection *)
Theorem projection
  : forall {A : Type} (l : List A) . Option.map Product.second (pop l) = tail l.
Proof.
  intros A l.
  destruct l as [| a l']; simpl in |- *; reflexivity.
Qed.

End tail. (* popping.tail *)

End popping. (* popping *)

Module zipping. (* zipping *)

Module inversion. (* zipping.inversion *)

Module of. (* zipping.inversion.of *)

(* Zipping the two halves of an [unzip] rebuilds the list. The other order,
 * [unzip (zip l1 l2)], needs the two lists to be of one length.
 *)
(* zipping.inversion.of.unzipping *)
Theorem unzipping
  : forall {A : Type} {B : Type} (l : List (A * B)) .
      zip (Product.first (unzip l)) (Product.second (unzip l)) = l.
Proof.
  intros A B l.
  induction l as [| p l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    unfold unzip in IH.
    simpl in IH.
    rewrite IH in |- *.
    rewrite <- (Product.introduction.surjectivity p) in |- *.
    reflexivity.
Qed.

End of. (* zipping.inversion.of *)

End inversion. (* zipping.inversion *)

(* [zip] stops with the shorter list, so its length is the smaller of the
 * two; each step adds one to both, and addition distributes over [min].
 *)
(* zipping.length *)
Theorem length
  : forall {A : Type} {B : Type} (l1 : List A) (l2 : List B) .
      (|| zip l1 l2 ||) = NatWithZero.min (|| l1 ||) (|| l2 ||).
Proof.
  intros A B l1.
  induction l1 as [| a l1' IH] using List_induction.
  - intros l2.
    destruct l2 as [| b l2'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (NatWithZero.minimum.left.annihilation (++ (|| l2' ||))) in |- *.
      reflexivity.
  - intros l2.
    destruct l2 as [| b l2'].
    + simpl in |- *.
      rewrite (NatWithZero.minimum.right.annihilation (++ (|| l1' ||))) in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (IH l2') in |- *.
      rewrite (NatWithZero.increment.specification
                 (NatWithZero.min (|| l1' ||) (|| l2' ||))) in |- *.
      rewrite (NatWithZero.minimum.left.distributivity.of.addition
                 (Positive One) (|| l1' ||) (|| l2' ||)) in |- *.
      rewrite (NatWithZero.increment.specification (|| l1' ||)) in |- *.
      rewrite (NatWithZero.increment.specification (|| l2' ||)) in |- *.
      reflexivity.
Qed.

End zipping. (* zipping *)

Module unzipping. (* unzipping *)

Module inversion. (* unzipping.inversion *)

Module of. (* unzipping.inversion.of *)

(* Unzipping a [zip] gives the two lists back when they are of one length;
 * [zip] stops with the shorter list, so a longer one is not recovered.
 * Induction on [l1] with [l2] kept in the motive, since [zip] and
 * [length] step on both lists at once; the two mismatched cases contradict
 * [NatWithZero.addition.right.identity.absence] and the matched case feeds the
 * hypothesis through [NatWithZero.addition.left.cancellation].
 *)
(* unzipping.inversion.of.zipping *)
Theorem zipping
  : forall {A : Type} {B : Type} {l1 : List A} {l2 : List B} .
      (|| l1 ||) = (|| l2 ||) -> unzip (zip l1 l2) = Product_introduction l1 l2.
Proof.
  intros A B l1.
  induction l1 as [| a l1' IH] using List_induction.
  - intros l2 e.
    destruct l2 as [| b l2'].
    + unfold unzip in |- *.
      simpl in |- *.
      reflexivity.
    + simpl in e.
      pose proof (Identity.symmetry e) as e'.
      rewrite (NatWithZero.increment.specification (|| l2' ||)) in e'.
      rewrite (NatWithZero.addition.commutativity (Positive One) (|| l2' ||)) in e'.
      pose proof (NatWithZero.addition.right.identity.absence (|| l2' ||) One) as h.
      unfold Negation in h.
      modus ponens h, e' as f.
      contradiction f.
  - intros l2 e.
    destruct l2 as [| b l2'].
    + simpl in e.
      rewrite (NatWithZero.increment.specification (|| l1' ||)) in e.
      rewrite (NatWithZero.addition.commutativity (Positive One) (|| l1' ||)) in e.
      pose proof (NatWithZero.addition.right.identity.absence (|| l1' ||) One) as h.
      unfold Negation in h.
      modus ponens h, e as f.
      contradiction f.
    + simpl in e.
      rewrite (NatWithZero.increment.specification (|| l1' ||)) in e.
      rewrite (NatWithZero.increment.specification (|| l2' ||)) in e.
      pose proof (NatWithZero.addition.left.cancellation e) as e'.
      pose proof (IH l2' e') as IH'.
      unfold unzip in IH'.
      pose proof (Product.introduction.injectivity IH') as e''.
      destruct e'' as [e1 e2].
      unfold unzip in |- *.
      simpl in |- *.
      rewrite e1 in |- *.
      rewrite e2 in |- *.
      reflexivity.
Qed.

End of. (* unzipping.inversion.of *)

End inversion. (* unzipping.inversion *)

End unzipping. (* unzipping *)

Module partitioning. (* partitioning *)

(* partitioning.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      partition p l
      = Product_introduction
          (filter p l)
          (filter (fun (a : A) . ! p a) l).
Proof.
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    destruct (p a) as [|] eqn:pa; simpl in |- *; reflexivity.
Qed.

End partitioning. (* partitioning *)

Module indexing. (* indexing *)

(* [nth] answers exactly for the indices below the length. Each step of the
 * index is one step of the list, so the halves lift [IH] through
 * [Positive One] added on both sides of the order.
 *)

Module forward. (* indexing.forward *)

(* indexing.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {i : NatWithZero} .
      (exists (a : A) . nth l i = Some a) -> i < (|| l ||).
Proof.
  intros A l.
  induction l as [| b l' IH] using List_induction.
  - intros i h.
    destruct h as [a e].
    simpl in e.
    discriminate e.
  - intros i h.
    destruct i as [| i'].
    + simpl in |- *.
      rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
      rewrite (NatWithZero.addition.commutativity (Positive One) (|| l' ||)) in |- *.
      exact (NatWithZero.addition.right.order.positivity (|| l' ||) One).
    + destruct i' as [| i''].
      * simpl in h.
        pose proof (IH Zero h) as lt.
        simpl in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        exact (NatWithZero.addition.order.strict.monotonicity (Positive One) Zero (|| l' ||) lt).
      * simpl in h.
        pose proof (IH (Positive i'') h) as lt.
        simpl in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        exact (NatWithZero.addition.order.strict.monotonicity
                 (Positive One) (Positive i'') (|| l' ||) lt).
Qed.

End forward. (* indexing.forward *)

Module backward. (* indexing.backward *)

(* indexing.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {i : NatWithZero} .
      i < (|| l ||) -> exists (a : A) . nth l i = Some a.
Proof.
  intros A l.
  induction l as [| b l' IH] using List_induction.
  - intros i h.
    simpl in h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    pose proof (NatWithZero.addition.right.identity.absence i k) as r.
    unfold Negation in r.
    modus ponens r, e as f.
    contradiction f.
  - intros i h.
    destruct i as [| i'].
    + simpl in |- *.
      apply (Exists_introduction b).
      reflexivity.
    + destruct i' as [| i''].
      * simpl in h.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in h.
        pose proof (NatWithZero.addition.order.strict.cancellation (Positive One) Zero (|| l' ||) h)
          as lt.
        simpl in |- *.
        exact (IH Zero lt).
      * simpl in h.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in h.
        pose proof (NatWithZero.addition.order.strict.cancellation
                      (Positive One) (Positive i'') (|| l' ||) h) as lt.
        simpl in |- *.
        exact (IH (Positive i'') lt).
Qed.

End backward. (* indexing.backward *)

(* indexing.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (i : NatWithZero) .
      (exists (a : A) . nth l i = Some a) <-> i < (|| l ||).
Proof.
  intros A l i.
  split.
  - exact (@indexing.forward.specification  A l i).
  - exact (@indexing.backward.specification A l i).
Qed.

End indexing. (* indexing *)

Module splitting. (* splitting *)

(* The two parts put back together give the list. *)
(* splitting.decomposition *)
Theorem decomposition
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      take n l ++ drop n l = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - intros n.
    simpl in |- *.
    reflexivity.
  - intros n.
    destruct n as [| n'].
    + simpl in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * simpl in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        reflexivity.
Qed.

End splitting. (* splitting *)

Module taking. (* taking *)

(* The length of a [take] is the smaller of the count and the length; each
 * step adds one to both candidates, and addition distributes over [min].
 *)
(* taking.length *)
Theorem length
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      (|| take n l ||) = NatWithZero.min n (|| l ||).
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - intros n.
    simpl in |- *.
    rewrite (NatWithZero.minimum.right.annihilation n) in |- *.
    reflexivity.
  - intros n.
    destruct n as [| n'].
    + simpl in |- *.
      rewrite (NatWithZero.minimum.left.annihilation (++ (|| l' ||))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * simpl in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        rewrite (NatWithZero.addition.commutativity (Positive One) (|| l' ||)) in |- *.
        rewrite (<-elim
                   (Comparable.minimum.specification (Positive One)
                      ((|| l' ||) + Positive One))
                   (NatWithZero.addition.right.order.extensivity
                      (|| l' ||) (Positive One))) in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        rewrite (NatWithZero.increment.specification
                   (NatWithZero.min (Positive n'') (|| l' ||))) in |- *.
        rewrite (NatWithZero.minimum.left.distributivity.of.addition
                   (Positive One) (Positive n'') (|| l' ||)) in |- *.
        change (Positive One + Positive n'')
          with (Positive (Successor n'')) in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        reflexivity.
Qed.

End taking. (* taking *)

Module dropping. (* dropping *)

(* The length of a [drop] is the length less the count; each step takes one
 * from both, which truncated subtraction ignores.
 *)
(* dropping.length *)
Theorem length
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      (|| drop n l ||) = NatWithZero.saturating_sub (|| l ||) n.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - intros n.
    simpl in |- *.
    reflexivity.
  - intros n.
    destruct n as [| n'].
    + simpl in |- *.
      rewrite (NatWithZero.subtraction.saturating.right.identity (++ (|| l' ||))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * simpl in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        rewrite (NatWithZero.addition.commutativity (Positive One) (|| l' ||)) in |- *.
        rewrite (NatWithZero.subtraction.saturating.inversion.of.addition
                   (|| l' ||) (Positive One)) in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        rewrite (NatWithZero.increment.specification (|| l' ||)) in |- *.
        change (Positive (Successor n''))
          with (Positive One + Positive n'') in |- *.
        rewrite (NatWithZero.subtraction.saturating.cancellation
                   (Positive One) (|| l' ||) (Positive n'')) in |- *.
        reflexivity.
Qed.

End dropping. (* dropping *)

Module replication. (* replication *)

Module positive. (* replication.positive *)

(* replication.positive.length *)
Lemma length
  : forall {A : Type} (k : Nat) (a : A) . (|| replicate_positive k a ||) = Positive k.
Proof.
  intros A k a.
  induction k as [| k' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    reflexivity.
Qed.

End positive. (* replication.positive *)

(* replication.length *)
Theorem length
  : forall {A : Type} (n : NatWithZero) (a : A) . (|| replicate n a ||) = n.
Proof.
  intros A n a.
  destruct n as [| k].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (replication.positive.length k a).
Qed.

End replication. (* replication *)

Module sum. (* sum *)

Module additivity. (* sum.additivity *)

Module over. (* sum.additivity.over *)

(* sum.additivity.over.concatenation *)
Theorem concatenation
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero) .
      sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  intros l1 l2.
  unfold sum in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.addition.associativity
               a (fold_right NatWithZero.add Zero l1') (fold_right NatWithZero.add Zero l2))
      in |- *.
    reflexivity.
Qed.

End over. (* sum.additivity.over *)

End additivity. (* sum.additivity *)

End sum. (* sum *)

Module product. (* product *)

Module multiplicativity. (* product.multiplicativity *)

Module over. (* product.multiplicativity.over *)

(* product.multiplicativity.over.concatenation *)
Theorem concatenation
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero) .
      product (l1 ++ l2) = product l1 * product l2.
Proof.
  intros l1 l2.
  unfold product in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - rewrite (concatenation.left.identity l2) in |- *.
    change (fold_right NatWithZero.mul (Positive One) []) with (Positive One) in |- *.
    rewrite (NatWithZero.multiplication.left.identity
               (fold_right NatWithZero.mul (Positive One) l2))
      in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.multiplication.associativity
               a (fold_right NatWithZero.mul (Positive One) l1')
               (fold_right NatWithZero.mul (Positive One) l2)) in |- *.
    reflexivity.
Qed.

End over. (* product.multiplicativity.over *)

End multiplicativity. (* product.multiplicativity *)

End product. (* product *)

Module counting. (* counting *)

(* counting.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (l : List A) . count p l = (|| filter p l ||).
Proof.
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    destruct (p a) as [|].
    + simpl in |- *.
      rewrite IH in |- *.
      reflexivity.
    + exact IH.
Qed.

Module zero. (* counting.zero *)

(* [count] answers [Zero] exactly when [p] answers [false] on every
 * member.
 *)
(* counting.zero.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      count p l = Zero <-> All (fun (a : A) . p a = false) l.
Proof.
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    split.
    + intro e.
      exact I.
    + intro v.
      reflexivity.
  - simpl in |- *.
    destruct (p a) as [|].
    + simpl in |- *.
      split.
      * intro e.
        rewrite (NatWithZero.increment.specification (count p l')) in e.
        rewrite (NatWithZero.addition.commutativity (Positive One) (count p l')) in e.
        pose proof (NatWithZero.addition.right.identity.absence (count p l') One) as r.
        unfold Negation in r.
        modus ponens r, e as f.
        contradiction f.
      * intro c.
        destruct c as [e f].
        discriminate e.
    + simpl in |- *.
      split.
      * intro e.
        exact (Conjunction_introduction
                 (Identity.reflexivity false)
                 (->elim IH e)).
      * intro c.
        destruct c as [e all'].
        exact (<-elim IH all').
Qed.

End zero. (* counting.zero *)

End counting. (* counting *)

Module sorting. (* sorting *)

Module insertion. (* sorting.insertion *)

Module preservation. (* sorting.insertion.preservation *)

Module of. (* sorting.insertion.preservation.of *)

(* sorting.insertion.preservation.of.all *)
Lemma all
  : forall {A : Type} (le : A -> A -> Bool) (P : A -> Prop) (a : A) (l : List A) .
      P a -> All P l -> All P (insert le a l).
Proof.
  intros A le P a l pa.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro v.
    exact (Conjunction_introduction pa v).
  - simpl in |- *.
    intro c.
    destruct c as [pb all'].
    destruct (le a b) as [|].
    + simpl in |- *.
      exact (Conjunction_introduction pa (Conjunction_introduction pb all')).
    + simpl in |- *.
      exact (Conjunction_introduction pb (IH all')).
Qed.

End of. (* sorting.insertion.preservation.of *)

End preservation. (* sorting.insertion.preservation *)

(* sorting.insertion.sortedness *)
Lemma sortedness
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall (a : A) (l : List A) . Sorted le l -> Sorted le (insert le a l).
Proof.
  intros A le total transitive a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro v.
    exact (Conjunction_introduction v v).
  - simpl in |- *.
    intro s.
    destruct s as [below sorted'].
    destruct (le a b) as [|] eqn:c.
    + simpl in |- *.
      pose proof (quantification.all.monotonicity
                    (fun (x : A) (h : le b x = true) . transitive a b x c h) below)
        as below_a.
      exact (Conjunction_introduction
               (Conjunction_introduction c below_a)
               (Conjunction_introduction below sorted')).
    + simpl in |- *.
      pose proof (total a b) as t.
      destruct t as [ab | ba].
      * rewrite c in ab.
        discriminate ab.
      * exact (Conjunction_introduction
                 (sorting.insertion.preservation.of.all
                    le (fun (x : A) . le b x = true) a l' ba below)
                 (IH sorted')).
Qed.

(* [insert] adds exactly its element to the members. *)

Module forward. (* sorting.insertion.forward *)

(* sorting.insertion.forward.membership *)
Lemma membership
  : forall {A : Type} {le : A -> A -> Bool} {a : A} {b : A} {l : List A} .
      insert le a l contains_member b -> b = a \/ l contains_member b.
Proof.
  intros A le a b l.
  induction l as [| c l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    destruct (le a c) as [|].
    + simpl in |- *.
      intro h.
      exact h.
    + simpl in |- *.
      intro h.
      destruct h as [e | h'].
      * exact (Disjunction.R (Disjunction.L e)).
      * modus ponens IH, h' as h''.
        destruct h'' as [e | h'''].
        { exact (Disjunction.L e). }
        { exact (Disjunction.R (Disjunction.R h''')). }
Qed.

End forward. (* sorting.insertion.forward *)

Module backward. (* sorting.insertion.backward *)

(* sorting.insertion.backward.membership *)
Lemma membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
      b = a \/ l contains_member b -> insert le a l contains_member b.
Proof.
  intros A le a b l.
  induction l as [| c l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    destruct (le a c) as [|].
    + simpl in |- *.
      intro h.
      exact h.
    + simpl in |- *.
      intro h.
      destruct h as [e | h'].
      * exact (Disjunction.R (IH (Disjunction.L e))).
      * destruct h' as [e | h''].
        { exact (Disjunction.L e). }
        { exact (Disjunction.R (IH (Disjunction.R h''))). }
Qed.

End backward. (* sorting.insertion.backward *)

(* sorting.insertion.membership *)
Theorem membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
      insert le a l contains_member b <-> b = a \/ l contains_member b.
Proof.
  intros A le a b l.
  split.
  - exact (@sorting.insertion.forward.membership  A le a b l).
  - exact (sorting.insertion.backward.membership le a b l).
Qed.

(* sorting.insertion.length *)
Lemma length
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      (|| insert le a l ||) = ++ (|| l ||).
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    destruct (le a b) as [|].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite IH in |- *.
      reflexivity.
Qed.

End insertion. (* sorting.insertion *)

(* sorting.sortedness *)
Theorem sortedness
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall (l : List A) . Sorted le (insertion_sort le l).
Proof.
  intros A le total transitive l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    exact I.
  - simpl in |- *.
    exact (sorting.insertion.sortedness
             total transitive a (insertion_sort le l') IH).
Qed.

Module forward. (* sorting.forward *)

Module preservation. (* sorting.forward.preservation *)

Module of. (* sorting.forward.preservation.of *)

(* sorting.forward.preservation.of.membership *)
Lemma membership
  : forall {A : Type} {le : A -> A -> Bool} {a : A} {l : List A} .
      insertion_sort le l contains_member a -> l contains_member a.
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    intro h.
    pose proof (sorting.insertion.forward.membership h) as h'.
    destruct h' as [e | h''].
    + exact (Disjunction.L e).
    + exact (Disjunction.R (IH h'')).
Qed.

End of. (* sorting.forward.preservation.of *)

End preservation. (* sorting.forward.preservation *)

End forward. (* sorting.forward *)

Module backward. (* sorting.backward *)

Module preservation. (* sorting.backward.preservation *)

Module of. (* sorting.backward.preservation.of *)

(* sorting.backward.preservation.of.membership *)
Lemma membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      l contains_member a -> insertion_sort le l contains_member a.
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    intro h.
    apply (sorting.insertion.backward.membership le b a (insertion_sort le l')).
    destruct h as [e | h'].
    + exact (Disjunction.L e).
    + exact (Disjunction.R (IH h')).
Qed.

End of. (* sorting.backward.preservation.of *)

End preservation. (* sorting.backward.preservation *)

End backward. (* sorting.backward *)

Module preservation. (* sorting.preservation *)

Module of. (* sorting.preservation.of *)

(* sorting.preservation.of.membership *)
Theorem membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      insertion_sort le l contains_member a <-> l contains_member a.
Proof.
  intros A le a l.
  split.
  - exact (@sorting.forward.preservation.of.membership  A le a l).
  - exact (sorting.backward.preservation.of.membership le a l).
Qed.

(* sorting.preservation.of.length *)
Theorem length
  : forall {A : Type} (le : A -> A -> Bool) (l : List A) .
      (|| insertion_sort le l ||) = (|| l ||).
Proof.
  intros A le l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (sorting.insertion.length le a (insertion_sort le l')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End of. (* sorting.preservation.of *)

End preservation. (* sorting.preservation *)

End sorting. (* sorting *)

Module range. (* range *)

Module positive. (* range.positive *)

(* range.positive.length *)
Lemma length
  : forall (p : Nat) . (|| range_positive p ||) = Positive p.
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (appending.length (range_positive p') (Positive p')) in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Module forward. (* range.positive.forward *)

(* range.positive.forward.membership *)
Lemma membership
  : forall {p : Nat} {i : NatWithZero} .
      range_positive p contains_member i -> i < Positive p.
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - intros i h.
    simpl in h.
    destruct h as [e | f].
    + rewrite e in |- *.
      unfold NatWithZero.LessThan in |- *.
      apply (Exists_introduction One).
      simpl in |- *.
      reflexivity.
    + contradiction f.
  - intros i h.
    simpl in h.
    pose proof (->elim
                  (membership.distributivity.over.concatenation
                     i (range_positive p') (Positive p' :: []))
                  h) as h'.
    change (Positive (Successor p'))
      with (Positive One + Positive p') in |- *.
    rewrite (NatWithZero.addition.commutativity (Positive One) (Positive p')) in |- *.
    apply (<-elim (NatWithZero.order.discreteness i (Positive p'))).
    unfold NatWithZero.LessOrEqual in |- *.
    destruct h' as [h1 | h2].
    + exact (Disjunction.R (IH i h1)).
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.L e).
      * contradiction f.
Qed.

End forward. (* range.positive.forward *)

Module backward. (* range.positive.backward *)

(* range.positive.backward.membership *)
Lemma membership
  : forall {p : Nat} {i : NatWithZero} .
      i < Positive p -> range_positive p contains_member i.
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - intros i h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    destruct i as [| q].
    + simpl in |- *.
      exact (Disjunction.L (Identity.reflexivity Zero)).
    + simpl in e.
      pose proof (NatWithZero.positive.injectivity e) as e'.
      destruct q as [| q']; simpl in e'; discriminate e'.
  - intros i h.
    change (Positive (Successor p'))
      with (Positive One + Positive p')
      in h.
    rewrite (NatWithZero.addition.commutativity (Positive One) (Positive p')) in h.
    pose proof (->elim (NatWithZero.order.discreteness i (Positive p')) h) as h'.
    simpl in |- *.
    apply (<-elim
             (membership.distributivity.over.concatenation
                i (range_positive p') (Positive p' :: []))).
    unfold NatWithZero.LessOrEqual in h'.
    destruct h' as [e | lt].
    + apply Disjunction.R.
      simpl in |- *.
      exact (Disjunction.L e).
    + exact (Disjunction.L (IH i lt)).
Qed.

End backward. (* range.positive.backward *)

End positive. (* range.positive *)

(* range.length *)
Theorem length : forall (n : NatWithZero) . (|| range n ||) = n.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (range.positive.length p).
Qed.

Module membership. (* range.membership *)

(* range.membership.specification *)
Theorem specification
  : forall (n : NatWithZero) (i : NatWithZero) .
      range n contains_member i <-> i < n.
Proof.
  intros n i.
  destruct n as [| p].
  - simpl in |- *.
    split.
    + intro f.
      contradiction f.
    + intro h.
      unfold NatWithZero.LessThan in h.
      destruct h as [k e].
      pose proof (NatWithZero.addition.right.identity.absence i k) as r.
      unfold Negation in r.
      modus ponens r, e as f.
      contradiction f.
  - simpl in |- *.
    split.
    + exact (@range.positive.forward.membership  p i).
    + exact (@range.positive.backward.membership p i).
Qed.

End membership. (* range.membership *)

Module sum. (* range.sum *)

(* A closed form is an answer written with a fixed number of operations,
 * none of them recursive: [sum (range n)] has to walk the list, while
 * [n * (n + One) / Two] does not, and the count of steps no longer grows
 * with [n]. There is no division here, so both sides are multiplied by
 * two.
 *)
(* range.sum.closed_form *)
Theorem closed_form
  : forall (p : Nat) .
      Positive (Successor One) * sum (range (Positive (Successor p)))
      = Positive p * Positive (Successor p).
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - unfold sum in |- *.
    simpl in |- *.
    reflexivity.
  - change (range (Positive (Successor (Successor p'))))
      with (append (range (Positive (Successor p'))) (Positive (Successor p')))
      in |- *.
    rewrite (appending.specification
               (range (Positive (Successor p'))) (Positive (Successor p'))) in |- *.
    rewrite (sum.additivity.over.concatenation
               (range (Positive (Successor p'))) (Positive (Successor p') :: []))
      in |- *.
    change (sum (Positive (Successor p') :: [])) with (Positive (Successor p')) in |- *.
    rewrite (NatWithZero.multiplication.left.distributivity.over.addition
               (Positive (Successor One))
               (sum (range (Positive (Successor p')))) (Positive (Successor p'))) in |- *.
    rewrite IH in |- *.
    rewrite <- (NatWithZero.multiplication.right.distributivity.over.addition
                  (Positive (Successor p')) (Positive p') (Positive (Successor One)))
      in |- *.
    change (Positive p' + Positive (Successor One))
      with (Positive (Nat.add p' (Successor One))) in |- *.
    rewrite (Nat.addition.commutativity p' (Successor One)) in |- *.
    change (Nat.add (Successor One) p') with (Successor (Successor p')) in |- *.
    rewrite (NatWithZero.multiplication.commutativity
               (Positive (Successor p')) (Positive (Successor (Successor p')))) in |- *.
    reflexivity.
Qed.

End sum. (* range.sum *)

End range. (* range *)

Module maximum. (* maximum *)

(* maximum.bound *)
Theorem bound
  : forall (l : List NatWithZero) .
      All (fun (a : NatWithZero) . a <= maximum_of l) l.
Proof.
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    exact I.
  - simpl in |- *.
    split.
    + exact (Comparable.maximum.left.injection a (fold_right NatWithZero.max Zero l')).
    + exact (quantification.all.monotonicity
               (fun (x : NatWithZero)
                    (h : x <= fold_right NatWithZero.max Zero l') .
                  Comparable.order.transitivity
                    x (fold_right NatWithZero.max Zero l')
                    (NatWithZero.max a (fold_right NatWithZero.max Zero l'))
                    h
                    (Comparable.maximum.right.injection
                       a (fold_right NatWithZero.max Zero l')))
               IH).
Qed.

(* maximum.membership *)
Theorem membership
  : forall {l : List NatWithZero} . ~ (l = []) -> l contains_member maximum_of l.
Proof.
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - intro h.
    unfold Negation in h.
    pose proof (h (Identity.reflexivity [])) as f.
    contradiction f.
  - intro h.
    destruct l' as [| b l''].
    + simpl in |- *.
      rewrite (NatWithZero.maximum.right.identity a) in |- *.
      exact (Disjunction.L (Identity.reflexivity a)).
    + pose proof (IH (distinctness b l'')) as c.
      change (NatWithZero.max a (fold_right NatWithZero.max Zero (b :: l'')) = a
              \/ (b :: l'')
                 contains_member
                 NatWithZero.max a (fold_right NatWithZero.max Zero (b :: l''))) in |- *.
      pose proof (Comparable.order.totality
                    (fold_right NatWithZero.max Zero (b :: l'')) a) as t.
      destruct t as [le | ge].
      * apply Disjunction.L.
        exact (<-elim
                 (Comparable.maximum.specification
                    a (fold_right NatWithZero.max Zero (b :: l''))) le).
      * apply Disjunction.R.
        rewrite (Comparable.maximum.commutativity
                   a (fold_right NatWithZero.max Zero (b :: l''))) in |- *.
        rewrite (<-elim
                   (Comparable.maximum.specification
                      (fold_right NatWithZero.max Zero (b :: l'')) a) ge) in |- *.
        exact c.
Qed.

End maximum. (* maximum *)

Module minimum. (* minimum *)

Module absence. (* minimum.absence *)

(* minimum.absence.specification *)
Lemma specification
  : forall (l : List NatWithZero) . minimum_of l = None <-> l = [].
Proof.
  intros l.
  split.
  - intro e.
    destruct l as [| a l'].
    + reflexivity.
    + simpl in e.
      destruct (minimum_of l') as [| m].
      * discriminate e.
      * discriminate e.
  - intro e.
    rewrite e in |- *.
    simpl in |- *.
    reflexivity.
Qed.

End absence. (* minimum.absence *)

(* minimum.bound *)
Theorem bound
  : forall {l : List NatWithZero} {m : NatWithZero} .
      minimum_of l = Some m
      -> All (fun (a : NatWithZero) . m <= a) l.
Proof.
  intros l.
  induction l as [| a l' IH] using List_induction.
  - intros m e.
    simpl in e.
    discriminate e.
  - intros m e.
    simpl in e.
    destruct (minimum_of l') as [| m'] eqn:r.
    + simpl in e.
      pose proof (->elim (minimum.absence.specification l') r) as en.
      pose proof (Option.some.injectivity e) as e'.
      rewrite en in |- *.
      rewrite e' in |- *.
      simpl in |- *.
      exact (Conjunction_introduction (Comparable.order.reflexivity m) I).
    + simpl in e.
      pose proof (Option.some.injectivity e) as e'.
      symmetry in e'.
      rewrite e' in |- *.
      simpl in |- *.
      split.
      * exact (Comparable.minimum.left.projection a m').
      * exact (quantification.all.monotonicity
                 (fun (x : NatWithZero) (h : m' <= x) .
                    Comparable.order.transitivity
                      (NatWithZero.min a m') m' x
                      (Comparable.minimum.right.projection a m') h)
                 (IH m' (Identity.reflexivity (Some m')))).
Qed.

(* minimum.membership *)
Theorem membership
  : forall {l : List NatWithZero} {m : NatWithZero} .
      minimum_of l = Some m -> l contains_member m.
Proof.
  intros l.
  induction l as [| a l' IH] using List_induction.
  - intros m e.
    simpl in e.
    discriminate e.
  - intros m e.
    simpl in e.
    destruct (minimum_of l') as [| m'] eqn:r.
    + simpl in e.
      pose proof (Option.some.injectivity e) as e'.
      simpl in |- *.
      exact (Disjunction.L (Identity.symmetry e')).
    + simpl in e.
      pose proof (Option.some.injectivity e) as e'.
      symmetry in e'.
      rewrite e' in |- *.
      simpl in |- *.
      pose proof (Comparable.order.totality a m') as t.
      destruct t as [le | ge].
      * apply Disjunction.L.
        exact (<-elim (Comparable.minimum.specification a m') le).
      * apply Disjunction.R.
        rewrite (Comparable.minimum.commutativity a m') in |- *.
        rewrite (<-elim (Comparable.minimum.specification m' a) ge) in |- *.
        exact (IH m' (Identity.reflexivity (Some m'))).
Qed.

End minimum. (* minimum *)

End List. (* List *)

(* Makes the notations declared in [Module List] usable in every file that
 * imports this one, as [(l1 ++ l2)%list] or under an opened
 * [jwa_list_scope]. Only the notations are exported: [concat] and the laws
 * still need the [List.] prefix. The ctor notations [[]] and [::] are
 * declared above the module and reach a client with the module itself.
 *)
Export (notations) List.

Instance List_concat_monoid
  : forall {A : Type} . Monoid (@List.concat A) Nil :=
  fun (A : Type) .
    ({| Monoid.semigroup :=
          {| Semigroup.associativity := @List.concatenation.associativity A |}
      ; Monoid.identity := @List.concatenation.identity A |}).

Instance List_functor
  : Functor List :=
  {| Functor.map             := fun (A : Type) (B : Type) . List.map
   ; Functor.map_identity    := @List.mapping.identity
   ; Functor.map_composition := @List.mapping.composition |}.

Instance List_sized
  : Sized List :=
  {| Sized.cardinality := @List.length |}.

Instance List_membership
  : Membership List :=
  {| Membership.Contains := @List.Contains |}.
