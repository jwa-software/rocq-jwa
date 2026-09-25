(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Collection.Membership.
From jwa Require Import Data.Collection.Sized.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Tactics.Equation.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Syllogism.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [List.concat]. The
 * type and its ctors are declared inside it, so the names [Nil] and [Cons]
 * are reachable only as [List.Nil] and [List.Cons]. A bare ctor at the top
 * level is claimed by whichever file declares it last, silently and with no
 * warning, which makes the meaning of a name depend on import order.
 *)
Module List. (* List *)

(* A list is empty, or one element in front of a list. [A] is a parameter:
 * every element has the one type.
 *)
Inductive T (A : Type) : Type :=
  | Nil  : T A
  | Cons : A -> T A -> T A.

(* [A] is inferred from the element or, for [Nil], from the expected type; a
 * use that has neither needs [@Nil A].
 *)
Arguments Nil  {A}.
Arguments Cons {A} a l.

(* The carrier is named [T] so that the type itself reads [List] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End List].
 *)
Abbreviation List := T.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * Every list notation lives in [jwa_list_scope], which [Core.Notations]
 * declares without opening: a client writes [(a :: l)%list] or opens the
 * scope. The [Export (notations)] below the module is what carries these
 * out to a client, and it carries the notations alone, so [[]] and [::]
 * travel without [Nil] and [Cons].
 *)
(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil
  : jwa_list_scope.

(* [a :: l] puts one element in front; with [[]] it spells a list out:
 * [a :: b :: []].
 *)
Notation "a :: l" := (Cons a l)
  : jwa_list_scope.

(* Opening the scope here lets every definition and law below use them. *)
Local Open Scope jwa_list_scope.

(* The eliminator that [match ... per] takes, written out. Its content is the [fix]:
 * the proof for [Cons a l] is built from the proof for [l], and following
 * [l] down to [Nil] is what terminates.
 *)
Definition induction
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

(* [Product]'s scope is opened for the [(a, b)] of [pop], [zip], [unzip],
 * [partition] and [split_at], whose results are pairs.
 *)
Local Open Scope jwa_product_scope.

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
  | []      => NatWithZero.Zero
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
  | a :: l' => Some (a, l')
  end.

(* [forall {A : Type} {B : Type} . List A -> List B -> List (A * B)] *)
Fixpoint zip {A : Type} {B : Type} (l1 : List A) (l2 : List B)
  : List (A * B) :=
  match l1, l2 with
  | a :: l1', b :: l2' => (a, b) :: zip l1' l2'
  | [], []             => []
  | [], _ :: _         => []
  | _ :: _, []         => []
  end.

(* The two projections mapped over the list, so the laws of [map] carry
 * over.
 *)
(* [forall {A : Type} {B : Type} . List (A * B) -> List A * List B] *)
Definition unzip := fun {A : Type} {B : Type} (l : List (A * B)) .
  (map Product.first l, map Product.second l).

(* Splits a list into the elements [p] accepts and the ones it rejects, in
 * one pass; the recursive result is opened by a [match] so both halves
 * are extended in place.
 *)
(* [forall {A : Type} . (A -> Bool) -> List A -> List A * List A] *)
Fixpoint partition {A : Type} (p : A -> Bool) (l : List A)
  : List A * List A :=
  match l with
  | []      => ([], [])
  | a :: l' =>
      match partition p l' with
      | (yes, no) =>
          match p a with
          | true  => (a :: yes, no)
          | false => (yes, a :: no)
          end
      end
  end.

(* Indexing from [NatWithZero.Zero]: [nth l i] is the element [i] places from the front,
 * [None] past the end. Recursion is on the list; the index is peeled by
 * one alongside, [NatWithZero.Positive Nat.One] being the last step before [NatWithZero.Zero].
 *)
(* [forall {A : Type} . List A -> NatWithZero -> Option A] *)
Fixpoint nth {A : Type} (l : List A) (i : NatWithZero) : Option A :=
  match l with
  | []      => None
  | a :: l' =>
      match i with
      | NatWithZero.Zero                    => Some a
      | NatWithZero.Positive Nat.One            => nth l' NatWithZero.Zero
      | NatWithZero.Positive (Nat.Successor i') => nth l' (NatWithZero.Positive i')
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
      | NatWithZero.Zero                    => []
      | NatWithZero.Positive Nat.One            => a :: []
      | NatWithZero.Positive (Nat.Successor n') => a :: take (NatWithZero.Positive n') l'
      end
  end.

(* [forall {A : Type} . NatWithZero -> List A -> List A] *)
Fixpoint drop {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' =>
      match n with
      | NatWithZero.Zero                    => a :: l'
      | NatWithZero.Positive Nat.One            => l'
      | NatWithZero.Positive (Nat.Successor n') => drop (NatWithZero.Positive n') l'
      end
  end.

(* [forall {A : Type} . NatWithZero -> List A -> List A * List A] *)
Definition split_at := fun {A : Type} (n : NatWithZero) (l : List A) .
  (take n l, drop n l).

(* [replicate n a] is [a] repeated [n] times. A count of [NatWithZero.Zero] gives [Nil];
 * a positive count recurses on its [Nat], one element per step, since a
 * [NatWithZero] has no step of its own to recurse on.
 *)
(* [forall {A : Type} . Nat -> A -> List A] *)
Fixpoint replicate_positive {A : Type} (k : Nat) (a : A) : List A :=
  match k with
  | Nat.One          => a :: []
  | Nat.Successor k' => a :: replicate_positive k' a
  end.

(* [forall {A : Type} . NatWithZero -> A -> List A] *)
Definition replicate := fun {A : Type} (n : NatWithZero) (a : A) .
  match n with
  | NatWithZero.Zero       => []
  | NatWithZero.Positive k => replicate_positive k a
  end.

(* [List NatWithZero -> NatWithZero] *)
Definition sum := fun (l : List NatWithZero) . fold_right NatWithZero.add NatWithZero.Zero l.

(* [List NatWithZero -> NatWithZero] *)
Definition product := fun (l : List NatWithZero) .
  fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) l.

(* [count p l] is how many elements [p] answers [true] on. *)
(* [forall {A : Type} . (A -> Bool) -> List A -> NatWithZero] *)
Fixpoint count {A : Type} (p : A -> Bool) (l : List A) : NatWithZero :=
  match l with
  | []      => NatWithZero.Zero
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
  | Nat.One          => NatWithZero.Zero :: []
  | Nat.Successor p' => append (range_positive p') (NatWithZero.Positive p')
  end.

(* [NatWithZero -> List NatWithZero] *)
Definition range_from_zero := fun (n : NatWithZero) .
  match n with
  | NatWithZero.Zero       => []
  | NatWithZero.Positive p => range_positive p
  end.

(* [range start stop] counts up from [start] and stops before [stop]: it
 * shifts as many numbers as separate the two. The subtraction is truncated,
 * so a [stop] at or below [start] leaves nothing to shift and the range is
 * empty.
 *)
(* [NatWithZero -> NatWithZero -> List NatWithZero] *)
Definition range := fun (start : NatWithZero) (stop : NatWithZero) .
  map (NatWithZero.add start) (range_from_zero (NatWithZero.saturating_sub stop start)).

(* [range_inclusive start stop] reaches [stop] itself, so it is [range] run
 * one further.
 *)
(* [NatWithZero -> NatWithZero -> List NatWithZero] *)
Definition range_inclusive := fun (start : NatWithZero) (stop : NatWithZero) .
  range start (NatWithZero.inc stop).

(* [le a b] answers whether [a] may precede [b]; it is the comparison
 * [insert] and [insertion_sort] take. The maximum of a list is the later of
 * its head and the maximum of its tail, so the empty list has none.
 *)
(* [forall {A : Type} . (A -> A -> Bool) -> List A -> Option A] *)
Fixpoint maximum_of {A : Type} (le : A -> A -> Bool) (l : List A) : Option A :=
  match l with
  | []      => None
  | a :: l' =>
      match maximum_of le l' with
      | None   => Some a
      | Some m =>
          match le a m with
          | true  => Some m
          | false => Some a
          end
      end
  end.

(* [forall {A : Type} . (A -> A -> Bool) -> List A -> Option A] *)
Fixpoint minimum_of {A : Type} (le : A -> A -> Bool) (l : List A) : Option A :=
  match l with
  | []      => None
  | a :: l' =>
      match minimum_of le l' with
      | None   => Some a
      | Some m =>
          match le a m with
          | true  => Some a
          | false => Some m
          end
      end
  end.

(* A law of the type itself rather than of any operation, so it belongs to
 * no topic below.
 *)
Theorem distinctness
  : forall {A : Type} (a : A) (l : List A) . ~ (a :: l = []).
Proof.
  intros A a l.
  simpl (~ _) in |- *.
  intro e.
  ex e quodlibet.
Qed.

Module concatenation. (* concatenation *)

(* concatenation.associativity *)
Theorem associativity
  : forall {A : Type} (l1 : List A) (l2 : List A) (l3 : List A) .
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

Module left. (* concatenation.left *)

(* concatenation.left.identity *)
Lemma identity : forall {A : Type} (l : List A) . [] ++ l = l.
Proof.
  intros A l.
  simpl in |- *.
  quod idem est.
Qed.

End left. (* concatenation.left *)

Module right. (* concatenation.right *)

(* concatenation.right.identity *)
Lemma identity : forall {A : Type} (l : List A) . l ++ [] = l.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

End right. (* concatenation.right *)

(* concatenation.identity *)
Theorem identity
  : forall {A : Type} (l : List A) . ([] ++ l = l) /\ (l ++ [] = l).
Proof.
  intros A l.
  divide et impera.
  - ipso (concatenation.left.identity  l).
  - ipso (concatenation.right.identity l).
Qed.

(* concatenation.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (l1 : List A) (l2 : List A) .
      l1 ++ l2 = fold_right Cons l2 l1.
Proof.
  intros A l1 l2.
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    leibniz (NatWithZero.increment.specification ((|| l1' ||) + (|| l2 ||)))
      in |- *.
    leibniz (NatWithZero.increment.specification (|| l1' ||))
      in |- *.
    leibniz (NatWithZero.addition.associativity (NatWithZero.Positive Nat.One) (|| l1' ||) (|| l2 ||))
      in |- *.
    quod idem est.
Qed.

End over. (* length.additivity.over *)

End additivity. (* length.additivity *)

(* length.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (l : List A) .
      (|| l ||)
      = fold_right (fun (_ : A) (n : NatWithZero) . (++ n))
                   NatWithZero.Zero
                   l.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

End length. (* length *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall {A : Type} (l : List A) . map (fun a . a) l = l.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

(* mapping.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C)
      (l : List A) .
    map g (map f l) = map (fun a . g (f a)) l.
Proof.
  intros A B C f g l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

Module distributivity. (* mapping.distributivity *)

Module over. (* mapping.distributivity.over *)

(* mapping.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} {B : Type} (f : A -> B) (l1 : List A) (l2 : List A) .
      map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros A B f l1 l2.
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro g.
    ipso g.
  - simpl in |- *.
    intro h.
    match h with | e | h' end.
    + lemma side : &f &a = &f &b.
      {
        leibniz e in |- *.
        quod idem est.
      }
      ipso (disjoin &side, _).
    + ipso (disjoin _, (&IH &h')).
Qed.

(* mapping.preservation.of.length *)
Theorem length
  : forall {A : Type} {B : Type} (f : A -> B) (l : List A) .
      (|| map f l ||) = (|| l ||).
Proof.
  intros A B f l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

End of. (* mapping.preservation.of *)

End preservation. (* mapping.preservation *)

Module membership. (* mapping.membership *)

(* An element of [map f l] is the image of an element of [l]. The forward
 * half of [preservation.of.membership] is the other direction.
 *)
(* mapping.membership.specification *)
Theorem specification
  : forall {A : Type} {B : Type} (f : A -> B) (b : B) (l : List A) .
      map f l contains_member b
      <-> forsome (a : A) . l contains_member a /\ b = f a.
Proof.
  intros A B f b l.
  divide et impera.
  - match l with | | a l' by IH end per List.induction.
    + simpl in |- *.
      intro g.
      ex g quodlibet.
    + simpl in |- *.
      intro h.
      match h with | e | h' end.
      * exists &a.
        ipso (conjoin (disjoin (Identity.reflexivity &a), _), &e).
      * let proof w := IH h'.
        match w with | a' c end.
        match c with | m e end.
        exists &a'.
        ipso (conjoin (disjoin _, &m), &e).
  - intro w.
    match w with | a c end.
    match c with | m e end.
    leibniz e in |- *.
    ipso (preservation.of.membership f a l m).
Qed.

End membership. (* mapping.membership *)

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
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  simpl (~ _) in |- *.
  simpl in |- *.
  intro f.
  ipso f.
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso (Disjunction.R h).
  - simpl in |- *.
    intro h.
    match h with | e | h' end.
    + ipso (Disjunction.L (Disjunction.L e)).
    + match (IH h') with | h1 | h2 end.
      * ipso (Disjunction.L (Disjunction.R h1)).
      * ipso (Disjunction.R h2).
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    match h with | f | h2 end.
    + ex f quodlibet.
    + ipso h2.
  - simpl in |- *.
    intro h.
    match h with | h1 | h2 end.
    + match h1 with | e | h1' end.
      * ipso (Disjunction.L e).
      * ipso (disjoin _, (&IH (disjoin &h1', _))).
    + ipso (disjoin _, (&IH (disjoin _, &h2))).
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
  divide et impera.
  - ipso (@membership.forward.distributivity.over.concatenation  A a l1 l2).
  - ipso (@membership.backward.distributivity.over.concatenation A a l1 l2).
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    leibniz (concatenation.right.identity (reverse &l2)) in |- *.
    quod idem est.
  - simpl in |- *.
    simpl append in |- *.
    leibniz IH in |- *.
    leibniz (concatenation.associativity (reverse &l2) (reverse &l1') (&a :: [])) in |- *.
    quod idem est.
Qed.

End over. (* reversal.antidistributivity.over *)

End antidistributivity. (* reversal.antidistributivity *)

(* reversal.involution *)
Theorem involution
  : forall {A : Type} (l : List A) . reverse (reverse l) = l.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    simpl append in |- *.
    leibniz (reversal.antidistributivity.over.concatenation (reverse &l') (&a :: [])) in |- *.
    simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro f.
    ipso f.
  - simpl in |- *.
    intro h.
    match (membership.forward.distributivity.over.concatenation h) with | h1 | h2 end.
    + ipso (disjoin _, (&IH &h1)).
    + simpl in h2.
      match h2 with | e | f end.
      * ipso (Disjunction.L e).
      * ex f quodlibet.
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro f.
    ipso f.
  - simpl in |- *.
    intro h.
    lemma facto : reverse &l' contains_member &a \/ (&b :: []) contains_member &a.
    {
      match h with | e | h' end.
      + lemma singleton : (&b :: []) contains_member &a.
        {
          simpl in |- *.
          ipso (Disjunction.L e).
        }
        ipso (disjoin _, &singleton).
      + ipso (disjoin (&IH &h'), _).
    }
    ipso (membership.backward.distributivity.over.concatenation &facto).
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
  divide et impera.
  - ipso (@reversal.forward.preservation.of.membership  A a l).
  - ipso (@reversal.backward.preservation.of.membership A a l).
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
  simpl append in |- *.
  quod idem est.
Qed.

(* appending.length *)
Theorem length
  : forall {A : Type} (l : List A) (a : A) . (|| append l a ||) = ++ (|| l ||).
Proof.
  intros A l a.
  leibniz (appending.specification l a) in |- *.
  leibniz (length.additivity.over.concatenation l (a :: [])) in |- *.
  simpl in |- *.
  leibniz (NatWithZero.increment.specification (|| l ||)) in |- *.
  leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l ||)) in |- *.
  quod idem est.
Qed.

(* appending.membership *)
Theorem membership
  : forall {A : Type} (l : List A) (a : A) (b : A) .
      append l a contains_member b <-> b = a \/ l contains_member b.
Proof.
  intros A l a b.
  leibniz (appending.specification l a) in |- *.
  divide et impera.
  - intro h.
    match (membership.forward.distributivity.over.concatenation h) with | h1 | h2 end.
    + ipso (Disjunction.R h1).
    + simpl in h2.
      match h2 with | e | f end.
      * ipso (Disjunction.L e).
      * ex f quodlibet.
  - intro h.
    lemma facto : &l contains_member &b \/ (&a :: []) contains_member &b.
    {
      match h with | e | h' end.
      + lemma singleton : (&a :: []) contains_member &b.
        {
          simpl in |- *.
          ipso (Disjunction.L e).
        }
        ipso (disjoin _, &singleton).
      + ipso (Disjunction.L h').
    }
    ipso (membership.backward.distributivity.over.concatenation &facto).
Qed.

(* appending.reversal *)
Theorem reversal
  : forall {A : Type} (l : List A) (a : A) . reverse (append l a) = a :: reverse l.
Proof.
  intros A l a.
  leibniz (appending.specification l a) in |- *.
  leibniz (reversal.antidistributivity.over.concatenation l (a :: [])) in |- *.
  simpl in |- *.
  quod idem est.
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match (p b) with | | end.
    + simpl in |- *.
      leibniz IH in |- *.
      quod idem est.
    + ipso IH.
Qed.

End over. (* filtering.distributivity.over *)

End distributivity. (* filtering.distributivity *)

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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

Module forward. (* filtering.forward *)

(* filtering.forward.specification *)
Lemma specification
  : forall {A : Type} {p : A -> Bool} {a : A} {l : List A} .
      filter p l contains_member a -> l contains_member a /\ p a = true.
Proof.
  intros A p a l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro f.
    ex f quodlibet.
  - simpl in |- *.
    match (p b) with | | end |- pb.
    + simpl in |- *.
      intro h.
      match h with | e | h' end.
      * divide et impera.
        -- ipso (Disjunction.L e).
        -- leibniz e in |- *.
           ipso pb.
      * match (IH h') with | hl pa end.
        divide et impera.
        -- ipso (Disjunction.R hl).
        -- ipso pa.
    + intro h'.
      match (IH h') with | hl pa end.
      divide et impera.
      * ipso (Disjunction.R hl).
      * ipso pa.
Qed.

End forward. (* filtering.forward *)

Module backward. (* filtering.backward *)

(* filtering.backward.specification *)
Lemma specification
  : forall {A : Type} {p : A -> Bool} {a : A} {l : List A} .
      l contains_member a /\ p a = true -> filter p l contains_member a.
Proof.
  intros A p a l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    match h with | f _ end.
    ex f quodlibet.
  - simpl in |- *.
    intro h.
    match h with | h1 pa end.
    match h1 with | e | h' end.
    + leibniz e in pa.
      leibniz pa in |- *.
      simpl in |- *.
      ipso (Disjunction.L e).
    + match (p b) with | | end.
      * simpl in |- *.
        ipso (disjoin _, (&IH (conjoin &h', &pa))).
      * ipso (&IH (conjoin &h', &pa)).
Qed.

End backward. (* filtering.backward *)

(* filtering.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (a : A) (l : List A) .
      filter p l contains_member a <-> l contains_member a /\ p a = true.
Proof.
  intros A p a l.
  divide et impera.
  - ipso (@filtering.forward.specification  A p a l).
  - ipso (@filtering.backward.specification A p a l).
Qed.

End filtering. (* filtering *)

Module quantification. (* quantification *)

Module all. (* quantification.all *)

Module forward. (* quantification.all.forward *)

Module distributivity. (* quantification.all.forward.distributivity *)

Module over. (* quantification.all.forward.distributivity.over *)

(* quantification.all.forward.distributivity.over.concatenation *)
Lemma concatenation
  : forall {A : Type} {P : A -> Prop} {l1 : List A} {l2 : List A} .
      All P (l1 ++ l2) -> All P l1 /\ All P l2.
Proof.
  intros A P l1 l2.
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    divide et impera.
    + ipso I.
    + ipso h.
  - simpl in |- *.
    intro h.
    match h with | pb h' end.
    match (IH h') with | h1 h2 end.
    divide et impera.
    + divide et impera.
      * ipso pb.
      * ipso h1.
    + ipso h2.
Qed.

End over. (* quantification.all.forward.distributivity.over *)

End distributivity. (* quantification.all.forward.distributivity *)

(* quantification.all.forward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      All P l -> forall (a : A) . l contains_member a -> P a.
Proof.
  intros A P l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intros v a f.
    ex f quodlibet.
  - simpl in |- *.
    intro h.
    match h with | pb h' end.
    intros a ha.
    match ha with | e | ha' end.
    + leibniz e in |- *.
      ipso pb.
    + ipso (&IH &h' &a &ha').
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    match h with | _ h2 end.
    ipso h2.
  - simpl in |- *.
    intro h.
    match h with | h1 h2 end.
    match h1 with | pb h1' end.
    divide et impera.
    + ipso pb.
    + ipso (&IH (conjoin &h1', &h2)).
Qed.

End over. (* quantification.all.backward.distributivity.over *)

End distributivity. (* quantification.all.backward.distributivity *)

(* quantification.all.backward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      (forall (a : A) . l contains_member a -> P a) -> All P l.
Proof.
  intros A P l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso I.
  - simpl in |- *.
    intro h.
    divide et impera.
    + ipso (&h &b (disjoin (Identity.reflexivity &b), _)).
    + lemma members : forall (a : &A) . &l' contains_member a -> &P a.
      {
        intros a ha.
        ipso (&h &a (disjoin _, &ha)).
      }
      ipso (&IH &members).
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
  divide et impera.
  - ipso (@quantification.all.forward.distributivity.over.concatenation  A P l1 l2).
  - ipso (@quantification.all.backward.distributivity.over.concatenation A P l1 l2).
Qed.

End over. (* quantification.all.distributivity.over *)

End distributivity. (* quantification.all.distributivity *)

(* quantification.all.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      All P l <-> (forall (a : A) . l contains_member a -> P a).
Proof.
  intros A P l.
  divide et impera.
  - ipso (@quantification.all.forward.specification  A P l).
  - ipso (@quantification.all.backward.specification A P l).
Qed.

(* quantification.all.monotonicity *)
Lemma monotonicity
  : forall {A : Type} {P : A -> Prop} {Q : A -> Prop} {l : List A} .
      (forall (a : A) . P a -> Q a) -> All P l -> All Q l.
Proof.
  intros A P Q l h.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro v.
    ipso v.
  - simpl in |- *.
    intro c.
    match c with | pb all' end.
    ipso (conjoin (h b pb), (IH all')).
Qed.

(* quantification.all.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      All P l = fold_right (fun (a : A) (rest : Prop) . P a /\ rest) Verum l.
Proof.
  intros A P l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso (Disjunction.R h).
  - simpl in |- *.
    intro h.
    match h with | pb | h' end.
    + ipso (Disjunction.L (Disjunction.L pb)).
    + match (IH h') with | h1 | h2 end.
      * ipso (Disjunction.L (Disjunction.R h1)).
      * ipso (Disjunction.R h2).
Qed.

End over. (* quantification.any.forward.distributivity.over *)

End distributivity. (* quantification.any.forward.distributivity *)

(* quantification.any.forward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      Any P l -> forsome (a : A) . l contains_member a /\ P a.
Proof.
  intros A P l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro f.
    ex f quodlibet.
  - simpl in |- *.
    intro h.
    match h with | pb | h' end.
    + exists b.
      divide et impera.
      * ipso (Disjunction.L (Identity.reflexivity b)).
      * ipso pb.
    + match (IH h') with | a ha end.
      match ha with | ha' pa end.
      exists a.
      divide et impera.
      * ipso (Disjunction.R ha').
      * ipso pa.
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
  match l1 with | | b l1' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    match h with | f | h2 end.
    + ex f quodlibet.
    + ipso h2.
  - simpl in |- *.
    intro h.
    match h with | h1 | h2 end.
    + match h1 with | pb | h1' end.
      * ipso (Disjunction.L pb).
      * ipso (disjoin _, (&IH (disjoin &h1', _))).
    + ipso (disjoin _, (&IH (disjoin _, &h2))).
Qed.

End over. (* quantification.any.backward.distributivity.over *)

End distributivity. (* quantification.any.backward.distributivity *)

(* quantification.any.backward.specification *)
Lemma specification
  : forall {A : Type} {P : A -> Prop} {l : List A} .
      (forsome (a : A) . l contains_member a /\ P a) -> Any P l.
Proof.
  intros A P l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    match h with | a ha end.
    match ha with | f _ end.
    ex f quodlibet.
  - simpl in |- *.
    intro h.
    match h with | a ha end.
    match ha with | ha' pa end.
    match ha' with | e | ha'' end.
    + leibniz e in pa.
      ipso (Disjunction.L pa).
    + lemma witness : forsome (x : &A) . &l' contains_member x /\ &P x.
      {
        exists &a.
        ipso (conjoin &ha'', &pa).
      }
      ipso (disjoin _, (&IH &witness)).
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
  divide et impera.
  - ipso (@quantification.any.forward.distributivity.over.concatenation  A P l1 l2).
  - ipso (@quantification.any.backward.distributivity.over.concatenation A P l1 l2).
Qed.

End over. (* quantification.any.distributivity.over *)

End distributivity. (* quantification.any.distributivity *)

(* quantification.any.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      Any P l <-> (forsome (a : A) . l contains_member a /\ P a).
Proof.
  intros A P l.
  divide et impera.
  - ipso (@quantification.any.forward.specification  A P l).
  - ipso (@quantification.any.backward.specification A P l).
Qed.

(* quantification.any.catamorphism *)
Theorem catamorphism
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      Any P l = fold_right (fun (a : A) (rest : Prop) . P a \/ rest) Falsum l.
Proof.
  intros A P l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

End any. (* quantification.any *)

End quantification. (* quantification *)

Module head. (* head *)

Module forward. (* head.forward *)

(* head.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      head l = Some a -> forsome (l' : List A) . l = a :: l'.
Proof.
  intros A a l.
  match l with | | b rest end.
  - simpl in |- *.
    intro e.
    ex e quodlibet.
  - simpl in |- *.
    intro e.
    let proof e' := Option.some.injectivity e.
    exists rest.
    leibniz e' in |- *.
    quod idem est.
Qed.

End forward. (* head.forward *)

Module backward. (* head.backward *)

(* head.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      (forsome (l' : List A) . l = a :: l') -> head l = Some a.
Proof.
  intros A a l.
  intro h.
  match h with | l' e end.
  leibniz e in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End backward. (* head.backward *)

(* head.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l : List A) .
      head l = Some a <-> (forsome (l' : List A) . l = a :: l').
Proof.
  intros A a l.
  divide et impera.
  - ipso (@head.forward.specification  A a l).
  - ipso (@head.backward.specification A a l).
Qed.

End head. (* head *)

Module tail. (* tail *)

Module forward. (* tail.forward *)

(* tail.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      tail l = Some l' -> forsome (a : A) . l = a :: l'.
Proof.
  intros A l l'.
  match l with | | b rest end.
  - simpl in |- *.
    intro e.
    ex e quodlibet.
  - simpl in |- *.
    intro e.
    let proof e' := Option.some.injectivity e.
    exists b.
    leibniz e' in |- *.
    quod idem est.
Qed.

End forward. (* tail.forward *)

Module backward. (* tail.backward *)

(* tail.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      (forsome (a : A) . l = a :: l') -> tail l = Some l'.
Proof.
  intros A l l'.
  intro h.
  match h with | a e end.
  leibniz e in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End backward. (* tail.backward *)

(* tail.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (l' : List A) .
      tail l = Some l' <-> (forsome (a : A) . l = a :: l').
Proof.
  intros A l l'.
  divide et impera.
  - ipso (@tail.forward.specification  A l l').
  - ipso (@tail.backward.specification A l l').
Qed.

End tail. (* tail *)

Module last. (* last *)

Module forward. (* last.forward *)

(* last.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      last l = Some a -> forsome (l' : List A) . l = append l' a.
Proof.
  intros A a l.
  simpl last in |- *.
  intro h.
  match (head.forward.specification h) with | r e end.
  exists (reverse r).
  let proof e' := Identity.congruence reverse e.
  leibniz (reversal.involution &l) in e'.
  simpl in e'.
  ipso e'.
Qed.

End forward. (* last.forward *)

Module backward. (* last.backward *)

(* last.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l : List A} .
      (forsome (l' : List A) . l = append l' a) -> last l = Some a.
Proof.
  intros A a l.
  intro h.
  match h with | l' e end.
  simpl last in |- *.
  leibniz e in |- *.
  leibniz (appending.reversal &l' &a) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End backward. (* last.backward *)

(* last.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l : List A) .
      last l = Some a <-> (forsome (l' : List A) . l = append l' a).
Proof.
  intros A a l.
  divide et impera.
  - ipso (@last.forward.specification  A a l).
  - ipso (@last.backward.specification A a l).
Qed.

End last. (* last *)

Module initial. (* initial *)

Module forward. (* initial.forward *)

(* initial.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      initial l = Some l' -> forsome (a : A) . l = append l' a.
Proof.
  intros A l l'.
  simpl initial in |- *.
  match (reverse l) with | | b r end |- er.
  - simpl in |- *.
    intro h.
    ex h quodlibet.
  - simpl in |- *.
    intro h.
    let proof e' := Option.some.injectivity h.
    exists b.
    let proof er' := Identity.congruence reverse er.
    leibniz (reversal.involution &l) in er'.
    simpl in er'.
    leibniz e' in er'.
    ipso er'.
Qed.

End forward. (* initial.forward *)

Module backward. (* initial.backward *)

(* initial.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {l' : List A} .
      (forsome (a : A) . l = append l' a) -> initial l = Some l'.
Proof.
  intros A l l'.
  intro h.
  match h with | a e end.
  simpl initial in |- *.
  leibniz e in |- *.
  leibniz (appending.reversal &l' &a) in |- *.
  simpl in |- *.
  leibniz (reversal.involution &l') in |- *.
  quod idem est.
Qed.

End backward. (* initial.backward *)

(* initial.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (l' : List A) .
      initial l = Some l' <-> (forsome (a : A) . l = append l' a).
Proof.
  intros A l l'.
  divide et impera.
  - ipso (@initial.forward.specification  A l l').
  - ipso (@initial.backward.specification A l l').
Qed.

End initial. (* initial *)

Module popping. (* popping *)

Module forward. (* popping.forward *)

(* popping.forward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l' : List A} {l : List A} .
      pop l = Some (a, l') -> l = a :: l'.
Proof.
  intros A a l' l.
  match l with | | b rest end.
  - simpl in |- *.
    intro e.
    ex e quodlibet.
  - simpl in |- *.
    intro e.
    let proof e' := Option.some.injectivity e.
    let proof e'' := Product.introduction.injectivity e'.
    match e'' with | eb erest end.
    leibniz eb in |- *.
    leibniz erest in |- *.
    quod idem est.
Qed.

End forward. (* popping.forward *)

Module backward. (* popping.backward *)

(* popping.backward.specification *)
Lemma specification
  : forall {A : Type} {a : A} {l' : List A} {l : List A} .
      l = a :: l' -> pop l = Some (a, l').
Proof.
  intros A a l' l e.
  leibniz e in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End backward. (* popping.backward *)

(* [pop] answers [Some (a , l')] exactly on [Cons a l']. *)
(* popping.specification *)
Theorem specification
  : forall {A : Type} (a : A) (l' : List A) (l : List A) .
      pop l = Some (a, l') <-> l = a :: l'.
Proof.
  intros A a l' l.
  divide et impera.
  - ipso (@popping.forward.specification  A a l' l).
  - ipso (@popping.backward.specification A a l' l).
Qed.

(* Projecting a [pop] gives back [head] and [tail]. *)

Module head. (* popping.head *)

(* popping.head.projection *)
Theorem projection
  : forall {A : Type} (l : List A) . Option.map Product.first (pop l) = head l.
Proof.
  intros A l.
  match l with | | a l' end; simpl in |- *; quod idem est.
Qed.

End head. (* popping.head *)

Module tail. (* popping.tail *)

(* popping.tail.projection *)
Theorem projection
  : forall {A : Type} (l : List A) . Option.map Product.second (pop l) = tail l.
Proof.
  intros A l.
  match l with | | a l' end; simpl in |- *; quod idem est.
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
  match l with | | p l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    simpl unzip in IH.
    simpl in IH.
    leibniz IH in |- *.
    leibniz <- (Product.introduction.surjectivity p) in |- *.
    quod idem est.
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
  match l1 with | | a l1' by IH end per List.induction.
  - intros l2.
    match l2 with | | b l2' end.
    + simpl in |- *.
      simpl Comparable.min, NatWithZero.compare in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (NatWithZero.minimum.left.annihilation (++ (|| l2' ||))) in |- *.
      quod idem est.
  - intros l2.
    match l2 with | | b l2' end.
    + simpl in |- *.
      leibniz (NatWithZero.minimum.right.annihilation (++ (|| l1' ||))) in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz (IH l2') in |- *.
      leibniz (NatWithZero.increment.specification
                 (NatWithZero.min (|| l1' ||) (|| l2' ||))) in |- *.
      leibniz (NatWithZero.minimum.left.distributivity.of.addition
                 (NatWithZero.Positive Nat.One) (|| l1' ||) (|| l2' ||)) in |- *.
      leibniz (NatWithZero.increment.specification (|| l1' ||)) in |- *.
      leibniz (NatWithZero.increment.specification (|| l2' ||)) in |- *.
      quod idem est.
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
      (|| l1 ||) = (|| l2 ||) -> unzip (zip l1 l2) = (l1, l2).
Proof.
  intros A B l1.
  match l1 with | | a l1' by IH end per List.induction.
  - intros l2 e.
    match l2 with | | b l2' end.
    + simpl unzip in |- *.
      simpl in |- *.
      quod idem est.
    + simpl in e.
      let proof e' := Identity.symmetry e.
      leibniz (NatWithZero.increment.specification (|| l2' ||)) in e'.
      leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l2' ||)) in e'.
      let proof h := NatWithZero.addition.right.identity.absence (|| l2' ||) Nat.One.
      simpl (~ _) in h.
      modus ponens h, e' |- f.
      ex f quodlibet.
  - intros l2 e.
    match l2 with | | b l2' end.
    + simpl in e.
      leibniz (NatWithZero.increment.specification (|| l1' ||)) in e.
      leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l1' ||)) in e.
      let proof h := NatWithZero.addition.right.identity.absence (|| l1' ||) Nat.One.
      simpl (~ _) in h.
      modus ponens h, e |- f.
      ex f quodlibet.
    + simpl in e.
      leibniz (NatWithZero.increment.specification (|| l1' ||)) in e.
      leibniz (NatWithZero.increment.specification (|| l2' ||)) in e.
      let proof e' := NatWithZero.addition.left.cancellation e.
      let proof IH' := IH l2' e'.
      simpl unzip in IH'.
      let proof e'' := Product.introduction.injectivity IH'.
      match e'' with | e1 e2 end.
      simpl unzip in |- *.
      simpl in |- *.
      leibniz e1 in |- *.
      leibniz e2 in |- *.
      quod idem est.
Qed.

End of. (* unzipping.inversion.of *)

End inversion. (* unzipping.inversion *)

End unzipping. (* unzipping *)

Module partitioning. (* partitioning *)

(* partitioning.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      partition p l
      = (filter p l, filter (fun (a : A) . ! p a) l).
Proof.
  intros A p l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    match (p a) with | | end |- pa; simpl in |- *; quod idem est.
Qed.

End partitioning. (* partitioning *)

(* The last law stated about a pair; nothing below spells one. *)
Local Close Scope jwa_product_scope.

Module indexing. (* indexing *)

(* [nth] answers exactly for the indices below the length. Each step of the
 * index is one step of the list, so the halves lift [IH] through
 * [NatWithZero.Positive Nat.One] added on both sides of the order.
 *)

Module forward. (* indexing.forward *)

(* indexing.forward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {i : NatWithZero} .
      (forsome (a : A) . nth l i = Some a) -> i < (|| l ||).
Proof.
  intros A l.
  match l with | | b l' by IH end per List.induction.
  - intros i h.
    match h with | a e end.
    simpl in e.
    ex e quodlibet.
  - intros i h.
    match i with | | i' end.
    + simpl in |- *.
      leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
      leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l' ||)) in |- *.
      ipso (NatWithZero.addition.right.order.positivity (|| l' ||) Nat.One).
    + match i' with | | i'' end.
      * simpl in h.
        let proof lt := IH NatWithZero.Zero h.
        simpl in |- *.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
        ipso (NatWithZero.addition.order.strict.monotonicity (NatWithZero.Positive Nat.One) NatWithZero.Zero (|| l' ||) lt).
      * simpl in h.
        let proof lt := IH (NatWithZero.Positive i'') h.
        simpl in |- *.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
        ipso (NatWithZero.addition.order.strict.monotonicity
                 (NatWithZero.Positive Nat.One) (NatWithZero.Positive i'') (|| l' ||) lt).
Qed.

End forward. (* indexing.forward *)

Module backward. (* indexing.backward *)

(* indexing.backward.specification *)
Lemma specification
  : forall {A : Type} {l : List A} {i : NatWithZero} .
      i < (|| l ||) -> forsome (a : A) . nth l i = Some a.
Proof.
  intros A l.
  match l with | | b l' by IH end per List.induction.
  - intros i h.
    simpl in h.
    simpl NatWithZero.LessThan in h.
    match h with | k e end.
    let proof r := NatWithZero.addition.right.identity.absence i k.
    simpl (~ _) in r.
    modus ponens r, e |- f.
    ex f quodlibet.
  - intros i h.
    match i with | | i' end.
    + simpl in |- *.
      exists b.
      quod idem est.
    + match i' with | | i'' end.
      * simpl in h.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in h.
        let proof lt := NatWithZero.addition.order.strict.cancellation (NatWithZero.Positive Nat.One) NatWithZero.Zero (|| l' ||) h.
        simpl in |- *.
        ipso (IH NatWithZero.Zero lt).
      * simpl in h.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in h.
        let proof lt := NatWithZero.addition.order.strict.cancellation
                      (NatWithZero.Positive Nat.One) (NatWithZero.Positive i'') (|| l' ||) h.
        simpl in |- *.
        ipso (IH (NatWithZero.Positive i'') lt).
Qed.

End backward. (* indexing.backward *)

(* indexing.specification *)
Theorem specification
  : forall {A : Type} (l : List A) (i : NatWithZero) .
      (forsome (a : A) . nth l i = Some a) <-> i < (|| l ||).
Proof.
  intros A l i.
  divide et impera.
  - ipso (@indexing.forward.specification  A l i).
  - ipso (@indexing.backward.specification A l i).
Qed.

End indexing. (* indexing *)

Module splitting. (* splitting *)

(* splitting.decomposition *)
Theorem decomposition
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      take n l ++ drop n l = l.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - intros n.
    simpl in |- *.
    quod idem est.
  - intros n.
    match n with | | n' end.
    + simpl in |- *.
      quod idem est.
    + match n' with | | n'' end.
      * simpl in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (IH (NatWithZero.Positive n'')) in |- *.
        quod idem est.
Qed.

End splitting. (* splitting *)

Module taking. (* taking *)

(* taking.length *)
Theorem length
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      (|| take n l ||) = NatWithZero.min n (|| l ||).
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - intros n.
    simpl in |- *.
    leibniz (NatWithZero.minimum.right.annihilation n) in |- *.
    quod idem est.
  - intros n.
    match n with | | n' end.
    + simpl in |- *.
      leibniz (NatWithZero.minimum.left.annihilation (++ (|| l' ||))) in |- *.
      quod idem est.
    + match n' with | | n'' end.
      * simpl in |- *.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
        leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l' ||)) in |- *.
        modus aequans
          (Comparable.minimum.specification (NatWithZero.Positive Nat.One)
            ((|| l' ||) + NatWithZero.Positive Nat.One)),
          (NatWithZero.addition.right.order.extensivity
            (|| l' ||) (NatWithZero.Positive Nat.One)) |- e.
        leibniz e in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (IH (NatWithZero.Positive n'')) in |- *.
        leibniz (NatWithZero.increment.specification
                  (NatWithZero.min (NatWithZero.Positive n'') (|| l' ||))) in |- *.
        leibniz (NatWithZero.minimum.left.distributivity.of.addition
                  (NatWithZero.Positive Nat.One) (NatWithZero.Positive n'') (|| l' ||)) in |- *.
        lemma facto
          : NatWithZero.min (NatWithZero.Positive (Nat.Successor &n'')) (NatWithZero.Positive Nat.One + (|| &l' ||))
          = NatWithZero.min (NatWithZero.Positive (Nat.Successor &n'')) (++ (|| &l' ||)).
        {
          leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
          quod idem est.
        }
        ipso &facto.
Qed.

End taking. (* taking *)

Module dropping. (* dropping *)

(* dropping.length *)
Theorem length
  : forall {A : Type} (l : List A) (n : NatWithZero) .
      (|| drop n l ||) = NatWithZero.saturating_sub (|| l ||) n.
Proof.
  intros A l.
  match l with | | a l' by IH end per List.induction.
  - intros n.
    simpl in |- *.
    quod idem est.
  - intros n.
    match n with | | n' end.
    + simpl in |- *.
      leibniz (NatWithZero.subtraction.saturating.right.identity (++ (|| l' ||))) in |- *.
      quod idem est.
    + match n' with | | n'' end.
      * simpl in |- *.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
        leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (|| l' ||)) in |- *.
        leibniz (NatWithZero.subtraction.saturating.inversion.of.addition
                   (|| l' ||) (NatWithZero.Positive Nat.One)) in |- *.
        quod idem est.
      * simpl in |- *.
        leibniz (IH (NatWithZero.Positive n'')) in |- *.
        leibniz (NatWithZero.increment.specification (|| l' ||)) in |- *.
        lemma facto
          : NatWithZero.saturating_sub (|| &l' ||) (NatWithZero.Positive &n'')
            = NatWithZero.saturating_sub (NatWithZero.Positive Nat.One + (|| &l' ||))
                                         (NatWithZero.Positive Nat.One + NatWithZero.Positive &n'').
        {
          leibniz (NatWithZero.subtraction.saturating.cancellation
                     (NatWithZero.Positive Nat.One) (|| l' ||) (NatWithZero.Positive n'')) in |- *.
          quod idem est.
        }
        ipso &facto.
Qed.

End dropping. (* dropping *)

Module replication. (* replication *)

Module positive. (* replication.positive *)

(* replication.positive.length *)
Lemma length
  : forall {A : Type} (k : Nat) (a : A) . (|| replicate_positive k a ||) = NatWithZero.Positive k.
Proof.
  intros A k a.
  match k with | | k' by IH end per Nat.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    simpl in |- *.
    simpl Nat.inc in |- *.
    quod idem est.
Qed.

End positive. (* replication.positive *)

(* replication.length *)
Theorem length
  : forall {A : Type} (n : NatWithZero) (a : A) . (|| replicate n a ||) = n.
Proof.
  intros A n a.
  match n with | | k end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (replication.positive.length k a).
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
  simpl sum in |- *.
  match l1 with | | a l1' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz IH in |- *.
    leibniz (NatWithZero.addition.associativity
               a (fold_right NatWithZero.add NatWithZero.Zero l1') (fold_right NatWithZero.add NatWithZero.Zero l2))
      in |- *.
    quod idem est.
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
  simpl product in |- *.
  match l1 with | | a l1' by IH end per List.induction.
  - leibniz (concatenation.left.identity l2) in |- *.
    lemma facto
      : fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) &l2
        = NatWithZero.Positive Nat.One
          * fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) &l2.
    {
      leibniz (NatWithZero.multiplication.left.identity
                 (fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) l2))
        in |- *.
      quod idem est.
    }
    ipso &facto.
  - simpl in |- *.
    leibniz IH in |- *.
    leibniz (NatWithZero.multiplication.associativity
               a (fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) l1')
               (fold_right NatWithZero.mul (NatWithZero.Positive Nat.One) l2)) in |- *.
    quod idem est.
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
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match (p a) with | | end.
    + simpl in |- *.
      leibniz IH in |- *.
      quod idem est.
    + ipso IH.
Qed.

Module zero. (* counting.zero *)

(* counting.zero.specification *)
Theorem specification
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      count p l = NatWithZero.Zero <-> All (fun (a : A) . p a = false) l.
Proof.
  intros A p l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    divide et impera.
    + intro e.
      ipso I.
    + intro v.
      quod idem est.
  - simpl in |- *.
    match (p a) with | | end.
    + divide et impera.
      * intro e.
        leibniz (NatWithZero.increment.specification (count p l')) in e.
        leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (count p l')) in e.
        let proof r := NatWithZero.addition.right.identity.absence (count p l') Nat.One.
        simpl (~ _) in r.
        modus ponens r, e |- f.
        ex f quodlibet.
      * intro c.
        match c with | e f end.
        ex e quodlibet.
    + divide et impera.
      * intro e.
        modus aequans IH, e |- all'.
        ipso (conjoin (Identity.reflexivity false), all').
      * intro c.
        match c with | e all' end.
        ipso (modus aequans IH, all').
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro v.
    ipso (conjoin pa, v).
  - simpl in |- *.
    intro c.
    match c with | pb all' end.
    match (le a b) with | | end.
    + simpl in |- *.
      ipso (conjoin pa, (conjoin pb, all')).
    + simpl in |- *.
      ipso (conjoin pb, (IH all')).
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro v.
    ipso (conjoin v, v).
  - simpl in |- *.
    intro s.
    match s with | below sorted' end.
    match (le a b) with | | end |- c.
    + simpl in |- *.
      let proof below_a := quantification.all.monotonicity
                    (fun (x : A) (h : le b x = true) . transitive a b x c h) below.
      ipso (conjoin
               (conjoin c, below_a),
               (conjoin below, sorted')).
    + simpl in |- *.
      let proof t := total a b.
      match t with | ab | ba end.
      * leibniz c in ab.
        ex ab quodlibet.
      * ipso (conjoin
                 (sorting.insertion.preservation.of.all
                    le (fun (x : A) . le b x = true) a l' ba below),
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
  match l with | | c l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso h.
  - simpl in |- *.
    match (le a c) with | | end.
    + simpl in |- *.
      intro h.
      ipso h.
    + simpl in |- *.
      intro h.
      match h with | e | h' end.
      * ipso (Disjunction.R (Disjunction.L e)).
      * modus ponens IH, h' |- h''.
        match h'' with | e | h''' end.
        { ipso (Disjunction.L e). }
        { ipso (Disjunction.R (Disjunction.R h''')). }
Qed.

End forward. (* sorting.insertion.forward *)

Module backward. (* sorting.insertion.backward *)

(* sorting.insertion.backward.membership *)
Lemma membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
      b = a \/ l contains_member b -> insert le a l contains_member b.
Proof.
  intros A le a b l.
  match l with | | c l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso h.
  - simpl in |- *.
    match (le a c) with | | end.
    + simpl in |- *.
      intro h.
      ipso h.
    + simpl in |- *.
      intro h.
      match h with | e | h' end.
      * ipso (Disjunction.R (IH (Disjunction.L e))).
      * match h' with | e | h'' end.
        { ipso (Disjunction.L e). }
        { ipso (Disjunction.R (IH (Disjunction.R h''))). }
Qed.

End backward. (* sorting.insertion.backward *)

(* sorting.insertion.membership *)
Theorem membership
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
      insert le a l contains_member b <-> b = a \/ l contains_member b.
Proof.
  intros A le a b l.
  divide et impera.
  - ipso (@sorting.insertion.forward.membership  A le a b l).
  - ipso (sorting.insertion.backward.membership le a b l).
Qed.

(* sorting.insertion.length *)
Lemma length
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      (|| insert le a l ||) = ++ (|| l ||).
Proof.
  intros A le a l.
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    match (le a b) with | | end.
    + simpl in |- *.
      quod idem est.
    + simpl in |- *.
      leibniz IH in |- *.
      quod idem est.
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
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    ipso I.
  - simpl in |- *.
    ipso (sorting.insertion.sortedness
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso h.
  - simpl in |- *.
    intro h.
    let proof h' := sorting.insertion.forward.membership h.
    match h' with | e | h'' end.
    + ipso (Disjunction.L e).
    + ipso (Disjunction.R (IH h'')).
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
  match l with | | b l' by IH end per List.induction.
  - simpl in |- *.
    intro h.
    ipso h.
  - simpl in |- *.
    intro h.
    lemma facto : &a = &b \/ insertion_sort &le &l' contains_member &a.
    {
      match h with | e | h' end.
      + ipso (Disjunction.L e).
      + ipso (Disjunction.R (IH h')).
    }
    ipso (sorting.insertion.backward.membership &le &b &a (insertion_sort &le &l') &facto).
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
  divide et impera.
  - ipso (@sorting.forward.preservation.of.membership  A le a l).
  - ipso (sorting.backward.preservation.of.membership le a l).
Qed.

(* sorting.preservation.of.length *)
Theorem length
  : forall {A : Type} (le : A -> A -> Bool) (l : List A) .
      (|| insertion_sort le l ||) = (|| l ||).
Proof.
  intros A le l.
  match l with | | a l' by IH end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (sorting.insertion.length le a (insertion_sort le l')) in |- *.
    leibniz IH in |- *.
    quod idem est.
Qed.

End of. (* sorting.preservation.of *)

End preservation. (* sorting.preservation *)

End sorting. (* sorting *)

Module range. (* range *)

Module positive. (* range.positive *)

(* range.positive.length *)
Lemma length
  : forall (p : Nat) . (|| range_positive p ||) = NatWithZero.Positive p.
Proof.
  intros p.
  match p with | | p' by IH end per Nat.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (appending.length (range_positive p') (NatWithZero.Positive p')) in |- *.
    leibniz IH in |- *.
    simpl in |- *.
    simpl Nat.inc in |- *.
    quod idem est.
Qed.

Module forward. (* range.positive.forward *)

(* range.positive.forward.membership *)
Lemma membership
  : forall {p : Nat} {i : NatWithZero} .
      range_positive p contains_member i -> i < NatWithZero.Positive p.
Proof.
  intros p.
  match p with | | p' by IH end per Nat.induction.
  - intros i h.
    simpl in h.
    match h with | e | f end.
    + leibniz e in |- *.
      simpl NatWithZero.LessThan in |- *.
      exists Nat.One.
      simpl in |- *.
      quod idem est.
    + ex f quodlibet.
  - intros i h.
    simpl in h.
    modus aequans
      (membership
        .distributivity
        .over
        .concatenation
          (i) (range_positive p') (NatWithZero.Positive p' :: [])),
      h |- h'.
    lemma facto : &i < NatWithZero.Positive Nat.One + NatWithZero.Positive &p'.
    {
      leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (NatWithZero.Positive p')) in |- *.
      lemma below : i <= NatWithZero.Positive p'.
      {
        simpl NatWithZero.LessOrEqual in |- *.
        match h' with | h1 | h2 end.
        + ipso (Disjunction.R (IH i h1)).
        + simpl in h2.
          match h2 with | e | f end.
          * ipso (Disjunction.L e).
          * ex f quodlibet.
      }
      ipso (modus aequans
            (NatWithZero.order.discreteness i (NatWithZero.Positive p')),
            below).
    }
    ipso &facto.
Qed.

End forward. (* range.positive.forward *)

Module backward. (* range.positive.backward *)

(* range.positive.backward.membership *)
Lemma membership
  : forall {p : Nat} {i : NatWithZero} .
      i < NatWithZero.Positive p -> range_positive p contains_member i.
Proof.
  intros p.
  match p with | | p' by IH end per Nat.induction.
  - intros i h.
    simpl NatWithZero.LessThan in h.
    match h with | k e end.
    match i with | | q end.
    + simpl in |- *.
      ipso (Disjunction.L (Identity.reflexivity NatWithZero.Zero)).
    + simpl in e.
      let proof e' := NatWithZero.positive.injectivity e.
      match q with | | q' end; simpl in e'; ex e' quodlibet.
  - intros i h.
    let proof h : i < NatWithZero.Positive Nat.One + NatWithZero.Positive p' := &h.
    leibniz (NatWithZero.addition.commutativity (NatWithZero.Positive Nat.One) (NatWithZero.Positive p')) in h.
    modus aequans (NatWithZero.order.discreteness i (NatWithZero.Positive p')), h |- h'.
    simpl in |- *.
    lemma side : range_positive p' contains_member i
                   \/ (NatWithZero.Positive p' :: []) contains_member i.
    {
      simpl NatWithZero.LessOrEqual in h'.
      match h' with | e | lt end.
      + lemma singleton : (NatWithZero.Positive &p' :: []) contains_member &i.
        {
          simpl in |- *.
          ipso (Disjunction.L e).
        }
        ipso (disjoin _, &singleton).
      + ipso (Disjunction.L (IH i lt)).
    }
    ipso (modus aequans
             (membership.distributivity.over.concatenation
                i (range_positive p') (NatWithZero.Positive p' :: [])),
           side).
Qed.

End backward. (* range.positive.backward *)

End positive. (* range.positive *)

Module from_zero. (* range.from_zero *)

(* range.from_zero.length *)
Theorem length : forall (n : NatWithZero) . (|| range_from_zero n ||) = n.
Proof.
  intros n.
  match n with | | p end.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    ipso (range.positive.length p).
Qed.

Module membership. (* range.from_zero.membership *)

(* range.from_zero.membership.specification *)
Theorem specification
  : forall (n : NatWithZero) (i : NatWithZero) .
      range_from_zero n contains_member i <-> i < n.
Proof.
  intros n i.
  match n with | | p end.
  - simpl in |- *.
    divide et impera.
    + intro f.
      ex f quodlibet.
    + intro h.
      simpl NatWithZero.LessThan in h.
      match h with | k e end.
      let proof r := NatWithZero.addition.right.identity.absence i k.
      simpl (~ _) in r.
      modus ponens r, e |- f.
      ex f quodlibet.
  - simpl in |- *.
    divide et impera.
    + ipso (@range.positive.forward.membership  p i).
    + ipso (@range.positive.backward.membership p i).
Qed.

End membership. (* range.from_zero.membership *)

Module sum. (* range.from_zero.sum *)

(* A closed form is an answer written with a fixed number of operations,
 * none of them recursive: [sum (range n)] has to walk the list, while
 * [n * (n + Nat.One) / Two] does not, and the count of steps no longer grows
 * with [n]. There is no division here, so both sides are multiplied by
 * two. A start other than zero would make this an arithmetic series, which
 * is a different theorem, so it is stated on [range_from_zero].
 *)
(* range.from_zero.sum.closed_form *)
Theorem closed_form
  : forall (p : Nat) .
      NatWithZero.Positive (Nat.Successor Nat.One)
      * sum (range_from_zero (NatWithZero.Positive (Nat.Successor p)))
      = NatWithZero.Positive p * NatWithZero.Positive (Nat.Successor p).
Proof.
  intros p.
  match p with | | p' by IH end per Nat.induction.
  - simpl sum in |- *.
    simpl in |- *.
    quod idem est.
  - lemma facto
      : NatWithZero.Positive (Nat.Successor Nat.One)
        * sum (append (range_from_zero (NatWithZero.Positive (Nat.Successor &p')))
                      (NatWithZero.Positive (Nat.Successor &p')))
        = NatWithZero.Positive (Nat.Successor &p')
          * NatWithZero.Positive (Nat.Successor (Nat.Successor &p')).
    {
      leibniz (appending.specification
                 (range_from_zero (NatWithZero.Positive (Nat.Successor p')))
                 (NatWithZero.Positive (Nat.Successor p'))) in |- *.
      leibniz (sum.additivity.over.concatenation
                 (range_from_zero (NatWithZero.Positive (Nat.Successor p')))
                 (NatWithZero.Positive (Nat.Successor p') :: []))
        in |- *.
      lemma facto
        : NatWithZero.Positive (Nat.Successor Nat.One)
          * (sum (range_from_zero (NatWithZero.Positive (Nat.Successor &p')))
             + NatWithZero.Positive (Nat.Successor &p'))
          = NatWithZero.Positive (Nat.Successor &p')
            * NatWithZero.Positive (Nat.Successor (Nat.Successor &p')).
      {
        leibniz (NatWithZero.multiplication.left.distributivity.over.addition
                   (NatWithZero.Positive (Nat.Successor Nat.One))
                   (sum (range_from_zero (NatWithZero.Positive (Nat.Successor p'))))
                   (NatWithZero.Positive (Nat.Successor p'))) in |- *.
        leibniz IH in |- *.
        leibniz <- (NatWithZero.multiplication.right.distributivity.over.addition
                      (NatWithZero.Positive (Nat.Successor p')) (NatWithZero.Positive p') (NatWithZero.Positive (Nat.Successor Nat.One)))
          in |- *.
        lemma facto
          : NatWithZero.Positive (Nat.add &p' (Nat.Successor Nat.One))
            * NatWithZero.Positive (Nat.Successor &p')
            = NatWithZero.Positive (Nat.Successor &p')
              * NatWithZero.Positive (Nat.Successor (Nat.Successor &p')).
        {
          leibniz (Nat.addition.commutativity p' (Nat.Successor Nat.One)) in |- *.
          lemma facto
            : NatWithZero.Positive (Nat.Successor (Nat.Successor &p'))
              * NatWithZero.Positive (Nat.Successor &p')
              = NatWithZero.Positive (Nat.Successor &p')
                * NatWithZero.Positive (Nat.Successor (Nat.Successor &p')).
          {
            leibniz (NatWithZero.multiplication.commutativity
                       (NatWithZero.Positive (Nat.Successor p')) (NatWithZero.Positive (Nat.Successor (Nat.Successor p')))) in |- *.
            quod idem est.
          }
          ipso &facto.
        }
        ipso &facto.
      }
      ipso &facto.
    }
    ipso &facto.
Qed.

End sum. (* range.from_zero.sum *)

End from_zero. (* range.from_zero *)

(* range.length *)
Theorem length
  : forall (start : NatWithZero) (stop : NatWithZero) .
      (|| range start stop ||) = NatWithZero.saturating_sub stop start.
Proof.
  intros start stop.
  simpl range in |- *.
  leibniz (mapping.preservation.of.length
             (NatWithZero.add start)
             (range_from_zero (NatWithZero.saturating_sub stop start))) in |- *.
  ipso (from_zero.length (NatWithZero.saturating_sub stop start)).
Qed.

Module membership. (* range.membership *)

(* range.membership.specification *)
Theorem specification
  : forall (start : NatWithZero) (stop : NatWithZero) (i : NatWithZero) .
      range start stop contains_member i <-> start <= i /\ i < stop.
Proof.
  intros start stop i.
  simpl range in |- *.
  match (Comparable.order.totality start stop) with | below | above end.
  - let proof reach := NatWithZero.subtraction.saturating.specification below.
    divide et impera.
    + intro h.
      modus aequans
        (mapping.membership.specification
           (NatWithZero.add start) i
           (range_from_zero (NatWithZero.saturating_sub stop start))),
        h |- w.
      match w with | j c end.
      match c with | m e end.
      modus aequans
        (from_zero.membership.specification
           (NatWithZero.saturating_sub stop start) j),
        m |- lt.
      divide et impera.
      * leibniz e in |- *.
        leibniz (NatWithZero.addition.commutativity start j) in |- *.
        ipso (NatWithZero.addition.right.order.extensivity j start).
      * leibniz e in |- *.
        leibniz <- reach in |- *.
        ipso (NatWithZero.addition.order.strict.monotonicity
                 start j (NatWithZero.saturating_sub stop start) lt).
    + intro c.
      match c with | low high end.
      let proof step := NatWithZero.subtraction.saturating.specification low.
      lemma inside : NatWithZero.saturating_sub i start
                       < NatWithZero.saturating_sub stop start.
      {
        lemma shifted : &start + NatWithZero.saturating_sub &i &start
                          < &start + NatWithZero.saturating_sub &stop &start.
        {
          leibniz step in |- *.
          leibniz reach in |- *.
          ipso high.
        }
        ipso (NatWithZero.addition.order.strict.cancellation &start _ _ &shifted).
      }
      lemma witness : forsome (j : NatWithZero) .
                range_from_zero (NatWithZero.saturating_sub stop start) contains_member j
                /\ i = NatWithZero.add start j.
      {
        exists (NatWithZero.saturating_sub i start).
        divide et impera.
        * ipso (modus aequans
                   (from_zero.membership.specification
                      (NatWithZero.saturating_sub stop start)
                      (NatWithZero.saturating_sub i start)),
                 inside).
        * symm in step.
          ipso step.
      }
      ipso (modus aequans
               (mapping.membership.specification
                  (NatWithZero.add start) i
                  (range_from_zero (NatWithZero.saturating_sub stop start))),
             witness).
  - let proof empty := NatWithZero.subtraction.saturating.truncation above.
    leibniz empty in |- *.
    simpl in |- *.
    divide et impera.
    + intro f.
      ex f quodlibet.
    + intro c.
      match c with | low high end.
      let proof reached := Comparable.order.transitivity stop start i above low.
      match reached with | e | lt end.
      * leibniz e in high.
        ipso (NatWithZero.order.strict.irreflexivity i high).
      * ipso (Comparable.order.strict.asymmetry i stop high lt).
Qed.

End membership. (* range.membership *)

Module inclusive. (* range.inclusive *)

(* range.inclusive.length *)
Theorem length
  : forall (start : NatWithZero) (stop : NatWithZero) .
      (|| range_inclusive start stop ||)
      = NatWithZero.saturating_sub (NatWithZero.inc stop) start.
Proof.
  intros start stop.
  simpl range_inclusive in |- *.
  ipso (range.length start (NatWithZero.inc stop)).
Qed.

Module membership. (* range.inclusive.membership *)

(* range.inclusive.membership.specification *)
Theorem specification
  : forall (start : NatWithZero) (stop : NatWithZero) (i : NatWithZero) .
      range_inclusive start stop contains_member i <-> start <= i /\ i <= stop.
Proof.
  intros start stop i.
  simpl range_inclusive in |- *.
  leibniz (NatWithZero.increment.specification stop) in |- *.
  leibniz (NatWithZero.addition.commutativity
             (NatWithZero.Positive Nat.One) stop) in |- *.
  divide et impera.
  - intro h.
    modus aequans
      (range.membership.specification
         start (stop + NatWithZero.Positive Nat.One) i),
      h |- c.
    match c with | low high end.
    divide et impera.
    + ipso low.
    + ipso (modus aequans (NatWithZero.order.discreteness i stop), high).
  - intro c.
    match c with | low high end.
    lemma bounds : start <= i /\ i < stop + NatWithZero.Positive Nat.One.
    {
      divide et impera.
      + ipso low.
      + ipso (modus aequans (NatWithZero.order.discreteness i stop), high).
    }
    ipso (modus aequans
             (range.membership.specification
                start (stop + NatWithZero.Positive Nat.One) i),
           bounds).
Qed.

End membership. (* range.inclusive.membership *)

End inclusive. (* range.inclusive *)

End range. (* range *)

Module comparison. (* comparison *)

(* [le] is the comparison that [insert], [insertion_sort], [maximum_of] and
 * [minimum_of] take. Both facts below follow from totality alone, and the
 * extrema laws use them where an element is compared with itself or where
 * a [false] answer has to be read the other way round.
 *)

(* comparison.reflexivity *)
Lemma reflexivity
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      forall (a : A) . le a a = true.
Proof.
  intros A le total a.
  match (total a a) with | h | h end.
  - ipso h.
  - ipso h.
Qed.

(* comparison.contraposition *)
Lemma contraposition
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      forall {a : A} {b : A} . le a b = false -> le b a = true.
Proof.
  intros A le total a b s.
  symm in s.
  hs (Identity.transitivity s), Bool.distinctness.backward as n.
  ipso (modus tollendo ponens (total a b), n).
Qed.

End comparison. (* comparison *)

Module maximum. (* maximum *)

Module absence. (* maximum.absence *)

(* maximum.absence.specification *)
Lemma specification
  : forall {A : Type} (le : A -> A -> Bool) (l : List A) .
      maximum_of le l = None <-> l = [].
Proof.
  intros A le l.
  divide et impera.
  - intro e.
    match l with | | a l' end.
    + quod idem est.
    + simpl in e.
      match (maximum_of le l') with | | m end.
      * ex e quodlibet.
      * match (le a m) with end.
        -- ex e quodlibet.
        -- ex e quodlibet.
  - intro e.
    leibniz e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End absence. (* maximum.absence *)

(* maximum.bound *)
Theorem bound
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall {l : List A} {m : A} .
        maximum_of le l = Some m -> All (fun (a : A) . le a m = true) l.
Proof.
  intros A le total transitive l.
  match l with | | a l' by IH end per List.induction.
  - intros m e.
    simpl in e.
    ex e quodlibet.
  - intros m e.
    simpl in e.
    match (maximum_of le l') with | | m' end |- r.
    + modus aequans (absence.specification le l'), r |- en.
      let proof e' := Option.some.injectivity e.
      leibniz en in |- *.
      leibniz <- e' in |- *.
      simpl in |- *.
      divide et impera.
      * ipso (comparison.reflexivity total a).
      * ipso I.
    + match (le a m') with end |- s.
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        divide et impera.
        -- ipso s.
        -- ipso (IH m' (Identity.reflexivity (Some m'))).
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        let proof ha := comparison.contraposition total s.
        divide et impera.
        -- ipso (comparison.reflexivity total a).
        -- ipso (quantification.all.monotonicity
                    (fun (x : A) (h : le x m' = true) . transitive x m' a h ha)
                    (IH m' (Identity.reflexivity (Some m')))).
Qed.

(* maximum.membership *)
Theorem membership
  : forall {A : Type} {le : A -> A -> Bool} {l : List A} {m : A} .
      maximum_of le l = Some m -> l contains_member m.
Proof.
  intros A le l.
  match l with | | a l' by IH end per List.induction.
  - intros m e.
    simpl in e.
    ex e quodlibet.
  - intros m e.
    simpl in e.
    match (maximum_of le l') with | | m' end |- r.
    + let proof e' := Option.some.injectivity e.
      simpl in |- *.
      ipso (Disjunction.L (Identity.symmetry e')).
    + match (le a m') with end |- s.
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        ipso (disjoin _, (&IH &m' (Identity.reflexivity (Some &m')))).
      * let proof e' := Option.some.injectivity e.
        simpl in |- *.
        ipso (Disjunction.L (Identity.symmetry e')).
Qed.

End maximum. (* maximum *)

Module minimum. (* minimum *)

Module absence. (* minimum.absence *)

(* minimum.absence.specification *)
Lemma specification
  : forall {A : Type} (le : A -> A -> Bool) (l : List A) .
      minimum_of le l = None <-> l = [].
Proof.
  intros A le l.
  divide et impera.
  - intro e.
    match l with | | a l' end.
    + quod idem est.
    + simpl in e.
      match (minimum_of le l') with | | m end.
      * ex e quodlibet.
      * match (le a m) with end.
        -- ex e quodlibet.
        -- ex e quodlibet.
  - intro e.
    leibniz e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End absence. (* minimum.absence *)

(* minimum.bound *)
Theorem bound
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall {l : List A} {m : A} .
        minimum_of le l = Some m -> All (fun (a : A) . le m a = true) l.
Proof.
  intros A le total transitive l.
  match l with | | a l' by IH end per List.induction.
  - intros m e.
    simpl in e.
    ex e quodlibet.
  - intros m e.
    simpl in e.
    match (minimum_of le l') with | | m' end |- r.
    + modus aequans (absence.specification le l'), r |- en.
      let proof e' := Option.some.injectivity e.
      leibniz en in |- *.
      leibniz <- e' in |- *.
      simpl in |- *.
      divide et impera.
      * ipso (comparison.reflexivity total a).
      * ipso I.
    + match (le a m') with end |- s.
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        divide et impera.
        -- ipso (comparison.reflexivity total a).
        -- ipso (quantification.all.monotonicity
                    (fun (x : A) (h : le m' x = true) . transitive a m' x s h)
                    (IH m' (Identity.reflexivity (Some m')))).
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        divide et impera.
        -- ipso (comparison.contraposition total s).
        -- ipso (IH m' (Identity.reflexivity (Some m'))).
Qed.

(* minimum.membership *)
Theorem membership
  : forall {A : Type} {le : A -> A -> Bool} {l : List A} {m : A} .
      minimum_of le l = Some m -> l contains_member m.
Proof.
  intros A le l.
  match l with | | a l' by IH end per List.induction.
  - intros m e.
    simpl in e.
    ex e quodlibet.
  - intros m e.
    simpl in e.
    match (minimum_of le l') with | | m' end |- r.
    + let proof e' := Option.some.injectivity e.
      simpl in |- *.
      ipso (Disjunction.L (Identity.symmetry e')).
    + match (le a m') with end |- s.
      * let proof e' := Option.some.injectivity e.
        simpl in |- *.
        ipso (Disjunction.L (Identity.symmetry e')).
      * let proof e' := Option.some.injectivity e.
        leibniz <- e' in |- *.
        simpl in |- *.
        ipso (disjoin _, (&IH &m' (Identity.reflexivity (Some &m')))).
Qed.

End minimum. (* minimum *)

End List. (* List *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [List A], not [List.T A].
 *)
Abbreviation List := List.T.

(* Makes the notations declared in [Module List] usable in every file that
 * imports this one, as [(l1 ++ l2)%list] or under an opened
 * [jwa_list_scope]. Only the notations are exported: [concat], the laws and
 * the two ctors still need the [List.] prefix. That split is the point of
 * the selective form -- [[]] and [::] are the spellings a client wants,
 * while [Nil] and [Cons] are the names a second container would collide
 * with.
 *)
Export (notations) List.

Instance List_concat_monoid
  : forall {A : Type} . Monoid (@List.concat A) List.Nil :=
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
