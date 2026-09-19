(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Algebra.Semigroup],
 * [Algebra.Monoid] and [Data.Functor] are the classes the
 * instances at the bottom fill; [Data.Number.NatWithZero] is what [length] counts
 * in, [Data.Comparable] holds the laws of its [min] and [max] and of its
 * order, [Data.Number.Nat] carries the [One] inside [Positive One], [Data.Bool] is
 * what a [filter] predicate answers in, [Data.Option] is what [head] and
 * [tail] answer in, and [Data.Product] is what [pop], [zip] and [partition]
 * answer in.
 *)
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.

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

(* The eliminator behind [induction], written out. Its content is the [fix]:
 * the proof for [Cons a l] is built from the proof for [l], and following
 * [l] down to [Nil] is what terminates.
 *)
Definition List_induction
  : forall (A : Type) (P : List A -> Prop),
      P Nil ->
      (forall (a : A) (l : List A), P l -> P (Cons a l)) ->
      forall (l : List A), P l
  := fun (A : Type) (P : List A -> Prop)
         (base : P Nil)
         (step : forall (a : A) (l : List A), P l -> P (Cons a l)) =>
       fix go (l : List A) : P l :=
         match l with
         | Nil       => base
         | Cons a l' => step a l' (go l')
         end.

(* A module may carry the type's name; its members read [List.append]. *)
Module List.

(* Recursion is on the first list: [append Nil l2] is [l2], and each [Cons]
 * of [l1] is put back in front of the result.
 *)
Fixpoint append {A : Type} (l1 : List A) (l2 : List A) : List A :=
  match l1 with
  | Nil        => l2
  | Cons a l1' => Cons a (append l1' l2)
  end.

Theorem append_associativity
  : forall {A : Type} (l1 : List A) (l2 : List A) (l3 : List A),
      append (append l1 l2) l3 = append l1 (append l2 l3).
Proof.
  intros A l1 l2 l3.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [append] recurses on its first argument, so [append Nil l] reduces while
 * [append l Nil] does not; the second identity takes an induction.
 *)

Lemma append_left_identity : forall {A : Type} (l : List A), append Nil l = l.
Proof.
  intros A l.
  simpl in |- *.
  reflexivity.
Qed.

Lemma append_right_identity : forall {A : Type} (l : List A), append l Nil = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem append_identity
  : forall {A : Type} (l : List A), (append Nil l = l) /\ (append l Nil = l).
Proof.
  intros A l.
  split.
  - exact (append_left_identity l).
  - exact (append_right_identity l).
Qed.

(* The empty list has length zero, which is why the count is a
 * [NatWithZero] and not a [Nat]. Each [Cons] adds one on the right:
 * [add] matches its first argument, so with the recursive call there
 * [simpl] leaves [add (length l') (Positive One)] folded instead of
 * opening a [match] on a term it cannot reduce.
 *)
Fixpoint length {A : Type} (l : List A) : NatWithZero :=
  match l with
  | Nil       => Zero
  | Cons _ l' => NatWithZero.add (length l') (Positive One)
  end.

Theorem length_additivity_over_append
  : forall {A : Type} (l1 : List A) (l2 : List A),
      length (append l1 l2) = NatWithZero.add (length l1) (length l2).
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite NatWithZero.addition_associativity in |- *.
    rewrite NatWithZero.addition_associativity in |- *.
    rewrite (NatWithZero.addition_commutativity (length l2) (Positive One)) in |- *.
    reflexivity.
Qed.

(* [map] applies [f] to every element and keeps the shape. *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | Nil       => Nil
  | Cons a l' => Cons (f a) (map f l')
  end.

(* The two functor laws, stated for every [l] as in [Data.Option]: nothing
 * here assumes functional extensionality.
 *)

Theorem map_identity
  : forall (A : Type) (l : List A), map (fun a => a) l = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem map_composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (l : List A),
    map g (map f l) = map (fun a => g (f a)) l.
Proof.
  intros A B C f g l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [map] distributes over [append]: mapping a concatenation is
 * concatenating the mapped halves.
 *)
Theorem map_distributivity_over_append
  : forall (A : Type) (B : Type) (f : A -> B) (l1 : List A) (l2 : List A),
      map f (append l1 l2) = append (map f l1) (map f l2).
Proof.
  intros A B f l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [reverse] moves each element to the end of the reversed rest. Quadratic,
 * and the simplest shape for the proofs below; an accumulator version can
 * come with a proof that it agrees.
 *)
Fixpoint reverse {A : Type} (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' => append (reverse l') (Cons a Nil)
  end.

(* [reverse] turns a concatenation around: the reversed halves come back in
 * the opposite order.
 *)
Theorem reverse_antidistributivity_over_append
  : forall (A : Type) (l1 : List A) (l2 : List A),
      reverse (append l1 l2) = append (reverse l2) (reverse l1).
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    rewrite append_right_identity in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite append_associativity in |- *.
    reflexivity.
Qed.

Theorem reverse_involution
  : forall (A : Type) (l : List A), reverse (reverse l) = l.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite reverse_antidistributivity_over_append in |- *.
    simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [fold_right f z] replaces every [Cons] by [f] and the final [Nil] by [z],
 * working from the right: [Cons a (Cons b Nil)] becomes [f a (f b z)].
 *)
Fixpoint fold_right {A : Type} {B : Type} (f : A -> B -> B) (z : B)
                    (l : List A) : B :=
  match l with
  | Nil       => z
  | Cons a l' => f a (fold_right f z l')
  end.

(* Read [fold_right f _ l] as a function of its seed; then the fold of a
 * concatenation is the composition of the two folds, the second list's
 * applied first.
 *)
Theorem fold_right_composition_over_append
  : forall (A : Type) (B : Type) (f : A -> B -> B) (z : B)
      (l1 : List A) (l2 : List A),
    fold_right f z (append l1 l2) = fold_right f (fold_right f z l2) l1.
Proof.
  intros A B f z l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* A catamorphism is a function on lists that is some [fold_right]: it only
 * fixes what replaces [Cons] and what replaces [Nil]. [append], [length]
 * and [map] are three of them.
 *)

Theorem append_catamorphism
  : forall (A : Type) (l1 : List A) (l2 : List A),
      append l1 l2 = fold_right Cons l2 l1.
Proof.
  intros A l1 l2.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem length_catamorphism
  : forall (A : Type) (l : List A),
      length l
      = fold_right (fun (_ : A) (n : NatWithZero) => NatWithZero.add n (Positive One))
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

Theorem map_catamorphism
  : forall (A : Type) (B : Type) (f : A -> B) (l : List A),
      map f l
      = fold_right (fun (a : A) (mapped : List B) => Cons (f a) mapped)
                   Nil
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

(* Membership, defined by recursion into [Prop]: [Contains a Nil] computes
 * to [Falsum] and [Contains a (Cons b l)] to [a = b \/ Contains a l], so
 * [simpl] exposes the cases and every proof below is a case analysis.
 *)
Fixpoint Contains {A : Type} (a : A) (l : List A) : Prop :=
  match l with
  | Nil       => Falsum
  | Cons b l' => a = b \/ Contains a l'
  end.

Theorem nil_contains_nothing
  : forall (A : Type) (a : A), ~ Contains a Nil.
Proof.
  intros A a.
  unfold Negation in |- *.
  simpl in |- *.
  intro f.
  exact f.
Qed.

(* Membership in a concatenation is membership in either half. The two
 * halves are lemmas, the [<->] the theorem.
 *)

Lemma contains_distributivity_over_append_forward
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a (append l1 l2) -> Contains a l1 \/ Contains a l2.
Proof.
  intros A a l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact (Disjunction.right h).
  - simpl in |- *.
    intro h.
    destruct h as [e | h'].
    + exact (Disjunction.left (Disjunction.left e)).
    + destruct (IH h') as [h1 | h2].
      * exact (Disjunction.left (Disjunction.right h1)).
      * exact (Disjunction.right h2).
Qed.

Lemma contains_distributivity_over_append_backward
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a l1 \/ Contains a l2 -> Contains a (append l1 l2).
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
      * exact (Disjunction.left e).
      * apply Disjunction.right.
        apply IH.
        exact (Disjunction.left h1').
    + apply Disjunction.right.
      apply IH.
      exact (Disjunction.right h2).
Qed.

Theorem contains_distributivity_over_append
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a (append l1 l2) <-> Contains a l1 \/ Contains a l2.
Proof.
  intros A a l1 l2.
  split.
  - exact (contains_distributivity_over_append_forward A a l1 l2).
  - exact (contains_distributivity_over_append_backward A a l1 l2).
Qed.

(* [map] carries membership along: an element of [l] has its image in
 * [map f l].
 *)
Theorem map_containment_preservation
  : forall (A : Type) (B : Type) (f : A -> B) (a : A) (l : List A),
      Contains a l -> Contains (f a) (map f l).
Proof.
  intros A B f a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro g.
    exact g.
  - simpl in |- *.
    intro h.
    destruct h as [e | h'].
    + apply Disjunction.left.
      rewrite e in |- *.
      reflexivity.
    + apply Disjunction.right.
      apply IH.
      exact h'.
Qed.

(* [reverse] keeps membership, in both directions; each direction goes
 * through the distributivity over [append], since [reverse] is built from
 * it.
 *)

Lemma reverse_containment_preservation_forward
  : forall (A : Type) (a : A) (l : List A),
      Contains a (reverse l) -> Contains a l.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    exact f.
  - simpl in |- *.
    intro h.
    destruct (contains_distributivity_over_append_forward
                A a (reverse l') (Cons b Nil) h) as [h1 | h2].
    + apply Disjunction.right.
      apply IH.
      exact h1.
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.left e).
      * contradiction f.
Qed.

Lemma reverse_containment_preservation_backward
  : forall (A : Type) (a : A) (l : List A),
      Contains a l -> Contains a (reverse l).
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    exact f.
  - simpl in |- *.
    intro h.
    apply contains_distributivity_over_append_backward.
    destruct h as [e | h'].
    + apply Disjunction.right.
      simpl in |- *.
      exact (Disjunction.left e).
    + apply Disjunction.left.
      apply IH.
      exact h'.
Qed.

Theorem reverse_containment_preservation
  : forall (A : Type) (a : A) (l : List A),
      Contains a (reverse l) <-> Contains a l.
Proof.
  intros A a l.
  split.
  - exact (reverse_containment_preservation_forward A a l).
  - exact (reverse_containment_preservation_backward A a l).
Qed.

(* [filter p] keeps the elements [p] answers [true] on, in their order. *)
Fixpoint filter {A : Type} (p : A -> Bool) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match p a with
      | true  => Cons a (filter p l')
      | false => filter p l'
      end
  end.

(* Filtering a concatenation filters each half. The head's answer decides
 * the shape, so each step is a case analysis on [p b].
 *)
Theorem filter_distributivity_over_append
  : forall (A : Type) (p : A -> Bool) (l1 : List A) (l2 : List A),
      filter p (append l1 l2) = append (filter p l1) (filter p l2).
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

(* [filter] is a catamorphism too: [Cons] becomes a conditional [Cons]. *)
Theorem filter_catamorphism
  : forall (A : Type) (p : A -> Bool) (l : List A),
      filter p l
      = fold_right (fun (a : A) (kept : List A) =>
                      match p a with
                      | true  => Cons a kept
                      | false => kept
                      end)
                    Nil
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

(* The specification of [filter]: an element is in the result exactly when
 * it was in the input and [p] answers [true] on it. The two halves are
 * lemmas, the [<->] the theorem. Where the head's answer matters later,
 * [destruct ... eqn:] keeps it as an equation in the context.
 *)

Lemma filter_specification_forward
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a (filter p l) -> Contains a l /\ p a = true.
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
        -- exact (Disjunction.left e).
        -- rewrite e in |- *.
           exact pb.
      * destruct (IH h') as [hl pa].
        split.
        -- exact (Disjunction.right hl).
        -- exact pa.
    + simpl in |- *.
      intro h'.
      destruct (IH h') as [hl pa].
      split.
      * exact (Disjunction.right hl).
      * exact pa.
Qed.

Lemma filter_specification_backward
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a l /\ p a = true -> Contains a (filter p l).
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
      exact (Disjunction.left e).
    + destruct (p b) as [|].
      * simpl in |- *.
        apply Disjunction.right.
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

Theorem filter_specification
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a (filter p l) <-> Contains a l /\ p a = true.
Proof.
  intros A p a l.
  split.
  - exact (filter_specification_forward A p a l).
  - exact (filter_specification_backward A p a l).
Qed.

(* [All P] holds when every element satisfies [P], [Any P] when some
 * element does. Both recurse into [Prop] as [Contains] does: [Nil] gives
 * the neutral proposition, [Cons] a conjunction or a disjunction.
 *)

Fixpoint All {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | Nil       => Verum
  | Cons a l' => P a /\ All P l'
  end.

Fixpoint Any {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | Nil       => Falsum
  | Cons a l' => P a \/ Any P l'
  end.

(* [All] over a concatenation is [All] over each half. *)

Lemma all_distributivity_over_append_forward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P (append l1 l2) -> All P l1 /\ All P l2.
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

Lemma all_distributivity_over_append_backward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P l1 /\ All P l2 -> All P (append l1 l2).
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

Theorem all_distributivity_over_append
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P (append l1 l2) <-> All P l1 /\ All P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (all_distributivity_over_append_forward A P l1 l2).
  - exact (all_distributivity_over_append_backward A P l1 l2).
Qed.

(* [Any] over a concatenation is [Any] over either half. *)

Lemma any_distributivity_over_append_forward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P (append l1 l2) -> Any P l1 \/ Any P l2.
Proof.
  intros A P l1 l2.
  induction l1 as [| b l1' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact (Disjunction.right h).
  - simpl in |- *.
    intro h.
    destruct h as [pb | h'].
    + exact (Disjunction.left (Disjunction.left pb)).
    + destruct (IH h') as [h1 | h2].
      * exact (Disjunction.left (Disjunction.right h1)).
      * exact (Disjunction.right h2).
Qed.

Lemma any_distributivity_over_append_backward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P l1 \/ Any P l2 -> Any P (append l1 l2).
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
      * exact (Disjunction.left pb).
      * apply Disjunction.right.
        apply IH.
        exact (Disjunction.left h1').
    + apply Disjunction.right.
      apply IH.
      exact (Disjunction.right h2).
Qed.

Theorem any_distributivity_over_append
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P (append l1 l2) <-> Any P l1 \/ Any P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (any_distributivity_over_append_forward A P l1 l2).
  - exact (any_distributivity_over_append_backward A P l1 l2).
Qed.

(* The specifications of [All] and [Any] through membership: [All P l] says
 * [P] of every member, [Any P l] that some member satisfies [P]. The
 * second is the first use of [exists] in the library.
 *)

Lemma all_specification_forward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l -> forall (a : A), Contains a l -> P a.
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

Lemma all_specification_backward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      (forall (a : A), Contains a l -> P a) -> All P l.
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
      exact (Disjunction.left (Identity.reflexivity b)).
    + apply IH.
      intros a ha.
      apply (h a).
      exact (Disjunction.right ha).
Qed.

Theorem all_specification
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l <-> (forall (a : A), Contains a l -> P a).
Proof.
  intros A P l.
  split.
  - exact (all_specification_forward A P l).
  - exact (all_specification_backward A P l).
Qed.

Lemma any_specification_forward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l -> exists (a : A), Contains a l /\ P a.
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
      * exact (Disjunction.left (Identity.reflexivity b)).
      * exact pb.
    + destruct (IH h') as [a ha].
      destruct ha as [ha' pa].
      apply (Exists_introduction a).
      split.
      * exact (Disjunction.right ha').
      * exact pa.
Qed.

Lemma any_specification_backward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      (exists (a : A), Contains a l /\ P a) -> Any P l.
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
      exact (Disjunction.left pa).
    + apply Disjunction.right.
      apply IH.
      apply (Exists_introduction a).
      split.
      * exact ha''.
      * exact pa.
Qed.

Theorem any_specification
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l <-> (exists (a : A), Contains a l /\ P a).
Proof.
  intros A P l.
  split.
  - exact (any_specification_forward A P l).
  - exact (any_specification_backward A P l).
Qed.

(* [Contains], [All] and [Any] are catamorphisms into [Prop]: [Cons]
 * becomes a connective and [Nil] its neutral proposition.
 *)

Theorem contains_catamorphism
  : forall (A : Type) (a : A) (l : List A),
      Contains a l
      = fold_right (fun (b : A) (rest : Prop) => a = b \/ rest) Falsum l.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem all_catamorphism
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l = fold_right (fun (a : A) (rest : Prop) => P a /\ rest) Verum l.
Proof.
  intros A P l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Theorem any_catamorphism
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l = fold_right (fun (a : A) (rest : Prop) => P a \/ rest) Falsum l.
Proof.
  intros A P l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* Taking a list apart at the front: [head] looks at the first element and
 * [tail] drops it. Both answer in [Option], since the empty list has
 * neither.
 *)

(* [forall {A : Type}, List A -> Option A] *)
Definition head := fun {A : Type} (l : List A) =>
  match l with
  | Nil      => None
  | Cons a _ => Some a
  end.

(* [forall {A : Type}, List A -> Option (List A)] *)
Definition tail := fun {A : Type} (l : List A) =>
  match l with
  | Nil       => None
  | Cons _ l' => Some l'
  end.

(* The specifications: [head l] is [Some a] exactly when [l] starts with
 * [a], and [tail l] is [Some l'] exactly when [l] is [l'] behind one
 * element. Each is a [<->] with its halves as lemmas.
 *)

Lemma head_specification_forward
  : forall (A : Type) (a : A) (l : List A),
      head l = Some a -> exists (l' : List A), l = Cons a l'.
Proof.
  intros A a l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some_injectivity A b a e) as e'.
    apply (Exists_introduction rest).
    rewrite e' in |- *.
    reflexivity.
Qed.

Lemma head_specification_backward
  : forall (A : Type) (a : A) (l : List A),
      (exists (l' : List A), l = Cons a l') -> head l = Some a.
Proof.
  intros A a l.
  intro h.
  destruct h as [l' e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem head_specification
  : forall (A : Type) (a : A) (l : List A),
      head l = Some a <-> (exists (l' : List A), l = Cons a l').
Proof.
  intros A a l.
  split.
  - exact (head_specification_forward A a l).
  - exact (head_specification_backward A a l).
Qed.

Lemma tail_specification_forward
  : forall (A : Type) (l : List A) (l' : List A),
      tail l = Some l' -> exists (a : A), l = Cons a l'.
Proof.
  intros A l l'.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some_injectivity (List A) rest l' e) as e'.
    apply (Exists_introduction b).
    rewrite e' in |- *.
    reflexivity.
Qed.

Lemma tail_specification_backward
  : forall (A : Type) (l : List A) (l' : List A),
      (exists (a : A), l = Cons a l') -> tail l = Some l'.
Proof.
  intros A l l'.
  intro h.
  destruct h as [a e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem tail_specification
  : forall (A : Type) (l : List A) (l' : List A),
      tail l = Some l' <-> (exists (a : A), l = Cons a l').
Proof.
  intros A l l'.
  split.
  - exact (tail_specification_forward A l l').
  - exact (tail_specification_backward A l l').
Qed.

(* Taking a list apart at the back, through [reverse]: the last element is
 * the head of the reversal, and what precedes it is the tail of the
 * reversal turned back around.
 *)

(* [forall {A : Type}, List A -> Option A] *)
Definition last := fun {A : Type} (l : List A) => head (reverse l).

(* [forall {A : Type}, List A -> Option (List A)] *)
Definition initial := fun {A : Type} (l : List A) => Option.map reverse (tail (reverse l)).

(* The specifications mirror those of [head] and [tail]: [last l] is
 * [Some a] exactly when [l] ends with [a], and [initial l] is [Some l']
 * exactly when [l] is [l'] followed by one element.
 *)

Lemma last_specification_forward
  : forall (A : Type) (a : A) (l : List A),
      last l = Some a -> exists (l' : List A), l = append l' (Cons a Nil).
Proof.
  intros A a l.
  unfold last in |- *.
  intro h.
  destruct (head_specification_forward A a (reverse l) h) as [r e].
  apply (Exists_introduction (reverse r)).
  pose proof (Identity.congruence reverse e) as e'.
  rewrite reverse_involution in e'.
  simpl in e'.
  exact e'.
Qed.

Lemma last_specification_backward
  : forall (A : Type) (a : A) (l : List A),
      (exists (l' : List A), l = append l' (Cons a Nil)) -> last l = Some a.
Proof.
  intros A a l.
  intro h.
  destruct h as [l' e].
  unfold last in |- *.
  rewrite e in |- *.
  rewrite reverse_antidistributivity_over_append in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem last_specification
  : forall (A : Type) (a : A) (l : List A),
      last l = Some a <-> (exists (l' : List A), l = append l' (Cons a Nil)).
Proof.
  intros A a l.
  split.
  - exact (last_specification_forward A a l).
  - exact (last_specification_backward A a l).
Qed.

Lemma initial_specification_forward
  : forall (A : Type) (l : List A) (l' : List A),
      initial l = Some l' -> exists (a : A), l = append l' (Cons a Nil).
Proof.
  intros A l l'.
  unfold initial in |- *.
  destruct (reverse l) as [| b r] eqn:er.
  - simpl in |- *.
    intro h.
    discriminate h.
  - simpl in |- *.
    intro h.
    pose proof (Option.some_injectivity (List A) (reverse r) l' h) as e'.
    apply (Exists_introduction b).
    pose proof (Identity.congruence reverse er) as er'.
    rewrite reverse_involution in er'.
    simpl in er'.
    rewrite e' in er'.
    exact er'.
Qed.

Lemma initial_specification_backward
  : forall (A : Type) (l : List A) (l' : List A),
      (exists (a : A), l = append l' (Cons a Nil)) -> initial l = Some l'.
Proof.
  intros A l l'.
  intro h.
  destruct h as [a e].
  unfold initial in |- *.
  rewrite e in |- *.
  rewrite reverse_antidistributivity_over_append in |- *.
  simpl in |- *.
  rewrite reverse_involution in |- *.
  reflexivity.
Qed.

Theorem initial_specification
  : forall (A : Type) (l : List A) (l' : List A),
      initial l = Some l' <-> (exists (a : A), l = append l' (Cons a Nil)).
Proof.
  intros A l l'.
  split.
  - exact (initial_specification_forward A l l').
  - exact (initial_specification_backward A l l').
Qed.

(* [forall {A : Type}, List A -> Option (A * List A)]
 * [head] and [tail] in one answer: [None] on the empty list, else the
 * first element paired with the rest.
 *)
Definition pop := fun {A : Type} (l : List A) =>
  match l return Option (A * List A) with
  | Nil       => None
  | Cons a l' => Some (Product_introduction a l')
  end.

Lemma pop_specification_forward
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      pop l = Some (Product_introduction a l') -> l = Cons a l'.
Proof.
  intros A a l' l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some_injectivity (A * List A)
                  (Product_introduction b rest) (Product_introduction a l') e) as e'.
    pose proof (Product.introduction_injectivity A (List A) b rest a l' e') as e''.
    destruct e'' as [eb erest].
    rewrite eb in |- *.
    rewrite erest in |- *.
    reflexivity.
Qed.

Lemma pop_specification_backward
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      l = Cons a l' -> pop l = Some (Product_introduction a l').
Proof.
  intros A a l' l e.
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

(* [pop] answers [Some (a , l')] exactly on [Cons a l']. *)
Theorem pop_specification
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      pop l = Some (Product_introduction a l') <-> l = Cons a l'.
Proof.
  intros A a l' l.
  split.
  - exact (pop_specification_forward A a l' l).
  - exact (pop_specification_backward A a l' l).
Qed.

(* Projecting a [pop] gives back [head] and [tail]. *)

Theorem pop_head_projection
  : forall (A : Type) (l : List A), Option.map Product.first (pop l) = head l.
Proof.
  intros A l.
  destruct l as [| a l'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem pop_tail_projection
  : forall (A : Type) (l : List A), Option.map Product.second (pop l) = tail l.
Proof.
  intros A l.
  destruct l as [| a l'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Fixpoint zip {A : Type} {B : Type} (l1 : List A) (l2 : List B)
  : List (A * B) :=
  match l1, l2 with
  | Cons a l1', Cons b l2' => Cons (Product_introduction a b) (zip l1' l2')
  | Nil, Nil               => Nil
  | Nil, Cons _ _          => Nil
  | Cons _ _, Nil          => Nil
  end.

(* [forall {A : Type} {B : Type}, List (A * B) -> List A * List B]
 * The two projections mapped over the list, so the laws of [map] carry
 * over.
 *)
Definition unzip := fun {A : Type} {B : Type} (l : List (A * B)) =>
  Product_introduction (map Product.first l) (map Product.second l).

(* Zipping the two halves of an [unzip] rebuilds the list. The other order,
 * [unzip (zip l1 l2)], needs the two lists to be of one length.
 *)
Theorem zip_unzip_identity
  : forall (A : Type) (B : Type) (l : List (A * B)),
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
    rewrite <- (Product.introduction_surjectivity A B p) in |- *.
    reflexivity.
Qed.

(* Unzipping a [zip] gives the two lists back when they are of one length;
 * [zip] stops with the shorter list, so a longer one is not recovered.
 * Induction on [l1] with [l2] kept in the motive, since [zip] and
 * [length] step on both lists at once; the two mismatched cases contradict
 * [NatWithZero.addition_positive_refutes_zero] and the matched case feeds the
 * hypothesis through [NatWithZero.add_r_cancellation].
 *)
Theorem unzip_zip_identity
  : forall (A : Type) (B : Type) (l1 : List A) (l2 : List B),
      length l1 = length l2 -> unzip (zip l1 l2) = Product_introduction l1 l2.
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
      pose proof (NatWithZero.addition_positive_refutes_zero (length l2') One) as h.
      unfold Negation in h.
      pose proof (h e') as f.
      contradiction f.
  - intros l2 e.
    destruct l2 as [| b l2'].
    + simpl in e.
      pose proof (NatWithZero.addition_positive_refutes_zero (length l1') One) as h.
      unfold Negation in h.
      pose proof (h e) as f.
      contradiction f.
    + simpl in e.
      pose proof (NatWithZero.add_r_cancellation
                    (length l1') (length l2') (Positive One) e) as e'.
      pose proof (IH l2' e') as IH'.
      unfold unzip in IH'.
      pose proof (Product.introduction_injectivity (List A) (List B)
                    (map Product.first (zip l1' l2'))
                    (map Product.second (zip l1' l2'))
                    l1' l2' IH') as e''.
      destruct e'' as [e1 e2].
      unfold unzip in |- *.
      simpl in |- *.
      rewrite e1 in |- *.
      rewrite e2 in |- *.
      reflexivity.
Qed.

(* Splits a list into the elements [p] accepts and the ones it rejects, in
 * one pass; the recursive result is opened by a [match] so both halves
 * are extended in place.
 *)
Fixpoint partition {A : Type} (p : A -> Bool) (l : List A)
  : List A * List A :=
  match l with
  | Nil       => Product_introduction Nil Nil
  | Cons a l' =>
      match partition p l' with
      | Product_introduction yes no =>
          match p a with
          | true  => Product_introduction (Cons a yes) no
          | false => Product_introduction yes (Cons a no)
          end
      end
  end.

(* The two halves of a [partition] are the two [filter]s, by [p] and by its
 * negation.
 *)
Theorem partition_specification
  : forall (A : Type) (p : A -> Bool) (l : List A),
      partition p l
      = Product_introduction (filter p l)
                          (filter (fun (a : A) => Bool.negate (p a)) l).
Proof.
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    destruct (p a) as [|] eqn:pa.
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      reflexivity.
Qed.

(* Indexing from [Zero]: [nth l i] is the element [i] places from the front,
 * [None] past the end. Recursion is on the list; the index is peeled by
 * one alongside, [Positive One] being the last step before [Zero].
 *)
Fixpoint nth {A : Type} (l : List A) (i : NatWithZero) : Option A :=
  match l with
  | Nil       => None
  | Cons a l' =>
      match i with
      | Zero                    => Some a
      | Positive One            => nth l' Zero
      | Positive (Successor i') => nth l' (Positive i')
      end
  end.

(* [nth] answers exactly for the indices below the length. Each step of the
 * index is one step of the list, so the halves lift [IH] through
 * [Positive One] added on both sides of the order.
 *)

Lemma nth_specification_forward
  : forall (A : Type) (l : List A) (i : NatWithZero),
      (exists (a : A), nth l i = Some a) -> NatWithZero.LessThan i (length l).
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
      exact (NatWithZero.addition_right_positivity (length l') One).
    + destruct i' as [| i''].
      * simpl in h.
        pose proof (IH Zero h) as lt.
        simpl in |- *.
        rewrite (NatWithZero.addition_commutativity (length l') (Positive One)) in |- *.
        exact (NatWithZero.addition_strict_monotonicity (Positive One) Zero (length l') lt).
      * simpl in h.
        pose proof (IH (Positive i'') h) as lt.
        simpl in |- *.
        rewrite (NatWithZero.addition_commutativity (length l') (Positive One)) in |- *.
        exact (NatWithZero.addition_strict_monotonicity
                 (Positive One) (Positive i'') (length l') lt).
Qed.

Lemma nth_specification_backward
  : forall (A : Type) (l : List A) (i : NatWithZero),
      NatWithZero.LessThan i (length l) -> exists (a : A), nth l i = Some a.
Proof.
  intros A l.
  induction l as [| b l' IH] using List_induction.
  - intros i h.
    simpl in h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    pose proof (NatWithZero.addition_positive_refutes_zero i k) as r.
    unfold Negation in r.
    pose proof (r e) as f.
    contradiction f.
  - intros i h.
    destruct i as [| i'].
    + simpl in |- *.
      apply (Exists_introduction b).
      reflexivity.
    + destruct i' as [| i''].
      * simpl in h.
        rewrite (NatWithZero.addition_commutativity (length l') (Positive One)) in h.
        pose proof (NatWithZero.addition_strict_cancellation (Positive One) Zero (length l') h)
          as lt.
        simpl in |- *.
        exact (IH Zero lt).
      * simpl in h.
        rewrite (NatWithZero.addition_commutativity (length l') (Positive One)) in h.
        pose proof (NatWithZero.addition_strict_cancellation
                      (Positive One) (Positive i'') (length l') h) as lt.
        simpl in |- *.
        exact (IH (Positive i'') lt).
Qed.

Theorem nth_specification
  : forall (A : Type) (l : List A) (i : NatWithZero),
      (exists (a : A), nth l i = Some a) <-> NatWithZero.LessThan i (length l).
Proof.
  intros A l i.
  split.
  - exact (nth_specification_forward  A l i).
  - exact (nth_specification_backward A l i).
Qed.

(* [take n l] is the first [n] elements, all of [l] when there are fewer;
 * [drop n l] is what is left. Both recurse on the list, peeling the count
 * alongside as [nth] does.
 *)
Fixpoint take {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match n with
      | Zero                    => Nil
      | Positive One            => Cons a Nil
      | Positive (Successor n') => Cons a (take (Positive n') l')
      end
  end.

Fixpoint drop {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match n with
      | Zero                    => Cons a l'
      | Positive One            => l'
      | Positive (Successor n') => drop (Positive n') l'
      end
  end.

(* [forall {A : Type}, NatWithZero -> List A -> List A * List A] *)
Definition split_at := fun {A : Type} (n : NatWithZero) (l : List A) =>
  Product_introduction (take n l) (drop n l).

(* The two parts put back together give the list. *)
Theorem take_drop_decomposition
  : forall (A : Type) (l : List A) (n : NatWithZero),
      append (take n l) (drop n l) = l.
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

(* The length of a [take] is the smaller of the count and the length; each
 * step adds one to both candidates, and addition distributes over [min].
 *)
Theorem length_take
  : forall (A : Type) (l : List A) (n : NatWithZero),
      length (take n l) = NatWithZero.min n (length l).
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - intros n.
    simpl in |- *.
    rewrite (NatWithZero.min_right_annihilation n) in |- *.
    reflexivity.
  - intros n.
    destruct n as [| n'].
    + simpl in |- *.
      rewrite (NatWithZero.min_left_annihilation
                 (NatWithZero.add (length l') (Positive One))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * simpl in |- *.
        rewrite (Biimplication.backward_elimination
                   (Comparable.min_specification (Positive One)
                      (NatWithZero.add (length l') (Positive One)))
                   (NatWithZero.addition_right_extensivity (length l') (Positive One))) in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        rewrite (NatWithZero.addition_commutativity
                   (NatWithZero.min (Positive n'') (length l')) (Positive One)) in |- *.
        rewrite (NatWithZero.addition_left_distributivity_over_min
                   (Positive One) (Positive n'') (length l')) in |- *.
        change (NatWithZero.add (Positive One) (Positive n''))
          with (Positive (Successor n'')) in |- *.
        rewrite (NatWithZero.addition_commutativity (Positive One) (length l')) in |- *.
        reflexivity.
Qed.

(* The length of a [drop] is the length less the count; each step takes one
 * from both, which truncated subtraction ignores.
 *)
Theorem length_drop
  : forall (A : Type) (l : List A) (n : NatWithZero),
      length (drop n l) = NatWithZero.saturating_sub (length l) n.
Proof.
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - intros n.
    simpl in |- *.
    reflexivity.
  - intros n.
    destruct n as [| n'].
    + simpl in |- *.
      rewrite (NatWithZero.saturating_sub_r_identity
                 (NatWithZero.add (length l') (Positive One))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * simpl in |- *.
        rewrite (NatWithZero.saturating_subtraction_inversion_of_addition
                   (length l') (Positive One)) in |- *.
        reflexivity.
      * simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        rewrite (NatWithZero.addition_commutativity (length l') (Positive One)) in |- *.
        change (Positive (Successor n''))
          with (NatWithZero.add (Positive One) (Positive n'')) in |- *.
        rewrite (NatWithZero.saturating_sub_translation_invariance
                   (Positive One) (length l') (Positive n'')) in |- *.
        reflexivity.
Qed.

(* [replicate n a] is [a] repeated [n] times. A count of [Zero] gives [Nil];
 * a positive count recurses on its [Nat], one element per step, since a
 * [NatWithZero] has no step of its own to recurse on.
 *)
Fixpoint replicate_positive {A : Type} (k : Nat) (a : A) : List A :=
  match k with
  | One          => Cons a Nil
  | Successor k' => Cons a (replicate_positive k' a)
  end.

(* [forall {A : Type}, NatWithZero -> A -> List A] *)
Definition replicate := fun {A : Type} (n : NatWithZero) (a : A) =>
  match n with
  | Zero       => Nil
  | Positive k => replicate_positive k a
  end.

Lemma length_replicate_positive
  : forall (A : Type) (k : Nat) (a : A), length (replicate_positive k a) = Positive k.
Proof.
  intros A k a.
  induction k as [| k' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    rewrite (Nat.addition_commutativity k' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem length_replicate
  : forall (A : Type) (n : NatWithZero) (a : A), length (replicate n a) = n.
Proof.
  intros A n a.
  destruct n as [| k].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (length_replicate_positive A k a).
Qed.

(* [zip] stops with the shorter list, so its length is the smaller of the
 * two; each step adds one to both, and addition distributes over [min].
 *)
Theorem length_zip
  : forall (A : Type) (B : Type) (l1 : List A) (l2 : List B),
      length (zip l1 l2) = NatWithZero.min (length l1) (length l2).
Proof.
  intros A B l1.
  induction l1 as [| a l1' IH] using List_induction.
  - intros l2.
    destruct l2 as [| b l2'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (NatWithZero.min_left_annihilation
                 (NatWithZero.add (length l2') (Positive One))) in |- *.
      reflexivity.
  - intros l2.
    destruct l2 as [| b l2'].
    + simpl in |- *.
      rewrite (NatWithZero.min_right_annihilation
                 (NatWithZero.add (length l1') (Positive One))) in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (IH l2') in |- *.
      rewrite (NatWithZero.addition_commutativity
                 (NatWithZero.min (length l1') (length l2')) (Positive One)) in |- *.
      rewrite (NatWithZero.addition_left_distributivity_over_min
                 (Positive One) (length l1') (length l2')) in |- *.
      rewrite (NatWithZero.addition_commutativity (Positive One) (length l1')) in |- *.
      rewrite (NatWithZero.addition_commutativity (Positive One) (length l2')) in |- *.
      reflexivity.
Qed.

(* The sum and the product of a list of numbers: [fold_right] over the two
 * monoids of [NatWithZero], the empty list giving the identity.
 *)

(* [List NatWithZero -> NatWithZero] *)
Definition sum := fun (l : List NatWithZero) => fold_right NatWithZero.add Zero l.

(* [List NatWithZero -> NatWithZero] *)
Definition product := fun (l : List NatWithZero) =>
  fold_right NatWithZero.mul (Positive One) l.

Theorem sum_additivity_over_append
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero),
      sum (append l1 l2) = NatWithZero.add (sum l1) (sum l2).
Proof.
  intros l1 l2.
  unfold sum in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.addition_associativity
               a (fold_right NatWithZero.add Zero l1') (fold_right NatWithZero.add Zero l2))
      in |- *.
    reflexivity.
Qed.

Theorem product_multiplicativity_over_append
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero),
      product (append l1 l2) = NatWithZero.mul (product l1) (product l2).
Proof.
  intros l1 l2.
  unfold product in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - rewrite (append_left_identity l2) in |- *.
    change (fold_right NatWithZero.mul (Positive One) Nil) with (Positive One) in |- *.
    rewrite (NatWithZero.mul_l_identity (fold_right NatWithZero.mul (Positive One) l2))
      in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.multiplication_associativity
               a (fold_right NatWithZero.mul (Positive One) l1')
               (fold_right NatWithZero.mul (Positive One) l2)) in |- *.
    reflexivity.
Qed.

(* [count p l] is how many elements [p] answers [true] on. *)
Fixpoint count {A : Type} (p : A -> Bool) (l : List A) : NatWithZero :=
  match l with
  | Nil       => Zero
  | Cons a l' =>
      match p a with
      | true  => NatWithZero.add (count p l') (Positive One)
      | false => count p l'
      end
  end.

(* [count] is the length of the [filter]: the same case analysis on each
 * answer.
 *)
Theorem count_specification
  : forall (A : Type) (p : A -> Bool) (l : List A), count p l = length (filter p l).
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

(* [All] is monotone in its predicate: whatever holds of every element under
 * [P] holds under any [Q] that [P] implies.
 *)
Lemma all_monotonicity
  : forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (l : List A),
      (forall (a : A), P a -> Q a) -> All P l -> All Q l.
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

(* Insertion sort, relative to a comparison [le] that answers [true] when
 * its first argument may come first. [insert] walks past every element
 * that may precede [a] and puts [a] in front of the first that may not.
 *)
Fixpoint insert {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) : List A :=
  match l with
  | Nil       => Cons a Nil
  | Cons b l' =>
      match le a b with
      | true  => Cons a (Cons b l')
      | false => Cons b (insert le a l')
      end
  end.

Fixpoint insertion_sort {A : Type} (le : A -> A -> Bool) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' => insert le a (insertion_sort le l')
  end.

(* Sortedness: every element may precede all that follow it. Stated with
 * [All] rather than on neighbours, so that [insert] is checked one element
 * at a time.
 *)
Fixpoint Sorted {A : Type} (le : A -> A -> Bool) (l : List A) : Prop :=
  match l with
  | Nil       => Verum
  | Cons a l' => All (fun (b : A) => le a b = true) l' /\ Sorted le l'
  end.

(* Inserting an element every member of which satisfies [P] keeps [All P]. *)
Lemma insert_all_preservation
  : forall (A : Type) (le : A -> A -> Bool) (P : A -> Prop) (a : A) (l : List A),
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

(* Inserting into a sorted list keeps it sorted, given that the comparison
 * is total (either of two may come first) and transitive. Where [a] stops,
 * it precedes the head by the answer and the rest by transitivity; where it
 * walks on, the head precedes it by totality.
 *)
Lemma insert_sortedness
  : forall (A : Type) (le : A -> A -> Bool),
      (forall (a : A) (b : A), le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A),
         le a b = true -> le b c = true -> le a c = true) ->
      forall (a : A) (l : List A), Sorted le l -> Sorted le (insert le a l).
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
      pose proof (all_monotonicity A
                    (fun (x : A) => le b x = true) (fun (x : A) => le a x = true) l'
                    (fun (x : A) (h : le b x = true) => transitive a b x c h) below)
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
                 (insert_all_preservation A le (fun (x : A) => le b x = true) a l' ba below)
                 (IH sorted')).
Qed.

Theorem insertion_sort_sortedness
  : forall (A : Type) (le : A -> A -> Bool),
      (forall (a : A) (b : A), le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A),
         le a b = true -> le b c = true -> le a c = true) ->
      forall (l : List A), Sorted le (insertion_sort le l).
Proof.
  intros A le total transitive l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    exact I.
  - simpl in |- *.
    exact (insert_sortedness A le total transitive a (insertion_sort le l') IH).
Qed.

(* [insert] adds exactly its element to the members. *)

Lemma insert_containment_forward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      Contains b (insert le a l) -> b = a \/ Contains b l.
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
      * exact (Disjunction.right (Disjunction.left e)).
      * pose proof (IH h') as h''.
        destruct h'' as [e | h'''].
        { exact (Disjunction.left e). }
        { exact (Disjunction.right (Disjunction.right h''')). }
Qed.

Lemma insert_containment_backward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      b = a \/ Contains b l -> Contains b (insert le a l).
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
      * exact (Disjunction.right (IH (Disjunction.left e))).
      * destruct h' as [e | h''].
        { exact (Disjunction.left e). }
        { exact (Disjunction.right (IH (Disjunction.right h''))). }
Qed.

Theorem insert_containment
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      Contains b (insert le a l) <-> b = a \/ Contains b l.
Proof.
  intros A le a b l.
  split.
  - exact (insert_containment_forward  A le a b l).
  - exact (insert_containment_backward A le a b l).
Qed.

(* Sorting keeps the members: each insertion adds exactly the element the
 * step took off.
 *)

Lemma insertion_sort_containment_preservation_forward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a (insertion_sort le l) -> Contains a l.
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    intro h.
    pose proof (insert_containment_forward A le b a (insertion_sort le l') h) as h'.
    destruct h' as [e | h''].
    + exact (Disjunction.left e).
    + exact (Disjunction.right (IH h'')).
Qed.

Lemma insertion_sort_containment_preservation_backward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a l -> Contains a (insertion_sort le l).
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    intro h.
    apply (insert_containment_backward A le b a (insertion_sort le l')).
    destruct h as [e | h'].
    + exact (Disjunction.left e).
    + exact (Disjunction.right (IH h')).
Qed.

Theorem insertion_sort_containment_preservation
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a (insertion_sort le l) <-> Contains a l.
Proof.
  intros A le a l.
  split.
  - exact (insertion_sort_containment_preservation_forward  A le a l).
  - exact (insertion_sort_containment_preservation_backward A le a l).
Qed.

Lemma insert_length
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      length (insert le a l) = NatWithZero.add (length l) (Positive One).
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

Theorem insertion_sort_length_preservation
  : forall (A : Type) (le : A -> A -> Bool) (l : List A),
      length (insertion_sort le l) = length l.
Proof.
  intros A le l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (insert_length A le a (insertion_sort le l')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [Cons] and [Nil] are distinct ctors, as a statement. *)
Theorem cons_nil_distinctness
  : forall (A : Type) (a : A) (l : List A), ~ (Cons a l = Nil).
Proof.
  intros A a l.
  unfold Negation in |- *.
  intro e.
  discriminate e.
Qed.

(* [range n] is [Zero] up to but excluding [n], in that order: a positive
 * count recurses on its [Nat], each step putting the new last element
 * behind the ones before it.
 *)
(* [Nat -> List NatWithZero] *)
Fixpoint range_positive (p : Nat) : List NatWithZero :=
  match p with
  | One          => Cons Zero Nil
  | Successor p' => append (range_positive p') (Cons (Positive p') Nil)
  end.

(* [NatWithZero -> List NatWithZero] *)
Definition range := fun (n : NatWithZero) =>
  match n with
  | Zero       => Nil
  | Positive p => range_positive p
  end.

Lemma length_range_positive
  : forall (p : Nat), length (range_positive p) = Positive p.
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (length_additivity_over_append
               (range_positive p') (Cons (Positive p') Nil)) in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    rewrite (Nat.addition_commutativity p' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem length_range : forall (n : NatWithZero), length (range n) = n.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (length_range_positive p).
Qed.

(* The members of [range n] are exactly the numbers below [n]. Each step
 * adds one element at the end, and strictly below one more than
 * [Positive p'] is at most [Positive p']: the old members by [IH], the new
 * one by equality.
 *)

Lemma range_positive_containment_forward
  : forall (p : Nat) (i : NatWithZero),
      Contains i (range_positive p) -> NatWithZero.LessThan i (Positive p).
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
    pose proof (Biimplication.forward_elimination
                  (contains_distributivity_over_append
                     NatWithZero i (range_positive p') (Cons (Positive p') Nil))
                  h) as h'.
    change (Positive (Successor p'))
      with (NatWithZero.add (Positive One) (Positive p')) in |- *.
    rewrite (NatWithZero.addition_commutativity (Positive One) (Positive p')) in |- *.
    apply (Biimplication.backward_elimination
             (NatWithZero.lt_add_one_specification i (Positive p'))).
    unfold NatWithZero.LessOrEqual in |- *.
    destruct h' as [h1 | h2].
    + exact (Disjunction.right (IH i h1)).
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.left e).
      * contradiction f.
Qed.

Lemma range_positive_containment_backward
  : forall (p : Nat) (i : NatWithZero),
      NatWithZero.LessThan i (Positive p) -> Contains i (range_positive p).
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - intros i h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    destruct i as [| q].
    + simpl in |- *.
      exact (Disjunction.left (Identity.reflexivity Zero)).
    + simpl in e.
      pose proof (NatWithZero.positive_injectivity (Nat.add q k) One e) as e'.
      destruct q as [| q'].
      * simpl in e'.
        discriminate e'.
      * simpl in e'.
        discriminate e'.
  - intros i h.
    change (Positive (Successor p'))
      with (NatWithZero.add (Positive One) (Positive p')) in h.
    rewrite (NatWithZero.addition_commutativity (Positive One) (Positive p')) in h.
    pose proof (Biimplication.forward_elimination
                  (NatWithZero.lt_add_one_specification i (Positive p')) h)
      as h'.
    simpl in |- *.
    apply (Biimplication.backward_elimination
             (contains_distributivity_over_append
                NatWithZero i (range_positive p') (Cons (Positive p') Nil))).
    unfold NatWithZero.LessOrEqual in h'.
    destruct h' as [e | lt].
    + apply Disjunction.right.
      simpl in |- *.
      exact (Disjunction.left e).
    + exact (Disjunction.left (IH i lt)).
Qed.

Theorem range_containment_specification
  : forall (n : NatWithZero) (i : NatWithZero),
      Contains i (range n) <-> NatWithZero.LessThan i n.
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
      pose proof (NatWithZero.addition_positive_refutes_zero i k) as r.
      unfold Negation in r.
      pose proof (r e) as f.
      contradiction f.
  - simpl in |- *.
    split.
    + exact (range_positive_containment_forward  p i).
    + exact (range_positive_containment_backward p i).
Qed.

(* The largest member of a list, [Zero] for [Nil]: [fold_right] over the
 * [max] monoid.
 *)
(* [List NatWithZero -> NatWithZero] *)
Definition maximum_of := fun (l : List NatWithZero) => fold_right NatWithZero.max Zero l.

(* Every member is at most the maximum: the head by the left injection,
 * the rest through the right injection and transitivity.
 *)
Theorem maximum_of_upper_bound
  : forall (l : List NatWithZero),
      All (fun (a : NatWithZero) => NatWithZero.LessOrEqual a (maximum_of l)) l.
Proof.
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    exact I.
  - simpl in |- *.
    split.
    + exact (Comparable.max_l_injection a (fold_right NatWithZero.max Zero l')).
    + exact (all_monotonicity NatWithZero
               (fun (x : NatWithZero) =>
                  NatWithZero.LessOrEqual x (fold_right NatWithZero.max Zero l'))
               (fun (x : NatWithZero) =>
                  NatWithZero.LessOrEqual x
                    (NatWithZero.max a (fold_right NatWithZero.max Zero l')))
               l'
               (fun (x : NatWithZero)
                    (h : NatWithZero.LessOrEqual x (fold_right NatWithZero.max Zero l')) =>
                  Comparable.le_transitivity
                    x (fold_right NatWithZero.max Zero l')
                    (NatWithZero.max a (fold_right NatWithZero.max Zero l'))
                    h
                    (Comparable.max_r_injection
                       a (fold_right NatWithZero.max Zero l')))
               IH).
Qed.

(* A non-empty list contains its maximum: the head when the maximum of the
 * tail is at most it, and otherwise that maximum, a member of the tail by
 * [IH].
 *)
Theorem maximum_of_containment
  : forall (l : List NatWithZero), ~ (l = Nil) -> Contains (maximum_of l) l.
Proof.
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - intro h.
    unfold Negation in h.
    pose proof (h (Identity.reflexivity Nil)) as f.
    contradiction f.
  - intro h.
    destruct l' as [| b l''].
    + simpl in |- *.
      rewrite (NatWithZero.max_r_identity a) in |- *.
      exact (Disjunction.left (Identity.reflexivity a)).
    + pose proof (IH (cons_nil_distinctness NatWithZero b l'')) as c.
      change (NatWithZero.max a (fold_right NatWithZero.max Zero (Cons b l'')) = a
              \/ Contains (NatWithZero.max a (fold_right NatWithZero.max Zero (Cons b l'')))
                          (Cons b l'')) in |- *.
      pose proof (Comparable.le_totality
                    (fold_right NatWithZero.max Zero (Cons b l'')) a) as t.
      destruct t as [le | ge].
      * apply Disjunction.left.
        exact (Biimplication.backward_elimination
                 (Comparable.max_specification
                    a (fold_right NatWithZero.max Zero (Cons b l''))) le).
      * apply Disjunction.right.
        rewrite (Comparable.max_commutativity
                   a (fold_right NatWithZero.max Zero (Cons b l''))) in |- *.
        rewrite (Biimplication.backward_elimination
                   (Comparable.max_specification
                      (fold_right NatWithZero.max Zero (Cons b l'')) a) ge) in |- *.
        exact c.
Qed.

(* The smallest member, [None] for [Nil]: the head alone, or the [min] of
 * the head and the smallest of the tail. No identity is available for
 * [min], so the empty case is an [Option].
 *)
(* [List NatWithZero -> Option NatWithZero] *)
Fixpoint minimum_of (l : List NatWithZero) : Option NatWithZero :=
  match l with
  | Nil       => None
  | Cons a l' =>
      match minimum_of l' with
      | None   => Some a
      | Some m => Some (NatWithZero.min a m)
      end
  end.

Lemma minimum_of_none_specification
  : forall (l : List NatWithZero), minimum_of l = None <-> l = Nil.
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

(* The minimum is at most every member: [IH] bounds the tail by its own
 * minimum, and [min] is at most both its arguments.
 *)
Theorem minimum_of_lower_bound
  : forall (l : List NatWithZero) (m : NatWithZero),
      minimum_of l = Some m
      -> All (fun (a : NatWithZero) => NatWithZero.LessOrEqual m a) l.
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
      pose proof (Biimplication.forward_elimination
                    (minimum_of_none_specification l') r) as en.
      pose proof (Option.some_injectivity NatWithZero a m e) as e'.
      rewrite en in |- *.
      rewrite e' in |- *.
      simpl in |- *.
      exact (Conjunction_introduction (Comparable.le_reflexivity m) I).
    + simpl in e.
      pose proof (Option.some_injectivity NatWithZero (NatWithZero.min a m') m e) as e'.
      pose proof (Identity.symmetry e') as e''.
      rewrite e'' in |- *.
      simpl in |- *.
      split.
      * exact (Comparable.min_l_projection a m').
      * exact (all_monotonicity NatWithZero
                 (fun (x : NatWithZero) => NatWithZero.LessOrEqual m' x)
                 (fun (x : NatWithZero) => NatWithZero.LessOrEqual (NatWithZero.min a m') x)
                 l'
                 (fun (x : NatWithZero) (h : NatWithZero.LessOrEqual m' x) =>
                    Comparable.le_transitivity
                      (NatWithZero.min a m') m' x
                      (Comparable.min_r_projection a m') h)
                 (IH m' (Identity.reflexivity (Some m')))).
Qed.

(* A list contains its minimum: the head when the tail is empty or its
 * minimum is not below the head, and otherwise that minimum, a member of
 * the tail by [IH].
 *)
Theorem minimum_of_containment
  : forall (l : List NatWithZero) (m : NatWithZero),
      minimum_of l = Some m -> Contains m l.
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
      pose proof (Option.some_injectivity NatWithZero a m e) as e'.
      simpl in |- *.
      exact (Disjunction.left (Identity.symmetry e')).
    + simpl in e.
      pose proof (Option.some_injectivity NatWithZero (NatWithZero.min a m') m e) as e'.
      pose proof (Identity.symmetry e') as e''.
      rewrite e'' in |- *.
      simpl in |- *.
      pose proof (Comparable.le_totality a m') as t.
      destruct t as [le | ge].
      * apply Disjunction.left.
        exact (Biimplication.backward_elimination
                 (Comparable.min_specification a m') le).
      * apply Disjunction.right.
        rewrite (Comparable.min_commutativity a m') in |- *.
        rewrite (Biimplication.backward_elimination
                   (Comparable.min_specification m' a) ge) in |- *.
        exact (IH m' (Identity.reflexivity (Some m'))).
Qed.

(* The closed form of the sum of [Zero] up to [p]: twice it is [p] times
 * one more. Each step adds the new last element at the end of the range,
 * distributivity splits the doubled sum, and the two products join into
 * the next one. The sum of the one added element is written out by
 * [change], since [simpl] would also open [range_positive] one level too
 * far for [IH].
 *)
Theorem sum_range_closed_form
  : forall (p : Nat),
      NatWithZero.mul (Positive (Successor One)) (sum (range (Positive (Successor p))))
      = NatWithZero.mul (Positive p) (Positive (Successor p)).
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - unfold sum in |- *.
    simpl in |- *.
    reflexivity.
  - change (range (Positive (Successor (Successor p'))))
      with (append (range (Positive (Successor p'))) (Cons (Positive (Successor p')) Nil))
      in |- *.
    rewrite (sum_additivity_over_append
               (range (Positive (Successor p'))) (Cons (Positive (Successor p')) Nil))
      in |- *.
    change (sum (Cons (Positive (Successor p')) Nil)) with (Positive (Successor p')) in |- *.
    rewrite (NatWithZero.mul_l_distributivity_over_addition
               (Positive (Successor One))
               (sum (range (Positive (Successor p')))) (Positive (Successor p'))) in |- *.
    rewrite IH in |- *.
    pose proof (Identity.symmetry
                  (NatWithZero.mul_r_distributivity_over_addition
                     (Positive (Successor p')) (Positive p') (Positive (Successor One))))
      as d.
    rewrite d in |- *.
    change (NatWithZero.add (Positive p') (Positive (Successor One)))
      with (Positive (Nat.add p' (Successor One))) in |- *.
    rewrite (Nat.addition_commutativity p' (Successor One)) in |- *.
    change (Nat.add (Successor One) p') with (Successor (Successor p')) in |- *.
    rewrite (NatWithZero.multiplication_commutativity
               (Positive (Successor p')) (Positive (Successor (Successor p')))) in |- *.
    reflexivity.
Qed.

(* [count] answers [Zero] exactly when [p] answers [false] on every
 * member.
 *)
Theorem count_all_specification
  : forall (A : Type) (p : A -> Bool) (l : List A),
      count p l = Zero <-> All (fun (a : A) => p a = false) l.
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
        pose proof (NatWithZero.addition_positive_refutes_zero (count p l') One) as r.
        unfold Negation in r.
        pose proof (r e) as f.
        contradiction f.
      * intro c.
        destruct c as [e f].
        discriminate e.
    + simpl in |- *.
      split.
      * intro e.
        exact (Conjunction_introduction
                 (Identity.reflexivity false)
                 (Biimplication.forward_elimination IH e)).
      * intro c.
        destruct c as [e all'].
        exact (Biimplication.backward_elimination IH all').
Qed.

End List.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * Declared at file level, it reaches a client through [Require Export].
 * Every list notation lives in [jwa_list_scope], which [Core.Notations]
 * declares without opening: a client writes [(l1 ++ l2)%list] or opens the
 * scope.
 *)
Notation "l1 ++ l2" := (List.append l1 l2)
  : jwa_list_scope.

(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil
  : jwa_list_scope.

(* [a :: l] puts one element in front; with [[]] it spells a list out:
 * [a :: b :: []].
 *)
Notation "a :: l" := (Cons a l)
  : jwa_list_scope.

(* Membership reads as a sentence, [l contains_member a], with the list
 * first; the arguments of [Contains] are the other way round, element
 * first, so that [Contains a] is a predicate on lists.
 *)
Notation "l 'contains_member' a" := (List.Contains a l)
  : jwa_list_scope.

(* The same relation read from the element's side. [only parsing] keeps one
 * spelling for printing, so a goal always shows [l contains_member a].
 *)
Notation "a 'belongs_to' l" := (List.Contains a l) (only parsing)
  : jwa_list_scope.

(* The negations, so that [~ Contains a l] reads and prints as a sentence
 * too; the element-first form is again [only parsing].
 *)
Notation "l 'does_not_contain_member' a" := (~ (List.Contains a l))
  : jwa_list_scope.
Notation "a 'does_not_belong_to' l" := (~ (List.Contains a l)) (only parsing)
  : jwa_list_scope.

(* [append] with [Nil] is the monoid on lists. [A] is a parameter of the
 * instance, so every element type gets one; [@] makes it explicit where
 * the operation and the laws are handed over unapplied.
 *)
Instance List_append_monoid
  : forall (A : Type), Monoid (@List.append A) Nil :=
  fun (A : Type) =>
    {| Monoid.semigroup :=
         {| Semigroup.associativity := @List.append_associativity A |}
     ; Monoid.identity := @List.append_identity A |}.

(* The two functor laws were already proved above, so the instance only
 * hands them over. [map]'s type arguments are maximally inserted, so the
 * bare name collapses to one fixed pair of them; binding [A] and [B] first
 * is what keeps it general enough for the field, as in [Data.Option].
 *)
Instance List_functor
  : Functor List :=
  {| Functor.map             := fun (A : Type) (B : Type) => List.map
   ; Functor.map_identity    := List.map_identity
   ; Functor.map_composition := List.map_composition |}.
