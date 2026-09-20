(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Collection.Sized.
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

(* A module may carry the type's name; its members read [List.append]. *)
Module List.

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

Theorem cons_nil_distinctness
  : forall {A : Type} (a : A) (l : List A) . ~ (a :: l = []).
Proof.
  intros A a l.
  unfold Negation in |- *.
  intro e.
  discriminate e.
Qed.

(* Append *)

(* Recursion is on the first list: [append Nil l2] is [l2], and each [Cons]
 * of [l1] is put back in front of the result.
 *)
(* [forall {A : Type} . List A -> List A -> List A] *)
Fixpoint append {A : Type} (l1 : List A) (l2 : List A) : List A :=
  match l1 with
  | []       => l2
  | a :: l1' => a :: append l1' l2
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * After [End List] a client writes [(l1 ++ l2)%list] or opens
 * [jwa_list_scope].
 *)
Notation "l1 ++ l2" := (append l1 l2)
  : jwa_list_scope.

Theorem append_associativity
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

Lemma append_left_identity : forall {A : Type} (l : List A) . [] ++ l = l.
Proof.
  intros A l.
  simpl in |- *.
  reflexivity.
Qed.

Lemma append_right_identity : forall {A : Type} (l : List A) . l ++ [] = l.
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
  : forall {A : Type} (l : List A) . ([] ++ l = l) /\ (l ++ [] = l).
Proof.
  intros A l.
  split.
  - exact (append_left_identity  l).
  - exact (append_right_identity l).
Qed.

(* Length *)

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

Theorem length_additivity_over_append
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

(* Map *)

(* [map] applies [f] to every element and keeps the shape. *)
(* [forall {A : Type} {B : Type} . (A -> B) -> List A -> List B] *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | []      => []
  | a :: l' => f a :: map f l'
  end.

Theorem map_identity
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

Theorem map_composition
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

Theorem map_distributivity_over_append
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

(* Reverse *)

(* [reverse] moves each element to the end of the reversed rest. Quadratic,
 * and the simplest shape for the proofs below; an accumulator version can
 * come with a proof that it agrees.
 *)
(* [forall {A : Type} . List A -> List A] *)
Fixpoint reverse {A : Type} (l : List A) : List A :=
  match l with
  | []      => []
  | a :: l' => reverse l' ++ (a :: [])
  end.

Theorem reverse_antidistributivity_over_append
  : forall {A : Type} (l1 : List A) (l2 : List A) .
      reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
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
  : forall {A : Type} (l : List A) . reverse (reverse l) = l.
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

(* Folding *)

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

Theorem fold_right_composition_over_append
  : forall {A : Type} {B : Type} (f : A -> B -> B) (z : B)
      (l1 : List A) (l2 : List A) .
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

Theorem append_catamorphism
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

Theorem length_catamorphism
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

Theorem map_catamorphism
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

(* Containment *)

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

Theorem nil_contains_nothing
  : forall {A : Type} (a : A) . [] does_not_contain_member a.
Proof.
  intros A a.
  unfold Negation in |- *.
  simpl in |- *.
  intro f.
  exact f.
Qed.

Lemma contains_distributivity_over_append_forward
  : forall {A : Type} (a : A) (l1 : List A) (l2 : List A) .
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

Lemma contains_distributivity_over_append_backward
  : forall {A : Type} (a : A) (l1 : List A) (l2 : List A) .
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

Theorem contains_distributivity_over_append
  : forall {A : Type} (a : A) (l1 : List A) (l2 : List A) .
      l1 ++ l2 contains_member a <-> l1 contains_member a \/ l2 contains_member a.
Proof.
  intros A a l1 l2.
  split.
  - exact (contains_distributivity_over_append_forward a l1 l2).
  - exact (contains_distributivity_over_append_backward a l1 l2).
Qed.

(* [map] carries membership along: an element of [l] has its image in
 * [map f l].
 *)
Theorem map_containment_preservation
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

Lemma reverse_containment_preservation_forward
  : forall {A : Type} (a : A) (l : List A) .
      reverse l contains_member a -> l contains_member a.
Proof.
  intros A a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro f.
    exact f.
  - simpl in |- *.
    intro h.
    destruct (contains_distributivity_over_append_forward
                a (reverse l') (b :: []) h) as [h1 | h2].
    + apply Disjunction.R.
      apply IH.
      exact h1.
    + simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.L e).
      * contradiction f.
Qed.

Lemma reverse_containment_preservation_backward
  : forall {A : Type} (a : A) (l : List A) .
      l contains_member a -> reverse l contains_member a.
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
    + apply Disjunction.R.
      simpl in |- *.
      exact (Disjunction.L e).
    + apply Disjunction.L.
      apply IH.
      exact h'.
Qed.

Theorem reverse_containment_preservation
  : forall {A : Type} (a : A) (l : List A) .
      reverse l contains_member a <-> l contains_member a.
Proof.
  intros A a l.
  split.
  - exact (reverse_containment_preservation_forward  a l).
  - exact (reverse_containment_preservation_backward a l).
Qed.

(* Filter *)

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

Theorem filter_distributivity_over_append
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

(* [filter] is a catamorphism too: [Cons] becomes a conditional [Cons]. *)
Theorem filter_catamorphism
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

Lemma filter_specification_forward
  : forall {A : Type} (p : A -> Bool) (a : A) (l : List A) .
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

Lemma filter_specification_backward
  : forall {A : Type} (p : A -> Bool) (a : A) (l : List A) .
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

Theorem filter_specification
  : forall {A : Type} (p : A -> Bool) (a : A) (l : List A) .
      filter p l contains_member a <-> l contains_member a /\ p a = true.
Proof.
  intros A p a l.
  split.
  - exact (filter_specification_forward p a l).
  - exact (filter_specification_backward p a l).
Qed.

(* Quantification *)

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

(* [All] over a concatenation is [All] over each half. *)
Lemma all_distributivity_over_append_forward
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
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

Lemma all_distributivity_over_append_backward
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
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

Theorem all_distributivity_over_append
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
      All P (l1 ++ l2) <-> All P l1 /\ All P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (all_distributivity_over_append_forward P l1 l2).
  - exact (all_distributivity_over_append_backward P l1 l2).
Qed.

(* [Any] over a concatenation is [Any] over either half. *)
Lemma any_distributivity_over_append_forward
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
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

Lemma any_distributivity_over_append_backward
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
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

Theorem any_distributivity_over_append
  : forall {A : Type} (P : A -> Prop) (l1 : List A) (l2 : List A) .
      Any P (l1 ++ l2) <-> Any P l1 \/ Any P l2.
Proof.
  intros A P l1 l2.
  split.
  - exact (any_distributivity_over_append_forward P l1 l2).
  - exact (any_distributivity_over_append_backward P l1 l2).
Qed.

Lemma all_specification_forward
  : forall {A : Type} (P : A -> Prop) (l : List A) .
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

Lemma all_specification_backward
  : forall {A : Type} (P : A -> Prop) (l : List A) .
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

Theorem all_specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      All P l <-> (forall (a : A) . l contains_member a -> P a).
Proof.
  intros A P l.
  split.
  - exact (all_specification_forward P l).
  - exact (all_specification_backward P l).
Qed.

Lemma any_specification_forward
  : forall {A : Type} (P : A -> Prop) (l : List A) .
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

Lemma any_specification_backward
  : forall {A : Type} (P : A -> Prop) (l : List A) .
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

Theorem any_specification
  : forall {A : Type} (P : A -> Prop) (l : List A) .
      Any P l <-> (exists (a : A) . l contains_member a /\ P a).
Proof.
  intros A P l.
  split.
  - exact (any_specification_forward P l).
  - exact (any_specification_backward P l).
Qed.

Lemma all_monotonicity
  : forall {A : Type} (P : A -> Prop) (Q : A -> Prop) (l : List A) .
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

Theorem contains_catamorphism
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

Theorem all_catamorphism
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

Theorem any_catamorphism
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

(* Head and tail *)

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

Lemma head_specification_forward
  : forall {A : Type} (a : A) (l : List A) .
      head l = Some a -> exists (l' : List A) . l = a :: l'.
Proof.
  intros A a l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity b a e) as e'.
    apply (Exists_introduction rest).
    rewrite e' in |- *.
    reflexivity.
Qed.

Lemma head_specification_backward
  : forall {A : Type} (a : A) (l : List A) .
      (exists (l' : List A) . l = a :: l') -> head l = Some a.
Proof.
  intros A a l.
  intro h.
  destruct h as [l' e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem head_specification
  : forall {A : Type} (a : A) (l : List A) .
      head l = Some a <-> (exists (l' : List A) . l = a :: l').
Proof.
  intros A a l.
  split.
  - exact (head_specification_forward a l).
  - exact (head_specification_backward a l).
Qed.

Lemma tail_specification_forward
  : forall {A : Type} (l : List A) (l' : List A) .
      tail l = Some l' -> exists (a : A) . l = a :: l'.
Proof.
  intros A l l'.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity rest l' e) as e'.
    apply (Exists_introduction b).
    rewrite e' in |- *.
    reflexivity.
Qed.

Lemma tail_specification_backward
  : forall {A : Type} (l : List A) (l' : List A) .
      (exists (a : A) . l = a :: l') -> tail l = Some l'.
Proof.
  intros A l l'.
  intro h.
  destruct h as [a e].
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

Theorem tail_specification
  : forall {A : Type} (l : List A) (l' : List A) .
      tail l = Some l' <-> (exists (a : A) . l = a :: l').
Proof.
  intros A l l'.
  split.
  - exact (tail_specification_forward l l').
  - exact (tail_specification_backward l l').
Qed.

(* [forall {A : Type} . List A -> Option A] *)
Definition last := fun {A : Type} (l : List A) . head (reverse l).

(* [forall {A : Type} . List A -> Option (List A)] *)
Definition initial := fun {A : Type} (l : List A) . Option.map reverse (tail (reverse l)).

Lemma last_specification_forward
  : forall {A : Type} (a : A) (l : List A) .
      last l = Some a -> exists (l' : List A) . l = l' ++ (a :: []).
Proof.
  intros A a l.
  unfold last in |- *.
  intro h.
  destruct (head_specification_forward a (reverse l) h) as [r e].
  apply (Exists_introduction (reverse r)).
  pose proof (Identity.congruence reverse e) as e'.
  rewrite reverse_involution in e'.
  simpl in e'.
  exact e'.
Qed.

Lemma last_specification_backward
  : forall {A : Type} (a : A) (l : List A) .
      (exists (l' : List A) . l = l' ++ (a :: [])) -> last l = Some a.
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
  : forall {A : Type} (a : A) (l : List A) .
      last l = Some a <-> (exists (l' : List A) . l = l' ++ (a :: [])).
Proof.
  intros A a l.
  split.
  - exact (last_specification_forward  a l).
  - exact (last_specification_backward a l).
Qed.

Lemma initial_specification_forward
  : forall {A : Type} (l : List A) (l' : List A) .
      initial l = Some l' -> exists (a : A) . l = l' ++ (a :: []).
Proof.
  intros A l l'.
  unfold initial in |- *.
  destruct (reverse l) as [| b r] eqn:er.
  - simpl in |- *.
    intro h.
    discriminate h.
  - simpl in |- *.
    intro h.
    pose proof (Option.some.injectivity (reverse r) l' h) as e'.
    apply (Exists_introduction b).
    pose proof (Identity.congruence reverse er) as er'.
    rewrite reverse_involution in er'.
    simpl in er'.
    rewrite e' in er'.
    exact er'.
Qed.

Lemma initial_specification_backward
  : forall {A : Type} (l : List A) (l' : List A) .
      (exists (a : A) . l = l' ++ (a :: [])) -> initial l = Some l'.
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
  : forall {A : Type} (l : List A) (l' : List A) .
      initial l = Some l' <-> (exists (a : A) . l = l' ++ (a :: [])).
Proof.
  intros A l l'.
  split.
  - exact (initial_specification_forward  l l').
  - exact (initial_specification_backward l l').
Qed.

(* [head] and [tail] in one answer: [None] on the empty list, else the
 * first element paired with the rest.
 *)
(* [forall {A : Type} . List A -> Option (A * List A)] *)
Definition pop := fun {A : Type} (l : List A) .
  match l return Option (A * List A) with
  | []      => None
  | a :: l' => Some (Product_introduction a l')
  end.

Lemma pop_specification_forward
  : forall {A : Type} (a : A) (l' : List A) (l : List A) .
      pop l = Some (Product_introduction a l') -> l = a :: l'.
Proof.
  intros A a l' l.
  destruct l as [| b rest].
  - simpl in |- *.
    intro e.
    discriminate e.
  - simpl in |- *.
    intro e.
    pose proof (Option.some.injectivity
                  (Product_introduction b rest) (Product_introduction a l') e) as e'.
    pose proof (Product.introduction_injectivity A (List A) b rest a l' e') as e''.
    destruct e'' as [eb erest].
    rewrite eb in |- *.
    rewrite erest in |- *.
    reflexivity.
Qed.

Lemma pop_specification_backward
  : forall {A : Type} (a : A) (l' : List A) (l : List A) .
      l = a :: l' -> pop l = Some (Product_introduction a l').
Proof.
  intros A a l' l e.
  rewrite e in |- *.
  simpl in |- *.
  reflexivity.
Qed.

(* [pop] answers [Some (a , l')] exactly on [Cons a l']. *)
Theorem pop_specification
  : forall {A : Type} (a : A) (l' : List A) (l : List A) .
      pop l = Some (Product_introduction a l') <-> l = a :: l'.
Proof.
  intros A a l' l.
  split.
  - exact (pop_specification_forward a l' l).
  - exact (pop_specification_backward a l' l).
Qed.

(* Projecting a [pop] gives back [head] and [tail]. *)

Theorem pop_head_projection
  : forall {A : Type} (l : List A) . Option.map Product.first (pop l) = head l.
Proof.
  intros A l.
  destruct l as [| a l'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

Theorem pop_tail_projection
  : forall {A : Type} (l : List A) . Option.map Product.second (pop l) = tail l.
Proof.
  intros A l.
  destruct l as [| a l'].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    reflexivity.
Qed.

(* Zip *)

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

(* Zipping the two halves of an [unzip] rebuilds the list. The other order,
 * [unzip (zip l1 l2)], needs the two lists to be of one length.
 *)
Theorem zip_unzip_identity
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
    rewrite <- (Product.introduction_surjectivity A B p) in |- *.
    reflexivity.
Qed.

(* Unzipping a [zip] gives the two lists back when they are of one length;
 * [zip] stops with the shorter list, so a longer one is not recovered.
 * Induction on [l1] with [l2] kept in the motive, since [zip] and
 * [length] step on both lists at once; the two mismatched cases contradict
 * [NatWithZero.addition.right.identity.absence] and the matched case feeds the
 * hypothesis through [NatWithZero.addition.left.cancellation].
 *)
Theorem unzip_zip_identity
  : forall {A : Type} {B : Type} (l1 : List A) (l2 : List B) .
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
      pose proof (h e') as f.
      contradiction f.
  - intros l2 e.
    destruct l2 as [| b l2'].
    + simpl in e.
      rewrite (NatWithZero.increment.specification (|| l1' ||)) in e.
      rewrite (NatWithZero.addition.commutativity (Positive One) (|| l1' ||)) in e.
      pose proof (NatWithZero.addition.right.identity.absence (|| l1' ||) One) as h.
      unfold Negation in h.
      pose proof (h e) as f.
      contradiction f.
    + simpl in e.
      rewrite (NatWithZero.increment.specification (|| l1' ||)) in e.
      rewrite (NatWithZero.increment.specification (|| l2' ||)) in e.
      pose proof (NatWithZero.addition.left.cancellation
                    (Positive One) (|| l1' ||) (|| l2' ||) e) as e'.
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

(* [zip] stops with the shorter list, so its length is the smaller of the
 * two; each step adds one to both, and addition distributes over [min].
 *)
Theorem length_zip
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

(* Partition *)

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

(* The two halves of a [partition] are the two [filter]s, by [p] and by its
 * negation.
 *)
Theorem partition_specification
  : forall {A : Type} (p : A -> Bool) (l : List A) .
      partition p l
      = Product_introduction (filter p l)
                          (filter (fun (a : A) . ! p a) l).
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

(* Indexing *)

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

(* [nth] answers exactly for the indices below the length. Each step of the
 * index is one step of the list, so the halves lift [IH] through
 * [Positive One] added on both sides of the order.
 *)

Lemma nth_specification_forward
  : forall {A : Type} (l : List A) (i : NatWithZero) .
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

Lemma nth_specification_backward
  : forall {A : Type} (l : List A) (i : NatWithZero) .
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
    pose proof (r e) as f.
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

Theorem nth_specification
  : forall {A : Type} (l : List A) (i : NatWithZero) .
      (exists (a : A) . nth l i = Some a) <-> i < (|| l ||).
Proof.
  intros A l i.
  split.
  - exact (nth_specification_forward  l i).
  - exact (nth_specification_backward l i).
Qed.

(* Take and drop *)

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

(* The two parts put back together give the list. *)
Theorem take_drop_decomposition
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

(* The length of a [take] is the smaller of the count and the length; each
 * step adds one to both candidates, and addition distributes over [min].
 *)
Theorem length_take
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

(* The length of a [drop] is the length less the count; each step takes one
 * from both, which truncated subtraction ignores.
 *)
Theorem length_drop
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

(* Replicate *)

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

Lemma length_replicate_positive
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

Theorem length_replicate
  : forall {A : Type} (n : NatWithZero) (a : A) . (|| replicate n a ||) = n.
Proof.
  intros A n a.
  destruct n as [| k].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (length_replicate_positive k a).
Qed.

(* Sum and product *)

(* [List NatWithZero -> NatWithZero] *)
Definition sum := fun (l : List NatWithZero) . fold_right NatWithZero.add Zero l.

(* [List NatWithZero -> NatWithZero] *)
Definition product := fun (l : List NatWithZero) .
  fold_right NatWithZero.mul (Positive One) l.

Theorem sum_additivity_over_append
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

Theorem product_multiplicativity_over_append
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero) .
      product (l1 ++ l2) = product l1 * product l2.
Proof.
  intros l1 l2.
  unfold product in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - rewrite (append_left_identity l2) in |- *.
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

(* Count *)

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

Theorem count_specification
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

(* [count] answers [Zero] exactly when [p] answers [false] on every
 * member.
 *)
Theorem count_all_specification
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
                 (->elim IH e)).
      * intro c.
        destruct c as [e all'].
        exact (<-elim IH all').
Qed.

(* Sorting *)

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

Lemma insert_all_preservation
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

Lemma insert_sortedness
  : forall {A : Type} (le : A -> A -> Bool) .
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
      pose proof (all_monotonicity
                    (fun (x : A) . le b x = true) (fun (x : A) . le a x = true) l'
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
                 (insert_all_preservation le (fun (x : A) . le b x = true) a l' ba below)
                 (IH sorted')).
Qed.

Theorem insertion_sort_sortedness
  : forall {A : Type} (le : A -> A -> Bool) .
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
    exact (insert_sortedness le total transitive a (insertion_sort le l') IH).
Qed.

(* [insert] adds exactly its element to the members. *)

Lemma insert_containment_forward
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
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
      * pose proof (IH h') as h''.
        destruct h'' as [e | h'''].
        { exact (Disjunction.L e). }
        { exact (Disjunction.R (Disjunction.R h''')). }
Qed.

Lemma insert_containment_backward
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

Theorem insert_containment
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (b : A) (l : List A) .
      insert le a l contains_member b <-> b = a \/ l contains_member b.
Proof.
  intros A le a b l.
  split.
  - exact (insert_containment_forward  le a b l).
  - exact (insert_containment_backward le a b l).
Qed.

Lemma insertion_sort_containment_preservation_forward
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      insertion_sort le l contains_member a -> l contains_member a.
Proof.
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - simpl in |- *.
    intro h.
    exact h.
  - simpl in |- *.
    intro h.
    pose proof (insert_containment_forward le b a (insertion_sort le l') h) as h'.
    destruct h' as [e | h''].
    + exact (Disjunction.L e).
    + exact (Disjunction.R (IH h'')).
Qed.

Lemma insertion_sort_containment_preservation_backward
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
    apply (insert_containment_backward le b a (insertion_sort le l')).
    destruct h as [e | h'].
    + exact (Disjunction.L e).
    + exact (Disjunction.R (IH h')).
Qed.

Theorem insertion_sort_containment_preservation
  : forall {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) .
      insertion_sort le l contains_member a <-> l contains_member a.
Proof.
  intros A le a l.
  split.
  - exact (insertion_sort_containment_preservation_forward  le a l).
  - exact (insertion_sort_containment_preservation_backward le a l).
Qed.

Lemma insert_length
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

Theorem insertion_sort_length_preservation
  : forall {A : Type} (le : A -> A -> Bool) (l : List A) .
      (|| insertion_sort le l ||) = (|| l ||).
Proof.
  intros A le l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (insert_length le a (insertion_sort le l')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* Range *)

(* [Nat -> List NatWithZero] *)
Fixpoint range_positive (p : Nat) : List NatWithZero :=
  match p with
  | One          => Zero :: []
  | Successor p' => range_positive p' ++ (Positive p' :: [])
  end.

(* [NatWithZero -> List NatWithZero] *)
Definition range := fun (n : NatWithZero) .
  match n with
  | Zero       => []
  | Positive p => range_positive p
  end.

Lemma length_range_positive
  : forall (p : Nat) . (|| range_positive p ||) = Positive p.
Proof.
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (length_additivity_over_append
               (range_positive p') (Positive p' :: [])) in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    rewrite (Nat.addition.commutativity p' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem length_range : forall (n : NatWithZero) . (|| range n ||) = n.
Proof.
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    exact (length_range_positive p).
Qed.

Lemma range_positive_containment_forward
  : forall (p : Nat) (i : NatWithZero) .
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
                  (contains_distributivity_over_append
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

Lemma range_positive_containment_backward
  : forall (p : Nat) (i : NatWithZero) .
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
      pose proof (NatWithZero.positive.injectivity (Nat.add q k) One e) as e'.
      destruct q as [| q']; simpl in e'; discriminate e'.
  - intros i h.
    change (Positive (Successor p'))
      with (Positive One + Positive p')
      in h.
    rewrite (NatWithZero.addition.commutativity (Positive One) (Positive p')) in h.
    pose proof (->elim (NatWithZero.order.discreteness i (Positive p')) h) as h'.
    simpl in |- *.
    apply (<-elim
             (contains_distributivity_over_append
                i (range_positive p') (Positive p' :: []))).
    unfold NatWithZero.LessOrEqual in h'.
    destruct h' as [e | lt].
    + apply Disjunction.R.
      simpl in |- *.
      exact (Disjunction.L e).
    + exact (Disjunction.L (IH i lt)).
Qed.

Theorem range_containment_specification
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
      pose proof (r e) as f.
      contradiction f.
  - simpl in |- *.
    split.
    + exact (range_positive_containment_forward  p i).
    + exact (range_positive_containment_backward p i).
Qed.

Theorem sum_range_closed_form
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
      with (range (Positive (Successor p')) ++ (Positive (Successor p') :: []))
      in |- *.
    rewrite (sum_additivity_over_append
               (range (Positive (Successor p'))) (Positive (Successor p') :: []))
      in |- *.
    change (sum (Positive (Successor p') :: [])) with (Positive (Successor p')) in |- *.
    rewrite (NatWithZero.multiplication.left.distributivity.over.addition
               (Positive (Successor One))
               (sum (range (Positive (Successor p')))) (Positive (Successor p'))) in |- *.
    rewrite IH in |- *.
    pose proof (Identity.symmetry
                  (NatWithZero.multiplication.right.distributivity.over.addition
                     (Positive (Successor p')) (Positive p') (Positive (Successor One))))
      as d.
    rewrite d in |- *.
    change (Positive p' + Positive (Successor One))
      with (Positive (Nat.add p' (Successor One))) in |- *.
    rewrite (Nat.addition.commutativity p' (Successor One)) in |- *.
    change (Nat.add (Successor One) p') with (Successor (Successor p')) in |- *.
    rewrite (NatWithZero.multiplication.commutativity
               (Positive (Successor p')) (Positive (Successor (Successor p')))) in |- *.
    reflexivity.
Qed.

(* Extrema *)

(* [List NatWithZero -> NatWithZero] *)
Definition maximum_of := fun (l : List NatWithZero) . fold_right NatWithZero.max Zero l.

Theorem maximum_of_upper_bound
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
    + exact (all_monotonicity
               (fun (x : NatWithZero) .
                  x <= fold_right NatWithZero.max Zero l')
               (fun (x : NatWithZero) .
                  x <= NatWithZero.max a (fold_right NatWithZero.max Zero l'))
               l'
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

Theorem maximum_of_containment
  : forall (l : List NatWithZero) . ~ (l = []) -> l contains_member maximum_of l.
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
    + pose proof (IH (cons_nil_distinctness b l'')) as c.
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

Lemma minimum_of_none_specification
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

Theorem minimum_of_lower_bound
  : forall (l : List NatWithZero) (m : NatWithZero) .
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
      pose proof (->elim (minimum_of_none_specification l') r) as en.
      pose proof (Option.some.injectivity a m e) as e'.
      rewrite en in |- *.
      rewrite e' in |- *.
      simpl in |- *.
      exact (Conjunction_introduction (Comparable.order.reflexivity m) I).
    + simpl in e.
      pose proof (Option.some.injectivity (NatWithZero.min a m') m e) as e'.
      symmetry in e'.
      rewrite e' in |- *.
      simpl in |- *.
      split.
      * exact (Comparable.minimum.left.projection a m').
      * exact (all_monotonicity
                 (fun (x : NatWithZero) . m' <= x)
                 (fun (x : NatWithZero) . NatWithZero.min a m' <= x)
                 l'
                 (fun (x : NatWithZero) (h : m' <= x) .
                    Comparable.order.transitivity
                      (NatWithZero.min a m') m' x
                      (Comparable.minimum.right.projection a m') h)
                 (IH m' (Identity.reflexivity (Some m')))).
Qed.

Theorem minimum_of_containment
  : forall (l : List NatWithZero) (m : NatWithZero) .
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
      pose proof (Option.some.injectivity a m e) as e'.
      simpl in |- *.
      exact (Disjunction.L (Identity.symmetry e')).
    + simpl in e.
      pose proof (Option.some.injectivity (NatWithZero.min a m') m e) as e'.
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

End List.

(* Makes the notations declared in [Module List] usable in every file that
 * imports this one, as [(l1 ++ l2)%list] or under an opened
 * [jwa_list_scope]. Only the notations are exported: [append] and the laws
 * still need the [List.] prefix. The ctor notations [[]] and [::] are
 * declared above the module and reach a client with the module itself.
 *)
Export (notations) List.

Instance List_append_monoid
  : forall {A : Type} . Monoid (@List.append A) Nil :=
  fun (A : Type) .
    ({| Monoid.semigroup :=
          {| Semigroup.associativity := @List.append_associativity A |}
      ; Monoid.identity := @List.append_identity A |}).

Instance List_functor
  : Functor List :=
  {| Functor.map             := fun (A : Type) (B : Type) . List.map
   ; Functor.map_identity    := @List.map_identity
   ; Functor.map_composition := @List.map_composition |}.

Instance List_sized
  : Sized List :=
  {| Sized.cardinality := @List.length |}.
