(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Collection.Membership.
From jwa Require Import Data.Collection.Sized.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Tactics.Modus.

(* A module may carry the type's name; its members read
 * [NonEmptyList.head]. The type and its ctors are declared inside it: a
 * ctor at the top level is rebound by any later file declaring the same
 * name, silently and with no warning.
 *)
Module NonEmptyList. (* NonEmptyList *)

(* A non-empty list is one element, or one element in front of a non-empty
 * list. It differs from [List] in one ctor: where a list ends with [Nil],
 * this ends with an element, so every value has a first element and the
 * operations that read one are total.
 *)
Inductive T (A : Type) : Type :=
  | One  : A -> T A
  | Cons : A -> T A -> T A.

(* [A] is inferred from the element in both ctors, so neither ever needs
 * writing out.
 *)
Arguments One  {A} a.
Arguments Cons {A} a x.

(* The carrier is named [T] so that the type itself reads [NonEmptyList] on
 * both sides of the module: here through this abbreviation, outside
 * through the one that follows [End NonEmptyList].
 *)
Abbreviation NonEmptyList := T.

(* The level is reserved in [Core.Notations]; only the meaning belongs
 * here. [List] gives the same token its own meaning in [jwa_list_scope],
 * so a reader says which is meant by opening a scope or by writing the
 * delimiter.
 *)
Notation "a :: x" := (Cons a x)
  : jwa_non_empty_list_scope.

(* [[a]] is the list of that one element, so a literal ends where [List]'s
 * ends with [[]]: [a :: b :: [c]] against [a :: b :: c :: []]. The
 * brackets are a closed token and take no level, as [[]] does not.
 *)
Notation "[ a ]" := (One a)
  : jwa_non_empty_list_scope.

(* Both scopes are open: [jwa_list_scope] for [to_list], whose result is a
 * [List], and this type's own for everything else. The one opened later
 * wins where a token is in both, so the [List] readings below carry their
 * delimiter.
 *)
Local Open Scope jwa_list_scope.
Local Open Scope jwa_non_empty_list_scope.

(* The eliminator behind the [induction] tactic, written out. Its content
 * is the [fix]: the proof for [Cons a x] is built from the proof for [x],
 * and following [x] down to [One] is what terminates.
 *)
Definition induction
  : forall (A : Type) (P : NonEmptyList A -> Prop) .
      (forall (a : A) . P (One a)) ->
      (forall (a : A) (x : NonEmptyList A) . P x -> P (Cons a x)) ->
      (forall (x : NonEmptyList A) . P x)
  := fun (A : Type) (P : NonEmptyList A -> Prop)
       (base : forall (a : A) . P (One a))
       (step : forall (a : A) (x : NonEmptyList A) . P x -> P (Cons a x)) .
       fix go (x : NonEmptyList A) : P x :=
         match x with
         | One a     => base a
         | Cons a x' => step a x' (go x')
         end.

(* [forall {A : Type} . NonEmptyList A -> A] *)
Definition head := fun {A : Type} (x : NonEmptyList A) .
  match x with
  | One  a   => a
  | Cons a _ => a
  end.

(* [forall {A : Type} . NonEmptyList A -> A] *)
Fixpoint last {A : Type} (x : NonEmptyList A) : A :=
  match x with
  | One  a    => a
  | Cons _ x' => last x'
  end.

(* The count is a [Nat] rather than a [NatWithZero]: no value of this type
 * holds nothing, so the zero would name a case that cannot arise.
 *)
(* [forall {A : Type} . NonEmptyList A -> Nat] *)
Fixpoint length {A : Type} (x : NonEmptyList A) : Nat :=
  match x with
  | One  _    => Nat.One
  | Cons _ x' => Nat.Successor (length x')
  end.

Notation "(|| x ||)" := (length x) (only parsing)
  : jwa_non_empty_list_scope.

(* The forgetful map into [List]: every operation of [List] is reachable
 * through it, and a law proved there transports along it.
 *)
(* [forall {A : Type} . NonEmptyList A -> List A] *)
Fixpoint to_list {A : Type} (x : NonEmptyList A) : List A :=
  match x with
  | One  a    => (a :: [])%list
  | Cons a x' => (a :: to_list x')%list
  end.

(* Joining two non-empty lists needs no empty case: the left one runs out
 * at an element, which is put in front of the right one.
 *)
(* [forall {A : Type} . NonEmptyList A -> NonEmptyList A -> NonEmptyList A] *)
Fixpoint concat {A : Type} (x : NonEmptyList A) (y : NonEmptyList A)
  : NonEmptyList A :=
  match x with
  | One  a    => a :: y
  | Cons a x' => a :: concat x' y
  end.

Notation "x ++ y" := (concat x y)
  : jwa_non_empty_list_scope.

(* [forall {A : Type} . NonEmptyList A -> NonEmptyList A] *)
Fixpoint reverse {A : Type} (x : NonEmptyList A) : NonEmptyList A :=
  match x with
  | One  a    => One a
  | Cons a x' => reverse x' ++ One a
  end.

(* Membership, defined by recursion into [Prop]: at [One b] there is one
 * element to be equal to, and at [Cons b x'] either that one or a member
 * of the rest.
 *)
(* [forall {A : Type} . A -> NonEmptyList A -> Prop] *)
Fixpoint Contains {A : Type} (a : A) (x : NonEmptyList A) : Prop :=
  match x with
  | One  b    => a = b
  | Cons b x' => a = b \/ Contains a x'
  end.

Notation "x 'contains_member' a" := (Contains a x)
  : jwa_non_empty_list_scope.

Notation "a 'belongs_to' x" := (Contains a x) (only parsing)
  : jwa_non_empty_list_scope.

Notation "x 'does_not_contain_member' a" := (~ (Contains a x))
  : jwa_non_empty_list_scope.

Notation "a 'does_not_belong_to' x" := (~ (Contains a x)) (only parsing)
  : jwa_non_empty_list_scope.

(* [forall {A : Type} {B : Type} . (A -> B) -> NonEmptyList A -> NonEmptyList B] *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (x : NonEmptyList A)
  : NonEmptyList B :=
  match x with
  | One  a    => One (f a)
  | Cons a x' => f a :: map f x'
  end.

(* The greatest element under [le], with no [Option] around it: every value
 * of this type carries one. [le a b] answers whether [a] may precede [b],
 * as it does for [insert] and [insertion_sort].
 *)
(* [forall {A : Type} . (A -> A -> Bool) -> NonEmptyList A -> A] *)
Fixpoint maximum_of {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) : A :=
  match x with
  | One  a    => a
  | Cons a x' =>
      match le a (maximum_of le x') with
      | true  => maximum_of le x'
      | false => a
      end
  end.

(* [forall {A : Type} . (A -> A -> Bool) -> NonEmptyList A -> A] *)
Fixpoint minimum_of {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) : A :=
  match x with
  | One  a    => a
  | Cons a x' =>
      match le a (minimum_of le x') with
      | true  => a
      | false => minimum_of le x'
      end
  end.

Module concatenation. (* concatenation *)

(* concatenation.associativity *)
Theorem associativity
  : forall {A : Type} (x : NonEmptyList A) (y : NonEmptyList A)
      (z : NonEmptyList A) .
      (x ++ y) ++ z = x ++ (y ++ z).
Proof.
  intros A x y z.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End concatenation. (* concatenation *)

Module length. (* length *)

Module additivity. (* length.additivity *)

Module over. (* length.additivity.over *)

(* length.additivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (x : NonEmptyList A) (y : NonEmptyList A) .
      (|| x ++ y ||) = Nat.add (|| x ||) (|| y ||).
Proof.
  intros A x y.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End over. (* length.additivity.over *)

End additivity. (* length.additivity *)

End length. (* length *)

Module membership. (* membership *)

Module distributivity. (* membership.distributivity *)

Module over. (* membership.distributivity.over *)

(* membership.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (a : A) (x : NonEmptyList A) (y : NonEmptyList A) .
      (x ++ y) contains_member a <-> x contains_member a \/ y contains_member a.
Proof.
  intros A a x y.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    split.
    + intro h.
      exact h.
    + intro h.
      exact h.
  - simpl in |- *.
    split.
    + intro h.
      destruct h as [e | h'].
      * exact (Disjunction.L (Disjunction.L e)).
      * modus aequans IH, h' as d.
        destruct d as [m | m].
        -- exact (Disjunction.L (Disjunction.R m)).
        -- exact (Disjunction.R m).
    + intro h.
      destruct h as [c | m].
      * destruct c as [e | m].
        -- exact (Disjunction.L e).
        -- modus aequans IH, (Disjunction.L m) as h'.
           exact (Disjunction.R h').
      * modus aequans IH, (Disjunction.R m) as h'.
        exact (Disjunction.R h').
Qed.

End over. (* membership.distributivity.over *)

End distributivity. (* membership.distributivity *)

End membership. (* membership *)

Module reversal. (* reversal *)

Module antidistributivity. (* reversal.antidistributivity *)

Module over. (* reversal.antidistributivity.over *)

(* reversal.antidistributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (x : NonEmptyList A) (y : NonEmptyList A) .
      reverse (x ++ y) = reverse y ++ reverse x.
Proof.
  intros A x y.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    exact (concatenation.associativity (reverse y) (reverse x') [a]).
Qed.

End over. (* reversal.antidistributivity.over *)

End antidistributivity. (* reversal.antidistributivity *)

(* reversal.involution *)
Theorem involution
  : forall {A : Type} (x : NonEmptyList A) . reverse (reverse x) = x.
Proof.
  intros A x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite (antidistributivity.over.concatenation (reverse x') [a]) in |- *.
    simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End reversal. (* reversal *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall (A : Type) (x : NonEmptyList A) . map (fun (a : A) . a) x = x.
Proof.
  intros A x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* mapping.composition *)
Theorem composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (x : NonEmptyList A) .
      map g (map f x) = map (fun (a : A) . g (f a)) x.
Proof.
  intros A B C f g x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

Module preservation. (* mapping.preservation *)

Module of. (* mapping.preservation.of *)

(* mapping.preservation.of.membership *)
Theorem membership
  : forall {A : Type} {B : Type} (f : A -> B) (a : A) (x : NonEmptyList A) .
      x contains_member a -> (map f x) contains_member f a.
Proof.
  intros A B f a x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    intro e.
    rewrite e in |- *.
    reflexivity.
  - simpl in |- *.
    intro h.
    destruct h as [e | h'].
    + apply Disjunction.L.
      rewrite e in |- *.
      reflexivity.
    + apply Disjunction.R.
      exact (IH h').
Qed.

End of. (* mapping.preservation.of *)

End preservation. (* mapping.preservation *)

End mapping. (* mapping *)

Module maximum. (* maximum *)

(* Neither law below has a premise about the list being non-empty, and
 * neither reads a [Some]: the two facts [List]'s pair has to state around
 * an [Option] are stated here about the element itself. The premises that
 * remain are about [le], and the facts read off them are [List]'s, since
 * they are about the comparison rather than about either container.
 *)
(* maximum.bound *)
Theorem bound
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall (x : NonEmptyList A) (a : A) .
        x contains_member a -> le a (maximum_of le x) = true.
Proof.
  intros A le total transitive x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - intros a h.
    simpl in |- *.
    simpl in h.
    rewrite h in |- *.
    exact (List.comparison.reflexivity total b).
  - intros a h.
    simpl in h.
    simpl in |- *.
    destruct (le b (maximum_of le x')) eqn:s.
    + destruct h as [e | m].
      * rewrite e in |- *.
        exact s.
      * exact (IH a m).
    + pose proof (List.comparison.contraposition total s) as ha.
      destruct h as [e | m].
      * rewrite e in |- *.
        exact (List.comparison.reflexivity total b).
      * exact (transitive a (maximum_of le x') b (IH a m) ha).
Qed.

(* maximum.membership *)
Theorem membership
  : forall {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) .
      x contains_member maximum_of le x.
Proof.
  intros A le x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    destruct (le b (maximum_of le x')) eqn:s.
    + exact (Disjunction.R IH).
    + exact (Disjunction.L (Identity.reflexivity b)).
Qed.

End maximum. (* maximum *)

Module minimum. (* minimum *)

(* minimum.bound *)
Theorem bound
  : forall {A : Type} {le : A -> A -> Bool} .
      (forall (a : A) (b : A) . le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A) .
         le a b = true -> le b c = true -> le a c = true) ->
      forall (x : NonEmptyList A) (a : A) .
        x contains_member a -> le (minimum_of le x) a = true.
Proof.
  intros A le total transitive x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - intros a h.
    simpl in |- *.
    simpl in h.
    rewrite h in |- *.
    exact (List.comparison.reflexivity total b).
  - intros a h.
    simpl in h.
    simpl in |- *.
    destruct (le b (minimum_of le x')) eqn:s.
    + destruct h as [e | m].
      * rewrite e in |- *.
        exact (List.comparison.reflexivity total b).
      * exact (transitive b (minimum_of le x') a s (IH a m)).
    + pose proof (List.comparison.contraposition total s) as ha.
      destruct h as [e | m].
      * rewrite e in |- *.
        exact ha.
      * exact (IH a m).
Qed.

(* minimum.membership *)
Theorem membership
  : forall {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) .
      x contains_member minimum_of le x.
Proof.
  intros A le x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    destruct (le b (minimum_of le x')) eqn:s.
    + exact (Disjunction.L (Identity.reflexivity b)).
    + exact (Disjunction.R IH).
Qed.

End minimum. (* minimum *)

Module conversion. (* conversion *)

(* [to_list] is a homomorphism, and the three laws below say so for the
 * join, the count and membership. They are the interface to [List]: a
 * statement about a [NonEmptyList] can be moved to the list it converts
 * to, and a [List] law brought back along them.
 *)
Module distributivity. (* conversion.distributivity *)

Module over. (* conversion.distributivity.over *)

(* conversion.distributivity.over.concatenation *)
Theorem concatenation
  : forall {A : Type} (x : NonEmptyList A) (y : NonEmptyList A) .
      to_list (x ++ y) = List.concat (to_list x) (to_list y).
Proof.
  intros A x y.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

End over. (* conversion.distributivity.over *)

End distributivity. (* conversion.distributivity *)

(* conversion.length *)
Theorem length
  : forall {A : Type} (x : NonEmptyList A) .
      List.length (to_list x) = NatWithZero.Positive (|| x ||).
Proof.
  intros A x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* conversion.membership *)
Theorem membership
  : forall {A : Type} (a : A) (x : NonEmptyList A) .
      x contains_member a <-> List.Contains a (to_list x).
Proof.
  intros A a x.
  induction x as [b | b x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    split.
    + intro e.
      exact (Disjunction.L e).
    + intro h.
      destruct h as [e | f].
      * exact e.
      * contradiction f.
  - simpl in |- *.
    split.
    + intro h.
      destruct h as [e | m].
      * exact (Disjunction.L e).
      * modus aequans IH, m as m'.
        exact (Disjunction.R m').
    + intro h.
      destruct h as [e | m].
      * exact (Disjunction.L e).
      * modus aequans IH, m as m'.
        exact (Disjunction.R m').
Qed.

(* The [Option] that [List]'s extrema carry is about emptiness and nothing
 * else: on a list that came from here it is always a [Some], and what it
 * wraps is the answer this type gives outright.
 *)
(* conversion.maximum *)
Theorem maximum
  : forall {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) .
      List.maximum_of le (to_list x) = Some (maximum_of le x).
Proof.
  intros A le x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    destruct (le a (maximum_of le x')) eqn:s; reflexivity.
Qed.

(* conversion.minimum *)
Theorem minimum
  : forall {A : Type} (le : A -> A -> Bool) (x : NonEmptyList A) .
      List.minimum_of le (to_list x) = Some (minimum_of le x).
Proof.
  intros A le x.
  induction x as [a | a x' IH] using NonEmptyList.induction.
  - simpl in |- *.
    reflexivity.
  - simpl in |- *.
    rewrite IH in |- *.
    destruct (le a (minimum_of le x')) eqn:s; reflexivity.
Qed.

End conversion. (* conversion *)

End NonEmptyList. (* NonEmptyList *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [NonEmptyList A], not [NonEmptyList.T A].
 *)
Abbreviation NonEmptyList := NonEmptyList.T.

(* Makes the notations declared in [Module NonEmptyList] usable in every
 * file that imports this one, as [(x ++ y)%non_empty_list] or under an
 * opened [jwa_non_empty_list_scope]. Only the notations are exported:
 * [concat], the laws and the two ctors still need the prefix.
 *)
Export (notations) NonEmptyList.

Instance NonEmptyList_functor
  : Functor NonEmptyList :=
  {| Functor.map             := fun (A : Type) (B : Type) . NonEmptyList.map
   ; Functor.map_identity    := @NonEmptyList.mapping.identity
   ; Functor.map_composition := @NonEmptyList.mapping.composition |}.

(* The count is a [Nat], which [Sized] takes as the positive case of a
 * [NatWithZero]: the class has to admit an empty container, this type
 * never is one.
 *)
Instance NonEmptyList_sized
  : Sized NonEmptyList :=
  {| Sized.cardinality :=
       fun (A : Type) (x : NonEmptyList A) .
         NatWithZero.Positive (NonEmptyList.length x) |}.

Instance NonEmptyList_membership
  : Membership NonEmptyList :=
  {| Membership.Contains := @NonEmptyList.Contains |}.
