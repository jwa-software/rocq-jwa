(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Collection.Membership.
From jwa Require Import Data.Collection.Sized.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* A module may carry the type's name; its members read [BinaryTree.map].
 * The type and its ctors are declared inside it: a ctor at the top level is
 * rebound by any later file declaring the same name, silently and with no
 * warning.
 *)
Module BinaryTree. (* BinaryTree *)

(* A binary tree is a leaf, which holds nothing, or a node: one element
 * between a left and a right subtree.
 *)
Inductive T (A : Type) : Type :=
  | Leaf : T A
  | Node : T A -> A -> T A -> T A.

(* [A] is inferred from the element or, for [Leaf], from the expected type;
 * a use that has neither needs [@Leaf A].
 *)
Arguments Leaf {A}.
Arguments Node {A} l a r.

(* The carrier is named [T] so that the type itself reads [BinaryTree] on
 * both sides of the module: here through this abbreviation, outside
 * through the one that follows [End BinaryTree].
 *)
Abbreviation BinaryTree := T.

(* [Nat0]'s scope is opened for the [++] and [+] of [size] and [height],
 * [List]'s for the [[]], [::] and [++] of [to_list].
 *)
Local Open Scope jwa_nat0_scope.
Local Open Scope jwa_list_scope.

(* The eliminator that [match ... per] takes, written out. A node has two
 * subtrees, so its step takes two hypotheses, each stated right after the
 * subtree it is about.
 *)
Definition induction
  : forall (A : Type) (P : BinaryTree A -> Prop) .
      P Leaf ->
      (forall (l : BinaryTree A) . P l ->
        forall (a : A) (r : BinaryTree A) . P r -> P (Node l a r)) ->
      (forall (t : BinaryTree A) . P t)
  := fun (A : Type) (P : BinaryTree A -> Prop) (base : P Leaf)
      (step : forall (l : BinaryTree A) . P l ->
        forall (a : A) (r : BinaryTree A) . P r -> P (Node l a r)) .
      fix go (t : BinaryTree A) : P t :=
        match t with
        | Leaf       => base
        | Node l a r => step l (go l) a r (go r)
        end.

(* [size] counts the elements, so a leaf counts for nothing. *)
(* [forall {A : Type} . BinaryTree A -> Nat0] *)
Fixpoint size {A : Type} (t : BinaryTree A) : Nat0 :=
  match t with
  | Leaf       => Nat0.Zero
  | Node l _ r => ++ (size l + size r)
  end.

(* The height of a leaf is zero, so a tree of one element has height one. *)
(* [forall {A : Type} . BinaryTree A -> Nat0] *)
Fixpoint height {A : Type} (t : BinaryTree A) : Nat0 :=
  match t with
  | Leaf       => Nat0.Zero
  | Node l _ r => ++ (Nat0.max (height l) (height r))
  end.

(* The elements in order: those of the left subtree, then the node's own,
 * then those of the right subtree.
 *)
(* [forall {A : Type} . BinaryTree A -> List A] *)
Fixpoint to_list {A : Type} (t : BinaryTree A) : List A :=
  match t with
  | Leaf       => []
  | Node l a r => to_list l ++ a :: to_list r
  end.

(* [map] applies [f] to every element and keeps the shape. *)
(* [forall {A : Type} {B : Type} . (A -> B) -> BinaryTree A -> BinaryTree B] *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (t : BinaryTree A)
  : BinaryTree B :=
  match t with
  | Leaf       => Leaf
  | Node l a r => Node (map f l) (f a) (map f r)
  end.

(* [mirror] exchanges the two subtrees of every node. *)
(* [forall {A : Type} . BinaryTree A -> BinaryTree A] *)
Fixpoint mirror {A : Type} (t : BinaryTree A) : BinaryTree A :=
  match t with
  | Leaf       => Leaf
  | Node l a r => Node (mirror r) a (mirror l)
  end.

(* Membership, defined by recursion into [Prop]: a leaf has no member, and
 * a member of a node is one of the left subtree, the element itself, or
 * one of the right subtree, in the order [to_list] gives.
 *)
(* [forall {A : Type} . A -> BinaryTree A -> Prop] *)
Fixpoint Contains {A : Type} (a : A) (t : BinaryTree A) : Prop :=
  match t with
  | Leaf       => Falsum
  | Node l b r => Contains a l \/ a = b \/ Contains a r
  end.

(* [All P] holds when every element satisfies [P], [Any P] when some
 * element does. Both recurse into [Prop] as [Contains] does: a leaf gives
 * the neutral proposition, a node a conjunction or a disjunction.
 *)

(* [forall {A : Type} . (A -> Prop) -> BinaryTree A -> Prop] *)
Fixpoint All {A : Type} (P : A -> Prop) (t : BinaryTree A) : Prop :=
  match t with
  | Leaf       => Verum
  | Node l a r => All P l /\ P a /\ All P r
  end.

(* [forall {A : Type} . (A -> Prop) -> BinaryTree A -> Prop] *)
Fixpoint Any {A : Type} (P : A -> Prop) (t : BinaryTree A) : Prop :=
  match t with
  | Leaf       => Falsum
  | Node l a r => Any P l \/ P a \/ Any P r
  end.

Module height. (* height *)

(* A path from the root passes one element at each level, so no tree is
 * taller than it has elements.
 *)
(* height.bound *)
Theorem bound
  : forall {A : Type} (t : BinaryTree A) . height t <= size t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    ipso (Comparable.order.reflexivity Nat0.Zero).
  - simpl in |- *.
    lemma leftward : height &l <= size &l + size &r.
    {
      lemma summand : size &l <= size &l + size &r.
      {
        leibniz (Nat0.addition.commutativity (size &l) (size &r)) in |- *.
        ipso (Nat0.addition.right.order.extensivity (size &r) (size &l)).
      }
      ipso (Comparable.order.transitivity (height &l) (size &l) (size &l + size &r) &IHl &summand).
    }
    lemma rightward : height &r <= size &l + size &r.
    {
      let proof summand := Nat0.addition.right.order.extensivity (size &l) (size &r).
      ipso (Comparable.order.transitivity (height &r) (size &r) (size &l + size &r) &IHr &summand).
    }
    let proof together :=
      Comparable.maximum.universality
        (size &l + size &r) (height &l) (height &r) &leftward &rightward.
    leibniz (Nat0.increment.specification (Nat0.max (height &l) (height &r))) in |- *.
    leibniz (Nat0.increment.specification (size &l + size &r)) in |- *.
    ipso
      (Nat0.addition.order.monotonicity
        Nat.One (Nat0.max (height &l) (height &r)) (size &l + size &r) &together).
Qed.

End height. (* height *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall (A : Type) (t : BinaryTree A) . map (fun (a : A) . a) t = t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    quod idem est.
Qed.

(* mapping.composition *)
Theorem composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (t : BinaryTree A) .
      map g (map f t) = map (fun (a : A) . g (f a)) t.
Proof.
  intros A B C f g t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    quod idem est.
Qed.

Module preservation. (* mapping.preservation *)

(* mapping.preservation.size *)
Theorem size
  : forall {A : Type} {B : Type} (f : A -> B) (t : BinaryTree A) .
      size (map f t) = size t.
Proof.
  intros A B f t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    quod idem est.
Qed.

(* mapping.preservation.height *)
Theorem height
  : forall {A : Type} {B : Type} (f : A -> B) (t : BinaryTree A) .
      height (map f t) = height t.
Proof.
  intros A B f t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    quod idem est.
Qed.

(* One direction only: where [f] sends two elements to one, [f a] is a
 * member of [map f t] through either of them.
 *)
(* mapping.preservation.membership *)
Theorem membership
  : forall {A : Type} {B : Type} (f : A -> B) (a : A) (t : BinaryTree A) .
      Contains a t -> Contains (f a) (map f t).
Proof.
  intros A B f a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    intro h.
    ipso &h.
  - simpl in |- *.
    intro h.
    match &h with | m | h' end.
    + modus ponens &IHl, &m |- m'.
      ipso (disjoin &m', _).
    + match &h' with | e | m end.
      * lemma facto : &f &a = &f &b.
        {
          leibniz &e in |- *.
          quod idem est.
        }
        ipso (disjoin _, (disjoin &facto, _)).
      * modus ponens &IHr, &m |- m'.
        ipso (disjoin _, (disjoin _, &m')).
Qed.

End preservation. (* mapping.preservation *)

End mapping. (* mapping *)

Module mirroring. (* mirroring *)

(* mirroring.involution *)
Theorem involution
  : forall {A : Type} (t : BinaryTree A) . mirror (mirror t) = t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    quod idem est.
Qed.

Module preservation. (* mirroring.preservation *)

(* mirroring.preservation.size *)
Theorem size
  : forall {A : Type} (t : BinaryTree A) . size (mirror t) = size t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    leibniz (Nat0.addition.commutativity (size &r) (size &l)) in |- *.
    quod idem est.
Qed.

(* mirroring.preservation.height *)
Theorem height
  : forall {A : Type} (t : BinaryTree A) . height (mirror t) = height t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    leibniz (Comparable.maximum.commutativity (height &r) (height &l)) in |- *.
    quod idem est.
Qed.

(* mirroring.preservation.membership *)
Theorem membership
  : forall {A : Type} (a : A) (t : BinaryTree A) .
      Contains a (mirror t) <-> Contains a t.
Proof.
  intros A a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      ipso &h.
    + intro h.
      ipso &h.
  - simpl in |- *.
    divide et impera.
    + intro h.
      match &h with | m | h' end.
      * modus aequans &IHr, &m |- m'.
        ipso (disjoin _, (disjoin _, &m')).
      * match &h' with | e | m end.
        -- ipso (disjoin _, (disjoin &e, _)).
        -- modus aequans &IHl, &m |- m'.
           ipso (disjoin &m', _).
    + intro h.
      match &h with | m | h' end.
      * modus aequans &IHl, &m |- m'.
        ipso (disjoin _, (disjoin _, &m')).
      * match &h' with | e | m end.
        -- ipso (disjoin _, (disjoin &e, _)).
        -- modus aequans &IHr, &m |- m'.
           ipso (disjoin &m', _).
Qed.

End preservation. (* mirroring.preservation *)

End mirroring. (* mirroring *)

Module conversion. (* conversion *)

(* [to_list] carries the tree's operations to [List]'s, and the laws below
 * say so one operation at a time: along them a statement about a tree
 * moves to the list of its elements, and a [List] law comes back.
 *)

(* conversion.size *)
Theorem size
  : forall {A : Type} (t : BinaryTree A) . (|| to_list t ||) = size t.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (List.length.additivity.over.concatenation (to_list &l) (&a :: to_list &r))
      in |- *.
    simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    leibniz (Nat0.increment.specification (size &r)) in |- *.
    leibniz (Nat0.increment.specification (size &l + size &r)) in |- *.
    leibniz (Nat0.addition.left.commutativity (size &l) Nat.One (size &r)) in |- *.
    quod idem est.
Qed.

(* conversion.mapping *)
Theorem mapping
  : forall {A : Type} {B : Type} (f : A -> B) (t : BinaryTree A) .
      to_list (map f t) = List.map f (to_list t).
Proof.
  intros A B f t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    leibniz (List.mapping.distributivity.over.concatenation &f (to_list &l) (&a :: to_list &r))
      in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conversion.mirroring *)
Theorem mirroring
  : forall {A : Type} (t : BinaryTree A) .
      to_list (mirror t) = List.reverse (to_list t).
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz &IHl, &IHr in |- *.
    leibniz (List.reversal.antidistributivity.over.concatenation (to_list &l) (&a :: to_list &r))
      in |- *.
    simpl in |- *.
    simpl List.append in |- *.
    leibniz
      (List.concatenation.associativity
        (List.reverse (to_list &r)) (&a :: []) (List.reverse (to_list &l)))
      in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* conversion.membership *)
Theorem membership
  : forall {A : Type} (a : A) (t : BinaryTree A) .
      Contains a t <-> List.Contains a (to_list t).
Proof.
  intros A a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      ipso &h.
    + intro h.
      ipso &h.
  - simpl in |- *.
    let proof split
      : List.Contains &a (to_list &l ++ &b :: to_list &r)
        <-> List.Contains &a (to_list &l) \/ &a = &b \/ List.Contains &a (to_list &r)
      := List.membership.distributivity.over.concatenation &a (to_list &l) (&b :: to_list &r).
    divide et impera.
    + intro h.
      lemma facto
        : List.Contains &a (to_list &l) \/ &a = &b \/ List.Contains &a (to_list &r).
      {
        match &h with | m | h' end.
        - modus aequans &IHl, &m |- m'.
          ipso (disjoin &m', _).
        - match &h' with | e | m end.
          + ipso (disjoin _, (disjoin &e, _)).
          + modus aequans &IHr, &m |- m'.
            ipso (disjoin _, (disjoin _, &m')).
      }
      ipso (modus aequans &split, &facto).
    + intro h.
      modus aequans &split, &h |- d.
      match &d with | m | d' end.
      * modus aequans &IHl, &m |- m'.
        ipso (disjoin &m', _).
      * match &d' with | e | m end.
        -- ipso (disjoin _, (disjoin &e, _)).
        -- modus aequans &IHr, &m |- m'.
           ipso (disjoin _, (disjoin _, &m')).
Qed.

(* conversion.all *)
Theorem all
  : forall {A : Type} (P : A -> Prop) (t : BinaryTree A) .
      All P t <-> List.All P (to_list t).
Proof.
  intros A P t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      ipso &h.
    + intro h.
      ipso &h.
  - simpl in |- *.
    let proof split
      : List.All &P (to_list &l ++ &a :: to_list &r)
        <-> List.All &P (to_list &l) /\ &P &a /\ List.All &P (to_list &r)
      := List.quantification.all.distributivity.over.concatenation
        &P (to_list &l) (&a :: to_list &r).
    divide et impera.
    + intro h.
      match &h with | hl h' end.
      match &h' with | pa hr end.
      modus aequans &IHl, &hl |- hl'.
      modus aequans &IHr, &hr |- hr'.
      ipso (modus aequans &split, (conjoin &hl', (conjoin &pa, &hr'))).
    + intro h.
      modus aequans &split, &h |- c.
      match &c with | hl c' end.
      match &c' with | pa hr end.
      modus aequans &IHl, &hl |- hl'.
      modus aequans &IHr, &hr |- hr'.
      ipso (conjoin &hl', (conjoin &pa, &hr')).
Qed.

(* conversion.any *)
Theorem any
  : forall {A : Type} (P : A -> Prop) (t : BinaryTree A) .
      Any P t <-> List.Any P (to_list t).
Proof.
  intros A P t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      ipso &h.
    + intro h.
      ipso &h.
  - simpl in |- *.
    let proof split
      : List.Any &P (to_list &l ++ &a :: to_list &r)
        <-> List.Any &P (to_list &l) \/ &P &a \/ List.Any &P (to_list &r)
      := List.quantification.any.distributivity.over.concatenation
        &P (to_list &l) (&a :: to_list &r).
    divide et impera.
    + intro h.
      lemma facto
        : List.Any &P (to_list &l) \/ &P &a \/ List.Any &P (to_list &r).
      {
        match &h with | m | h' end.
        - modus aequans &IHl, &m |- m'.
          ipso (disjoin &m', _).
        - match &h' with | pa | m end.
          + ipso (disjoin _, (disjoin &pa, _)).
          + modus aequans &IHr, &m |- m'.
            ipso (disjoin _, (disjoin _, &m')).
      }
      ipso (modus aequans &split, &facto).
    + intro h.
      modus aequans &split, &h |- d.
      match &d with | m | d' end.
      * modus aequans &IHl, &m |- m'.
        ipso (disjoin &m', _).
      * match &d' with | pa | m end.
        -- ipso (disjoin _, (disjoin &pa, _)).
        -- modus aequans &IHr, &m |- m'.
           ipso (disjoin _, (disjoin _, &m')).
Qed.

End conversion. (* conversion *)

Module quantification. (* quantification *)

(* Each quantifier, stated through membership. Both laws come back from
 * [List]'s along [conversion], so neither is an induction of its own.
 *)

Module all. (* quantification.all *)

(* quantification.all.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (t : BinaryTree A) .
      All P t <-> (forall (a : A) . Contains a t -> P a).
Proof.
  intros A P t.
  let proof listed := conversion.all &P &t.
  let proof each := List.quantification.all.specification &P (to_list &t).
  divide et impera.
  - intros h a m.
    modus aequans &listed, &h |- h'.
    modus aequans &each, &h' |- every.
    modus aequans (conversion.membership &a &t), &m |- m'.
    ipso (&every &a &m').
  - intro h.
    lemma every : forall (a : &A) . List.Contains a (to_list &t) -> &P a.
    {
      intros a m'.
      modus aequans (conversion.membership &a &t), &m' |- m.
      ipso (&h &a &m).
    }
    modus aequans &each, &every |- h'.
    ipso (modus aequans &listed, &h').
Qed.

(* quantification.all.monotonicity *)
Theorem monotonicity
  : forall {A : Type} {P : A -> Prop} {Q : A -> Prop} {t : BinaryTree A} .
      (forall (a : A) . P a -> Q a) -> All P t -> All Q t.
Proof.
  intros A P Q t weaker h.
  modus aequans (quantification.all.specification &P &t), &h |- each.
  lemma every : forall (a : &A) . Contains a &t -> &Q a.
  {
    intros a m.
    ipso (&weaker &a (&each &a &m)).
  }
  ipso (modus aequans (quantification.all.specification &Q &t), &every).
Qed.

End all. (* quantification.all *)

Module any. (* quantification.any *)

(* quantification.any.specification *)
Theorem specification
  : forall {A : Type} (P : A -> Prop) (t : BinaryTree A) .
      Any P t <-> (forsome (a : A) . Contains a t /\ P a).
Proof.
  intros A P t.
  let proof listed := conversion.any &P &t.
  let proof one := List.quantification.any.specification &P (to_list &t).
  divide et impera.
  - intro h.
    modus aequans &listed, &h |- h'.
    modus aequans &one, &h' |- found.
    match &found with | a both end.
    match &both with | m' pa end.
    modus aequans (conversion.membership &a &t), &m' |- m.
    exists &a.
    ipso (conjoin &m, &pa).
  - intro h.
    match &h with | a both end.
    match &both with | m pa end.
    modus aequans (conversion.membership &a &t), &m |- m'.
    lemma found : forsome (b : &A) . List.Contains b (to_list &t) /\ &P b.
    {
      exists &a.
      ipso (conjoin &m', &pa).
    }
    modus aequans &one, &found |- h'.
    ipso (modus aequans &listed, &h').
Qed.

End any. (* quantification.any *)

End quantification. (* quantification *)

End BinaryTree. (* BinaryTree *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [BinaryTree A], not [BinaryTree.T A].
 *)
Abbreviation BinaryTree := BinaryTree.T.

Instance BinaryTree_functor
  : Functor BinaryTree :=
  {| Functor.map := fun (A : Type) (B : Type) . BinaryTree.map
  ; Functor.identity := BinaryTree.mapping.identity
  ; Functor.composition := BinaryTree.mapping.composition |}.

Instance BinaryTree_sized
  : Sized BinaryTree :=
  {| Sized.cardinality := @BinaryTree.size |}.

Instance BinaryTree_membership
  : Membership BinaryTree :=
  {| Membership.Contains := @BinaryTree.Contains |}.
