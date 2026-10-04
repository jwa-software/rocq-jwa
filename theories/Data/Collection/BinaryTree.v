(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Collection.Membership.
From jwa Require Import Data.Collection.Sized.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.Nat0.

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

End preservation. (* mapping.preservation *)

End mapping. (* mapping *)

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

End conversion. (* conversion *)

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
