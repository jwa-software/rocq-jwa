(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.BinaryTree.
From jwa Require Import Data.Comparable.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Tactics.Modus.

(* A search tree is a [BinaryTree] whose elements stand in order: at every
 * node the left subtree holds what is below the node's element, and the
 * right subtree what is above it. The module adds no type: it holds that
 * rule as a proposition, and the operations that rely on it.
 *)
Module BST. (* BST *)

(* A node speaks of its whole subtrees, through [BinaryTree.All], and not
 * of its two children alone: a child below its parent may still have a
 * descendant above it.
 *)
(* [forall {A : Type} . (A -> A -> Prop) -> BinaryTree A -> Prop] *)
Fixpoint Ordered {A : Type} (lt : A -> A -> Prop) (t : BinaryTree A) : Prop :=
  match t with
  | BinaryTree.Leaf       => Verum
  | BinaryTree.Node l a r =>
      BinaryTree.All (fun (b : A) . lt b a) l
      /\ BinaryTree.All (fun (b : A) . lt a b) r
      /\ Ordered lt l
      /\ Ordered lt r
  end.

(* [cmp a b] picks one subtree at each node, so the search follows one path
 * and never reads the other subtree. Its answer is the tree's membership
 * only where the tree is [Ordered].
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> BinaryTree A -> Bool] *)
Fixpoint contains {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : BinaryTree A) : Bool :=
  match t with
  | BinaryTree.Leaf       => false
  | BinaryTree.Node l b r =>
      match cmp a b with
      | Comparison.Lt => contains cmp a l
      | Comparison.Eq => true
      | Comparison.Gt => contains cmp a r
      end
  end.

Module search. (* search *)

(* search.specification *)
Theorem specification
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : BinaryTree A) .
        Ordered lt t -> (contains cmp a t = true <-> BinaryTree.Contains a t).
Proof.
  intros A cmp lt C a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - intro o.
    simpl in |- *.
    divide et impera.
    + intro e.
      ex &e quodlibet.
    + intro f.
      ex &f quodlibet.
  - intro o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    modus ponens &IHl, &lower |- left.
    modus ponens &IHr, &upper |- right.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    (* [a] is below [b]: it is in the left subtree or nowhere. *)
    + modus aequans (Comparable.comparison.strict.specification &a &b), &c |- ab.
      divide et impera.
      * intro e.
        modus aequans &left, &e |- m.
        ipso (disjoin &m, _).
      * intro h.
        match &h with | m | h' end.
        -- ipso (modus aequans &left, &m).
        -- match &h' with | e | m end.
           ++ leibniz &e in &ab.
              ex (Comparable.order.strict.irreflexivity &b &ab) quodlibet.
           ++ modus aequans
                (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &b x) &r),
                &above
                |- each.
              let proof ba : &lt &b &a := &each &a &m.
              ex (Comparable.order.strict.asymmetry &a &b &ab &ba) quodlibet.
    (* [a] is [b]: it is found at this node. *)
    + modus aequans (Comparable.comparison.equality.specification &a &b), &c |- e.
      divide et impera.
      * intro h.
        ipso (disjoin _, (disjoin &e, _)).
      * intro h.
        quod idem est.
    (* [a] is above [b]: it is in the right subtree or nowhere. *)
    + modus aequans
        (Comparable.comparison.strict.transposition.specification &a &b), &c |- ba.
      divide et impera.
      * intro e.
        modus aequans &right, &e |- m.
        ipso (disjoin _, (disjoin _, &m)).
      * intro h.
        match &h with | m | h' end.
        -- modus aequans
             (BinaryTree.quantification.all.specification (fun (x : &A) . &lt x &b) &l),
             &below
             |- each.
           let proof ab : &lt &a &b := &each &a &m.
           ex (Comparable.order.strict.asymmetry &a &b &ab &ba) quodlibet.
        -- match &h' with | e | m end.
           ++ leibniz &e in &ba.
              ex (Comparable.order.strict.irreflexivity &b &ba) quodlibet.
           ++ ipso (modus aequans &right, &m).
Qed.

End search. (* search *)

End BST. (* BST *)
