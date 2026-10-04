(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.BinaryTree.
From jwa Require Import Data.Comparable.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Tactics.Equation.
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

(* [insert] walks the path [contains] walks and puts [a] at the leaf it
 * ends on. An element the tree already holds is not added again, so the
 * tree holds each element once.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> BinaryTree A -> BinaryTree A] *)
Fixpoint insert {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : BinaryTree A)
  : BinaryTree A :=
  match t with
  | BinaryTree.Leaf       => BinaryTree.Node BinaryTree.Leaf a BinaryTree.Leaf
  | BinaryTree.Node l b r =>
      match cmp a b with
      | Comparison.Lt => BinaryTree.Node (insert cmp a l) b r
      | Comparison.Eq => BinaryTree.Node l b r
      | Comparison.Gt => BinaryTree.Node l b (insert cmp a r)
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

Module insertion. (* insertion *)

(* A predicate holds of every element after [insert] exactly when it holds
 * of the new element and of every element before.
 *)
(* insertion.all *)
Theorem all
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (P : A -> Prop) (a : A) (t : BinaryTree A) .
        BinaryTree.All P (insert cmp a t) <-> P a /\ BinaryTree.All P t.
Proof.
  intros A cmp lt C P a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      match &h with | v h' end.
      match &h' with | pa v' end.
      ipso (conjoin &pa, I).
    + intro h.
      match &h with | pa v end.
      ipso (conjoin I, (conjoin &pa, I)).
  - simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    + simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | inserted rest end.
        modus aequans &IHl, &inserted |- both.
        match &both with | pa pl end.
        ipso (conjoin &pa, (conjoin &pl, &rest)).
      * intro h.
        match &h with | pa h' end.
        match &h' with | pl rest end.
        modus aequans &IHl, (conjoin &pa, &pl) |- inserted.
        ipso (conjoin &inserted, &rest).
    (* [a] is [b], already in the tree: [P a] is [P b]. *)
    + modus aequans (Comparable.comparison.equality.specification &a &b), &c |- e.
      simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | pl h' end.
        match &h' with | pb pr end.
        lemma pa : &P &a.
        {
          leibniz &e in |- *.
          ipso &pb.
        }
        ipso (conjoin &pa, (conjoin &pl, (conjoin &pb, &pr))).
      * intro h.
        match &h with | pa rest end.
        ipso &rest.
    + simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | pl h' end.
        match &h' with | pb inserted end.
        modus aequans &IHr, &inserted |- both.
        match &both with | pa pr end.
        ipso (conjoin &pa, (conjoin &pl, (conjoin &pb, &pr))).
      * intro h.
        match &h with | pa h1 end.
        match &h1 with | pl h2 end.
        match &h2 with | pb pr end.
        modus aequans &IHr, (conjoin &pa, &pr) |- inserted.
        ipso (conjoin &pl, (conjoin &pb, &inserted)).
Qed.

(* This law asks for no ordered tree: [insert] adds [a] and loses nothing
 * on any tree.
 *)
(* insertion.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (b : A) (t : BinaryTree A) .
        BinaryTree.Contains b (insert cmp a t) <-> b = a \/ BinaryTree.Contains b t.
Proof.
  intros A cmp lt C a b t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) end per BinaryTree.induction.
  - simpl in |- *.
    divide et impera.
    + intro h.
      match &h with | f | h' end.
      * ex &f quodlibet.
      * match &h' with | e | f end.
        -- ipso (disjoin &e, _).
        -- ex &f quodlibet.
    + intro h.
      match &h with | e | f end.
      * ipso (disjoin _, (disjoin &e, _)).
      * ex &f quodlibet.
  - simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    + simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | m | rest end.
        -- modus aequans &IHl, &m |- found.
           match &found with | e | m' end.
           ++ ipso (disjoin &e, _).
           ++ ipso (disjoin _, (disjoin &m', _)).
        -- ipso (disjoin _, (disjoin _, &rest)).
      * intro h.
        match &h with | e | h' end.
        -- modus aequans &IHl, (disjoin &e, _) |- m.
           ipso (disjoin &m, _).
        -- match &h' with | m | rest end.
           ++ modus aequans &IHl, (disjoin _, &m) |- m'.
              ipso (disjoin &m', _).
           ++ ipso (disjoin _, &rest).
    (* [a] is [c], already in the tree: [b = a] is [b = c]. *)
    + modus aequans (Comparable.comparison.equality.specification &a &c), &k |- ac.
      simpl in |- *.
      divide et impera.
      * intro h.
        ipso (disjoin _, &h).
      * intro h.
        match &h with | e | present end.
        -- trans &e, &ac |- bc.
           ipso (disjoin _, (disjoin &bc, _)).
        -- ipso &present.
    + simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | m | h' end.
        -- ipso (disjoin _, (disjoin &m, _)).
        -- match &h' with | e | m end.
           ++ ipso (disjoin _, (disjoin _, (disjoin &e, _))).
           ++ modus aequans &IHr, &m |- found.
              match &found with | e | m' end.
              ** ipso (disjoin &e, _).
              ** ipso (disjoin _, (disjoin _, (disjoin _, &m'))).
      * intro h.
        match &h with | e | h1 end.
        -- modus aequans &IHr, (disjoin &e, _) |- m.
           ipso (disjoin _, (disjoin _, &m)).
        -- match &h1 with | m | h2 end.
           ++ ipso (disjoin &m, _).
           ++ match &h2 with | e | m end.
              ** ipso (disjoin _, (disjoin &e, _)).
              ** modus aequans &IHr, (disjoin _, &m) |- m'.
                 ipso (disjoin _, (disjoin _, &m')).
Qed.

(* insertion.preservation *)
Theorem preservation
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : BinaryTree A) . Ordered lt t -> Ordered lt (insert cmp a t).
Proof.
  intros A cmp lt C a t.
  match &t with | Leaf | Node (l by IHl) b (r by IHr) end per BinaryTree.induction.
  - intro o.
    simpl in |- *.
    ipso (conjoin I, (conjoin I, (conjoin I, I))).
  - intro o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (&cmp &a &b) with | | | end |- c.
    (* [a] goes into the left subtree, and is below [b] as all of it is. *)
    + modus aequans (Comparable.comparison.strict.specification &a &b), &c |- ab.
      simpl in |- *.
      let proof spec
        : BinaryTree.All (fun (x : &A) . &lt x &b) (insert &cmp &a &l)
          <-> &lt &a &b /\ BinaryTree.All (fun (x : &A) . &lt x &b) &l
        := insertion.all &C (fun (x : &A) . &lt x &b) &a &l.
      modus aequans &spec, (conjoin &ab, &below) |- inserted.
      modus ponens &IHl, &lower |- kept.
      ipso (conjoin &inserted, (conjoin &above, (conjoin &kept, &upper))).
    + simpl in |- *.
      ipso (conjoin &below, (conjoin &above, (conjoin &lower, &upper))).
    (* [a] goes into the right subtree, and is above [b] as all of it is. *)
    + modus aequans
        (Comparable.comparison.strict.transposition.specification &a &b), &c |- ba.
      simpl in |- *.
      let proof spec
        : BinaryTree.All (fun (x : &A) . &lt &b x) (insert &cmp &a &r)
          <-> &lt &b &a /\ BinaryTree.All (fun (x : &A) . &lt &b x) &r
        := insertion.all &C (fun (x : &A) . &lt &b x) &a &r.
      modus aequans &spec, (conjoin &ba, &above) |- inserted.
      modus ponens &IHr, &upper |- kept.
      ipso (conjoin &below, (conjoin &inserted, (conjoin &lower, &kept))).
Qed.

End insertion. (* insertion *)

End BST. (* BST *)
