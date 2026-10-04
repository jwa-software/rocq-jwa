(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Collection.BinaryTree.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Option.
From jwa Require Import Data.Product.
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

(* [Product]'s scope is opened for the [(m, rest)] that [pop_minimum]
 * answers with.
 *)
Local Open Scope jwa_product_scope.

(* The smallest element of an ordered tree is its leftmost one.
 * [pop_minimum] answers with it and with the tree that is left, and with
 * [None] on a leaf.
 *)
(* [forall {A : Type} . BinaryTree A -> Option (A * BinaryTree A)] *)
Fixpoint pop_minimum {A : Type} (t : BinaryTree A) : Option (A * BinaryTree A) :=
  match t with
  | BinaryTree.Leaf       => None
  | BinaryTree.Node l a r =>
      match pop_minimum l with
      | None         => Some (a, r)
      | Some (m, l') => Some (m, BinaryTree.Node l' a r)
      end
  end.

(* One tree out of two, for an [l] that lies wholly below [r]: the smallest
 * element of [r] becomes the root, the one element that may stand between
 * the two.
 *)
(* [forall {A : Type} . BinaryTree A -> BinaryTree A -> BinaryTree A] *)
Definition join := fun {A : Type} (l : BinaryTree A) (r : BinaryTree A) .
  match pop_minimum r with
  | None         => l
  | Some (m, r') => BinaryTree.Node l m r'
  end.

(* [remove] walks the path [contains] walks. Where it finds [a], the node
 * goes and its two subtrees are joined.
 *)
(* [forall {A : Type} . (A -> A -> Comparison) -> A -> BinaryTree A -> BinaryTree A] *)
Fixpoint remove {A : Type} (cmp : A -> A -> Comparison) (a : A) (t : BinaryTree A)
  : BinaryTree A :=
  match t with
  | BinaryTree.Leaf       => BinaryTree.Leaf
  | BinaryTree.Node l b r =>
      match cmp a b with
      | Comparison.Lt => BinaryTree.Node (remove cmp a l) b r
      | Comparison.Eq => join l r
      | Comparison.Gt => BinaryTree.Node l b (remove cmp a r)
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

Module extraction. (* extraction *)

Module absence. (* extraction.absence *)

(* extraction.absence.specification *)
Theorem specification
  : forall {A : Type} (t : BinaryTree A) . pop_minimum t = None <-> t = BinaryTree.Leaf.
Proof.
  intros A t.
  divide et impera.
  - match &t with | Leaf | Node l a r end.
    + intro e.
      quod idem est.
    + simpl in |- *.
      match (pop_minimum &l) with | None | Some p end |- found.
      * intro e.
        ex &e quodlibet.
      * match &p with | m l' end.
        intro e.
        ex &e quodlibet.
  - intro e.
    leibniz &e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End absence. (* extraction.absence *)

(* This law asks for no ordered tree: on any tree, the element taken out
 * and the tree that is left hold what the tree held.
 *)
(* extraction.membership *)
Theorem membership
  : forall {A : Type} (t : BinaryTree A) (m : A) (rest : BinaryTree A) .
      pop_minimum t = Some (m, rest) ->
      forall (b : A) . BinaryTree.Contains b t <-> b = m \/ BinaryTree.Contains b rest.
Proof.
  intros A t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - intros m rest e b.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest.
    simpl in |- *.
    match (pop_minimum &l) with | None | Some p end |- found.
    + intros e b.
      modus aequans (extraction.absence.specification &l), &found |- empty.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz &empty in |- *.
      leibniz <- &am, <- &rr in |- *.
      simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | f | h' end.
        -- ex &f quodlibet.
        -- ipso &h'.
      * intro h.
        ipso (disjoin _, &h).
    + match &p with | m' l' end.
      intros e b.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &mm, <- &nr in |- *.
      simpl in |- *.
      let proof spec := &IHl &m' &l' (Identity.reflexivity (Some (&m', &l'))) &b.
      divide et impera.
      * intro h.
        match &h with | inside | others end.
        -- modus aequans &spec, &inside |- d.
           match &d with | least | kept end.
           ++ ipso (disjoin &least, _).
           ++ ipso (disjoin _, (disjoin &kept, _)).
        -- ipso (disjoin _, (disjoin _, &others)).
      * intro h.
        match &h with | least | h' end.
        -- modus aequans &spec, (disjoin &least, _) |- inside.
           ipso (disjoin &inside, _).
        -- match &h' with | kept | others end.
           ++ modus aequans &spec, (disjoin _, &kept) |- inside.
              ipso (disjoin &inside, _).
           ++ ipso (disjoin _, &others).
Qed.

(* Transitivity is the one property of [lt] this law reads, so it takes
 * that alone and no comparison.
 *)
(* extraction.minimality *)
Theorem minimality
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (t : BinaryTree A) (m : A) (rest : BinaryTree A) .
        Ordered lt t -> pop_minimum t = Some (m, rest) ->
        BinaryTree.All (fun (b : A) . lt m b) rest.
Proof.
  intros A lt transitive t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - intros m rest o e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (pop_minimum &l) with | None | Some p end |- found.
    + intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz <- &am, <- &rr in |- *.
      ipso &above.
    (* The element taken out is in the left subtree, so it is below [a],
     * and through [a] below all of the right subtree.
     *)
    + match &p with | m' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &mm, <- &nr in |- *.
      simpl in |- *.
      let proof smaller := &IHl &m' &l' &lower (Identity.reflexivity (Some (&m', &l'))).
      lemma inside : BinaryTree.Contains &m' &l.
      {
        modus aequans
          (extraction.membership &l &m' &l' &found &m'), (disjoin (Identity.reflexivity &m'), _)
          |- member.
        ipso &member.
      }
      modus aequans
        (BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) &l), &below
        |- each.
      let proof ma : &lt &m' &a := &each &m' &inside.
      lemma beyond : BinaryTree.All (fun (b : &A) . &lt &m' b) &r.
      {
        ipso
          (BinaryTree.quantification.all.monotonicity
            (fun (b : &A) (ab : &lt &a b) . &transitive &m' &a b &ma ab) &above).
      }
      ipso (conjoin &smaller, (conjoin &ma, &beyond)).
Qed.

(* extraction.preservation *)
Theorem preservation
  : forall {A : Type} {lt : A -> A -> Prop} (t : BinaryTree A) (m : A) (rest : BinaryTree A) .
      Ordered lt t -> pop_minimum t = Some (m, rest) -> Ordered lt rest.
Proof.
  intros A lt t.
  match &t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction.
  - intros m rest o e.
    simpl in &e.
    ex &e quodlibet.
  - intros m rest o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (pop_minimum &l) with | None | Some p end |- found.
    + intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | am rr end.
      leibniz <- &rr in |- *.
      ipso &upper.
    (* What is left of the left subtree was in it, so it is still below [a]. *)
    + match &p with | m' l' end.
      intro e.
      match (Product.introduction.injectivity (Option.some.injectivity &e)) with | mm nr end.
      leibniz <- &nr in |- *.
      simpl in |- *.
      let proof kept := &IHl &m' &l' &lower (Identity.reflexivity (Some (&m', &l'))).
      modus aequans
        (BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) &l), &below
        |- each.
      lemma every : forall (x : &A) . BinaryTree.Contains x &l' -> &lt x &a.
      {
        intros x member.
        modus aequans (extraction.membership &l &m' &l' &found &x), (disjoin _, &member) |- inside.
        ipso (&each &x &inside).
      }
      let proof after
        : BinaryTree.All (fun (b : &A) . &lt b &a) &l'
          <-> (forall (x : &A) . BinaryTree.Contains x &l' -> &lt x &a)
        := BinaryTree.quantification.all.specification (fun (b : &A) . &lt b &a) &l'.
      modus aequans &after, &every |- smaller.
      ipso (conjoin &smaller, (conjoin &above, (conjoin &kept, &upper))).
Qed.

End extraction. (* extraction *)

Module joining. (* joining *)

(* joining.membership *)
Theorem membership
  : forall {A : Type} (l : BinaryTree A) (r : BinaryTree A) (b : A) .
      BinaryTree.Contains b (join l r) <-> BinaryTree.Contains b l \/ BinaryTree.Contains b r.
Proof.
  intros A l r b.
  simpl join in |- *.
  match (pop_minimum &r) with | None | Some p end |- found.
  - modus aequans (extraction.absence.specification &r), &found |- empty.
    leibniz &empty in |- *.
    simpl in |- *.
    divide et impera.
    + intro h.
      ipso (disjoin &h, _).
    + intro h.
      match &h with | m | f end.
      * ipso &m.
      * ex &f quodlibet.
  - match &p with | m r' end.
    simpl in |- *.
    let proof spec := extraction.membership &r &m &r' &found &b.
    divide et impera.
    + intro h.
      match &h with | inside | rest end.
      * ipso (disjoin &inside, _).
      * ipso (disjoin _, (modus aequans &spec, &rest)).
    + intro h.
      match &h with | inside | beyond end.
      * ipso (disjoin &inside, _).
      * modus aequans &spec, &beyond |- rest.
        ipso (disjoin _, &rest).
Qed.

(* [b] stands between the two trees: every element of [l] is below it, and
 * every element of [r] above it.
 *)
(* joining.preservation *)
Theorem preservation
  : forall {A : Type} {lt : A -> A -> Prop} .
      (forall (x : A) (y : A) (z : A) . lt x y -> lt y z -> lt x z) ->
      forall (b : A) (l : BinaryTree A) (r : BinaryTree A) .
        BinaryTree.All (fun (x : A) . lt x b) l ->
        BinaryTree.All (fun (x : A) . lt b x) r ->
        Ordered lt l -> Ordered lt r -> Ordered lt (join l r).
Proof.
  intros A lt transitive b l r below above lower upper.
  simpl join in |- *.
  match (pop_minimum &r) with | None | Some p end |- found.
  - ipso &lower.
  - match &p with | m r' end.
    simpl in |- *.
    lemma inside : BinaryTree.Contains &m &r.
    {
      modus aequans
        (extraction.membership &r &m &r' &found &m), (disjoin (Identity.reflexivity &m), _)
        |- member.
      ipso &member.
    }
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &b x) &r), &above
      |- each.
    let proof bm : &lt &b &m := &each &m &inside.
    lemma smaller : BinaryTree.All (fun (x : &A) . &lt x &m) &l.
    {
      ipso
        (BinaryTree.quantification.all.monotonicity
          (fun (x : &A) (xb : &lt x &b) . &transitive x &b &m xb &bm) &below).
    }
    let proof larger := extraction.minimality &transitive &r &m &r' &upper &found.
    let proof kept := extraction.preservation &r &m &r' &upper &found.
    ipso (conjoin &smaller, (conjoin &larger, (conjoin &lower, &kept))).
Qed.

End joining. (* joining *)

Module removal. (* removal *)

(* removal.membership *)
Theorem membership
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (b : A) (t : BinaryTree A) .
        Ordered lt t ->
        (BinaryTree.Contains b (remove cmp a t) <-> BinaryTree.Contains b t /\ ~ (b = a)).
Proof.
  intros A cmp lt C a b t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) end per BinaryTree.induction.
  - intro o.
    simpl in |- *.
    divide et impera.
    + intro f.
      ex &f quodlibet.
    + intro h.
      match &h with | f differs end.
      ex &f quodlibet.
  - intro o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    modus ponens &IHl, &lower |- left.
    modus ponens &IHr, &upper |- right.
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt x &c) &l), &below
      |- under.
    modus aequans
      (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &c x) &r), &above
      |- over.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    (* [a] is below [c]: it is removed from the left subtree. *)
    + modus aequans (Comparable.comparison.strict.specification &a &c), &k |- ac.
      simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | m | h' end.
        -- modus aequans &left, &m |- both.
           match &both with | inside differs end.
           ipso (conjoin (disjoin &inside, _), &differs).
        -- match &h' with | e | m end.
           ++ lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                leibniz <- &ba in &ac.
                leibniz &e in &ac.
                ex (Comparable.order.strict.irreflexivity &c &ac) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin &e, _)), &differs).
           ++ lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                let proof cb : &lt &c &b := &over &b &m.
                leibniz &ba in &cb.
                ex (Comparable.order.strict.asymmetry &a &c &ac &cb) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin _, &m)), &differs).
      * intro h.
        match &h with | present differs end.
        match &present with | m | rest end.
        -- modus aequans &left, (conjoin &m, &differs) |- kept.
           ipso (disjoin &kept, _).
        -- ipso (disjoin _, &rest).
    (* [a] is [c]: the node goes, and its two subtrees are joined. *)
    + modus aequans (Comparable.comparison.equality.specification &a &c), &k |- ac.
      let proof joined := joining.membership &l &r &b.
      divide et impera.
      * intro h.
        modus aequans &joined, &h |- either.
        match &either with | m | m end.
        -- lemma differs : ~ (&b = &a).
           {
             simpl (~ _) in |- *.
             intro ba.
             let proof bc : &lt &b &c := &under &b &m.
             leibniz &ba in &bc.
             leibniz &ac in &bc.
             ex (Comparable.order.strict.irreflexivity &c &bc) quodlibet.
           }
           ipso (conjoin (disjoin &m, _), &differs).
        -- lemma differs : ~ (&b = &a).
           {
             simpl (~ _) in |- *.
             intro ba.
             let proof cb : &lt &c &b := &over &b &m.
             leibniz &ba in &cb.
             leibniz &ac in &cb.
             ex (Comparable.order.strict.irreflexivity &c &cb) quodlibet.
           }
           ipso (conjoin (disjoin _, (disjoin _, &m)), &differs).
      * intro h.
        match &h with | present differs end.
        match &present with | m | rest end.
        -- ipso (modus aequans &joined, (disjoin &m, _)).
        -- match &rest with | e | m end.
           ++ trans &e, (symm &ac) |- ba.
              ex (&differs &ba) quodlibet.
           ++ ipso (modus aequans &joined, (disjoin _, &m)).
    (* [a] is above [c]: it is removed from the right subtree. *)
    + modus aequans
        (Comparable.comparison.strict.transposition.specification &a &c), &k |- ca.
      simpl in |- *.
      divide et impera.
      * intro h.
        match &h with | m | h' end.
        -- lemma differs : ~ (&b = &a).
           {
             simpl (~ _) in |- *.
             intro ba.
             let proof bc : &lt &b &c := &under &b &m.
             leibniz &ba in &bc.
             ex (Comparable.order.strict.asymmetry &a &c &bc &ca) quodlibet.
           }
           ipso (conjoin (disjoin &m, _), &differs).
        -- match &h' with | e | m end.
           ++ lemma differs : ~ (&b = &a).
              {
                simpl (~ _) in |- *.
                intro ba.
                leibniz <- &ba in &ca.
                leibniz &e in &ca.
                ex (Comparable.order.strict.irreflexivity &c &ca) quodlibet.
              }
              ipso (conjoin (disjoin _, (disjoin &e, _)), &differs).
           ++ modus aequans &right, &m |- both.
              match &both with | inside differs end.
              ipso (conjoin (disjoin _, (disjoin _, &inside)), &differs).
      * intro h.
        match &h with | present differs end.
        match &present with | m | rest end.
        -- ipso (disjoin &m, _).
        -- match &rest with | e | m end.
           ++ ipso (disjoin _, (disjoin &e, _)).
           ++ modus aequans &right, (conjoin &m, &differs) |- kept.
              ipso (disjoin _, (disjoin _, &kept)).
Qed.

(* removal.preservation *)
Theorem preservation
  : forall {A : Type} {cmp : A -> A -> Comparison} {lt : A -> A -> Prop} .
      Comparable cmp lt ->
      forall (a : A) (t : BinaryTree A) . Ordered lt t -> Ordered lt (remove cmp a t).
Proof.
  intros A cmp lt C a t.
  match &t with | Leaf | Node (l by IHl) c (r by IHr) end per BinaryTree.induction.
  - intro o.
    simpl in |- *.
    ipso I.
  - intro o.
    simpl in &o.
    match &o with | below o1 end.
    match &o1 with | above o2 end.
    match &o2 with | lower upper end.
    simpl in |- *.
    match (&cmp &a &c) with | | | end |- k.
    (* What is left of the left subtree was in it, so it is still below [c]. *)
    + simpl in |- *.
      modus ponens &IHl, &lower |- kept.
      modus aequans
        (BinaryTree.quantification.all.specification (fun (x : &A) . &lt x &c) &l), &below
        |- under.
      lemma every : forall (x : &A) . BinaryTree.Contains x (remove &cmp &a &l) -> &lt x &c.
      {
        intros x member.
        modus aequans (removal.membership &C &a &x &l &lower), &member |- both.
        match &both with | inside differs end.
        ipso (&under &x &inside).
      }
      let proof after
        : BinaryTree.All (fun (x : &A) . &lt x &c) (remove &cmp &a &l)
          <-> (forall (x : &A) . BinaryTree.Contains x (remove &cmp &a &l) -> &lt x &c)
        := BinaryTree.quantification.all.specification
          (fun (x : &A) . &lt x &c) (remove &cmp &a &l).
      modus aequans &after, &every |- smaller.
      ipso (conjoin &smaller, (conjoin &above, (conjoin &kept, &upper))).
    + ipso
        (joining.preservation
          (fun (x : &A) (y : &A) (z : &A) . Comparable.transitivity x y z)
          &c &l &r &below &above &lower &upper).
    (* What is left of the right subtree was in it, so it is still above [c]. *)
    + simpl in |- *.
      modus ponens &IHr, &upper |- kept.
      modus aequans
        (BinaryTree.quantification.all.specification (fun (x : &A) . &lt &c x) &r), &above
        |- over.
      lemma every : forall (x : &A) . BinaryTree.Contains x (remove &cmp &a &r) -> &lt &c x.
      {
        intros x member.
        modus aequans (removal.membership &C &a &x &r &upper), &member |- both.
        match &both with | inside differs end.
        ipso (&over &x &inside).
      }
      let proof after
        : BinaryTree.All (fun (x : &A) . &lt &c x) (remove &cmp &a &r)
          <-> (forall (x : &A) . BinaryTree.Contains x (remove &cmp &a &r) -> &lt &c x)
        := BinaryTree.quantification.all.specification
          (fun (x : &A) . &lt &c x) (remove &cmp &a &r).
      modus aequans &after, &every |- larger.
      ipso (conjoin &below, (conjoin &larger, (conjoin &lower, &kept))).
Qed.

End removal. (* removal *)

End BST. (* BST *)
