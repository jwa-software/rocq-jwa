(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Order.StrictPartialOrder.
From jwa Require Import Relation.Order.StrictTotalOrder.
From jwa Require Import Relation.Order.TotalOrder.
From jwa Require Import Tactics.Modus.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Total.
From jwa Require Import Relation.Transitive.
From jwa Require Import Relation.Trichotomous.

(* A three-way [compare] that decides the strict order [lt]: [Comparison.Lt] is [lt m n],
 * [Comparison.Eq] is [m = n], and [Comparison.Gt], by [antisymmetry], is [lt n m].
 *)
Class Comparable {A : Type} (compare : A -> A -> Comparison) (lt : A -> A -> Prop) : Prop :=
  { transitivity
    : forall (l : A) (m : A) (n : A) .
      lt l m -> lt m n -> lt l n
  ; specification
    : forall (m : A) (n : A) .
      (compare m n = Comparison.Lt <-> lt m n) /\ (compare m n = Comparison.Eq <-> m = n)
  ; antisymmetry
    : forall (m : A) (n : A) .
      compare m n = Comparison.transpose (compare n m) }.

(* Everything below holds of any [Comparable compare lt], so each number type
 * proves the three fields once and inherits the rest.
 *)
Module Comparable. (* Comparable *)

(* [forall {A : Type} . (A -> A -> Prop) -> A -> A -> Prop] *)
Definition LessOrEqual := fun {A : Type} (lt : A -> A -> Prop) (m : A) (n : A) .
  m = n \/ lt m n.

(* [forall {A : Type} . (A -> A -> Comparison) -> A -> A -> Bool] *)
Definition eq := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) .
  match compare m n with
  | Comparison.Lt => false
  | Comparison.Eq => true
  | Comparison.Gt => false
  end.

(* [forall {A : Type} . (A -> A -> Comparison) -> A -> A -> Bool] *)
Definition le := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) .
  match compare m n with
  | Comparison.Lt => true
  | Comparison.Eq => true
  | Comparison.Gt => false
  end.

(* [forall {A : Type} . (A -> A -> Comparison) -> A -> A -> A] *)
Definition min := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) .
  match compare m n with
  | Comparison.Lt => m
  | Comparison.Eq => m
  | Comparison.Gt => n
  end.

(* [forall {A : Type} . (A -> A -> Comparison) -> A -> A -> A] *)
Definition max := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) .
  match compare m n with
  | Comparison.Lt => n
  | Comparison.Eq => m
  | Comparison.Gt => m
  end.

Module comparison. (* comparison *)

(* comparison.reflexivity *)
Theorem reflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A) .
    compare n n = Comparison.Eq.
Proof.
  intros A compare lt C n.
  match (Comparable.specification n n) with | _ s end.
  ipso (modus aequans s, (Identity.reflexivity n)).
Qed.

Module strict. (* comparison.strict *)

(* comparison.strict.specification *)
Theorem specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    compare m n = Comparison.Lt <-> lt m n.
Proof.
  intros A compare lt C m n.
  match (Comparable.specification m n) with | s _ end.
  ipso s.
Qed.

Module transposition. (* comparison.strict.transposition *)

(* [Comparison.Gt] is [Comparison.Lt] read from the other side, which is what [antisymmetry] says;
 * the proof is that law, then the [Comparison.Lt] case.
 *)
(* comparison.strict.transposition.specification *)
Theorem specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    compare m n = Comparison.Gt <-> lt n m.
Proof.
  intros A compare lt C m n.
  leibniz (Comparable.antisymmetry m n) in |- *.
  divide et impera.
  - intro e.
    match (compare n m) with | | | end |- c.
    + match (Comparable.specification n m) with | s _ end.
      ipso (modus aequans s, c).
    + simpl in e.
      ex e quodlibet.
    + simpl in e.
      ex e quodlibet.
  - intro h.
    match (Comparable.specification n m) with | s _ end.
    modus aequans s, h |- e.
    leibniz e in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End transposition. (* comparison.strict.transposition *)

End strict. (* comparison.strict *)

Module equality. (* comparison.equality *)

(* comparison.equality.specification *)
Theorem specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    compare m n = Comparison.Eq <-> m = n.
Proof.
  intros A compare lt C m n.
  match (Comparable.specification m n) with | _ s end.
  ipso s.
Qed.

(* comparison.equality.reflection *)
Theorem reflection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    eq compare m n = true <-> m = n.
Proof.
  intros A compare lt C m n.
  simpl eq in |- *.
  divide et impera.
  - intro e.
    match (compare m n) with | | | end |- c.
    + ex e quodlibet.
    + match (Comparable.specification m n) with | _ s end.
      ipso (modus aequans s, c).
    + ex e quodlibet.
  - intro h.
    match (Comparable.specification m n) with | _ s end.
    leibniz (modus aequans s, h) in |- *.
    simpl in |- *.
    quod idem est.
Qed.

End equality. (* comparison.equality *)

End comparison. (* comparison *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.irreflexivity *)
Theorem irreflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A) .
    ~ (lt n n).
Proof.
  intros A compare lt C n.
  simpl (~ _) in |- *.
  intro h.
  modus aequans (comparison.strict.specification n n), h |- c.
  leibniz (comparison.reflexivity n) in c.
  ex c quodlibet.
Qed.

(* order.strict.asymmetry *)
Theorem asymmetry
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    lt m n -> ~ (lt n m).
Proof.
  intros A compare lt C m n h1.
  simpl (~ _) in |- *.
  intro h2.
  let proof h := Comparable.transitivity m n m h1 h2.
  let proof i := order.strict.irreflexivity m.
  simpl (~ _) in i.
  modus ponens i, h |- f.
  ex f quodlibet.
Qed.

(* order.strict.trichotomy *)
Theorem trichotomy
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    lt m n \/ m = n \/ lt n m.
Proof.
  intros A compare lt C m n.
  match (compare m n) with | | | end |- c.
  - match (Comparable.specification m n) with | s _ end.
    modus aequans s, c |- h.
    ipso (disjoin h, _).
  - match (Comparable.specification m n) with | _ s end.
    modus aequans s, c |- h.
    ipso (disjoin _, (disjoin h, _)).
  - modus aequans (comparison.strict.transposition.specification m n), c |- h.
    ipso (disjoin _, (disjoin _, h)).
Qed.

End strict. (* order.strict *)

(* order.reflexivity *)
Theorem reflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A) .
    LessOrEqual lt n n.
Proof.
  intros A compare lt C n.
  simpl LessOrEqual in |- *.
  ipso (disjoin (Identity.reflexivity n), _).
Qed.

(* order.antisymmetry *)
Theorem antisymmetry
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    LessOrEqual lt m n -> LessOrEqual lt n m -> m = n.
Proof.
  intros A compare lt C m n h1 h2.
  simpl LessOrEqual in h1.
  simpl LessOrEqual in h2.
  match h1 with | e1 | lt1 end.
  - ipso e1.
  - match h2 with | e2 | lt2 end.
    + ipso (Identity.symmetry e2).
    + let proof a := order.strict.asymmetry m n lt1.
      simpl (~ _) in a.
      modus ponens a, lt2 |- f.
      ex f quodlibet.
Qed.

(* order.transitivity *)
Theorem transitivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A) .
    LessOrEqual lt l m -> LessOrEqual lt m n -> LessOrEqual lt l n.
Proof.
  intros A compare lt C l m n h1 h2.
  simpl LessOrEqual in h1, h2 |- *.
  match h1 with | e1 | lt1 end.
  - leibniz e1 in |- *.
    ipso h2.
  - match h2 with | e2 | lt2 end.
    + leibniz e2 in lt1.
      ipso (disjoin _, lt1).
    + ipso (disjoin _, (Comparable.transitivity l m n lt1 lt2)).
Qed.

(* order.totality *)
Theorem totality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    LessOrEqual lt m n \/ LessOrEqual lt n m.
Proof.
  intros A c lt C m n.
  let proof t := order.strict.trichotomy m n.
  simpl LessOrEqual in |- *.
  match t with | lt1 | rest end.
  - ipso (disjoin (disjoin _, lt1), _).
  - match rest with | e | gt end.
    + ipso (disjoin (disjoin e, _), _).
    + ipso (disjoin _, (disjoin _, gt)).
Qed.

(* order.reflection *)
Theorem reflection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    le compare m n = true <-> LessOrEqual lt m n.
Proof.
  intros A compare lt C m n.
  simpl le in |- *.
  simpl LessOrEqual in |- *.
  match (compare m n) with | | | end |- c.
  - divide et impera.
    + intro e.
      match (Comparable.specification m n) with | s _ end.
      ipso (disjoin _, (modus aequans s, c)).
    + intro h.
      quod idem est.
  - divide et impera.
    + intro e.
      match (Comparable.specification m n) with | _ s end.
      ipso (disjoin (modus aequans s, c), _).
    + intro h.
      quod idem est.
  - divide et impera.
    + intro e.
      ex e quodlibet.
    + intro h.
      match h with | e | lt1 end.
      * match (Comparable.specification m n) with | _ s end.
        modus aequans s, e |- e'.
        leibniz e' in c.
        ex c quodlibet.
      * match (Comparable.specification m n) with | s _ end.
        modus aequans s, lt1 |- e.
        leibniz e in c.
        ex c quodlibet.
Qed.

End order. (* order *)

Module minimum. (* minimum *)

(* minimum.specification *)
Theorem specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    min compare m n = m <-> LessOrEqual lt m n.
Proof.
  intros A compare lt C m n.
  simpl min in |- *.
  simpl LessOrEqual in |- *.
  divide et impera.
  - intro e.
    match (compare m n) with | | | end |- c.
    + match (Comparable.specification m n) with | s _ end.
      ipso (disjoin _, (modus aequans s, c)).
    + match (Comparable.specification m n) with | _ s end.
      ipso (disjoin (modus aequans s, c), _).
    + ipso (disjoin (Identity.symmetry e), _).
  - intro h.
    match (compare m n) with | | | end |- c.
    + quod idem est.
    + quod idem est.
    + match h with | e | lt1 end.
      * ipso (Identity.symmetry e).
      * match (Comparable.specification m n) with | s _ end.
        modus aequans s, lt1 |- e.
        leibniz e in c.
        ex c quodlibet.
Qed.

Module left. (* minimum.left *)

(* minimum.left.projection *)
Lemma projection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A) .
    LessOrEqual lt (min compare l r) l.
Proof.
  intros A compare lt C l r.
  simpl min in |- *.
  simpl LessOrEqual in |- *.
  match (compare l r) with | | | end |- c.
  - ipso (disjoin (Identity.reflexivity l), _).
  - ipso (disjoin (Identity.reflexivity l), _).
  - ipso (disjoin _, (modus aequans
                         (comparison.strict.transposition.specification l r), c)).
Qed.

End left. (* minimum.left *)

Module right. (* minimum.right *)

(* minimum.right.projection *)
Lemma projection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A) .
    LessOrEqual lt (min compare l r) r.
Proof.
  intros A compare lt C l r.
  simpl min in |- *.
  simpl LessOrEqual in |- *.
  match (compare l r) with | | | end |- c.
  - match (Comparable.specification l r) with | s _ end.
    ipso (disjoin _, (modus aequans s, c)).
  - match (Comparable.specification l r) with | _ s end.
    ipso (disjoin (modus aequans s, c), _).
  - ipso (disjoin (Identity.reflexivity r), _).
Qed.

End right. (* minimum.right *)

(* minimum.universality *)
Theorem universality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (k : A) (m : A) (n : A) .
    LessOrEqual lt k m -> LessOrEqual lt k n -> LessOrEqual lt k (min compare m n).
Proof.
  intros A c lt C k m n h1 h2.
  simpl min in |- *.
  match (c m n) with | | | end.
  - ipso h1.
  - ipso h1.
  - ipso h2.
Qed.

(* minimum.commutativity *)
Theorem commutativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    min compare m n = min compare n m.
Proof.
  intros A c lt C m n.
  ipso (order.antisymmetry (min c m n) (min c n m)
          (minimum.universality
             (min c m n) n m
             (minimum.right.projection m n) (minimum.left.projection m n))
          (minimum.universality
             (min c n m) m n
             (minimum.right.projection n m) (minimum.left.projection n m))).
Qed.

(* minimum.associativity *)
Theorem associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A) .
    min compare (min compare l m) n = min compare l (min compare m n).
Proof.
  intros A c lt C l m n.
  lemma forth : LessOrEqual &lt (min &c (min &c &l &m) &n) (min &c &l (min &c &m &n)).
  {
    ipso (minimum.universality
            (min c (min c l m) n) l (min c m n)
            (order.transitivity
               (min c (min c l m) n) (min c l m) l
               (minimum.left.projection (min c l m) n)
               (minimum.left.projection l m))
            (minimum.universality
               (min c (min c l m) n) m n
               (order.transitivity
                  (min c (min c l m) n) (min c l m) m
                  (minimum.left.projection (min c l m) n)
                  (minimum.right.projection l m))
               (minimum.right.projection
                  (min c l m) n))).
  }
  lemma back : LessOrEqual &lt (min &c &l (min &c &m &n)) (min &c (min &c &l &m) &n).
  {
    ipso (minimum.universality
            (min c l (min c m n))
            (min c l m)
            n
            (minimum.universality
               (min c l (min c m n)) l m
               (minimum.left.projection
                  l
                  (min c m n))
               (order.transitivity
                  (min c l (min c m n)) (min c m n) m
                  (minimum.right.projection l (min c m n))
                  (minimum.left.projection m n)))
            (order.transitivity
               (min c l (min c m n)) (min c m n) n
               (minimum.right.projection l (min c m n))
               (minimum.right.projection m n))).
  }
  ipso (order.antisymmetry
          (min c (min c l m) n)
          (min c l (min c m n))
          &forth &back).
Qed.

(* minimum.idempotence *)
Theorem idempotence
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A) .
    min compare n n = n.
Proof.
  intros A c lt C n.
  simpl min in |- *.
  leibniz (comparison.reflexivity n) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End minimum. (* minimum *)

Module maximum. (* maximum *)

(* maximum.specification *)
Theorem specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    max compare m n = m <-> LessOrEqual lt n m.
Proof.
  intros A compare lt C m n.
  simpl max in |- *.
  simpl LessOrEqual in |- *.
  divide et impera.
  - intro e.
    match (compare m n) with | | | end |- c.
    + ipso (disjoin e, _).
    + match (Comparable.specification m n) with | _ s end.
      modus aequans s, c |- e'.
      ipso (disjoin (Identity.symmetry e'), _).
    + ipso (disjoin _, (modus aequans
                           (comparison.strict.transposition.specification m n), c)).
  - intro h.
    match (compare m n) with | | | end |- c.
    + match h with | e | gt end.
      * ipso e.
      * modus aequans (comparison.strict.transposition.specification m n), gt |- e.
        leibniz e in c.
        ex c quodlibet.
    + quod idem est.
    + quod idem est.
Qed.

Module left. (* maximum.left *)

(* maximum.left.injection *)
Lemma injection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A) .
    LessOrEqual lt l (max compare l r).
Proof.
  intros A compare lt C l r.
  simpl max in |- *.
  simpl LessOrEqual in |- *.
  match (compare l r) with | | | end |- c.
  - match (Comparable.specification l r) with | s _ end.
    ipso (disjoin _, (modus aequans s, c)).
  - ipso (disjoin (Identity.reflexivity l), _).
  - ipso (disjoin (Identity.reflexivity l), _).
Qed.

End left. (* maximum.left *)

Module right. (* maximum.right *)

(* maximum.right.injection *)
Lemma injection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A) .
    LessOrEqual lt r (max compare l r).
Proof.
  intros A compare lt C l r.
  simpl max in |- *.
  simpl LessOrEqual in |- *.
  match (compare l r) with | | | end |- c.
  - ipso (disjoin (Identity.reflexivity r), _).
  - match (Comparable.specification l r) with | _ s end.
    modus aequans s, c |- e.
    ipso (disjoin (Identity.symmetry e), _).
  - ipso (disjoin _, (modus aequans
                         (comparison.strict.transposition.specification l r), c)).
Qed.

End right. (* maximum.right *)

(* maximum.universality *)
Theorem universality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (k : A)
      (m : A) (n : A) .
    LessOrEqual lt m k -> LessOrEqual lt n k -> LessOrEqual lt (max compare m n) k.
Proof.
  intros A c lt C k m n h1 h2.
  simpl max in |- *.
  match (c m n) with | | | end.
  - ipso h2.
  - ipso h1.
  - ipso h1.
Qed.

(* maximum.commutativity *)
Theorem commutativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A) .
    max compare m n = max compare n m.
Proof.
  intros A c lt C m n.
  ipso (order.antisymmetry (max c m n) (max c n m)
          (maximum.universality
             (max c n m) m n
             (maximum.right.injection n m) (maximum.left.injection n m))
          (maximum.universality
             (max c m n) n m
             (maximum.right.injection m n) (maximum.left.injection m n))).
Qed.

(* maximum.associativity *)
Theorem associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A) .
    max compare (max compare l m) n = max compare l (max compare m n).
Proof.
  intros A c lt C l m n.
  lemma forth : LessOrEqual &lt (max &c (max &c &l &m) &n) (max &c &l (max &c &m &n)).
  {
    ipso (maximum.universality
            (max c l (max c m n))
            (max c l m)
            n
            (maximum.universality
               (max c l (max c m n)) l m
               (maximum.left.injection
                  l (max c m n))
               (order.transitivity
                  m (max c m n) (max c l (max c m n))
                  (maximum.left.injection m n)
                  (maximum.right.injection l (max c m n))))
            (order.transitivity
               n (max c m n) (max c l (max c m n))
               (maximum.right.injection m n)
               (maximum.right.injection l (max c m n)))).
  }
  lemma back : LessOrEqual &lt (max &c &l (max &c &m &n)) (max &c (max &c &l &m) &n).
  {
    ipso (maximum.universality
            (max c (max c l m) n)
            l (max c m n)
            (order.transitivity
               l (max c l m) (max c (max c l m) n)
               (maximum.left.injection l m)
               (maximum.left.injection (max c l m)
               n))
            (maximum.universality
               (max c (max c l m) n) m n
               (order.transitivity
                  m (max c l m) (max c (max c l m) n)
                  (maximum.right.injection l m)
                  (maximum.left.injection (max c l m) n))
               (maximum.right.injection
                  (max c l m) n))).
  }
  ipso (order.antisymmetry
          (max c (max c l m) n)
          (max c l (max c m n))
          &forth &back).
Qed.

(* maximum.idempotence *)
Theorem idempotence
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A) .
    max compare n n = n.
Proof.
  intros A c lt C n.
  simpl max in |- *.
  leibniz (comparison.reflexivity n) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End maximum. (* maximum *)

End Comparable. (* Comparable *)

Section Orders.

Context
  {A : Type}
  {compare : A -> A -> Comparison}
  {lt : A -> A -> Prop}
  {C : Comparable compare lt}.

#[export] Instance strict_partial_order
  : StrictPartialOrder lt :=
  {| StrictPartialOrder.irreflexivity :=
       {| Irreflexive.irreflexivity := Comparable.order.strict.irreflexivity |}
   ; StrictPartialOrder.transitivity  :=
       {| Transitive.transitivity   := Comparable.transitivity |} |}.

#[export] Instance strict_total_order
  : StrictTotalOrder lt :=
  {| StrictTotalOrder.strict_partial_order := strict_partial_order
   ; StrictTotalOrder.trichotomy           :=
       {| Trichotomous.trichotomy := Comparable.order.strict.trichotomy |} |}.

#[export] Instance total_order
  : TotalOrder (Comparable.LessOrEqual lt) :=
  {| TotalOrder.partial_order :=
       {| PartialOrder.reflexivity :=
            {| Reflexive.reflexivity      := Comparable.order.reflexivity |}
        ; PartialOrder.antisymmetry :=
            {| Antisymmetric.antisymmetry := Comparable.order.antisymmetry |}
        ; PartialOrder.transitivity :=
            {| Transitive.transitivity    := Comparable.order.transitivity |} |}
   ; TotalOrder.totality :=
       {| Total.totality := Comparable.order.totality |} |}.

End Orders.
