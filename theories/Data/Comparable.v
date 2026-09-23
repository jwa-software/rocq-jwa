(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Base.Comparison.
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
  destruct (Comparable.specification n n) as [_ s].
  exact (modus aequans s, (Identity.reflexivity n)).
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
  destruct (Comparable.specification m n) as [s _].
  exact s.
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
  rewrite (Comparable.antisymmetry m n) in |- *.
  split.
  - intro e.
    destruct (compare n m) as [| |] eqn:c.
    + destruct (Comparable.specification n m) as [s _].
      exact (modus aequans s, c).
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
  - intro h.
    destruct (Comparable.specification n m) as [s _].
    modus aequans s, h as e.
    rewrite e in |- *.
    simpl in |- *.
    reflexivity.
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
  destruct (Comparable.specification m n) as [_ s].
  exact s.
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
  unfold eq in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + discriminate e.
    + destruct (Comparable.specification m n) as [_ s].
      exact (modus aequans s, c).
    + discriminate e.
  - intro h.
    destruct (Comparable.specification m n) as [_ s].
    modus aequans s, h as e.
    rewrite e in |- *.
    reflexivity.
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
  unfold Negation in |- *.
  intro h.
  modus aequans (comparison.strict.specification n n), h as c.
  rewrite (comparison.reflexivity n) in c.
  discriminate c.
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
  unfold Negation in |- *.
  intro h2.
  pose proof (Comparable.transitivity m n m h1 h2) as h.
  pose proof (order.strict.irreflexivity m) as i.
  unfold Negation in i.
  modus ponens i, h as f.
  contradiction f.
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
  destruct (compare m n) as [| |] eqn:c.
  - destruct (Comparable.specification m n) as [s _].
    modus aequans s, c as h.
    exact (Disjunction.L h).
  - destruct (Comparable.specification m n) as [_ s].
    modus aequans s, c as h.
    exact (Disjunction.R (Disjunction.L h)).
  - modus aequans (comparison.strict.transposition.specification m n), c as h.
    exact (Disjunction.R (Disjunction.R h)).
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
  unfold LessOrEqual in |- *.
  exact (Disjunction.L (Identity.reflexivity n)).
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
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  destruct h1 as [e1 | lt1].
  - exact e1.
  - destruct h2 as [e2 | lt2].
    + exact (Identity.symmetry e2).
    + pose proof (order.strict.asymmetry m n lt1) as a.
      unfold Negation in a.
      modus ponens a, lt2 as f.
      contradiction f.
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
  unfold LessOrEqual in h1, h2 |- *.
  destruct h1 as [e1 | lt1].
  - rewrite e1 in |- *.
    exact h2.
  - destruct h2 as [e2 | lt2].
    + rewrite e2 in lt1.
      exact (Disjunction.R lt1).
    + exact (Disjunction.R (Comparable.transitivity l m n lt1 lt2)).
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
  pose proof (order.strict.trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt1 | rest].
  - exact (Disjunction.L (Disjunction.R lt1)).
  - destruct rest as [e | gt].
    + exact (Disjunction.L (Disjunction.L e)).
    + exact (Disjunction.R (Disjunction.R gt)).
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
  unfold le in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - split.
    + intro e.
      apply Disjunction.R.
      destruct (Comparable.specification m n) as [s _].
      exact (modus aequans s, c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      apply Disjunction.L.
      destruct (Comparable.specification m n) as [_ s].
      exact (modus aequans s, c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      discriminate e.
    + intro h.
      destruct h as [e | lt1].
      * destruct (Comparable.specification m n) as [_ s].
        modus aequans s, e as e'.
        rewrite e' in c.
        discriminate c.
      * destruct (Comparable.specification m n) as [s _].
        modus aequans s, lt1 as e.
        rewrite e in c.
        discriminate c.
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
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.R.
      destruct (Comparable.specification m n) as [s _].
      exact (modus aequans s, c).
    + apply Disjunction.L.
      destruct (Comparable.specification m n) as [_ s].
      exact (modus aequans s, c).
    + apply Disjunction.L.
      exact (Identity.symmetry e).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + destruct h as [e | lt1].
      * exact (Identity.symmetry e).
      * destruct (Comparable.specification m n) as [s _].
        modus aequans s, lt1 as e.
        rewrite e in c.
        discriminate c.
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
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.L (Identity.reflexivity l)).
  - exact (Disjunction.L (Identity.reflexivity l)).
  - apply Disjunction.R.
    exact (modus aequans
             (comparison.strict.transposition.specification l r), c).
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
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.R.
    destruct (Comparable.specification l r) as [s _].
    exact (modus aequans s, c).
  - apply Disjunction.L.
    destruct (Comparable.specification l r) as [_ s].
    exact (modus aequans s, c).
  - exact (Disjunction.L (Identity.reflexivity r)).
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
  unfold min in |- *.
  destruct (c m n) as [| |].
  - exact h1.
  - exact h1.
  - exact h2.
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
  apply (order.antisymmetry (min c m n) (min c n m)).
  - exact (minimum.universality
            (min c m n) n m
            (minimum.right.projection m n) (minimum.left.projection m n)).
  - exact (minimum.universality
            (min c n m) m n
            (minimum.right.projection n m) (minimum.left.projection n m)).
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
  apply (order.antisymmetry
          (min c (min c l m) n)
          (min c l (min c m n))).
  - apply (minimum.universality
            (min c (min c l m) n) l (min c m n)).
    + exact (order.transitivity
              (min c (min c l m) n) (min c l m) l
              (minimum.left.projection (min c l m) n)
              (minimum.left.projection l m)).
    + apply (minimum.universality
              (min c (min c l m) n) m n).
      * exact (order.transitivity
                (min c (min c l m) n) (min c l m) m
                (minimum.left.projection (min c l m) n)
                (minimum.right.projection l m)).
      * exact (minimum.right.projection
                (min c l m) n).
  - apply (minimum.universality
              (min c l (min c m n))
              (min c l m)
              n).
    + apply (minimum.universality
              (min c l (min c m n)) l m).
      * exact (minimum.left.projection
                l
                (min c m n)).
      * exact (order.transitivity
                (min c l (min c m n)) (min c m n) m
                (minimum.right.projection l (min c m n))
                (minimum.left.projection m n)).
    + exact (order.transitivity
              (min c l (min c m n)) (min c m n) n
              (minimum.right.projection l (min c m n))
              (minimum.right.projection m n)).
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
  unfold min in |- *.
  rewrite (comparison.reflexivity n) in |- *.
  reflexivity.
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
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.L.
      exact e.
    + apply Disjunction.L.
      destruct (Comparable.specification m n) as [_ s].
      modus aequans s, c as e'.
      exact (Identity.symmetry e').
    + apply Disjunction.R.
      exact (modus aequans
               (comparison.strict.transposition.specification m n), c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + destruct h as [e | gt].
      * exact e.
      * modus aequans (comparison.strict.transposition.specification m n), gt as e.
        rewrite e in c.
        discriminate c.
    + reflexivity.
    + reflexivity.
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
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.R.
    destruct (Comparable.specification l r) as [s _].
    exact (modus aequans s, c).
  - exact (Disjunction.L (Identity.reflexivity l)).
  - exact (Disjunction.L (Identity.reflexivity l)).
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
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.L (Identity.reflexivity r)).
  - apply Disjunction.L.
    destruct (Comparable.specification l r) as [_ s].
    modus aequans s, c as e.
    exact (Identity.symmetry e).
  - apply Disjunction.R.
    exact (modus aequans
             (comparison.strict.transposition.specification l r), c).
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
  unfold max in |- *.
  destruct (c m n) as [| |].
  - exact h2.
  - exact h1.
  - exact h1.
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
  apply (order.antisymmetry (max c m n) (max c n m)).
  - exact (maximum.universality
            (max c n m) m n
            (maximum.right.injection n m) (maximum.left.injection n m)).
  - exact (maximum.universality
            (max c m n) n m
            (maximum.right.injection m n) (maximum.left.injection m n)).
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
  apply (order.antisymmetry
          (max c (max c l m) n)
          (max c l (max c m n))).
  - apply (maximum.universality
            (max c l (max c m n))
            (max c l m)
            n).
    + apply (maximum.universality
              (max c l (max c m n)) l m).
      * exact (maximum.left.injection
                l (max c m n)).
      * exact (order.transitivity
                m (max c m n) (max c l (max c m n))
                (maximum.left.injection m n)
                (maximum.right.injection l (max c m n))).
    + exact (order.transitivity
              n (max c m n) (max c l (max c m n))
              (maximum.right.injection m n)
              (maximum.right.injection l (max c m n))).
  - apply (maximum.universality
            (max c (max c l m) n)
            l (max c m n)).
    + exact (order.transitivity
              l (max c l m) (max c (max c l m) n)
              (maximum.left.injection l m)
              (maximum.left.injection (max c l m)
              n)).
    + apply (maximum.universality
              (max c (max c l m) n) m n).
      * exact (order.transitivity
                m (max c l m) (max c (max c l m) n)
                (maximum.right.injection l m)
                (maximum.left.injection (max c l m) n)).
      * exact (maximum.right.injection
                (max c l m) n).
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
  unfold max in |- *.
  rewrite (comparison.reflexivity n) in |- *.
  reflexivity.
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
