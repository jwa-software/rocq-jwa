(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Comparison.
From jwa Require Import Relation.Antisymmetric.
From jwa Require Import Relation.Irreflexive.
From jwa Require Import Relation.Order.PartialOrder.
From jwa Require Import Relation.Order.StrictPartialOrder.
From jwa Require Import Relation.Order.StrictTotalOrder.
From jwa Require Import Relation.Order.TotalOrder.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Total.
From jwa Require Import Relation.Transitive.
From jwa Require Import Relation.Trichotomous.

(* A three-way [compare] that decides the strict order [lt]: [Lt] is [lt m n],
 * [Eq] is [m = n], and [Gt], by [antisymmetry], is [lt n m].
 *)
Class Comparable {A : Type} (compare : A -> A -> Comparison) (lt : A -> A -> Prop) : Prop :=
  { transitivity
    : forall (l : A) (m : A) (n : A),
      lt l m -> lt m n -> lt l n
  ; specification
    : forall (m : A) (n : A),
      (compare m n = Lt <-> lt m n) /\ (compare m n = Eq <-> m = n)
  ; antisymmetry
    : forall (m : A) (n : A),
      compare m n = Comparison.transpose (compare n m) }.

(* Everything below holds of any [Comparable compare lt], so each number type
 * proves the three fields once and inherits the rest.
 *)
Module Comparable.

(* [forall {A : Type}, (A -> A -> Prop) -> A -> A -> Prop] *)
Definition LessOrEqual := fun {A : Type} (lt : A -> A -> Prop) (m : A) (n : A) =>
  m = n \/ lt m n.

(* [forall {A : Type}, (A -> A -> Comparison) -> A -> A -> Bool] *)
Definition eq := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

(* [forall {A : Type}, (A -> A -> Comparison) -> A -> A -> Bool] *)
Definition le := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
  match compare m n with
  | Lt => true
  | Eq => true
  | Gt => false
  end.

(* [forall {A : Type}, (A -> A -> Comparison) -> A -> A -> A] *)
Definition min := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
  match compare m n with
  | Lt => m
  | Eq => m
  | Gt => n
  end.

(* [forall {A : Type}, (A -> A -> Comparison) -> A -> A -> A] *)
Definition max := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
  match compare m n with
  | Lt => n
  | Eq => m
  | Gt => m
  end.

Theorem reflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    compare n n = Eq.
Proof.
  intros A compare lt C n.
  destruct (Comparable.specification n n) as [_ s].
  exact (Biimplication.backward_elimination
          s
          (Identity.reflexivity n)).
Qed.

Theorem lt_specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    compare m n = Lt <-> lt m n.
Proof.
  intros A compare lt C m n.
  destruct (Comparable.specification m n) as [s _].
  exact s.
Qed.

Theorem eq_specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    compare m n = Eq <-> m = n.
Proof.
  intros A compare lt C m n.
  destruct (Comparable.specification m n) as [_ s].
  exact s.
Qed.

Theorem gt_specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    compare m n = Gt <-> lt n m.
Proof.
  intros A compare lt C m n.
  rewrite (Comparable.antisymmetry m n) in |- *.
  split.
  - intro e.
    destruct (compare n m) as [| |] eqn:c.
    + destruct (Comparable.specification n m) as [s _].
      exact (Biimplication.forward_elimination s c).
    + simpl in e.
      discriminate e.
    + simpl in e.
      discriminate e.
  - intro h.
    destruct (Comparable.specification n m) as [s _].
    rewrite (Biimplication.backward_elimination s h) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem trichotomy
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    lt m n \/ m = n \/ lt n m.
Proof.
  intros A compare lt C m n.
  destruct (compare m n) as [| |] eqn:c.
  - destruct (Comparable.specification m n) as [s _].
    exact (Disjunction.l
             (Biimplication.forward_elimination s c)).
  - destruct (Comparable.specification m n) as [_ s].
    exact (Disjunction.r
            (Disjunction.l
              (Biimplication.forward_elimination s c))).
  - exact (Disjunction.r
            (Disjunction.r
              (Biimplication.forward_elimination (gt_specification m n) c))).
Qed.

Theorem lt_irreflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    ~ (lt n n).
Proof.
  intros A compare lt C n.
  unfold Negation in |- *.
  intro h.
  pose proof (Biimplication.backward_elimination (lt_specification n n) h) as c.
  rewrite (Comparable.reflexivity n) in c.
  discriminate c.
Qed.

Theorem lt_asymmetry
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    lt m n -> ~ (lt n m).
Proof.
  intros A compare lt C m n h1.
  unfold Negation in |- *.
  intro h2.
  pose proof (Comparable.transitivity m n m h1 h2) as h.
  pose proof (lt_irreflexivity m) as i.
  unfold Negation in i.
  pose proof (i h) as f.
  contradiction f.
Qed.

Theorem eq_reflection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    eq compare m n = true <-> m = n.
Proof.
  intros A compare lt C m n.
  unfold eq in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + discriminate e.
    + destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination s c).
    + discriminate e.
  - intro h.
    destruct (Comparable.specification m n) as [_ s].
    rewrite (Biimplication.backward_elimination s h) in |- *.
    reflexivity.
Qed.

Theorem le_reflexivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    LessOrEqual lt n n.
Proof.
  intros A compare lt C n.
  unfold LessOrEqual in |- *.
  exact (Disjunction.l (Identity.reflexivity n)).
Qed.

Theorem le_antisymmetry
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    LessOrEqual lt m n -> LessOrEqual lt n m -> m = n.
Proof.
  intros A compare lt C m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  destruct h1 as [e1 | lt1].
  - exact e1.
  - destruct h2 as [e2 | lt2].
    + exact (Identity.symmetry e2).
    + pose proof (lt_asymmetry m n lt1) as a.
      unfold Negation in a.
      pose proof (a lt2) as f.
      contradiction f.
Qed.

Theorem le_transitivity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A),
    LessOrEqual lt l m -> LessOrEqual lt m n -> LessOrEqual lt l n.
Proof.
  intros A compare lt C l m n h1 h2.
  unfold LessOrEqual in h1.
  unfold LessOrEqual in h2.
  unfold LessOrEqual in |- *.
  destruct h1 as [e1 | lt1].
  - rewrite e1 in |- *.
    exact h2.
  - destruct h2 as [e2 | lt2].
    + rewrite e2 in lt1.
      exact (Disjunction.r lt1).
    + exact (Disjunction.r (Comparable.transitivity l m n lt1 lt2)).
Qed.

Theorem le_totality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    LessOrEqual lt m n \/ LessOrEqual lt n m.
Proof.
  intros A c lt C m n.
  pose proof (trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt1 | rest].
  - exact (Disjunction.l (Disjunction.r lt1)).
  - destruct rest as [e | gt].
    + exact (Disjunction.l (Disjunction.l e)).
    + exact (Disjunction.r (Disjunction.r gt)).
Qed.

Theorem le_reflection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    le compare m n = true <-> LessOrEqual lt m n.
Proof.
  intros A compare lt C m n.
  unfold le in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - split.
    + intro e.
      apply Disjunction.r.
      destruct (Comparable.specification m n) as [s _].
      exact (Biimplication.forward_elimination s c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      apply Disjunction.l.
      destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination s c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      discriminate e.
    + intro h.
      destruct h as [e | lt1].
      * destruct (Comparable.specification m n) as [_ s].
        rewrite (Biimplication.backward_elimination s e)   in c.
        discriminate c.
      * destruct (Comparable.specification m n) as [s _].
        rewrite (Biimplication.backward_elimination s lt1) in c.
        discriminate c.
Qed.

Theorem min_specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    min compare m n = m <-> LessOrEqual lt m n.
Proof.
  intros A compare lt C m n.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.r.
      destruct (Comparable.specification m n) as [s _].
      exact (Biimplication.forward_elimination s c).
    + apply Disjunction.l.
      destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination s c).
    + apply Disjunction.l.
      exact (Identity.symmetry e).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + destruct h as [e | lt1].
      * exact (Identity.symmetry e).
      * destruct (Comparable.specification m n) as [s _].
        rewrite (Biimplication.backward_elimination s lt1) in c.
        discriminate c.
Qed.

Theorem max_specification
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    max compare m n = m <-> LessOrEqual lt n m.
Proof.
  intros A compare lt C m n.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + apply Disjunction.l.
      exact e.
    + apply Disjunction.l.
      destruct (Comparable.specification m n) as [_ s].
      exact (Identity.symmetry
               (Biimplication.forward_elimination s c)).
    + apply Disjunction.r.
      exact (Biimplication.forward_elimination
               (gt_specification m n) c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + destruct h as [e | gt].
      * exact e.
      * rewrite (Biimplication.backward_elimination (gt_specification m n) gt) in c.
        discriminate c.
    + reflexivity.
    + reflexivity.
Qed.

Lemma min_l_projection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A),
    LessOrEqual lt (min compare l r) l.
Proof.
  intros A compare lt C l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination (gt_specification l r) c).
Qed.

Lemma min_r_projection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A),
    LessOrEqual lt (min compare l r) r.
Proof.
  intros A compare lt C l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    destruct (Comparable.specification l r) as [s _].
    exact (Biimplication.forward_elimination s c).
  - apply Disjunction.l.
    destruct (Comparable.specification l r) as [_ s].
    exact (Biimplication.forward_elimination s c).
  - exact (Disjunction.l (Identity.reflexivity r)).
Qed.

Theorem min_universality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (k : A) (m : A) (n : A),
    LessOrEqual lt k m -> LessOrEqual lt k n -> LessOrEqual lt k (min compare m n).
Proof.
  intros A c lt C k m n h1 h2.
  unfold min in |- *.
  destruct (c m n) as [| |].
  - exact h1.
  - exact h1.
  - exact h2.
Qed.

Lemma max_l_injection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A),
    LessOrEqual lt l (max compare l r).
Proof.
  intros A compare lt C l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    destruct (Comparable.specification l r) as [s _].
    exact (Biimplication.forward_elimination s c).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
Qed.

Lemma max_r_injection
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (r : A),
    LessOrEqual lt r (max compare l r).
Proof.
  intros A compare lt C l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity r)).
  - apply Disjunction.l.
    destruct (Comparable.specification l r) as [_ s].
    exact (Identity.symmetry (Biimplication.forward_elimination s c)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination (gt_specification l r) c).
Qed.

Theorem max_universality
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (k : A)
      (m : A) (n : A),
    LessOrEqual lt m k -> LessOrEqual lt n k -> LessOrEqual lt (max compare m n) k.
Proof.
  intros A c lt C k m n h1 h2.
  unfold max in |- *.
  destruct (c m n) as [| |].
  - exact h2.
  - exact h1.
  - exact h1.
Qed.

Theorem min_commutativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    min compare m n = min compare n m.
Proof.
  intros A c lt C m n.
  apply (le_antisymmetry (min c m n) (min c n m)).
  - exact (min_universality
            (min c m n) n m
            (min_r_projection m n) (min_l_projection m n)).
  - exact (min_universality
            (min c n m) m n
            (min_r_projection n m) (min_l_projection n m)).
Qed.

Theorem max_commutativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (m : A) (n : A),
    max compare m n = max compare n m.
Proof.
  intros A c lt C m n.
  apply (le_antisymmetry (max c m n) (max c n m)).
  - exact (max_universality
            (max c n m) m n
            (max_r_injection n m) (max_l_injection n m)).
  - exact (max_universality
            (max c m n) n m
            (max_r_injection m n) (max_l_injection m n)).
Qed.

Theorem min_associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A),
    min compare (min compare l m) n = min compare l (min compare m n).
Proof.
  intros A c lt C l m n.
  apply (le_antisymmetry
          (min c (min c l m) n)
          (min c l (min c m n))).
  - apply (min_universality
            (min c (min c l m) n)
            l
            (min c m n)).
    + exact (le_transitivity
              (min c (min c l m) n)
              (min c l m)
              l
              (min_l_projection (min c l m) n)
              (min_l_projection l m)).
    + apply (min_universality
              (min c (min c l m) n) m n).
      * exact (le_transitivity
                (min c (min c l m) n)
                (min c l m)
                m
                (min_l_projection (min c l m) n)
                (min_r_projection l m)).
      * exact (min_r_projection
                (min c l m) n).
  - apply (min_universality
              (min c l (min c m n))
              (min c l m)
              n).
    + apply (min_universality
              (min c l (min c m n)) l m).
      * exact (min_l_projection
                l
                (min c m n)).
      * exact (le_transitivity
                (min c l (min c m n))
                (min c m n)
                m
                (min_r_projection l (min c m n))
                (min_l_projection m n)).
    + exact (le_transitivity
              (min c l (min c m n))
              (min c m n)
              n
              (min_r_projection l (min c m n))
              (min_r_projection m n)).
Qed.

Theorem max_associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A) (m : A) (n : A),
    max compare (max compare l m) n = max compare l (max compare m n).
Proof.
  intros A c lt C l m n.
  apply (le_antisymmetry
          (max c (max c l m) n)
          (max c l (max c m n))).
  - apply (max_universality
            (max c l (max c m n))
            (max c l m)
            n).
    + apply (max_universality
              (max c l (max c m n)) l m).
      * exact (max_l_injection
                l (max c m n)).
      * exact (le_transitivity
                m
                (max c m n)
                (max c l (max c m n))
                (max_l_injection m n)
                (max_r_injection l (max c m n))).
    + exact (le_transitivity
              n
              (max c m n)
              (max c l (max c m n))
              (max_r_injection m n)
              (max_r_injection l (max c m n))).
  - apply (max_universality
            (max c (max c l m) n)
            l (max c m n)).
    + exact (le_transitivity
              l
              (max c l m)
              (max c (max c l m) n)
              (max_l_injection l m)
              (max_l_injection (max c l m)
              n)).
    + apply (max_universality
              (max c (max c l m) n) m n).
      * exact (le_transitivity
                m
                (max c l m)
                (max c (max c l m) n)
                (max_r_injection l m)
                (max_l_injection (max c l m) n)).
      * exact (max_r_injection
                (max c l m) n).
Qed.

Theorem min_idempotence
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    min compare n n = n.
Proof.
  intros A c lt C n.
  unfold min in |- *.
  rewrite (Comparable.reflexivity n) in |- *.
  reflexivity.
Qed.

Theorem max_idempotence
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    max compare n n = n.
Proof.
  intros A c lt C n.
  unfold max in |- *.
  rewrite (Comparable.reflexivity n) in |- *.
  reflexivity.
Qed.

End Comparable.

Section Orders.

Context
  {A : Type}
  {compare : A -> A -> Comparison}
  {lt : A -> A -> Prop}
  {C : Comparable compare lt}.

#[export] Instance strict_partial_order
  : StrictPartialOrder lt :=
  {| StrictPartialOrder.irreflexivity :=
       {| Irreflexive.irreflexivity := Comparable.lt_irreflexivity |}
   ; StrictPartialOrder.transitivity  :=
       {| Transitive.transitivity   := Comparable.transitivity |} |}.

#[export] Instance strict_total_order
  : StrictTotalOrder lt :=
  {| StrictTotalOrder.strict_partial_order := strict_partial_order
   ; StrictTotalOrder.trichotomy           :=
       {| Trichotomous.trichotomy := Comparable.trichotomy |} |}.

#[export] Instance total_order
  : TotalOrder (Comparable.LessOrEqual lt) :=
  {| TotalOrder.partial_order :=
       {| PartialOrder.reflexivity :=
            {| Reflexive.reflexivity      := Comparable.le_reflexivity |}
        ; PartialOrder.antisymmetry :=
            {| Antisymmetric.antisymmetry := Comparable.le_antisymmetry |}
        ; PartialOrder.transitivity :=
            {| Transitive.transitivity    := Comparable.le_transitivity |} |}
   ; TotalOrder.totality :=
       {| Total.totality := Comparable.le_totality |} |}.

End Orders.
