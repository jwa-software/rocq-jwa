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
  { strict_partial_order
    :: StrictPartialOrder lt
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
Definition equal := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
  match compare m n with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

(* [forall {A : Type}, (A -> A -> Comparison) -> A -> A -> Bool] *)
Definition at_most := fun {A : Type} (compare : A -> A -> Comparison) (m : A) (n : A) =>
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
           (compare n n = Eq) (n = n) s (Identity.reflexivity n)).
Qed.

Theorem gt_specification
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      compare m n = Gt <-> lt n m.
Proof.
  intros A compare lt C m n.
  rewrite (Comparable.antisymmetry m n) in |- *.
  split.
  - intro e.
    destruct (compare n m) as [| |] eqn:c.
    + destruct (Comparable.specification n m) as [s _].
      exact (Biimplication.forward_elimination (compare n m = Lt) (lt n m) s c).
    + simpl in e.
      discriminate.
    + simpl in e.
      discriminate.
  - intro h.
    destruct (Comparable.specification n m) as [s _].
    rewrite (Biimplication.backward_elimination (compare n m = Lt) (lt n m) s h) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem trichotomy
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      lt m n \/ m = n \/ lt n m.
Proof.
  intros A compare lt C m n.
  destruct (compare m n) as [| |] eqn:c.
  - destruct (Comparable.specification m n) as [s _].
    exact (Disjunction.l
             (Biimplication.forward_elimination (compare m n = Lt) (lt m n) s c)).
  - destruct (Comparable.specification m n) as [_ s].
    exact (Disjunction.r
             (Disjunction.l
                (Biimplication.forward_elimination (compare m n = Eq) (m = n) s c))).
  - exact (Disjunction.r
             (Disjunction.r
                (Biimplication.forward_elimination
                   (compare m n = Gt) (lt n m) (gt_specification m n) c))).
Qed.

Theorem lt_asymmetry
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      lt m n -> ~ (lt n m).
Proof.
  intros A compare lt C m n h1.
  unfold Negation in |- *.
  intro h2.
  (* The two compose into [lt m m], against irreflexivity. *)
  pose proof (Transitive.transitivity m n m h1 h2) as h.
  pose proof (Irreflexive.irreflexivity m) as i.
  unfold Negation in i.
  pose proof (i h) as f.
  contradiction.
Qed.

(* A [Definition], like [total_order]: each number type states its own
 * [StrictTotalOrder] instance with this as the body, so a client of that
 * type alone finds it.
 *)
(* [forall {A : Type}
 *         {compare : A -> A -> Comparison}
 *         {lt : A -> A -> Prop}
 *         {C : Comparable compare lt},
 *    StrictTotalOrder lt]
 *)
Definition strict_total_order
  := fun {A : Type}
         {compare : A -> A -> Comparison}
         {lt : A -> A -> Prop}
         {C : Comparable compare lt} =>
       {| StrictTotalOrder.strict_partial_order :=
            @Comparable.strict_partial_order A compare lt C
        ; StrictTotalOrder.trichotomy :=
            {| Trichotomous.trichotomy := @trichotomy A compare lt C |} |}.

Theorem eq_specification
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      equal compare m n = true <-> m = n.
Proof.
  intros A compare lt C m n.
  unfold equal in |- *.
  split.
  - intro e.
    destruct (compare m n) as [| |] eqn:c.
    + discriminate.
    + destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination (compare m n = Eq) (m = n) s c).
    + discriminate.
  - intro h.
    destruct (Comparable.specification m n) as [_ s].
    rewrite (Biimplication.backward_elimination (compare m n = Eq) (m = n) s h) in |- *.
    reflexivity.
Qed.

(* The [false] answer refutes equality: were the two equal, it would be
 * [true].
 *)
Theorem eq_refutation
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      equal compare m n = false -> ~ (m = n).
Proof.
  intros A compare lt C m n e.
  unfold Negation in |- *.
  intro h.
  rewrite (Biimplication.backward_elimination
             (equal compare m n = true) (m = n) (eq_specification m n) h) in e.
  discriminate.
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
           (m : A)
           (n : A),
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
      contradiction.
Qed.

Theorem le_transitivity
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (m : A)
           (n : A),
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
    + exact (Disjunction.r (Transitive.transitivity l m n lt1 lt2)).
Qed.

Theorem le_totality
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      LessOrEqual lt m n \/ LessOrEqual lt n m.
Proof.
  intros A compare lt C m n.
  pose proof (trichotomy m n) as t.
  unfold LessOrEqual in |- *.
  destruct t as [lt1 | rest].
  - exact (Disjunction.l (Disjunction.r lt1)).
  - destruct rest as [e | gt].
    + exact (Disjunction.l (Disjunction.l e)).
    + exact (Disjunction.r (Disjunction.r gt)).
Qed.

(* A [Definition], not an [Instance]: a number type's own [LessOrEqual] is
 * [LessOrEqual lt] only after unfolding, which instance search does not do,
 * so each type states its [TotalOrder] instance with this as the body.
 *)
(* [forall {A : Type}
 *         {compare : A -> A -> Comparison}
 *         {lt : A -> A -> Prop}
 *         {C : Comparable compare lt},
 *    TotalOrder (LessOrEqual lt)]
 *)
Definition total_order
  := fun {A : Type}
         {compare : A -> A -> Comparison}
         {lt : A -> A -> Prop}
         {C : Comparable compare lt} =>
       {| TotalOrder.partial_order :=
            {| PartialOrder.reflexivity :=
                 {| Reflexive.reflexivity      := @le_reflexivity  A compare lt C |}
             ; PartialOrder.antisymmetry :=
                 {| Antisymmetric.antisymmetry := @le_antisymmetry A compare lt C |}
             ; PartialOrder.transitivity :=
                 {| Transitive.transitivity    := @le_transitivity A compare lt C |} |}
        ; TotalOrder.totality :=
            {| Total.totality := @le_totality A compare lt C |} |}.

Theorem at_most_specification
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      at_most compare m n = true <-> LessOrEqual lt m n.
Proof.
  intros A compare lt C m n.
  unfold at_most in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - split.
    + intro e.
      apply Disjunction.r.
      destruct (Comparable.specification m n) as [s _].
      exact (Biimplication.forward_elimination (compare m n = Lt) (lt m n) s c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      apply Disjunction.l.
      destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination (compare m n = Eq) (m = n) s c).
    + intro h.
      reflexivity.
  - split.
    + intro e.
      discriminate.
    + (* Either half of [h] turns [c] into an equation between two ctors. *)
      intro h.
      destruct h as [e | lt1].
      * destruct (Comparable.specification m n) as [_ s].
        rewrite (Biimplication.backward_elimination (compare m n = Eq) (m = n) s e) in c.
        discriminate.
      * destruct (Comparable.specification m n) as [s _].
        rewrite (Biimplication.backward_elimination (compare m n = Lt) (lt m n) s lt1) in c.
        discriminate.
Qed.

(* The two laws a sorting comparison needs, read off the order. *)

Theorem at_most_totality
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      at_most compare m n = true \/ at_most compare n m = true.
Proof.
  intros A compare lt C m n.
  destruct (le_totality m n) as [h | h].
  - apply Disjunction.l.
    exact (Biimplication.backward_elimination
             (at_most compare m n = true) (LessOrEqual lt m n) (at_most_specification m n) h).
  - apply Disjunction.r.
    exact (Biimplication.backward_elimination
             (at_most compare n m = true) (LessOrEqual lt n m) (at_most_specification n m) h).
Qed.

Theorem at_most_transitivity
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (m : A)
           (n : A),
      at_most compare l m = true -> at_most compare m n = true -> at_most compare l n = true.
Proof.
  intros A compare lt C l m n h1 h2.
  pose proof (Biimplication.forward_elimination
                (at_most compare l m = true) (LessOrEqual lt l m) (at_most_specification l m) h1)
    as le1.
  pose proof (Biimplication.forward_elimination
                (at_most compare m n = true) (LessOrEqual lt m n) (at_most_specification m n) h2)
    as le2.
  exact (Biimplication.backward_elimination
           (at_most compare l n = true) (LessOrEqual lt l n) (at_most_specification l n)
           (le_transitivity l m n le1 le2)).
Qed.

Theorem min_specification
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
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
      exact (Biimplication.forward_elimination (compare m n = Lt) (lt m n) s c).
    + apply Disjunction.l.
      destruct (Comparable.specification m n) as [_ s].
      exact (Biimplication.forward_elimination (compare m n = Eq) (m = n) s c).
    + apply Disjunction.l.
      exact (Identity.symmetry e).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + reflexivity.
    + reflexivity.
    + destruct h as [e | lt1].
      * exact (Identity.symmetry e).
      * (* [lt1] says [compare m n] is [Lt], against [c]. *)
        destruct (Comparable.specification m n) as [s _].
        rewrite (Biimplication.backward_elimination (compare m n = Lt) (lt m n) s lt1) in c.
        discriminate.
Qed.

Theorem max_specification
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
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
               (Biimplication.forward_elimination (compare m n = Eq) (m = n) s c)).
    + apply Disjunction.r.
      exact (Biimplication.forward_elimination
               (compare m n = Gt) (lt n m) (gt_specification m n) c).
  - intro h.
    destruct (compare m n) as [| |] eqn:c.
    + destruct h as [e | gt].
      * exact e.
      * (* [gt] says [compare m n] is [Gt], against [c]. *)
        rewrite (Biimplication.backward_elimination
                   (compare m n = Gt) (lt n m) (gt_specification m n) gt) in c.
        discriminate.
    + reflexivity.
    + reflexivity.
Qed.

(* [min l r] is the meet of [l] and [r]: below both, and above anything
 * below both.
 *)

Theorem min_left_projection
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (r : A),
      LessOrEqual lt (min compare l r) l.
Proof.
  intros A compare lt C l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Gt) (lt r l) (gt_specification l r) c).
Qed.

Theorem min_right_projection
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (r : A),
      LessOrEqual lt (min compare l r) r.
Proof.
  intros A compare lt C l r.
  unfold min in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    destruct (Comparable.specification l r) as [s _].
    exact (Biimplication.forward_elimination (compare l r = Lt) (lt l r) s c).
  - apply Disjunction.l.
    destruct (Comparable.specification l r) as [_ s].
    exact (Biimplication.forward_elimination (compare l r = Eq) (l = r) s c).
  - exact (Disjunction.l (Identity.reflexivity r)).
Qed.

Theorem min_universality
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (k : A)
           (m : A)
           (n : A),
      LessOrEqual lt k m -> LessOrEqual lt k n -> LessOrEqual lt k (min compare m n).
Proof.
  intros A compare lt C k m n h1 h2.
  unfold min in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h1.
  - exact h1.
  - exact h2.
Qed.

(* [max l r] is the join: above both, and below anything above both. *)

Theorem max_left_injection
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (r : A),
      LessOrEqual lt l (max compare l r).
Proof.
  intros A compare lt C l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - apply Disjunction.r.
    destruct (Comparable.specification l r) as [s _].
    exact (Biimplication.forward_elimination (compare l r = Lt) (lt l r) s c).
  - exact (Disjunction.l (Identity.reflexivity l)).
  - exact (Disjunction.l (Identity.reflexivity l)).
Qed.

Theorem max_right_injection
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (l : A)
           (r : A),
      LessOrEqual lt r (max compare l r).
Proof.
  intros A compare lt C l r.
  unfold max in |- *.
  unfold LessOrEqual in |- *.
  destruct (compare l r) as [| |] eqn:c.
  - exact (Disjunction.l (Identity.reflexivity r)).
  - apply Disjunction.l.
    destruct (Comparable.specification l r) as [_ s].
    exact (Identity.symmetry
             (Biimplication.forward_elimination (compare l r = Eq) (l = r) s c)).
  - apply Disjunction.r.
    exact (Biimplication.forward_elimination
             (compare l r = Gt) (lt r l) (gt_specification l r) c).
Qed.

Theorem max_universality
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (k : A)
           (m : A)
           (n : A),
      LessOrEqual lt m k -> LessOrEqual lt n k -> LessOrEqual lt (max compare m n) k.
Proof.
  intros A compare lt C k m n h1 h2.
  unfold max in |- *.
  destruct (compare m n) as [| |] eqn:c.
  - exact h2.
  - exact h1.
  - exact h1.
Qed.

(* Two meets, or two joins, of the same pair bound each other, so
 * antisymmetry makes them equal.
 *)

Theorem min_commutativity
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      min compare m n = min compare n m.
Proof.
  intros A compare lt C m n.
  apply (le_antisymmetry (min compare m n) (min compare n m)).
  - exact (min_universality (min compare m n) n m
            (min_right_projection m n) (min_left_projection m n)).
  - exact (min_universality (min compare n m) m n
            (min_right_projection n m) (min_left_projection n m)).
Qed.

Theorem max_commutativity
  : forall {A : Type}
           {compare : A -> A -> Comparison}
           {lt : A -> A -> Prop}
           {C : Comparable compare lt}
           (m : A)
           (n : A),
      max compare m n = max compare n m.
Proof.
  intros A compare lt C m n.
  apply (le_antisymmetry (max compare m n) (max compare n m)).
  - exact (max_universality (max compare n m) m n
            (max_right_injection n m) (max_left_injection n m)).
  - exact (max_universality (max compare m n) n m
            (max_right_injection m n) (max_left_injection m n)).
Qed.

Theorem min_associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A)
      (m : A)
      (n : A),
    min compare (min compare l m) n = min compare l (min compare m n).
Proof.
  intros A compare lt C l m n.
  apply (le_antisymmetry (min compare (min compare l m) n) (min compare l (min compare m n))).
  - apply (min_universality (min compare (min compare l m) n) l (min compare m n)).
    + exact (le_transitivity (min compare (min compare l m) n) (min compare l m) l
              (min_left_projection (min compare l m) n) (min_left_projection l m)).
    + apply (min_universality (min compare (min compare l m) n) m n).
      * exact (le_transitivity (min compare (min compare l m) n) (min compare l m) m
                (min_left_projection (min compare l m) n) (min_right_projection l m)).
      * exact (min_right_projection (min compare l m) n).
  - apply (min_universality (min compare l (min compare m n)) (min compare l m) n).
    + apply (min_universality (min compare l (min compare m n)) l m).
      * exact (min_left_projection l (min compare m n)).
      * exact (le_transitivity (min compare l (min compare m n)) (min compare m n) m
                (min_right_projection l (min compare m n)) (min_left_projection m n)).
    + exact (le_transitivity (min compare l (min compare m n)) (min compare m n) n
              (min_right_projection l (min compare m n)) (min_right_projection m n)).
Qed.

Theorem max_associativity
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (l : A)
      (m : A)
      (n : A),
    max compare (max compare l m) n = max compare l (max compare m n).
Proof.
  intros A compare lt C l m n.
  apply (le_antisymmetry (max compare (max compare l m) n) (max compare l (max compare m n))).
  - apply (max_universality (max compare l (max compare m n)) (max compare l m) n).
    + apply (max_universality (max compare l (max compare m n)) l m).
      * exact (max_left_injection l (max compare m n)).
      * exact (le_transitivity m (max compare m n) (max compare l (max compare m n))
                (max_left_injection m n) (max_right_injection l (max compare m n))).
    + exact (le_transitivity n (max compare m n) (max compare l (max compare m n))
              (max_right_injection m n) (max_right_injection l (max compare m n))).
  - apply (max_universality (max compare (max compare l m) n) l (max compare m n)).
    + exact (le_transitivity l (max compare l m) (max compare (max compare l m) n)
              (max_left_injection l m) (max_left_injection (max compare l m) n)).
    + apply (max_universality (max compare (max compare l m) n) m n).
      * exact (le_transitivity m (max compare l m) (max compare (max compare l m) n)
                (max_right_injection l m) (max_left_injection (max compare l m) n)).
      * exact (max_right_injection (max compare l m) n).
Qed.

Theorem min_idempotence
  : forall {A : Type}
      {compare : A -> A -> Comparison}
      {lt : A -> A -> Prop}
      {C : Comparable compare lt}
      (n : A),
    min compare n n = n.
Proof.
  intros A compare lt C n.
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
  intros A compare lt C n.
  unfold max in |- *.
  rewrite (Comparable.reflexivity n) in |- *.
  reflexivity.
Qed.

End Comparable.
