(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.

(* A module may carry the type's name; its members read [Bool.and]. *)
Module Bool.

Theorem distinctness : ~ (true = false).
Proof.
  unfold Negation in |- *.
  intro e.
  discriminate e.
Qed.

(* [Bool -> Bool] *)
Definition negate := fun (b : Bool) =>
  match b with
  | true  => false
  | false => true
  end.

(* [Bool -> Bool -> Bool] *)
Definition and := fun (b1 : Bool) (b2 : Bool) =>
  match b1 with
  | true  => b2
  | false => false
  end.

(* [Bool -> Bool -> Bool] *)
Definition or := fun (b1 : Bool) (b2 : Bool) =>
  match b1 with
  | true  => true
  | false => b2
  end.

(* [Bool -> Bool -> Bool] *)
Definition xor := fun (b1 : Bool) (b2 : Bool) =>
  match b1 with
  | true  => negate b2
  | false => b2
  end.

Theorem negate_involution : forall (b : Bool) . negate (negate b) = b.
Proof.
  intros b.
  destruct b as [|]; simpl in |- *; reflexivity.
Qed.

Theorem and_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      and (and b1 b2) b3 = and b1 (and b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem and_commutativity
  : forall (b1 : Bool) (b2 : Bool) . and b1 b2 = and b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem and_identity
  : forall (b : Bool) . (and true b = b) /\ (and b true = b).
Proof.
  intros b.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (and_commutativity b true) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem or_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      or (or b1 b2) b3 = or b1 (or b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem or_commutativity : forall (b1 : Bool) (b2 : Bool) . or b1 b2 = or b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem or_identity
  : forall (b : Bool) . (or false b = b) /\ (or b false = b).
Proof.
  intros b.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (or_commutativity b false) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem xor_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      xor (xor b1 b2) b3 = xor b1 (xor b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem xor_commutativity
  : forall (b1 : Bool) (b2 : Bool) . xor b1 b2 = xor b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem xor_identity
  : forall (b : Bool) . (xor false b = b) /\ (xor b false = b).
Proof.
  intros b.
  split.
  - simpl in |- *.
    reflexivity.
  - rewrite (xor_commutativity b false) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem xor_irreflexivity : forall (b : Bool) . xor b b = false.
Proof.
  intros b.
  destruct b as [|]; reflexivity.
Qed.

Theorem xor_inverse
  : forall (b : Bool) . (xor b b = false) /\ (xor b b = false).
Proof.
  intros b.
  split.
  - exact (xor_irreflexivity b).
  - exact (xor_irreflexivity b).
Qed.

Theorem and_left_distributivity_over_xor
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      and b1 (xor b2 b3) = xor (and b1 b2) (and b1 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem and_right_distributivity_over_xor
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      and (xor b2 b3) b1 = xor (and b2 b1) (and b3 b1).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem and_distributivity_over_xor
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool) .
      (and b1 (xor b2 b3) = xor (and b1 b2) (and b1 b3))
    /\ (and (xor b2 b3) b1 = xor (and b2 b1) (and b3 b1)).
Proof.
  intros b1 b2 b3.
  split.
  - exact (and_left_distributivity_over_xor b1 b2 b3).
  - exact (and_right_distributivity_over_xor b1 b2 b3).
Qed.

(* The bridge from a computed answer to a statement. [Assert true] is
 * [Verum] and [Assert false] is [Falsum] by reduction, so case analysis on
 * a [Bool] turns each law below into a concrete implication in both
 * directions.
 *)
(* [Bool -> Prop] *)
Definition Assert := fun (b : Bool) =>
  match b with
  | true  => Verum
  | false => Falsum
  end.

Theorem assert_conjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (and b1 b2) <-> Assert b1 /\ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  + split; exact I.
  + exact I.
  + contradiction h.
  + destruct h as [_ h].
    exact h.
  + contradiction h.
  + destruct h as [h _].
    exact h.
  + contradiction h.
  + destruct h as [h _].
    exact h.
Qed.

Theorem assert_disjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (or b1 b2) <-> Assert b1 \/ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  + exact (Disjunction.left I).
  + exact I.
  + exact (Disjunction.left I).
  + exact I.
  + exact (Disjunction.right I).
  + exact I.
  + contradiction h.
  + destruct h as [h1 | h2].
    * exact h1.
    * exact h2.
Qed.

Theorem assert_sejunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (xor b1 b2) <-> Assert b1 _\/_ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  + contradiction h.
  + destruct h as [t nt | nt t].
    * exact (nt t).
    * exact (nt t).
  + exact (Sejunction.left  I (fun (f : Falsum) => f)).
  + exact I.
  + exact (Sejunction.right (fun (f : Falsum) => f) I).
  + exact I.
  + contradiction h.
  + destruct h as [f _ | _ f].
    * exact f.
    * exact f.
Qed.

Theorem assert_negation
  : forall (b : Bool) . Assert (negate b) <-> ~ Assert b.
Proof.
  intros b.
  unfold Negation in |- *.
  destruct b as [|]; simpl in |- *; split; intro h.
  + contradiction h.
  + exact (h I).
  + intro k.
    destruct k.
  + exact I.
Qed.

Theorem assert_specification : forall (b : Bool) . Assert b <-> b = true.
Proof.
  intros b.
  destruct b as [|]; simpl in |- *; split; intro h.
  + reflexivity.
  + exact I.
  + contradiction h.
  + discriminate h.
Qed.

End Bool.

(* The levels are reserved in [Core.Notations]; only the meanings belong
 * here. Declared at file level, they reach a client through
 * [Require Export].
 *)
Notation "b1 && b2" := (Bool.and b1 b2)
  : jwa_type_scope.
Notation "b1 ^^ b2" := (Bool.xor b1 b2)
  : jwa_type_scope.
Notation "b1 || b2" := (Bool.or  b1 b2)
  : jwa_type_scope.

Instance Bool_and_monoid
  : Monoid Bool.and true :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.and_associativity |}
   ; Monoid.identity       := Bool.and_identity |}.

Instance Bool_or_monoid
  : Monoid Bool.or false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.or_associativity |}
   ; Monoid.identity       := Bool.or_identity |}.

Instance Bool_xor_monoid
  : Monoid Bool.xor false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.xor_associativity |}
   ; Monoid.identity       := Bool.xor_identity |}.

Instance Bool_and_commutative
  : Commutative Bool.and :=
  {| Commutative.commutativity := Bool.and_commutativity |}.

Instance Bool_or_commutative
  : Commutative Bool.or :=
  {| Commutative.commutativity := Bool.or_commutativity |}.

Instance Bool_xor_commutative
  : Commutative Bool.xor :=
  {| Commutative.commutativity := Bool.xor_commutativity |}.

Instance Bool_xor_group
  : Group Bool.xor false (fun (b : Bool) => b) :=
  {| Group.monoid  := Bool_xor_monoid
   ; Group.inverse := Bool.xor_inverse |}.

Instance Bool_xor_abelian_group
  : AbelianGroup Bool.xor false (fun (b : Bool) => b) :=
  {| AbelianGroup.group       := Bool_xor_group
   ; AbelianGroup.commutative := Bool_xor_commutative |}.

Instance Bool_ring
  : Ring Bool.xor false (fun (b : Bool) => b) Bool.and true :=
  {| Ring.abelian_group  := Bool_xor_abelian_group
   ; Ring.monoid         := Bool_and_monoid
   ; Ring.distributivity := Bool.and_distributivity_over_xor |}.
