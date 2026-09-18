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

Theorem negate_involution : forall (b : Bool), negate (negate b) = b.
Proof.
  intros b.
  destruct b as [|]; simpl in |- *; reflexivity.
Qed.

Theorem and_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      and (and b1 b2) b3 = and b1 (and b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem and_commutativity
  : forall (b1 : Bool) (b2 : Bool), and b1 b2 = and b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem or_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      or (or b1 b2) b3 = or b1 (or b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem or_commutativity : forall (b1 : Bool) (b2 : Bool), or b1 b2 = or b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem xor_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      xor (xor b1 b2) b3 = xor b1 (xor b2 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem xor_commutativity
  : forall (b1 : Bool) (b2 : Bool), xor b1 b2 = xor b2 b1.
Proof.
  intros b1 b2.
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem xor_irreflexivity : forall (b : Bool), xor b b = false.
Proof.
  intros b.
  destruct b as [|]; reflexivity.
Qed.

Theorem and_left_distributivity_over_xor
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      and b1 (xor b2 b3) = xor (and b1 b2) (and b1 b3).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Theorem and_right_distributivity_over_xor
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      and (xor b2 b3) b1 = xor (and b2 b1) (and b3 b1).
Proof.
  intros b1 b2 b3.
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
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
  : forall (b1 : Bool) (b2 : Bool),
      Assert (and b1 b2) <-> Assert b1 /\ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  + split; exact I.
  + exact I.
  + contradiction.
  + destruct h as [_ h].
    exact h.
  + contradiction.
  + destruct h as [h _].
    exact h.
  + contradiction.
  + destruct h as [h _].
    exact h.
Qed.

Theorem assert_disjunction
  : forall (b1 : Bool) (b2 : Bool),
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
  + contradiction.
  + destruct h as [h1 | h2].
    * exact h1.
    * exact h2.
Qed.

Theorem assert_sejunction
  : forall (b1 : Bool) (b2 : Bool),
      Assert (xor b1 b2) <-> Assert b1 _\/_ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  + contradiction.
  + destruct h as [t nt | nt t].
    * exact (nt t).
    * exact (nt t).
  + exact (Sejunction.left  I (fun (f : Falsum) => f)).
  + exact I.
  + exact (Sejunction.right (fun (f : Falsum) => f) I).
  + exact I.
  + contradiction.
  + destruct h as [f _ | _ f].
    * exact f.
    * exact f.
Qed.

Theorem assert_negation
  : forall (b : Bool), Assert (negate b) <-> ~ Assert b.
Proof.
  intros b.
  unfold Negation in |- *.
  destruct b as [|]; simpl in |- *; split; intro h.
  + contradiction.
  + exact (h I).
  + intro k.
    destruct k.
  + exact I.
Qed.

Theorem assert_specification : forall (b : Bool), Assert b <-> b = true.
Proof.
  intros b.
  destruct b as [|]; simpl in |- *; split; intro h.
  + reflexivity.
  + exact I.
  + contradiction.
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
  : Monoid.T Bool Bool.and true :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.and_associativity |}
   ; Monoid.left_identity  :=
       fun (b : Bool) => Identity.reflexivity (Bool.and true b)
   ; Monoid.right_identity :=
       fun (b : Bool) => Bool.and_commutativity b true |}.

Instance Bool_or_monoid
  : Monoid.T Bool Bool.or false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.or_associativity |}
   ; Monoid.left_identity  :=
       fun (b : Bool) => Identity.reflexivity (Bool.or false b)
   ; Monoid.right_identity :=
       fun (b : Bool) => Bool.or_commutativity b false |}.

Instance Bool_xor_monoid
  : Monoid.T Bool Bool.xor false :=
  {| Monoid.semigroup      :=
       {| Semigroup.associativity := Bool.xor_associativity |}
   ; Monoid.left_identity  :=
       fun (b : Bool) => Identity.reflexivity (Bool.xor false b)
   ; Monoid.right_identity :=
       fun (b : Bool) => Bool.xor_commutativity b false |}.

Instance Bool_and_commutative
  : Commutative.T Bool Bool.and :=
  {| Commutative.commutativity := Bool.and_commutativity |}.

Instance Bool_or_commutative
  : Commutative.T Bool Bool.or :=
  {| Commutative.commutativity := Bool.or_commutativity |}.

Instance Bool_xor_commutative
  : Commutative.T Bool Bool.xor :=
  {| Commutative.commutativity := Bool.xor_commutativity |}.

Instance Bool_xor_group
  : Group.T Bool Bool.xor false (fun (b : Bool) => b) :=
  {| Group.monoid        := Bool_xor_monoid
   ; Group.left_inverse  := Bool.xor_irreflexivity
   ; Group.right_inverse := Bool.xor_irreflexivity |}.

Instance Bool_xor_abelian_group
  : AbelianGroup.T Bool Bool.xor false (fun (b : Bool) => b) :=
  {| AbelianGroup.group       := Bool_xor_group
   ; AbelianGroup.commutative := Bool_xor_commutative |}.

Instance Bool_ring
  : Ring.T Bool Bool.xor false (fun (b : Bool) => b) Bool.and true :=
  {| Ring.add_group            := Bool_xor_abelian_group
   ; Ring.mul_monoid           := Bool_and_monoid
   ; Ring.left_distributivity  := Bool.and_left_distributivity_over_xor
   ; Ring.right_distributivity := Bool.and_right_distributivity_over_xor |}.
