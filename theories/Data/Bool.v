(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->], [~] and [=]: with [-noinit] a file has only what
   it requires. [Structures.Semigroup], [Structures.Monoid] and
   [Structures.Commutative] are the classes the instances at the bottom
   fill. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Commutative.
From jwa Require Import Structures.AbelianGroup.
From jwa Require Import Structures.Group.
From jwa Require Import Structures.Ring.

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.

Theorem Bool_distinctness : ~ (true = false).
Proof.
  (* The goal goes from [~ (true = false)] to [true = false -> Falsum]. *)
  unfold Negation in |- *.
  (* The goal goes from [true = false -> Falsum] to [Falsum], and the context
     gains [e : true = false]. *)
  intro e.
  (* [e] claims [true = false], but the only way to build an equality is
     [Equijunction.reflexivity], whose two sides are the same term, and
     [true] and [false] are different ctors. No such proof exists, and from
     that impossibility [discriminate] proves the goal [Falsum]. *)
  discriminate e.
Qed.

(* A module may carry the type's name; its members read [Bool.and]. *)
Module Bool.

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

(* Exclusive or: [true] when exactly one side is. [true] flips the other
   side, [false] leaves it alone. *)
(* [Bool -> Bool -> Bool] *)
Definition xor := fun (b1 : Bool) (b2 : Bool) =>
  match b1 with
  | true  => negate b2
  | false => b2
  end.

Theorem negate_involution : forall (b : Bool), negate (negate b) = b.
Proof.
  (* The context gains [b]: [|- negate (negate b) = b] *)
  intros b.
  (* Two cases, one per ctor; both sides reduce to that same ctor in each. *)
  destruct b as [|]; reflexivity.
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

(* Every element is its own inverse under [xor], which is what makes
   [(Bool, xor, false)] more than a monoid; the group structure waits for a
   [Group] class. *)
Theorem xor_self_inverse : forall (b : Bool), xor b b = false.
Proof.
  intros b.
  destruct b as [|]; reflexivity.
Qed.

(* [and] distributes over [xor] on both sides: the law that makes
 * [(Bool, xor, and)] a ring, a truth table as the laws above.
 *)

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

(* The bridge from a computed answer to a statement. [Assert true] is [Verum]
   and [Assert false] is [Falsum] by reduction, so case analysis on a [Bool]
   turns each law below into a concrete implication in both directions. *)
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
  (* The context gains [b1] and [b2]:
     [|- Assert (and b1 b2) <-> Assert b1 /\ Assert b2] *)
  intros b1 b2.
  (* Four cases, each a concrete implication both ways. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- Verum <-> Verum /\ Verum] *)
    split; intro h.
    + (* [|- Verum /\ Verum], and [I] proves each side. *)
      split; exact I.
    + (* [|- Verum] *)
      exact I.
  - (* [|- Falsum <-> Verum /\ Falsum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- Falsum], and the right half of [h] is one; the left half is
         dropped. *)
      destruct h as [_ h]. exact h.
  - (* [|- Falsum <-> Falsum /\ Verum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- Falsum], and the left half of [h] is one; the right half is
         dropped. *)
      destruct h as [h _]. exact h.
  - (* [|- Falsum <-> Falsum /\ Falsum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- Falsum], and either half of [h] is one; the left is taken. *)
      destruct h as [h _]. exact h.
Qed.

Theorem assert_disjunction
  : forall (b1 : Bool) (b2 : Bool),
      Assert (or b1 b2) <-> Assert b1 \/ Assert b2.
Proof.
  (* The context gains [b1] and [b2]:
     [|- Assert (or b1 b2) <-> Assert b1 \/ Assert b2] *)
  intros b1 b2.
  (* Four cases; only the last has [or] reduce to [false]. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- Verum <-> Verum \/ Verum] *)
    split; intro h.
    + (* Either side will do, so [exact (Disjunction.right I)] would close it
         as well; the left one is taken. *)
      exact (Disjunction.left I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- Verum <-> Verum \/ Falsum] *)
    split; intro h.
    + (* Only the left side holds. *)
      exact (Disjunction.left I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- Verum <-> Falsum \/ Verum] *)
    split; intro h.
    + (* Only the right side holds. *)
      exact (Disjunction.right I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- Falsum <-> Falsum \/ Falsum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [Falsum]. *)
      destruct h as [h1 | h2]. exact h1. exact h2.
Qed.

Theorem assert_sejunction
  : forall (b1 : Bool) (b2 : Bool),
      Assert (xor b1 b2) <-> Assert b1 _\/_ Assert b2.
Proof.
  (* The context gains [b1] and [b2]:
     [|- Assert (xor b1 b2) <-> Assert b1 _\/_ Assert b2] *)
  intros b1 b2.
  (* Four cases; [xor] reduces to [false] in the first and the last. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- Falsum <-> Verum _\/_ Verum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [Verum] and a [~ Verum], which is
         [Verum -> Falsum]; applying the one to the other gives the goal. *)
      destruct h as [t nt | nt t]. exact (nt t). exact (nt t).
  - (* [|- Verum <-> Verum _\/_ Falsum] *)
    split; intro h.
    + (* [Sejunction_left] asks for a [Verum] and a [~ Falsum], which is
         [Falsum -> Falsum]; [I] is the first and the identity the second. *)
      exact (Sejunction_left I (fun (f : Falsum) => f)).
    + (* [|- Verum] *)
      exact I.
  - (* [|- Verum <-> Falsum _\/_ Verum] *)
    split; intro h.
    + (* [Sejunction_right] asks for the same two in the other order. *)
      exact (Sejunction_right (fun (f : Falsum) => f) I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- Falsum <-> Falsum _\/_ Falsum] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [Falsum]; the [~ Falsum] beside it is
         dropped. *)
      destruct h as [f _ | _ f]. exact f. exact f.
Qed.

Theorem assert_negation
  : forall (b : Bool), Assert (negate b) <-> ~ Assert b.
Proof.
  (* The context gains [b]: [|- Assert (negate b) <-> ~ Assert b] *)
  intros b.
  (* [~] is a definition and has to come off before the arrow underneath is
     visible: [|- Assert (negate b) <-> (Assert b -> Falsum)] *)
  unfold Negation in |- *.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- Falsum <-> (Verum -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h] turns a [Verum] into a [Falsum], and [I] is a [Verum]. *)
      exact (h I).
  - (* [|- Verum <-> (Falsum -> Falsum)] *)
    split; intro h.
    + (* The hypothesis introduced next is a [Falsum]. *)
      intro k. destruct k.
    + (* [|- Verum] *)
      exact I.
Qed.

(* The other reading of [Assert], and what makes it usable with [rewrite] and
   [discriminate]. *)
Theorem assert_equijunction : forall (b : Bool), Assert b <-> b = true.
Proof.
  (* The context gains [b]: [|- Assert b <-> b = true] *)
  intros b.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- Verum <-> true = true] *)
    split; intro h.
    + (* Both sides are the same term. *)
      reflexivity.
    + (* [|- Verum] *)
      exact I.
  - (* [|- Falsum <-> false = true] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h] claims [false = true], and the two are different ctors. *)
      discriminate h.
Qed.

End Bool.

(* The levels are reserved in [Core.Notations]; only the meanings belong
   here. Declared at file level, they reach a client through
   [Require Export]. *)
Notation "b1 && b2" := (Bool.and b1 b2)
  : jwa_type_scope.
Notation "b1 ^^ b2" := (Bool.xor b1 b2)
  : jwa_type_scope.
Notation "b1 || b2" := (Bool.or  b1 b2)
  : jwa_type_scope.

(* Each identity law on the left computes, so it is reflexivity stated on
   the reduced term; each on the right is commutativity at the identity,
   whose right side computes the same way. *)
Instance Bool_and_monoid
  : Monoid.T Bool Bool.and true :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bool.and_associativity |}
   ; Monoid.left_identity  :=
      fun (b : Bool) => Equijunction.reflexivity (Bool.and true b)
   ; Monoid.right_identity :=
      fun (b : Bool) => Bool.and_commutativity b true
  |}.

Instance Bool_or_monoid
  : Monoid.T Bool Bool.or false :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bool.or_associativity |}
   ; Monoid.left_identity  :=
      fun (b : Bool) => Equijunction.reflexivity (Bool.or false b)
   ; Monoid.right_identity :=
      fun (b : Bool) => Bool.or_commutativity b false
  |}.

Instance Bool_xor_monoid
  : Monoid.T Bool Bool.xor false :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Bool.xor_associativity |}
  ; Monoid.left_identity :=
      fun (b : Bool) => Equijunction.reflexivity (Bool.xor false b)
  ; Monoid.right_identity :=
      fun (b : Bool) => Bool.xor_commutativity b false
  |}.

Instance Bool_and_commutative
  : Commutative.T Bool Bool.and := {|
      Commutative.commutativity := Bool.and_commutativity
  |}.

Instance Bool_or_commutative
  : Commutative.T Bool Bool.or := {|
      Commutative.commutativity := Bool.or_commutativity
  |}.

Instance Bool_xor_commutative
  : Commutative.T Bool Bool.xor := {|
      Commutative.commutativity := Bool.xor_commutativity
  |}.

(* Every element is its own inverse under [xor], so [(Bool, xor, false)] is
 * a group, and a commutative one; with [and] as the product it is a ring,
 * the Boolean ring. [inverse] is the identity function, so the two inverse
 * laws are [xor_self_inverse] as it stands.
 *)
Instance Bool_xor_group
  : Group.T Bool Bool.xor false (fun (b : Bool) => b) :=
  {| Group.monoid        := Bool_xor_monoid
   ; Group.left_inverse  := Bool.xor_self_inverse
   ; Group.right_inverse := Bool.xor_self_inverse |}.

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
