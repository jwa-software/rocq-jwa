(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->], [~] and [=]: with [-noinit] a file has only what
   it requires. [Structures.Semigroup] and [Structures.Monoid] are the classes
   the instances at the bottom fill. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.

(* [true] first: [if] takes the first constructor as its [then] branch. *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.

Theorem Bool_distinctness : ~ (true = false).
Proof.
  (* The goal goes from [~ (true = false)] to [true = false -> False]. *)
  unfold Not in |- *.
  (* The goal goes from [true = false -> False] to [False], and the context
     gains [e : true = false]. *)
  intro e.
  (* [e] claims [true = false], but the only way to build an equality is
     [Eq_reflexivity], whose two sides are the same term, and [true] and
     [false] are different ctors. No such proof exists, and from that
     impossibility [discriminate] proves the goal [False]. *)
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

Theorem negate_self_inversion : forall (b : Bool), negate (negate b) = b.
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
  (* The context gains [b1], [b2] and [b3]:
     [|- and (and b1 b2) b3 = and b1 (and b2 b3)] *)
  intros b1 b2 b3.
  (* Eight cases, one per assignment of the three ctors; both sides reduce to
     the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Lemma and_true_left : forall (b : Bool), and true b = b.
Proof.
  (* The context gains [b]. [and] matches its first argument, and [true]
     returns the second untouched: [|- b = b] *)
  intros b.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma and_true_right : forall (b : Bool), and b true = b.
Proof.
  (* The context gains [b]: [|- and b true = b] *)
  intros b.
  (* Nothing reduces until [b] is a ctor, since [and] matches it first. *)
  destruct b as [|]; reflexivity.
Qed.

Theorem and_commutativity
  : forall (b1 : Bool) (b2 : Bool), and b1 b2 = and b2 b1.
Proof.
  (* The context gains [b1] and [b2]: [|- and b1 b2 = and b2 b1] *)
  intros b1 b2.
  (* Four cases; both sides reduce to the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

Theorem or_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      or (or b1 b2) b3 = or b1 (or b2 b3).
Proof.
  (* The context gains [b1], [b2] and [b3]:
     [|- or (or b1 b2) b3 = or b1 (or b2 b3)] *)
  intros b1 b2 b3.
  (* Eight cases; both sides reduce to the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Lemma or_false_left : forall (b : Bool), or false b = b.
Proof.
  (* The context gains [b]. [or] matches its first argument, and [false]
     returns the second untouched: [|- b = b] *)
  intros b.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma or_false_right : forall (b : Bool), or b false = b.
Proof.
  (* The context gains [b]: [|- or b false = b] *)
  intros b.
  (* Nothing reduces until [b] is a ctor, since [or] matches it first. *)
  destruct b as [|]; reflexivity.
Qed.

Theorem or_commutativity : forall (b1 : Bool) (b2 : Bool), or b1 b2 = or b2 b1.
Proof.
  (* The context gains [b1] and [b2]: [|- or b1 b2 = or b2 b1] *)
  intros b1 b2.
  (* Four cases; both sides reduce to the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

End Bool.

Instance Bool_and_monoid : Monoid Bool Bool.and true :=
  {| Monoid_semigroup :=
       {| Semigroup_associativity := Bool.and_associativity |}
   ; Monoid_identity_left  := Bool.and_true_left
   ; Monoid_identity_right := Bool.and_true_right |}.

Instance Bool_or_monoid : Monoid Bool Bool.or false :=
  {| Monoid_semigroup :=
       {| Semigroup_associativity := Bool.or_associativity |}
   ; Monoid_identity_left  := Bool.or_false_left
   ; Monoid_identity_right := Bool.or_false_right |}.
