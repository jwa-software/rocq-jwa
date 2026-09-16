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

Theorem xor_associativity
  : forall (b1 : Bool) (b2 : Bool) (b3 : Bool),
      xor (xor b1 b2) b3 = xor b1 (xor b2 b3).
Proof.
  (* The context gains [b1], [b2] and [b3]:
     [|- xor (xor b1 b2) b3 = xor b1 (xor b2 b3)] *)
  intros b1 b2 b3.
  (* Eight cases; [xor] and [negate] both reduce on ctors, so both sides
     reduce to the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; destruct b3 as [|]; reflexivity.
Qed.

Lemma xor_false_left : forall (b : Bool), xor false b = b.
Proof.
  (* The context gains [b]. [xor] matches its first argument, and [false]
     returns the second untouched: [|- b = b] *)
  intros b.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma xor_false_right : forall (b : Bool), xor b false = b.
Proof.
  (* The context gains [b]: [|- xor b false = b] *)
  intros b.
  (* Nothing reduces until [b] is a ctor, since [xor] matches it first; the
     [true] case goes through [negate false]. *)
  destruct b as [|]; reflexivity.
Qed.

Theorem xor_commutativity
  : forall (b1 : Bool) (b2 : Bool), xor b1 b2 = xor b2 b1.
Proof.
  (* The context gains [b1] and [b2]: [|- xor b1 b2 = xor b2 b1] *)
  intros b1 b2.
  (* Four cases; both sides reduce to the same ctor in every one. *)
  destruct b1 as [|]; destruct b2 as [|]; reflexivity.
Qed.

(* Every element is its own inverse under [xor], which is what makes
   [(Bool, xor, false)] more than a monoid; the group structure waits for a
   [Group] class. *)
Theorem xor_self_inverse : forall (b : Bool), xor b b = false.
Proof.
  (* The context gains [b]: [|- xor b b = false] *)
  intros b.
  (* Two cases: [xor true true] is [negate true], [xor false false] is
     [false]. *)
  destruct b as [|]; reflexivity.
Qed.

(* The bridge from a computed answer to a statement. [Holds true] is [True]
   and [Holds false] is [False] by reduction, so case analysis on a [Bool]
   turns each law below into a concrete implication in both directions. *)
(* [Bool -> Prop] *)
Definition Holds := fun (b : Bool) =>
  match b with
  | true  => True
  | false => False
  end.

Theorem holds_conjunction
  : forall (b1 : Bool) (b2 : Bool),
      Holds (and b1 b2) <-> Holds b1 /\ Holds b2.
Proof.
  (* The context gains [b1] and [b2]:
     [|- Holds (and b1 b2) <-> Holds b1 /\ Holds b2] *)
  intros b1 b2.
  (* [<->] is a [Definition], so [split] cannot see the [/\] beneath it:
     [|- (Holds (and b1 b2) -> Holds b1 /\ Holds b2)
         /\ (Holds b1 /\ Holds b2 -> Holds (and b1 b2))] *)
  unfold Biconditional in |- *.
  (* Four cases, each a concrete implication both ways. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (True -> True /\ True) /\ (True /\ True -> True)] *)
    split; intro h.
    + (* [|- True /\ True], and [I] proves each side. *)
      split; exact I.
    + (* [|- True] *)
      exact I.
  - (* [|- (False -> True /\ False) /\ (True /\ False -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- False], and the right half of [h] is one; the left half is
         dropped. *)
      destruct h as [_ h]. exact h.
  - (* [|- (False -> False /\ True) /\ (False /\ True -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- False], and the left half of [h] is one; the right half is
         dropped. *)
      destruct h as [h _]. exact h.
  - (* [|- (False -> False /\ False) /\ (False /\ False -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- False], and either half of [h] is one; the left is taken. *)
      destruct h as [h _]. exact h.
Qed.

Theorem holds_disjunction
  : forall (b1 : Bool) (b2 : Bool),
      Holds (or b1 b2) <-> Holds b1 \/ Holds b2.
Proof.
  (* The context gains [b1] and [b2]:
     [|- Holds (or b1 b2) <-> Holds b1 \/ Holds b2] *)
  intros b1 b2.
  (* [|- (Holds (or b1 b2) -> Holds b1 \/ Holds b2)
         /\ (Holds b1 \/ Holds b2 -> Holds (or b1 b2))] *)
  unfold Biconditional in |- *.
  (* Four cases; only the last has [or] reduce to [false]. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (True -> True \/ True) /\ (True \/ True -> True)] *)
    split; intro h.
    + (* Either side will do, so [exact (Or_right I)] would close it as well;
         the left one is taken. *)
      exact (Or_left I).
    + (* [|- True] *)
      exact I.
  - (* [|- (True -> True \/ False) /\ (True \/ False -> True)] *)
    split; intro h.
    + (* Only the left side holds. *)
      exact (Or_left I).
    + (* [|- True] *)
      exact I.
  - (* [|- (True -> False \/ True) /\ (False \/ True -> True)] *)
    split; intro h.
    + (* Only the right side holds. *)
      exact (Or_right I).
    + (* [|- True] *)
      exact I.
  - (* [|- (False -> False \/ False) /\ (False \/ False -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [False]. *)
      destruct h as [h1 | h2]. exact h1. exact h2.
Qed.

Theorem holds_exclusive_disjunction
  : forall (b1 : Bool) (b2 : Bool),
      Holds (xor b1 b2) <-> Holds b1 _\/_ Holds b2.
Proof.
  (* The context gains [b1] and [b2]:
     [|- Holds (xor b1 b2) <-> Holds b1 _\/_ Holds b2] *)
  intros b1 b2.
  (* [|- (Holds (xor b1 b2) -> Holds b1 _\/_ Holds b2)
         /\ (Holds b1 _\/_ Holds b2 -> Holds (xor b1 b2))] *)
  unfold Biconditional in |- *.
  (* Four cases; [xor] reduces to [false] in the first and the last. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (False -> True _\/_ True) /\ (True _\/_ True -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [True] and a [~ True], which is
         [True -> False]; applying the one to the other gives the goal. *)
      destruct h as [t nt | nt t]. exact (nt t). exact (nt t).
  - (* [|- (True -> True _\/_ False) /\ (True _\/_ False -> True)] *)
    split; intro h.
    + (* [Xor_left] asks for a [True] and a [~ False], which is
         [False -> False]; [I] is the first and the identity the second. *)
      exact (Xor_left I (fun (f : False) => f)).
    + (* [|- True] *)
      exact I.
  - (* [|- (True -> False _\/_ True) /\ (False _\/_ True -> True)] *)
    split; intro h.
    + (* [Xor_right] asks for the same two in the other order. *)
      exact (Xor_right (fun (f : False) => f) I).
    + (* [|- True] *)
      exact I.
  - (* [|- (False -> False _\/_ False) /\ (False _\/_ False -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [False]; the [~ False] beside it is
         dropped. *)
      destruct h as [f _ | _ f]. exact f. exact f.
Qed.

Theorem holds_negation : forall (b : Bool), Holds (negate b) <-> ~ Holds b.
Proof.
  (* The context gains [b]: [|- Holds (negate b) <-> ~ Holds b] *)
  intros b.
  (* Both [<->] and [~] are definitions and have to come off before the
     structure underneath is visible. *)
  unfold Biconditional, Not in |- *.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- (False -> True -> False) /\ ((True -> False) -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h] turns a [True] into a [False], and [I] is a [True]. *)
      exact (h I).
  - (* [|- (True -> False -> False) /\ ((False -> False) -> True)] *)
    split; intro h.
    + (* The hypothesis introduced next is a [False]. *)
      intro k. destruct k.
    + (* [|- True] *)
      exact I.
Qed.

(* The other reading of [Holds], and what makes it usable with [rewrite] and
   [discriminate]. *)
Theorem holds_equality : forall (b : Bool), Holds b <-> b = true.
Proof.
  (* The context gains [b]: [|- Holds b <-> b = true] *)
  intros b.
  (* [|- (Holds b -> b = true) /\ (b = true -> Holds b)] *)
  unfold Biconditional in |- *.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- (True -> true = true) /\ (true = true -> True)] *)
    split; intro h.
    + (* Both sides are the same term. *)
      reflexivity.
    + (* [|- True] *)
      exact I.
  - (* [|- (False -> false = true) /\ (false = true -> False)] *)
    split; intro h.
    + (* [h : False], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h] claims [false = true], and the two are different ctors. *)
      discriminate h.
Qed.

End Bool.

(* The levels are reserved in [Core.Notations]; only the meanings belong
   here. Declared at file level, they reach a client through
   [Require Export]. *)
Notation "b1 && b2" := (Bool.and b1 b2) : jwa_type_scope.
Notation "b1 ^^ b2" := (Bool.xor b1 b2) : jwa_type_scope.
Notation "b1 || b2" := (Bool.or  b1 b2) : jwa_type_scope.

Instance Bool_and_monoid : Monoid.T Bool Bool.and true :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Bool.and_associativity |}
   ; Monoid.identity_left  := Bool.and_true_left
   ; Monoid.identity_right := Bool.and_true_right |}.

Instance Bool_or_monoid : Monoid.T Bool Bool.or false :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Bool.or_associativity |}
   ; Monoid.identity_left  := Bool.or_false_left
   ; Monoid.identity_right := Bool.or_false_right |}.

Instance Bool_xor_monoid : Monoid.T Bool Bool.xor false :=
  {| Monoid.semigroup :=
       {| Semigroup.associativity := Bool.xor_associativity |}
   ; Monoid.identity_left  := Bool.xor_false_left
   ; Monoid.identity_right := Bool.xor_false_right |}.
