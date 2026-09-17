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
  (* The goal goes from [~ (true = false)] to [true = false -> Falsum]. *)
  unfold Unjunction in |- *.
  (* The goal goes from [true = false -> Falsum] to [Falsum], and the context
     gains [e : true = false]. *)
  intro e.
  (* [e] claims [true = false], but the only way to build an equality is
     [Equijunction_reflexivity], whose two sides are the same term, and
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
  (* [<->] is a [Definition], so [split] cannot see the [/\] beneath it:
     [|- (Assert (and b1 b2) -> Assert b1 /\ Assert b2)
         /\ (Assert b1 /\ Assert b2 -> Assert (and b1 b2))] *)
  unfold Bijunction in |- *.
  (* Four cases, each a concrete implication both ways. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (Verum -> Verum /\ Verum) /\ (Verum /\ Verum -> Verum)] *)
    split; intro h.
    + (* [|- Verum /\ Verum], and [I] proves each side. *)
      split; exact I.
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Falsum -> Verum /\ Falsum) /\ (Verum /\ Falsum -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- Falsum], and the right half of [h] is one; the left half is
         dropped. *)
      destruct h as [_ h]. exact h.
  - (* [|- (Falsum -> Falsum /\ Verum) /\ (Falsum /\ Verum -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [|- Falsum], and the left half of [h] is one; the right half is
         dropped. *)
      destruct h as [h _]. exact h.
  - (* [|- (Falsum -> Falsum /\ Falsum) /\ (Falsum /\ Falsum -> Falsum)] *)
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
  (* [|- (Assert (or b1 b2) -> Assert b1 \/ Assert b2)
         /\ (Assert b1 \/ Assert b2 -> Assert (or b1 b2))] *)
  unfold Bijunction in |- *.
  (* Four cases; only the last has [or] reduce to [false]. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (Verum -> Verum \/ Verum) /\ (Verum \/ Verum -> Verum)] *)
    split; intro h.
    + (* Either side will do, so [exact (Disjunction_right I)] would close it
         as well; the left one is taken. *)
      exact (Disjunction_left I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Verum -> Verum \/ Falsum) /\ (Verum \/ Falsum -> Verum)] *)
    split; intro h.
    + (* Only the left side holds. *)
      exact (Disjunction_left I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Verum -> Falsum \/ Verum) /\ (Falsum \/ Verum -> Verum)] *)
    split; intro h.
    + (* Only the right side holds. *)
      exact (Disjunction_right I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Falsum -> Falsum \/ Falsum) /\ (Falsum \/ Falsum -> Falsum)] *)
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
  (* [|- (Assert (xor b1 b2) -> Assert b1 _\/_ Assert b2)
         /\ (Assert b1 _\/_ Assert b2 -> Assert (xor b1 b2))] *)
  unfold Bijunction in |- *.
  (* Four cases; [xor] reduces to [false] in the first and the last. *)
  destruct b1 as [|]; destruct b2 as [|]; simpl in |- *.
  - (* [|- (Falsum -> Verum _\/_ Verum) /\ (Verum _\/_ Verum -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [Verum] and a [~ Verum], which is
         [Verum -> Falsum]; applying the one to the other gives the goal. *)
      destruct h as [t nt | nt t]. exact (nt t). exact (nt t).
  - (* [|- (Verum -> Verum _\/_ Falsum) /\ (Verum _\/_ Falsum -> Verum)] *)
    split; intro h.
    + (* [Sejunction_left] asks for a [Verum] and a [~ Falsum], which is
         [Falsum -> Falsum]; [I] is the first and the identity the second. *)
      exact (Sejunction_left I (fun (f : Falsum) => f)).
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Verum -> Falsum _\/_ Verum) /\ (Falsum _\/_ Verum -> Verum)] *)
    split; intro h.
    + (* [Sejunction_right] asks for the same two in the other order. *)
      exact (Sejunction_right (fun (f : Falsum) => f) I).
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Falsum -> Falsum _\/_ Falsum) /\ (Falsum _\/_ Falsum -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Either ctor of [h] carries a [Falsum]; the [~ Falsum] beside it is
         dropped. *)
      destruct h as [f _ | _ f]. exact f. exact f.
Qed.

Theorem assert_unjunction
  : forall (b : Bool), Assert (negate b) <-> ~ Assert b.
Proof.
  (* The context gains [b]: [|- Assert (negate b) <-> ~ Assert b] *)
  intros b.
  (* Both [<->] and [~] are definitions and have to come off before the
     structure underneath is visible. *)
  unfold Bijunction, Unjunction in |- *.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- (Falsum -> Verum -> Falsum) /\ ((Verum -> Falsum) -> Falsum)] *)
    split; intro h.
    + (* [h : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h] turns a [Verum] into a [Falsum], and [I] is a [Verum]. *)
      exact (h I).
  - (* [|- (Verum -> Falsum -> Falsum) /\ ((Falsum -> Falsum) -> Verum)] *)
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
  (* [|- (Assert b -> b = true) /\ (b = true -> Assert b)] *)
  unfold Bijunction in |- *.
  (* Two cases, one per ctor. *)
  destruct b as [|]; simpl in |- *.
  - (* [|- (Verum -> true = true) /\ (true = true -> Verum)] *)
    split; intro h.
    + (* Both sides are the same term. *)
      reflexivity.
    + (* [|- Verum] *)
      exact I.
  - (* [|- (Falsum -> false = true) /\ (false = true -> Falsum)] *)
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
