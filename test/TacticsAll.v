(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.All.
From jwa Require Import Tactics.All.

Theorem tactics_all_delivers_modus_ponens
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponens hab, ha.
Qed.

Theorem tactics_all_delivers_modus_ponens_reversed
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponens ha, hab.
Qed.

Theorem tactics_all_delivers_modus_ponens_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B /\ C) -> A -> B.
Proof.
  intros A B C hab ha.
  modus ponens hab, ha as [b c].
  exact b.
Qed.

Theorem tactics_all_delivers_modus_ponendo_ponens
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponendo ponens hab, ha.
Qed.

Theorem tactics_all_delivers_modus_ponendo_ponens_as
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponendo ponens hab, ha as h.
  exact h.
Qed.

Theorem tactics_all_delivers_modus_ponens_implicit
  : forall (m : Nat) (n : Nat) . Nat.compare m n = Comparison.Lt -> Nat.LessThan m n.
Proof.
  intros m n c.
  modus ponens Nat.comparison.strict.forward.specification, c.
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_short
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  HS hab, hbc.
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_short_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  HS hab, hbc as hac.
  exact hac.
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  hypothetical syllogism hab, hbc.
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  hypothetical syllogism hab, hbc as hac.
  exact hac.
Qed.

Theorem tactics_all_delivers_simplify_definition
  : forall (A : Prop) . ~ A -> ~ A -> A -> Falsum.
Proof.
  intros A na1 na2 a.
  simplify Negation in na1, na2.
  exact (na1 a).
Qed.

Theorem tactics_all_delivers_simplify_definition_and_goal
  : forall (A : Prop) . ~ A -> A -> Falsum.
Proof.
  intros A na a.
  simplify Negation in na |- *.
  exact (na a).
Qed.

Theorem tactics_all_delivers_simplify_goal
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  simplify Negation in |- *.
  intro na.
  exact (na a).
Qed.

Theorem tactics_all_delivers_simplify_four_definitions
  : forall (m : NatWithZero) . NatWithZero.Even m -> NatWithZero.Even m.
Proof.
  intros m e.
  simplify NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan in e.
  exact e.
Qed.

Theorem tactics_all_delivers_simplify_ten_definitions
  : forall (m : NatWithZero) . NatWithZero.Even m -> NatWithZero.Even m.
Proof.
  intros m e.
  simplify NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan, NatWithZero.LessOrEqual, NatWithZero.add,
      NatWithZero.mul, NatWithZero.sub, NatWithZero.le, NatWithZero.min in e.
  exact e.
Qed.

Theorem tactics_all_delivers_simplify_everywhere
  : forall (A : Prop) . ~ A -> A -> Falsum.
Proof.
  intros A na a.
  simplify Negation in *.
  exact (na a).
Qed.

Theorem tactics_all_delivers_simplify_reduction_everywhere
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.add Nat.One m = n.
Proof.
  intros m n e.
  simplify in *.
  exact e.
Qed.

Theorem tactics_all_delivers_simplify_reduction
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.add Nat.One m = n.
Proof.
  intros m n e.
  simplify in e |- *.
  exact e.
Qed.

Theorem tactics_all_delivers_simplify_reduction_goal
  : forall (m : Nat) . Nat.add Nat.One m = Nat.add Nat.One m.
Proof.
  intro m.
  simplify in |- *.
  reflexivity.
Qed.

Theorem tactics_all_delivers_barbara
  : forall (A : Type) (S : A -> Prop) (M : A -> Prop) (P : A -> Prop) .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . S x -> P x).
Proof.
  intros A S M P mp sm.
  barbara mp, sm.
Qed.

Theorem tactics_all_delivers_barbara_as
  : forall (A : Type) (S : A -> Prop) (M : A -> Prop) (P : A -> Prop) .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . S x -> P x).
Proof.
  intros A S M P mp sm.
  barbara mp, sm as sp.
  exact sp.
Qed.

Theorem tactics_all_delivers_modus_tollens
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollens hab, hnb.
Qed.

Theorem tactics_all_delivers_modus_tollendo_tollens
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollendo tollens hab, hnb as na.
  exact na.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ A -> B.
Proof.
  intros A B hor hna.
  modus tollendo ponens hor, hna.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_as
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ A -> B.
Proof.
  intros A B hor hna.
  modus tollendo ponens hor, hna as b.
  exact b.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_right
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ B -> A.
Proof.
  intros A B hor hnb.
  modus tollendo ponens hor, hnb.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> A -> ~ B.
Proof.
  intros A B hn ha.
  modus ponendo tollens hn, ha.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_right
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> B -> ~ A.
Proof.
  intros A B hn hb.
  modus ponendo tollens hn, hb.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_sejunction_right
  : forall (A : Prop) (B : Prop) . A _\/_ B -> B -> ~ A.
Proof.
  intros A B hs hb.
  modus ponendo tollens hs, hb as na.
  exact na.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_sejunction
  : forall (A : Prop) (B : Prop) . A _\/_ B -> A -> ~ B.
Proof.
  intros A B hs ha.
  modus ponendo tollens hs, ha as nb.
  exact nb.
Qed.

Theorem tactics_all_delivers_modus_aequans
  : forall (A : Prop) (B : Prop) . (A <-> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus aequans hab, ha.
Qed.

Theorem tactics_all_delivers_modus_aequans_backward
  : forall (A : Prop) (B : Prop) . (A <-> B) -> B -> A.
Proof.
  intros A B hab hb.
  modus aequans hab, hb.
Qed.

Theorem tactics_all_delivers_modus_aequans_reversed
  : forall (A : Prop) (B : Prop) . (A <-> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus aequans ha, hab.
Qed.

Theorem tactics_all_delivers_modus_aequans_as
  : forall (A : Prop) (B : Prop) . (A <-> B) -> B -> A.
Proof.
  intros A B hab hb.
  modus aequans hab, hb as a.
  exact a.
Qed.
