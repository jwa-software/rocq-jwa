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
  : forall (m : Nat) (n : Nat) . Nat.compare m n = Lt -> Nat.LessThan m n.
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
