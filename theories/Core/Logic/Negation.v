(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Exists.
From jwa Require Import Core.Logic.Falsum.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Negation: a proof of [A] leads to [Falsum]. *)
(* [Prop -> Prop] *)
Definition Negation := fun (A : Prop) . A -> Falsum.

Notation "~ A" := (Negation A)
  : jwa_type_scope.

(* A module may carry the definition's name; its laws read
 * [Negation.contraposition].
 *)
Module Negation. (* Negation *)

Module de_morgan. (* de_morgan *)

(* De Morgan: the negation of a disjunction is the conjunction of the
 * negations, in both directions.
 *)
(* de_morgan.disjunction *)
Theorem disjunction
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) <-> ~ A /\ ~ B.
Proof.
  intros A B.
  unfold Negation in |- *.
  split.
  - intro h.
    split.
    + intro a.
      apply h.
      exact (Disjunction.left a).
    + intro b.
      apply h.
      exact (Disjunction.right b).
  - intro h.
    destruct h as [not_a not_b].
    intro ab.
    destruct ab as [a | b].
    + exact (not_a a).
    + exact (not_b b).
Qed.

(* De Morgan for a conjunction holds in this direction only: from
 * [~ (A /\ B)] alone there is no telling which of [A] and [B] fails, so the
 * converse is not constructive.
 *)
(* de_morgan.conjunction *)
Theorem conjunction
  : forall {A : Prop} {B : Prop} . ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  intros A B.
  unfold Negation in |- *.
  intro h.
  intro ab.
  destruct ab as [a b].
  destruct h as [not_a | not_b].
  - exact (not_a a).
  - exact (not_b b).
Qed.

(* De Morgan for [exists], the disjunction over every [x]: no [x] satisfies
 * [P] exactly when each [x] fails it, in both directions.
 *)
(* de_morgan.existential *)
Theorem existential
  : forall (A : Type) (P : A -> Prop) . ~ (exists (x : A) . P x) <-> forall (x : A) . ~ P x.
Proof.
  intros A P.
  unfold Negation in |- *.
  split.
  - intro h.
    intro x.
    intro p.
    apply h.
    exact (Exists_introduction x p).
  - intro h.
    intro e.
    destruct e as [x p].
    exact (h x p).
Qed.

End de_morgan. (* de_morgan *)

(* [left] and [right] say which side of the connective the second premise
 * speaks of, the first premise being the whole connective either way.
 *)
Module elimination. (* elimination *)

Module left. (* elimination.left *)

Module of. (* elimination.left.of *)

(* elimination.left.of.disjunction *)
Theorem disjunction
  : forall {A : Prop} {B : Prop} . A \/ B -> ~ A -> B.
Proof.
  intro A.
  intro B.
  intro h.

  (* [|- (A -> Falsum) -> B] *)
  unfold Negation in |- *.

  (* The context gains [not_a : A -> Falsum]: [|- B] *)
  intro not_a.

  destruct h as [a | b].
  - pose proof (not_a a) as f.
    ex f quodlibet.
  - exact b.
Qed.

End of. (* elimination.left.of *)

End left. (* elimination.left *)

Module right. (* elimination.right *)

Module of. (* elimination.right.of *)

(* elimination.right.of.disjunction *)
Theorem disjunction
  : forall {A : Prop} {B : Prop} . A \/ B -> ~ B -> A.
Proof.
  intro A.
  intro B.
  intro h.

  (* [|- (B -> Falsum) -> A] *)
  unfold Negation in |- *.

  intro not_b.

  destruct h as [a | b].
  - exact a.
  - pose proof (not_b b) as f.
    ex f quodlibet.
Qed.

End of. (* elimination.right.of *)

End right. (* elimination.right *)

End elimination. (* elimination *)

Module exclusion. (* exclusion *)

Module left. (* exclusion.left *)

Module of. (* exclusion.left.of *)

(* exclusion.left.of.conjunction *)
Theorem conjunction
  : forall {A : Prop} {B : Prop} . ~ (A /\ B) -> A -> ~ B.
Proof.
  intro A.
  intro B.

  (* [|- (A /\ B -> Falsum) -> A -> B -> Falsum] *)
  unfold Negation in |- *.

  intro h.
  intro a.
  intro b.

  (* [|- A /\ B] *)
  apply h.

  exact (Conjunction_introduction a b).
Qed.

End of. (* exclusion.left.of *)

End left. (* exclusion.left *)

Module right. (* exclusion.right *)

Module of. (* exclusion.right.of *)

(* exclusion.right.of.conjunction *)
Theorem conjunction
  : forall {A : Prop} {B : Prop} . ~ (A /\ B) -> B -> ~ A.
Proof.
  intro A.
  intro B.

  (* [|- (A /\ B -> Falsum) -> B -> A -> Falsum] *)
  unfold Negation in |- *.

  intro h.
  intro b.
  intro a.

  (* [|- A /\ B] *)
  apply h.

  exact (Conjunction_introduction a b).
Qed.

End of. (* exclusion.right.of *)

End right. (* exclusion.right *)

End exclusion. (* exclusion *)

Module double. (* double *)

(* double.introduction *)
Theorem introduction : forall {A : Prop} . A -> ~ ~ A.
Proof.
  intro A.
  intro a.
  unfold Negation in |- *.
  intro not_a.
  exact (not_a a).
Qed.

End double. (* double *)

Module triple. (* triple *)

(* triple.reduction *)
Theorem reduction : forall {A : Prop} . ~ ~ ~ A -> ~ A.
Proof.
  intro A.
  unfold Negation in |- *.
  intro not_not_not_a.
  intro a.
  apply not_not_not_a.
  intro not_a.
  exact (not_a a).
Qed.

End triple. (* triple *)

Theorem contraposition
  : forall {A : Prop} {B : Prop} . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B.

  (* [|- (A -> B) -> (B -> Falsum) -> (A -> Falsum)] *)
  unfold Negation in |- *.

  (* The context gains [ab : A -> B]: [|- (B -> Falsum) -> A -> Falsum] *)
  intro ab.
  (* The context gains [not_b : B -> Falsum]: [|- A -> Falsum] *)
  intro not_b.
  (* The context gains [a : A]: [|- Falsum] *)
  intro a.

  (* [|- B] *)
  apply not_b.
  (* [|- A] *)
  apply ab.

  exact a.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} . (A1 <-> A2) -> (~ A1 <-> ~ A2).
Proof.
  intros A1 A2.
  intro ea.

  (* [a12 : A1 -> A2]
   * [a21 : A2 -> A1].
   *)
  destruct ea as [a12 a21].

  (* [|- (A1 -> Falsum) <-> (A2 -> Falsum)] *)
  unfold Negation in |- *.

  (* [Biconditional] has one ctor with two fields,
   * so the goal splits into two goals:
   * [|- (A1 -> Falsum) -> (A2 -> Falsum)]
   * [|- (A2 -> Falsum) -> (A1 -> Falsum)].
   *)
  split.

  - intro not_a1.
    intro a2.

    (* [|- A1] *)
    apply not_a1.
    (* [|- A2] *)
    apply a21.

    exact a2.

  - intro not_a2.
    intro a1.

    (* [|- A2] *)
    apply not_a2.
    (* [|- A1] *)
    apply a12.

    exact a1.
Qed.

End Negation. (* Negation *)
