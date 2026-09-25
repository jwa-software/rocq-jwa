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
  simpl (~ _) in |- *.
  divide et impera.
  - intro h.
    divide et impera.
    + intro a.
      ipso (h (disjoin a, _)).
    + intro b.
      ipso (h (disjoin _, b)).
  - intro h.
    match h with | not_a not_b end.
    intro ab.
    match ab with | a | b end.
    + ipso (not_a a).
    + ipso (not_b b).
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
  simpl (~ _) in |- *.
  intro h.
  intro ab.
  match ab with | a b end.
  match h with | not_a | not_b end.
  - ipso (not_a a).
  - ipso (not_b b).
Qed.

(* De Morgan for [forsome], the disjunction over every [x]: no [x] satisfies
 * [P] exactly when each [x] fails it, in both directions.
 *)
(* de_morgan.existential *)
Theorem existential
  : forall (A : Type) (P : A -> Prop) . ~ (forsome (x : A) . P x) <-> forall (x : A) . ~ P x.
Proof.
  intros A P.
  simpl (~ _) in |- *.
  divide et impera.
  - intro h.
    intro x.
    intro p.
    ipso (h (Exists_introduction x p)).
  - intro h.
    intro e.
    match e with | x p end.
    ipso (h x p).
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
  simpl (~ _) in |- *.

  (* The context gains [not_a : A -> Falsum]: [|- B] *)
  intro not_a.

  match h with | a | b end.
  - let proof f := not_a a.
    ex f quodlibet.
  - ipso b.
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
  simpl (~ _) in |- *.

  intro not_b.

  match h with | a | b end.
  - ipso a.
  - let proof f := not_b b.
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
  simpl (~ _) in |- *.

  intro h.
  intro a.
  intro b.

  ipso (h (conjoin a, b)).
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
  simpl (~ _) in |- *.

  intro h.
  intro b.
  intro a.

  ipso (h (conjoin a, b)).
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
  simpl (~ _) in |- *.
  intro not_a.
  ipso (not_a a).
Qed.

End double. (* double *)

Module triple. (* triple *)

(* triple.reduction *)
Theorem reduction : forall {A : Prop} . ~ ~ ~ A -> ~ A.
Proof.
  intro A.
  simpl (~ _) in |- *.
  intro not_not_not_a.
  intro a.
  (* not_a                         : A -> Falsum          (= ~ A)
   * a                             : A
   * not_a a                       : Falsum               (body)
   * fun (not_a : ~ A) . not_a a   : (A -> Falsum) -> Falsum
   *                               = ~ (A -> Falsum)
   *                               = ~ (~ A)
   *                               = ~ ~ A
   *
   * [let proof] keeps the type alone, [not_not_a : ~ ~ A].
   * [let] works here too, but keeps the body as well, [not_not_a := fun (not_a : ~ A) . not_a a : ~ ~ A].
   *)
  let proof not_not_a : ~ ~ A := fun (not_a : ~ A) . not_a a.
  ipso (not_not_not_a not_not_a).
Qed.

End triple. (* triple *)

Theorem contraposition
  : forall {A : Prop} {B : Prop} . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B.

  (* [|- (A -> B) -> (B -> Falsum) -> (A -> Falsum)] *)
  simpl (~ _) in |- *.

  (* The context gains [ab : A -> B]: [|- (B -> Falsum) -> A -> Falsum] *)
  intro ab.
  (* The context gains [not_b : B -> Falsum]: [|- A -> Falsum] *)
  intro not_b.
  (* The context gains [a : A]: [|- Falsum] *)
  intro a.

  (* The context gains [b : B] *)
  let proof b := ab a.
  (* The context gains [facto : Falsum] *)
  let proof facto := not_b b.

  ipso facto.
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} . (A1 <-> A2) -> (~ A1 <-> ~ A2).
Proof.
  intros A1 A2.
  intro ea.

  (* [a12 : A1 -> A2]
   * [a21 : A2 -> A1].
   *)
  match ea with | a12 a21 end.

  (* [|- (A1 -> Falsum) <-> (A2 -> Falsum)] *)
  simpl (~ _) in |- *.

  (* [Biconditional] has one ctor with two fields,
   * so the goal splits into two goals:
   * [|- (A1 -> Falsum) -> (A2 -> Falsum)]
   * [|- (A2 -> Falsum) -> (A1 -> Falsum)].
   *)
  divide et impera.

  - intro not_a1.
    intro a2.

    (* The context gains [a1 : A1] *)
    let proof a1 := a21 a2.
    (* The context gains [facto : Falsum] *)
    let proof facto := not_a1 a1.

    ipso facto.

  - intro not_a2.
    intro a1.

    (* The context gains [a2 : A2] *)
    let proof a2 := a12 a1.
    (* The context gains [facto : Falsum] *)
    let proof facto := not_a2 a2.

    ipso facto.
Qed.

End Negation. (* Negation *)
