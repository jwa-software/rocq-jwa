(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Abjunction is material nonimplication: [A] holds and [B] does not, the
 * one case in which [A -> B] fails.
 *)
Inductive Abjunction (A : Prop) (B : Prop) : Prop :=
  | Abjunction_introduction : A -> ~ B -> Abjunction A B.

Arguments Abjunction_introduction {A} {B} a nb.

Notation "A -/> B" := (Abjunction A B)
  : jwa_type_scope.

(* [abjoin a, nb] : [A -/> B], from [a : A] and [nb : ~ B]. *)
Notation "'abjoin' a , nb" := (Abjunction_introduction a nb) (only parsing).

(* A module may carry the type's name; its laws read
 * [Abjunction.congruence].
 *)
Module Abjunction. (* Abjunction *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* Two propositions are incompatible when they cannot both hold: an
 * abjunction and the conditional between the same two sides.
 *)
(* exclusion.of.conditional *)
Theorem conditional
  : forall {A : Prop} {B : Prop} . A -/> B -> ~ (A -> B).
Proof.
  intros A B.
  intro h.
  match h with | a nb end.
  simpl (~ _) in nb |- *.
  intro ab.
  let proof b := ab a.
  let proof facto := nb b.
  ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

Module negation. (* negation *)

(* negation.specification *)
Theorem specification
  : forall (A : Prop) (B : Prop) . ~ (A -/> B) <-> (A -> ~ ~ B).
Proof.
  intros A B.
  divide et impera.
  - intro h.
    simpl (~ _) in h |- *.
    intro a.
    intro nb.
    ipso (h (Abjunction_introduction a nb)).
  - simpl (~ _) in |- *.
    intro f.
    intro h.
    match h with | a nb end.
    ipso (f a nb).
Qed.

End negation. (* negation *)

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 -/> B1 <-> A2 -/> B2).
Proof.
  intros A1 A2 B1 B2.
  intro ea.
  intro eb.
  match ea with | a12 a21 end.
  match eb with | b12 b21 end.
  divide et impera; intro h.
  - match h with | a1 nb1 end.
    divide et impera.
    + ipso (a12 a1).
    + simpl (~ _) in nb1 |- *.
      intro b2.
      let proof b1 := b21 b2.
      let proof facto := nb1 b1.
      ipso facto.
  - match h with | a2 nb2 end.
    divide et impera.
    + ipso (a21 a2).
    + simpl (~ _) in nb2 |- *.
      intro b1.
      let proof b2 := b12 b1.
      let proof facto := nb2 b2.
      ipso facto.
Qed.

End Abjunction. (* Abjunction *)

(* The same incompatibility read from the conditional's side belongs to
 * [Conditional], but it can be stated only here, where [-/>] is known. A
 * second module of that name carries it, and a client reads
 * [Conditional.exclusion.of.abjunction].
 *)
Module Conditional. (* Conditional *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* exclusion.of.abjunction *)
Theorem abjunction
  : forall {A : Prop} {B : Prop} . (A -> B) -> ~ (A -/> B).
Proof.
  intros A B.
  intro ab.
  simpl (~ _) in |- *.
  intro h.
  match h with | a nb end.
  simpl (~ _) in nb.
  let proof b := ab a.
  let proof facto := nb b.
  ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

End Conditional. (* Conditional *)
