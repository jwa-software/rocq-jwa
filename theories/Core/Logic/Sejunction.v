(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Abjunction.
From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* Sejunction is exclusive disjunction: one side holds and the other does
 * not. [Theorem t : Verum _\/_ Verum.] is accepted and [Proof.] opens, but no
 * step reaches [Qed.]: either ctor demands [~ Verum], and no term has that
 * type. Being writable does not make a statement provable.
 *)
Inductive Sejunction (A : Prop) (B : Prop) : Prop :=
  | Sejunction_introduction_left  : A -> ~ B -> Sejunction A B
  | Sejunction_introduction_right : ~ A -> B -> Sejunction A B.

Arguments Sejunction_introduction_left  {A} {B} a  nb.
Arguments Sejunction_introduction_right {A} {B} na b.

Notation "A _\/_ B" := (Sejunction A B)
  : jwa_type_scope.

(* [sejoin a, nb] : [A _\/_ B] from [a : A] and [nb : ~ B], and [sejoin na, b]
 * from [na : ~ A] and [b : B]: the types of the two decide the side.
 *)
Notation "'sejoin' a , b"
    := (ltac2:(Control.once_plus
                 (fun () => Control.refine (fun () =>
                    constr:(Sejunction_introduction_left $preterm:a $preterm:b)))
                 (fun _ => Control.once_plus
                    (fun () => Control.refine (fun () =>
                       constr:(Sejunction_introduction_right $preterm:a $preterm:b)))
                    (fun _ => Control.zero (Tactic_failure (Some (Message.concat
                       (Message.of_string
                          "sejoin: give a proof of one side and a refutation of the other,")
                       (Message.of_string " as in sejoin a, nb or sejoin na, b"))))))))
  (only parsing).

(* A module may carry the type's name; its laws read
 * [Sejunction.commutativity].
 *)
Module Sejunction. (* Sejunction *)

(* The two ctors under the names a proof writes: [Sejunction.left a nb] and
 * [Sejunction.right na b]. An abbreviation is the ctor itself, so it also
 * serves as a pattern; Rocq prints the ctor's own name.
 *)
Abbreviation left  := Sejunction_introduction_left.
Abbreviation right := Sejunction_introduction_right.
Abbreviation L     := Sejunction_introduction_left  (only parsing).
Abbreviation R     := Sejunction_introduction_right (only parsing).

Theorem commutativity
  : forall {A : Prop} {B : Prop} . A _\/_ B -> B _\/_ A.
Proof.
  intros A B.
  intro h.
  (* [Sejunction] has two ctors with two fields each,
   * so [h] gives two same goals with different contexts:
   * - one with [a : A]    and [nb : ~ B],
   * - one with [na : ~ A] and [b : B].
   *)
  match h with | a nb | na b end.
  - ipso (Sejunction.right nb  a).
  - ipso (Sejunction.left   b na).
Qed.

Module decomposition. (* decomposition *)

Module into. (* decomposition.into *)

(* A sejunction is one of the two abjunctions: the left side without the
 * right, or the right side without the left.
 *)
(* decomposition.into.abjunction *)
Theorem abjunction
  : forall (A : Prop) (B : Prop) . A _\/_ B <-> (A -/> B) \/ (B -/> A).
Proof.
  intros A B.
  divide et impera.
  - intro h.
    match h with | a nb | na b end.
    + ipso (Disjunction.left (Abjunction_introduction a nb)).
    + ipso (Disjunction.right (Abjunction_introduction b na)).
  - intro h.
    match h with | ab | ba end.
    + match ab with | a nb end.
      ipso (Sejunction.left a nb).
    + match ba with | b na end.
      ipso (Sejunction.right na b).
Qed.

End into. (* decomposition.into *)

End decomposition. (* decomposition *)

(* The textbook definition of exclusive disjunction, as a theorem: one of
 * the two holds, and not both.
 *)
Theorem specification
  : forall (A : Prop) (B : Prop) . A _\/_ B <-> (A \/ B) /\ ~ (A /\ B).
Proof.
  intros A B.
  divide et impera.
  - intro h.
    match h with | a nb | na b end; divide et impera.
    + ipso (Disjunction.left a).
    + simpl (~ _) in nb |- *.
      intro ab.
      match ab with | _ b end.
      ipso (nb b).
    + ipso (Disjunction.right b).
    + simpl (~ _) in na |- *.
      intro ab.
      match ab with | a _ end.
      ipso (na a).
  - intro h.
    match h with | ab nab end.
    simpl (~ _) in nab.
    match ab with | a | b end.
    + let proof nb : ~ B := fun (b : B) . nab (conjoin a, b).
      ipso (Sejunction.left a nb).
    + let proof na : ~ A := fun (a : A) . nab (conjoin a, b).
      ipso (Sejunction.right na b).
Qed.

Theorem congruence
  : forall {A1 : Prop} {A2 : Prop} {B1 : Prop} {B2 : Prop} .
      (A1 <-> A2) -> (B1 <-> B2) -> (A1 _\/_ B1 <-> A2 _\/_ B2).
Proof.
  intros A1 A2 B1 B2.
  intro ea.
  intro eb.
  match ea with | a12 a21 end.
  match eb with | b12 b21 end.
  divide et impera; intro h.
  - match h with | a1 nb1 | na1 b1 end.
    + let proof nb2 : ~ B2 := fun (b2 : B2) . nb1 (b21 b2).
      ipso (Sejunction.left (a12 a1) nb2).
    + let proof na2 : ~ A2 := fun (a2 : A2) . na1 (a21 a2).
      ipso (Sejunction.right na2 (b12 b1)).
  - match h with | a2 nb2 | na2 b2 end.
    + let proof nb1 : ~ B1 := fun (b1 : B1) . nb2 (b12 b1).
      ipso (Sejunction.left (a21 a2) nb1).
    + let proof na1 : ~ A1 := fun (a1 : A1) . na2 (a12 a1).
      ipso (Sejunction.right na1 (b21 b2)).
Qed.

Module weakening. (* weakening *)

Module to. (* weakening.to *)

(* A sejunction is a disjunction that has forgotten which side fails. *)
(* weakening.to.disjunction *)
Theorem disjunction
  : forall {A : Prop} {B : Prop} . A _\/_ B -> A \/ B.
Proof.
  intros A B.
  intro h.
  match h with | a nb | na b end.
  - ipso (Disjunction.left  a).
  - ipso (Disjunction.right b).
Qed.

End to. (* weakening.to *)

End weakening. (* weakening *)

(* Two propositions are incompatible when they cannot both hold. A
 * sejunction is incompatible with the conjunction of its sides and with
 * their biconditional.
 *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* exclusion.of.conjunction *)
Theorem conjunction
  : forall {A : Prop} {B : Prop} . A _\/_ B -> ~ (A /\ B).
Proof.
  intros A B.
  intro h.
  simpl (~ _) in |- *.
  intro ab.
  match ab with | a b end.
  match h  with | _ nb | na _ end.
  - ipso (nb b).
  - ipso (na a).
Qed.

(* exclusion.of.biconditional *)
Theorem biconditional
  : forall {A : Prop} {B : Prop} . A _\/_ B -> ~ (A <-> B).
Proof.
  intros A B.
  intro h.
  simpl (~ _) in |- *.
  intro e.
  match e with | ab ba end.
  match h with | a nb | na b end.
  - simpl (~ _) in nb.
    let proof b := ab a.
    let proof facto := nb b.
    ipso facto.
  - simpl (~ _) in na.
    let proof a := ba b.
    let proof facto := na a.
    ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

End Sejunction. (* Sejunction *)

(* The same incompatibility read from the biconditional's side belongs to
 * [Biconditional], but it can be stated only here, where [_\/_] is known. A
 * second module of that name carries it, and a client reads
 * [Biconditional.exclusion.of.sejunction].
 *)
Module Biconditional. (* Biconditional *)

Module exclusion. (* exclusion *)

Module of. (* exclusion.of *)

(* exclusion.of.sejunction *)
Theorem sejunction
  : forall {A : Prop} {B : Prop} . (A <-> B) -> ~ (A _\/_ B).
Proof.
  intros A B.
  intro e.
  match e with | ab ba end.
  simpl (~ _) in |- *.
  intro h.
  match h with | a nb | na b end.
  - simpl (~ _) in nb.
    let proof b := ab a.
    let proof facto := nb b.
    ipso facto.
  - simpl (~ _) in na.
    let proof a := ba b.
    let proof facto := na a.
    ipso facto.
Qed.

End of. (* exclusion.of *)

End exclusion. (* exclusion *)

End Biconditional. (* Biconditional *)
