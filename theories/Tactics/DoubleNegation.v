(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Double negation introduction.
 *
 *   dni <H>    A |- ~ ~ A
 *
 * Bare, it is a term: [ipso (dni a)], [pose proof (dni a) as h], or one
 * nested in another. Only [dni <H> as <p>], or equally [dni <H> |- <p>], is a
 * tactic. Nothing anywhere may be named [dni].
 *)

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'dni' H" := (Negation.double.introduction H)
  (only parsing).

Tactic Notation "dni" uconstr(H) "as" simple_intropattern(p) :=
  pose proof (Negation.double.introduction H) as p.

Tactic Notation "dni" uconstr(H) "|-" simple_intropattern(p) :=
  pose proof (Negation.double.introduction H) as p.

(* In place, adding nothing:
 *
 *   dni in <H>            <H> : A becomes ~ ~ A
 *   dni in |- *           the goal ~ ~ A becomes A
 *   dni in <H> |- *       both
 *
 * On the goal the rule runs backward, from the new goal to the old, so the
 * goal loses its two negations and grows stronger: [~ ~ (A \/ ~ A)] is
 * provable, [A \/ ~ A] is not.
 *)
Ltac dni_in_goal :=
  lazymatch goal with
  | |- ~ ~ _ => apply Negation.double.introduction
  | |- _ => fail "dni: expects a goal of the shape ~ ~ A"
  end.

Tactic Notation "dni" "in" hyp(H) :=
  apply Negation.double.introduction in H.

Tactic Notation "dni" "in" "|-" "*" :=
  dni_in_goal.

Tactic Notation "dni" "in" hyp(H) "|-" "*" :=
  apply Negation.double.introduction in H;
  dni_in_goal.

(* Double negation elimination, only where it holds constructively.
 *
 *   dne <H>    ~ ~ ~ A |- ~ A
 *
 * [~ ~ A |- A] in general is classical: [~ ~ A] says only that [A] cannot
 * fail, and gives no proof of [A] to return. The library adds no axiom, so
 * [dne] removes two negations only when a third remains beneath them, [~ A]
 * being a function into [Falsum] that [~ ~ ~ A] suffices to build. On any
 * other shape it is a type error.
 *
 * Shaped like [dni]: a term when bare, a tactic with [as <p>] or [|- <p>].
 * Nothing anywhere may be named [dne].
 *)
Notation "'dne' H" := (Negation.triple.reduction H)
  (only parsing).

Tactic Notation "dne" uconstr(H) "as" simple_intropattern(p) :=
  pose proof (Negation.triple.reduction H) as p.

Tactic Notation "dne" uconstr(H) "|-" simple_intropattern(p) :=
  pose proof (Negation.triple.reduction H) as p.

(* In place, adding nothing:
 *
 *   dne in <H>            <H> : ~ ~ ~ A becomes ~ A
 *   dne in |- *           the goal ~ A becomes ~ ~ ~ A
 *   dne in <H> |- *       both
 *
 * The two are equivalent, so on the goal nothing is lost. The shape is read
 * first, so that a refusal says why.
 *)
Ltac dne_in_hypothesis H :=
  lazymatch type of H with
  | ~ ~ ~ _ => apply Negation.triple.reduction in H
  | _ =>
      fail "dne: expects ~ ~ ~ A, since ~ ~ A |- A in general is not constructive"
  end.

Ltac dne_in_goal :=
  lazymatch goal with
  | |- ~ _ => apply Negation.triple.reduction
  | |- _ => fail "dne: expects a goal of the shape ~ A"
  end.

Tactic Notation "dne" "in" hyp(H) :=
  dne_in_hypothesis H.

Tactic Notation "dne" "in" "|-" "*" :=
  dne_in_goal.

Tactic Notation "dne" "in" hyp(H) "|-" "*" :=
  dne_in_hypothesis H;
  dne_in_goal.
