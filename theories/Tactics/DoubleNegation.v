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
