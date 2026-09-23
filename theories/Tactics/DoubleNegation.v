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
