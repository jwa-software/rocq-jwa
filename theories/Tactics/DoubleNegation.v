(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Import Notations.
From Ltac2 Require Constr Control List Message Std.

(* [Ltac2.Notations] is imported for [apply] and [lazy_match!] inside this
 * file; an [Import] does not travel, so a file importing this one still sees
 * none of Rocq's tactic syntax.
 *)

Ltac2 refuse (message : string) :=
  Control.zero (Tactic_failure (Some (Message.of_string message))).

(* Double negation introduction.
 *
 *   dni <H>    A |- ~ ~ A
 *
 * Bare, it is a term: [ipso (dni a)], [let proof h := dni a], or one nested
 * in another. Only [dni <H> as <p>], or equally [dni <H> |- <p>], is a
 * tactic. Nothing anywhere may be named [dni].
 *)

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'dni' H" := (Negation.double.introduction H)
  (only parsing).

Ltac2 Notation "dni" h(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    Local.check_preterm "dni" h;
    Std.specialize
      (open_constr:(Negation.double.introduction $preterm:h), Std.NoBindings) (Some p)).

Ltac2 Notation "dni" h(preterm) "|-" p(intropattern) :=
  Control.enter (fun () =>
    Local.check_preterm "dni" h;
    Std.specialize
      (open_constr:(Negation.double.introduction $preterm:h), Std.NoBindings) (Some p)).

(* In place, adding nothing; <hypotheses> is a comma-separated list of names,
 * one or more:
 *
 *   dni in <hypotheses>           each A becomes ~ ~ A
 *   dni in |- *                   the goal ~ ~ A becomes A
 *   dni in <hypotheses> |- *      both
 *
 * On the goal the rule runs backward, from the new goal to the old, so the
 * goal loses its two negations and grows stronger: [~ ~ (A \/ ~ A)] is
 * provable, [A \/ ~ A] is not.
 *)
Ltac2 dni_in_hypothesis (h : ident) :=
  apply Negation.double.introduction in $h.

Ltac2 dni_in_goal () :=
  lazy_match! goal with
  | [ |- ~ ~ _ ] => apply Negation.double.introduction
  | [ |- _ ] => refuse "dni: expects a goal of the shape ~ ~ A"
  end.

Ltac2 Notation "dni" "in" hypotheses(list1(context_name, ",")) :=
  Control.enter (fun () =>
    List.iter dni_in_hypothesis (Local.context_idents "dni" hypotheses)).

Ltac2 Notation "dni" "in" "|-" "*" :=
  Control.enter dni_in_goal.

Ltac2 Notation "dni" "in" hypotheses(list1(context_name, ",")) "|-" "*" :=
  Control.enter (fun () =>
    List.iter dni_in_hypothesis (Local.context_idents "dni" hypotheses); dni_in_goal ()).

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

Ltac2 Notation "dne" h(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    Local.check_preterm "dne" h;
    Std.specialize
      (open_constr:(Negation.triple.reduction $preterm:h), Std.NoBindings) (Some p)).

Ltac2 Notation "dne" h(preterm) "|-" p(intropattern) :=
  Control.enter (fun () =>
    Local.check_preterm "dne" h;
    Std.specialize
      (open_constr:(Negation.triple.reduction $preterm:h), Std.NoBindings) (Some p)).

(* In place, adding nothing:
 *
 *   dne in <hypotheses>           each ~ ~ ~ A becomes ~ A
 *   dne in |- *                   the goal ~ A becomes ~ ~ ~ A
 *   dne in <hypotheses> |- *      both
 *
 * The two are equivalent, so on the goal nothing is lost. The shape is read
 * first, so that a refusal says why.
 *)
Ltac2 dne_in_hypothesis (h : ident) :=
  lazy_match! Constr.type (Control.hyp h) with
  | ~ ~ ~ _ => apply Negation.triple.reduction in $h
  | _ => refuse "dne: expects ~ ~ ~ A, since ~ ~ A |- A in general is not constructive"
  end.

Ltac2 dne_in_goal () :=
  lazy_match! goal with
  | [ |- ~ _ ] => apply Negation.triple.reduction
  | [ |- _ ] => refuse "dne: expects a goal of the shape ~ A"
  end.

Ltac2 Notation "dne" "in" hypotheses(list1(context_name, ",")) :=
  Control.enter (fun () =>
    List.iter dne_in_hypothesis (Local.context_idents "dne" hypotheses)).

Ltac2 Notation "dne" "in" "|-" "*" :=
  Control.enter dne_in_goal.

Ltac2 Notation "dne" "in" hypotheses(list1(context_name, ",")) "|-" "*" :=
  Control.enter (fun () =>
    List.iter dne_in_hypothesis (Local.context_idents "dne" hypotheses); dne_in_goal ()).
