(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Logic.Sejunction.
From jwa Require Import Core.Ltac.

(* The four modi of traditional logic, each naming the step it takes. Every
 * form also comes with [as <p>], which puts the conclusion into the context
 * under the intro pattern <p> instead of closing the goal.
 *
 *   modus ponens          <Hab> <Ha>     A -> B, A |- B
 *
 *   modus tollens         <Hab> <Hnb>    A -> B, ~ B |- ~ A
 *
 *   modus tollendo ponens <Hor> <Hna>    A \/ B, ~ A |- B
 *
 *   modus ponendo tollens <Hn>  <Ha>     ~ (A /\ B), A |- ~ B
 *
 * The first two answer to their full names as well, [modus ponendo ponens]
 * and [modus tollendo tollens].
 *
 * [modus ponendo tollens] accepts either spelling of incompatibility: the
 * negated conjunction, or the sejunction [A _\/_ B], which says that and also
 * that one of the two holds. The sejunction is carried into the law by
 * [Sejunction.exclusion.of.conjunction] once the first form fails to apply.
 *
 * The proofs are [uconstr]: a [constr] is elaborated alone, where a lemma's
 * implicit binders have nothing yet to fix them.
 *)

Tactic Notation "modus" "ponens" uconstr(Hab) uconstr(Ha) :=
  exact (Hab Ha).

Tactic Notation "modus" "ponens" uconstr(Hab) uconstr(Ha) "as" simple_intropattern(p) :=
  pose proof (Hab Ha) as p.

Tactic Notation "modus" "ponendo" "ponens" uconstr(Hab) uconstr(Ha) :=
  exact (Hab Ha).

Tactic Notation "modus" "ponendo" "ponens" uconstr(Hab) uconstr(Ha)
    "as" simple_intropattern(p) :=
  pose proof (Hab Ha) as p.

Tactic Notation "modus" "tollens" uconstr(Hab) uconstr(Hnb) :=
  exact (Negation.contraposition Hab Hnb).

Tactic Notation "modus" "tollens" uconstr(Hab) uconstr(Hnb) "as" simple_intropattern(p) :=
  pose proof (Negation.contraposition Hab Hnb) as p.

Tactic Notation "modus" "tollendo" "tollens" uconstr(Hab) uconstr(Hnb) :=
  exact (Negation.contraposition Hab Hnb).

Tactic Notation "modus" "tollendo" "tollens" uconstr(Hab) uconstr(Hnb)
    "as" simple_intropattern(p) :=
  pose proof (Negation.contraposition Hab Hnb) as p.

Tactic Notation "modus" "tollendo" "ponens" uconstr(Hor) uconstr(Hna) :=
  exact (Negation.elimination.of.disjunction Hor Hna).

Tactic Notation "modus" "tollendo" "ponens" uconstr(Hor) uconstr(Hna)
    "as" simple_intropattern(p) :=
  pose proof (Negation.elimination.of.disjunction Hor Hna) as p.

Tactic Notation "modus" "ponendo" "tollens" uconstr(Hn) uconstr(Ha) :=
  first
    [ exact (Negation.exclusion.of.conjunction Hn Ha)
    | exact (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction Hn) Ha) ].

Tactic Notation "modus" "ponendo" "tollens" uconstr(Hn) uconstr(Ha)
    "as" simple_intropattern(p) :=
  first
    [ pose proof (Negation.exclusion.of.conjunction Hn Ha) as p
    | pose proof
        (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction Hn) Ha)
        as p ].
