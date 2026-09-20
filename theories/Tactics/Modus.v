(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Logic.Sejunction.
From jwa Require Import Core.Ltac.

(* The four modi of traditional logic, each naming the step it takes. Every
 * form also comes with [as <p>], which puts the conclusion into the context
 * under the intro pattern <p> instead of closing the goal.
 *
 *   modus ponens          <H1>, <H2>    A -> B, A |- B
 *
 *   modus tollens         <H1>, <H2>    A -> B, ~ B |- ~ A
 *
 *   modus tollendo ponens <H1>, <H2>    A \/ B, ~ A |- B
 *
 *   modus ponendo tollens <H1>, <H2>    ~ (A /\ B), A |- ~ B
 *
 * The two premises are separated by a comma and may be given in either order:
 * each body tries the other way round when the first does not apply. In the
 * bare form the goal decides; under [as] there is no goal to decide, so if
 * both orders happen to type check the first one stands.
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

Tactic Notation "modus" "ponens" uconstr(H1) "," uconstr(H2) :=
  first [ exact (H1 H2) | exact (H2 H1) ].

Tactic Notation "modus" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (H1 H2) as p | pose proof (H2 H1) as p ].

Tactic Notation "modus" "ponendo" "ponens" uconstr(H1) "," uconstr(H2) :=
  first [ exact (H1 H2) | exact (H2 H1) ].

Tactic Notation "modus" "ponendo" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (H1 H2) as p | pose proof (H2 H1) as p ].

Tactic Notation "modus" "tollens" uconstr(H1) "," uconstr(H2) :=
  first [ exact (Negation.contraposition H1 H2)
        | exact (Negation.contraposition H2 H1) ].

Tactic Notation "modus" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (Negation.contraposition H1 H2) as p
        | pose proof (Negation.contraposition H2 H1) as p ].

Tactic Notation "modus" "tollendo" "tollens" uconstr(H1) "," uconstr(H2) :=
  first [ exact (Negation.contraposition H1 H2)
        | exact (Negation.contraposition H2 H1) ].

Tactic Notation "modus" "tollendo" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (Negation.contraposition H1 H2) as p
        | pose proof (Negation.contraposition H2 H1) as p ].

Tactic Notation "modus" "tollendo" "ponens" uconstr(H1) "," uconstr(H2) :=
  first [ exact (Negation.elimination.of.disjunction H1 H2)
        | exact (Negation.elimination.of.disjunction H2 H1) ].

Tactic Notation "modus" "tollendo" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (Negation.elimination.of.disjunction H1 H2) as p
        | pose proof (Negation.elimination.of.disjunction H2 H1) as p ].

Tactic Notation "modus" "ponendo" "tollens" uconstr(H1) "," uconstr(H2) :=
  first
    [ exact (Negation.exclusion.of.conjunction H1 H2)
    | exact (Negation.exclusion.of.conjunction H2 H1)
    | exact (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction H1) H2)
    | exact (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction H2) H1) ].

Tactic Notation "modus" "ponendo" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first
    [ pose proof (Negation.exclusion.of.conjunction H1 H2) as p
    | pose proof (Negation.exclusion.of.conjunction H2 H1) as p
    | pose proof
        (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction H1) H2) as p
    | pose proof
        (Negation.exclusion.of.conjunction (Sejunction.exclusion.of.conjunction H2) H1) as p ].
