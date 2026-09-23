(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Logic.Sejunction.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* The four modi of traditional logic and a fifth in their pattern.
 *
 *   modus ponens          <H1>, <H2>    A -> B, A |- B
 *   modus tollens         <H1>, <H2>    A -> B, ~ B |- ~ A
 *   modus tollendo ponens <H1>, <H2>    A \/ B, ~ A |- B
 *                                       A \/ B, ~ B |- A
 *   modus ponendo tollens <H1>, <H2>    ~ (A /\ B), A |- ~ B
 *                                       ~ (A /\ B), B |- ~ A
 *   modus aequans         <H1>, <H2>    A <-> B, A |- B
 *                                       A <-> B, B |- A
 *
 * Bare, each is a term: [exact (modus ponens hab, ha)], [pose proof (modus
 * aequans e, a) as h], or one nested in another. Only [... as <p>] is a
 * tactic, and [... |- <p>] spells the same tactic the way the table above
 * reads. Every one takes its premises in the order written, the connective
 * first and the term second. The last three read either side of their
 * connective, and [modus ponendo tollens] takes a sejunction [A _\/_ B] as
 * well as a negated conjunction; the first two also answer to [modus ponendo
 * ponens] and [modus tollendo tollens].
 *
 * Nothing anywhere may be named [modus], [ponens], [tollens], [ponendo],
 * [tollendo] or [aequans]. In the last three, whose bodies must try their
 * branches, a premise that is a bare lemma name whose implicits only the
 * other premise would fix does not elaborate: give them with [@], name the
 * lemma first, or use the [as] form.
 *)

(* The levels are reserved in [Core.Notations]; only the meanings belong
 * here. [ltac:] is what lets a term carry a [first]: it opens a goal, runs
 * the tactic, and the proof is the term.
 *)
Notation "'modus' 'ponens' H1 , H2" := (H1 H2)
  (only parsing).

Tactic Notation "modus" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  pose proof (H1 H2) as p.

Tactic Notation "modus" "ponens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  pose proof (H1 H2) as p.

Notation "'modus' 'ponendo' 'ponens' H1 , H2" := (H1 H2)
  (only parsing).

Tactic Notation "modus" "ponendo" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  pose proof (H1 H2) as p.

Tactic Notation "modus" "ponendo" "ponens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  pose proof (H1 H2) as p.

Notation "'modus' 'tollens' H1 , H2" := (Negation.contraposition H1 H2)
  (only parsing).

Tactic Notation "modus" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  pose proof (Negation.contraposition H1 H2) as p.

Tactic Notation "modus" "tollens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  pose proof (Negation.contraposition H1 H2) as p.

Notation "'modus' 'tollendo' 'tollens' H1 , H2"
    := (Negation.contraposition H1 H2)
  (only parsing).

Tactic Notation "modus" "tollendo" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  pose proof (Negation.contraposition H1 H2) as p.

Tactic Notation "modus" "tollendo" "tollens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  pose proof (Negation.contraposition H1 H2) as p.

Notation "'modus' 'tollendo' 'ponens' H1 , H2"
    := (ltac:(first [ exact (Negation.elimination.left.of.disjunction H1 H2)
                    | exact (Negation.elimination.right.of.disjunction H1 H2)
                    ]))
  (only parsing).

Tactic Notation "modus" "tollendo" "ponens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (Negation.elimination.left.of.disjunction H1 H2) as p
        | pose proof (Negation.elimination.right.of.disjunction H1 H2) as p ].

Tactic Notation "modus" "tollendo" "ponens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  first [ pose proof (Negation.elimination.left.of.disjunction H1 H2) as p
        | pose proof (Negation.elimination.right.of.disjunction H1 H2) as p ].

Notation "'modus' 'ponendo' 'tollens' H1 , H2"
    := (ltac:(first
                [ exact (Negation.exclusion.left.of.conjunction H1 H2)
                | exact (Negation.exclusion.right.of.conjunction H1 H2)
                | exact (Negation.exclusion.left.of.conjunction
                           (Sejunction.exclusion.of.conjunction H1) H2)
                | exact (Negation.exclusion.right.of.conjunction
                           (Sejunction.exclusion.of.conjunction H1) H2) ]))
  (only parsing).

Tactic Notation "modus" "ponendo" "tollens" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first
    [ pose proof (Negation.exclusion.left.of.conjunction H1 H2) as p
    | pose proof (Negation.exclusion.right.of.conjunction H1 H2) as p
    | pose proof (Negation.exclusion.left.of.conjunction
                    (Sejunction.exclusion.of.conjunction H1) H2) as p
    | pose proof (Negation.exclusion.right.of.conjunction
                    (Sejunction.exclusion.of.conjunction H1) H2) as p ].

Tactic Notation "modus" "ponendo" "tollens" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  first
    [ pose proof (Negation.exclusion.left.of.conjunction H1 H2) as p
    | pose proof (Negation.exclusion.right.of.conjunction H1 H2) as p
    | pose proof (Negation.exclusion.left.of.conjunction
                    (Sejunction.exclusion.of.conjunction H1) H2) as p
    | pose proof (Negation.exclusion.right.of.conjunction
                    (Sejunction.exclusion.of.conjunction H1) H2) as p ].

Notation "'modus' 'aequans' H1 , H2"
    := (ltac:(first [ exact (Biconditional.forward.elimination H1 H2)
                    | exact (Biconditional.backward.elimination H1 H2) ]))
  (only parsing).

Tactic Notation "modus" "aequans" uconstr(H1) "," uconstr(H2)
    "as" simple_intropattern(p) :=
  first [ pose proof (Biconditional.forward.elimination H1 H2) as p
        | pose proof (Biconditional.backward.elimination H1 H2) as p ].

Tactic Notation "modus" "aequans" uconstr(H1) "," uconstr(H2)
    "|-" simple_intropattern(p) :=
  first [ pose proof (Biconditional.forward.elimination H1 H2) as p
        | pose proof (Biconditional.backward.elimination H1 H2) as p ].
