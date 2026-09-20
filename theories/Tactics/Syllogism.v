(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Implication.
From jwa Require Import Core.Ltac.

(* Hypothetical syllogism: two implications meeting in the middle compose.
 *
 *   HS                     <Hab>, <Hbc>    A -> B, B -> C |- A -> C
 *
 *   hypothetical syllogism <Hab>, <Hbc>    the same rule, spelled out
 *
 * [as <p>] puts [A -> C] into the context under the intro pattern <p> instead
 * of closing the goal.
 *
 * The premises are taken in the order written: the middle term is what the
 * first concludes and the second assumes. Giving them the other way round is
 * a type error naming the argument at fault.
 *
 * The proofs are [uconstr]: a [constr] is elaborated alone, where a lemma's
 * implicit binders have nothing yet to fix them.
 *)

Tactic Notation "HS" uconstr(Hab) "," uconstr(Hbc) :=
  exact (Implication.transitivity Hab Hbc).

Tactic Notation "HS" uconstr(Hab) "," uconstr(Hbc) "as" simple_intropattern(p) :=
  pose proof (Implication.transitivity Hab Hbc) as p.

Tactic Notation "hypothetical" "syllogism" uconstr(Hab) "," uconstr(Hbc) :=
  exact (Implication.transitivity Hab Hbc).

Tactic Notation "hypothetical" "syllogism" uconstr(Hab) "," uconstr(Hbc)
    "as" simple_intropattern(p) :=
  pose proof (Implication.transitivity Hab Hbc) as p.
