(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Syllogism.
From jwa Require Import Core.Ltac.

(* Syllogisms: two premises meeting in a middle term compose into a third.
 *
 *   HS                     <Hab>, <Hbc>    A -> B, B -> C |- A -> C
 *
 *   hypothetical syllogism <Hab>, <Hbc>    the same rule, spelled out
 *
 *   barbara                <Hmp>, <Hsm>    forall x . M x -> P x,
 *                                          forall x . S x -> M x
 *                                          |- forall x . S x -> P x
 *
 * [as <p>] puts the conclusion into the context under the intro pattern <p>
 * instead of closing the goal.
 *
 * The premises are taken in the order written: the middle term is what the
 * first concludes and the second assumes. Giving them the other way round is
 * a type error naming the argument at fault. Unlike the modi, whose two
 * premises have different shapes, both premises of a syllogism look alike,
 * so their order is what says which one is the major.
 *
 * The proofs are [uconstr]: a [constr] is elaborated alone, where a lemma's
 * implicit binders have nothing yet to fix them.
 *)

Tactic Notation "HS" uconstr(Hab) "," uconstr(Hbc) :=
  exact (Conditional.transitivity Hab Hbc).

Tactic Notation "HS" uconstr(Hab) "," uconstr(Hbc) "as" simple_intropattern(p) :=
  pose proof (Conditional.transitivity Hab Hbc) as p.

Tactic Notation "hypothetical" "syllogism" uconstr(Hab) "," uconstr(Hbc) :=
  exact (Conditional.transitivity Hab Hbc).

Tactic Notation "hypothetical" "syllogism" uconstr(Hab) "," uconstr(Hbc)
    "as" simple_intropattern(p) :=
  pose proof (Conditional.transitivity Hab Hbc) as p.

Tactic Notation "barbara" uconstr(Hmp) "," uconstr(Hsm) :=
  exact (Syllogism.Barbara Hmp Hsm).

Tactic Notation "barbara" uconstr(Hmp) "," uconstr(Hsm) "as" simple_intropattern(p) :=
  pose proof (Syllogism.Barbara Hmp Hsm) as p.
