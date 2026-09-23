(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Syllogism.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* Syllogisms: two premises meeting in a middle term compose into a third.
 *
 *   hs                     <Hab>, <Hbc>    A -> B, B -> C |- A -> C
 *
 *   hypothetical syllogism <Hab>, <Hbc>    the same rule, spelled out
 *
 *   barbara                <Hmp>, <Hsm>    forall x . M x -> P x,
 *                                          forall x . S x -> M x
 *                                          |- forall x . S x -> P x
 *
 * Each of the three splits into two shapes. Bare, none of them is a tactic:
 * each is a term, so it closes nothing and stands where its conclusion is
 * wanted -- inside [exact], a [pose proof], or another of the same, which is
 * what lets two syllogisms be written as one expression, [hs (hs hab, hbc),
 * hcd]. Only [<name> <H1>, <H2> as <p>] is a tactic, putting the conclusion
 * into the context under the intro pattern <p>.
 *
 * A term notation makes its head a keyword, so nothing anywhere may be named
 * [hs], [hypothetical], [syllogism] or [barbara].
 *
 * The premises are taken in the order written: the middle term is what the
 * first concludes and the second assumes. Giving them the other way round is
 * a type error naming the argument at fault. Unlike the modi, whose two
 * premises have different shapes, both premises of a syllogism look alike,
 * so their order is what says which one is the major.
 *
 * The tactics take their proofs as [uconstr]: a [constr] is elaborated
 * alone, where a lemma's implicit binders have nothing yet to fix them. The
 * term form needs no such care, being elaborated in the place it stands.
 *)

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'hs' Hab , Hbc" := (Conditional.transitivity Hab Hbc)
  (only parsing).

Tactic Notation "hs" uconstr(Hab) "," uconstr(Hbc) "as" simple_intropattern(p) :=
  pose proof (Conditional.transitivity Hab Hbc) as p.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'hypothetical' 'syllogism' Hab , Hbc"
    := (Conditional.transitivity Hab Hbc)
  (only parsing).

Tactic Notation "hypothetical" "syllogism" uconstr(Hab) "," uconstr(Hbc)
    "as" simple_intropattern(p) :=
  pose proof (Conditional.transitivity Hab Hbc) as p.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'barbara' Hmp , Hsm" := (Syllogism.Barbara Hmp Hsm)
  (only parsing).

Tactic Notation "barbara" uconstr(Hmp) "," uconstr(Hsm) "as" simple_intropattern(p) :=
  pose proof (Syllogism.Barbara Hmp Hsm) as p.
