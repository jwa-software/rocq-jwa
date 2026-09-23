(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Syllogism.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.
From Ltac2 Require Control Std.

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
 * wanted -- inside [ipso], a [let proof], or another of the same, which is
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
 * The tactics take their proofs as [preterm]s and type the whole application
 * at once, so that a lemma's implicit binders may be fixed by the other
 * premise. The term form has no such delay to offer, each of its premises
 * being a term in its own right, so a bare lemma name whose implicits only
 * the other premise would fix does not elaborate there. Name it first, or
 * write [@] and supply them; or use the [as] form.
 *)

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'hs' Hab , Hbc" := (Conditional.transitivity Hab Hbc)
  (only parsing).

Ltac2 Notation "hs" hab(preterm) "," hbc(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    Std.specialize
      (open_constr:(Conditional.transitivity $preterm:hab $preterm:hbc), Std.NoBindings)
      (Some p)).

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'hypothetical' 'syllogism' Hab , Hbc"
    := (Conditional.transitivity Hab Hbc)
  (only parsing).

Ltac2 Notation "hypothetical" "syllogism" hab(preterm) "," hbc(preterm)
    "as" p(intropattern) :=
  Control.enter (fun () =>
    Std.specialize
      (open_constr:(Conditional.transitivity $preterm:hab $preterm:hbc), Std.NoBindings)
      (Some p)).

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'barbara' Hmp , Hsm" := (Syllogism.Barbara Hmp Hsm)
  (only parsing).

Ltac2 Notation "barbara" hmp(preterm) "," hsm(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    Std.specialize
      (open_constr:(Syllogism.Barbara $preterm:hmp $preterm:hsm), Std.NoBindings)
      (Some p)).
