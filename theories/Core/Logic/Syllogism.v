(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.All.

(* The syllogisms of traditional logic, each under the mediaeval name that
 * encodes its form. [S], [M] and [P] are the minor, middle and major terms,
 * predicates over a domain rather than propositions, which is what separates
 * a syllogism from the propositional rules of the other files here.
 *
 * No type is declared for the subject, so the module carries the name by
 * itself; its laws read [Syllogism.Barbara]. A law that is a proper name
 * keeps its capital, which also tells the law apart from the tactic that
 * applies it.
 *)
Module Syllogism. (* Syllogism *)

(* Barbara: every M is P, every S is M, so every S is P. The name's three
 * [a]s are the three universal affirmative propositions.
 *)
(* Barbara *)
Theorem Barbara
  : forall {A : Type} {S : A -> Prop} {M : A -> Prop} {P : A -> Prop} .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . S x -> P x).
Proof.
  intros A S M P.

  (* The context gains [mp : forall (x : A) . M x -> P x] *)
  intro mp.
  (* The context gains [sm : forall (x : A) . S x -> M x] *)
  intro sm.

  intro x.
  intro s.

  let proof m := sm x s.
  let proof facto := mp x m.

  ipso facto.
Qed.

End Syllogism. (* Syllogism *)
