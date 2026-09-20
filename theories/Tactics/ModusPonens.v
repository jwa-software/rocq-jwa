(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* Modus ponens: from [A -> B] and [A], infer [B].
 *
 *   modus ponens <Hab> <Ha>            proves a goal [B]
 *   modus ponens <Hab> <Ha> as <p>     adds [B] to the context as <p>
 *
 * [<Hab>] is a proof of [A -> B], [<Ha>] a proof of [A]. [<p>] is an intro
 * pattern, not only a name, so [as [x y]] splits a conjunction on arrival.
 *
 * The proofs are [uconstr]: a [constr] is elaborated alone, where a lemma's
 * implicit binders have nothing yet to fix them.
 *)
Tactic Notation "modus" "ponens" uconstr(HAB) uconstr(HA) :=
  exact (HAB HA).

Tactic Notation "modus" "ponens" uconstr(HAB) uconstr(HA) "as" simple_intropattern(p) :=
  pose proof (HAB HA) as p.
