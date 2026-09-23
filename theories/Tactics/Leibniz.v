(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.
From jwa Require Import Tactics.Place.
From Ltac2 Require Control Std.

(* Leibniz's law, x = y, P x |- P y: what is equal may be put for what it
 * equals. Below, <e> is a proof of an equation and <hypotheses> a
 * comma-separated list of hypothesis names, one or more.
 *
 *   leibniz <e> in <hypotheses>                  rewrite <e> in <hypotheses>
 *   leibniz <e> in <hypotheses> |- *             rewrite <e> in <hypotheses> |- *
 *   leibniz <e> in |- *                          rewrite <e> in |- *
 *   leibniz <e> in *                             rewrite <e> in *
 *
 * There is no bare [leibniz <e>]: the place is always written, the goal as
 * [in |- *]. Each of the four also takes [->] or [<-] before <e>, as
 * [rewrite] does. [<-] is the same law read the other way, [=] being
 * symmetric. A list of equations, [at] and [by] are not taken.
 *
 * <e> is a [preterm] typed as an open term, so that a hole in it is left for
 * the rewrite to fill by matching.
 *)
Ltac2 leibniz_rewrite (orientation : Std.orientation option) (e : preterm) (place : Std.clause) :=
  Control.enter (fun () =>
    Std.rewrite
      false
      [ { Std.rew_orient := orientation;
          Std.rew_repeat := Std.Precisely 1;
          Std.rew_equatn := (fun () => (open_constr:($preterm:e), Std.NoBindings)) } ]
      place
      None).

Ltac2 Notation "leibniz" o(orient) e(preterm) "in" hypotheses(list1(ident, ",")) :=
  leibniz_rewrite o e (Place.hypotheses hypotheses).

Ltac2 Notation "leibniz" o(orient) e(preterm) "in" hypotheses(list1(ident, ",")) "|-" "*" :=
  leibniz_rewrite o e (Place.hypotheses_and_goal hypotheses).

Ltac2 Notation "leibniz" o(orient) e(preterm) "in" "|-" "*" :=
  leibniz_rewrite o e Place.goal.

Ltac2 Notation "leibniz" o(orient) e(preterm) "in" "*" :=
  leibniz_rewrite o e Place.everywhere.
