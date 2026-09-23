(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

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
 * [rewrite] does.
 * [<-] is the same law read the other way, [=] being symmetric. Lists of
 * equations, [at] and [by] are not forwarded: a clause cannot be handed on
 * whole, so every shape here is spelled out.
 *)

Tactic Notation "leibniz" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") :=
  rewrite e in hypotheses.

Tactic Notation "leibniz" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  rewrite e in hypotheses |- *.

Tactic Notation "leibniz" uconstr(e) "in" "|-" "*" :=
  rewrite e in |- *.

Tactic Notation "leibniz" uconstr(e) "in" "*" :=
  rewrite e in *.

Tactic Notation "leibniz" "->" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") :=
  rewrite -> e in hypotheses.

Tactic Notation "leibniz" "->" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  rewrite -> e in hypotheses |- *.

Tactic Notation "leibniz" "->" uconstr(e) "in" "|-" "*" :=
  rewrite -> e in |- *.

Tactic Notation "leibniz" "->" uconstr(e) "in" "*" :=
  rewrite -> e in *.

Tactic Notation "leibniz" "<-" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") :=
  rewrite <- e in hypotheses.

Tactic Notation "leibniz" "<-" uconstr(e) "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  rewrite <- e in hypotheses |- *.

Tactic Notation "leibniz" "<-" uconstr(e) "in" "|-" "*" :=
  rewrite <- e in |- *.

Tactic Notation "leibniz" "<-" uconstr(e) "in" "*" :=
  rewrite <- e in *.
