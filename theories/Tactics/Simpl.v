(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* [unfold] and [simpl] serve one purpose, making a statement plainer
 * without changing what it says, so this file gives them one name: [simpl]
 * with a definition unfolds it, [simpl] without one reduces what is already
 * applied. Below, <hypotheses> is a comma-separated list of hypothesis names,
 * one or more.
 *
 * Unfolding one definition, in the four places a step can act:
 *
 *   simpl <d> in <hypotheses>                     unfold <d> in <hypotheses>
 *   simpl <d> in <hypotheses> |- *                unfold <d> in <hypotheses> |- *
 *   simpl <d> in |- *                             unfold <d> in |- *
 *   simpl <d> in *                                unfold <d> in *
 *
 * The same four places, for two definitions and so on up to ten:
 *
 *   simpl <d1>, <d2> in <hypotheses>              unfold <d1>, <d2> in <hypotheses>
 *   simpl <d1>, <d2> in <hypotheses> |- *         unfold <d1>, <d2> in <hypotheses> |- *
 *   simpl <d1>, <d2> in |- *                      unfold <d1>, <d2> in |- *
 *   simpl <d1>, <d2> in *                         unfold <d1>, <d2> in *
 *
 *   simpl <d1>, ..., <d10> in <hypotheses>        unfold <d1>, ..., <d10> in <hypotheses>
 *   simpl <d1>, ..., <d10> in <hypotheses> |- *   and the other two places likewise
 *
 * Reducing what is already applied is Rocq's own [simpl], untouched:
 * [simpl in <hypotheses>], [simpl in <hypotheses> |- *], [simpl in |- *],
 * [simpl in *]. [|- *] is the goal, and [*] every hypothesis together with
 * the goal.
 *
 * Rocq's own [simpl <d> in ...] reduces only the calls headed by <d> and
 * leaves a stuck one as it was; here it unfolds <d> whatever follows. Its
 * [simpl <d>] and [simpl <d> at <n>], without [in], no longer parse where
 * this file is imported.
 *
 * The definitions are counted out to ten, four notations each, because a list
 * of references cannot be handed on: [unfold] parses its own list, while this
 * file can only forward what it was given, and a list of hypotheses is the one
 * kind that survives the journey. Past ten, [unfold] itself has no limit.
 *)

Tactic Notation "simpl" reference(d) "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d in hypotheses.

Tactic Notation "simpl" reference(d) "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d in hypotheses |- *.

Tactic Notation "simpl" reference(d) "in" "|-" "*" :=
  unfold d in |- *.

Tactic Notation "simpl" reference(d) "in" "*" :=
  unfold d in *.

Tactic Notation "simpl" reference(d1) "," reference(d2)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2)
    "in" "|-" "*" :=
  unfold d1, d2 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2)
    "in" "*" :=
  unfold d1, d2 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "in" "|-" "*" :=
  unfold d1, d2, d3 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "in" "*" :=
  unfold d1, d2, d3 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" "*" :=
  unfold d1, d2, d3, d4 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5, d6 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" ne_hyp_list_sep(hypotheses, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in hypotheses.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" ne_hyp_list_sep(hypotheses, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in hypotheses |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in |- *.

Tactic Notation "simpl" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in *.
