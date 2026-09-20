(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* One name for the two ways a statement is made plainer without changing
 * what it says: unfolding a definition, and reducing what is already applied.
 * Below, <hs> is a comma-separated list of hypotheses, one or more.
 *
 * Unfolding one definition, in the four places a step can act:
 *
 *   simplify <d> in <hs>                     unfold <d> in <hs>
 *   simplify <d> in <hs> |- *                unfold <d> in <hs> |- *
 *   simplify <d> in |- *                     unfold <d> in |- *
 *   simplify <d> in *                        unfold <d> in *
 *
 * The same four places, for two definitions and so on up to ten:
 *
 *   simplify <d1>, <d2> in <hs>              unfold <d1>, <d2> in <hs>
 *   simplify <d1>, <d2> in <hs> |- *         unfold <d1>, <d2> in <hs> |- *
 *   simplify <d1>, <d2> in |- *              unfold <d1>, <d2> in |- *
 *   simplify <d1>, <d2> in *                 unfold <d1>, <d2> in *
 *
 *   simplify <d1>, ..., <d10> in <hs>        unfold <d1>, ..., <d10> in <hs>
 *   simplify <d1>, ..., <d10> in <hs> |- *   and the other two places likewise
 *
 * Reducing what is already applied:
 *
 *   simplify in <hs>                         simpl in <hs>
 *   simplify in <hs> |- *                    simpl in <hs> |- *
 *   simplify in |- *                         simpl in |- *
 *   simplify in *                            simpl in *
 *
 * [|- *] is the goal, and [*] every hypothesis together with the goal.
 *
 * Written out, one of each shape:
 *
 *   simplify Negation in h1, h2
 *   simplify Negation in h |- *
 *   simplify Even, Divides in |- *
 *   simplify Even, Divides in *
 *   simplify in e
 *   simplify in e |- *
 *   simplify in |- *
 *   simplify in *
 *
 * The [in] is what tells the two forms apart: an identifier after [simplify]
 * opens the unfolding form, [in] the reducing one. Without it the parser
 * cannot choose, both forms then starting with an identifier.
 *
 * The definitions are counted out to ten, four notations each, because a list
 * of references cannot be handed on: [unfold] parses its own list, while this
 * file can only forward what it was given, and a list of hypotheses is the one
 * kind that survives the journey. Past ten, [unfold] itself has no limit.
 *)

Tactic Notation "simplify" reference(d) "in" ne_hyp_list_sep(hs, ",") :=
  unfold d in hs.

Tactic Notation "simplify" reference(d) "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d in hs |- *.

Tactic Notation "simplify" reference(d) "in" "|-" "*" :=
  unfold d in |- *.

Tactic Notation "simplify" reference(d) "in" "*" :=
  unfold d in *.

Tactic Notation "simplify" reference(d1) "," reference(d2)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2)
    "in" "|-" "*" :=
  unfold d1, d2 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2)
    "in" "*" :=
  unfold d1, d2 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "in" "|-" "*" :=
  unfold d1, d2, d3 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "in" "*" :=
  unfold d1, d2, d3 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4)
    "in" "*" :=
  unfold d1, d2, d3, d4 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5, d6 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9 in *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" ne_hyp_list_sep(hs, ",") :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in hs.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in hs |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" "|-" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in |- *.

Tactic Notation "simplify" reference(d1) "," reference(d2) "," reference(d3)
    "," reference(d4) "," reference(d5) "," reference(d6)
    "," reference(d7) "," reference(d8) "," reference(d9)
    "," reference(d10)
    "in" "*" :=
  unfold d1, d2, d3, d4, d5, d6, d7, d8, d9, d10 in *.

Tactic Notation "simplify" "in" ne_hyp_list_sep(hs, ",") :=
  simpl in hs.

Tactic Notation "simplify" "in" ne_hyp_list_sep(hs, ",") "|-" "*" :=
  simpl in hs |- *.

Tactic Notation "simplify" "in" "|-" "*" :=
  simpl in |- *.

Tactic Notation "simplify" "in" "*" :=
  simpl in *.
