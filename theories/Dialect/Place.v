(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require List Std.

(* The four places a step of this layer acts on, each spelled with [in]:
 *
 *   in <hypotheses>          Place.hypotheses
 *   in <hypotheses> |- *     Place.hypotheses_and_goal
 *   in |- *                  Place.goal
 *   in *                     Place.everywhere
 *
 * as the [Std.clause] a primitive tactic takes. The notations spell the
 * places out themselves rather than take Ltac2's own [clause]: that would
 * also accept [at <n>] with no [in], and the goal is never left implicit.
 *)

Ltac2 hypotheses (names : ident list) : Std.clause :=
  { Std.on_hyps := Some (List.map (fun h => (h, Std.AllOccurrences, Std.InHyp)) names);
    Std.on_concl := Std.NoOccurrences }.

Ltac2 hypotheses_and_goal (names : ident list) : Std.clause :=
  { Std.on_hyps := Some (List.map (fun h => (h, Std.AllOccurrences, Std.InHyp)) names);
    Std.on_concl := Std.AllOccurrences }.

Ltac2 goal : Std.clause :=
  { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }.

Ltac2 everywhere : Std.clause :=
  { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.
