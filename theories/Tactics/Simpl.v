(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.
From jwa Require Import Tactics.Place.
From Ltac2 Require Control List Message RedFlags Std.

(* [unfold] and [simpl] serve one purpose, making a statement plainer
 * without changing what it says, so this file gives them one name: [simpl]
 * with definitions unfolds them, [simpl] without one reduces what is already
 * applied. Below, <definitions> and <hypotheses> are comma-separated lists
 * of names, one or more of each.
 *
 * Unfolding, in the four places a step can act:
 *
 *   simpl <definitions> in <hypotheses>          unfold <definitions> in <hypotheses>
 *   simpl <definitions> in <hypotheses> |- *     unfold <definitions> in <hypotheses> |- *
 *   simpl <definitions> in |- *                  unfold <definitions> in |- *
 *   simpl <definitions> in *                     unfold <definitions> in *
 *
 * Unfolding only the <n>th occurrence of one definition, counting from one,
 * in one hypothesis or in the goal:
 *
 *   simpl <d> at <n> in <H>                      unfold <d> at <n> in <H>
 *   simpl <d> at <n> in |- *                     unfold <d> at <n> in |- *
 *
 * Reducing what is already applied, Rocq's own [simpl]:
 *
 *   simpl in <hypotheses>
 *   simpl in <hypotheses> |- *
 *   simpl in |- *
 *   simpl in *
 *
 * [|- *] is the goal, and [*] every hypothesis together with the goal.
 * There is no bare [simpl] and no [simpl <d>]: the place is always written.
 * Rocq's own [simpl <d> in ...] would reduce only the calls headed by <d>
 * and leave a stuck one as it was; here it unfolds <d> whatever follows.
 *)

Ltac2 unfold_definitions (ds : Std.reference list) (place : Std.clause) :=
  Control.enter (fun () =>
    Std.unfold (List.map (fun d => (d, Std.AllOccurrences)) ds) place).

(* One notation takes both [simpl <definitions> in] and [simpl <d> at <n>
 * in], the parser having no way to tell a list of one from a single name
 * before it reaches [at]; the second form checks that the list has one.
 *)
Ltac2 unfold_occurrence (ds : Std.reference list) (n : int) (place : Std.clause) :=
  match ds with
  | [d] => Control.enter (fun () => Std.unfold [(d, Std.OnlyOccurrences [n])] place)
  | _ =>
      Control.zero
        (Tactic_failure (Some (Message.of_string "simpl: at <n> takes one definition")))
  end.

Ltac2 reduce (place : Std.clause) :=
  Control.enter (fun () => Std.simpl RedFlags.all None place).

Ltac2 Notation "simpl" ds(list1(reference, ",")) "in" hypotheses(list1(ident, ",")) :=
  unfold_definitions ds (Place.hypotheses hypotheses).

Ltac2 Notation "simpl" ds(list1(reference, ",")) "in" hypotheses(list1(ident, ",")) "|-" "*" :=
  unfold_definitions ds (Place.hypotheses_and_goal hypotheses).

Ltac2 Notation "simpl" ds(list1(reference, ",")) "in" "|-" "*" :=
  unfold_definitions ds Place.goal.

Ltac2 Notation "simpl" ds(list1(reference, ",")) "in" "*" :=
  unfold_definitions ds Place.everywhere.

Ltac2 Notation "simpl" ds(list1(reference, ",")) "at" n(tactic(0)) "in" h(ident) :=
  unfold_occurrence ds n (Place.hypotheses [h]).

Ltac2 Notation "simpl" ds(list1(reference, ",")) "at" n(tactic(0)) "in" "|-" "*" :=
  unfold_occurrence ds n Place.goal.

Ltac2 Notation "simpl" "in" hypotheses(list1(ident, ",")) :=
  reduce (Place.hypotheses hypotheses).

Ltac2 Notation "simpl" "in" hypotheses(list1(ident, ",")) "|-" "*" :=
  reduce (Place.hypotheses_and_goal hypotheses).

Ltac2 Notation "simpl" "in" "|-" "*" :=
  reduce Place.goal.

Ltac2 Notation "simpl" "in" "*" :=
  reduce Place.everywhere.
