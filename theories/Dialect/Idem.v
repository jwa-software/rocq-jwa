(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Std.

(* quod idem est    closes a goal <a> = <b> whose sides are convertible, as
 *                  Rocq's [reflexivity] does
 *
 * Latin for "which is the same thing": the two sides reduce to one term. A
 * tactic notation, not a term notation, so [quod], [idem] and [est] stay free
 * as names.
 *)
Ltac2 Notation "quod" "idem" "est" :=
  Std.reflexivity ().
