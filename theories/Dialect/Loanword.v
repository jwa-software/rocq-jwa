(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Control Std.

(* Rocq's own tactics that this dialect keeps, each borrowed as it is.
 *
 * [Dialect.Ltac] loads Ltac2 without [Ltac2.Notations], which holds the
 * syntax of every Rocq tactic, so none exists until it is declared. Each
 * declaration below is copied from [Ltac2.Notations] and behaves as Rocq's
 * tactic of that name.
 *
 *   intros <patterns>              intro every premise, by the patterns given
 *   intro [<name>] [<location>]    intro one premise
 *
 * The abbreviations let the bare name be passed where a tactic is expected,
 * as Rocq's own do.
 *)

Ltac2 Notation "intros" p(intropatterns) :=
  Control.enter (fun () => Std.intros false p).
Ltac2 Abbreviation intros := intros.

Ltac2 Notation "intro" id(opt(ident)) mv(opt(move_location)) :=
  Std.intro id mv.
Ltac2 Abbreviation intro := intro.
