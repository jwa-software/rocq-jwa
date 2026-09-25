(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From Ltac2 Require Constr Control Std.

(* ipso <H>    closes the goal with <H>, as Rocq's [exact <H>] does
 *
 * Latin for "by itself": the proof given is the whole of it. The preferred
 * use names the closing proof [facto], so the step reads [ipso facto], "by
 * the fact itself"; [facto] alone may be written without [&]. A tactic
 * notation, not a term notation, so [ipso] stays free as a name.
 *
 * <H> is a [preterm], typed against the goal only here, so that a hole or an
 * implicit argument in it is filled from the goal.
 *)
Ltac2 exact_preterm (c : preterm) :=
  Control.enter (fun () =>
    let c :=
      Local.checked "ipso" (fun () =>
        Constr.Pretype.pretype
          Constr.Pretype.Flags.constr_flags
          (Constr.Pretype.expected_oftype (Control.goal ()))
          c) in
    Std.exact_no_check c).

Ltac2 Notation "ipso" c(preterm) :=
  exact_preterm c.
