(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* The tactic language is a compiled plugin, not Rocq syntax: without this,
   [exact] is a syntax error. *)
Declare ML Module "rocq-runtime.plugins.ltac".

(* Picks the grammar that [Proof.] bodies are parsed with; Ltac1 is "Classic".
   [#[export]] or the setting does not reach importing files. *)
#[export] Set Default Proof Mode "Classic".
