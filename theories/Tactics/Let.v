(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* let <x> = <e>                pose (<x> := <e>)
 * let <x> : <T> = <e>          pose (<x> : <T> := <e>)
 * let proof <p> = <e>          pose proof (<e>) as <p>
 * let proof <p> : <T> = <e>    pose proof (<e> : <T>) as <p>
 *
 * [let] names <e> as a local definition <x>, whose body stays visible;
 * [let proof] adds <e> as a hypothesis, its type alone, destructured by the
 * intro pattern <p> or named by it. Nothing else in the goal or the context
 * is replaced. Once [let proof] exists, [let] cannot name a definition
 * [proof]: the parser reads [let proof] as the start of the second form.
 *
 * Declared at level 5 beside Ltac's own [let <x> := <v> in <tac>], which it
 * shadows wherever this file is imported: after [let <x>] the parser now
 * wants [=] or [:]. <e> is an [lconstr], a term at level 200, so that an
 * application needs no parentheses; a plain [constr] stops at level 8 and
 * would read [let k = f m] as [let k = f].
 *)

Tactic Notation (at level 5) "let" ident(x) "=" lconstr(e) :=
  pose (x := e).

Tactic Notation (at level 5) "let" ident(x) ":" constr(T) "=" lconstr(e) :=
  refine (let x : T := e in _).

Tactic Notation (at level 5) "let" "proof" simple_intropattern(p) "=" lconstr(e) :=
  pose proof e as p.

Tactic Notation (at level 5) "let" "proof" simple_intropattern(p) ":" constr(T) "=" lconstr(e) :=
  pose proof (e : T) as p.
