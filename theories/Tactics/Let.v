(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* let <x> = <e>          pose (<x> := <e>)
 * let <x> : <T> = <e>    pose (<x> : <T> := <e>)
 *
 * Names <e> as a local definition <x>, whose body stays visible; nothing
 * else in the goal or the context is replaced.
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
