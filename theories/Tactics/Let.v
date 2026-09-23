(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.

(* let <x> := <e>                pose (<x> := <e>)
 * let <x> : <T> := <e>          pose (<x> : <T> := <e>)
 * let proof <p> := <e>          pose proof (<e>) as <p>
 * let proof <p> : <T> := <e>    pose proof (<e> : <T>) as <p>
 *
 * [:=] reads "is defined as", as in [Definition]: the binding is neither an
 * equation to be proved nor an assignment. [let] names <e> as a local
 * definition <x>, whose body stays visible; [let proof] adds <e> as a
 * hypothesis, its type alone, named by <p> or destructured by it.
 *
 * A name already in the context is shadowed, not refused:
 *
 *   let proof h : (A -> Falsum) := h    retypes [h] in place, by [change]
 *   let proof h := lemma h              binds [h] to the result
 *
 * With a type and the same name on the right, [h] keeps its body and takes
 * the new type, which must be convertible with the old. Otherwise the old
 * [h] is replaced: gone from the context, and, if it was a definition,
 * written out in the new body where it was mentioned. When another
 * hypothesis depends on the old [h], nothing happens and [clear] says which.
 * Once [let proof] exists, [let] cannot name a definition [proof].
 *
 * Declared at level 5 beside Ltac's own [let <x> := <v> in <tac>], which it
 * shadows wherever this file is imported. <T> and <e> are [lconstr]s, terms
 * at level 200, so that neither an application nor an operator needs
 * parentheses; a plain [constr] stops at level 8.
 *)

(* The helpers come first: they use Ltac's [let ... in], which the notations
 * below take over.
 *)

(* [tryif (let t := type of x in idtac)] asks whether [x] names anything in
 * the context.
 *)

(* The new value <y> is bound first, so that <e> may still mention the old
 * <x>. If the old <x> is a definition, its body is written into <y> in its
 * place, which leaves <y> free of it; then the old <x> is cleared, and <y>
 * takes the name. The [clear] fails, with the whole step, when something
 * else still depends on the old <x>.
 *)
Ltac let_replace x y :=
  try unfold x in (value of y);
  clear x;
  rename y into x.

Ltac let_definition x e :=
  tryif (let t := type of x in idtac)
  then (let y := fresh x in pose (y := e); let_replace x y)
  else pose (x := e).

Ltac let_definition_typed x T e :=
  tryif (let t := type of x in idtac)
  then
    (tryif constr_eq e x
     then change T in (type of x)
     else (let y := fresh x in refine (let y : T := e in _); let_replace x y))
  else refine (let x : T := e in _).

Ltac let_proof h e :=
  tryif (let t := type of h in idtac)
  then (let y := fresh h in pose proof e as y; let_replace h y)
  else pose proof e as h.

Ltac let_proof_typed h T e :=
  tryif (let t := type of h in idtac)
  then
    (tryif constr_eq e h
     then change T in (type of h)
     else (let y := fresh h in pose proof (e : T) as y; let_replace h y))
  else pose proof (e : T) as h.

(* The intro-pattern forms are declared before the name forms: of two rules
 * that both accept a bare name, the later one is tried first, and a name
 * must reach the helpers that know how to shadow.
 *)
Tactic Notation (at level 5) "let" "proof" simple_intropattern(p) ":=" lconstr(e) :=
  pose proof e as p.

Tactic Notation (at level 5) "let" "proof" simple_intropattern(p) ":" lconstr(T) ":=" lconstr(e) :=
  pose proof (e : T) as p.

Tactic Notation (at level 5) "let" ident(x) ":=" lconstr(e) :=
  let_definition x e.

Tactic Notation (at level 5) "let" ident(x) ":" lconstr(T) ":=" lconstr(e) :=
  let_definition_typed x T e.

Tactic Notation (at level 5) "let" "proof" ident(h) ":=" lconstr(e) :=
  let_proof h e.

Tactic Notation (at level 5) "let" "proof" ident(h) ":" lconstr(T) ":=" lconstr(e) :=
  let_proof_typed h T e.
