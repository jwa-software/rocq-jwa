(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Ltac.
From Ltac2 Require Constr Control Fresh Std.

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
 *   let proof h : A -> Falsum := h    retypes [h] in place, by [change]
 *   let proof h := h                  drops the body of [h], by [clearbody]
 *   let proof h := lemma h            binds [h] to the result
 *
 * With the same name on the right, [h] stays where it is: [let] may give it
 * a new type, which must be convertible with the old, and keeps its body;
 * [let proof] does the same and then drops the body, so that [h] becomes a
 * hypothesis, and does nothing to a hypothesis already of that type.
 * Otherwise the old [h] is replaced: gone from the context, and, if it was a
 * definition, written out in the new body where it was mentioned. When
 * another hypothesis depends on the old [h], nothing happens and [clear]
 * says which. Once [let proof] exists, [let] cannot name a definition
 * [proof].
 *
 * Declared at level 5 beside Ltac2's own [let <x> := <v> in <e>], which is
 * part of the language and which these notations shadow: in a proof, and in
 * any file importing this one, Ltac2's [let ... in] no longer parses. <T>
 * and <e> are [lconstr]s, terms at level 200, so that neither an application
 * nor an operator needs parentheses.
 *)

(* The helpers come first: they use Ltac2's [let ... in], which the
 * notations below take over.
 *)

(* [Control.once_plus], not [Control.plus]: a later failure must not come
 * back here and try the other answer, which would turn a refused [clear]
 * into a second, wrong attempt under the assumption that the name is free.
 *)
Ltac2 is_in_context (x : ident) : bool :=
  Control.once_plus (fun () => let _ := Control.hyp x in true) (fun _ => false).

Ltac2 type_of (x : ident) : Std.clause :=
  { Std.on_hyps := Some [(x, Std.AllOccurrences, Std.InHypTypeOnly)];
    Std.on_concl := Std.NoOccurrences }.

Ltac2 value_of (x : ident) : Std.clause :=
  { Std.on_hyps := Some [(x, Std.AllOccurrences, Std.InHypValueOnly)];
    Std.on_concl := Std.NoOccurrences }.

Ltac2 retype (x : ident) (t : constr) :=
  Std.change None (fun _ => t) (type_of x).

Ltac2 drop_body (x : ident) :=
  Control.once_plus (fun () => Std.clearbody [x]) (fun _ => ()).

(* The new value <y> is bound first, so that <e> may still mention the old
 * <x>. If the old <x> is a definition, its body is written into <y> in its
 * place, which leaves <y> free of it; then the old <x> is cleared, and <y>
 * takes the name. The [clear] fails, with the whole step, when something
 * else still depends on the old <x>.
 *)
Ltac2 shadow_with (x : ident) (y : ident) :=
  Control.once_plus
    (fun () => Std.unfold [(Std.VarRef x, Std.AllOccurrences)] (value_of y))
    (fun _ => ());
  Std.clear [x];
  Std.rename [(y, x)].

Ltac2 pose_proof (e : constr) (x : ident) :=
  Std.specialize (e, Std.NoBindings) (Some (Std.IntroNaming (Std.IntroIdentifier x))).

Ltac2 let_definition (x : ident) (e : constr) :=
  if is_in_context x
  then (let y := Fresh.in_goal x in Std.pose (Some y) e; shadow_with x y)
  else Std.pose (Some x) e.

Ltac2 let_definition_typed (x : ident) (t : constr) (e : constr) :=
  if is_in_context x
  then
    if Constr.equal e (Control.hyp x)
    then retype x t
    else (let y := Fresh.in_goal x in Std.pose (Some y) e; retype y t; shadow_with x y)
  else (Std.pose (Some x) e; retype x t).

(* [let proof h := h] keeps the name and drops the body: [clearbody] leaves
 * every hypothesis that mentions [h] valid, where a replacement would have
 * to clear [h] and so refuse. On a hypothesis with no body it does nothing.
 *)
Ltac2 let_proof (h : ident) (e : constr) :=
  if is_in_context h
  then
    if Constr.equal e (Control.hyp h)
    then drop_body h
    else (let y := Fresh.in_goal h in pose_proof e y; shadow_with h y)
  else pose_proof e h.

Ltac2 let_proof_typed (h : ident) (t : constr) (e : constr) :=
  if is_in_context h
  then
    if Constr.equal e (Control.hyp h)
    then (retype h t; drop_body h)
    else (let y := Fresh.in_goal h in pose_proof constr:($e : $t) y; shadow_with h y)
  else pose_proof constr:($e : $t) h.

(* The intro-pattern forms are declared before the name forms: of two rules
 * that both accept a bare name, the later one is tried first, and a name
 * must reach the helpers that know how to shadow.
 *)
Ltac2 Notation "let" "proof" p(intropattern) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => Std.specialize (e, Std.NoBindings) (Some p)).

Ltac2 Notation "let" "proof" p(intropattern) ":" t(lconstr) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => Std.specialize (constr:($e : $t), Std.NoBindings) (Some p)).

Ltac2 Notation "let" x(ident) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => let_definition x e).

Ltac2 Notation "let" x(ident) ":" t(lconstr) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => let_definition_typed x t e).

Ltac2 Notation "let" "proof" h(ident) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => let_proof h e).

Ltac2 Notation "let" "proof" h(ident) ":" t(lconstr) ":=" e(lconstr) : 5 :=
  Control.enter (fun () => let_proof_typed h t e).
