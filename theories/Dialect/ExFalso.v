(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Constr Control Ind Int Message Std.

(* Ex falso quodlibet: from what cannot exist, anything.
 *
 *   ex <H> quodlibet    <H> : Falsum |- any goal
 *
 * Closes the goal outright, whatever its sort, [Prop] or [Type]; <H> is a
 * hypothesis or any term, parenthesised when it is an application. Rocq's
 * [exfalso] is another step: it turns the goal into [Falsum] and leaves it to
 * be proved, where this one needs the proof in hand.
 *
 * <H> must have an empty type: an inductive with no constructor, once its
 * type is reduced to head normal form, so [Assert false] passes. That is
 * [Falsum] for a proposition and [Empty] for a type, the same principle at
 * two sorts; this layer sits below both and names neither. Anything else is
 * refused with an error naming what <H> proves instead.
 *
 * The goal is closed by [match <H> return <goal> with end], which has no
 * branch to write since the type has no constructor.
 *)

Ltac2 has_no_constructor (t : constr) : bool :=
  match Constr.Unsafe.kind (Std.eval_hnf t) with
  | Constr.Unsafe.Ind inductive _ => Int.equal (Ind.nconstructors (Ind.data inductive)) 0
  | _ => false
  end.

Ltac2 ex_quodlibet (h : constr) :=
  Control.enter (fun () =>
    let t := Constr.type h in
    if has_no_constructor t
    then
      Control.refine (fun () =>
        let goal := Control.goal () in
        constr:(match $h return $goal with end))
    else
      Control.zero
        (Tactic_failure
           (Some (Message.concat (Message.of_string "ex quodlibet: ")
                 (Message.concat (Message.of_constr h)
                 (Message.concat (Message.of_string " proves ")
                 (Message.concat (Message.of_constr t)
                                 (Message.of_string ", which is not empty")))))))).

Ltac2 Notation "ex" h(constr) "quodlibet" :=
  ex_quodlibet h.
