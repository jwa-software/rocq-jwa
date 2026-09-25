(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Idem.
From jwa Require Import Dialect.Local.
From Ltac2 Require Array Constr Control Ind Int Message Std.

(* Ex falso quodlibet: from what cannot exist, anything.
 *
 *   ex <H> quodlibet    <H> : Falsum |- any goal
 *   ex <H> quodlibet    <H> : C1 ... = C2 ... |- any goal, C1 and C2 two
 *                       different constructors, as [discriminate <H>]
 *
 * Closes the goal outright, whatever its sort, [Prop] or [Type]; <H> is a
 * hypothesis or any term, parenthesised when it is an application. Rocq's
 * [exfalso] is another step: it turns the goal into [Falsum] and leaves it to
 * be proved, where this one needs the proof in hand.
 *
 * The type of <H> is read as written, nothing reduced. It is either an
 * inductive with no constructor -- [Falsum] for a proposition, [Empty] for
 * a type, the same principle at two sorts; this layer sits below both and
 * names neither -- or an equation [<a> = <b>] whose sides are headed by two
 * different constructors, which no proof can be. A type that only computes
 * to one of these, such as [Assert false] or [negate true = true], is
 * refused, to be simplified first; so is a function such as [~ A], to be
 * applied first: [ex (<H> <argument>) quodlibet].
 *
 * The goal is closed by [match <H> return <goal> with end], which has no
 * branch to write since the type has no constructor.
 *)

Ltac2 has_no_constructor (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind inductive _ => Int.equal (Ind.nconstructors (Ind.data inductive)) 0
  | _ => false
  end.

(* The constructor a term is headed by as written, applied or not. *)
Ltac2 constructor_head (c : constr) : constr option :=
  let head := match Constr.Unsafe.kind c with Constr.Unsafe.App f _ => f | _ => c end in
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Constructor _ _ => Some head
  | _ => None
  end.

Ltac2 is_constructor_clash (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App head args =>
      let n := Array.length args in
      if Int.lt n 2
      then false
      else if Idem.is_equality head
      then
        match constructor_head (Array.get args (Int.sub n 2)) with
        | Some a =>
            match constructor_head (Array.get args (Int.sub n 1)) with
            | Some b => if Constr.equal a b then false else true
            | None => false
            end
        | None => false
        end
      else false
  | _ => false
  end.

Ltac2 ex_refuse (h : constr) (t : constr) (rest : message) :=
  Control.zero
    (Tactic_failure
       (Some (Message.concat (Message.of_string "ex quodlibet: ")
             (Message.concat (Message.of_constr h)
             (Message.concat (Message.of_string " proves ")
             (Message.concat (Message.of_constr t) rest)))))).

Ltac2 not_as_written (h : constr) (t : constr) :=
  ex_refuse h t
    (Message.concat
       (Message.of_string ", which as written is neither empty nor an equation")
       (Message.concat
          (Message.of_string " between different constructors;")
          (Message.of_string " if it computes to one, simplify it first"))).

Ltac2 ex_quodlibet (h : unit -> constr) :=
  Control.enter (fun () =>
    let h := Local.checked "ex quodlibet" h in
    let t := Constr.type h in
    if has_no_constructor t
    then
      Control.refine (fun () =>
        let goal := Control.goal () in
        constr:(match $h return $goal with end))
    else if is_constructor_clash t
    then
      Control.once_plus
        (fun () =>
          Std.discriminate false (Some (Std.ElimOnConstr (fun () => (h, Std.NoBindings)))))
        (fun _ => not_as_written h t)
    else
      (* The type is reduced only to choose the advice, so [~ A] is told to be applied. *)
      match Constr.Unsafe.kind (Std.eval_hnf t) with
      | Constr.Unsafe.Prod _ _ =>
          ex_refuse h t
            (Message.concat (Message.of_string ", a function; apply it first: ex (")
               (Message.concat (Message.of_constr h)
                  (Message.of_string " <argument>) quodlibet")))
      | _ => not_as_written h t
      end).

Ltac2 Notation "ex" h(thunk(constr)) "quodlibet" :=
  ex_quodlibet h.
