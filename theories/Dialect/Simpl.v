(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Place.
From Ltac2 Require Constr Control Env Ident List Message RedFlags Std.

(* [unfold] and [simpl] serve one purpose, making a statement plainer
 * without changing what it says, so this file gives them one name: [simpl]
 * with definitions unfolds them, [simpl] without one reduces what is already
 * applied. Below, <definitions> and <hypotheses> are comma-separated lists
 * of names, one or more of each; in <definitions>, a local definition of the
 * context is written [&P].
 *
 * Unfolding, in the four places a step can act:
 *
 *   simpl <definitions> in <hypotheses>          unfold <definitions> in <hypotheses>
 *   simpl <definitions> in <hypotheses> |- *     unfold <definitions> in <hypotheses> |- *
 *   simpl <definitions> in |- *                  unfold <definitions> in |- *
 *   simpl <definitions> in *                     unfold <definitions> in *
 *
 * Unfolding only the <n>th occurrence of one definition, counting from one,
 * in one hypothesis or in the goal:
 *
 *   simpl <d> at <n> in <H>                      unfold <d> at <n> in <H>
 *   simpl <d> at <n> in |- *                     unfold <d> at <n> in |- *
 *
 * Reducing what is already applied, Rocq's own [simpl]:
 *
 *   simpl in <hypotheses>
 *   simpl in <hypotheses> |- *
 *   simpl in |- *
 *   simpl in *
 *
 * Reducing the type of a proof, as a term, the way [symm <H>] turns an
 * equation round: [let proof e := simpl &h], [leibniz (simpl &e) in |- *].
 *
 *   simpl <H>
 *
 * [|- *] is the goal, and [*] every hypothesis together with the goal.
 * As a step there is no bare [simpl] and no [simpl <d>]: the place is always written.
 * Rocq's own [simpl <d> in ...] would reduce only the calls headed by <d>
 * and leave a stuck one as it was; here it unfolds <d> whatever follows.
 *
 * An unfolding that would change nothing fails and says where: each
 * definition must occur in each hypothesis named, in the goal when [|- *]
 * is named, and somewhere when [*] is; each hypothesis named must be in the
 * context. A reduction that would change nothing fails the same way: each
 * hypothesis named must change, the goal when [|- *] is named, and
 * something when [*] is; [simpl <H>] fails when the type of <H> has
 * nothing to reduce.
 *)

(* A global definition is named as in a term, [Negation] or [Nat.add], and a
 * local definition of the context by [&P]; a local one never hides a global
 * one of the same name. The name is read as a term, which may add holes for
 * implicit arguments: the head is taken, and the answer leaves by an
 * exception, which undoes the holes.
 *)
Ltac2 rec head (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => head f
  | _ => c
  end.

Ltac2 Type exn ::= [ Simpl_definition (Std.reference * message) ].

Ltac2 refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

Ltac2 simpl_says (s : string) : message := Message.of_string s.

(* The body and the type of a name of the context, the body being [None]
 * for a hypothesis; [None] for a name the context does not hold.
 *)
Ltac2 entry (x : ident) : (constr option * constr) option :=
  match List.find_opt (fun h => match h with (y, _, _) => Ident.equal x y end)
          (Control.hyps ()) with
  | Some h => match h with (_, body, type) => Some (body, type) end
  | None => None
  end.

Ltac2 ampersand (x : ident) : message :=
  Message.concat (simpl_says "&") (Message.of_ident x).

Ltac2 hypothesis (shown : message) :=
  refuse [simpl_says "simpl: "; shown;
          simpl_says " is a hypothesis, not a definition; it has nothing to unfold"].

Ltac2 not_a_definition (c : constr) :=
  refuse [simpl_says "simpl: "; Message.of_constr c;
          simpl_says " is not a definition; it has nothing to unfold"].

(* [&x]: the local definition [x] of the context. *)
Ltac2 local (x : ident) (global_name : message) : Std.reference * message :=
  match entry x with
  | Some (Some _, _) => (Std.VarRef x, ampersand x)
  | Some (None, _) => hypothesis (ampersand x)
  | None =>
      refuse [simpl_says "simpl: "; global_name;
              simpl_says " is a global definition; write it without &"]
  end.

(* A bare name: a global definition only. *)
Ltac2 global (c : constr) : Std.reference * message :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => (Std.ConstRef k, Message.of_constr c)
  | Constr.Unsafe.Var x =>
      match entry x with
      | Some (Some _, _) =>
          refuse [simpl_says "simpl: "; Message.of_ident x;
                  simpl_says " is a local definition; write "; ampersand x;
                  simpl_says " to unfold it"]
      | _ => hypothesis (Message.of_ident x)
      end
  | _ => not_a_definition c
  end.

(* After [&] the name is read without it, so a global of the same name is
 * what the term finds; the local one is then looked up by that name.
 *)
Ltac2 definition (d : unit option * (unit -> constr)) : Std.reference * message :=
  match d with
  | (ampersand_written, read) =>
      Control.once_plus
        (fun () =>
          let c := head (read ()) in
          let found :=
            match ampersand_written with
            | Some _ =>
                match Constr.Unsafe.kind c with
                | Constr.Unsafe.Var x => local x (Message.of_ident x)
                | Constr.Unsafe.Constant k _ =>
                    local (List.last (Env.path (Std.ConstRef k))) (Message.of_constr c)
                | _ => not_a_definition c
                end
            | None => global c
            end in
          Control.zero (Simpl_definition found))
        (fun e =>
          match e with
          | Simpl_definition found => found
          | _ => Control.zero e
          end)
  end.

(* The places a step names, taken one at a time. *)
Ltac2 Type target := [ In_hypothesis (ident) | In_goal | Everywhere ].

Ltac2 same_body (a : constr option) (b : constr option) : bool :=
  match a with
  | Some a => match b with Some b => Constr.equal a b | None => false end
  | None => match b with Some _ => false | None => true end
  end.

Ltac2 same_entry (a : constr option * constr) (b : constr option * constr) : bool :=
  match a with
  | (body_a, type_a) =>
      match b with
      | (body_b, type_b) =>
          if same_body body_a body_b then Constr.equal type_a type_b else false
      end
  end.

Ltac2 same_context
  (a : (ident * constr option * constr) list) (b : (ident * constr option * constr) list) : bool :=
  List.for_all2
    (fun x y =>
      match x with
      | (_, body_x, type_x) =>
          match y with
          | (_, body_y, type_y) => same_entry (body_x, type_x) (body_y, type_y)
          end
      end)
    a b.

Ltac2 does_not_occur (shown : message) (place_name : message) :=
  refuse [simpl_says "simpl: "; shown; simpl_says " does not occur in "; place_name].

(* Rocq's own complaint about an <n> past the last occurrence names no
 * definition and no place, so it is replaced.
 *)
Ltac2 unfold_one
  (r : Std.reference) (occurrences : Std.occurrences) (place : Std.clause)
  (shown : message) (place_name : message) :=
  match occurrences with
  | Std.OnlyOccurrences [n] =>
      Control.once_plus
        (fun () => Std.unfold [(r, occurrences)] place)
        (fun _ =>
          refuse [simpl_says "simpl: "; shown; simpl_says " has no occurrence ";
                  Message.of_int n; simpl_says " in "; place_name])
  | _ => Std.unfold [(r, occurrences)] place
  end.

(* One definition in one place, all its occurrences or only the <n>th; the
 * place is compared before and after, and an unchanged one is refused.
 *)
Ltac2 unfold_in (d : Std.reference * message) (occurrences : Std.occurrences) (t : target) :=
  match d with
  | (r, shown) =>
      match t with
      | In_hypothesis h =>
          match entry h with
          | None =>
              refuse [simpl_says "simpl: "; Message.of_ident h;
                      simpl_says " is not in the context"]
          | Some before =>
              (unfold_one r occurrences (Place.hypotheses [h]) shown (Message.of_ident h);
               match entry h with
               | Some after =>
                   if same_entry before after
                   then does_not_occur shown (Message.of_ident h)
                   else ()
               | None => ()
               end)
          end
      | In_goal =>
          let before := Control.goal () in
          (unfold_one r occurrences Place.goal shown (simpl_says "the goal");
           if Constr.equal before (Control.goal ())
           then does_not_occur shown (simpl_says "the goal")
           else ())
      | Everywhere =>
          let hypotheses_before := Control.hyps () in
          let goal_before := Control.goal () in
          (Std.unfold [(r, occurrences)] Place.everywhere;
           if same_context hypotheses_before (Control.hyps ())
           then
             if Constr.equal goal_before (Control.goal ())
             then
               refuse [simpl_says "simpl: "; shown;
                       simpl_says " occurs nowhere, neither in the context nor in the goal"]
             else ()
           else ())
      end
  end.

Ltac2 unfold_all
  (ds : (unit option * (unit -> constr)) list) (occurrences : Std.occurrences)
  (targets : target list) :=
  Control.enter (fun () =>
    List.iter
      (fun d =>
        let d := definition d in
        List.iter (fun t => unfold_in d occurrences t) targets)
      ds).

Ltac2 no_place () :=
  refuse [simpl_says "simpl: a place must follow in, such as in |- * for the goal"].

Ltac2 targets
  (hypotheses : ident list option) (goal : unit option) (everywhere : unit option)
  : target list :=
  match everywhere with
  | Some _ =>
      match hypotheses with
      | None =>
          match goal with
          | None => [Everywhere]
          | Some _ => refuse [simpl_says "simpl: in * stands alone, with no hypothesis and no |- *"]
          end
      | Some _ => refuse [simpl_says "simpl: in * stands alone, with no hypothesis and no |- *"]
      end
  | None =>
      let named :=
        match hypotheses with
        | Some hs => List.map (fun h => In_hypothesis h) hs
        | None => []
        end in
      match goal with
      | Some _ => List.append named [In_goal]
      | None => match named with [] => no_place () | _ => named end
      end
  end.

(* Every form with definitions is one notation, whose place arrives in
 * pieces: notations opening with the same list of definitions cannot be
 * told apart by the parser. [simpl_definitions] rebuilds the place and
 * refuses a combination that is none of the forms above.
 *)
Ltac2 simpl_definitions
  (ds : (unit option * (unit -> constr)) list) (n : int option)
  (hypotheses : (bool * ident) list option) (goal : unit option) (everywhere : unit option) :=
  let hypotheses :=
    match hypotheses with
    | Some hs => Some (Local.context_idents "simpl" hs)
    | None => None
    end in
  let places := targets hypotheses goal everywhere in
  match n with
  | None => unfold_all ds Std.AllOccurrences places
  | Some n =>
      match ds with
      | [_] =>
          match places with
          | [In_hypothesis _] => unfold_all ds (Std.OnlyOccurrences [n]) places
          | [In_goal] => unfold_all ds (Std.OnlyOccurrences [n]) places
          | _ => refuse [simpl_says "simpl: at <n> acts in one hypothesis or in |- *"]
          end
      | _ => refuse [simpl_says "simpl: at <n> takes one definition"]
      end
  end.

(* Each hypothesis named, and the goal when [|- *] is, is compared before
 * and after, and one [simpl] leaves unchanged is refused.
 *)
Ltac2 reduce (hypotheses : ident list) (goal : bool) :=
  Control.enter (fun () =>
    let before :=
      List.map
        (fun h =>
          match entry h with
          | Some e => (h, e)
          | None =>
              refuse [simpl_says "simpl: "; Message.of_ident h;
                      simpl_says " is not in the context"]
          end)
        hypotheses in
    let goal_before := Control.goal () in
    let place :=
      if goal
      then (match hypotheses with [] => Place.goal | _ => Place.hypotheses_and_goal hypotheses end)
      else Place.hypotheses hypotheses in
    Std.simpl RedFlags.all None place;
    List.iter
      (fun p =>
        match p with
        | (h, e) =>
            match entry h with
            | Some after =>
                if same_entry e after
                then refuse [simpl_says "simpl: "; Message.of_ident h;
                             simpl_says " has nothing to reduce"]
                else ()
            | None => ()
            end
        end)
      before;
    if goal
    then
      (if Constr.equal goal_before (Control.goal ())
       then refuse [simpl_says "simpl: the goal has nothing to reduce"]
       else ())
    else ()).

Ltac2 reduce_everywhere () :=
  Control.enter (fun () =>
    let hypotheses_before := Control.hyps () in
    let goal_before := Control.goal () in
    Std.simpl RedFlags.all None Place.everywhere;
    if same_context hypotheses_before (Control.hyps ())
    then
      if Constr.equal goal_before (Control.goal ())
      then refuse [simpl_says "simpl: nothing to reduce, neither in the context nor in the goal"]
      else ()
    else ()).

Ltac2 Notation "simpl" ds(list1(seq(opt("&"), thunk(open_constr)), ","))
  n(opt(seq("at", tactic(0)))) "in"
  hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*")) :=
  simpl_definitions ds n hypotheses goal everywhere.

Ltac2 Notation "simpl" "in" hypotheses(list1(context_name, ",")) :=
  reduce (Local.context_idents "simpl" hypotheses) false.

Ltac2 Notation "simpl" "in" hypotheses(list1(context_name, ",")) "|-" "*" :=
  reduce (Local.context_idents "simpl" hypotheses) true.

Ltac2 Notation "simpl" "in" "|-" "*" :=
  reduce [] true.

Ltac2 Notation "simpl" "in" "*" :=
  reduce_everywhere ().

(* <H> cast to its type as [simpl in] reduces it, so that whatever reads the
 * type of the term, [let proof] or [leibniz], meets the reduced one.
 *)
Ltac2 simplified (h : constr) : constr :=
  let t := Constr.type h in
  let reduced := Std.eval_simpl RedFlags.all None t in
  if Constr.equal t reduced
  then refuse [simpl_says "simpl: "; Message.of_constr h; simpl_says " has nothing to reduce"]
  else constr:($h : $reduced).

Notation "'simpl' H" :=
  (ltac2:(Control.refine (fun () => simplified constr:($preterm:H))))
  (at level 10, H at next level, only parsing).
