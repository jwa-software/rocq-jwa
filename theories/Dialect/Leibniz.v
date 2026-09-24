(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Idem.
From jwa Require Import Dialect.Local.
From Ltac2 Require Array Bool Constr Control Fresh Ident Int List Message Std.

(* Leibniz's law, x = y, P x |- P y: what is equal may be put for what it
 * equals. Below, <e> is a proof of an equation and <hypotheses> a
 * comma-separated list of hypothesis names, one or more.
 *
 *   leibniz <e> in <hypotheses>                  rewrite <e> in <hypotheses>
 *   leibniz <e> in <hypotheses> |- *             rewrite <e> in <hypotheses> |- *
 *   leibniz <e> in |- *                          rewrite <e> in |- *
 *   leibniz <e> in *                             rewrite <e> in *
 *
 * There is no bare [leibniz <e>]: the place is always written, the goal as
 * [in |- *]. Each of the four also takes [->] or [<-] before <e>: with
 * <e> : <a> = <b>, [->] (the default) puts <b> for every <a>, [<-] puts <a>
 * for every <b>. [at] and [by] are not taken.
 *
 * <e> may also be a comma-separated list, each equation with its own [->]
 * or [<-]: [leibniz <e1>, <- <e2> in <places>] is [leibniz <e1> in <places>]
 * followed by [leibniz <- <e2> in <places>], each checked as if written
 * alone.
 *
 * <e> is an equation given whole, never a law still waiting for arguments:
 * [leibniz (addition.commutativity m n) in |- *], so the step shows which
 * equation it uses. The side replaced is found as written, nothing reduced.
 * Refused: a place it does not occur in, one that is not a proposition, and
 * a hypothesis that is a local definition; [in *] passes over those and
 * fails only when nothing changes anywhere.
 *
 * The proof is built from Leibniz's law itself, proved where [=] is defined
 * and handed over with [Ltac2 Set]; Rocq's [rewrite] is not used.
 *)

(* [forall {A : Type} {x : A} {y : A} (P : A -> Prop) . x = y -> P x -> P y],
 * set by the file that proves it; until then every step is refused.
 *)
Ltac2 mutable law : unit -> constr option := fun () => None.

Ltac2 leibniz_refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

Ltac2 says (s : string) : message := Message.of_string s.

Ltac2 the_law () : constr :=
  match law () with
  | Some l => l
  | None => leibniz_refuse [says "leibniz: no equality is defined here yet"]
  end.

(* The type and the two sides of the equation <e> proves. *)
Ltac2 sides (e : constr) : constr * constr * constr :=
  let t := Constr.type e in
  let refuse_with rest :=
    leibniz_refuse [says "leibniz: "; Message.of_constr e; says " proves ";
                    Message.of_constr t; rest] in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App head args =>
      if Idem.is_equality head
      then
        if Int.equal (Array.length args) 3
        then (Array.get args 0, Array.get args 1, Array.get args 2)
        else refuse_with (says ", which is not an equation")
      else refuse_with (says ", which is not an equation")
  | Constr.Unsafe.Prod _ _ =>
      refuse_with
        (Message.concat (says ", a law still waiting for arguments; write (")
           (Message.concat (Message.of_constr e) (says " <arguments>)")))
  | _ => refuse_with (says ", which is not an equation")
  end.

(* <c>, <depth> binders below the top of a motive, with every <from> put
 * for the motive's own bound variable. <from> is closed, so no occurrence
 * of it mentions a variable bound inside <c>.
 *)
Ltac2 rec bind_occurrences (from : constr) (depth : int) (c : constr) : constr :=
  if Constr.equal c from
  then Constr.Unsafe.make (Constr.Unsafe.Rel (Int.add depth 1))
  else
    Constr.Unsafe.map_with_binders
      (fun d _ => Int.add d 1) (fun d c => bind_occurrences from d c) depth c.

Ltac2 is_proposition (t : constr) : bool :=
  Constr.equal (Constr.type t) 'Prop.

(* One rewriting, of the statement <t>: the motive [fun z : <ty> . ...],
 * with [z] for every <from>, and <t> with <to> put there instead; [None]
 * when <from> does not occur in <t>. [Std.eval_pattern] raises an error no
 * handler catches when the motive is not well typed, so the motive is
 * built by hand and checked by [well_typed].
 *)
Ltac2 rewritten (ty : constr) (from : constr) (to : constr) (t : constr)
  : (constr * constr) option :=
  let body := bind_occurrences from 0 t in
  if Constr.Unsafe.noccurn 1 body
  then None
  else
    Some (Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.make (Some @z) ty) body),
          Constr.Unsafe.substnl [to] 0 body).

(* A statement where some <from> cannot be told apart from the rest, such
 * as one a type depends on, gives a motive that is not well typed.
 *)
Ltac2 ill_typed (from : constr) (to : constr) (place : message) :=
  leibniz_refuse [says "leibniz: putting "; Message.of_constr to; says " for ";
                  Message.of_constr from; says " in "; place;
                  says " does not give a well-typed statement"].

Ltac2 well_typed (motive : constr) : bool :=
  match Constr.Unsafe.check motive with
  | Val _ => true
  | Err _ => false
  end.

(* A proof of <after> from a proof <p> of the statement <motive> <from>.
 * [->] applies the law directly; [<-] applies it to the motive
 * [fun z . motive z -> after], whose instance at <a> is the identity.
 *)
Ltac2 carry
  (forward : bool) (ty : constr) (a : constr) (b : constr) (e : constr)
  (motive : constr) (after : constr) (p : constr) : constr :=
  let l := the_law () in
  if forward
  then open_constr:($l $ty $a $b $motive $e $p : $after)
  else
    open_constr:($l $ty $a $b (fun z : $ty => forall (_ : $motive z), $after) $e
                    (fun w : $after => w) $p
                  : $after).

Ltac2 rec next_after (h : ident) (hyps : (ident * constr option * constr) list) : ident option :=
  match hyps with
  | [] => None
  | x :: rest =>
      match x with
      | (y, _, _) =>
          if Ident.equal y h
          then match rest with (z, _, _) :: _ => Some z | [] => None end
          else next_after h rest
      end
  end.

(* The new [h] goes back where the old one stood, unless its statement now
 * names something that stands later. [Std.MoveAfter n] puts it just above
 * [n] as the context is printed: Ltac2 counts from the other end.
 *)
Ltac2 replace_hypothesis (h : ident) (proof : constr) :=
  let next := next_after h (Control.hyps ()) in
  let y := Fresh.in_goal h in
  Std.specialize (proof, Std.NoBindings) (Some (Std.IntroNaming (Std.IntroIdentifier y)));
  Std.clear [h];
  Std.rename [(y, h)];
  match next with
  | Some n => Control.once_plus (fun () => Std.move h (Std.MoveAfter n)) (fun _ => ())
  | None => ()
  end.

(* The step as it applies to one hypothesis; [false] when <from> does not
 * occur in it.
 *)
Ltac2 in_hypothesis
  (forward : bool) (ty : constr) (a : constr) (b : constr) (e : constr) (h : ident) : bool :=
  let from := if forward then a else b in
  let to := if forward then b else a in
  let t := Constr.type (Control.hyp h) in
  match rewritten ty from to t with
  | Some (motive, after) =>
      if well_typed motive
      then (replace_hypothesis h (carry forward ty a b e motive after (Control.hyp h)); true)
      else ill_typed from to (Message.of_ident h)
  | None => false
  end.

(* The step as it applies to the goal: the goal becomes <after>, and the
 * old goal is proved from it by the law read the other way.
 *)
Ltac2 in_goal (forward : bool) (ty : constr) (a : constr) (b : constr) (e : constr) : bool :=
  let from := if forward then a else b in
  let to := if forward then b else a in
  let goal := Control.goal () in
  match rewritten ty from to goal with
  | Some (motive, after) =>
      if well_typed motive
      then
        (Control.refine (fun () =>
           let hole := open_constr:(_ : $after) in
           carry (Bool.neg forward) ty a b e motive goal hole);
         true)
      else ill_typed from to (says "the goal")
  | None => false
  end.

Ltac2 does_not_occur (from : constr) (place : message) :=
  leibniz_refuse [says "leibniz: "; Message.of_constr from; says " does not occur in "; place].

Ltac2 check_hypothesis (h : ident) :=
  match List.find_opt (fun x => match x with (y, _, _) => Ident.equal h y end)
          (Control.hyps ()) with
  | None => leibniz_refuse [says "leibniz: "; Message.of_ident h; says " is not in the context"]
  | Some (_, Some _, _) =>
      leibniz_refuse [says "leibniz: "; Message.of_ident h;
                      says " is a local definition, which leibniz does not rewrite"]
  | Some (_, None, t) =>
      if is_proposition t
      then ()
      else leibniz_refuse [says "leibniz: "; Message.of_ident h; says " is not a proposition"]
  end.

(* <hypotheses> named, then the goal when <goal> is [true]. *)
Ltac2 leibniz_named
  (orientation : Std.orientation option) (e : preterm) (hypotheses : ident list) (goal : bool) :=
  Control.enter (fun () =>
    Local.check_preterm "leibniz" e;
    let e := constr:($preterm:e) in
    let forward := match orientation with Some Std.RTL => false | _ => true end in
    match sides e with
    | (ty, a, b) =>
        let from := if forward then a else b in
        (List.iter
           (fun h =>
             check_hypothesis h;
             if in_hypothesis forward ty a b e h
             then ()
             else does_not_occur from (Message.of_ident h))
           hypotheses;
         if goal
         then
           if is_proposition (Control.goal ())
           then
             if in_goal forward ty a b e
             then ()
             else does_not_occur from (says "the goal")
           else leibniz_refuse [says "leibniz: the goal is not a proposition"]
         else ())
    end).

(* Every hypothesis that is a proposition, other than <e> itself, and the
 * goal; at least one must change.
 *)
Ltac2 leibniz_everywhere (orientation : Std.orientation option) (e : preterm) :=
  Control.enter (fun () =>
    Local.check_preterm "leibniz" e;
    let e := constr:($preterm:e) in
    let forward := match orientation with Some Std.RTL => false | _ => true end in
    match sides e with
    | (ty, a, b) =>
        let from := if forward then a else b in
        let is_e h := match Constr.Unsafe.kind e with
                      | Constr.Unsafe.Var x => Ident.equal x h
                      | _ => false
                      end in
        let changed :=
          List.fold_left
            (fun acc x =>
              match x with
              | (h, None, t) =>
                  if is_e h then acc
                  else if is_proposition t
                  then (if in_hypothesis forward ty a b e h then true else acc)
                  else acc
              | (_, Some _, _) => acc
              end)
            false (Control.hyps ()) in
        let goal_changed :=
          if is_proposition (Control.goal ()) then in_goal forward ty a b e else false in
        if changed then () else if goal_changed then ()
        else
          leibniz_refuse [says "leibniz: "; Message.of_constr from;
                          says " occurs nowhere, neither in the context nor in the goal"]
    end).

(* The place of a step, rebuilt from the pieces the notation reads: the
 * hypotheses and whether the goal is named, or [None] for [in *].
 *)
Ltac2 leibniz_place
  (hypotheses : (bool * ident) list option) (goal : unit option) (everywhere : unit option)
  : (ident list * bool) option :=
  let alone () :=
    leibniz_refuse [says "leibniz: in * stands alone, with no hypothesis and no |- *"] in
  match everywhere with
  | Some _ =>
      match hypotheses with
      | Some _ => alone ()
      | None => match goal with Some _ => alone () | None => None end
      end
  | None =>
      let hs :=
        match hypotheses with
        | Some hs => Local.context_idents "leibniz" hs
        | None => []
        end in
      let goal := match goal with Some _ => true | None => false end in
      match hs with
      | [] =>
          if goal
          then Some ([], true)
          else leibniz_refuse [says "leibniz: a place must follow in, such as in |- * for the goal"]
      | _ => Some (hs, goal)
      end
  end.

Ltac2 leibniz_steps
  (steps : (Std.orientation option * preterm) list) (place : (ident list * bool) option) :=
  List.iter
    (fun step =>
      match step with
      | (orientation, e) =>
          match place with
          | Some (hypotheses, goal) => leibniz_named orientation e hypotheses goal
          | None => leibniz_everywhere orientation e
          end
      end)
    steps.

(* One notation, whose place arrives in pieces: notations opening with the
 * same list of equations cannot be told apart by the parser.
 *)
Ltac2 Notation "leibniz" steps(list1(seq(orient, preterm), ","))
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*")) :=
  leibniz_steps steps (leibniz_place hypotheses goal everywhere).
