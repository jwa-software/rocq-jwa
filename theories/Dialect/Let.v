(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Place.
From Ltac2 Require Constr Control Fresh Ident Int List Message Std.

(* let <x> := <e>                           pose (<x> := <e>)
 * let <x> : <T> := <e>                     pose (<x> : <T> := <e>)
 * let <x> := <e> in <places>               set (<x> := <e>) in <places>
 * let <x> : <T> := <e> in <places>         set (<x> : <T> := <e>) in <places>
 * let <x> := <e> at <n> in <H>             set (<x> := <e>) in <H> at <n>
 * let <x> := <e> at <n> in |- *            set (<x> := <e>) in |- * at <n>
 * let &<x> in <places>                     fold <x> in <places>
 * let proof <p> := <e>                     pose proof (<e>) as <p>
 * let proof <p> : <T> := <e>               pose proof (<e> : <T>) as <p>
 *
 * [:=] reads "is defined as", as in [Definition]: the binding is neither an
 * equation to be proved nor an assignment. [let] names <e> as a local
 * definition <x>, whose body stays visible; [let proof] adds <e> as a
 * hypothesis, its type alone, named by <p> or destructured by it.
 *
 * With [in], [let] also writes <x> for each occurrence of <e> in the places
 * named, the four of [simpl]: [in &h1, &h2], [in &h1 |- *], [in |- *],
 * [in *]. It fails when <e> does not occur in a hypothesis named, in the
 * goal when [|- *] is named, or anywhere under [in *]. With [at <n>], typed
 * or not, only the <n>th occurrence of <e>, counting from one, is written
 * <x>, in one hypothesis or in the goal; it fails when there is none.
 *
 * [let &<x> in <places>] does the same for a local definition <x> already
 * in the context: its body, as written, becomes <x> in the places named,
 * a hypothesis's body included. Refused: an <x> that is no definition, a
 * place where the body does not occur, <x> itself, and a hypothesis that
 * stands before <x>, which cannot name it; [in *] passes over those two.
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

Ltac2 let_refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

(* Rocq's own [Not convertible.] names neither the value nor the types, so
 * it is replaced. <e> is the value as the step wrote it; <x> holds it, under
 * a fresh name when the step shadows one.
 *)
Ltac2 retype (who : string) (e : constr) (x : ident) (t : constr) :=
  let before := Constr.type (Control.hyp x) in
  Control.once_plus
    (fun () => Std.change None (fun _ => t) (type_of x))
    (fun _ =>
      let_refuse [Message.of_string who; Message.of_string ": "; Message.of_constr e;
                  Message.of_string " has type "; Message.of_constr before;
                  Message.of_string ", which is not convertible with "; Message.of_constr t]).

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
    then retype "let" e x t
    else (let y := Fresh.in_goal x in Std.pose (Some y) e; retype "let" e y t; shadow_with x y)
  else (Std.pose (Some x) e; retype "let" e x t).

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
    then (retype "let proof" e h t; drop_body h)
    else (let y := Fresh.in_goal h in pose_proof constr:($e : $t) y; shadow_with h y)
  else pose_proof constr:($e : $t) h.

(* <T> and <e> arrive unread, so that [Local.checked] can read them twice. *)
Ltac2 typed_proof (who : string) (t : unit -> constr) (e : unit -> constr) : constr :=
  let t := Local.checked who t in
  let e := Local.checked who e in
  constr:($e : $t).

(* The body and the type of a name of the context, [None] when it is not
 * there.
 *)
Ltac2 entry (x : ident) : (constr option * constr) option :=
  match List.find_opt (fun h => match h with (y, _, _) => Ident.equal x y end)
          (Control.hyps ()) with
  | Some h => match h with (_, body, type) => Some (body, type) end
  | None => None
  end.

Ltac2 same_body (a : constr option) (b : constr option) : bool :=
  match a with
  | Some a => match b with Some b => Constr.equal a b | None => false end
  | None => match b with Some _ => false | None => true end
  end.

Ltac2 same_entry (a : (constr option * constr) option) (b : (constr option * constr) option)
  : bool :=
  match a with
  | Some (body_a, type_a) =>
      match b with
      | Some (body_b, type_b) =>
          if same_body body_a body_b then Constr.equal type_a type_b else false
      | None => false
      end
  | None => match b with Some _ => false | None => true end
  end.

(* The places of [let ... in], from the pieces the notation reads: the
 * hypotheses named, whether the goal is named, whether [*] is.
 *)
Ltac2 let_places
  (hypotheses : (bool * ident) list option) (goal : unit option) (everywhere : unit option)
  : ident list * bool * bool :=
  let hs :=
    match hypotheses with
    | Some hs => Local.context_idents "let" hs
    | None => []
    end in
  let goal := match goal with Some _ => true | None => false end in
  match everywhere with
  | Some _ =>
      match hs with
      | [] =>
          if goal
          then let_refuse [Message.of_string "let: in * stands alone, with no hypothesis and no |- *"]
          else ([], false, true)
      | _ => let_refuse [Message.of_string "let: in * stands alone, with no hypothesis and no |- *"]
      end
  | None =>
      match hs with
      | [] =>
          if goal
          then ([], true, false)
          else let_refuse [Message.of_string "let: a place must follow in, such as in |- * for the goal"]
      | _ => (hs, goal, false)
      end
  end.

(* [set_under y] sets the value <e> under the name [y]; [x] is shadowed by
 * it as [let] does.
 *)
Ltac2 set_definition
  (x : ident) (e : constr) (set_under : ident -> unit) (typed : constr option) :=
  let bind y :=
    (set_under y;
     match typed with Some t => retype "let" e y t | None => () end) in
  if is_in_context x
  then (let y := Fresh.in_goal x in bind y; shadow_with x y)
  else bind x.

(* The places are compared before and after, and one left unchanged is
 * refused.
 *)
Ltac2 let_in
  (x : ident) (e : constr) (typed : constr option) (places : ident list * bool * bool) :=
  match places with
  | (hs, goal, everywhere) =>
      (List.iter
        (fun h =>
          match entry h with
          | None =>
              let_refuse [Message.of_string "let: "; Message.of_ident h;
                          Message.of_string " is not in the context"]
          | Some _ => ()
          end)
        hs;
      let place :=
        if everywhere
        then Place.everywhere
        else if goal
        then (match hs with [] => Place.goal | _ => Place.hypotheses_and_goal hs end)
        else Place.hypotheses hs in
      let before := List.map (fun h => (h, entry h)) hs in
      let context_before := Control.hyps () in
      let goal_before := Control.goal () in
      set_definition x e (fun y => Std.set false (fun () => (Some y, e)) place) typed;
      let does_not_occur place_name :=
        let_refuse [Message.of_string "let: "; Message.of_constr e;
                    Message.of_string " does not occur in "; place_name] in
      if everywhere
      then
        (if Constr.equal goal_before (Control.goal ())
         then
           if List.for_all
                (fun h => match h with (y, body, type) => same_entry (Some (body, type)) (entry y) end)
                context_before
           then
             let_refuse [Message.of_string "let: "; Message.of_constr e;
                         Message.of_string " occurs nowhere, neither in the context nor in the goal"]
           else ()
         else ())
      else
        (List.iter
           (fun p =>
             match p with
             | (h, entry_before) =>
                 if same_entry entry_before (entry h)
                 then does_not_occur (Message.of_ident h)
                 else ()
             end)
           before;
         if goal
         then
           (if Constr.equal goal_before (Control.goal ())
            then does_not_occur (Message.of_string "the goal")
            else ())
         else ()))
  end.

Ltac2 hypothesis_at (h : ident) (n : int) : Std.clause :=
  { Std.on_hyps := Some [(h, Std.OnlyOccurrences [n], Std.InHyp)];
    Std.on_concl := Std.NoOccurrences }.

Ltac2 goal_at (n : int) : Std.clause :=
  { Std.on_hyps := Some []; Std.on_concl := Std.OnlyOccurrences [n] }.

(* Rocq's own complaint about an <n> past the last occurrence names neither
 * <e> nor the place, so it is replaced; a place left unchanged gets the
 * same message.
 *)
Ltac2 let_at
  (x : ident) (e : constr) (typed : constr option) (n : int)
  (places : ident list * bool * bool) :=
  let no_occurrence place_name :=
    let_refuse [Message.of_string "let: "; Message.of_constr e;
                Message.of_string " has no occurrence "; Message.of_int n;
                Message.of_string " in "; place_name] in
  let set_at place place_name y :=
    Control.once_plus
      (fun () => Std.set false (fun () => (Some y, e)) place)
      (fun _ => no_occurrence place_name) in
  let one_place () :=
    let_refuse [Message.of_string "let: at <n> acts in one hypothesis or in |- *"] in
  if Int.lt n 1
  then
    let_refuse [Message.of_string "let: at "; Message.of_int n;
                Message.of_string " names no occurrence, since they count from 1"]
  else
    match places with
    | (hs, goal, everywhere) =>
        if everywhere
        then one_place ()
        else
          match hs with
          | [h] =>
              if goal
              then one_place ()
              else
                match entry h with
                | None =>
                    let_refuse [Message.of_string "let: "; Message.of_ident h;
                                Message.of_string " is not in the context"]
                | Some before =>
                    (set_definition x e (set_at (hypothesis_at h n) (Message.of_ident h)) typed;
                     if same_entry (Some before) (entry h)
                     then no_occurrence (Message.of_ident h)
                     else ())
                end
          | [] =>
              let before := Control.goal () in
              (set_definition x e (set_at (goal_at n) (Message.of_string "the goal")) typed;
               if Constr.equal before (Control.goal ())
               then no_occurrence (Message.of_string "the goal")
               else ())
          | _ => one_place ()
          end
    end.

(* <c> with every <body> in it written <name>. <body> is closed, so no
 * occurrence of it mentions a variable bound inside <c>.
 *)
Ltac2 rec fold_occurrences (body : constr) (name : constr) (c : constr) : constr :=
  if Constr.equal c body
  then name
  else Constr.Unsafe.map (fold_occurrences body name) c.

(* Whether [h] stands before [x] in the context. *)
Ltac2 before (h : ident) (x : ident) : bool :=
  let rec scan hyps :=
    match hyps with
    | [] => false
    | y :: rest =>
        match y with
        | (y, _, _) =>
            if Ident.equal y h then true
            else if Ident.equal y x then false
            else scan rest
        end
    end in
  scan (Control.hyps ()).

(* The body of [x], as [let &x in ...] folds it. *)
Ltac2 fold_body (x : ident) : constr :=
  match entry x with
  | Some (Some body, _) => body
  | Some (None, _) =>
      let_refuse [Message.of_string "let: "; Message.of_ident x;
                  Message.of_string " is a hypothesis, not a definition; it has nothing to fold"]
  | None =>
      let_refuse [Message.of_string "let: "; Message.of_ident x;
                  Message.of_string " is not in the context"]
  end.

(* The folding in [h], type and body; [false] when the body of [x] occurs
 * in neither.
 *)
Ltac2 fold_in_hypothesis (x : ident) (body : constr) (h : ident) : bool :=
  match entry h with
  | Some (value, type) =>
      let name := Control.hyp x in
      let new_type := fold_occurrences body name type in
      let type_changed := if Constr.equal new_type type then false else true in
      let value_changed :=
        match value with
        | Some v =>
            let new_value := fold_occurrences body name v in
            if Constr.equal new_value v
            then false
            else (Std.change None (fun _ => new_value) (value_of h); true)
        | None => false
        end in
      if type_changed
      then (Std.change None (fun _ => new_type) (type_of h); true)
      else value_changed
  | None => false
  end.

Ltac2 fold_in_goal (x : ident) (body : constr) : bool :=
  let goal := Control.goal () in
  let new_goal := fold_occurrences body (Control.hyp x) goal in
  if Constr.equal new_goal goal
  then false
  else (Std.change None (fun _ => new_goal) Place.goal; true).

Ltac2 let_fold (x : ident) (places : ident list * bool * bool) :=
  let body := fold_body x in
  let does_not_occur place_name :=
    let_refuse [Message.of_string "let: "; Message.of_constr body;
                Message.of_string " does not occur in "; place_name] in
  match places with
  | (hs, goal, everywhere) =>
      if everywhere
      then
        let hypotheses_changed :=
          List.fold_left
            (fun acc y =>
              match y with
              | (h, _, _) =>
                  if Ident.equal h x then acc
                  else if before h x then acc
                  else if fold_in_hypothesis x body h then true
                  else acc
              end)
            false (Control.hyps ()) in
        let goal_changed := fold_in_goal x body in
        if hypotheses_changed then ()
        else if goal_changed then ()
        else
          let_refuse [Message.of_string "let: "; Message.of_constr body;
                      Message.of_string " occurs neither in the goal nor in a hypothesis after ";
                      Message.of_ident x]
      else
        (List.iter
           (fun h =>
             match entry h with
             | None =>
                 let_refuse [Message.of_string "let: "; Message.of_ident h;
                             Message.of_string " is not in the context"]
             | Some _ =>
                 if Ident.equal h x
                 then
                   let_refuse [Message.of_string "let: "; Message.of_ident x;
                               Message.of_string " cannot be folded into itself"]
                 else if before h x
                 then
                   let_refuse [Message.of_string "let: "; Message.of_ident h;
                               Message.of_string " stands before "; Message.of_ident x;
                               Message.of_string " in the context, so it cannot name it"]
                 else if fold_in_hypothesis x body h
                 then ()
                 else does_not_occur (Message.of_ident h)
             end)
           hs;
         if goal
         then (if fold_in_goal x body then () else does_not_occur (Message.of_string "the goal"))
         else ())
  end.

(* The intro-pattern forms are declared before the name forms: of two rules
 * that both accept a bare name, the later one is tried first, and a name
 * must reach the helpers that know how to shadow.
 *)
Ltac2 Notation "let" "proof" p(intropattern) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () =>
    Std.specialize (Local.checked "let proof" e, Std.NoBindings) (Some p)).

Ltac2 Notation "let" "proof" p(intropattern) ":" t(thunk(lconstr)) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () =>
    Std.specialize (typed_proof "let proof" t e, Std.NoBindings) (Some p)).

Ltac2 Notation "let" x(ident) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () => let_definition x (Local.checked "let" e)).

Ltac2 Notation "let" x(ident) ":" t(thunk(lconstr)) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () =>
    let_definition_typed x (Local.checked "let" t) (Local.checked "let" e)).

Ltac2 Notation "let" x(ident) ":=" e(thunk(lconstr))
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*"))
  : 5 :=
  Control.enter (fun () =>
    let_in x (Local.checked "let" e) None (let_places hypotheses goal everywhere)).

Ltac2 Notation "let" x(ident) ":" t(thunk(lconstr)) ":=" e(thunk(lconstr))
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*"))
  : 5 :=
  Control.enter (fun () =>
    let_in x (Local.checked "let" e) (Some (Local.checked "let" t))
      (let_places hypotheses goal everywhere)).

Ltac2 Notation "let" x(ident) ":=" e(thunk(lconstr)) "at" n(tactic(0))
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*"))
  : 5 :=
  Control.enter (fun () =>
    let_at x (Local.checked "let" e) None n (let_places hypotheses goal everywhere)).

Ltac2 Notation "let" x(ident) ":" t(thunk(lconstr)) ":=" e(thunk(lconstr)) "at" n(tactic(0))
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*"))
  : 5 :=
  Control.enter (fun () =>
    let_at x (Local.checked "let" e) (Some (Local.checked "let" t)) n
      (let_places hypotheses goal everywhere)).

Ltac2 Notation "let" "&" x(ident)
  "in" hypotheses(opt(list1(context_name, ","))) goal(opt(seq("|-", "*"))) everywhere(opt("*"))
  : 5 :=
  Control.enter (fun () => let_fold x (let_places hypotheses goal everywhere)).

Ltac2 Notation "let" "proof" h(ident) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () => let_proof h (Local.checked "let proof" e)).

Ltac2 Notation "let" "proof" h(ident) ":" t(thunk(lconstr)) ":=" e(thunk(lconstr)) : 5 :=
  Control.enter (fun () =>
    let_proof_typed h (Local.checked "let proof" t) (Local.checked "let proof" e)).
