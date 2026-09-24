(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Constr Control Ident Int List Message Ref Std.

(* Tidying the context:
 *
 *   mv <H> <name>          rename <H> into <name>
 *   rm <H1> ... <Hn>       clear <H1> ... <Hn>
 *   rm -f <H1> ... <Hn>    clear those of <H1> ... <Hn> nothing depends on
 *   rm -r <H1> ... <Hn>    clear <H1> ... <Hn> and every hypothesis that
 *                          depends on one, as [clear dependent] does
 *
 * [mv] takes exactly the old name and then the new one. It fails when <H>
 * is not in the context, and it never overwrites: a <name> already in the
 * context is an error, and nothing changes. [rm] takes one name or more,
 * space-separated, and fails without clearing any of them when one is not
 * in the context, or when another hypothesis or the goal still depends on
 * one. [rm -f] leaves in place, without complaint, a name something still
 * depends on; [rm -r] clears with it every hypothesis that depends on it,
 * and fails when the goal does. Both refuse a name not in the context.
 *)

Ltac2 refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

Ltac2 in_context (x : ident) : bool :=
  List.exist (fun h => match h with (y, _, _) => Ident.equal x y end) (Control.hyps ()).

Ltac2 rename (h : ident) (name : ident) :=
  Control.enter (fun () =>
    if in_context h
    then
      if in_context name
      then
        refuse [Message.of_string "mv: "; Message.of_ident name;
                Message.of_string " is already in the context, and mv never overwrites"]
      else Std.rename [(h, name)]
    else refuse [Message.of_string "mv: "; Message.of_ident h;
                 Message.of_string " is not in the context"]).

Ltac2 all_in_context (hypotheses : ident list) :=
  List.iter
    (fun h =>
      if in_context h
      then ()
      else refuse [Message.of_string "rm: "; Message.of_ident h;
                   Message.of_string " is not in the context"])
    hypotheses.

Ltac2 remove (hypotheses : ident list) :=
  Control.enter (fun () =>
    (all_in_context hypotheses;
     Std.clear hypotheses)).

Ltac2 try_clear (h : ident) : bool :=
  Control.once_plus (fun () => (Std.clear [h]; true)) (fun _ => false).

(* A name cleared late may free one tried early, so the names left are
 * tried again for as long as some are cleared.
 *)
Ltac2 rec clear_what_can (hypotheses : ident list) :=
  let left := List.filter (fun h => if try_clear h then false else true) hypotheses in
  if Int.lt (List.length left) (List.length hypotheses) then clear_what_can left else ().

Ltac2 remove_force (hypotheses : ident list) :=
  Control.enter (fun () =>
    (all_in_context hypotheses;
     clear_what_can hypotheses)).

Ltac2 rec mark (x : ident) (found : bool Ref.ref) (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var y => if Ident.equal x y then Ref.set found true else ()
  | _ => Constr.Unsafe.iter (mark x found) c
  end.

Ltac2 occurs (x : ident) (c : constr) : bool :=
  let found := Ref.ref false in
  (mark x found c; Ref.get found).

Ltac2 mentions (xs : ident list) (c : constr) : bool :=
  List.exist (fun x => occurs x c) xs.

(* The context lists a hypothesis after everything it depends on, so one
 * pass in that order gathers the dependents of the names given.
 *)
Ltac2 with_dependents (hypotheses : ident list) : ident list :=
  List.fold_left
    (fun gathered h =>
      match h with
      | (y, body, type) =>
          if List.exist (Ident.equal y) gathered
          then gathered
          else
            let depends :=
              if mentions gathered type
              then true
              else match body with Some b => mentions gathered b | None => false end in
            if depends then List.append gathered [y] else gathered
      end)
    hypotheses (Control.hyps ()).

Ltac2 remove_recursive (hypotheses : ident list) :=
  Control.enter (fun () =>
    (all_in_context hypotheses;
     let gathered := with_dependents hypotheses in
     let goal := Control.goal () in
     match List.find_opt (fun x => occurs x goal) gathered with
     | Some x =>
         refuse [Message.of_string "rm -r: the goal depends on "; Message.of_ident x;
                 Message.of_string ", so it cannot be cleared"]
     | None => Std.clear gathered
     end)).

Ltac2 Notation "mv" h(ident) name(ident) :=
  rename h name.

Ltac2 Notation "rm" hypotheses(list1(ident)) :=
  remove hypotheses.

Ltac2 Notation "rm" "-" "f" hypotheses(list1(ident)) :=
  remove_force hypotheses.

Ltac2 Notation "rm" "-" "r" hypotheses(list1(ident)) :=
  remove_recursive hypotheses.
