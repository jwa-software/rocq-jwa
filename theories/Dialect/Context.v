(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From Ltac2 Require Constr Control Ident Int List Message Ref Std.

(* Tidying the context:
 *
 *   mv <H> <name>          rename <H> into <name>
 *   rm <H1> ... <Hn>       clear <H1> ... <Hn>
 *   rm -f <H1> ... <Hn>    clear those of <H1> ... <Hn> nothing depends on
 *   rm -r <H1> ... <Hn>    clear <H1> ... <Hn> and every hypothesis that
 *                          depends on one, as [clear dependent] does
 *   extro <H>              put <H> back into the goal, the reverse of [intro]
 *   extros <H1> ... <Hn>   put <H1> ... <Hn> back, the reverse of [intros]
 *
 * [mv] takes exactly the old name and then the new one. It fails when <H>
 * is not in the context, and it never overwrites: a <name> already in the
 * context is an error, and nothing changes. [rm] takes one name or more,
 * space-separated, and fails without clearing any of them when one is not
 * in the context, or when another hypothesis or the goal still depends on
 * one. [rm -f] leaves in place, without complaint, a name something still
 * depends on; [rm -r] clears with it every hypothesis that depends on it,
 * and fails when the goal does. Both refuse a name not in the context.
 *
 * [extros a b] turns the goal G into [A -> B -> G], or [forall] where G
 * mentions them, so [intros a b] gives it back; a local definition returns
 * as [let]. Each name must be in the context and come after those it
 * depends on, and a hypothesis that depends on one of them must be named
 * too: nothing is put back that the line does not name.
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

Ltac2 names_message (xs : ident list) (prefix : string) : message :=
  List.fold_left
    (fun m x =>
       Message.concat m
         (Message.concat (Message.of_string " ")
            (Message.concat (Message.of_string prefix) (Message.of_ident x))))
    (Message.of_string "") xs.

Ltac2 remove (hypotheses : ident list) :=
  Control.enter (fun () =>
    (all_in_context hypotheses;
     let goal := Control.goal () in
     match List.find_opt (fun x => occurs x goal) hypotheses with
     | Some x =>
         refuse [Message.of_string "rm: the goal depends on "; Message.of_ident x;
                 Message.of_string ", so it cannot be cleared"]
     | None =>
         let left :=
           List.filter (fun y => if List.exist (Ident.equal y) hypotheses then false else true)
             (with_dependents hypotheses) in
         match left with
         | [] => Std.clear hypotheses
         | _ =>
             refuse [Message.of_string "rm:"; names_message left "";
                     Message.of_string " would be left depending on what is cleared; write rm";
                     names_message (with_dependents hypotheses) "&";
                     Message.of_string ", or rm -r"; names_message hypotheses "&"]
         end
     end)).

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

Ltac2 depends_on (h : ident) (x : ident) : bool :=
  match List.find_opt
          (fun d => match d with (y, _, _) => Ident.equal h y end)
          (Control.hyps ()) with
  | Some (_, body, type) =>
      if occurs x type then true
      else match body with Some b => occurs x b | None => false end
  | None => false
  end.

Ltac2 rec check_order (who : string) (xs : ident list) :=
  match xs with
  | [] => ()
  | x :: rest =>
      match List.find_opt (fun y => depends_on x y) rest with
      | Some y =>
          refuse [Message.of_string who; Message.of_string ": "; Message.of_ident x;
                  Message.of_string " depends on "; Message.of_ident y;
                  Message.of_string ", so "; Message.of_ident y;
                  Message.of_string " comes first"]
      | None => check_order who rest
      end
  end.

Ltac2 extro_names (who : string) (xs : ident list) :=
  Control.enter (fun () =>
    List.iter
      (fun x =>
         if in_context x then ()
         else refuse [Message.of_string who; Message.of_string ": "; Message.of_ident x;
                      Message.of_string " is not in the context"])
      xs;
    check_order who xs;
    let gathered := with_dependents xs in
    let left :=
      List.filter (fun y => if List.exist (Ident.equal y) xs then false else true) gathered in
    match left with
    | [] => Std.revert xs
    | _ =>
        refuse [Message.of_string who; Message.of_string ":";
                names_message left "";
                Message.of_string " would be left depending on what goes back; write extros";
                names_message gathered "&"]
    end).

Ltac2 Notation "mv" h(context_name) name(ident) :=
  rename (Local.context_ident "mv" h) name.

Ltac2 Notation "rm" hypotheses(list1(context_name)) :=
  remove (Local.context_idents "rm" hypotheses).

Ltac2 Notation "rm" "-" "f" hypotheses(list1(context_name)) :=
  remove_force (Local.context_idents "rm -f" hypotheses).

Ltac2 Notation "rm" "-" "r" hypotheses(list1(context_name)) :=
  remove_recursive (Local.context_idents "rm -r" hypotheses).

Ltac2 Notation "extro" h(context_name) :=
  extro_names "extro" [Local.context_ident "extro" h].

Ltac2 Notation "extros" hypotheses(list1(context_name)) :=
  extro_names "extros" (Local.context_idents "extros" hypotheses).
