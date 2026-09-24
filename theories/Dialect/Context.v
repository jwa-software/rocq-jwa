(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Control Ident List Message Std.

(* Tidying the context:
 *
 *   mv <H> <name>          rename <H> into <name>
 *   rm <H1> ... <Hn>       clear <H1> ... <Hn>
 *
 * [mv] takes exactly the old name and then the new one. It fails when <H>
 * is not in the context, and it never overwrites: a <name> already in the
 * context is an error, and nothing changes. [rm] takes one name or more,
 * space-separated, and fails without clearing any of them when one is not
 * in the context, or when another hypothesis or the goal still depends on
 * one.
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

Ltac2 remove (hypotheses : ident list) :=
  Control.enter (fun () =>
    (List.iter
       (fun h =>
         if in_context h
         then ()
         else refuse [Message.of_string "rm: "; Message.of_ident h;
                      Message.of_string " is not in the context"])
       hypotheses;
     Std.clear hypotheses)).

Ltac2 Notation "mv" h(ident) name(ident) :=
  rename h name.

Ltac2 Notation "rm" hypotheses(list1(ident)) :=
  remove hypotheses.
