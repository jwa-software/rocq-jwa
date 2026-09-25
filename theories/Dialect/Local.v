(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Char Constr Control Fresh Ident Int List Message Std String.

(* A name of the context is written [&h] in every tactic of this library: a
 * hypothesis, a local definition and a type introduced by [intros] ([&A])
 * alike. A global is written bare, and a name being introduced takes no [&]:
 * [intro a], [let proof x], [match h with | a b end], a binder of [fun].
 *
 * While [checking] is [NonStrict], a bare name of the context is accepted
 * too; [Ltac2 Set Local.checking := Strict] makes every tactic refuse it with
 * [<tactic>: h is in the context; write &h]. The one exception is [facto],
 * the closing proof of [ipso facto], accepted bare in both modes.
 *
 * A name a notation reads itself, as in [in &h] or [rm &a &b], is a
 * [context_name]. A term is checked by reading it once more with every name
 * of the context renamed: a bare name then fails as an unknown variable, and
 * an [&h] as an unknown hypothesis. Rocq raises both as the same exception,
 * so they are told apart by the words of their messages, those of Rocq 9.2.
 *)
Ltac2 Type mode := [ NonStrict | Strict ].

Ltac2 mutable checking := NonStrict.

Ltac2 is_strict () : bool :=
  match checking with
  | Strict => true
  | NonStrict => false
  end.

Ltac2 Custom Entry context_name.

Ltac2 Notation "&" x(ident) : context_name(0) := (true, x).

Ltac2 Notation x(ident) : context_name(0) := (false, x).

Ltac2 local_refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

Ltac2 write_ampersand (who : string) (x : ident) :=
  local_refuse [Message.of_string who; Message.of_string ": "; Message.of_ident x;
                Message.of_string " is in the context; write &"; Message.of_ident x].

Ltac2 is_facto (x : ident) : bool := Ident.equal x @facto.

(* A [context_name] as the ident it names. *)
Ltac2 context_ident (who : string) (x : bool * ident) : ident :=
  match x with
  | (marked, h) =>
      if marked then h
      else if is_facto h then h
      else if is_strict () then write_ampersand who h
      else h
  end.

Ltac2 context_idents (who : string) (xs : (bool * ident) list) : ident list :=
  List.map (context_ident who) xs.

Ltac2 local_in_context (x : ident) : bool :=
  List.exist (fun h => match h with (y, _, _) => Ident.equal x y end) (Control.hyps ()).

Ltac2 hide_all_but (kept : ident list) :=
  List.iter
    (fun h =>
      match h with
      | (x, _, _) =>
          if List.exist (Ident.equal x) kept
          then ()
          else Std.rename [(x, Fresh.fresh (Fresh.Free.of_goal ()) @hidden)]
      end)
    (Control.hyps ()).

(* Letters, digits, [_] and ['], the characters of a name. *)
Ltac2 is_name_char (c : char) : bool :=
  let n := Char.to_int c in
  if Int.le 97 n then Int.le n 122
  else if Int.le 65 n then (if Int.le n 90 then true else Int.equal n 95)
  else if Int.le 48 n then Int.le n 57
  else Int.equal n 39.

Ltac2 is_blank (c : char) : bool :=
  let n := Char.to_int c in
  if Int.equal n 32 then true else Int.equal n 10.

Ltac2 rec index_from (s : string) (pattern : string) (i : int) : int :=
  if Int.lt (String.length s) (Int.add i (String.length pattern)) then -1
  else if String.equal (String.sub s i (String.length pattern)) pattern then i
  else index_from s pattern (Int.add i 1).

Ltac2 rec skip_while (keep : char -> bool) (s : string) (i : int) : int :=
  if Int.lt i (String.length s)
  then (if keep (String.get s i) then skip_while keep s (Int.add i 1) else i)
  else i.

(* The name that follows [pattern] in [s], if any. *)
Ltac2 name_after (s : string) (pattern : string) : ident option :=
  let i := index_from s pattern 0 in
  if Int.lt i 0
  then None
  else
    let start := skip_while is_blank s (Int.add i (String.length pattern)) in
    let stop := skip_while is_name_char s start in
    if Int.equal start stop
    then None
    else Ident.of_string (String.sub s start (Int.sub stop start)).

Ltac2 Type exn ::= [ Local_read ].

Ltac2 Type verdict := [ Read | Bare (ident) | Marked (ident) | Unknown ].

(* One reading with every name but [kept] hidden; always undone. *)
Ltac2 attempt (read : unit -> constr) (kept : ident list) : verdict :=
  Control.once_plus
    (fun () => (hide_all_but kept; let _ := read () in Control.zero Local_read))
    (fun e =>
      match e with
      | Local_read => Read
      | _ =>
          let text := Message.to_string (Message.of_exn e) in
          match name_after text "The variable" with
          | Some x => if local_in_context x then Bare x else Unknown
          | None =>
              match name_after text "Hypothesis """ with
              | Some x => if local_in_context x then Marked x else Unknown
              | None => Unknown
              end
          end
      end).

(* An [&x] met is kept visible and the reading tried again, until it goes
 * through or a bare name of the context stops it.
 *)
Ltac2 rec hunt (read : unit -> constr) (kept : ident list) : ident option :=
  match attempt read kept with
  | Bare x => Some x
  | Marked x =>
      if List.exist (Ident.equal x) kept then None else hunt read (x :: kept)
  | _ => None
  end.

(* Under [Strict], refuse a term that names the context bare; [facto] is kept
 * visible from the start.
 *)
Ltac2 check (who : string) (read : unit -> constr) :=
  if is_strict ()
  then
    match hunt read [@facto] with
    | Some x => write_ampersand who x
    | None => ()
    end
  else ().

Ltac2 checked (who : string) (read : unit -> constr) : constr :=
  (check who read; read ()).

Ltac2 check_preterm (who : string) (p : preterm) :=
  check who (fun () => open_constr:($preterm:p)).

Ltac2 check_preterms (who : string) (ps : preterm list) :=
  List.iter (check_preterm who) ps.

(* A term built from the preterms of a tactic, as [open_constr:] reads it:
 * the whole application typed at once, so one premise may fix another's
 * implicit arguments. Typeclass inference then runs as well, which
 * [open_constr:] leaves out; without it an instance argument such as
 * [{C : Comparable compare lt}] stays a hole, and every argument it fixes
 * with it.
 *)
Ltac2 elaborate (p : preterm) : constr :=
  Constr.Pretype.pretype
    Constr.Pretype.Flags.open_constr_flags_with_tc
    Constr.Pretype.expected_without_type_constraint
    p.
