(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From Ltac2 Require Control List Message Std.

(* match <H> with end                          destruct <H>
 * match <H> with | <b1> | ... | <bn> end      destruct <H> as [<b1> | ... | <bn>]
 * match <H> with end |- <E>                   destruct <H> eqn:<E>
 * match <H> with | <b1> | ... end |- <E>      destruct <H> as [...] eqn:<E>
 *
 * Case analysis on <H>, one goal per constructor of its type; the proof term
 * built is a [match] on <H>. The branch <bi> names the arguments of the i-th
 * constructor in order, each a name or [_], and may be empty; [with end]
 * leaves the names to Rocq. [|- <E>] adds to each goal the equation <E>
 * between <H> and that goal's constructor. A branch takes one constructor
 * apart and no more: an argument to be taken apart in turn is named, then
 * matched again.
 *
 * <H> is a [constr], a term at level 8, so an application is parenthesised.
 * Declared at level 5 beside Ltac2's own [match <v> with <branches> end],
 * which it shadows: in a proof, and in any file importing this one, Ltac2's
 * [match] no longer parses.
 *)

(* The helpers come first: they use Ltac2's [match], which the notation below
 * takes over.
 *)

Ltac2 name_or_wildcard (p : Std.intro_pattern) : Std.intro_pattern :=
  match p with
  | Std.IntroNaming (Std.IntroIdentifier _) => p
  | Std.IntroAction Std.IntroWildcard => p
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (Message.of_string
                    "match: a branch takes names and _ only; name the part and match it again")))
  end.

Ltac2 match_destruct
  (h : unit -> constr) (e : ident option) (branches : Std.intro_pattern list list) :=
  let branches := List.map (List.map name_or_wildcard) branches in
  let pattern :=
    match branches with
    | [] => None
    | _ => Some (Std.IntroOrPattern branches)
    end in
  let equation :=
    match e with
    | Some e => Some (Std.IntroIdentifier e)
    | None => None
    end in
  Control.enter (fun () =>
    let h := Local.checked "match" h in
    Std.destruct false
      [{ Std.indcl_arg := Std.ElimOnConstr (fun () => (h, Std.NoBindings));
         Std.indcl_eqn := equation;
         Std.indcl_as := pattern;
         Std.indcl_in := None }]
      None).

Ltac2 Notation "match" h(thunk(constr)) "with"
  branches(list0(seq("|", list0(intropattern)))) "end" e(opt(seq("|-", ident))) : 5 :=
  match_destruct h e branches.
