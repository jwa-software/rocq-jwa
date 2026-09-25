(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Identity.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Import Notations.
From Ltac2 Require Constr Control List Message Std.

(* [Ltac2.Notations] is imported for [apply] and [lazy_match!] inside this
 * file; an [Import] does not travel, so a file importing this one still sees
 * none of Rocq's tactic syntax.
 *)

Ltac2 refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

Ltac2 not_an_equation (who : string) (c : constr) :=
  refuse [Message.of_string who; Message.of_string ": "; Message.of_constr c;
          Message.of_string " proves "; Message.of_constr (Constr.type c);
          Message.of_string ", which is not an equation"].

Ltac2 must_be_equation (who : string) (c : constr) :=
  lazy_match! Constr.type c with
  | _ = _ => ()
  | _ => not_an_equation who c
  end.

(* The name an [as] or [|-] gives must be new. *)
Ltac2 must_be_new (who : string) (p : Std.intro_pattern) :=
  match p with
  | Std.IntroNaming (Std.IntroIdentifier x) =>
      if Local.local_in_context x
      then refuse [Message.of_string who; Message.of_string ": "; Message.of_ident x;
                   Message.of_string " is already in the context"]
      else ()
  | _ => ()
  end.

(* The symmetry of [=].
 *
 *   symm <H>    A = B |- B = A
 *
 * Bare, it is a term: [ipso (symm &e)], [let proof f := symm &e]. Only
 * [symm <H> as <p>], or equally [symm <H> |- <p>], is a tactic, and <p>
 * must be new. In place, on a comma-separated list of hypotheses:
 *
 *   symm in <hypotheses>          each A = B becomes B = A
 *   symm in |- *                  the goal A = B becomes B = A
 *   symm in <hypotheses> |- *     both
 *
 * Anything but an equation is refused. Nothing anywhere may be named [symm].
 *)
Notation "'symm' H" := (Identity.symmetry H)
  (only parsing).

Ltac2 symm_as (h : unit -> constr) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    let c := Local.checked "symm" h in
    must_be_equation "symm" c;
    must_be_new "symm" p;
    Std.specialize (constr:(Identity.symmetry $c), Std.NoBindings) (Some p)).

Ltac2 Notation "symm" h(thunk(constr)) "as" p(intropattern) :=
  symm_as h p.

Ltac2 Notation "symm" h(thunk(constr)) "|-" p(intropattern) :=
  symm_as h p.

Ltac2 symm_in_hypothesis (h : ident) :=
  if Local.local_in_context h
  then
    lazy_match! Constr.type (Control.hyp h) with
    | _ = _ => apply Identity.symmetry in $h
    | _ => not_an_equation "symm" (Control.hyp h)
    end
  else refuse [Message.of_string "symm: "; Message.of_ident h;
               Message.of_string " is not in the context"].

Ltac2 symm_in_goal () :=
  lazy_match! goal with
  | [ |- _ = _ ] => apply Identity.symmetry
  | [ |- _ ] => refuse [Message.of_string "symm: the goal is not an equation"]
  end.

Ltac2 Notation "symm" "in" hypotheses(list1(context_name, ",")) :=
  Control.enter (fun () =>
    List.iter symm_in_hypothesis (Local.context_idents "symm" hypotheses)).

Ltac2 Notation "symm" "in" "|-" "*" :=
  Control.enter symm_in_goal.

Ltac2 Notation "symm" "in" hypotheses(list1(context_name, ",")) "|-" "*" :=
  Control.enter (fun () =>
    List.iter symm_in_hypothesis (Local.context_idents "symm" hypotheses); symm_in_goal ()).

(* The transitivity of [=].
 *
 *   trans <H1>, <H2>    A = B, B = C |- A = C
 *
 * The premises in that order, the right side of <H1> being the left side of
 * <H2>. Bare, it is a term; [trans <H1>, <H2> as <p>], or equally
 * [trans <H1>, <H2> |- <p>], is a tactic, and <p> must be new. Anything but
 * two equations that chain is refused. Nothing anywhere may be named
 * [trans].
 *)
Notation "'trans' H1 , H2" := (Identity.transitivity H1 H2)
  (only parsing).

Ltac2 trans_as (h1 : unit -> constr) (h2 : unit -> constr) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    let c1 := Local.checked "trans" h1 in
    let c2 := Local.checked "trans" h2 in
    must_be_equation "trans" c1;
    must_be_equation "trans" c2;
    must_be_new "trans" p;
    Control.once_plus
      (fun () =>
        Std.specialize (constr:(Identity.transitivity $c1 $c2), Std.NoBindings) (Some p))
      (fun _ =>
        refuse [Message.of_string "trans: "; Message.of_constr (Constr.type c1);
                Message.of_string " and "; Message.of_constr (Constr.type c2);
                Message.of_string " do not chain, the right side of the first";
                Message.of_string " not being the left side of the second"])).

Ltac2 Notation "trans" h1(thunk(constr)) "," h2(thunk(constr)) "as" p(intropattern) :=
  trans_as h1 h2 p.

Ltac2 Notation "trans" h1(thunk(constr)) "," h2(thunk(constr)) "|-" p(intropattern) :=
  trans_as h1 h2 p.

(* The congruence of [=] under a function.
 *
 *   congru <F>, <H>    x = y |- F x = F y
 *
 * <F> a function, <H> an equation between values of the type <F> takes.
 * Bare, it is a term; [congru <F>, <H> as <p>], or equally
 * [congru <F>, <H> |- <p>], is a tactic, and <p> must be new. An <H> that is
 * no equation, and an <F> that takes another type, are refused. Nothing
 * anywhere may be named [congru].
 *)
Notation "'congru' F , H" := (Identity.congruence F H)
  (only parsing).

(* <F> and <H> are typed as one application, so that <H> fixes the implicit
 * arguments of an <F> such as [first]; <F> alone is typed only to word the
 * refusal.
 *)
Ltac2 congru_as (f : preterm) (h : preterm) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    Local.check_preterms "congru" [f; h];
    let ch := Local.elaborate h in
    must_be_equation "congru" ch;
    must_be_new "congru" p;
    Control.once_plus
      (fun () =>
        Std.specialize
          (Local.elaborate preterm:(Identity.congruence $preterm:f $preterm:h), Std.NoBindings)
          (Some p))
      (fun _ =>
        let function :=
          Control.once_plus
            (fun () =>
               let cf := Local.elaborate f in
               Message.concat (Message.of_constr cf)
                 (Message.concat (Message.of_string " has type ")
                    (Message.of_constr (Constr.type cf))))
            (fun _ => Message.of_string "the function") in
        refuse [Message.of_string "congru: "; function;
                Message.of_string ", which does not take the sides of ";
                Message.of_constr (Constr.type ch)])).

Ltac2 Notation "congru" f(preterm) "," h(preterm) "as" p(intropattern) :=
  congru_as f h p.

Ltac2 Notation "congru" f(preterm) "," h(preterm) "|-" p(intropattern) :=
  congru_as f h p.
