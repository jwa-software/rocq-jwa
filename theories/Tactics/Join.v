(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Abjunction.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Sejunction.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Control Message Std.

(* The introduction of each junction, written as the rule reads:
 *
 *   conjoin <a>, <b>       <a> : A, <b> : B         |- A /\ B
 *   disjoin <a>, _         <a> : A                  |- A \/ B
 *   disjoin _, <b>         <b> : B                  |- A \/ B
 *   sejoin <a>, <nb>       <a> : A, <nb> : ~ B      |- A _\/_ B
 *   sejoin <na>, <b>       <na> : ~ A, <b> : B      |- A _\/_ B
 *   abjoin <a>, <nb>       <a> : A, <nb> : ~ B      |- A -/> B
 *
 * Bare, each is a term, defined beside its connective in [Core.Logic]. With
 * [|- <p>], [conjoin], [sejoin] and [abjoin] are also tactics that add the
 * conclusion as <p>. [disjoin] has no such form: the side written [_] is
 * known only from an expected type, so it is written inside [ipso (...)] or
 * [let proof <p> : A \/ B := ...].
 *)

Ltac2 join (who : string) (a : preterm) (b : preterm) (built : unit -> constr)
  (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    (Local.check_preterms who [a; b];
     Std.specialize (built (), Std.NoBindings) (Some p))).

Ltac2 Notation "conjoin" a(preterm) "," b(preterm) "|-" p(intropattern) :=
  join "conjoin" a b
    (fun () => Local.elaborate preterm:(Conjunction_introduction $preterm:a $preterm:b)) p.

Ltac2 Notation "abjoin" a(preterm) "," b(preterm) "|-" p(intropattern) :=
  join "abjoin" a b
    (fun () => Local.elaborate preterm:(Abjunction_introduction $preterm:a $preterm:b)) p.

(* The left ctor is tried first, then the right; when neither types, the
 * refusal says what the two must be.
 *)
Ltac2 Notation "sejoin" a(preterm) "," b(preterm) "|-" p(intropattern) :=
  join "sejoin" a b
    (fun () =>
      Control.once_plus
        (fun () =>
          Local.elaborate preterm:(Sejunction_introduction_left $preterm:a $preterm:b))
        (fun _ =>
          Control.once_plus
            (fun () =>
              Local.elaborate preterm:(Sejunction_introduction_right $preterm:a $preterm:b))
            (fun _ =>
              Control.zero
                (Tactic_failure
                   (Some (Message.concat
                           (Message.of_string
                              "sejoin: give a proof of one side and a refutation of the other,")
                           (Message.of_string " as in sejoin a, nb or sejoin na, b")))))))
    p.
