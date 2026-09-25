(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Logic.Sejunction.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Control Std.

(* The four modi of traditional logic and a fifth in their pattern.
 *
 *   modus ponens          <H1>, <H2>    A -> B, A |- B
 *   modus tollens         <H1>, <H2>    A -> B, ~ B |- ~ A
 *   modus tollendo ponens <H1>, <H2>    A \/ B, ~ A |- B
 *                                       A \/ B, ~ B |- A
 *   modus ponendo tollens <H1>, <H2>    ~ (A /\ B), A |- ~ B
 *                                       ~ (A /\ B), B |- ~ A
 *   modus aequans         <H1>, <H2>    A <-> B, A |- B
 *                                       A <-> B, B |- A
 *
 * Bare, each is a term: [ipso (modus ponens hab, ha)], [let proof h := modus
 * aequans e, a], or one nested in another. Only [... as <p>] is a tactic, and
 * [... |- <p>] spells the same tactic the way the table above reads. Every
 * one takes its premises in the order written, the connective first and the
 * term second. The last three read either side of their connective, and
 * [modus ponendo tollens] takes a sejunction [A _\/_ B] as well as a negated
 * conjunction; the first two also answer to [modus ponendo ponens] and
 * [modus tollendo tollens].
 *
 * Nothing anywhere may be named [modus], [ponens], [tollens], [ponendo],
 * [tollendo] or [aequans]. The tactics type the whole application at once,
 * so a lemma's implicit arguments may be fixed by the other premise; the
 * term forms of the last three, whose bodies must try their branches, do
 * not, and there a premise that is a bare lemma name whose implicits only
 * the other premise would fix does not elaborate: give them with [@], name
 * the lemma first, or use the [as] form.
 *)

(* Tries each branch in turn and keeps the first that succeeds; a later
 * failure does not come back to try the next, as [Control.plus] alone
 * would. When none succeeds, [refusal] says why.
 *)
Ltac2 rec first_branch (refusal : unit -> unit) (branches : (unit -> unit) list) :=
  match branches with
  | [] => refusal ()
  | branch :: rest => Control.once_plus branch (fun _ => first_branch refusal rest)
  end.

(* A premise and its type, printed from the elaborated term, where [&h] reads [h]. *)
Ltac2 premise (h : preterm) : message :=
  Control.once_plus
    (fun () =>
       let t := Local.elaborate h in
       Message.concat (Message.of_constr t)
         (Message.concat (Message.of_string " proves ")
            (Message.of_constr (Constr.type t))))
    (fun _ => Message.of_string "a premise that does not type on its own").

(* The refusal of a modus whose two premises fit none of its forms. *)
Ltac2 refuse_premises (who : string) (forms : string) (h1 : preterm) (h2 : preterm) :=
  Control.zero
    (Tactic_failure
       (Some (Message.concat (Message.of_string who)
             (Message.concat (Message.of_string ": ")
             (Message.concat (premise h1)
             (Message.concat (Message.of_string " and ")
             (Message.concat (premise h2)
             (Message.concat (Message.of_string "; the rule takes ")
                (Message.of_string forms))))))))).

Ltac2 tollendo_ponens_forms () := "A \/ B with ~ A, or A \/ B with ~ B".

Ltac2 ponendo_tollens_forms () := "~ (A /\ B) or A _\/_ B, with A or with B".

Ltac2 aequans_forms () := "A <-> B with A, or A <-> B with B".

(* The levels are reserved in [Core.Notations]; only the meanings belong
 * here. [ltac2:] is what lets a term try branches: it opens a goal, runs the
 * tactic, and the proof is the term. Inside it the notation's variables are
 * [preterm]s, typed with the whole application at once.
 *)
Notation "'modus' 'ponens' H1 , H2" := (H1 H2)
  (only parsing).

Ltac2 Notation "modus" "ponens" h1(preterm) "," h2(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus ponens" [h1; h2];
     Std.specialize (Local.elaborate preterm:($preterm:h1 $preterm:h2), Std.NoBindings) (Some p))).

Ltac2 Notation "modus" "ponens" h1(preterm) "," h2(preterm) "|-" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus ponens" [h1; h2];
     Std.specialize (Local.elaborate preterm:($preterm:h1 $preterm:h2), Std.NoBindings) (Some p))).

Notation "'modus' 'ponendo' 'ponens' H1 , H2" := (H1 H2)
  (only parsing).

Ltac2 Notation "modus" "ponendo" "ponens" h1(preterm) "," h2(preterm)
    "as" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus ponendo ponens" [h1; h2];
     Std.specialize (Local.elaborate preterm:($preterm:h1 $preterm:h2), Std.NoBindings) (Some p))).

Ltac2 Notation "modus" "ponendo" "ponens" h1(preterm) "," h2(preterm)
    "|-" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus ponendo ponens" [h1; h2];
     Std.specialize (Local.elaborate preterm:($preterm:h1 $preterm:h2), Std.NoBindings) (Some p))).

Notation "'modus' 'tollens' H1 , H2" := (Negation.contraposition H1 H2)
  (only parsing).

Ltac2 Notation "modus" "tollens" h1(preterm) "," h2(preterm) "as" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus tollens" [h1; h2];
     Std.specialize
       (Local.elaborate preterm:(Negation.contraposition $preterm:h1 $preterm:h2), Std.NoBindings)
       (Some p))).

Ltac2 Notation "modus" "tollens" h1(preterm) "," h2(preterm) "|-" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus tollens" [h1; h2];
     Std.specialize
       (Local.elaborate preterm:(Negation.contraposition $preterm:h1 $preterm:h2), Std.NoBindings)
       (Some p))).

Notation "'modus' 'tollendo' 'tollens' H1 , H2"
    := (Negation.contraposition H1 H2)
  (only parsing).

Ltac2 Notation "modus" "tollendo" "tollens" h1(preterm) "," h2(preterm)
    "as" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus tollendo tollens" [h1; h2];
     Std.specialize
       (Local.elaborate preterm:(Negation.contraposition $preterm:h1 $preterm:h2), Std.NoBindings)
       (Some p))).

Ltac2 Notation "modus" "tollendo" "tollens" h1(preterm) "," h2(preterm)
    "|-" p(intropattern) :=
  Control.enter (fun () =>
    (Local.check_preterms "modus tollendo tollens" [h1; h2];
     Std.specialize
       (Local.elaborate preterm:(Negation.contraposition $preterm:h1 $preterm:h2), Std.NoBindings)
       (Some p))).

Notation "'modus' 'tollendo' 'ponens' H1 , H2"
    := (ltac2:(first_branch
                 (fun () => refuse_premises "modus tollendo ponens" (tollendo_ponens_forms ())
                              preterm:($preterm:H1) preterm:($preterm:H2))
                 [ (fun () => Control.refine (fun () =>
                      constr:(Negation.elimination.left.of.disjunction
                                $preterm:H1 $preterm:H2)));
                   (fun () => Control.refine (fun () =>
                      constr:(Negation.elimination.right.of.disjunction
                                $preterm:H1 $preterm:H2))) ]))
  (only parsing).

Ltac2 modus_tollendo_ponens (h1 : preterm) (h2 : preterm) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    Local.check_preterms "modus tollendo ponens" [h1; h2];
    first_branch
      (fun () => refuse_premises "modus tollendo ponens" (tollendo_ponens_forms ()) h1 h2)
      [ (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.elimination.left.of.disjunction
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p));
        (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.elimination.right.of.disjunction
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p)) ]).

Ltac2 Notation "modus" "tollendo" "ponens" h1(preterm) "," h2(preterm)
    "as" p(intropattern) :=
  modus_tollendo_ponens h1 h2 p.

Ltac2 Notation "modus" "tollendo" "ponens" h1(preterm) "," h2(preterm)
    "|-" p(intropattern) :=
  modus_tollendo_ponens h1 h2 p.

Notation "'modus' 'ponendo' 'tollens' H1 , H2"
    := (ltac2:(first_branch
                 (fun () => refuse_premises "modus ponendo tollens" (ponendo_tollens_forms ())
                              preterm:($preterm:H1) preterm:($preterm:H2))
                 [ (fun () => Control.refine (fun () =>
                      constr:(Negation.exclusion.left.of.conjunction
                                $preterm:H1 $preterm:H2)));
                   (fun () => Control.refine (fun () =>
                      constr:(Negation.exclusion.right.of.conjunction
                                $preterm:H1 $preterm:H2)));
                   (fun () => Control.refine (fun () =>
                      constr:(Negation.exclusion.left.of.conjunction
                                (Sejunction.exclusion.of.conjunction $preterm:H1)
                                $preterm:H2)));
                   (fun () => Control.refine (fun () =>
                      constr:(Negation.exclusion.right.of.conjunction
                                (Sejunction.exclusion.of.conjunction $preterm:H1)
                                $preterm:H2))) ]))
  (only parsing).

Ltac2 modus_ponendo_tollens (h1 : preterm) (h2 : preterm) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    Local.check_preterms "modus ponendo tollens" [h1; h2];
    first_branch
      (fun () => refuse_premises "modus ponendo tollens" (ponendo_tollens_forms ()) h1 h2)
      [ (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.exclusion.left.of.conjunction
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p));
        (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.exclusion.right.of.conjunction
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p));
        (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.exclusion.left.of.conjunction
                      (Sejunction.exclusion.of.conjunction $preterm:h1)
                      $preterm:h2), Std.NoBindings) (Some p));
        (fun () => Std.specialize
           (Local.elaborate preterm:(Negation.exclusion.right.of.conjunction
                      (Sejunction.exclusion.of.conjunction $preterm:h1)
                      $preterm:h2), Std.NoBindings) (Some p)) ]).

Ltac2 Notation "modus" "ponendo" "tollens" h1(preterm) "," h2(preterm)
    "as" p(intropattern) :=
  modus_ponendo_tollens h1 h2 p.

Ltac2 Notation "modus" "ponendo" "tollens" h1(preterm) "," h2(preterm)
    "|-" p(intropattern) :=
  modus_ponendo_tollens h1 h2 p.

Notation "'modus' 'aequans' H1 , H2"
    := (ltac2:(first_branch
                 (fun () => refuse_premises "modus aequans" (aequans_forms ())
                              preterm:($preterm:H1) preterm:($preterm:H2))
                 [ (fun () => Control.refine (fun () =>
                      constr:(Biconditional.forward.elimination
                                $preterm:H1 $preterm:H2)));
                   (fun () => Control.refine (fun () =>
                      constr:(Biconditional.backward.elimination
                                $preterm:H1 $preterm:H2))) ]))
  (only parsing).

Ltac2 modus_aequans (h1 : preterm) (h2 : preterm) (p : Std.intro_pattern) :=
  Control.enter (fun () =>
    Local.check_preterms "modus aequans" [h1; h2];
    first_branch
      (fun () => refuse_premises "modus aequans" (aequans_forms ()) h1 h2)
      [ (fun () => Std.specialize
           (Local.elaborate preterm:(Biconditional.forward.elimination
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p));
        (fun () => Std.specialize
           (Local.elaborate preterm:(Biconditional.backward.elimination
                      $preterm:h1 $preterm:h2), Std.NoBindings) (Some p)) ]).

Ltac2 Notation "modus" "aequans" h1(preterm) "," h2(preterm) "as" p(intropattern) :=
  modus_aequans h1 h2 p.

Ltac2 Notation "modus" "aequans" h1(preterm) "," h2(preterm) "|-" p(intropattern) :=
  modus_aequans h1 h2 p.
