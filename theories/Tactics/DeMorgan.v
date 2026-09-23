(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* De Morgan, unfolding a negated disjunction.
 *
 *   de morgan <H>    ~ (A \/ B) |- ~ A /\ ~ B
 *
 * Only [~ (A \/ B)] unfolds. [~ (A /\ B)] is refused with an error saying
 * why: [~ A \/ ~ B] would have to name which of [A] and [B] fails, and
 * [~ (A /\ B)] does not say, so that direction is not constructive. Any
 * other shape is refused as well.
 *
 * Bare, it is a term: [ipso (de morgan h)], [pose proof (de morgan h) as p].
 * Only [de morgan <H> as <p>], or equally [de morgan <H> |- <p>], is a
 * tactic. Nothing anywhere may be named [de] or [morgan].
 *)

(* Both forms first read the shape of <H>, so that a refusal carries its
 * reason instead of a unification error.
 *)
Ltac de_morgan_refuse H :=
  lazymatch type of H with
  | ~ (_ /\ _) =>
      fail "de morgan: ~ (A /\ B) does not split constructively,"
           " since it does not say which of A and B fails"
  | _ => fail "de morgan: expects a hypothesis of the shape ~ (A \/ B)"
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'de' 'morgan' H" :=
  (ltac:(lazymatch type of H with
         | ~ (_ \/ _) =>
             exact (Biconditional.forward.elimination
                      (Negation.de_morgan.disjunction _ _) H)
         | _ => de_morgan_refuse H
         end))
  (only parsing).

Tactic Notation "de" "morgan" constr(H) "as" simple_intropattern(p) :=
  lazymatch type of H with
  | ~ (_ \/ _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.disjunction _ _) H) as p
  | _ => de_morgan_refuse H
  end.

Tactic Notation "de" "morgan" constr(H) "|-" simple_intropattern(p) :=
  lazymatch type of H with
  | ~ (_ \/ _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.disjunction _ _) H) as p
  | _ => de_morgan_refuse H
  end.
