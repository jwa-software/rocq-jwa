(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Exists.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Ltac.
From jwa Require Import Core.Notations.

(* De Morgan, unfolding a negated disjunction or a negated [exists].
 *
 *   de morgan <H>    ~ (A \/ B) |- ~ A /\ ~ B
 *                    ~ (exists x . P x) |- forall x . ~ P x
 *
 * Only these two unfold. [~ (A /\ B)] and [~ (forall x . P x)] are refused
 * with an error saying why: [~ A \/ ~ B] would have to name which of [A] and
 * [B] fails, and [exists x . ~ P x] which [x] fails, and neither premise
 * says, so those directions are not constructive. Any other shape is
 * refused as well.
 *
 * Bare, it is a term: [ipso (de morgan h)], [pose proof (de morgan h) as p].
 * [de morgan <H> as <p>], or equally [de morgan <H> |- <p>], is a tactic
 * adding the result. Nothing anywhere may be named [de] or [morgan].
 *
 *   de morgan in <H>          rewrites <H> in place
 *   de morgan in |- *         rewrites the goal in place
 *   de morgan in <H> |- *     both
 *
 * These change the target itself and add nothing. On the goal the same two
 * shapes are rewritten, each an equivalence, so a provable goal stays
 * provable. [~ (A /\ B)] and [~ (forall x . P x)] are refused there too:
 * [~ A \/ ~ B] and [exists x . ~ P x] would prove them, but may not be
 * provable where the original is, as [~ (A /\ ~ A)] shows. One hypothesis at
 * most: Ltac cannot walk a list of them one by one.
 *)

(* Both forms first read the shape of <H>, so that a refusal carries its
 * reason instead of a unification error. An implication is a [forall] too,
 * so [~ (A -> B)] is caught first and gets the general message.
 *)
Ltac de_morgan_refuse H :=
  lazymatch type of H with
  | ~ (_ /\ _) =>
      fail "de morgan: ~ (A /\ B) does not split constructively,"
           " since it does not say which of A and B fails"
  | ~ (?A -> ?B) =>
      fail "de morgan: expects a hypothesis of the shape ~ (A \/ B) or ~ (exists x . P x)"
  | ~ (forall _, _) =>
      fail "de morgan: ~ (forall x . P x) does not split constructively,"
           " since it does not say which x fails"
  | _ =>
      fail "de morgan: expects a hypothesis of the shape ~ (A \/ B) or ~ (exists x . P x)"
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here. *)
Notation "'de' 'morgan' H" :=
  (ltac:(lazymatch type of H with
         | ~ (_ \/ _) =>
             exact (Biconditional.forward.elimination
                      (Negation.de_morgan.disjunction _ _) H)
         | ~ (Exists _) =>
             exact (Biconditional.forward.elimination
                      (Negation.de_morgan.existential _ _) H)
         | _ => de_morgan_refuse H
         end))
  (only parsing).

Tactic Notation "de" "morgan" constr(H) "as" simple_intropattern(p) :=
  lazymatch type of H with
  | ~ (_ \/ _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.disjunction _ _) H) as p
  | ~ (Exists _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.existential _ _) H) as p
  | _ => de_morgan_refuse H
  end.

Tactic Notation "de" "morgan" constr(H) "|-" simple_intropattern(p) :=
  lazymatch type of H with
  | ~ (_ \/ _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.disjunction _ _) H) as p
  | ~ (Exists _) =>
      pose proof (Biconditional.forward.elimination
                    (Negation.de_morgan.existential _ _) H) as p
  | _ => de_morgan_refuse H
  end.

Ltac de_morgan_in_hypothesis H :=
  lazymatch type of H with
  | ~ (_ \/ _) =>
      apply (Biconditional.forward.elimination
               (Negation.de_morgan.disjunction _ _)) in H
  | ~ (Exists _) =>
      apply (Biconditional.forward.elimination
               (Negation.de_morgan.existential _ _)) in H
  | _ => de_morgan_refuse H
  end.

(* The goal is rewritten backward, from the new statement to the old, which
 * is why only the two equivalences are allowed here.
 *)
Ltac de_morgan_in_goal :=
  lazymatch goal with
  | |- ~ (_ \/ _) =>
      apply (Biconditional.backward.elimination
               (Negation.de_morgan.disjunction _ _))
  | |- ~ (Exists _) =>
      apply (Biconditional.backward.elimination
               (Negation.de_morgan.existential _ _))
  | |- ~ (_ /\ _) =>
      fail "de morgan: a goal ~ (A /\ B) is left alone,"
           " since ~ A \/ ~ B may not be provable where it is"
  | |- ~ (?A -> ?B) =>
      fail "de morgan: expects a goal of the shape ~ (A \/ B) or ~ (exists x . P x)"
  | |- ~ (forall _, _) =>
      fail "de morgan: a goal ~ (forall x . P x) is left alone,"
           " since exists x . ~ P x may not be provable where it is"
  | |- _ =>
      fail "de morgan: expects a goal of the shape ~ (A \/ B) or ~ (exists x . P x)"
  end.

Tactic Notation "de" "morgan" "in" hyp(H) :=
  de_morgan_in_hypothesis H.

Tactic Notation "de" "morgan" "in" "|-" "*" :=
  de_morgan_in_goal.

Tactic Notation "de" "morgan" "in" hyp(H) "|-" "*" :=
  de_morgan_in_hypothesis H;
  de_morgan_in_goal.
