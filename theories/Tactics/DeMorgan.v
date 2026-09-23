(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Biconditional.
From jwa Require Import Core.Logic.Conditional.
From jwa Require Import Core.Logic.Conjunction.
From jwa Require Import Core.Logic.Disjunction.
From jwa Require Import Core.Logic.Exists.
From jwa Require Import Core.Logic.Negation.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Import Notations.
From Ltac2 Require Constr Control List Message Std String.

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
 * Bare, it is a term: [ipso (de morgan h)], [let proof p := de morgan h].
 * [de morgan <H> as <p>], or equally [de morgan <H> |- <p>], is a tactic
 * adding the result. Nothing anywhere may be named [de] or [morgan].
 *
 *   de morgan in <hypotheses>          rewrites each in place
 *   de morgan in |- *                  rewrites the goal in place
 *   de morgan in <hypotheses> |- *     both
 *
 * <hypotheses> is a comma-separated list of names, one or more. These change
 * the targets themselves and add nothing. On the goal the same two shapes
 * are rewritten, each an equivalence, so a provable goal stays provable.
 * [~ (A /\ B)] and [~ (forall x . P x)] are refused there too: [~ A \/ ~ B]
 * and [exists x . ~ P x] would prove them, but may not be provable where the
 * original is, as [~ (A /\ ~ A)] shows.
 *
 * [Ltac2.Notations] is imported for [apply] and [lazy_match!] inside this
 * file; an [Import] does not travel, so a file importing this one still sees
 * none of Rocq's tactic syntax.
 *)

Ltac2 refuse (message : string) :=
  Control.zero (Tactic_failure (Some (Message.of_string message))).

(* Every form reads the shape first, so that a refusal carries its reason
 * instead of a unification error. An implication is a [forall] too, so
 * [~ (A -> B)] is caught first and gets the general message.
 *)
Ltac2 de_morgan_refuse (t : constr) :=
  lazy_match! t with
  | ~ (_ /\ _) =>
      refuse (String.app "de morgan: ~ (A /\ B) does not split constructively,"
                         " since it does not say which of A and B fails")
  | ~ (?_a -> ?_b) =>
      refuse "de morgan: expects a hypothesis of the shape ~ (A \/ B) or ~ (exists x . P x)"
  | ~ (forall _, _) =>
      refuse (String.app "de morgan: ~ (forall x . P x) does not split constructively,"
                         " since it does not say which x fails")
  | _ =>
      refuse "de morgan: expects a hypothesis of the shape ~ (A \/ B) or ~ (exists x . P x)"
  end.

(* The unfolded proof of what <h> proves. *)
Ltac2 de_morgan_of (h : constr) : constr :=
  let t := Constr.type h in
  lazy_match! t with
  | ~ (_ \/ _) =>
      constr:(Biconditional.forward.elimination (Negation.de_morgan.disjunction _ _) $h)
  | ~ (Exists _) =>
      constr:(Biconditional.forward.elimination (Negation.de_morgan.existential _ _) $h)
  | _ => de_morgan_refuse t
  end.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * Inside [ltac2:] the notation's variable is a [preterm], typed by the
 * [constr:] quotation.
 *)
Notation "'de' 'morgan' H" :=
  (ltac2:(Control.refine (fun () => de_morgan_of constr:($preterm:H))))
  (only parsing).

Ltac2 Notation "de" "morgan" h(constr) "as" p(intropattern) :=
  Control.enter (fun () => Std.specialize (de_morgan_of h, Std.NoBindings) (Some p)).

Ltac2 Notation "de" "morgan" h(constr) "|-" p(intropattern) :=
  Control.enter (fun () => Std.specialize (de_morgan_of h, Std.NoBindings) (Some p)).

Ltac2 de_morgan_in_hypothesis (h : ident) :=
  let t := Constr.type (Control.hyp h) in
  lazy_match! t with
  | ~ (_ \/ _) =>
      apply (Biconditional.forward.elimination (Negation.de_morgan.disjunction _ _)) in $h
  | ~ (Exists _) =>
      apply (Biconditional.forward.elimination (Negation.de_morgan.existential _ _)) in $h
  | _ => de_morgan_refuse t
  end.

(* The goal is rewritten backward, from the new statement to the old, which
 * is why only the two equivalences are allowed here.
 *)
Ltac2 de_morgan_in_goal () :=
  lazy_match! goal with
  | [ |- ~ (_ \/ _) ] =>
      apply (Biconditional.backward.elimination (Negation.de_morgan.disjunction _ _))
  | [ |- ~ (Exists _) ] =>
      apply (Biconditional.backward.elimination (Negation.de_morgan.existential _ _))
  | [ |- ~ (_ /\ _) ] =>
      refuse (String.app "de morgan: a goal ~ (A /\ B) is left alone,"
                         " since ~ A \/ ~ B may not be provable where it is")
  | [ |- ~ (?_a -> ?_b) ] =>
      refuse "de morgan: expects a goal of the shape ~ (A \/ B) or ~ (exists x . P x)"
  | [ |- ~ (forall _, _) ] =>
      refuse (String.app "de morgan: a goal ~ (forall x . P x) is left alone,"
                         " since exists x . ~ P x may not be provable where it is")
  | [ |- _ ] =>
      refuse "de morgan: expects a goal of the shape ~ (A \/ B) or ~ (exists x . P x)"
  end.

Ltac2 Notation "de" "morgan" "in" hypotheses(list1(ident, ",")) :=
  Control.enter (fun () => List.iter de_morgan_in_hypothesis hypotheses).

Ltac2 Notation "de" "morgan" "in" "|-" "*" :=
  Control.enter de_morgan_in_goal.

Ltac2 Notation "de" "morgan" "in" hypotheses(list1(ident, ",")) "|-" "*" :=
  Control.enter (fun () =>
    List.iter de_morgan_in_hypothesis hypotheses; de_morgan_in_goal ()).
