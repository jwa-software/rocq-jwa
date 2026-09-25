(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.All.
From jwa Require Import Tactics.All.

Ltac2 Notation "lazy_match!" t(tactic(6)) "with" m(constr_matching) "end" : 0 :=
  Pattern.lazy_match0 t m.

Ltac2 Notation "lazy_match!" "goal" "with" m(goal_matching) "end" : 0 :=
  Pattern.lazy_goal_match0 false m.

Theorem tactics_all_delivers_de_morgan
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  intros A B h.
  ipso (de morgan h).
Qed.

Theorem tactics_all_delivers_de_morgan_as
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ B.
Proof.
  intros A B h.
  de morgan h as [na nb].
  ipso nb.
Qed.

Theorem tactics_all_delivers_de_morgan_turnstile
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  intros A B h.
  de morgan h |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_de_morgan_refusing_a_conjunction
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> ~ (A /\ B).
Proof.
  intros A B h.
  Fail de morgan h as x.
  Fail let proof x := de morgan h.
  ipso h.
Qed.

Theorem tactics_all_delivers_de_morgan_existential
  : forall (A : Type) (P : A -> Prop) . ~ (forsome (x : A) . P x) -> forall (x : A) . ~ P x.
Proof.
  intros A P h.
  ipso (de morgan h).
Qed.

Theorem tactics_all_delivers_de_morgan_existential_as
  : forall (A : Type) (P : A -> Prop) (a : A) . ~ (forsome (x : A) . P x) -> ~ P a.
Proof.
  intros A P a h.
  de morgan h as facto.
  ipso (facto a).
Qed.

Theorem tactics_all_delivers_de_morgan_refusing_a_universal
  : forall (A : Type) (P : A -> Prop) . ~ (forall (x : A) . P x) -> ~ (forall (x : A) . P x).
Proof.
  intros A P h.
  Fail de morgan h as x.
  Fail let proof x := de morgan h.
  ipso h.
Qed.

Theorem tactics_all_delivers_de_morgan_in_hypothesis
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ B.
Proof.
  intros A B h.
  de morgan in h.
  lazy_match! Constr.type &h with
  | ~ A /\ ~ B => match h with | na nb end
  end.
  ipso nb.
Qed.

Theorem tactics_all_delivers_de_morgan_in_goal
  : forall (A : Type) (P : A -> Prop) . (forall (x : A) . ~ P x) -> ~ (forsome (x : A) . P x).
Proof.
  intros A P h.
  de morgan in |- *.
  lazy_match! goal with
  | [ |- forall (x : A) . ~ P x ] => ipso h
  end.
Qed.

Theorem tactics_all_delivers_de_morgan_in_hypothesis_and_goal
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ (A \/ B).
Proof.
  intros A B h.
  de morgan in h |- *.
  ipso h.
Qed.

Theorem tactics_all_delivers_de_morgan_in_two_hypotheses
  : forall (A : Prop) (B : Prop) (C : Prop) (D : Prop) .
      ~ (A \/ B) -> ~ (C \/ D) -> (~ A /\ ~ B) /\ (~ C /\ ~ D).
Proof.
  intros A B C D h k.
  de morgan in &h, &k.
  ipso (conjoin &h, &k).
Qed.

Theorem tactics_all_delivers_de_morgan_in_refusing_a_conjunction
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> ~ (A /\ B).
Proof.
  intros A B h.
  Fail de morgan in h.
  Fail de morgan in |- *.
  ipso h.
Qed.

Theorem tactics_all_delivers_dni
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  ipso (dni a).
Qed.

Theorem tactics_all_delivers_dni_nested
  : forall (A : Prop) . A -> ~ ~ ~ ~ A.
Proof.
  intros A a.
  ipso (dni (dni a)).
Qed.

Theorem tactics_all_delivers_dni_as
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  dni a as facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_dni_turnstile
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  dni a |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_dne
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  ipso (dne nnna).
Qed.

Theorem tactics_all_delivers_dne_of_dni
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  ipso (dne (dni na)).
Qed.

Theorem tactics_all_delivers_dne_as
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne nnna as facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_dne_turnstile
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne nnna |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_dni_in_hypothesis
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  dni in a.
  lazy_match! Constr.type &a with
  | ~ ~ A => ipso a
  end.
Qed.

Theorem tactics_all_delivers_dni_in_goal
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  dni in |- *.
  lazy_match! goal with
  | [ |- A ] => ipso a
  end.
Qed.

Theorem tactics_all_delivers_dni_in_hypothesis_and_goal
  : forall (A : Prop) . A -> ~ ~ ~ ~ A.
Proof.
  intros A a.
  dni in a |- *.
  ipso a.
Qed.

Theorem tactics_all_delivers_dni_in_two_hypotheses
  : forall (A : Prop) (B : Prop) . A -> B -> ~ ~ A /\ ~ ~ B.
Proof.
  intros A B a b.
  dni in &a, &b.
  ipso (conjoin &a, &b).
Qed.

Theorem tactics_all_delivers_dne_in_hypothesis
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in nnna.
  lazy_match! Constr.type &nnna with
  | ~ A => ipso nnna
  end.
Qed.

Theorem tactics_all_delivers_dne_in_goal
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in |- *.
  lazy_match! goal with
  | [ |- ~ ~ ~ A ] => ipso nnna
  end.
Qed.

Theorem tactics_all_delivers_dne_in_hypothesis_and_goal
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in nnna |- *.
  ipso (dni nnna).
Qed.

Theorem tactics_all_delivers_dne_in_two_hypotheses
  : forall (A : Prop) (B : Prop) . ~ ~ ~ A -> ~ ~ ~ B -> ~ A /\ ~ B.
Proof.
  intros A B nnna nnnb.
  dne in &nnna, &nnnb.
  ipso (conjoin &nnna, &nnnb).
Qed.

Theorem tactics_all_delivers_dne_in_refusing_a_double_negation
  : forall (A : Prop) . ~ ~ A -> ~ ~ A.
Proof.
  intros A nna.
  Fail dne in nna.
  ipso nna.
Qed.

Theorem tactics_all_delivers_let
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  let k := m.
  lazy_match! goal with
  | [ _ := m |- _ ] => quod idem est
  end.
Qed.

Theorem tactics_all_delivers_let_of_an_application
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k := Nat.add m m.
  lazy_match! goal with
  | [ _ := Nat.add m m |- _ ] => quod idem est
  end.
Qed.

Theorem tactics_all_delivers_let_with_a_type
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k : Nat := Nat.add m m.
  lazy_match! goal with
  | [ _ := Nat.add m m : Nat |- _ ] => quod idem est
  end.
Qed.

Theorem tactics_all_delivers_let_proof
  : forall (m : Nat) (n : Nat) .
      Nat.LessThan m n -> Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n).
Proof.
  intros m n h.
  let proof facto := Nat.addition.order.monotonicity Nat.One m n h.
  ipso facto.
Qed.

Theorem tactics_all_delivers_let_proof_with_a_pattern
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B /\ C) -> A -> C.
Proof.
  intros A B C hab ha.
  let proof [b c] := hab ha.
  ipso c.
Qed.

Theorem tactics_all_delivers_let_proof_with_a_type
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  let proof facto : B := hab ha.
  lazy_match! Constr.type &facto with
  | B => ipso facto
  end.
Qed.

Theorem tactics_all_delivers_let_with_an_arrow_type
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  let k : A -> Falsum := na.
  lazy_match! goal with
  | [ _ := na : A -> Falsum |- _ ] => ipso k
  end.
Qed.

Theorem tactics_all_delivers_let_proof_retyping_a_hypothesis
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A h.
  let proof h : A -> Falsum := h.
  lazy_match! Constr.type &h with
  | A -> Falsum => ipso h
  end.
Qed.

Theorem tactics_all_delivers_let_retyping_a_definition
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  let k := na.
  let k : A -> Falsum := k.
  lazy_match! goal with
  | [ _ := na : A -> Falsum |- _ ] => ipso k
  end.
Qed.

Theorem tactics_all_delivers_let_proof_shadowing
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab h.
  let proof h := hab h.
  lazy_match! goal with
  | [ _ : B |- _ ] => ipso h
  end.
Qed.

Theorem tactics_all_delivers_let_shadowing
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  let k := Nat.add m m.
  let k := Nat.add k k.
  lazy_match! goal with
  | [ _ := Nat.add (Nat.add m m) (Nat.add m m) |- _ ] => ()
  end.
  Fail lazy_match! goal with
  | [ _ := Nat.add m m |- _ ] => ()
  end.
  quod idem est.
Qed.

Theorem tactics_all_delivers_let_proof_dropping_a_body
  : forall (m : Nat) (n : Nat) .
      Nat.LessThan m n -> Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n).
Proof.
  intros m n h.
  let H := Nat.addition.order.monotonicity Nat.One m n h.
  let proof H := H.
  Fail lazy_match! goal with
  | [ _ := _ |- _ ] => ()
  end.
  ipso H.
Qed.

Theorem tactics_all_delivers_let_proof_dropping_a_body_with_a_type
  : forall (m : Nat) (n : Nat) .
      Nat.LessThan m n -> Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n).
Proof.
  intros m n h.
  let H := Nat.addition.order.monotonicity Nat.One m n h.
  let proof H : Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n) := H.
  Fail lazy_match! goal with
  | [ _ := _ |- _ ] => ()
  end.
  ipso H.
Qed.

Theorem tactics_all_delivers_let_proof_of_a_definition_under_another_name
  : forall (m : Nat) (n : Nat) .
      Nat.LessThan m n -> Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n).
Proof.
  intros m n h.
  let H := Nat.addition.order.monotonicity Nat.One m n h.
  let proof facto := H.
  lazy_match! goal with
  | [ _ := _ |- _ ] => ipso facto
  end.
Qed.

Theorem tactics_all_delivers_let_proof_dropping_a_body_others_mention
  : forall (m : Nat) . Verum.
Proof.
  intro m.
  let k := Nat.add m m.
  lemma q : k = k.
  - quod idem est.
  - let proof k := k.
    Fail lazy_match! goal with
    | [ _ := _ |- _ ] => ()
    end.
    lazy_match! goal with
    | [ _ : k = k |- _ ] => ipso I
    end.
Qed.

Theorem tactics_all_delivers_let_proof_leaving_a_hypothesis_alone
  : forall (A : Prop) . A -> A.
Proof.
  intros A H.
  let proof H := H.
  let proof H : A := H.
  ipso H.
Qed.

Theorem tactics_all_delivers_let_proof_refusing_what_another_depends_on
  : forall (n : Nat) (e : n = n) (P : n = n -> Prop) . P e -> P e.
Proof.
  intros n e P p.
  Fail let proof e := Identity.symmetry e.
  ipso p.
Qed.

Theorem tactics_all_delivers_ipso
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  ipso a.
Qed.

Theorem tactics_all_delivers_ipso_with_a_term
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  ipso (modus ponens hab, ha).
Qed.

Theorem tactics_all_delivers_ipso_as_a_name
  : forall (A : Prop) . A -> A.
Proof.
  intros A ipso.
  ipso ipso.
Qed.

Theorem tactics_all_delivers_leibniz
  : forall (A : Type) (P : A -> Prop) (x : A) (y : A) . x = y -> P y -> P x.
Proof.
  intros A P x y e p.
  leibniz e in |- *.
  ipso p.
Qed.

Theorem tactics_all_delivers_leibniz_backward
  : forall (A : Type) (P : A -> Prop) (x : A) (y : A) . y = x -> P y -> P x.
Proof.
  intros A P x y e p.
  leibniz <- e in |- *.
  ipso p.
Qed.

Theorem tactics_all_delivers_leibniz_hypotheses
  : forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (x : A) (y : A) .
      x = y -> P x -> Q x -> P y /\ Q y.
Proof.
  intros A P Q x y e p q.
  leibniz e in p, q.
  ipso (conjoin p, q).
Qed.

Theorem tactics_all_delivers_leibniz_hypotheses_and_goal
  : forall (A : Type) (P : A -> Prop) (x : A) (y : A) . y = x -> P x -> P x.
Proof.
  intros A P x y e p.
  leibniz <- e in p |- *.
  ipso p.
Qed.

Theorem tactics_all_delivers_leibniz_goal
  : forall (A : Type) (P : A -> Prop) (x : A) (y : A) . x = y -> P y -> P x.
Proof.
  intros A P x y e p.
  leibniz -> e in |- *.
  ipso p.
Qed.

Theorem tactics_all_delivers_leibniz_everywhere
  : forall (A : Type) (P : A -> Prop) (x : A) (y : A) . x = y -> P x -> P y.
Proof.
  intros A P x y e p.
  leibniz e in *.
  ipso p.
Qed.

Theorem tactics_all_delivers_leibniz_as_a_name
  : forall (A : Prop) . A -> A.
Proof.
  intros A leibniz.
  ipso leibniz.
Qed.

Theorem tactics_all_delivers_modus_ponens
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  ipso (modus ponens hab, ha).
Qed.

Theorem tactics_all_delivers_modus_ponens_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B /\ C) -> A -> B.
Proof.
  intros A B C hab ha.
  modus ponens hab, ha as [b c].
  ipso b.
Qed.

Theorem tactics_all_delivers_modus_ponendo_ponens
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  ipso (modus ponendo ponens hab, ha).
Qed.

Theorem tactics_all_delivers_modus_ponendo_ponens_as
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponendo ponens hab, ha as h.
  ipso h.
Qed.

Theorem tactics_all_delivers_modus_ponens_implicit
  : forall (m : Nat) (n : Nat) . Nat.compare m n = Comparison.Lt -> Nat.LessThan m n.
Proof.
  intros m n c.
  modus ponens Nat.comparison.strict.forward.specification, c as h.
  ipso h.
Qed.

Theorem tactics_all_delivers_modus_ponens_implicit_as_a_term
  : forall (m : Nat) (n : Nat) . Nat.compare m n = Comparison.Lt -> Nat.LessThan m n.
Proof.
  intros m n c.
  ipso (modus ponens Nat.comparison.strict.forward.specification, c).
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_short
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  ipso (hs hab, hbc).
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_short_nested
  : forall (A : Prop) (B : Prop) (C : Prop) (D : Prop) .
      (A -> B) -> (B -> C) -> (C -> D) -> (A -> D).
Proof.
  intros A B C D hab hbc hcd.
  ipso (hs (hs hab, hbc), hcd).
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_short_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  hs hab, hbc as hac.
  ipso hac.
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  ipso (hypothetical syllogism hab, hbc).
Qed.

Theorem tactics_all_delivers_hypothetical_syllogism_as
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C hab hbc.
  hypothetical syllogism hab, hbc as hac.
  ipso hac.
Qed.

Theorem tactics_all_delivers_simpl_definition
  : forall (A : Prop) . ~ A -> ~ A -> A -> Falsum.
Proof.
  intros A na1 na2 a.
  simpl (~ _) in na1, na2.
  ipso (na1 a).
Qed.

Theorem tactics_all_delivers_simpl_definition_and_goal
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  simpl (~ _) in na |- *.
  ipso na.
Qed.

Theorem tactics_all_delivers_simpl_goal
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  simpl (~ _) in |- *.
  intro na.
  ipso (na a).
Qed.

Theorem tactics_all_delivers_simpl_first_occurrence
  : forall (A : Prop) . ~ A /\ ~ A -> (A -> Falsum) /\ ~ A.
Proof.
  intros A h.
  simpl (~ _) at 1 in h.
  lazy_match! Constr.type &h with
  | (A -> Falsum) /\ ~ A => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_second_occurrence
  : forall (A : Prop) . ~ A /\ ~ A -> ~ A /\ (A -> Falsum).
Proof.
  intros A h.
  simpl (~ _) at 2 in h.
  lazy_match! Constr.type &h with
  | ~ A /\ (A -> Falsum) => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_occurrence_in_goal
  : forall (A : Prop) . ~ A /\ ~ A -> ~ A /\ ~ A.
Proof.
  intros A h.
  simpl (~ _) at 2 in |- *.
  lazy_match! goal with
  | [ |- ~ A /\ (A -> Falsum) ] => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_four_definitions
  : forall (m : NatWithZero) (n : NatWithZero) .
      NatWithZero.Even m /\ NatWithZero.Odd n
      /\ NatWithZero.Divides m n /\ NatWithZero.LessThan m n
      -> NatWithZero.Even m /\ NatWithZero.Odd n
         /\ NatWithZero.Divides m n /\ NatWithZero.LessThan m n.
Proof.
  intros m n e.
  simpl NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan in e.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_ten_definitions
  : forall (m : NatWithZero) (n : NatWithZero) .
      NatWithZero.Even m /\ NatWithZero.Odd n
      /\ NatWithZero.Divides m n /\ NatWithZero.LessThan m n
      /\ NatWithZero.LessOrEqual m n /\ NatWithZero.add m n = NatWithZero.mul m n
      /\ NatWithZero.sub m n = None /\ NatWithZero.le m n = true /\ NatWithZero.min m n = m
      -> NatWithZero.Even m /\ NatWithZero.Odd n
         /\ NatWithZero.Divides m n /\ NatWithZero.LessThan m n
         /\ NatWithZero.LessOrEqual m n /\ NatWithZero.add m n = NatWithZero.mul m n
         /\ NatWithZero.sub m n = None /\ NatWithZero.le m n = true /\ NatWithZero.min m n = m.
Proof.
  intros m n e.
  simpl NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan, NatWithZero.LessOrEqual, NatWithZero.add,
      NatWithZero.mul, NatWithZero.sub, NatWithZero.le, NatWithZero.min in e.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_everywhere
  : forall (A : Prop) . ~ A -> A -> Falsum.
Proof.
  intros A na a.
  simpl (~ _) in *.
  ipso (na a).
Qed.

Theorem tactics_all_delivers_simpl_reduction_everywhere
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.add Nat.One m = n.
Proof.
  intros m n e.
  simpl in *.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_reduction
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.add Nat.One m = n.
Proof.
  intros m n e.
  simpl in e |- *.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_reduction_goal
  : forall (m : Nat) . Nat.add Nat.One m = Nat.add Nat.One m.
Proof.
  intro m.
  simpl in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_simpl_term
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.Successor m = n.
Proof.
  intros m n e.
  leibniz <- (simpl &e) in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_simpl_term_as_hypothesis
  : forall (m : Nat) (n : Nat) . Nat.add Nat.One m = n -> Nat.Successor m = n.
Proof.
  intros m n e.
  let proof f := simpl &e.
  leibniz <- &f in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_barbara
  : forall (A : Type) (S : A -> Prop) (M : A -> Prop) (P : A -> Prop) .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . S x -> P x).
Proof.
  intros A S M P mp sm.
  ipso (barbara mp, sm).
Qed.

Theorem tactics_all_delivers_barbara_as
  : forall (A : Type) (S : A -> Prop) (M : A -> Prop) (P : A -> Prop) .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . S x -> P x).
Proof.
  intros A S M P mp sm.
  barbara mp, sm as sp.
  ipso sp.
Qed.

Theorem tactics_all_delivers_barbara_nested
  : forall (A : Type) (R : A -> Prop) (S : A -> Prop) (M : A -> Prop)
      (P : A -> Prop) .
      (forall (x : A) . M x -> P x) ->
      (forall (x : A) . S x -> M x) ->
      (forall (x : A) . R x -> S x) ->
      (forall (x : A) . R x -> P x).
Proof.
  intros A R S M P mp sm rs.
  ipso (barbara (barbara mp, sm), rs).
Qed.

Theorem tactics_all_delivers_modus_tollens
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  ipso (modus tollens hab, hnb).
Qed.

Theorem tactics_all_delivers_modus_tollens_as
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollens &hab, &hnb as na.
  ipso &na.
Qed.

Theorem tactics_all_delivers_modus_tollendo_tollens
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollendo tollens hab, hnb as na.
  ipso na.
Qed.

Theorem tactics_all_delivers_modus_tollendo_tollens_as_a_term
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  ipso (modus tollendo tollens &hab, &hnb).
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ A -> B.
Proof.
  intros A B hor hna.
  ipso (modus tollendo ponens hor, hna).
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_as
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ A -> B.
Proof.
  intros A B hor hna.
  modus tollendo ponens hor, hna as b.
  ipso b.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_right
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ B -> A.
Proof.
  intros A B hor hnb.
  ipso (modus tollendo ponens hor, hnb).
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> A -> ~ B.
Proof.
  intros A B hn ha.
  ipso (modus ponendo tollens hn, ha).
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_right
  : forall (A : Prop) (B : Prop) . ~ (A /\ B) -> B -> ~ A.
Proof.
  intros A B hn hb.
  ipso (modus ponendo tollens hn, hb).
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_sejunction_right
  : forall (A : Prop) (B : Prop) . A _\/_ B -> B -> ~ A.
Proof.
  intros A B exclusion hb.
  modus ponendo tollens exclusion, hb as na.
  ipso na.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_sejunction
  : forall (A : Prop) (B : Prop) . A _\/_ B -> A -> ~ B.
Proof.
  intros A B exclusion ha.
  modus ponendo tollens exclusion, ha as nb.
  ipso nb.
Qed.

Theorem tactics_all_delivers_modus_aequans
  : forall (A : Prop) (B : Prop) . (A <-> B) -> A -> B.
Proof.
  intros A B hab ha.
  ipso (modus aequans hab, ha).
Qed.

Theorem tactics_all_delivers_modus_aequans_backward
  : forall (A : Prop) (B : Prop) . (A <-> B) -> B -> A.
Proof.
  intros A B hab hb.
  ipso (modus aequans hab, hb).
Qed.

Theorem tactics_all_delivers_modus_aequans_as
  : forall (A : Prop) (B : Prop) . (A <-> B) -> B -> A.
Proof.
  intros A B hab hb.
  modus aequans hab, hb as a.
  ipso a.
Qed.

Theorem tactics_all_delivers_modus_ponens_turnstile
  : forall (A : Prop) (B : Prop) (C : Prop) . (A -> B /\ C) -> A -> B.
Proof.
  intros A B C hab ha.
  modus ponens hab, ha |- [b c].
  ipso b.
Qed.

Theorem tactics_all_delivers_modus_ponens_implicit_turnstile
  : forall (m : Nat) (n : Nat) . Nat.compare m n = Comparison.Lt -> Nat.LessThan m n.
Proof.
  intros m n c.
  modus ponens Nat.comparison.strict.forward.specification, c |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_ponendo_ponens_turnstile
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab ha.
  modus ponendo ponens hab, ha |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_tollens_turnstile
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollens hab, hnb |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_tollendo_tollens_turnstile
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollendo tollens hab, hnb |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_turnstile
  : forall (A : Prop) (B : Prop) . A \/ B -> ~ B -> A.
Proof.
  intros A B hor hnb.
  modus tollendo ponens hor, hnb |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_turnstile
  : forall (A : Prop) (B : Prop) . A _\/_ B -> B -> ~ A.
Proof.
  intros A B exclusion hb.
  modus ponendo tollens exclusion, hb |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_aequans_turnstile
  : forall (A : Prop) (B : Prop) . (A <-> B) -> B -> A.
Proof.
  intros A B hab hb.
  modus aequans hab, hb |- facto.
  ipso facto.
Qed.

Theorem tactics_all_delivers_modus_tollendo_ponens_refusing
  : forall (A : Prop) (B : Prop) (C : Prop) . A \/ B -> C -> C.
Proof.
  intros A B C h c.
  Fail modus tollendo ponens &h, &c |- d.
  Fail let proof d := modus tollendo ponens &h, &c.
  ipso &c.
Qed.

Theorem tactics_all_delivers_modus_ponendo_tollens_refusing
  : forall (A : Prop) (B : Prop) (C : Prop) . ~ (A /\ B) -> C -> C.
Proof.
  intros A B C h c.
  Fail modus ponendo tollens &h, &c |- d.
  Fail let proof d := modus ponendo tollens &h, &c.
  ipso &c.
Qed.

Theorem tactics_all_delivers_modus_aequans_refusing
  : forall (A : Prop) (B : Prop) (C : Prop) . (A <-> B) -> C -> C.
Proof.
  intros A B C h c.
  Fail modus aequans &h, &c |- d.
  Fail let proof d := modus aequans &h, &c.
  ipso &c.
Qed.

Theorem tactics_all_delivers_quod_idem_est
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  quod idem est.
Qed.

Theorem tactics_all_delivers_quod_idem_est_refusing_sides_that_only_compute_alike
  : Nat.add Nat.One Nat.One = Nat.Successor Nat.One.
Proof.
  Fail quod idem est.
  simpl in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_quod_idem_est_refusing_what_is_no_equation
  : Verum.
Proof.
  Fail quod idem est.
  ipso I.
Qed.

Theorem tactics_all_delivers_divide_et_impera
  : forall (A : Prop) (B : Prop) . A -> B -> A /\ B.
Proof.
  intros A B a b.
  divide et impera.
  - ipso &a.
  - ipso &b.
Qed.

Theorem tactics_all_delivers_divide_et_impera_biconditional
  : forall (A : Prop) . A <-> A.
Proof.
  intro A.
  divide et impera.
  - intro a.
    ipso &a.
  - intro a.
    ipso &a.
Qed.

Theorem tactics_all_delivers_ex_quodlibet
  : forall (A : Prop) . Falsum -> A.
Proof.
  intros A f.
  ex &f quodlibet.
Qed.

Theorem tactics_all_delivers_ex_quodlibet_constructor_clash
  : forall (A : Prop) . Bool.true = Bool.false -> A.
Proof.
  intros A e.
  ex &e quodlibet.
Qed.

Theorem tactics_all_delivers_ex_quodlibet_refusing_a_negation
  : forall (A : Prop) (B : Prop) . ~ A -> A -> B.
Proof.
  intros A B na a.
  Fail ex &na quodlibet.
  ex (&na &a) quodlibet.
Qed.

Theorem tactics_all_delivers_ex_quodlibet_refusing_a_function
  : forall (A : Prop) (B : Prop) . (A -> Falsum) -> A -> B.
Proof.
  intros A B f a.
  Fail ex &f quodlibet.
  ex (&f &a) quodlibet.
Qed.

Theorem tactics_all_delivers_ex_quodlibet_refusing_what_only_computes_to_a_clash
  : forall (A : Prop) . Bool.negate Bool.true = Bool.true -> A.
Proof.
  intros A e.
  Fail ex &e quodlibet.
  simpl in &e.
  ex &e quodlibet.
Qed.

Theorem tactics_all_delivers_lemma
  : forall (A : Prop) (B : Prop) . A -> (A -> B) -> B.
Proof.
  intros A B a hab.
  lemma b : &B.
  {
    ipso (&hab &a).
  }
  ipso &b.
Qed.

Theorem tactics_all_delivers_lemma_refusing_a_name_in_use
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  Fail lemma a : &A.
  ipso &a.
Qed.

Theorem tactics_all_delivers_mv
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  mv &a b.
  ipso &b.
Qed.

Theorem tactics_all_delivers_mv_refusing
  : forall (A : Prop) (B : Prop) . A -> B -> A.
Proof.
  intros A B a b.
  Fail mv &c d.
  Fail mv &a b.
  ipso &a.
Qed.

Theorem tactics_all_delivers_rm
  : forall (A : Prop) (B : Prop) (C : Prop) . A -> B -> C -> A.
Proof.
  intros A B C a b c.
  rm &b &c.
  Fail rm &b.
  ipso &a.
Qed.

Theorem tactics_all_delivers_rm_refusing
  : forall (n : Nat) . n = n -> n = n.
Proof.
  intros n e.
  Fail rm &n.
  Fail rm &e &x.
  ipso &e.
Qed.

Theorem tactics_all_delivers_rm_refusing_a_dependent_left_behind
  : forall (n : Nat) (e : n = n) (A : Prop) . A -> A.
Proof.
  intros n e A a.
  Fail rm &n.
  rm &n &e.
  ipso &a.
Qed.

Theorem tactics_all_delivers_rm_force
  : forall (n : Nat) (e : n = n) (A : Prop) . A -> A.
Proof.
  intros n e A a.
  rm -f &n.
  rm &e &n.
  ipso &a.
Qed.

Theorem tactics_all_delivers_rm_recursive
  : forall (n : Nat) (e : n = n) (A : Prop) . A -> A.
Proof.
  intros n e A a.
  rm -r &n.
  Fail rm &e.
  ipso &a.
Qed.

Theorem tactics_all_delivers_rm_recursive_refusing_what_the_goal_depends_on
  : forall (n : Nat) . n = n.
Proof.
  intro n.
  Fail rm -r &n.
  quod idem est.
Qed.

Theorem tactics_all_delivers_extro
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  extro &a.
  lazy_match! goal with
  | [ |- A -> A ] => ()
  end.
  intro a.
  ipso &a.
Qed.

Theorem tactics_all_delivers_extros
  : forall (n : Nat) . n = n -> n = n.
Proof.
  intros n e.
  extros &n &e.
  lazy_match! goal with
  | [ |- forall (m : Nat) . m = m -> m = m ] => ()
  end.
  intros n e.
  ipso &e.
Qed.

Theorem tactics_all_delivers_extro_of_a_definition
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  let k := m.
  extro &k.
  lazy_match! goal with
  | [ |- let k := m in m = m ] => ()
  end.
  intro k.
  quod idem est.
Qed.

Theorem tactics_all_delivers_extros_refusing
  : forall (n : Nat) . n = n -> n = n.
Proof.
  intros n e.
  Fail extros &e &n.
  Fail extro &n.
  Fail extro &x.
  ipso &e.
Qed.

Theorem tactics_all_delivers_match
  : forall (A : Prop) (B : Prop) . A \/ B -> B \/ A.
Proof.
  intros A B h.
  match &h with | a | b end.
  - ipso (disjoin _, &a).
  - ipso (disjoin &b, _).
Qed.

Theorem tactics_all_delivers_match_named
  : forall (n : Nat) . n = n.
Proof.
  intro n.
  match &n with | One | Successor n' end.
  - quod idem est.
  - quod idem est.
Qed.

Theorem tactics_all_delivers_match_without_names
  : forall (b : Bool) . b = b.
Proof.
  intro b.
  match &b with end.
  - quod idem est.
  - quod idem est.
Qed.

Theorem tactics_all_delivers_match_with_an_equation
  : forall (b : Bool) . Bool.negate b = Bool.negate b.
Proof.
  intro b.
  match (Bool.negate &b) with | | end |- e.
  - lazy_match! Constr.type &e with
    | Bool.negate b = Bool.true => quod idem est
    end.
  - lazy_match! Constr.type &e with
    | Bool.negate b = Bool.false => quod idem est
    end.
Qed.

Theorem tactics_all_delivers_match_refusing
  : forall (A : Prop) (B : Prop) (C : Prop) . A /\ (B /\ C) -> C.
Proof.
  intros A B C h.
  Fail match &h with | a [b c] end.
  match &h with | a bc end.
  match &bc with | b c end.
  ipso &c.
Qed.

Theorem tactics_all_delivers_match_refusing_named_branches_out_of_order
  : forall (n : Nat) . n = n.
Proof.
  intro n.
  Fail match &n with | Successor n' | One end.
  Fail match &n with | One | n' end.
  quod idem est.
Qed.

Theorem tactics_all_delivers_match_per
  : forall (P : Nat -> Prop) .
      P Nat.One -> (forall (n : Nat) . P n -> P (Nat.Successor n)) -> forall (n : Nat) . P n.
Proof.
  intros P base step n.
  match &n with | | n' by IH end per Nat.induction.
  - ipso &base.
  - ipso (&step &n' &IH).
Qed.

Theorem tactics_all_delivers_match_per_named
  : forall (P : Nat -> Prop) .
      P Nat.One -> (forall (n : Nat) . P n -> P (Nat.Successor n)) -> forall (n : Nat) . P n.
Proof.
  intros P base step n.
  match &n with | One | Successor (n' by IH) end per Nat.induction.
  - ipso &base.
  - ipso (&step &n' &IH).
Qed.

Theorem tactics_all_delivers_match_per_dropping_the_hypothesis
  : forall (n : Nat) . n = n.
Proof.
  intro n.
  match &n with | | n' by _ end per Nat.induction.
  - quod idem est.
  - quod idem est.
Qed.

Theorem tactics_all_delivers_match_per_for
  : forall (P : Nat -> Prop) .
      P Nat.One -> (forall (n : Nat) . P n -> P (Nat.Successor n)) -> forall (n : Nat) . P n.
Proof.
  intros P base step n.
  match &n with | | n' by IH end per Nat.induction for (fun (m : Nat) . &P m).
  - ipso &base.
  - ipso (&step &n' &IH).
Qed.

Theorem tactics_all_delivers_match_per_refusing
  : forall (n : Nat) . n = n.
Proof.
  intro n.
  Fail match &n with | | n' end per Nat.induction.
  Fail match &n with | | n' by IH end.
  Fail match &n with | | n' by IH end per Nat.induction for (fun (m : Nat) . m = Nat.One).
  Fail match &n with | | n' by IH end per Nat.induction |- e.
  quod idem est.
Qed.

Theorem tactics_all_delivers_match_per_refusing_by_on_a_value
  : forall (A : Type) (l : List A) . l = l.
Proof.
  intros A l.
  Fail match &l with | | (a by IH) (l' by IH') end per List.induction.
  quod idem est.
Qed.

Theorem tactics_all_delivers_let_in
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k := Nat.add &m &m in |- *.
  lazy_match! goal with
  | [ |- k = k ] => quod idem est
  end.
Qed.

Theorem tactics_all_delivers_let_in_hypothesis_and_goal
  : forall (m : Nat) (P : Nat -> Prop) . P (Nat.add m m) -> P (Nat.add m m).
Proof.
  intros m P p.
  let k := Nat.add &m &m in &p |- *.
  lazy_match! Constr.type &p with
  | P k => ipso &p
  end.
Qed.

Theorem tactics_all_delivers_let_in_everywhere
  : forall (m : Nat) (P : Nat -> Prop) . P (Nat.add m m) -> P (Nat.add m m).
Proof.
  intros m P p.
  let k : Nat := Nat.add &m &m in *.
  lazy_match! goal with
  | [ _ : P k |- P k ] => ipso &p
  end.
Qed.

Theorem tactics_all_delivers_let_at
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k := Nat.add &m &m at 2 in |- *.
  lazy_match! goal with
  | [ |- Nat.add m m = k ] => ()
  end.
  simpl &k in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_let_fold
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k := Nat.add &m &m.
  let &k in |- *.
  lazy_match! goal with
  | [ |- k = k ] => quod idem est
  end.
Qed.

Theorem tactics_all_delivers_let_refusing
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  Fail let k := Nat.add &m &m in |- *.
  Fail let k := &m at 3 in |- *.
  Fail let &m in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_simpl_refusing
  : forall (A : Prop) (m : Nat) . A -> m = m.
Proof.
  intros A m a.
  Fail simpl (~ _) in |- *.
  Fail simpl (~ _) in &a.
  Fail simpl in |- *.
  Fail simpl in &x.
  Fail let proof b := simpl &a.
  let k := &m.
  Fail simpl k in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_leibniz_list
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> n = p -> m = p.
Proof.
  intros m n p e f.
  leibniz &e, <- &f in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_leibniz_refusing_a_law_waiting_for_arguments
  : forall (m : Nat) (n : Nat) . Nat.add m n = Nat.add n m.
Proof.
  intros m n.
  Fail leibniz Nat.addition.commutativity in |- *.
  leibniz (Nat.addition.commutativity &m &n) in |- *.
  quod idem est.
Qed.

Theorem tactics_all_delivers_symm
  : forall (m : Nat) (n : Nat) . m = n -> n = m.
Proof.
  intros m n e.
  ipso (symm &e).
Qed.

Theorem tactics_all_delivers_symm_as
  : forall (m : Nat) (n : Nat) . m = n -> n = m.
Proof.
  intros m n e.
  symm &e as f.
  ipso &f.
Qed.

Theorem tactics_all_delivers_symm_turnstile
  : forall (m : Nat) (n : Nat) . m = n -> n = m.
Proof.
  intros m n e.
  symm &e |- f.
  ipso &f.
Qed.

Theorem tactics_all_delivers_symm_in_hypothesis
  : forall (m : Nat) (n : Nat) . m = n -> n = m.
Proof.
  intros m n e.
  symm in &e.
  ipso &e.
Qed.

Theorem tactics_all_delivers_symm_in_goal
  : forall (m : Nat) (n : Nat) . m = n -> n = m.
Proof.
  intros m n e.
  symm in |- *.
  ipso &e.
Qed.

Theorem tactics_all_delivers_symm_in_hypothesis_and_goal
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> n = p -> m = n.
Proof.
  intros m n p e f.
  symm in &e, &f |- *.
  ipso &e.
Qed.

Theorem tactics_all_delivers_symm_refusing
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  Fail symm in &a.
  Fail symm in |- *.
  Fail symm &a as b.
  ipso &a.
Qed.

Theorem tactics_all_delivers_trans
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> n = p -> m = p.
Proof.
  intros m n p e f.
  ipso (trans &e, &f).
Qed.

Theorem tactics_all_delivers_trans_as
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> n = p -> m = p.
Proof.
  intros m n p e f.
  trans &e, &f as g.
  ipso &g.
Qed.

Theorem tactics_all_delivers_trans_turnstile
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> n = p -> m = p.
Proof.
  intros m n p e f.
  trans &e, &f |- g.
  ipso &g.
Qed.

Theorem tactics_all_delivers_trans_refusing
  : forall (m : Nat) (n : Nat) (p : Nat) . m = n -> p = n -> m = n.
Proof.
  intros m n p e f.
  Fail trans &e, &f as g.
  ipso &e.
Qed.

Theorem tactics_all_delivers_congru
  : forall (A : Type) (B : Type) (f : A -> B) (x : A) (y : A) . x = y -> f x = f y.
Proof.
  intros A B f x y e.
  ipso (congru &f, &e).
Qed.

Theorem tactics_all_delivers_congru_as
  : forall (A : Type) (B : Type) (f : A -> B) (x : A) (y : A) . x = y -> f x = f y.
Proof.
  intros A B f x y e.
  congru &f, &e as g.
  ipso &g.
Qed.

Theorem tactics_all_delivers_congru_turnstile
  : forall (A : Type) (B : Type) (f : A -> B) (x : A) (y : A) . x = y -> f x = f y.
Proof.
  intros A B f x y e.
  congru &f, &e |- g.
  ipso &g.
Qed.

Theorem tactics_all_delivers_congru_with_implicit_arguments
  : forall (A : Type) (B : Type) (p : Product A B) (q : Product A B) .
      p = q -> Product.first p = Product.first q.
Proof.
  intros A B p q e.
  congru Product.first, &e |- g.
  ipso &g.
Qed.

Theorem tactics_all_delivers_congru_refusing
  : forall (A : Type) (B : Type) (C : Prop) (f : A -> B) (x : A) (b : B) .
      C -> x = x -> b = b -> C.
Proof.
  intros A B C f x b c ex eb.
  Fail congru &f, &c |- g.
  Fail congru &f, &eb |- g.
  Fail congru &f, &ex |- c.
  ipso &c.
Qed.

Theorem tactics_all_delivers_exists
  : forall (A : Type) (P : A -> Prop) (a : A) . P a -> forsome (x : A) . P x.
Proof.
  intros A P a p.
  exists &a.
  ipso &p.
Qed.

Theorem tactics_all_delivers_exists_two
  : forall (A : Type) (Q : A -> A -> Prop) (a : A) (b : A) .
      Q a b -> forsome (x : A) (y : A) . Q x y.
Proof.
  intros A Q a b q.
  exists &a, &b.
  ipso &q.
Qed.

Theorem tactics_all_delivers_exists_refusing
  : forall (A : Type) (P : A -> Prop) (a : A) . P a -> forsome (x : A) . P x.
Proof.
  intros A P a p.
  Fail exists Nat.One.
  exists &a.
  Fail exists &a.
  ipso &p.
Qed.

Theorem tactics_all_delivers_conjoin_turnstile
  : forall (A : Prop) (B : Prop) . A -> B -> A /\ B.
Proof.
  intros A B a b.
  conjoin &a, &b |- c.
  ipso &c.
Qed.

Theorem tactics_all_delivers_disjoin
  : forall (A : Prop) (B : Prop) . A -> A \/ B.
Proof.
  intros A B a.
  ipso (disjoin &a, _).
Qed.

Theorem tactics_all_delivers_disjoin_right
  : forall (A : Prop) (B : Prop) . B -> A \/ B.
Proof.
  intros A B b.
  ipso (disjoin _, &b).
Qed.

Theorem tactics_all_delivers_sejoin
  : forall (A : Prop) (B : Prop) . A -> ~ B -> A _\/_ B.
Proof.
  intros A B a nb.
  ipso (sejoin &a, &nb).
Qed.

Theorem tactics_all_delivers_sejoin_right
  : forall (A : Prop) (B : Prop) . ~ A -> B -> A _\/_ B.
Proof.
  intros A B na b.
  ipso (sejoin &na, &b).
Qed.

Theorem tactics_all_delivers_sejoin_turnstile
  : forall (A : Prop) (B : Prop) . A -> ~ B -> A _\/_ B.
Proof.
  intros A B a nb.
  sejoin &a, &nb |- s.
  ipso &s.
Qed.

Theorem tactics_all_delivers_sejoin_refusing
  : forall (A : Prop) (B : Prop) . A -> B -> A.
Proof.
  intros A B a b.
  Fail sejoin &a, &b |- s.
  ipso &a.
Qed.

Theorem tactics_all_delivers_abjoin
  : forall (A : Prop) (B : Prop) . A -> ~ B -> A -/> B.
Proof.
  intros A B a nb.
  ipso (abjoin &a, &nb).
Qed.

Theorem tactics_all_delivers_abjoin_turnstile
  : forall (A : Prop) (B : Prop) . A -> ~ B -> A -/> B.
Proof.
  intros A B a nb.
  abjoin &a, &nb |- s.
  ipso &s.
Qed.

Module strict.

Ltac2 Set Local.checking := Strict.

Theorem tactics_all_delivers_strict_checking
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  Fail ipso a.
  Fail let proof b : A := &a.
  let proof b : &A := &a.
  ipso &b.
Qed.

Theorem tactics_all_delivers_strict_checking_sparing_facto
  : forall (A : Prop) . A -> A.
Proof.
  intros A a.
  lemma facto : &A.
  {
    ipso &a.
  }
  mv facto b.
  lemma facto : &A.
  {
    ipso &b.
  }
  ipso facto.
Qed.

End strict.
