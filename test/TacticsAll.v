(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.All.
From jwa Require Import Tactics.All.

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
  : forall (A : Type) (P : A -> Prop) . ~ (exists (x : A) . P x) -> forall (x : A) . ~ P x.
Proof.
  intros A P h.
  ipso (de morgan h).
Qed.

Theorem tactics_all_delivers_de_morgan_existential_as
  : forall (A : Type) (P : A -> Prop) (a : A) . ~ (exists (x : A) . P x) -> ~ P a.
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
  lazymatch type of h with
  | ~ A /\ ~ B => destruct h as [na nb]
  end.
  ipso nb.
Qed.

Theorem tactics_all_delivers_de_morgan_in_goal
  : forall (A : Type) (P : A -> Prop) . (forall (x : A) . ~ P x) -> ~ (exists (x : A) . P x).
Proof.
  intros A P h.
  de morgan in |- *.
  lazymatch goal with
  | |- forall (x : A) . ~ P x => ipso h
  end.
Qed.

Theorem tactics_all_delivers_de_morgan_in_hypothesis_and_goal
  : forall (A : Prop) (B : Prop) . ~ (A \/ B) -> ~ (A \/ B).
Proof.
  intros A B h.
  de morgan in h |- *.
  ipso h.
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
  lazymatch type of a with
  | ~ ~ A => ipso a
  end.
Qed.

Theorem tactics_all_delivers_dni_in_goal
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  dni in |- *.
  lazymatch goal with
  | |- A => ipso a
  end.
Qed.

Theorem tactics_all_delivers_dni_in_hypothesis_and_goal
  : forall (A : Prop) . A -> ~ ~ ~ ~ A.
Proof.
  intros A a.
  dni in a |- *.
  ipso a.
Qed.

Theorem tactics_all_delivers_dne_in_hypothesis
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in nnna.
  lazymatch type of nnna with
  | ~ A => ipso nnna
  end.
Qed.

Theorem tactics_all_delivers_dne_in_goal
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in |- *.
  lazymatch goal with
  | |- ~ ~ ~ A => ipso nnna
  end.
Qed.

Theorem tactics_all_delivers_dne_in_hypothesis_and_goal
  : forall (A : Prop) . ~ ~ ~ A -> ~ A.
Proof.
  intros A nnna.
  dne in nnna |- *.
  ipso (dni nnna).
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
  lazymatch goal with
  | k := m |- _ => reflexivity
  end.
Qed.

Theorem tactics_all_delivers_let_of_an_application
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k := Nat.add m m.
  lazymatch goal with
  | k := Nat.add m m |- _ => reflexivity
  end.
Qed.

Theorem tactics_all_delivers_let_with_a_type
  : forall (m : Nat) . Nat.add m m = Nat.add m m.
Proof.
  intro m.
  let k : Nat := Nat.add m m.
  lazymatch goal with
  | k := Nat.add m m : Nat |- _ => reflexivity
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
  lazymatch type of facto with
  | B => ipso facto
  end.
Qed.

Theorem tactics_all_delivers_let_with_an_arrow_type
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  let k : A -> Falsum := na.
  lazymatch goal with
  | k := na : A -> Falsum |- _ => ipso k
  end.
Qed.

Theorem tactics_all_delivers_let_proof_retyping_a_hypothesis
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A h.
  let proof h : A -> Falsum := h.
  lazymatch type of h with
  | A -> Falsum => ipso h
  end.
Qed.

Theorem tactics_all_delivers_let_retyping_a_definition
  : forall (A : Prop) . ~ A -> ~ A.
Proof.
  intros A na.
  let k := na.
  let k : A -> Falsum := k.
  lazymatch goal with
  | k := na : A -> Falsum |- _ => ipso k
  end.
Qed.

Theorem tactics_all_delivers_let_proof_shadowing
  : forall (A : Prop) (B : Prop) . (A -> B) -> A -> B.
Proof.
  intros A B hab h.
  let proof h := hab h.
  lazymatch goal with
  | h : B |- _ => ipso h
  end.
Qed.

Theorem tactics_all_delivers_let_shadowing
  : forall (m : Nat) . m = m.
Proof.
  intro m.
  let k := Nat.add m m.
  let k := Nat.add k k.
  lazymatch goal with
  | k := Nat.add (Nat.add m m) (Nat.add m m) |- _ => idtac
  end.
  Fail lazymatch goal with
  | _ := Nat.add m m |- _ => idtac
  end.
  reflexivity.
Qed.

Theorem tactics_all_delivers_let_proof_dropping_a_body
  : forall (m : Nat) (n : Nat) .
      Nat.LessThan m n -> Nat.LessThan (Nat.add Nat.One m) (Nat.add Nat.One n).
Proof.
  intros m n h.
  let H := Nat.addition.order.monotonicity Nat.One m n h.
  let proof H := H.
  Fail lazymatch goal with
  | _ := _ |- _ => idtac
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
  Fail lazymatch goal with
  | _ := _ |- _ => idtac
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
  lazymatch goal with
  | H := _ |- _ => ipso facto
  end.
Qed.

Theorem tactics_all_delivers_let_proof_dropping_a_body_others_mention
  : forall (m : Nat) . Verum.
Proof.
  intro m.
  let k := Nat.add m m.
  lemma q : k = k.
  - reflexivity.
  - let proof k := k.
    Fail lazymatch goal with
    | _ := _ |- _ => idtac
    end.
    lazymatch goal with
    | q : k = k |- _ => ipso I
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
  ipso (Conjunction_introduction p q).
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
  simpl Negation in na1, na2.
  ipso (na1 a).
Qed.

Theorem tactics_all_delivers_simpl_definition_and_goal
  : forall (A : Prop) . ~ A -> A -> Falsum.
Proof.
  intros A na a.
  simpl Negation in na |- *.
  ipso (na a).
Qed.

Theorem tactics_all_delivers_simpl_goal
  : forall (A : Prop) . A -> ~ ~ A.
Proof.
  intros A a.
  simpl Negation in |- *.
  intro na.
  ipso (na a).
Qed.

Theorem tactics_all_delivers_simpl_first_occurrence
  : forall (A : Prop) . ~ A /\ ~ A -> (A -> Falsum) /\ ~ A.
Proof.
  intros A h.
  simpl Negation at 1 in h.
  lazymatch type of h with
  | (A -> Falsum) /\ ~ A => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_second_occurrence
  : forall (A : Prop) . ~ A /\ ~ A -> ~ A /\ (A -> Falsum).
Proof.
  intros A h.
  simpl Negation at 2 in h.
  lazymatch type of h with
  | ~ A /\ (A -> Falsum) => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_occurrence_in_goal
  : forall (A : Prop) . ~ A /\ ~ A -> ~ A /\ ~ A.
Proof.
  intros A h.
  simpl Negation at 2 in |- *.
  lazymatch goal with
  | |- ~ A /\ (A -> Falsum) => ipso h
  end.
Qed.

Theorem tactics_all_delivers_simpl_four_definitions
  : forall (m : NatWithZero) . NatWithZero.Even m -> NatWithZero.Even m.
Proof.
  intros m e.
  simpl NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan in e.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_ten_definitions
  : forall (m : NatWithZero) . NatWithZero.Even m -> NatWithZero.Even m.
Proof.
  intros m e.
  simpl NatWithZero.Even, NatWithZero.Odd, NatWithZero.Divides,
      NatWithZero.LessThan, NatWithZero.LessOrEqual, NatWithZero.add,
      NatWithZero.mul, NatWithZero.sub, NatWithZero.le, NatWithZero.min in e.
  ipso e.
Qed.

Theorem tactics_all_delivers_simpl_everywhere
  : forall (A : Prop) . ~ A -> A -> Falsum.
Proof.
  intros A na a.
  simpl Negation in *.
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
  reflexivity.
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

Theorem tactics_all_delivers_modus_tollendo_tollens
  : forall (A : Prop) (B : Prop) . (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B hab hnb.
  modus tollendo tollens hab, hnb as na.
  ipso na.
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
