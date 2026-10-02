(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Base.Bool.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Witness.

(* The bridge from a computed answer to a statement. [Assert true] is
 * [Verum] and [Assert false] is [Falsum] by reduction, so case analysis on
 * a [Bool] turns each law below into a concrete implication in both
 * directions.
 *)
(* [Bool -> Prop] *)
Definition Assert := fun (b : Bool) .
  match b with
  | true  => Verum
  | false => Falsum
  end.

(* The laws carry the name of what they are about, as a type's do; the
 * bridge itself is declared above them.
 *)
Module Assert. (* Assert *)

(* [&&], [||], [^^] and [!] are exported by [Data.Bool] into
 * [jwa_bool_scope], which every law below reads.
 *)
Local Open Scope jwa_bool_scope.

(* [Some (f I)] when [b] is [true], [None] otherwise: [f] is applied only
 * where its premise holds, so a value that needs a proof of [Assert b] is
 * built from a [b] computed at run time.
 *)
(* [forall {X : Type} (b : Bool) . (Assert b -> X) -> Option X] *)
Definition guard := fun {X : Type} (b : Bool) (f : Assert b -> X) .
  match b as r return (Assert r -> X) -> Option X with
  | true => fun (g : Assert true -> X) . Some (g I)
  | false => fun (_ : Assert false -> X) . None
  end f.

(* Assert.conjunction *)
Theorem conjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 && b2) <-> Assert b1 /\ Assert b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; divide et impera; intro h.
  - divide et impera; ipso I.
  - ipso I.
  - ex h quodlibet.
  - match h with | _ h end.
    ipso h.
  - ex h quodlibet.
  - match h with | h _ end.
    ipso h.
  - ex h quodlibet.
  - match h with | h _ end.
    ipso h.
Qed.

(* Assert.disjunction *)
Theorem disjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 || b2) <-> Assert b1 \/ Assert b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; divide et impera; intro h.
  - ipso (disjoin I, _).
  - ipso I.
  - ipso (disjoin I, _).
  - ipso I.
  - ipso (disjoin _, I).
  - ipso I.
  - ex h quodlibet.
  - match h with | h1 | h2 end.
    + ipso h1.
    + ipso h2.
Qed.

(* Assert.sejunction *)
Theorem sejunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 ^^ b2) <-> Assert b1 _\/_ Assert b2.
Proof.
  intros b1 b2.
  match b1 with | | end; match b2 with | | end; simpl in |- *; divide et impera; intro h.
  - ex h quodlibet.
  - match h with | t nt | nt t end; ipso (modus ponens nt, t).
  - ipso (sejoin I, (fun (f : Falsum) . f)).
  - ipso I.
  - ipso (sejoin (fun (f : Falsum) . f), I).
  - ipso I.
  - ex h quodlibet.
  - match h with | f _ | _ f end; ipso f.
Qed.

(* Assert.negation *)
Theorem negation
  : forall (b : Bool) . Assert (! b) <-> ~ Assert b.
Proof.
  intros b.
  simpl (~ _) in |- *.
  match b with | | end; simpl in |- *; divide et impera; intro h.
  - ex h quodlibet.
  - ipso (modus ponens h, I).
  - intro k.
    match k with end.
  - ipso I.
Qed.

(* Assert.specification *)
Theorem specification : forall (b : Bool) . Assert b <-> b = true.
Proof.
  intros b.
  match b with | | end; simpl in |- *; divide et impera; intro h.
  - quod idem est.
  - ipso I.
  - ex h quodlibet.
  - ex h quodlibet.
Qed.

(* Two proofs of one [Assert b] are equal: [Verum] has one, [Falsum] none. *)
(* Assert.uniqueness *)
Theorem uniqueness : forall (b : Bool) (p : Assert b) (q : Assert b) . p = q.
Proof.
  intros b p q.
  match &b with | | end.
  - simpl Assert in &p, &q.
    match &p with end.
    match &q with end.
    quod idem est.
  - simpl Assert in &p.
    ex &p quodlibet.
Qed.

Module guarding. (* Assert.guarding *)

(* Assert.guarding.evaluation *)
Theorem evaluation
  : forall {X : Type} (b : Bool) (f : Assert b -> X) (p : Assert b) . guard b f = Some (f p).
Proof.
  intros X b f p.
  match &b with | | end.
  - simpl guard in |- *.
    leibniz (uniqueness true &p I) in |- *.
    quod idem est.
  - simpl Assert in &p.
    ex &p quodlibet.
Qed.

(* Assert.guarding.inversion *)
Theorem inversion
  : forall {X : Type} (b : Bool) (f : Assert b -> X) (x : X) .
      guard b f = Some x -> forsome (p : Assert b) . f p = x.
Proof.
  intros X b f x h.
  match &b with | | end.
  - simpl guard in &h.
    exists I.
    ipso (Option.some.injectivity &h).
  - simpl guard in &h.
    ex &h quodlibet.
Qed.

End guarding. (* Assert.guarding *)

End Assert. (* Assert *)
