(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.AbelianGroup.
From jwa Require Import Algebra.Cancellative.
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Group.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Ring.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Base.Comparison.
From jwa Require Import Data.Comparable.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Dialect.ExFalso.
From jwa Require Import Dialect.Simpl.
From jwa Require Import Tactics.Modus.

Module Rational. (* Rational *)

(* A fraction in lowest terms, an [Integer] over a [Nat]: the denominator is
 * never zero by its type, and the two share no factor by the equation the
 * ctor demands. There is no unreduced inhabitant, so a law may speak of
 * every value and not only of what [make] returned.
 *)
Inductive T : Type :=
  | Rational_introduction
      : forall (n : Integer) (d : Nat) .
          NatWithZero.gcd.nat (Integer.abs n) d = Nat.One -> T.

Abbreviation Rational := T.

(* [Integer -> Nat -> Rational] *)
Definition make := fun (n : Integer) (d : Nat) .
  let n' := Integer.abs n
  in
  let g  := NatWithZero.gcd.nat n' d
  in
  let numerator   := Integer.divide n g
  in
  let denominator := NatWithZero.divide.nat.safe d g (NatWithZero.gcd.nat.right.divisibility n' d)
  in
  Rational_introduction numerator denominator (Integer.division.exhaustiveness n d).

(* [Rational -> Integer] *)
Definition numerator := fun (x : Rational) .
match x with
  | Rational_introduction n _ _ => n
end.

(* [Rational -> Nat] *)
Definition denominator := fun (x : Rational) .
match x with
  | Rational_introduction _ d _ => d
end.

(* [Rational] *)
Definition Zero :=
  Rational_introduction Integer.Zero Nat.One
    (NatWithZero.gcd.nat.zero
      (Integer.abs Integer.Zero)
      (Nat.One)
      ((Identity.reflexivity NatWithZero.Zero)
        : NatWithZero.modulo (Integer.abs Integer.Zero) Nat.One = NatWithZero.Zero)).

(* [Rational] *)
Definition One :=
  Rational_introduction (Integer.Positive Nat.One) Nat.One
    (NatWithZero.gcd.nat.zero
      (Integer.abs (Integer.Positive Nat.One))
      (Nat.One)
      ((Identity.reflexivity NatWithZero.Zero)
        : NatWithZero.modulo (Integer.abs (Integer.Positive Nat.One)) Nat.One = NatWithZero.Zero)).

(* [Rational -> Rational] *)
Definition negate := fun (x : Rational) .
  let n := Integer.negate (numerator x) in
  let d := denominator x in
  make n d.

(* [Rational -> Rational -> Rational] *)
Definition add := fun (x : Rational) (y : Rational) .
  let nx := numerator x in
  let ny := numerator y in
  let dx := denominator x in
  let dy := denominator y in
  let dx' := Integer.from_nat dx in
  let dy' := Integer.from_nat dy in
  let n := Integer.add (Integer.mul nx dy') (Integer.mul ny dx') in
  let d := Nat.mul dx dy in
  make n d.

Notation "x + y" := (add x y) (only parsing)
  : jwa_rational_scope.

(* [Rational -> Rational -> Rational] *)
Definition sub := fun (x : Rational) (y : Rational) . let y := negate y in add x y.

(* [Rational -> Rational -> Rational] *)
Definition mul := fun (x : Rational) (y : Rational) .
  let n := Integer.mul (numerator x) (numerator y)
  in
  let d := Nat.mul (denominator x) ( denominator y)
  in
  make n d.

Notation "x * y" := (mul x y) (only parsing)
  : jwa_rational_scope.

(* x/y -> y/x *)
(* [Rational -> Option Rational] *)
Definition inverse := fun (x : Rational) .
  let n := numerator   x in
  let d := denominator x in
  match n with
  | Integer.Negative n => let d := Integer.Negative d in Some (make d n)
  | Integer.Zero       => None
  | Integer.Positive n => let d := Integer.Positive d in Some (make d n)
  end.

(* [Rational -> Rational -> Prop] *)
Definition LessThan := fun (x : Rational) (y : Rational) .
  Integer.LessThan
    (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
    (Integer.mul (numerator y) (Integer.from_nat (denominator x))).

(* [Rational -> Rational -> Prop] *)
Definition LessOrEqual := fun (x : Rational) (y : Rational) .
  x = y \/ LessThan x y.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_rational_scope.
Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_rational_scope.
Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_rational_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_rational_scope.

(* [Rational -> Rational -> Comparison] *)
Definition compare := fun (x : Rational) (y : Rational) .
  Integer.compare
    (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
    (Integer.mul (numerator y) (Integer.from_nat (denominator x))).

(* [Integer -> Rational] *)
Definition from_integer := fun (n : Integer) . make n Nat.One.

Local Open Scope jwa_rational_scope.

Theorem extensionality
  : forall (x : Rational) (y : Rational) .
      numerator x = numerator y
      -> denominator x = denominator y
      -> x = y.
Proof.
  intros x y.
  match x with | n1 d1 h1 end.
  match y with | n2 d2 h2 end.
  simpl numerator, denominator in |- *.
  intros e1 e2.
  match e1 with end.
  match e2 with end.
  leibniz (Nat.equality.uniqueness
             (NatWithZero.gcd.nat (Integer.abs n1) d1) Nat.One h1 h2) in |- *.
  quod idem est.
Qed.

Theorem irreducibility
  : forall (x : Rational) .
      NatWithZero.gcd.nat (Integer.abs (numerator x)) (denominator x)
      = Nat.One.
Proof.
  intro x.
  match x with | n d h end.
  simpl numerator, denominator in |- *.
  ipso h.
Qed.


Module make. (* make *)

(* make.retraction *)
Theorem retraction
  : forall (x : Rational) . make (numerator x) (denominator x) = x.
Proof.
  intro x.
  match x with | n d h end.
  simpl numerator, denominator in |- *.

  lemma whole : Integer.divide n Nat.One = n.
  {
    let proof e := Integer.division.exactness
                  n Nat.One
                  (NatWithZero.divisibility.bottom (Integer.abs n)).
    let proof i := Integer.multiplication.right.identity
                  (Integer.divide n Nat.One).
    symmetry in i.
    ipso (Identity.transitivity i e).
  }

  lemma undivided : NatWithZero.divide (NatWithZero.Positive d) (Nat.One)
          = NatWithZero.Positive d.
  {
    let proof e := NatWithZero.division.exactness
                  (NatWithZero.Positive d) (Nat.One)
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d)).
    let proof i := NatWithZero.multiplication.right.identity
                  (NatWithZero.divide (NatWithZero.Positive d) (Nat.One)).
    symmetry in i.
    ipso (Identity.transitivity i e).
  }

  lemma same : NatWithZero.divide (NatWithZero.Positive d)
              (NatWithZero.gcd.nat (Integer.abs n) d)
          = NatWithZero.divide (NatWithZero.Positive d) (Nat.One).
  {
    leibniz h in |- *.
    quod idem est.
  }

  apply extensionality.
  - simpl make      in |- *.
    simpl numerator in |- *.
    leibniz h in |- *.
    ipso whole.
  - simpl make        in |- *.
    simpl denominator in |- *.
    let proof c := NatWithZero.divide.nat.safe.congruence
                  d (NatWithZero.gcd.nat (Integer.abs n) d)
                  (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)
                  d Nat.One
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d))
                  same.
    let proof s := NatWithZero.divide.nat.safe.specification
                  d Nat.One
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d)).
    leibniz undivided in s.
    let proof inj := NatWithZero.positive.injectivity s.
    ipso (Identity.transitivity c inj).
Qed.

(* make.invariance *)
Theorem invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      make (Integer.mul (Integer.Positive k) n) (Nat.mul k d) = make n d.
Proof.
  intros n d k.

  lemma common : NatWithZero.gcd.nat
              (Integer.abs (Integer.mul (Integer.Positive k) n))
              (Nat.mul k d)
          = Nat.mul k (NatWithZero.gcd.nat (Integer.abs n) d).
  {
    let proof am := Integer.multiplication.magnitude (Integer.Positive k) n.
    let proof am
      : Integer.abs (Integer.mul (Integer.Positive k) n)
        = NatWithZero.mul (NatWithZero.Positive k) (Integer.abs n)
      := &am.
    leibniz am in |- *.
    let proof gd := NatWithZero.gcd.nat.left.distributivity.of.multiplication
                  k d (Integer.abs n).
    symmetry in gd.
    ipso gd.
  }

  simpl make in |- *.

  lemma top : Integer.divide
              (Integer.mul (Integer.Positive k) n)
              (NatWithZero.gcd.nat
                (Integer.abs (Integer.mul (Integer.Positive k) n))
                (Nat.mul k d))
          = Integer.divide n (NatWithZero.gcd.nat (Integer.abs n) d).
  {
    leibniz common in |- *.
    ipso (Integer.division.invariance
             n (NatWithZero.gcd.nat (Integer.abs n) d) k).
  }

  lemma bottom : NatWithZero.divide.nat.safe
                (Nat.mul k d)
                (NatWithZero.gcd.nat
                  (Integer.abs (Integer.mul (Integer.Positive k) n))
                  (Nat.mul k d))
                (NatWithZero.gcd.nat.right.divisibility
                  (Integer.abs (Integer.mul (Integer.Positive k) n))
                  (Nat.mul k d))
          = NatWithZero.divide.nat.safe
                d
                (NatWithZero.gcd.nat (Integer.abs n) d)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d).
  {
    apply NatWithZero.divide.nat.safe.congruence.
    leibniz common in |- *.
    let proof inv := NatWithZero.division.invariance
                  (NatWithZero.Positive d)
                  (NatWithZero.gcd.nat (Integer.abs n) d) k.
    let proof inv
      : NatWithZero.divide
          (NatWithZero.Positive (Nat.mul k d))
          (Nat.mul k (NatWithZero.gcd.nat (Integer.abs n) d))
        = NatWithZero.divide (NatWithZero.Positive d) (NatWithZero.gcd.nat (Integer.abs n) d)
      := &inv.
    ipso inv.
  }

  apply extensionality.
  - simpl make      in |- *.
    simpl numerator in |- *.
    ipso top.
  - simpl make        in |- *.
    simpl denominator in |- *.
    ipso bottom.
Qed.

(* make.proportionality *)
Theorem proportionality
  : forall (a : Integer) (b : Nat) .
      Integer.mul (numerator (make a b)) (Integer.from_nat b)
      = Integer.mul a (Integer.from_nat (denominator (make a b))).
Proof.
  intros a b.
  simpl make in |- *.
  simpl numerator, denominator in |- *.

  lemma bottom : Nat.mul
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b))
              (NatWithZero.gcd.nat (Integer.abs a) b)
          = b.
  {
    let proof s := NatWithZero.divide.nat.safe.specification
                  b (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b).
    let proof e := NatWithZero.division.exactness
                  (NatWithZero.Positive b)
                  (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b).
    symmetry in s.
    leibniz s in e.
    ipso (NatWithZero.positive.injectivity e).
  }

  lemma lifted : Integer.from_nat b
          = Integer.mul
              (Integer.from_nat
                (NatWithZero.divide.nat.safe
                    b (NatWithZero.gcd.nat (Integer.abs a) b)
                    (NatWithZero.gcd.nat.right.divisibility
                      (Integer.abs a) b)))
              (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b)).
  {
    let proof c := Identity.congruence Integer.from_nat bottom.
    symmetry in c.
    leibniz c in |- *.
    quod idem est.
  }

  lemma whole : Integer.mul
              (Integer.divide a (NatWithZero.gcd.nat (Integer.abs a) b))
              (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b))
          = a.
  {
    ipso (Integer.division.exactness
            a (NatWithZero.gcd.nat (Integer.abs a) b)
            (NatWithZero.gcd.nat.left.divisibility (Integer.abs a) b)).
  }

  leibniz lifted in |- *.
  leibniz (Integer.multiplication.commutativity
            (Integer.from_nat
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b)))
            (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b)))
    in |- *.
  let proof assoc := Identity.symmetry
                (Integer.multiplication.associativity
                  (Integer.divide a (NatWithZero.gcd.nat (Integer.abs a) b))
                  (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b))
                  (Integer.from_nat
                    (NatWithZero.divide.nat.safe
                      b (NatWithZero.gcd.nat (Integer.abs a) b)
                      (NatWithZero.gcd.nat.right.divisibility
                        (Integer.abs a) b)))).
  leibniz assoc in |- *.
  leibniz whole in |- *.
  quod idem est.
Qed.

(* make.characterisation *)
Theorem characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      make a b = make c d
      <-> Integer.mul a (Integer.from_nat d)
        = Integer.mul c (Integer.from_nat b).
Proof.
  intros a b c d.

  lemma swap : forall (x : Integer) (y : Integer) (z : Integer) .
              Integer.mul (Integer.mul x y) z
              = Integer.mul (Integer.mul x z) y.
  {
    intros x y z.
    leibniz (Integer.multiplication.associativity x y z) in |- *.
    leibniz (Integer.multiplication.commutativity y z)   in |- *.
    let proof h := Identity.symmetry (Integer.multiplication.associativity x z y).
    leibniz h in |- *.
    quod idem est.
  }

  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.

  (* The third field is the irreducibility of each pair, handed over by the
   * case analysis rather than proved after it.
   *)
  match (make a b) per E1 with | p q I1 end.
  match (make c d) per E2 with | r s I2 end.
  simpl numerator, denominator in P1, P2.

  lemma nzq : ~ (Integer.from_nat q = Integer.Zero).
  {
    simpl (~ _) in |- *.
    intro z.
    ex z quodlibet.
  }

  lemma nzs : ~ (Integer.from_nat s = Integer.Zero).
  {
    simpl (~ _) in |- *.
    intro z.
    ex z quodlibet.
  }

  divide et impera.

  - intro e.
    let proof hp := Identity.congruence numerator   e.
    let proof hq := Identity.congruence denominator e.
    simpl numerator   in hp.
    simpl denominator in hq.
    leibniz hp in P1.
    leibniz hq in P1.

    lemma Q1 : Integer.mul (Integer.mul r (Integer.from_nat b))
                             (Integer.from_nat d)
                 = Integer.mul (Integer.mul a (Integer.from_nat s))
                               (Integer.from_nat d).
    {
      leibniz P1 in |- *.
      quod idem est.
    }

    lemma Q2 : Integer.mul (Integer.mul r (Integer.from_nat d))
                             (Integer.from_nat b)
                 = Integer.mul (Integer.mul c (Integer.from_nat s))
                               (Integer.from_nat b).
    {
      leibniz P2 in |- *.
      quod idem est.
    }

    leibniz (swap r (Integer.from_nat b) (Integer.from_nat d)) in Q1.
    symmetry in Q1.
    let proof Q := Identity.transitivity Q1 Q2.
    leibniz (swap a (Integer.from_nat s) (Integer.from_nat d)) in Q.
    leibniz (swap c (Integer.from_nat s) (Integer.from_nat b)) in Q.
    leibniz (Integer.multiplication.commutativity
              (Integer.mul a (Integer.from_nat d))
              (Integer.from_nat s)) in Q.
    leibniz (Integer.multiplication.commutativity
              (Integer.mul c (Integer.from_nat b))
              (Integer.from_nat s)) in Q.
    ipso (Integer.multiplication.cancellation
            (Integer.from_nat s) (Integer.mul a (Integer.from_nat d))
            (Integer.mul c (Integer.from_nat b)) nzs Q).

  - intro e.

    lemma nzbd : ~ (Integer.mul (Integer.from_nat b) (Integer.from_nat d)
            = Integer.Zero).
    {
      simpl (~ _) in |- *.
      intro z.
      ex z quodlibet.
    }

    lemma widened : Integer.mul (Integer.mul p (Integer.from_nat s))
                (Integer.mul (Integer.from_nat b) (Integer.from_nat d))
            = Integer.mul (Integer.mul r (Integer.from_nat q))
                (Integer.mul (Integer.from_nat b) (Integer.from_nat d)).
    {
      leibniz (Integer.multiplication.interchange
                p (Integer.from_nat s) (Integer.from_nat b) (Integer.from_nat d)) in |- *.
      leibniz P1 in |- *.
      leibniz (Integer.multiplication.commutativity (Integer.from_nat s) (Integer.from_nat d)) in |- *.
      leibniz (Integer.multiplication.interchange
                a (Integer.from_nat q) (Integer.from_nat d) (Integer.from_nat s)) in |- *.
      leibniz e in |- *.
      leibniz (Integer.multiplication.commutativity (Integer.from_nat q) (Integer.from_nat s)) in |- *.
      leibniz (Integer.multiplication.interchange
                c (Integer.from_nat b) (Integer.from_nat s) (Integer.from_nat q)) in |- *.
      let proof P2' := Identity.symmetry P2.
      leibniz P2' in |- *.
      leibniz (Integer.multiplication.commutativity (Integer.from_nat b) (Integer.from_nat q)) in |- *.
      leibniz (Integer.multiplication.interchange
                r (Integer.from_nat d) (Integer.from_nat q) (Integer.from_nat b)) in |- *.
      leibniz (Integer.multiplication.commutativity (Integer.from_nat d) (Integer.from_nat b)) in |- *.
      quod idem est.
    }

    leibniz (Integer.multiplication.commutativity
              (Integer.mul p (Integer.from_nat s))
              (Integer.mul (Integer.from_nat b)
                           (Integer.from_nat d))) in widened.
    leibniz (Integer.multiplication.commutativity
              (Integer.mul r (Integer.from_nat q))
              (Integer.mul (Integer.from_nat b)
                           (Integer.from_nat d))) in widened.
    let proof cross := Integer.multiplication.cancellation
                  (Integer.mul (Integer.from_nat b) (Integer.from_nat d))
                  (Integer.mul p (Integer.from_nat s))
                  (Integer.mul r (Integer.from_nat q))
                  nzbd widened.

    let proof m := Identity.congruence Integer.abs cross.
    leibniz (Integer.multiplication.magnitude p (Integer.from_nat s)) in m.
    leibniz (Integer.multiplication.magnitude r (Integer.from_nat q)) in m.
    let proof m
      : NatWithZero.mul (Integer.abs p) (NatWithZero.Positive s)
        = NatWithZero.mul (Integer.abs r) (NatWithZero.Positive q)
      := &m.

    lemma coprime1 : NatWithZero.gcd (NatWithZero.Positive q) (Integer.abs p)
            = NatWithZero.Positive Nat.One.
    {
      let proof g := NatWithZero.gcd.nat.specification q (Integer.abs p).
      leibniz I1 in g.
      leibniz (NatWithZero.gcd.commutativity
                (Integer.abs p) (NatWithZero.Positive q)) in g.
      ipso g.
    }

    lemma coprime2 : NatWithZero.gcd (NatWithZero.Positive s) (Integer.abs r)
            = NatWithZero.Positive Nat.One.
    {
      let proof g := NatWithZero.gcd.nat.specification s (Integer.abs r).
      leibniz I2 in g.
      leibniz (NatWithZero.gcd.commutativity (Integer.abs r)
                 (NatWithZero.Positive s)) in g.
      ipso g.
    }

    lemma qs : NatWithZero.Divides (NatWithZero.Positive q) (NatWithZero.Positive s).
    {
      let proof h := NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive q) (NatWithZero.Positive q)
                    (Integer.abs r)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive q)).
      leibniz (NatWithZero.multiplication.commutativity
                (NatWithZero.Positive q) (Integer.abs r)) in h.
      let proof m' := Identity.symmetry m.
      leibniz m' in h.
      ipso (NatWithZero.gcd.multiplication.cancellation
              (NatWithZero.Positive q) (Integer.abs p)
              (NatWithZero.Positive s) h coprime1).
    }

    lemma sq : NatWithZero.Divides (NatWithZero.Positive s) (NatWithZero.Positive q).
    {
      let proof h := NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive s) (NatWithZero.Positive s)
                    (Integer.abs p)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive s)).
      leibniz (NatWithZero.multiplication.commutativity
                 (NatWithZero.Positive s) (Integer.abs p)) in h.
      leibniz m in h.
      ipso (NatWithZero.gcd.multiplication.cancellation
               (NatWithZero.Positive s) (Integer.abs r)
               (NatWithZero.Positive q) h coprime2).
    }

    let proof hq := NatWithZero.positive.injectivity (NatWithZero.divisibility.antisymmetry qs sq).
    leibniz hq in cross.
    leibniz (Integer.multiplication.commutativity p (Integer.from_nat s)) in cross.
    leibniz (Integer.multiplication.commutativity r (Integer.from_nat s)) in cross.
    let proof hp := Integer.multiplication.cancellation (Integer.from_nat s) p r nzs cross.
    apply extensionality.
    + simpl numerator in |- *.
      ipso hp.
    + simpl denominator in |- *.
      ipso hq.
Qed.

(* make.annihilation *)
Theorem annihilation
  : forall (b : Nat) . make Integer.Zero b = Zero.
Proof.
  intro b.

  lemma unit : make Integer.Zero Nat.One = Zero.
  {
    let proof r := retraction Zero.
    let proof r : make Integer.Zero Nat.One = Zero := &r.
    ipso r.
  }

  lemma cross : Integer.mul Integer.Zero (Integer.from_nat Nat.One)
          = Integer.mul Integer.Zero (Integer.from_nat b).
  {
    leibniz (Integer.multiplication.left.annihilation (Integer.from_nat Nat.One)) in |- *.
    leibniz (Integer.multiplication.left.annihilation (Integer.from_nat b))     in |- *.
    quod idem est.
  }

  let proof criterion := characterisation Integer.Zero b Integer.Zero Nat.One.
  modus aequans criterion, cross |- joined.
  ipso (Identity.transitivity joined unit).
Qed.

Module addition. (* make.addition *)

(* make.addition.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      (make a b) + (make c d)
      = make (Integer.add (Integer.mul a (Integer.from_nat d))
                    (Integer.mul c (Integer.from_nat b)))
             (Nat.mul b d).
Proof.
  intros a b c d.
  simpl add in |- *.

  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.

  match (make a b) per E1 with | p q I1 end.
  match (make c d) per E2 with | r s I2 end.
  simpl numerator, denominator in P1, P2.
  simpl numerator, denominator in |- *.

  let b' := Integer.from_nat b in *.
  let d' := Integer.from_nat d in *.
  let q' := Integer.from_nat q in *.
  let s' := Integer.from_nat s in *.

  lemma first : Integer.mul (Integer.mul p s') (Integer.mul b' d')
          = Integer.mul (Integer.mul a d') (Integer.mul q' s').
  {
    leibniz (Integer.multiplication.interchange p s' b' d') in |- *.
    leibniz P1 in |- *.
    leibniz (Integer.multiplication.commutativity s' d') in |- *.
    leibniz (Integer.multiplication.interchange a q' d' s') in |- *.
    quod idem est.
  }

  lemma second : Integer.mul (Integer.mul r q') (Integer.mul b' d')
          = Integer.mul (Integer.mul c b') (Integer.mul q' s').
  {
    leibniz (Integer.multiplication.commutativity b' d') in |- *.
    leibniz (Integer.multiplication.interchange r q' d' b') in |- *.
    leibniz P2 in |- *.
    leibniz (Integer.multiplication.commutativity q' b') in |- *.
    leibniz (Integer.multiplication.interchange c s' b' q') in |- *.
    leibniz (Integer.multiplication.commutativity s' q') in |- *.
    quod idem est.
  }

  lemma cross : Integer.mul (Integer.add (Integer.mul p s') (Integer.mul r q'))
                  (Integer.from_nat (Nat.mul b d))
          = Integer.mul (Integer.add (Integer.mul a d') (Integer.mul c b'))
                  (Integer.from_nat (Nat.mul q s)).
  {
    lemma facto
      : Integer.mul (Integer.add (Integer.mul &p &s') (Integer.mul &r &q')) (Integer.mul &b' &d')
        = Integer.mul (Integer.add (Integer.mul &a &d') (Integer.mul &c &b')) (Integer.mul &q' &s').
    {
      leibniz (Integer.multiplication.right.distributivity.over.addition
                (Integer.mul b' d') (Integer.mul p s') (Integer.mul r q')) in |- *.
      leibniz (Integer.multiplication.right.distributivity.over.addition
                (Integer.mul q' s') (Integer.mul a d') (Integer.mul c b')) in |- *.
      leibniz first  in |- *.
      leibniz second in |- *.
      quod idem est.
    }
    let proof facto
      : Integer.mul (Integer.add (Integer.mul &p &s') (Integer.mul &r &q')) (Integer.mul &b' &d')
        = Integer.mul (Integer.add (Integer.mul &a &d') (Integer.mul &c &b'))
                      (Integer.from_nat (Nat.mul &q &s))
      := &facto.
    ipso &facto.
  }

  let proof criterion := characterisation
                (Integer.add (Integer.mul p s') (Integer.mul r q'))
                (Nat.mul q s)
                (Integer.add (Integer.mul a d') (Integer.mul c b'))
                (Nat.mul b d).
  modus aequans criterion, cross |- joined.
  ipso joined.
Qed.

End addition. (* make.addition *)

Module multiplication. (* make.multiplication *)

(* make.multiplication.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
    (make a b) * (make c d) = make (Integer.mul a c) (Nat.mul b d).
Proof.
  intros a b c d.
  simpl mul in |- *.

  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.

  match (make a b) per E1 with | p q I1 end.
  match (make c d) per E2 with | r s I2 end.
  simpl numerator, denominator in P1, P2.
  simpl numerator, denominator in |- *.

  lemma cross : Integer.mul (Integer.mul p r) (Integer.from_nat (Nat.mul b d))
          = Integer.mul (Integer.mul a c) (Integer.from_nat (Nat.mul q s)).
  {
    lemma facto
      : Integer.mul (Integer.mul &p &r) (Integer.mul (Integer.from_nat &b) (Integer.from_nat &d))
        = Integer.mul (Integer.mul &a &c) (Integer.mul (Integer.from_nat &q) (Integer.from_nat &s)).
    {
      leibniz (Integer.multiplication.interchange
                p r (Integer.from_nat b) (Integer.from_nat d)) in |- *.
      leibniz P1 in |- *.
      leibniz P2 in |- *.
      leibniz (Integer.multiplication.interchange
                a (Integer.from_nat q) c (Integer.from_nat s)) in |- *.
      quod idem est.
    }
    let proof facto
      : Integer.mul (Integer.mul &p &r) (Integer.mul (Integer.from_nat &b) (Integer.from_nat &d))
        = Integer.mul (Integer.mul &a &c) (Integer.from_nat (Nat.mul &q &s))
      := &facto.
    ipso &facto.
  }

  let proof criterion := characterisation
                (Integer.mul p r) (Nat.mul q s)
                (Integer.mul a c) (Nat.mul b d).
  modus aequans criterion, cross |- joined.
  ipso joined.
Qed.

End multiplication. (* make.multiplication *)

Module negation. (* make.negation *)

(* make.negation.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) .
      negate (make a b) = make (Integer.negate a) b.
Proof.
  intros a b.
  simpl negate in |- *.

  let proof P1 := proportionality a b.

  match (make a b) per E1 with | p q I1 end.
  simpl numerator, denominator in P1.
  simpl numerator, denominator in |- *.

  lemma cross : Integer.mul (Integer.negate p) (Integer.from_nat b)
          = Integer.mul (Integer.negate a) (Integer.from_nat q).
  {
    leibniz (Integer.multiplication.left.negation p (Integer.from_nat b)) in |- *.
    leibniz (Integer.multiplication.left.negation a (Integer.from_nat q)) in |- *.
    leibniz P1 in |- *.
    quod idem est.
  }

  let proof criterion := characterisation
                (Integer.negate p) q (Integer.negate a) b.
  modus aequans criterion, cross |- joined.
  ipso joined.
Qed.

End negation. (* make.negation *)

End make. (* make *)

Theorem characterisation
  : forall (x : Rational) (y : Rational) .
      x = y
      <-> Integer.mul (numerator x) (Integer.from_nat (denominator y))
        = Integer.mul (numerator y) (Integer.from_nat (denominator x)).
Proof.
  intros x y.
  let proof c := make.characterisation
                (numerator x) (denominator x)
                (numerator y) (denominator y).
  leibniz (make.retraction x) in c.
  leibniz (make.retraction y) in c.
  ipso c.
Qed.

Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (x + y) + z = x + (y + z).
Proof.
  intros x y z.

  lemma general : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) (e : Integer) (f : Nat) .
              ((make a b) + (make c d)) + (make e f)
            = (make a b) + ((make c d) + (make e f)).
  {
    intros a b c d e f.
    leibniz (make.addition.homomorphism a b c d) in |- *.
    leibniz (make.addition.homomorphism c d e f) in |- *.
    leibniz (make.addition.homomorphism
               (Integer.add (Integer.mul a (Integer.from_nat d))
                      (Integer.mul c (Integer.from_nat b)))
               (Nat.mul b d)
               e f) in |- *.
    leibniz (make.addition.homomorphism
               a b
               (Integer.add (Integer.mul c (Integer.from_nat f))
                      (Integer.mul e (Integer.from_nat d)))
               (Nat.mul d f)) in |- *.

    let b' := Integer.from_nat b in *.
    let d' := Integer.from_nat d in *.
    let f' := Integer.from_nat f in *.

    lemma facto
      : make (Integer.add (Integer.mul (Integer.add (Integer.mul &a &d') (Integer.mul &c &b')) &f')
                          (Integer.mul &e (Integer.mul &b' &d')))
             (Nat.mul (Nat.mul &b &d) &f)
        = make (Integer.add (Integer.mul &a (Integer.mul &d' &f'))
                            (Integer.mul (Integer.add (Integer.mul &c &f') (Integer.mul &e &d'))
                                         &b'))
               (Nat.mul &b (Nat.mul &d &f)).
    {
      lemma tops : Integer.add
                  (Integer.mul (Integer.add (Integer.mul a d') (Integer.mul c b')) (f'))
                  (Integer.mul (e) (Integer.mul b' d'))
              = Integer.add
                  (Integer.mul (a) (Integer.mul d' f'))
                  (Integer.mul (Integer.add (Integer.mul c f') (Integer.mul e d')) (b')).
      {
        leibniz (Integer.multiplication.right.distributivity.over.addition
                  f' (Integer.mul a d') (Integer.mul c b')) in |- *.
        leibniz (Integer.multiplication.right.distributivity.over.addition
                  b' (Integer.mul c f') (Integer.mul e d')) in |- *.
        leibniz (Integer.addition.associativity
                  (Integer.mul (Integer.mul a d') f')
                  (Integer.mul (Integer.mul c b') f')
                  (Integer.mul e (Integer.mul b' d'))) in |- *.
        leibniz (Integer.multiplication.associativity a d' f') in |- *.
        leibniz (Integer.multiplication.associativity c b' f') in |- *.
        leibniz (Integer.multiplication.associativity c f' b') in |- *.
        leibniz (Integer.multiplication.associativity e d' b') in |- *.
        leibniz (Integer.multiplication.commutativity b' f') in |- *.
        leibniz (Integer.multiplication.commutativity b' d') in |- *.
        quod idem est.
      }

      leibniz tops in |- *.
      leibniz (Nat.multiplication.associativity b d f) in |- *.
      quod idem est.
    }
    let proof facto
      : make (Integer.add (Integer.mul (Integer.add (Integer.mul &a &d') (Integer.mul &c &b')) &f')
                          (Integer.mul &e (Integer.mul &b' &d')))
             (Nat.mul (Nat.mul &b &d) &f)
        = make (Integer.add (Integer.mul &a (Integer.from_nat (Nat.mul &d &f)))
                            (Integer.mul (Integer.add (Integer.mul &c &f') (Integer.mul &e &d'))
                                         &b'))
               (Nat.mul &b (Nat.mul &d &f))
      := &facto.
    ipso &facto.
  }

  let proof g := general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z).
  leibniz (make.retraction x) in g.
  leibniz (make.retraction y) in g.
  leibniz (make.retraction z) in g.
  ipso g.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (x : Rational) (y : Rational) . x + y = y + x.
Proof.
  intros x y.
  simpl add in |- *.
  leibniz (Integer.addition.commutativity
            (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
            (Integer.mul (numerator y) (Integer.from_nat (denominator x)))) in |- *.
  leibniz (Nat.multiplication.commutativity (denominator x) (denominator y)) in |- *.
  quod idem est.
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
  Theorem identity : forall (x : Rational) . Zero + x = x.
Proof.
  intro x.
  simpl add in |- *.
  lemma facto
    : make (Integer.add (Integer.mul Integer.Zero (Integer.from_nat (denominator &x)))
                        (Integer.mul (numerator &x) (Integer.Positive Nat.One)))
           (denominator &x)
      = &x.
  {
    leibniz (Integer.multiplication.left.annihilation
               (Integer.from_nat (denominator x))) in |- *.
    leibniz (Integer.addition.left.identity
               (Integer.mul (numerator x)
                            (Integer.Positive Nat.One))) in |- *.
    leibniz (Integer.multiplication.right.identity (numerator x)) in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (Integer.add (Integer.mul Integer.Zero (Integer.from_nat (denominator &x)))
                        (Integer.mul (numerator &x) (Integer.Positive Nat.One)))
           (Nat.mul Nat.One (denominator &x))
      = &x
    := &facto.
  let proof facto
    : make (Integer.add (Integer.mul Integer.Zero (Integer.from_nat (denominator &x)))
                        (Integer.mul (numerator &x) (Integer.from_nat Nat.One)))
           (Nat.mul Nat.One (denominator &x))
      = &x
    := &facto.
  let proof facto
    : make (Integer.add (Integer.mul Integer.Zero (Integer.from_nat (denominator &x)))
                        (Integer.mul (numerator &x) (Integer.from_nat (denominator Zero))))
           (Nat.mul (denominator Zero) (denominator &x))
      = &x
    := &facto.
  ipso &facto.
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (x : Rational) . (negate x) + x = Zero.
Proof.
  intro x.

  lemma general : forall (a : Integer) (b : Nat) . (negate (make a b)) + (make a b) = Zero.
  {
    intros a b.
    leibniz (make.negation.homomorphism a b) in |- *.
    leibniz (make.addition.homomorphism (Integer.negate a) b a b) in |- *.
    leibniz (Integer.multiplication.left.negation (a) (Integer.from_nat b)) in |- *.
    leibniz (Integer.addition.left.inverse (Integer.mul a (Integer.from_nat b))) in |- *.
    ipso (make.annihilation (Nat.mul b b)).
  }

  let proof g := general (numerator x) (denominator x).
  leibniz (make.retraction x) in g.
  ipso g.
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall (k : Rational) (m : Rational) (n : Rational) .
      k + m = k + n -> m = n.
Proof.
  intros k m n e.

  let proof am := associativity (negate k) k m.
  leibniz (inverse k)  in am.
  leibniz (identity m) in am.

  let proof an := associativity (negate k) k n.
  leibniz (inverse k)  in an.
  leibniz (identity n) in an.

  let proof h := Identity.congruence
                (fun (t : Rational) . add (negate k) t)
                (e).
  simpl in h.

  symmetry in an.
  ipso (Identity.transitivity am (Identity.transitivity h an)).
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
  Theorem identity : forall (x : Rational) . x + Zero = x.
Proof.
  intro x.
  simpl add in |- *.
  lemma facto
    : make (Integer.add (Integer.mul (numerator &x) (Integer.Positive Nat.One))
                        (Integer.mul Integer.Zero (Integer.from_nat (denominator &x))))
           (Nat.mul (denominator &x) Nat.One)
      = &x.
  {
    leibniz (Integer.multiplication.right.identity (numerator x)) in |- *.
    leibniz (Integer.multiplication.left.annihilation (Integer.from_nat (denominator x))) in |- *.
    leibniz (Integer.addition.right.identity (numerator x)) in |- *.
    match (Nat.multiplication.identity (denominator x)) with | _ unit end.
    leibniz unit in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (Integer.add (Integer.mul (numerator &x) (Integer.from_nat Nat.One))
                        (Integer.mul Integer.Zero (Integer.from_nat (denominator &x))))
           (Nat.mul (denominator &x) Nat.One)
      = &x
    := &facto.
  let proof facto
    : make (Integer.add (Integer.mul (numerator &x) (Integer.from_nat (denominator Zero)))
                        (Integer.mul Integer.Zero (Integer.from_nat (denominator &x))))
           (Nat.mul (denominator &x) (denominator Zero))
      = &x
    := &facto.
  ipso &facto.
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (x : Rational) . x + (negate x) = Zero.
Proof.
  intro x.

  lemma general : forall (a : Integer) (b : Nat) .
              add (make a b) (negate (make a b)) = Zero.
  {
    intros a b.
    leibniz (make.negation.homomorphism a b) in |- *.
    leibniz (make.addition.homomorphism a b (Integer.negate a) b) in |- *.
    leibniz (Integer.multiplication.left.negation
               a (Integer.from_nat b)) in |- *.
    leibniz (Integer.addition.right.inverse
               (Integer.mul a (Integer.from_nat b))) in |- *.
    ipso (make.annihilation (Nat.mul b b)).
  }

  let proof g := general (numerator x) (denominator x).
  leibniz (make.retraction x) in g.
  ipso g.
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall (k : Rational) (m : Rational) (n : Rational) .
      add m k = add n k -> m = n.
Proof.
  intros k m n e.

  let proof am := associativity m k (negate k).
  leibniz (inverse k)  in am.
  leibniz (identity m) in am.

  let proof an := associativity n k (negate k).
  leibniz (inverse k)  in an.
  leibniz (identity n) in an.

  let proof h := Identity.congruence (fun (t : Rational) . add t (negate k)) e.
  simpl in h.

  symmetry in am.
  ipso (Identity.transitivity am (Identity.transitivity h an)).
Qed.

End right. (* addition.right *)

(* addition.identity *)
Theorem identity
  : forall (x : Rational) . (Zero + x = x) /\ (x + Zero = x).
Proof.
  intro x.
  divide et impera.
  - ipso (left.identity  x).
  - ipso (right.identity x).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (x : Rational) .
      ((negate x) + x = Zero) /\ (x + (negate x) = Zero).
Proof.
  intro x.
  divide et impera.
  - ipso (left.inverse  x).
  - ipso (right.inverse x).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Rational) (n : Rational) (k : Rational) .
      (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  divide et impera.
  - ipso (left.cancellation  m n k).
  - ipso (right.cancellation n m k).
Qed.

End addition. (* addition *)


Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (x : Rational) (y : Rational) . x * y = y * x.
Proof.
  intros x y.
  simpl mul in |- *.
  leibniz (Integer.multiplication.commutativity (numerator   x) (numerator   y)) in |- *.
  leibniz (Nat.multiplication.commutativity (denominator x) (denominator y)) in |- *.
  quod idem est.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (x * y) * z = x * (y * z).
Proof.
  intros x y z.

  lemma general : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) (e : Integer) (f : Nat) .
              ((make a b) * (make c d)) * (make e f)
            = (make a b) * ((make c d) * (make e f)).
  {
    intros a b c d e f.
    leibniz (make.multiplication.homomorphism a b c d) in |- *.
    leibniz (make.multiplication.homomorphism c d e f) in |- *.
    leibniz (make.multiplication.homomorphism
              (Integer.mul a c) (Nat.mul b d) e f) in |- *.
    leibniz (make.multiplication.homomorphism
              a b (Integer.mul c e) (Nat.mul d f)) in |- *.
    leibniz (Integer.multiplication.associativity a c e) in |- *.
    leibniz (Nat.multiplication.associativity b d f) in |- *.
    quod idem est.
  }

  let proof g := general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z).
  leibniz (make.retraction x) in g.
  leibniz (make.retraction y) in g.
  leibniz (make.retraction z) in g.
  ipso g.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Theorem identity : forall (x : Rational) . mul One x = x.
Proof.
  intro x.
  simpl mul in |- *.
  lemma facto
    : make (Integer.mul (Integer.Positive Nat.One) (numerator &x)) (denominator &x) = &x.
  {
    leibniz (Integer.multiplication.left.identity (numerator x)) in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (Integer.mul (Integer.Positive Nat.One) (numerator &x))
           (Nat.mul Nat.One (denominator &x))
      = &x
    := &facto.
  let proof facto
    : make (Integer.mul (Integer.Positive Nat.One) (numerator &x))
           (Nat.mul (denominator One) (denominator &x))
      = &x
    := &facto.
  ipso &facto.
Qed.

(* multiplication.left.annihilation *)
Theorem annihilation : forall (x : Rational) . Zero * x = Zero.
Proof.
  intro x.
  simpl mul in |- *.
  lemma facto
    : make (Integer.mul Integer.Zero (numerator &x)) (denominator &x) = Zero.
  {
    leibniz (Integer.multiplication.left.annihilation (numerator x)) in |- *.
    ipso (make.annihilation (denominator x)).
  }
  let proof facto
    : make (Integer.mul Integer.Zero (numerator &x)) (Nat.mul Nat.One (denominator &x)) = Zero
    := &facto.
  let proof facto
    : make (Integer.mul Integer.Zero (numerator &x))
           (Nat.mul (denominator Zero) (denominator &x))
      = Zero
    := &facto.
  ipso &facto.
Qed.

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (x : Rational) (y : Rational) (z : Rational) .
      x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.

  lemma general : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat)
              (e : Integer) (f : Nat) .
              (make a b) * ((make c d) + (make e f))
            = ((make a b) * (make c d)) + ((make a b) * (make e f)).
  {
    intros a b c d e f.
    leibniz (make.addition.homomorphism c d e f) in |- *.
    leibniz (make.multiplication.homomorphism
              a b
              (Integer.add (Integer.mul c (Integer.from_nat f))
                     (Integer.mul e (Integer.from_nat d)))
              (Nat.mul d f)) in |- *.
    leibniz (make.multiplication.homomorphism a b c d) in |- *.
    leibniz (make.multiplication.homomorphism a b e f) in |- *.
    leibniz (make.addition.homomorphism
              (Integer.mul a c) (Nat.mul b d)
              (Integer.mul a e) (Nat.mul b f)) in |- *.

    let b' := Integer.from_nat b.
    let d' := Integer.from_nat d in *.
    let f' := Integer.from_nat f in *.

    lemma facto
      : make (Integer.mul &a (Integer.add (Integer.mul &c &f') (Integer.mul &e &d')))
             (Nat.mul &b (Nat.mul &d &f))
        = make (Integer.add (Integer.mul (Integer.mul &a &c) (Integer.mul &b' &f'))
                            (Integer.mul (Integer.mul &a &e) (Integer.mul &b' &d')))
               (Nat.mul (Nat.mul &b &d) (Nat.mul &b &f)).
    {
      lemma tops : Integer.add
                  (Integer.mul (Integer.mul a c) (Integer.mul b' f'))
                  (Integer.mul (Integer.mul a e) (Integer.mul b' d'))
              = Integer.mul b'
                  (Integer.mul
                    (a)
                    (Integer.add (Integer.mul c f') (Integer.mul e d'))).
      {
        leibniz (Integer.multiplication.left.distributivity.over.addition
                  a (Integer.mul c f') (Integer.mul e d')) in |- *.
        leibniz (Integer.multiplication.left.distributivity.over.addition
                  b'
                  (Integer.mul a (Integer.mul c f'))
                  (Integer.mul a (Integer.mul e d'))) in |- *.
        leibniz (Integer.multiplication.interchange a c b' f') in |- *.
        leibniz (Integer.multiplication.interchange a e b' d') in |- *.
        leibniz (Integer.multiplication.commutativity a b') in |- *.
        leibniz (Integer.multiplication.associativity
                  b' a (Integer.mul c f')) in |- *.
        leibniz (Integer.multiplication.associativity
                  b' a (Integer.mul e d')) in |- *.
        quod idem est.
      }

      lemma bots : Nat.mul
                  (Nat.mul b d)
                  (Nat.mul b f)
              = Nat.mul
                  (b)
                  (Nat.mul b (Nat.mul d f)).
      {
        leibniz (Nat.multiplication.associativity b d (Nat.mul b f)) in |- *.
        leibniz (Nat.multiplication.commutativity d (Nat.mul b f)) in |- *.
        leibniz (Nat.multiplication.associativity b f d) in |- *.
        leibniz (Nat.multiplication.commutativity f d) in |- *.
        quod idem est.
      }

      leibniz tops in |- *.
      leibniz bots in |- *.
      symmetry in |- *.
      ipso (make.invariance
              (Integer.mul (a) (Integer.add (Integer.mul c f') (Integer.mul e d')))
              (Nat.mul (b) (Nat.mul d f))
              (b)).
    }
    let proof facto
      : make (Integer.mul &a (Integer.add (Integer.mul &c &f') (Integer.mul &e &d')))
             (Nat.mul &b (Nat.mul &d &f))
        = make (Integer.add (Integer.mul (Integer.mul &a &c) (Integer.mul &b' &f'))
                            (Integer.mul (Integer.mul &a &e) (Integer.from_nat (Nat.mul &b &d))))
               (Nat.mul (Nat.mul &b &d) (Nat.mul &b &f))
      := &facto.
    ipso &facto.
  }

  let proof g := general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z).
  leibniz (make.retraction x) in g.
  leibniz (make.retraction y) in g.
  leibniz (make.retraction z) in g.
  ipso g.
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
  Theorem identity : forall (x : Rational) . x * One = x.
Proof.
  intro x.
  leibniz (commutativity x One) in |- *.
  ipso (left.identity x).
Qed.

(* multiplication.right.annihilation *)
Theorem annihilation : forall (x : Rational) . x * Zero = Zero.
Proof.
  intro x.
  leibniz (commutativity x Zero) in |- *.
  ipso (left.annihilation x).
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (y + z) * x = (y * x) + (z * x).
Proof.
  intros x y z.
  leibniz (commutativity (y + z) x) in |- *.
  leibniz (left.distributivity.over.addition x y z) in |- *.
  leibniz (commutativity x y) in |- *.
  leibniz (commutativity x z) in |- *.
  quod idem est.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (x : Rational) . (One * x = x) /\ (x * One = x).
Proof.
  intro x.
  divide et impera.
  - ipso (left.identity  x).
  - ipso (right.identity x).
Qed.

Module distributivity. (* multiplication.distributivity *)

Module over. (* multiplication.distributivity.over *)

(* multiplication.distributivity.over.addition *)
Theorem addition
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (x * (y + z) = (x * y) + (x * z))
    /\ ((y + z) * x = (y * x) + (z * x)).
Proof.
  intros x y z.
  divide et impera.
  - ipso (left.distributivity.over.addition  x y z).
  - ipso (right.distributivity.over.addition x y z).
Qed.

End over. (* multiplication.distributivity.over *)

End distributivity. (* multiplication.distributivity *)

End multiplication. (* multiplication *)

Module inverse. (* inverse *)

(* inverse.specification *)
Theorem specification
  : forall (x : Rational) (y : Rational) .
      inverse x = Some y -> x * y = One.
Proof.
  intros x y e.

  lemma unit : make (Integer.Positive Nat.One) Nat.One = One.
  {
    let proof r := make.retraction One.
    let proof r : make (Integer.Positive Nat.One) Nat.One = One := &r.
    ipso r.
  }

  let proof r := make.retraction x.
  simpl inverse in e.
  match (numerator x) per E with | p | | p end.

  - let proof hy := Option.some.injectivity e.
    symmetry in r.
    leibniz r in |- *.
    symmetry in hy.
    leibniz hy in |- *.
    let d := denominator x in *.
    leibniz (make.multiplication.homomorphism (Integer.Negative p) (d) (Integer.Negative d) (p)) in |- *.
    lemma facto : make (Integer.Positive (Nat.mul &p &d)) (Nat.mul &d &p) = One.
    {
      lemma cross : Integer.mul (Integer.Positive (Nat.mul p d))
                      (Integer.from_nat Nat.One)
              = Integer.mul (Integer.Positive Nat.One)
                      (Integer.from_nat (Nat.mul d p)).
      {
        lemma facto
          : Integer.mul (Integer.Positive (Nat.mul &p &d)) (Integer.Positive Nat.One)
            = Integer.mul (Integer.Positive Nat.One) (Integer.Positive (Nat.mul &d &p)).
        {
          leibniz (Integer.multiplication.right.identity
                    (Integer.Positive (Nat.mul p d))) in |- *.
          leibniz (Integer.multiplication.left.identity
                    (Integer.Positive (Nat.mul d p))) in |- *.
          leibniz (Nat.multiplication.commutativity p d) in |- *.
          quod idem est.
        }
        let proof facto
          : Integer.mul (Integer.Positive (Nat.mul &p &d)) (Integer.Positive Nat.One)
            = Integer.mul (Integer.Positive Nat.One) (Integer.from_nat (Nat.mul &d &p))
          := &facto.
        ipso &facto.
      }

      let proof criterion := make.characterisation
                    (Integer.Positive (Nat.mul p d))
                    (Nat.mul d p)
                    (Integer.Positive Nat.One)
                    (Nat.One).
      modus aequans criterion, cross |- joined.
      ipso (Identity.transitivity joined unit).
    }
    ipso &facto.

  - ex e quodlibet.

  - let proof hy := Option.some.injectivity e.
    symmetry in r.
    leibniz r in |- *.
    symmetry in hy.
    leibniz hy in |- *.
    let d := denominator x in *.
    leibniz (make.multiplication.homomorphism
              (Integer.Positive p) (d)
              (Integer.Positive d) (p)) in |- *.
    lemma facto : make (Integer.Positive (Nat.mul &p &d)) (Nat.mul &d &p) = One.
    {
      lemma cross : Integer.mul (Integer.Positive (Nat.mul p d))
                      (Integer.from_nat Nat.One)
              = Integer.mul (Integer.Positive Nat.One)
                      (Integer.from_nat (Nat.mul d p)).
      {
        lemma facto
          : Integer.mul (Integer.Positive (Nat.mul &p &d)) (Integer.Positive Nat.One)
            = Integer.mul (Integer.Positive Nat.One) (Integer.Positive (Nat.mul &d &p)).
        {
          leibniz (Integer.multiplication.right.identity (Integer.Positive (Nat.mul p d))) in |- *.
          leibniz (Integer.multiplication.left.identity (Integer.Positive (Nat.mul d p))) in |- *.
          leibniz (Nat.multiplication.commutativity p d) in |- *.
          quod idem est.
        }
        let proof facto
          : Integer.mul (Integer.Positive (Nat.mul &p &d)) (Integer.Positive Nat.One)
            = Integer.mul (Integer.Positive Nat.One) (Integer.from_nat (Nat.mul &d &p))
          := &facto.
        ipso &facto.
      }

      let proof criterion := make.characterisation
                    (Integer.Positive (Nat.mul p d))
                    (Nat.mul d p)
                    (Integer.Positive Nat.One)
                    (Nat.One).
      modus aequans criterion, cross |- joined.
      ipso (Identity.transitivity joined unit).
    }
    ipso &facto.
Qed.

End inverse. (* inverse *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      LessThan x y -> LessThan y z -> LessThan x z.
Proof.
  intros x y z H1 H2.
  simpl LessThan in H1, H2 |- *.
  simpl Integer.from_nat in H1, H2 |- *.

  let a := numerator   x in *.
  let b := denominator x in *.
  let c := numerator   y in *.
  let d := denominator y in *.
  let e := numerator   z in *.
  let f := denominator z in *.

  lemma bridge : Integer.mul (Integer.Positive f)
                        (Integer.mul c (Integer.Positive b))
          = Integer.mul (Integer.Positive b)
                        (Integer.mul c (Integer.Positive f)).
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    (Integer.Positive f) c (Integer.Positive b)).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity
               (Integer.Positive f) c) in |- *.
    leibniz (Integer.multiplication.commutativity
               (Integer.mul c (Integer.Positive f))
               (Integer.Positive b)) in |- *.
    quod idem est.
  }

  lemma leftward : Integer.mul (Integer.Positive f)
                  (Integer.mul a (Integer.Positive d))
          = Integer.mul (Integer.Positive d)
                  (Integer.mul a (Integer.Positive f)).
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    (Integer.Positive f) a (Integer.Positive d)).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity
              (Integer.Positive f)
              (a)) in |- *.
    leibniz (Integer.multiplication.commutativity
              (Integer.mul a (Integer.Positive f))
              (Integer.Positive d)) in |- *.
    quod idem est.
  }

  lemma rightward : Integer.mul (Integer.Positive b)
                  (Integer.mul e (Integer.Positive d))
          = Integer.mul (Integer.Positive d)
                  (Integer.mul e (Integer.Positive b)).
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    (Integer.Positive b)
                    (e)
                    (Integer.Positive d)).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity (Integer.Positive b) e) in |- *.
    leibniz (Integer.multiplication.commutativity
               (Integer.mul e (Integer.Positive b))
               (Integer.Positive d)) in |- *.
    quod idem est.
  }

  let proof S1 := Integer.multiplication.left.order.strict.monotonicity
                f (Integer.mul a (Integer.Positive d))
                  (Integer.mul c (Integer.Positive b)) H1.
  let proof S2 := Integer.multiplication.left.order.strict.monotonicity
                b (Integer.mul c (Integer.Positive f))
                  (Integer.mul e (Integer.Positive d)) H2.

  leibniz bridge    in S1.
  leibniz leftward  in S1.
  leibniz rightward in S2.

  let proof chain := Integer.order.strict.transitivity S1 S2.

  match (Comparable.order.strict.trichotomy
           (Integer.mul a (Integer.Positive f))
           (Integer.mul e (Integer.Positive b)))
        with | lt | rest end.

  - ipso lt.

  - match rest with | eq | gt end.

    + leibniz eq in chain.
      let proof ir := Integer.order.strict.irreflexivity
                    (Integer.mul (Integer.Positive d)
                           (Integer.mul e (Integer.Positive b))).
      ex (ir chain) quodlibet.

    + let proof back := Integer.multiplication.left.order.strict.monotonicity
                    d (Integer.mul e (Integer.Positive b))
                      (Integer.mul a (Integer.Positive f)) gt.
      let proof loop := Integer.order.strict.transitivity chain back.
      let proof ir := Integer.order.strict.irreflexivity
                    (Integer.mul (Integer.Positive d)
                           (Integer.mul a (Integer.Positive f))).
      ex (ir loop) quodlibet.
Qed.

End strict. (* order.strict *)

End order. (* order *)

Module comparison. (* comparison *)

(* comparison.specification *)
Theorem specification
  : forall (x : Rational) (y : Rational) .
      (compare x y = Comparison.Lt <-> x < y)
    /\ (compare x y = Comparison.Eq <-> x = y).
Proof.
  intros x y.

  match (Integer.comparison.specification
              (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
              (Integer.mul (numerator y) (Integer.from_nat (denominator x))))
        with | below equal end.

  divide et impera.
  - ipso below.
  - divide et impera.
    + intro h.
      modus aequans equal, h |- cross.
      modus aequans (characterisation x y), cross |- same.
      ipso same.
    + intro h.
      modus aequans (characterisation x y), h |- cross.
      modus aequans equal, cross |- answer.
      ipso answer.
Qed.

(* comparison.antisymmetry *)
Theorem antisymmetry
  : forall (x : Rational) (y : Rational) .
      compare x y = Comparison.transpose (compare y x).
Proof.
  intros x y.
  ipso (Integer.comparison.antisymmetry
          (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
          (Integer.mul (numerator y) (Integer.from_nat (denominator x)))).
Qed.

End comparison. (* comparison *)

Module embedding. (* embedding *)

(* embedding.injectivity *)
Theorem injectivity
  : forall {m : Integer} {n : Integer} .
      from_integer m = from_integer n -> m = n.
Proof.
  intros m n e.
  simpl from_integer in e.
  modus aequans (make.characterisation m Nat.One n Nat.One), e |- cross.
  let proof cross
    : Integer.mul m (Integer.Positive Nat.One) = Integer.mul n (Integer.Positive Nat.One)
    := &cross.
  leibniz (Integer.multiplication.right.identity m) in cross.
  leibniz (Integer.multiplication.right.identity n) in cross.
  ipso cross.
Qed.

(* embedding.addition *)
Theorem addition
  : forall (m : Integer) (n : Integer) .
      from_integer (Integer.add m n)
    = (from_integer m) + (from_integer n).
Proof.
  intros m n.
  simpl from_integer in |- *.
  leibniz (make.addition.homomorphism m Nat.One n Nat.One) in |- *.
  lemma facto
    : make (Integer.add &m &n) Nat.One
      = make (Integer.add (Integer.mul &m (Integer.Positive Nat.One))
                          (Integer.mul &n (Integer.Positive Nat.One)))
             (Nat.mul Nat.One Nat.One).
  {
    leibniz (Integer.multiplication.right.identity m) in |- *.
    leibniz (Integer.multiplication.right.identity n) in |- *.
    lemma facto : make (Integer.add &m &n) Nat.One = make (Integer.add &m &n) Nat.One.
    {
      quod idem est.
    }
    ipso &facto.
  }
  ipso &facto.
Qed.

(* embedding.multiplication *)
Theorem multiplication
  : forall (m : Integer) (n : Integer) .
      from_integer (Integer.mul m n)
    = (from_integer m) * (from_integer n).
Proof.
  intros m n.
  simpl from_integer in |- *.
  leibniz (make.multiplication.homomorphism m Nat.One n Nat.One) in |- *.
  lemma facto : make (Integer.mul &m &n) Nat.One = make (Integer.mul &m &n) Nat.One.
  {
    quod idem est.
  }
  ipso &facto.
Qed.

(* embedding.order *)
Theorem order
  : forall (m : Integer) (n : Integer) .
      Integer.LessThan m n
      <-> LessThan (from_integer m) (from_integer n).
Proof.
  intros m n.

  lemma scaling : forall (p : Integer) (q : Integer) (k : Nat) .
              Integer.LessThan p q
              <-> Integer.LessThan (Integer.mul p (Integer.Positive k))
                                   (Integer.mul q (Integer.Positive k)).
  {
    intros p q k.
    divide et impera.
    - intro h.
      let proof s := Integer.multiplication.left.order.strict.monotonicity
                    k p q h.
      leibniz (Integer.multiplication.commutativity
                 (Integer.Positive k) p) in s.
      leibniz (Integer.multiplication.commutativity
                 (Integer.Positive k) q) in s.
      ipso s.
    - intro h.
      match (Comparable.order.strict.trichotomy p q)
            with | below | rest end.
      + ipso below.
      + match rest with | equal | above end.
        * leibniz equal in h.
          let proof ir := Integer.order.strict.irreflexivity
                        (Integer.mul q (Integer.Positive k)).
          ex (ir h) quodlibet.
        * let proof s := Integer.multiplication.left.order.strict.monotonicity
                        k q p above.
          leibniz (Integer.multiplication.commutativity
                     (Integer.Positive k) q) in s.
          leibniz (Integer.multiplication.commutativity
                     (Integer.Positive k) p) in s.
          let proof loop := Integer.order.strict.transitivity h s.
          let proof ir := Integer.order.strict.irreflexivity
                        (Integer.mul p (Integer.Positive k)).
          ex (ir loop) quodlibet.
  }

  let proof P1 := make.proportionality m Nat.One.
  let proof P2 := make.proportionality n Nat.One.
  let proof P1
    : Integer.mul (numerator (make m Nat.One)) (Integer.Positive Nat.One)
      = Integer.mul m (Integer.from_nat (denominator (make m Nat.One)))
    := &P1.
  let proof P2
    : Integer.mul (numerator (make n Nat.One)) (Integer.Positive Nat.One)
      = Integer.mul n (Integer.from_nat (denominator (make n Nat.One)))
    := &P2.
  leibniz (Integer.multiplication.right.identity
             (numerator (make m Nat.One))) in P1.
  leibniz (Integer.multiplication.right.identity
             (numerator (make n Nat.One))) in P2.

  simpl LessThan   in |- *.
  simpl from_integer in |- *.
  leibniz P1 in |- *.
  leibniz P2 in |- *.

  let dm := Integer.from_nat (denominator (make m Nat.One)) in *.
  let dn := Integer.from_nat (denominator (make n Nat.One)) in *.

  leibniz (Integer.multiplication.associativity m dm dn) in |- *.
  leibniz (Integer.multiplication.associativity n dn dm) in |- *.
  leibniz (Integer.multiplication.commutativity dn dm) in |- *.

  lemma facto
    : Integer.LessThan &m &n
      <-> Integer.LessThan
            (Integer.mul &m (Integer.Positive (Nat.mul (denominator (make &m Nat.One))
                                                       (denominator (make &n Nat.One)))))
            (Integer.mul &n (Integer.Positive (Nat.mul (denominator (make &m Nat.One))
                                                       (denominator (make &n Nat.One))))).
  {
    ipso (scaling m n
             (Nat.mul (denominator (make m Nat.One))
                      (denominator (make n Nat.One)))).
  }
  ipso &facto.
Qed.

End embedding. (* embedding *)

Local Close Scope jwa_rational_scope.

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.

(* Makes the notations declared in [Module Rational] usable in every file
 * that imports this one, as [(x + y)%rational]. Only the notations are
 * exported: [add] and the laws still need the [Rational.] prefix.
 *)
Export (notations) Rational.

Instance Rational_comparable
  : Comparable Rational.compare Rational.LessThan :=
  {| Comparable.transitivity  := Rational.order.strict.transitivity
   ; Comparable.specification := Rational.comparison.specification
   ; Comparable.antisymmetry  := Rational.comparison.antisymmetry |}.

Instance Rational_add_monoid : Monoid Rational.add Rational.Zero :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Rational.addition.associativity |}
   ; Monoid.identity := Rational.addition.identity |}.

Instance Rational_add_cancellative : Cancellative Rational.add :=
  {| Cancellative.cancellation := Rational.addition.cancellation |}.

Instance Rational_add_commutative : Commutative Rational.add :=
  {| Commutative.commutativity := Rational.addition.commutativity |}.

Instance Rational_mul_monoid : Monoid Rational.mul Rational.One :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Rational.multiplication.associativity |}
   ; Monoid.identity := Rational.multiplication.identity |}.

Instance Rational_mul_commutative : Commutative Rational.mul :=
  {| Commutative.commutativity := Rational.multiplication.commutativity |}.

Instance Rational_add_group
  : Group Rational.add Rational.Zero Rational.negate :=
  {| Group.monoid  := Rational_add_monoid
   ; Group.inverse := Rational.addition.inverse |}.

Instance Rational_add_abelian_group
  : AbelianGroup Rational.add Rational.Zero Rational.negate :=
  {| AbelianGroup.group       := Rational_add_group
   ; AbelianGroup.commutative := Rational_add_commutative |}.

Instance Rational_ring
  : Ring Rational.add Rational.Zero Rational.negate
      Rational.mul Rational.One :=
  {| Ring.abelian_group  := Rational_add_abelian_group
   ; Ring.monoid         := Rational_mul_monoid
   ; Ring.distributivity :=
       Rational.multiplication.distributivity.over.addition |}.
