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
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Tactics.Modus.
From jwa Require Import Tactics.Simplify.

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

Local Open Scope jwa_rational_scope.

Theorem extensionality
  : forall (x : Rational) (y : Rational) .
      numerator x = numerator y
      -> denominator x = denominator y
      -> x = y.
Proof.
  intros x y.
  destruct x as [n1 d1 h1].
  destruct y as [n2 d2 h2].
  simplify numerator, denominator in |- *.
  intros e1 e2.
  destruct e1.
  destruct e2.
  rewrite (Nat.equality.uniqueness
             (NatWithZero.gcd.nat (Integer.abs n1) d1) Nat.One h1 h2) in |- *.
  reflexivity.
Qed.

Theorem irreducibility
  : forall (x : Rational) .
      NatWithZero.gcd.nat (Integer.abs (numerator x)) (denominator x)
      = Nat.One.
Proof.
  intro x.
  destruct x as [n d h].
  simplify numerator, denominator in |- *.
  exact h.
Qed.


Module make. (* make *)

(* make.retraction *)
Theorem retraction
  : forall (x : Rational) . make (numerator x) (denominator x) = x.
Proof.
  intro x.
  destruct x as [n d h].
  simplify numerator, denominator in |- *.

  assert (whole : Integer.divide n Nat.One = n).
  {
    pose proof (Integer.division.exactness
                  n Nat.One
                  (NatWithZero.divisibility.bottom (Integer.abs n))) as e.
    pose proof (Integer.multiplication.right.identity
                  (Integer.divide n Nat.One)) as i.
    symmetry in i.
    exact (Identity.transitivity i e).
  }

  assert (undivided
          : NatWithZero.divide (NatWithZero.Positive d) (Nat.One)
          = NatWithZero.Positive d).
  {
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive d) (Nat.One)
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d)))
            as e.
    pose proof (NatWithZero.multiplication.right.identity
                  (NatWithZero.divide (NatWithZero.Positive d) (Nat.One))) as i.
    symmetry in i.
    exact (Identity.transitivity i e).
  }

  assert (same
          : NatWithZero.divide (NatWithZero.Positive d)
              (NatWithZero.gcd.nat (Integer.abs n) d)
          = NatWithZero.divide (NatWithZero.Positive d) (Nat.One)).
  {
    rewrite h in |- *.
    reflexivity.
  }

  apply extensionality.
  - simplify make      in |- *.
    simplify numerator in |- *.
    rewrite h in |- *.
    exact whole.
  - simplify make        in |- *.
    simplify denominator in |- *.
    pose proof (NatWithZero.divide.nat.safe.congruence
                  d (NatWithZero.gcd.nat (Integer.abs n) d)
                  (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)
                  d Nat.One
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d))
                  same)
            as c.
    pose proof (NatWithZero.divide.nat.safe.specification
                  d Nat.One
                  (NatWithZero.divisibility.bottom (NatWithZero.Positive d)))
            as s.
    rewrite undivided in s.
    pose proof (NatWithZero.positive.injectivity s) as inj.
    exact (Identity.transitivity c inj).
Qed.

(* make.invariance *)
Theorem invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      make (Integer.mul (Integer.Positive k) n) (Nat.mul k d) = make n d.
Proof.
  intros n d k.

  assert (common
          : NatWithZero.gcd.nat
              (Integer.abs (Integer.mul (Integer.Positive k) n))
              (Nat.mul k d)
          = Nat.mul k (NatWithZero.gcd.nat (Integer.abs n) d)).
  {
    pose proof (Integer.multiplication.magnitude (Integer.Positive k) n) as am.
    change (Integer.abs (Integer.Positive k))
      with (NatWithZero.Positive k) in am.
    rewrite am in |- *.
    pose proof (NatWithZero.gcd.nat.left.distributivity.of.multiplication
                  k d (Integer.abs n))
            as gd.
    symmetry in gd.
    exact gd.
  }

  simplify make in |- *.

  assert (top
          : Integer.divide
              (Integer.mul (Integer.Positive k) n)
              (NatWithZero.gcd.nat
                (Integer.abs (Integer.mul (Integer.Positive k) n))
                (Nat.mul k d))
          = Integer.divide n (NatWithZero.gcd.nat (Integer.abs n) d)).
  {
    rewrite common in |- *.
    exact (Integer.division.invariance
             n (NatWithZero.gcd.nat (Integer.abs n) d) k).
  }

  assert (bottom
          : NatWithZero.divide.nat.safe
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
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)).
  {
    apply NatWithZero.divide.nat.safe.congruence.
    rewrite common in |- *.
    pose proof (NatWithZero.division.invariance
                  (NatWithZero.Positive d)
                  (NatWithZero.gcd.nat (Integer.abs n) d) k)
            as inv.
    change (NatWithZero.mul (NatWithZero.Positive k) (NatWithZero.Positive d))
      with (NatWithZero.Positive (Nat.mul k d))
        in inv.
    exact inv.
  }

  apply extensionality.
  - simplify make      in |- *.
    simplify numerator in |- *.
    exact top.
  - simplify make        in |- *.
    simplify denominator in |- *.
    exact bottom.
Qed.

(* make.proportionality *)
Theorem proportionality
  : forall (a : Integer) (b : Nat) .
      Integer.mul (numerator (make a b)) (Integer.from_nat b)
      = Integer.mul a (Integer.from_nat (denominator (make a b))).
Proof.
  intros a b.
  simplify make in |- *.
  simplify numerator, denominator in |- *.

  assert (bottom
          : Nat.mul
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b))
              (NatWithZero.gcd.nat (Integer.abs a) b)
          = b).
  {
    pose proof (NatWithZero.divide.nat.safe.specification
                  b (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b)) as s.
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive b)
                  (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b)) as e.
    symmetry in s.
    rewrite s in e.
    exact (NatWithZero.positive.injectivity e).
  }

  assert (lifted
          : Integer.from_nat b
          = Integer.mul
              (Integer.from_nat
                (NatWithZero.divide.nat.safe
                    b (NatWithZero.gcd.nat (Integer.abs a) b)
                    (NatWithZero.gcd.nat.right.divisibility
                      (Integer.abs a) b)))
              (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b))).
  {
    pose proof (Identity.congruence Integer.from_nat bottom) as c.
    symmetry in c.
    rewrite c in |- *.
    reflexivity.
  }

  assert (whole
          : Integer.mul
              (Integer.divide a (NatWithZero.gcd.nat (Integer.abs a) b))
              (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b))
          = a).
  {
    exact (Integer.division.exactness
            a (NatWithZero.gcd.nat (Integer.abs a) b)
            (NatWithZero.gcd.nat.left.divisibility (Integer.abs a) b)).
  }

  rewrite lifted in |- *.
  rewrite (Integer.multiplication.commutativity
            (Integer.from_nat
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b)))
            (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b)))
    in |- *.
  pose proof (Identity.symmetry
                (Integer.multiplication.associativity
                  (Integer.divide a (NatWithZero.gcd.nat (Integer.abs a) b))
                  (Integer.from_nat (NatWithZero.gcd.nat (Integer.abs a) b))
                  (Integer.from_nat
                    (NatWithZero.divide.nat.safe
                      b (NatWithZero.gcd.nat (Integer.abs a) b)
                      (NatWithZero.gcd.nat.right.divisibility
                        (Integer.abs a) b)))))
          as assoc.
  rewrite assoc in |- *.
  rewrite whole in |- *.
  reflexivity.
Qed.

(* make.characterisation *)
Theorem characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      make a b = make c d
      <-> Integer.mul a (Integer.from_nat d)
          = Integer.mul c (Integer.from_nat b).
Proof.
  intros a b c d.

  assert (swap
          : forall (x : Integer) (y : Integer) (z : Integer) .
              Integer.mul (Integer.mul x y) z
              = Integer.mul (Integer.mul x z) y).
  {
    intros x y z.
    rewrite (Integer.multiplication.associativity x y z) in |- *.
    rewrite (Integer.multiplication.commutativity y z)   in |- *.
    pose proof (Identity.symmetry (Integer.multiplication.associativity x z y)) as h.
    rewrite h in |- *.
    reflexivity.
  }

  pose proof (proportionality a b) as P1.
  pose proof (proportionality c d) as P2.

  (* The third field is the irreducibility of each pair, handed over by the
   * case analysis rather than proved after it.
   *)
  destruct (make a b) as [p q I1] eqn:E1.
  destruct (make c d) as [r s I2] eqn:E2.
  simplify numerator, denominator in P1, P2.

  assert (nzq : ~ (Integer.from_nat q = Integer.Zero)).
  {
    unfold Negation in |- *.
    intro z.
    discriminate z.
  }

  assert (nzs : ~ (Integer.from_nat s = Integer.Zero)).
  {
    unfold Negation in |- *.
    intro z.
    discriminate z.
  }

  split.

  - intro e.
    pose proof (Identity.congruence numerator   e) as hp.
    pose proof (Identity.congruence denominator e) as hq.
    simplify numerator   in hp.
    simplify denominator in hq.
    rewrite hp in P1.
    rewrite hq in P1.

    assert (Q1 : Integer.mul (Integer.mul r (Integer.from_nat b))
                             (Integer.from_nat d)
                 = Integer.mul (Integer.mul a (Integer.from_nat s))
                               (Integer.from_nat d)).
    {
      rewrite P1 in |- *.
      reflexivity.
    }

    assert (Q2 : Integer.mul (Integer.mul r (Integer.from_nat d))
                             (Integer.from_nat b)
                 = Integer.mul (Integer.mul c (Integer.from_nat s))
                               (Integer.from_nat b)).
    {
      rewrite P2 in |- *.
      reflexivity.
    }

    rewrite (swap r (Integer.from_nat b) (Integer.from_nat d)) in Q1.
    symmetry in Q1.
    pose proof (Identity.transitivity Q1 Q2) as Q.
    rewrite (swap a (Integer.from_nat s) (Integer.from_nat d)) in Q.
    rewrite (swap c (Integer.from_nat s) (Integer.from_nat b)) in Q.
    rewrite (Integer.multiplication.commutativity
              (Integer.mul a (Integer.from_nat d))
              (Integer.from_nat s)) in Q.
    rewrite (Integer.multiplication.commutativity
              (Integer.mul c (Integer.from_nat b))
              (Integer.from_nat s)) in Q.
    exact (Integer.multiplication.cancellation
            (Integer.from_nat s) (Integer.mul a (Integer.from_nat d))
            (Integer.mul c (Integer.from_nat b)) nzs Q).

  - intro e.

    assert (nzbd
            : ~ (Integer.mul (Integer.from_nat b) (Integer.from_nat d)
            = Integer.Zero)).
    {
      unfold Negation in |- *.
      intro z.
      discriminate z.
    }

    assert (widened
            : Integer.mul (Integer.mul p (Integer.from_nat s))
                (Integer.mul (Integer.from_nat b) (Integer.from_nat d))
            = Integer.mul (Integer.mul r (Integer.from_nat q))
                (Integer.mul (Integer.from_nat b) (Integer.from_nat d))).
    {
      rewrite (Integer.multiplication.interchange
                p (Integer.from_nat s) (Integer.from_nat b) (Integer.from_nat d)) in |- *.
      rewrite P1 in |- *.
      rewrite (Integer.multiplication.commutativity (Integer.from_nat s) (Integer.from_nat d)) in |- *.
      rewrite (Integer.multiplication.interchange
                a (Integer.from_nat q) (Integer.from_nat d) (Integer.from_nat s)) in |- *.
      rewrite e in |- *.
      rewrite (Integer.multiplication.commutativity (Integer.from_nat q) (Integer.from_nat s)) in |- *.
      rewrite (Integer.multiplication.interchange
                c (Integer.from_nat b) (Integer.from_nat s) (Integer.from_nat q)) in |- *.
      pose proof (Identity.symmetry P2) as P2'.
      rewrite P2' in |- *.
      rewrite (Integer.multiplication.commutativity (Integer.from_nat b) (Integer.from_nat q)) in |- *.
      rewrite (Integer.multiplication.interchange
                r (Integer.from_nat d) (Integer.from_nat q) (Integer.from_nat b)) in |- *.
      rewrite (Integer.multiplication.commutativity (Integer.from_nat d) (Integer.from_nat b)) in |- *.
      reflexivity.
    }

    rewrite (Integer.multiplication.commutativity
              (Integer.mul p (Integer.from_nat s))
              (Integer.mul (Integer.from_nat b)
                           (Integer.from_nat d))) in widened.
    rewrite (Integer.multiplication.commutativity
              (Integer.mul r (Integer.from_nat q))
              (Integer.mul (Integer.from_nat b)
                           (Integer.from_nat d))) in widened.
    pose proof (Integer.multiplication.cancellation
                  (Integer.mul (Integer.from_nat b) (Integer.from_nat d))
                  (Integer.mul p (Integer.from_nat s))
                  (Integer.mul r (Integer.from_nat q))
                  nzbd widened) as cross.

    pose proof (Identity.congruence Integer.abs cross) as m.
    rewrite (Integer.multiplication.magnitude p (Integer.from_nat s)) in m.
    rewrite (Integer.multiplication.magnitude r (Integer.from_nat q)) in m.
    change (Integer.abs (Integer.from_nat s))
      with (NatWithZero.Positive s) in m.
    change (Integer.abs (Integer.from_nat q))
      with (NatWithZero.Positive q) in m.

    assert (coprime1
            : NatWithZero.gcd (NatWithZero.Positive q) (Integer.abs p)
            = NatWithZero.Positive Nat.One).
    {
      pose proof (NatWithZero.gcd.nat.specification q (Integer.abs p)) as g.
      rewrite I1 in g.
      rewrite (NatWithZero.gcd.commutativity
                (Integer.abs p) (NatWithZero.Positive q)) in g.
      exact g.
    }

    assert (coprime2
            : NatWithZero.gcd (NatWithZero.Positive s) (Integer.abs r)
            = NatWithZero.Positive Nat.One).
    {
      pose proof (NatWithZero.gcd.nat.specification s (Integer.abs r)) as g.
      rewrite I2 in g.
      rewrite (NatWithZero.gcd.commutativity (Integer.abs r)
                 (NatWithZero.Positive s)) in g.
      exact g.
    }

    assert (qs : NatWithZero.Divides (NatWithZero.Positive q) (NatWithZero.Positive s)).
    {
      pose proof (NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive q) (NatWithZero.Positive q)
                    (Integer.abs r)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive q)))
              as h.
      rewrite (NatWithZero.multiplication.commutativity
                (NatWithZero.Positive q) (Integer.abs r)) in h.
      pose proof (Identity.symmetry m) as m'.
      rewrite m' in h.
      exact (NatWithZero.gcd.multiplication.cancellation
              (NatWithZero.Positive q) (Integer.abs p)
              (NatWithZero.Positive s) h coprime1).
    }

    assert (sq : NatWithZero.Divides (NatWithZero.Positive s) (NatWithZero.Positive q)).
    {
      pose proof (NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive s) (NatWithZero.Positive s)
                    (Integer.abs p)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive s))) as h.
      rewrite (NatWithZero.multiplication.commutativity
                 (NatWithZero.Positive s) (Integer.abs p)) in h.
      rewrite m in h.
      exact (NatWithZero.gcd.multiplication.cancellation
               (NatWithZero.Positive s) (Integer.abs r)
               (NatWithZero.Positive q) h coprime2).
    }

    pose proof (NatWithZero.positive.injectivity (NatWithZero.divisibility.antisymmetry qs sq)) as hq.
    rewrite hq in cross.
    rewrite (Integer.multiplication.commutativity p (Integer.from_nat s)) in cross.
    rewrite (Integer.multiplication.commutativity r (Integer.from_nat s)) in cross.
    pose proof (Integer.multiplication.cancellation (Integer.from_nat s) p r nzs cross)
            as hp.
    apply extensionality.
    + simplify numerator in |- *.
      exact hp.
    + simplify denominator in |- *.
      exact hq.
Qed.

(* make.annihilation *)
Theorem annihilation
  : forall (b : Nat) . make Integer.Zero b = Zero.
Proof.
  intro b.

  assert (unit : make Integer.Zero Nat.One = Zero).
  {
    pose proof (retraction Zero) as r.
    change (numerator   Zero) with Integer.Zero in r.
    change (denominator Zero) with Nat.One  in r.
    exact r.
  }

  assert (cross
          : Integer.mul Integer.Zero (Integer.from_nat Nat.One)
          = Integer.mul Integer.Zero (Integer.from_nat b)).
  {
    rewrite (Integer.multiplication.left.annihilation (Integer.from_nat Nat.One)) in |- *.
    rewrite (Integer.multiplication.left.annihilation (Integer.from_nat b))     in |- *.
    reflexivity.
  }

  pose proof (characterisation Integer.Zero b Integer.Zero Nat.One) as criterion.
  modus aequans criterion, cross as joined.
  exact (Identity.transitivity joined unit).
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
  simplify add in |- *.

  pose proof (proportionality a b) as P1.
  pose proof (proportionality c d) as P2.

  destruct (make a b) as [p q I1] eqn:E1.
  destruct (make c d) as [r s I2] eqn:E2.
  simplify numerator, denominator in P1, P2.
  simplify numerator, denominator in |- *.

  set (b' := Integer.from_nat b) in *.
  set (d' := Integer.from_nat d) in *.
  set (q' := Integer.from_nat q) in *.
  set (s' := Integer.from_nat s) in *.

  assert (first
          : Integer.mul (Integer.mul p s') (Integer.mul b' d')
          = Integer.mul (Integer.mul a d') (Integer.mul q' s')).
  {
    rewrite (Integer.multiplication.interchange p s' b' d') in |- *.
    rewrite P1 in |- *.
    rewrite (Integer.multiplication.commutativity s' d') in |- *.
    rewrite (Integer.multiplication.interchange a q' d' s') in |- *.
    reflexivity.
  }

  assert (second
          : Integer.mul (Integer.mul r q') (Integer.mul b' d')
          = Integer.mul (Integer.mul c b') (Integer.mul q' s')).
  {
    rewrite (Integer.multiplication.commutativity b' d') in |- *.
    rewrite (Integer.multiplication.interchange r q' d' b') in |- *.
    rewrite P2 in |- *.
    rewrite (Integer.multiplication.commutativity q' b') in |- *.
    rewrite (Integer.multiplication.interchange c s' b' q') in |- *.
    rewrite (Integer.multiplication.commutativity s' q') in |- *.
    reflexivity.
  }

  assert (cross
          : Integer.mul (Integer.add (Integer.mul p s') (Integer.mul r q'))
                  (Integer.from_nat (Nat.mul b d))
          = Integer.mul (Integer.add (Integer.mul a d') (Integer.mul c b'))
                  (Integer.from_nat (Nat.mul q s))).
  {
    change (Integer.from_nat (Nat.mul b d))
      with (Integer.mul b' d')
        in |- *.
    change (Integer.from_nat (Nat.mul q s))
      with (Integer.mul q' s')
        in |- *.
    rewrite (Integer.multiplication.right.distributivity.over.addition
              (Integer.mul b' d') (Integer.mul p s') (Integer.mul r q')) in |- *.
    rewrite (Integer.multiplication.right.distributivity.over.addition
              (Integer.mul q' s') (Integer.mul a d') (Integer.mul c b')) in |- *.
    rewrite first  in |- *.
    rewrite second in |- *.
    reflexivity.
  }

  pose proof (characterisation
                (Integer.add (Integer.mul p s') (Integer.mul r q'))
                (Nat.mul q s)
                (Integer.add (Integer.mul a d') (Integer.mul c b'))
                (Nat.mul b d)) as criterion.
  modus aequans criterion, cross as joined.
  exact joined.
Qed.

End addition. (* make.addition *)

Module multiplication. (* make.multiplication *)

(* make.multiplication.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
    (make a b) * (make c d) = make (Integer.mul a c) (Nat.mul b d).
Proof.
  intros a b c d.
  simplify mul in |- *.

  pose proof (proportionality a b) as P1.
  pose proof (proportionality c d) as P2.

  destruct (make a b) as [p q I1] eqn:E1.
  destruct (make c d) as [r s I2] eqn:E2.
  simplify numerator, denominator in P1, P2.
  simplify numerator, denominator in |- *.

  assert (cross
          : Integer.mul (Integer.mul p r) (Integer.from_nat (Nat.mul b d))
          = Integer.mul (Integer.mul a c) (Integer.from_nat (Nat.mul q s))).
  {
    change (Integer.from_nat (Nat.mul b d))
      with (Integer.mul (Integer.from_nat b) (Integer.from_nat d))
        in |- *.
    change (Integer.from_nat (Nat.mul q s))
      with (Integer.mul (Integer.from_nat q) (Integer.from_nat s))
        in |- *.
    rewrite (Integer.multiplication.interchange
              p r (Integer.from_nat b) (Integer.from_nat d)) in |- *.
    rewrite P1 in |- *.
    rewrite P2 in |- *.
    rewrite (Integer.multiplication.interchange
              a (Integer.from_nat q) c (Integer.from_nat s)) in |- *.
    reflexivity.
  }

  pose proof (characterisation
                (Integer.mul p r) (Nat.mul q s)
                (Integer.mul a c) (Nat.mul b d)) as criterion.
  modus aequans criterion, cross as joined.
  exact joined.
Qed.

End multiplication. (* make.multiplication *)

Module negation. (* make.negation *)

(* make.negation.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) .
      negate (make a b) = make (Integer.negate a) b.
Proof.
  intros a b.
  simplify negate in |- *.

  pose proof (proportionality a b) as P1.

  destruct (make a b) as [p q I1] eqn:E1.
  simplify numerator, denominator in P1.
  simplify numerator, denominator in |- *.

  assert (cross
          : Integer.mul (Integer.negate p) (Integer.from_nat b)
          = Integer.mul (Integer.negate a) (Integer.from_nat q)).
  {
    rewrite (Integer.multiplication.left.negation p (Integer.from_nat b)) in |- *.
    rewrite (Integer.multiplication.left.negation a (Integer.from_nat q)) in |- *.
    rewrite P1 in |- *.
    reflexivity.
  }

  pose proof (characterisation
                (Integer.negate p) q (Integer.negate a) b) as criterion.
  modus aequans criterion, cross as joined.
  exact joined.
Qed.

End negation. (* make.negation *)

End make. (* make *)


Module addition. (* addition *)

(* addition.associativity *)
Theorem associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (x + y) + z = x + (y + z).
Proof.
  intros x y z.

  assert (general
          : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) (e : Integer) (f : Nat) .
              ((make a b) + (make c d)) + (make e f)
            = (make a b) + ((make c d) + (make e f))).
  {
    intros a b c d e f.
    rewrite (make.addition.homomorphism a b c d) in |- *.
    rewrite (make.addition.homomorphism c d e f) in |- *.
    rewrite (make.addition.homomorphism
               (Integer.add (Integer.mul a (Integer.from_nat d))
                      (Integer.mul c (Integer.from_nat b)))
               (Nat.mul b d)
               e f) in |- *.
    rewrite (make.addition.homomorphism
               a b
               (Integer.add (Integer.mul c (Integer.from_nat f))
                      (Integer.mul e (Integer.from_nat d)))
               (Nat.mul d f)) in |- *.

    set (b' := Integer.from_nat b) in *.
    set (d' := Integer.from_nat d) in *.
    set (f' := Integer.from_nat f) in *.

    change (Integer.from_nat (Nat.mul b d))
      with (Integer.mul b' d')
        in |- *.
    change (Integer.from_nat (Nat.mul d f))
      with (Integer.mul d' f')
        in |- *.

    assert (tops
            : Integer.add
                (Integer.mul (Integer.add (Integer.mul a d') (Integer.mul c b')) (f'))
                (Integer.mul (e) (Integer.mul b' d'))
            = Integer.add
                (Integer.mul (a) (Integer.mul d' f'))
                (Integer.mul (Integer.add (Integer.mul c f') (Integer.mul e d')) (b'))).
    {
      rewrite (Integer.multiplication.right.distributivity.over.addition
                f' (Integer.mul a d') (Integer.mul c b')) in |- *.
      rewrite (Integer.multiplication.right.distributivity.over.addition
                b' (Integer.mul c f') (Integer.mul e d')) in |- *.
      rewrite (Integer.addition.associativity
                (Integer.mul (Integer.mul a d') f')
                (Integer.mul (Integer.mul c b') f')
                (Integer.mul e (Integer.mul b' d'))) in |- *.
      rewrite (Integer.multiplication.associativity a d' f') in |- *.
      rewrite (Integer.multiplication.associativity c b' f') in |- *.
      rewrite (Integer.multiplication.associativity c f' b') in |- *.
      rewrite (Integer.multiplication.associativity e d' b') in |- *.
      rewrite (Integer.multiplication.commutativity b' f') in |- *.
      rewrite (Integer.multiplication.commutativity b' d') in |- *.
      reflexivity.
    }

    rewrite tops in |- *.
    rewrite (Nat.multiplication.associativity b d f) in |- *.
    reflexivity.
  }

  pose proof (general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z)) as g.
  rewrite (make.retraction x) in g.
  rewrite (make.retraction y) in g.
  rewrite (make.retraction z) in g.
  exact g.
Qed.

(* addition.commutativity *)
Theorem commutativity
  : forall (x : Rational) (y : Rational) . x + y = y + x.
Proof.
  intros x y.
  simplify add in |- *.
  rewrite (Integer.addition.commutativity
            (Integer.mul (numerator x) (Integer.from_nat (denominator y)))
            (Integer.mul (numerator y) (Integer.from_nat (denominator x)))) in |- *.
  rewrite (Nat.multiplication.commutativity (denominator x) (denominator y)) in |- *.
  reflexivity.
Qed.

Module left. (* addition.left *)

(* addition.left.identity *)
  Theorem identity : forall (x : Rational) . Zero + x = x.
Proof.
  intro x.
  simplify add in |- *.
  change (numerator Zero)
    with Integer.Zero
      in |- *.
  change (denominator Zero)
    with Nat.One
      in |- *.
  change (Integer.from_nat Nat.One)
    with (Integer.Positive Nat.One)
      in |- *.
  change (Nat.mul Nat.One (denominator x)) with (denominator x) in |- *.
  rewrite (Integer.multiplication.left.annihilation
             (Integer.from_nat (denominator x))) in |- *.
  rewrite (Integer.addition.left.identity
             (Integer.mul (numerator x)
                          (Integer.Positive Nat.One))) in |- *.
  rewrite (Integer.multiplication.right.identity (numerator x)) in |- *.
  exact (make.retraction x).
Qed.

(* addition.left.inverse *)
Theorem inverse : forall (x : Rational) . (negate x) + x = Zero.
Proof.
  intro x.

  assert (general
          : forall (a : Integer) (b : Nat) . (negate (make a b)) + (make a b) = Zero).
  {
    intros a b.
    rewrite (make.negation.homomorphism a b) in |- *.
    rewrite (make.addition.homomorphism (Integer.negate a) b a b) in |- *.
    rewrite (Integer.multiplication.left.negation (a) (Integer.from_nat b)) in |- *.
    rewrite (Integer.addition.left.inverse (Integer.mul a (Integer.from_nat b))) in |- *.
    exact (make.annihilation (Nat.mul b b)).
  }

  pose proof (general (numerator x) (denominator x)) as g.
  rewrite (make.retraction x) in g.
  exact g.
Qed.

(* addition.left.cancellation *)
Theorem cancellation
  : forall (k : Rational) (m : Rational) (n : Rational) .
      k + m = k + n -> m = n.
Proof.
  intros k m n e.

  pose proof (associativity (negate k) k m) as am.
  rewrite (inverse k)  in am.
  rewrite (identity m) in am.

  pose proof (associativity (negate k) k n) as an.
  rewrite (inverse k)  in an.
  rewrite (identity n) in an.

  pose proof (Identity.congruence
                (fun (t : Rational) . add (negate k) t)
                (e)) as h.
  simplify in h.

  symmetry in an.
  exact (Identity.transitivity am (Identity.transitivity h an)).
Qed.

End left. (* addition.left *)

Module right. (* addition.right *)

(* addition.right.identity *)
  Theorem identity : forall (x : Rational) . x + Zero = x.
Proof.
  intro x.
  simplify add in |- *.
  change (numerator   Zero) with Integer.Zero in |- *.
  change (denominator Zero) with Nat.One  in |- *.
  change (Integer.from_nat Nat.One) with (Integer.Positive Nat.One) in |- *.
  rewrite (Integer.multiplication.right.identity (numerator x)) in |- *.
  rewrite (Integer.multiplication.left.annihilation (Integer.from_nat (denominator x))) in |- *.
  rewrite (Integer.addition.right.identity (numerator x)) in |- *.
  destruct (Nat.multiplication.identity (denominator x)) as [_ unit].
  rewrite unit in |- *.
  exact (make.retraction x).
Qed.

(* addition.right.inverse *)
Theorem inverse : forall (x : Rational) . x + (negate x) = Zero.
Proof.
  intro x.

  assert (general
          : forall (a : Integer) (b : Nat) .
              add (make a b) (negate (make a b)) = Zero).
  {
    intros a b.
    rewrite (make.negation.homomorphism a b) in |- *.
    rewrite (make.addition.homomorphism a b (Integer.negate a) b) in |- *.
    rewrite (Integer.multiplication.left.negation
               a (Integer.from_nat b)) in |- *.
    rewrite (Integer.addition.right.inverse
               (Integer.mul a (Integer.from_nat b))) in |- *.
    exact (make.annihilation (Nat.mul b b)).
  }

  pose proof (general (numerator x) (denominator x)) as g.
  rewrite (make.retraction x) in g.
  exact g.
Qed.

(* addition.right.cancellation *)
Theorem cancellation
  : forall (k : Rational) (m : Rational) (n : Rational) .
      add m k = add n k -> m = n.
Proof.
  intros k m n e.

  pose proof (associativity m k (negate k)) as am.
  rewrite (inverse k)  in am.
  rewrite (identity m) in am.

  pose proof (associativity n k (negate k)) as an.
  rewrite (inverse k)  in an.
  rewrite (identity n) in an.

  pose proof (Identity.congruence (fun (t : Rational) . add t (negate k)) e)
          as h.
  simplify in h.

  symmetry in am.
  exact (Identity.transitivity am (Identity.transitivity h an)).
Qed.

End right. (* addition.right *)

(* addition.identity *)
Theorem identity
  : forall (x : Rational) . (Zero + x = x) /\ (x + Zero = x).
Proof.
  intro x.
  split.
  - exact (left.identity  x).
  - exact (right.identity x).
Qed.

(* addition.inverse *)
Theorem inverse
  : forall (x : Rational) .
      ((negate x) + x = Zero) /\ (x + (negate x) = Zero).
Proof.
  intro x.
  split.
  - exact (left.inverse  x).
  - exact (right.inverse x).
Qed.

(* addition.cancellation *)
Theorem cancellation
  : forall (m : Rational) (n : Rational) (k : Rational) .
      (m + n = m + k -> n = k) /\ (m + n = k + n -> m = k).
Proof.
  intros m n k.
  split.
  - exact (left.cancellation  m n k).
  - exact (right.cancellation n m k).
Qed.

End addition. (* addition *)


Module multiplication. (* multiplication *)

(* multiplication.commutativity *)
Theorem commutativity
  : forall (x : Rational) (y : Rational) . x * y = y * x.
Proof.
  intros x y.
  simplify mul in |- *.
  rewrite (Integer.multiplication.commutativity (numerator   x) (numerator   y)) in |- *.
  rewrite (Nat.multiplication.commutativity (denominator x) (denominator y)) in |- *.
  reflexivity.
Qed.

(* multiplication.associativity *)
Theorem associativity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (x * y) * z = x * (y * z).
Proof.
  intros x y z.

  assert (general
          : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) (e : Integer) (f : Nat) .
              ((make a b) * (make c d)) * (make e f)
            = (make a b) * ((make c d) * (make e f))).
  {
    intros a b c d e f.
    rewrite (make.multiplication.homomorphism a b c d) in |- *.
    rewrite (make.multiplication.homomorphism c d e f) in |- *.
    rewrite (make.multiplication.homomorphism
              (Integer.mul a c) (Nat.mul b d) e f) in |- *.
    rewrite (make.multiplication.homomorphism
              a b (Integer.mul c e) (Nat.mul d f)) in |- *.
    rewrite (Integer.multiplication.associativity a c e) in |- *.
    rewrite (Nat.multiplication.associativity b d f) in |- *.
    reflexivity.
  }

  pose proof (general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z)) as g.
  rewrite (make.retraction x) in g.
  rewrite (make.retraction y) in g.
  rewrite (make.retraction z) in g.
  exact g.
Qed.

Module left. (* multiplication.left *)

(* multiplication.left.identity *)
Theorem identity : forall (x : Rational) . mul One x = x.
Proof.
  intro x.
  simplify mul in |- *.
  change (numerator   One) with (Integer.Positive Nat.One) in |- *.
  change (denominator One) with Nat.One              in |- *.
  change (Nat.mul Nat.One (denominator x)) with (denominator x) in |- *.
  rewrite (Integer.multiplication.left.identity (numerator x)) in |- *.
  exact (make.retraction x).
Qed.

(* multiplication.left.annihilation *)
Theorem annihilation : forall (x : Rational) . Zero * x = Zero.
Proof.
  intro x.
  simplify mul in |- *.
  change (numerator   Zero) with Integer.Zero in |- *.
  change (denominator Zero) with Nat.One  in |- *.
  change (Nat.mul Nat.One (denominator x)) with (denominator x)  in |- *.
  rewrite (Integer.multiplication.left.annihilation (numerator x)) in |- *.
  exact (make.annihilation (denominator x)).
Qed.

Module distributivity. (* multiplication.left.distributivity *)

Module over. (* multiplication.left.distributivity.over *)

(* multiplication.left.distributivity.over.addition *)
Theorem addition
  : forall (x : Rational) (y : Rational) (z : Rational) .
      x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.

  assert (general
          : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat)
              (e : Integer) (f : Nat) .
              (make a b) * ((make c d) + (make e f))
            = ((make a b) * (make c d)) + ((make a b) * (make e f))).
  {
    intros a b c d e f.
    rewrite (make.addition.homomorphism c d e f) in |- *.
    rewrite (make.multiplication.homomorphism
              a b
              (Integer.add (Integer.mul c (Integer.from_nat f))
                     (Integer.mul e (Integer.from_nat d)))
              (Nat.mul d f)) in |- *.
    rewrite (make.multiplication.homomorphism a b c d) in |- *.
    rewrite (make.multiplication.homomorphism a b e f) in |- *.
    rewrite (make.addition.homomorphism
              (Integer.mul a c) (Nat.mul b d)
              (Integer.mul a e) (Nat.mul b f)) in |- *.

    set (b' := Integer.from_nat b) in *.
    set (d' := Integer.from_nat d) in *.
    set (f' := Integer.from_nat f) in *.

    change (Integer.from_nat (Nat.mul b f))
      with (Integer.mul b' f')
        in |- *.
    change (Integer.from_nat (Nat.mul b d))
      with (Integer.mul b' d')
        in |- *.

    assert (tops
            : Integer.add
                (Integer.mul (Integer.mul a c) (Integer.mul b' f'))
                (Integer.mul (Integer.mul a e) (Integer.mul b' d'))
            = Integer.mul b'
                (Integer.mul
                  (a)
                  (Integer.add (Integer.mul c f') (Integer.mul e d')))).
    {
      rewrite (Integer.multiplication.left.distributivity.over.addition
                a (Integer.mul c f') (Integer.mul e d')) in |- *.
      rewrite (Integer.multiplication.left.distributivity.over.addition
                b'
                (Integer.mul a (Integer.mul c f'))
                (Integer.mul a (Integer.mul e d'))) in |- *.
      rewrite (Integer.multiplication.interchange a c b' f') in |- *.
      rewrite (Integer.multiplication.interchange a e b' d') in |- *.
      rewrite (Integer.multiplication.commutativity a b') in |- *.
      rewrite (Integer.multiplication.associativity
                b' a (Integer.mul c f')) in |- *.
      rewrite (Integer.multiplication.associativity
                b' a (Integer.mul e d')) in |- *.
      reflexivity.
    }

    assert (bots
            : Nat.mul
                (Nat.mul b d)
                (Nat.mul b f)
            = Nat.mul
                (b)
                (Nat.mul b (Nat.mul d f))).
    {
      rewrite (Nat.multiplication.associativity b d (Nat.mul b f)) in |- *.
      rewrite (Nat.multiplication.commutativity d (Nat.mul b f)) in |- *.
      rewrite (Nat.multiplication.associativity b f d) in |- *.
      rewrite (Nat.multiplication.commutativity f d) in |- *.
      reflexivity.
    }

    rewrite tops in |- *.
    rewrite bots in |- *.
    symmetry in |- *.
    exact (make.invariance
            (Integer.mul (a) (Integer.add (Integer.mul c f') (Integer.mul e d')))
            (Nat.mul (b) (Nat.mul d f))
            (b)).
  }

  pose proof (general
                (numerator x) (denominator x)
                (numerator y) (denominator y)
                (numerator z) (denominator z)) as g.
  rewrite (make.retraction x) in g.
  rewrite (make.retraction y) in g.
  rewrite (make.retraction z) in g.
  exact g.
Qed.

End over. (* multiplication.left.distributivity.over *)

End distributivity. (* multiplication.left.distributivity *)

End left. (* multiplication.left *)

Module right. (* multiplication.right *)

(* multiplication.right.identity *)
  Theorem identity : forall (x : Rational) . x * One = x.
Proof.
  intro x.
  rewrite (commutativity x One) in |- *.
  exact (left.identity x).
Qed.

(* multiplication.right.annihilation *)
Theorem annihilation : forall (x : Rational) . x * Zero = Zero.
Proof.
  intro x.
  rewrite (commutativity x Zero) in |- *.
  exact (left.annihilation x).
Qed.

Module distributivity. (* multiplication.right.distributivity *)

Module over. (* multiplication.right.distributivity.over *)

(* multiplication.right.distributivity.over.addition *)
Theorem addition
  : forall (x : Rational) (y : Rational) (z : Rational) .
      (y + z) * x = (y * x) + (z * x).
Proof.
  intros x y z.
  rewrite (commutativity (y + z) x) in |- *.
  rewrite (left.distributivity.over.addition x y z) in |- *.
  rewrite (commutativity x y) in |- *.
  rewrite (commutativity x z) in |- *.
  reflexivity.
Qed.

End over. (* multiplication.right.distributivity.over *)

End distributivity. (* multiplication.right.distributivity *)

End right. (* multiplication.right *)

(* multiplication.identity *)
Theorem identity
  : forall (x : Rational) . (One * x = x) /\ (x * One = x).
Proof.
  intro x.
  split.
  - exact (left.identity  x).
  - exact (right.identity x).
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
  split.
  - exact (left.distributivity.over.addition  x y z).
  - exact (right.distributivity.over.addition x y z).
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

  assert (unit : make (Integer.Positive Nat.One) Nat.One = One).
  {
    pose proof (make.retraction One) as r.
    change (numerator   One) with (Integer.Positive Nat.One) in r.
    change (denominator One) with Nat.One              in r.
    exact r.
  }

  pose proof (make.retraction x) as r.
  simplify inverse in e.
  destruct (numerator x) as [p | | p] eqn:E.

  - pose proof (Option.some.injectivity e) as hy.
    symmetry in r.
    rewrite r in |- *.
    symmetry in hy.
    rewrite hy in |- *.
    set (d := denominator x) in *.
    rewrite (make.multiplication.homomorphism (Integer.Negative p) (d) (Integer.Negative d) (p)) in |- *.
    change (Integer.mul (Integer.Negative p) (Integer.Negative d))
      with (Integer.Positive (Nat.mul p d))
        in |- *.

    assert (cross
            : Integer.mul (Integer.Positive (Nat.mul p d))
                    (Integer.from_nat Nat.One)
            = Integer.mul (Integer.Positive Nat.One)
                    (Integer.from_nat (Nat.mul d p))).
    {
      change (Integer.from_nat Nat.One)
        with (Integer.Positive Nat.One)
          in |- *.
      change (Integer.from_nat (Nat.mul d p))
        with (Integer.Positive (Nat.mul d p))
          in |- *.
      rewrite (Integer.multiplication.right.identity
                (Integer.Positive (Nat.mul p d))) in |- *.
      rewrite (Integer.multiplication.left.identity
                (Integer.Positive (Nat.mul d p))) in |- *.
      rewrite (Nat.multiplication.commutativity p d) in |- *.
      reflexivity.
    }

    pose proof (make.characterisation
                  (Integer.Positive (Nat.mul p d))
                  (Nat.mul d p)
                  (Integer.Positive Nat.One)
                  (Nat.One)) as criterion.
    modus aequans criterion, cross as joined.
    exact (Identity.transitivity joined unit).

  - discriminate e.

  - pose proof (Option.some.injectivity e) as hy.
    symmetry in r.
    rewrite r in |- *.
    symmetry in hy.
    rewrite hy in |- *.
    set (d := denominator x) in *.
    rewrite (make.multiplication.homomorphism
              (Integer.Positive p) (d)
              (Integer.Positive d) (p)) in |- *.
    change (Integer.mul (Integer.Positive p) (Integer.Positive d))
      with (Integer.Positive (Nat.mul p d))
        in |- *.

    assert (cross
            : Integer.mul (Integer.Positive (Nat.mul p d))
                    (Integer.from_nat Nat.One)
            = Integer.mul (Integer.Positive Nat.One)
                    (Integer.from_nat (Nat.mul d p))).
    {
      change (Integer.from_nat Nat.One) with (Integer.Positive Nat.One) in |- *.
      change (Integer.from_nat (Nat.mul d p)) with (Integer.Positive (Nat.mul d p)) in |- *.
      rewrite (Integer.multiplication.right.identity (Integer.Positive (Nat.mul p d))) in |- *.
      rewrite (Integer.multiplication.left.identity (Integer.Positive (Nat.mul d p))) in |- *.
      rewrite (Nat.multiplication.commutativity p d) in |- *.
      reflexivity.
    }

    pose proof (make.characterisation
                  (Integer.Positive (Nat.mul p d))
                  (Nat.mul d p)
                  (Integer.Positive Nat.One)
                  (Nat.One)) as criterion.
    modus aequans criterion, cross as joined.
    exact (Identity.transitivity joined unit).
Qed.

End inverse. (* inverse *)

Local Close Scope jwa_rational_scope.

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.

(* Makes the notations declared in [Module Rational] usable in every file
 * that imports this one, as [(x + y)%rational]. Only the notations are
 * exported: [add] and the laws still need the [Rational.] prefix.
 *)
Export (notations) Rational.

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
