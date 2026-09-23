(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Number.Integer.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
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

(* [Rational -> Rational -> Rational] *)
Definition sub := fun (x : Rational) (y : Rational) . let y := negate y in add x y.

(* [Rational -> Rational -> Rational] *)
Definition mul := fun (x : Rational) (y : Rational) .
  let n := Integer.mul (numerator x) (numerator y)
  in
  let d := Nat.mul (denominator x) ( denominator y)
  in
  make n d.

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

(* Two fractions in lowest terms that agree as fractions are the same value.
 * The third field is an equation between two [Nat]s, and such an equation
 * is proved in only one way, so it cannot tell them apart.
 *)
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

(* Nothing is in the type that is not in lowest terms; this is the field the
 * ctor demands, read back off an arbitrary value.
 *)
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

Local Open Scope jwa_integer_scope.

(* make.invariance *)
Theorem invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      make ((Integer.Positive k) * n) (Nat.mul k d) = make n d.
Proof.
  intros n d k.

  assert (common
          : NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d)
          = Nat.mul k (NatWithZero.gcd.nat (| n |) d)).
  {
    pose proof (Integer.multiplication.magnitude (Integer.Positive k) n) as am.
    change (| Integer.Positive k |) with (NatWithZero.Positive k) in am.
    rewrite am in |- *.
    pose proof (NatWithZero.gcd.nat.left.distributivity.of.multiplication k d (| n |))
            as gd.
    symmetry in gd.
    exact gd.
  }

  simplify make in |- *.

  assert (top
          : ((Integer.Positive k) * n) /. (NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d))
          = n /. (NatWithZero.gcd.nat (| n |) d)).
  {
    rewrite common in |- *.
    exact (Integer.division.invariance n (NatWithZero.gcd.nat (| n |) d) k).
  }

  assert (bottom
          : NatWithZero.divide.nat.safe
                (Nat.mul k d)
                (NatWithZero.gcd.nat (| (Integer.Positive k) * n |) (Nat.mul k d))
                (NatWithZero.gcd.nat.right.divisibility (| (Integer.Positive k) * n |) (Nat.mul k d))
          = NatWithZero.divide.nat.safe
                d
                (NatWithZero.gcd.nat (| n |) d)
                (NatWithZero.gcd.nat.right.divisibility (| n |) d)).
  {
    apply NatWithZero.divide.nat.safe.congruence.
    rewrite common in |- *.
    pose proof (NatWithZero.division.invariance
                  (NatWithZero.Positive d)
                  (NatWithZero.gcd.nat (| n |) d) k)
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
      (numerator (make a b)) * (Integer.from_nat b)
      = a * (Integer.from_nat (denominator (make a b))).
Proof.
  intros a b.
  simplify make in |- *.
  simplify numerator, denominator in |- *.

  assert (bottom
          : Nat.mul
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (| a |) b)
                (NatWithZero.gcd.nat.right.divisibility (| a |) b))
              (NatWithZero.gcd.nat (| a |) b)
          = b).
  {
    pose proof (NatWithZero.divide.nat.safe.specification
                  b (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)) as s.
    pose proof (NatWithZero.division.exactness
                  (NatWithZero.Positive b) (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)) as e.
    symmetry in s.
    rewrite s in e.
    exact (NatWithZero.positive.injectivity e).
  }

  assert (lifted
          : Integer.from_nat b
          = (Integer.from_nat
              (NatWithZero.divide.nat.safe
                  b (NatWithZero.gcd.nat (| a |) b)
                  (NatWithZero.gcd.nat.right.divisibility (| a |) b)))
            * (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))).
  {
    pose proof (Identity.congruence Integer.from_nat bottom) as c.
    symmetry in c.
    rewrite c in |- *.
    reflexivity.
  }

  assert (whole
          : (a /. (NatWithZero.gcd.nat (| a |) b)) * (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))
          = a).
  {
    exact (Integer.division.exactness
            a (NatWithZero.gcd.nat (| a |) b)
            (NatWithZero.gcd.nat.left.divisibility (| a |) b)).
  }

  rewrite lifted in |- *.
  rewrite (Integer.multiplication.commutativity
            (Integer.from_nat
              (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (| a |) b)
                (NatWithZero.gcd.nat.right.divisibility (| a |) b)))
            (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))) in |- *.
  pose proof (Identity.symmetry
                (Integer.multiplication.associativity
                  (a /. (NatWithZero.gcd.nat (| a |) b))
                  (Integer.from_nat (NatWithZero.gcd.nat (| a |) b))
                  (Integer.from_nat
                    (NatWithZero.divide.nat.safe
                      b (NatWithZero.gcd.nat (| a |) b)
                      (NatWithZero.gcd.nat.right.divisibility (| a |) b)))))
          as assoc.
  rewrite assoc in |- *.
  rewrite whole in |- *.
  reflexivity.
Qed.

(* make.characterisation *)
Theorem characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      make a b = make c d
      <-> a * (Integer.from_nat d) = c * (Integer.from_nat b).
Proof.
  intros a b c d.

  assert (swap
          : forall (x : Integer) (y : Integer) (z : Integer) . (x * y) * z = (x * z) * y).
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

    assert (Q1 : (r * (Integer.from_nat b)) * (Integer.from_nat d)
                 = (a * (Integer.from_nat s)) * (Integer.from_nat d)).
    {
      rewrite P1 in |- *.
      reflexivity.
    }

    assert (Q2 : (r * (Integer.from_nat d)) * (Integer.from_nat b)
                 = (c * (Integer.from_nat s)) * (Integer.from_nat b)).
    {
      rewrite P2 in |- *.
      reflexivity.
    }

    rewrite (swap r (Integer.from_nat b) (Integer.from_nat d)) in Q1.
    symmetry in Q1.
    pose proof (Identity.transitivity Q1 Q2) as Q.
    rewrite (swap a (Integer.from_nat s) (Integer.from_nat d)) in Q.
    rewrite (swap c (Integer.from_nat s) (Integer.from_nat b)) in Q.
    rewrite (Integer.multiplication.commutativity (a * (Integer.from_nat d)) (Integer.from_nat s)) in Q.
    rewrite (Integer.multiplication.commutativity (c * (Integer.from_nat b)) (Integer.from_nat s)) in Q.
    exact (Integer.multiplication.cancellation
            (Integer.from_nat s) (a * (Integer.from_nat d))
            (c * (Integer.from_nat b)) nzs Q).

  - intro e.

    assert (nzbd
            : ~ ((Integer.from_nat b) * (Integer.from_nat d)
            = Integer.Zero)).
    {
      unfold Negation in |- *.
      intro z.
      discriminate z.
    }

    assert (widened
            : (p * (Integer.from_nat s)) * ((Integer.from_nat b) * (Integer.from_nat d))
            = (r * (Integer.from_nat q)) * ((Integer.from_nat b) * (Integer.from_nat d))).
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
              (p * (Integer.from_nat s))
              ((Integer.from_nat b) * (Integer.from_nat d))) in widened.
    rewrite (Integer.multiplication.commutativity
              (r * (Integer.from_nat q))
              ((Integer.from_nat b) * (Integer.from_nat d))) in widened.
    pose proof (Integer.multiplication.cancellation
                  ((Integer.from_nat b) * (Integer.from_nat d))
                  (p * (Integer.from_nat s)) (r * (Integer.from_nat q))
                  nzbd widened) as cross.

    pose proof (Identity.congruence Integer.abs cross) as m.
    rewrite (Integer.multiplication.magnitude p (Integer.from_nat s)) in m.
    rewrite (Integer.multiplication.magnitude r (Integer.from_nat q)) in m.
    change (| Integer.from_nat s |) with (NatWithZero.Positive s) in m.
    change (| Integer.from_nat q |) with (NatWithZero.Positive q) in m.

    assert (coprime1
            : NatWithZero.gcd (NatWithZero.Positive q) (| p |)
            = NatWithZero.Positive Nat.One).
    {
      pose proof (NatWithZero.gcd.nat.specification q (| p |)) as g.
      rewrite I1 in g.
      rewrite (NatWithZero.gcd.commutativity (| p |) (NatWithZero.Positive q)) in g.
      exact g.
    }

    assert (coprime2
            : NatWithZero.gcd (NatWithZero.Positive s) (| r |)
            = NatWithZero.Positive Nat.One).
    {
      pose proof (NatWithZero.gcd.nat.specification s (| r |)) as g.
      rewrite I2 in g.
      rewrite (NatWithZero.gcd.commutativity (| r |)
                 (NatWithZero.Positive s)) in g.
      exact g.
    }

    assert (qs : NatWithZero.Divides (NatWithZero.Positive q) (NatWithZero.Positive s)).
    {
      pose proof (NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive q) (NatWithZero.Positive q) (| r |)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive q)))
              as h.
      rewrite (NatWithZero.multiplication.commutativity
                (NatWithZero.Positive q) (| r |)) in h.
      pose proof (Identity.symmetry m) as m'.
      rewrite m' in h.
      exact (NatWithZero.gcd.multiplication.cancellation
              (NatWithZero.Positive q) (| p |)
              (NatWithZero.Positive s) h coprime1).
    }

    assert (sq : NatWithZero.Divides (NatWithZero.Positive s) (NatWithZero.Positive q)).
    {
      pose proof (NatWithZero.divisibility.multiplication.closure
                    (NatWithZero.Positive s) (NatWithZero.Positive s) (| p |)
                    (NatWithZero.divisibility.reflexivity (NatWithZero.Positive s))) as h.
      rewrite (NatWithZero.multiplication.commutativity
                 (NatWithZero.Positive s) (| p |)) in h.
      rewrite m in h.
      exact (NatWithZero.gcd.multiplication.cancellation
               (NatWithZero.Positive s) (| r |)
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

Local Close Scope jwa_integer_scope.

End make. (* make *)

End Rational. (* Rational *)

Abbreviation Rational := Rational.T.
