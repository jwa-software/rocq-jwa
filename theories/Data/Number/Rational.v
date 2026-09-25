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
From jwa Require Import Tactics.Equation.
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
  let numerator   := (n /. g)%integer
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
        : (Integer.abs Integer.Zero %. Nat.One)%nat_with_zero = NatWithZero.Zero)).

(* [Rational] *)
Definition One :=
  Rational_introduction Nat.One Nat.One
    (NatWithZero.gcd.nat.zero
      (Integer.abs Nat.One)
      (Nat.One)
      ((Identity.reflexivity NatWithZero.Zero)
        : (Integer.abs Nat.One %. Nat.One)%nat_with_zero = NatWithZero.Zero)).

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
  let dx' : Integer := dx in
  let dy' : Integer := dy in
  let n := (nx * dy' + ny * dx')%integer in
  let d := (dx * dy)%nat in
  make n d.

Notation "x + y" := (add x y) (only parsing)
  : jwa_rational_scope.

(* [Rational -> Rational -> Rational] *)
Definition sub := fun (x : Rational) (y : Rational) . let y := negate y in add x y.

(* [Rational -> Rational -> Rational] *)
Definition mul := fun (x : Rational) (y : Rational) .
  let n := (numerator x * numerator y)%integer
  in
  let d := (denominator x *  denominator y)%nat
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
  | Integer.Positive n => let d : Integer := d in Some (make d n)
  end.

(* [Rational -> Rational -> Prop] *)
Definition LessThan := fun (x : Rational) (y : Rational) .
  ((numerator x * denominator y)%integer
   < (numerator y * denominator x)%integer)%integer.

Notation "x < y" := (LessThan x y) (only parsing)
  : jwa_rational_scope.

(* [Rational -> Rational -> Prop] *)
Definition LessOrEqual := fun (x : Rational) (y : Rational) .
  x = y \/ (x < y)%rational.

Notation "x <= y" := (LessOrEqual x y) (only parsing)
  : jwa_rational_scope.
Notation "x > y" := (LessThan y x) (only parsing)
  : jwa_rational_scope.
Notation "x >= y" := (LessOrEqual y x) (only parsing)
  : jwa_rational_scope.

Notation "'(<)'" := LessThan (only parsing)
  : jwa_rational_scope.
Notation "'(<=)'" := LessOrEqual (only parsing)
  : jwa_rational_scope.

(* [Rational -> Rational -> Comparison] *)
Definition compare := fun (x : Rational) (y : Rational) .
  Integer.compare
    (numerator x * denominator y)%integer
    (numerator y * denominator x)%integer.

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

  lemma whole : (n /. Nat.One)%integer = n.
  {
    let proof e := Integer.division.exactness
                  n Nat.One
                  (NatWithZero.divisibility.bottom (Integer.abs n)).
    let proof i := Integer.multiplication.right.identity
                  (n /. Nat.One)%integer.
    symm in i.
    ipso (Identity.transitivity i e).
  }

  lemma undivided : (d /. (Nat.One))%nat_with_zero
          = d.
  {
    let proof e := NatWithZero.division.exactness
                  d (Nat.One)
                  (NatWithZero.divisibility.bottom d).
    let proof i := NatWithZero.multiplication.right.identity
                  (d /. (Nat.One))%nat_with_zero.
    symm in i.
    ipso (Identity.transitivity i e).
  }

  lemma same : (d /. NatWithZero.gcd.nat (Integer.abs n) d)%nat_with_zero
          = (d /. (Nat.One))%nat_with_zero.
  {
    leibniz h in |- *.
    quod idem est.
  }

  lemma top : numerator (make &n &d) = numerator (Rational_introduction &n &d &h).
  {
    simpl make      in |- *.
    simpl numerator in |- *.
    leibniz h in |- *.
    ipso whole.
  }
  lemma bottom : denominator (make &n &d) = denominator (Rational_introduction &n &d &h).
  {
    simpl make        in |- *.
    simpl denominator in |- *.
    let proof c := NatWithZero.divide.nat.safe.congruence
                  d (NatWithZero.gcd.nat (Integer.abs n) d)
                  (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d)
                  d Nat.One
                  (NatWithZero.divisibility.bottom d)
                  same.
    let proof s := NatWithZero.divide.nat.safe.specification
                  d Nat.One
                  (NatWithZero.divisibility.bottom d).
    leibniz undivided in s.
    let proof inj := NatWithZero.positive.injectivity s.
    ipso (Identity.transitivity c inj).
  }
  ipso (extensionality _ _ &top &bottom).
Qed.

(* make.invariance *)
Theorem invariance
  : forall (n : Integer) (d : Nat) (k : Nat) .
      make (k * n)%integer (k * d)%nat = make n d.
Proof.
  intros n d k.

  lemma common : NatWithZero.gcd.nat
              (Integer.abs (k * n)%integer)
              (k * d)%nat
          = (k * NatWithZero.gcd.nat (Integer.abs n) d)%nat.
  {
    let proof am := Integer.multiplication.magnitude k n.
    let proof am
      : Integer.abs (k * n)%integer
        = (k * Integer.abs n)%nat_with_zero
      := &am.
    leibniz am in |- *.
    let proof gd := NatWithZero.gcd.nat.left.distributivity.of.multiplication
                  k d (Integer.abs n).
    symm in gd.
    ipso gd.
  }

  simpl make in |- *.

  lemma top : (k * n /. NatWithZero.gcd.nat
                (Integer.abs (k * n)%integer)
                (k * d)%nat)%integer
          = (n /. NatWithZero.gcd.nat (Integer.abs n) d)%integer.
  {
    leibniz common in |- *.
    ipso (Integer.division.invariance
             n (NatWithZero.gcd.nat (Integer.abs n) d) k).
  }

  lemma bottom : NatWithZero.divide.nat.safe
                (k * d)%nat
                (NatWithZero.gcd.nat
                  (Integer.abs (k * n)%integer)
                  (k * d)%nat)
                (NatWithZero.gcd.nat.right.divisibility
                  (Integer.abs (k * n)%integer)
                  (k * d)%nat)
          = NatWithZero.divide.nat.safe
                d
                (NatWithZero.gcd.nat (Integer.abs n) d)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs n) d).
  {
    lemma quotients
      : ((&k * &d)%nat
         /. NatWithZero.gcd.nat (Integer.abs (k * &n)%integer) (&k * &d)%nat)%nat_with_zero
        = (d /. NatWithZero.gcd.nat (Integer.abs &n) &d)%nat_with_zero.
    {
      leibniz common in |- *.
      let proof inv := NatWithZero.division.invariance
                    d
                    (NatWithZero.gcd.nat (Integer.abs n) d) k.
      let proof inv
        : ((k * d)%nat
           /. (k * NatWithZero.gcd.nat (Integer.abs n) d)%nat)%nat_with_zero
          = (d /. NatWithZero.gcd.nat (Integer.abs n) d)%nat_with_zero
        := &inv.
      ipso inv.
    }
    ipso (NatWithZero.divide.nat.safe.congruence _ _ _ _ _ _ &quotients).
  }

  ipso (extensionality
          (make (k * &n)%integer (&k * &d)%nat)
          (make &n &d)
          &top &bottom).
Qed.

(* make.proportionality *)
Theorem proportionality
  : forall (a : Integer) (b : Nat) .
      (numerator (make a b) * b)%integer
      = (a * denominator (make a b))%integer.
Proof.
  intros a b.
  simpl make in |- *.
  simpl numerator, denominator in |- *.

  lemma bottom : (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b)
              * NatWithZero.gcd.nat (Integer.abs a) b)%nat
          = b.
  {
    let proof s := NatWithZero.divide.nat.safe.specification
                  b (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b).
    let proof e := NatWithZero.division.exactness
                  b
                  (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.gcd.nat.right.divisibility
                    (Integer.abs a) b).
    symm in s.
    leibniz s in e.
    ipso (NatWithZero.positive.injectivity e).
  }

  lemma lifted : Integer.Positive b
          = (NatWithZero.divide.nat.safe
                    b (NatWithZero.gcd.nat (Integer.abs a) b)
                    (NatWithZero.gcd.nat.right.divisibility
                      (Integer.abs a) b) * NatWithZero.gcd.nat (Integer.abs a) b)%integer.
  {
    congru Integer.Positive, bottom |- c.
    symm in c.
    leibniz c in |- *.
    simpl in |- *.
    quod idem est.
  }

  lemma whole : ((a /. NatWithZero.gcd.nat (Integer.abs a) b)
                 * NatWithZero.gcd.nat (Integer.abs a) b)%integer
          = a.
  {
    ipso (Integer.division.exactness
            a (NatWithZero.gcd.nat (Integer.abs a) b)
            (NatWithZero.gcd.nat.left.divisibility (Integer.abs a) b)).
  }

  leibniz lifted in |- *.
  leibniz (Integer.multiplication.commutativity
            (NatWithZero.divide.nat.safe
                b (NatWithZero.gcd.nat (Integer.abs a) b)
                (NatWithZero.gcd.nat.right.divisibility (Integer.abs a) b))
            (NatWithZero.gcd.nat (Integer.abs a) b))
    in |- *.
  let proof assoc := Identity.symmetry
                (Integer.multiplication.associativity
                  (a /. NatWithZero.gcd.nat (Integer.abs a) b)%integer
                  (NatWithZero.gcd.nat (Integer.abs a) b)
                  (NatWithZero.divide.nat.safe
                      b (NatWithZero.gcd.nat (Integer.abs a) b)
                      (NatWithZero.gcd.nat.right.divisibility
                        (Integer.abs a) b))).
  leibniz assoc in |- *.
  leibniz whole in |- *.
  quod idem est.
Qed.

(* make.characterisation *)
Theorem characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      make a b = make c d
      <-> (a * d)%integer
        = (c * b)%integer.
Proof.
  intros a b c d.

  lemma swap : forall (x : Integer) (y : Integer) (z : Integer) .
              (x * y * z)%integer
              = (x * z * y)%integer.
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
  match (make a b) with | p q I1 end |- E1.
  match (make c d) with | r s I2 end |- E2.
  simpl numerator, denominator in P1, P2.

  lemma nzq : ~ (Integer.Positive q = Integer.Zero).
  {
    simpl (~ _) in |- *.
    intro z.
    ex z quodlibet.
  }

  lemma nzs : ~ (Integer.Positive s = Integer.Zero).
  {
    simpl (~ _) in |- *.
    intro z.
    ex z quodlibet.
  }

  divide et impera.

  - intro e.
    congru numerator,   e |- hp.
    congru denominator, e |- hq.
    simpl numerator   in hp.
    simpl denominator in hq.
    leibniz hp in P1.
    leibniz hq in P1.

    lemma Q1 : (r * b * d)%integer
                 = (a * s * d)%integer.
    {
      leibniz P1 in |- *.
      quod idem est.
    }

    lemma Q2 : (r * d * b)%integer
                 = (c * s * b)%integer.
    {
      leibniz P2 in |- *.
      quod idem est.
    }

    leibniz (swap r b d) in Q1.
    symm in Q1.
    let proof Q := Identity.transitivity Q1 Q2.
    leibniz (swap a s d) in Q.
    leibniz (swap c s b) in Q.
    leibniz (Integer.multiplication.commutativity
              (a * d)%integer
              s) in Q.
    leibniz (Integer.multiplication.commutativity
              (c * b)%integer
              s) in Q.
    ipso (Integer.multiplication.cancellation
            s (a * d)%integer
            (c * b)%integer nzs Q).

  - intro e.

    lemma nzbd : ~ ((b * d)%integer
            = Integer.Zero).
    {
      simpl (~ _) in |- *.
      intro z.
      simpl in z.
      ex z quodlibet.
    }

    lemma widened : (p * s * (b * d))%integer
            = (r * q * (b * d))%integer.
    {
      leibniz (Integer.multiplication.interchange
                p s b d) in |- *.
      leibniz P1 in |- *.
      leibniz (Integer.multiplication.commutativity s d) in |- *.
      leibniz (Integer.multiplication.interchange
                a q d s) in |- *.
      leibniz e in |- *.
      leibniz (Integer.multiplication.commutativity q s) in |- *.
      leibniz (Integer.multiplication.interchange
                c b s q) in |- *.
      let proof P2' := Identity.symmetry P2.
      leibniz P2' in |- *.
      leibniz (Integer.multiplication.commutativity b q) in |- *.
      leibniz (Integer.multiplication.interchange
                r d q b) in |- *.
      leibniz (Integer.multiplication.commutativity d b) in |- *.
      quod idem est.
    }

    leibniz (Integer.multiplication.commutativity
              (p * s)%integer
              (b * d)%integer) in widened.
    leibniz (Integer.multiplication.commutativity
              (r * q)%integer
              (b * d)%integer) in widened.
    let proof cross := Integer.multiplication.cancellation
                  (b * d)%integer
                  (p * s)%integer
                  (r * q)%integer
                  nzbd widened.

    congru Integer.abs, cross |- m.
    leibniz (Integer.multiplication.magnitude p s) in m.
    leibniz (Integer.multiplication.magnitude r q) in m.
    let proof m
      : (Integer.abs p * s)%nat_with_zero
        = (Integer.abs r * q)%nat_with_zero
      := &m.

    lemma coprime1 : NatWithZero.gcd q (Integer.abs p)
            = Nat.One.
    {
      let proof g := NatWithZero.gcd.nat.specification q (Integer.abs p).
      leibniz I1 in g.
      leibniz (NatWithZero.gcd.commutativity
                (Integer.abs p) q) in g.
      ipso g.
    }

    lemma coprime2 : NatWithZero.gcd s (Integer.abs r)
            = Nat.One.
    {
      let proof g := NatWithZero.gcd.nat.specification s (Integer.abs r).
      leibniz I2 in g.
      leibniz (NatWithZero.gcd.commutativity (Integer.abs r)
                 s) in g.
      ipso g.
    }

    lemma qs : NatWithZero.Divides q s.
    {
      let proof h := NatWithZero.divisibility.multiplication.closure
                    q q
                    (Integer.abs r)
                    (NatWithZero.divisibility.reflexivity q).
      leibniz (NatWithZero.multiplication.commutativity
                q (Integer.abs r)) in h.
      let proof m' := Identity.symmetry m.
      leibniz m' in h.
      ipso (NatWithZero.gcd.multiplication.cancellation
              q (Integer.abs p)
              s h coprime1).
    }

    lemma sq : NatWithZero.Divides s q.
    {
      let proof h := NatWithZero.divisibility.multiplication.closure
                    s s
                    (Integer.abs p)
                    (NatWithZero.divisibility.reflexivity s).
      leibniz (NatWithZero.multiplication.commutativity
                 s (Integer.abs p)) in h.
      leibniz m in h.
      ipso (NatWithZero.gcd.multiplication.cancellation
               s (Integer.abs r)
               q h coprime2).
    }

    let proof hq := NatWithZero.positive.injectivity (NatWithZero.divisibility.antisymmetry qs sq).
    leibniz hq in cross.
    leibniz (Integer.multiplication.commutativity p s) in cross.
    leibniz (Integer.multiplication.commutativity r s) in cross.
    let proof hp := Integer.multiplication.cancellation s p r nzs cross.
    ipso (extensionality
            (Rational_introduction &p &q &I1) (Rational_introduction &r &s &I2)
            &hp &hq).
Qed.

(* make.annihilation *)
Theorem annihilation
  : forall (b : Nat) . make Integer.Zero b = Zero.
Proof.
  intro b.

  lemma unit : make Integer.Zero Nat.One = Zero.
  {
    let proof r := make.retraction Zero.
    let proof r : make Integer.Zero Nat.One = Zero := &r.
    ipso r.
  }

  lemma cross : (Integer.Zero * Nat.One)%integer
          = (Integer.Zero * b)%integer.
  {
    leibniz (Integer.multiplication.left.annihilation Nat.One) in |- *.
    leibniz (Integer.multiplication.left.annihilation b)     in |- *.
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
      = make (a * d + c * b)%integer
             (b * d)%nat.
Proof.
  intros a b c d.
  simpl add in |- *.

  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.

  match (make a b) with | p q I1 end |- E1.
  match (make c d) with | r s I2 end |- E2.
  simpl numerator, denominator in P1, P2.
  simpl numerator, denominator in |- *.

  let b' : Integer := b in *.
  let d' : Integer := d in *.
  let q' : Integer := q in *.
  let s' : Integer := s in *.

  lemma first : (p * s' * (b' * d'))%integer
          = (a * d' * (q' * s'))%integer.
  {
    leibniz (Integer.multiplication.interchange p s' b' d') in |- *.
    leibniz P1 in |- *.
    leibniz (Integer.multiplication.commutativity s' d') in |- *.
    leibniz (Integer.multiplication.interchange a q' d' s') in |- *.
    quod idem est.
  }

  lemma second : (r * q' * (b' * d'))%integer
          = (c * b' * (q' * s'))%integer.
  {
    leibniz (Integer.multiplication.commutativity b' d') in |- *.
    leibniz (Integer.multiplication.interchange r q' d' b') in |- *.
    leibniz P2 in |- *.
    leibniz (Integer.multiplication.commutativity q' b') in |- *.
    leibniz (Integer.multiplication.interchange c s' b' q') in |- *.
    leibniz (Integer.multiplication.commutativity s' q') in |- *.
    quod idem est.
  }

  lemma cross : ((p * s' + r * q') * (b * d)%nat)%integer
          = ((a * d' + c * b') * (q * s)%nat)%integer.
  {
    lemma facto
      : ((&p * &s' + &r * &q') * (&b' * &d'))%integer
        = ((&a * &d' + &c * &b') * (&q' * &s'))%integer.
    {
      leibniz (Integer.multiplication.right.distributivity.over.addition
                (b' * d')%integer (p * s')%integer (r * q')%integer) in |- *.
      leibniz (Integer.multiplication.right.distributivity.over.addition
                (q' * s')%integer (a * d')%integer (c * b')%integer) in |- *.
      leibniz first  in |- *.
      leibniz second in |- *.
      quod idem est.
    }
    let proof facto
      : ((&p * &s' + &r * &q') * (&b' * &d'))%integer
        = ((&a * &d' + &c * &b') * (&q * &s)%nat)%integer
      := facto.
    ipso facto.
  }

  let proof criterion := characterisation
                (p * s' + r * q')%integer
                (q * s)%nat
                (a * d' + c * b')%integer
                (b * d)%nat.
  modus aequans criterion, cross |- joined.
  ipso joined.
Qed.

End addition. (* make.addition *)

Module multiplication. (* make.multiplication *)

(* make.multiplication.homomorphism *)
Theorem homomorphism
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
    (make a b) * (make c d) = make (a * c)%integer (b * d)%nat.
Proof.
  intros a b c d.
  simpl mul in |- *.

  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.

  match (make a b) with | p q I1 end |- E1.
  match (make c d) with | r s I2 end |- E2.
  simpl numerator, denominator in P1, P2.
  simpl numerator, denominator in |- *.

  lemma cross : (p * r * (b * d)%nat)%integer
          = (a * c * (q * s)%nat)%integer.
  {
    lemma facto
      : (&p * &r * (b * d))%integer
        = (&a * &c * (q * s))%integer.
    {
      leibniz (Integer.multiplication.interchange
                p r b d) in |- *.
      leibniz P1 in |- *.
      leibniz P2 in |- *.
      leibniz (Integer.multiplication.interchange
                a q c s) in |- *.
      quod idem est.
    }
    let proof facto
      : (&p * &r * (b * d))%integer
        = (&a * &c * (&q * &s)%nat)%integer
      := facto.
    ipso facto.
  }

  let proof criterion := characterisation
                (p * r)%integer (q * s)%nat
                (a * c)%integer (b * d)%nat.
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

  match (make a b) with | p q I1 end |- E1.
  simpl numerator, denominator in P1.
  simpl numerator, denominator in |- *.

  lemma cross : (Integer.negate p * b)%integer
          = (Integer.negate a * q)%integer.
  {
    leibniz (Integer.multiplication.left.negation p b) in |- *.
    leibniz (Integer.multiplication.left.negation a q) in |- *.
    leibniz P1 in |- *.
    quod idem est.
  }

  let proof criterion := characterisation
                (Integer.negate p) q (Integer.negate a) b.
  modus aequans criterion, cross |- joined.
  ipso joined.
Qed.

End negation. (* make.negation *)

Module order. (* make.order *)

Module strict. (* make.order.strict *)

(* make.order.strict.characterisation *)
Theorem characterisation
  : forall (a : Integer) (b : Nat) (c : Integer) (d : Nat) .
      make a b < make c d
      <-> ((a * d)%integer < (c * b)%integer)%integer.
Proof.
  intros a b c d.
  let proof P1 := proportionality a b.
  let proof P2 := proportionality c d.
  simpl ( _ < _ ) in |- *.
  let p := numerator   (make &a &b) in *.
  let q := denominator (make &a &b) in *.
  let r := numerator   (make &c &d) in *.
  let s := denominator (make &c &d) in *.

  lemma scaling : forall (m : Integer) (n : Integer) (k : Nat) .
              (m < n)%integer
              <-> ((m * k)%integer
                   < (n * k)%integer)%integer.
  {
    intros m n k.
    divide et impera.
    - intro h.
      let proof h' := Integer.multiplication.left.order.strict.monotonicity &k &m &n &h.
      leibniz (Integer.multiplication.commutativity k &m),
              (Integer.multiplication.commutativity k &n) in &h'.
      ipso &h'.
    - intro h.
      match (Comparable.order.strict.trichotomy &m &n) with | below | rest end.
      + ipso &below.
      + match &rest with | equal | above end.
        * leibniz &equal in &h.
          ex (Integer.order.strict.irreflexivity (&n * k)%integer &h)
            quodlibet.
        * let proof back := Integer.multiplication.left.order.strict.monotonicity &k &n &m &above.
          leibniz (Integer.multiplication.commutativity k &n),
                  (Integer.multiplication.commutativity k &m) in &back.
          let proof loop := Integer.order.strict.transitivity &h &back.
          ex (Integer.order.strict.irreflexivity (&m * k)%integer &loop)
            quodlibet.
  }

  lemma left_side
    : (&p * s * (&b * &d)%nat)%integer
      = (&a * d * (&q * &s)%nat)%integer.
  {
    leibniz <- (Integer.multiplication.positive.homomorphism &b &d),
            <- (Integer.multiplication.positive.homomorphism &q &s) in |- *.
    leibniz (Integer.multiplication.interchange
               &p s b d) in |- *.
    leibniz &P1 in |- *.
    leibniz (Integer.multiplication.commutativity s d)
      in |- *.
    leibniz (Integer.multiplication.interchange
               &a q d s) in |- *.
    quod idem est.
  }

  lemma right_side
    : (&r * q * (&b * &d)%nat)%integer
      = (&c * b * (&q * &s)%nat)%integer.
  {
    leibniz <- (Integer.multiplication.positive.homomorphism &b &d),
            <- (Integer.multiplication.positive.homomorphism &q &s) in |- *.
    leibniz (Integer.multiplication.commutativity b d)
      in |- *.
    leibniz (Integer.multiplication.interchange
               &r q d b) in |- *.
    leibniz &P2 in |- *.
    leibniz (Integer.multiplication.commutativity q b)
      in |- *.
    leibniz (Integer.multiplication.interchange
               &c s b q) in |- *.
    leibniz (Integer.multiplication.commutativity s q)
      in |- *.
    quod idem est.
  }

  divide et impera.
  - intro h.
    modus aequans
      (&scaling (&p * s)%integer (&r * q)%integer
                (&b * &d)%nat),
      &h |- scaled.
    leibniz &left_side, &right_side in &scaled.
    modus aequans
      (&scaling (&a * d)%integer (&c * b)%integer
                (&q * &s)%nat),
      &scaled |- facto.
    ipso facto.
  - intro h.
    modus aequans
      (&scaling (&a * d)%integer (&c * b)%integer
                (&q * &s)%nat),
      &h |- scaled.
    leibniz <- &left_side, <- &right_side in &scaled.
    modus aequans
      (&scaling (&p * s)%integer (&r * q)%integer
                (&b * &d)%nat),
      &scaled |- facto.
    ipso facto.
Qed.

End strict. (* make.order.strict *)

End order. (* make.order *)

End make. (* make *)

Theorem characterisation
  : forall (x : Rational) (y : Rational) .
      x = y
      <-> (numerator x * denominator y)%integer
        = (numerator y * denominator x)%integer.
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
               (a * d + c * b)%integer
               (b * d)%nat
               e f) in |- *.
    leibniz (make.addition.homomorphism
               a b
               (c * f + e * d)%integer
               (d * f)%nat) in |- *.

    let b' : Integer := b in *.
    let d' : Integer := d in *.
    let f' : Integer := f in *.

    lemma facto
      : make ((&a * &d' + &c * &b') * &f' + &e * (&b' * &d'))%integer
             (&b * &d * &f)%nat
        = make (&a * (&d' * &f') + (&c * &f' + &e * &d') * &b')%integer
               (&b * (&d * &f))%nat.
    {
      lemma tops : ((a * d' + c * b') * (f') + (e) * (b' * d'))%integer
              = ((a) * (d' * f') + (c * f' + e * d') * (b'))%integer.
      {
        leibniz (Integer.multiplication.right.distributivity.over.addition
                  f' (a * d')%integer (c * b')%integer) in |- *.
        leibniz (Integer.multiplication.right.distributivity.over.addition
                  b' (c * f')%integer (e * d')%integer) in |- *.
        leibniz (Integer.addition.associativity
                  (a * d' * f')%integer
                  (c * b' * f')%integer
                  (e * (b' * d'))%integer) in |- *.
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
      : make ((&a * &d' + &c * &b') * &f' + &e * (&b' * &d'))%integer
             (&b * &d * &f)%nat
        = make (&a * (&d * &f)%nat + (&c * &f' + &e * &d') * &b')%integer
               (&b * (&d * &f))%nat
      := facto.
    ipso facto.
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
            (numerator x * denominator y)%integer
            (numerator y * denominator x)%integer) in |- *.
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
    : make (Integer.Zero * denominator &x + numerator &x * Nat.One)%integer
           (denominator &x)
      = &x.
  {
    leibniz (Integer.multiplication.left.annihilation
               (denominator x)) in |- *.
    leibniz (Integer.addition.left.identity
               (numerator x * Nat.One)%integer) in |- *.
    leibniz (Integer.multiplication.right.identity (numerator x)) in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (Integer.Zero * denominator &x + numerator &x * Nat.One)%integer
           (Nat.One * denominator &x)%nat
      = &x
    := facto.
  let proof facto
    : make (Integer.Zero * denominator &x + numerator &x * Nat.One)%integer
           (Nat.One * denominator &x)%nat
      = &x
    := facto.
  let proof facto
    : make (Integer.Zero * denominator &x + numerator &x * denominator Zero)%integer
           (denominator Zero * denominator &x)%nat
      = &x
    := facto.
  ipso facto.
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
    leibniz (Integer.multiplication.left.negation (a) b) in |- *.
    leibniz (Integer.addition.left.inverse (a * b)%integer) in |- *.
    ipso (make.annihilation (b * b)%nat).
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

  congru (fun (t : Rational) . add (negate k) t), e |- h.
  simpl in h.

  symm in an.
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
    : make (numerator &x * Nat.One + Integer.Zero * denominator &x)%integer
           (denominator &x * Nat.One)%nat
      = &x.
  {
    leibniz (Integer.multiplication.right.identity (numerator x)) in |- *.
    leibniz (Integer.multiplication.left.annihilation (denominator x)) in |- *.
    leibniz (Integer.addition.right.identity (numerator x)) in |- *.
    match (Nat.multiplication.identity (denominator x)) with | _ unit end.
    leibniz unit in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (numerator &x * Nat.One + Integer.Zero * denominator &x)%integer
           (denominator &x * Nat.One)%nat
      = &x
    := facto.
  let proof facto
    : make (numerator &x * denominator Zero + Integer.Zero * denominator &x)%integer
           (denominator &x * denominator Zero)%nat
      = &x
    := facto.
  ipso facto.
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
               a b) in |- *.
    leibniz (Integer.addition.right.inverse
               (a * b)%integer) in |- *.
    ipso (make.annihilation (b * b)%nat).
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

  congru (fun (t : Rational) . add t (negate k)), e |- h.
  simpl in h.

  symm in am.
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

Module order. (* addition.order *)

Module strict. (* addition.order.strict *)

(* addition.order.strict.monotonicity *)
Theorem monotonicity
  : forall (z : Rational) (x : Rational) (y : Rational) .
      x < y -> z + x < z + y.
Proof.
  intros z x y h.
  match &z with | e f hz end.
  match &x with | a b hx end.
  match &y with | c d hy end.
  simpl ( _ < _ ), numerator, denominator in &h.
  let proof rz := make.retraction (Rational_introduction &e &f &hz).
  let proof rx := make.retraction (Rational_introduction &a &b &hx).
  let proof ry := make.retraction (Rational_introduction &c &d &hy).
  simpl numerator, denominator in &rz, &rx, &ry.
  leibniz <- &rz, <- &rx, <- &ry in |- *.
  leibniz (make.addition.homomorphism &e &f &a &b),
          (make.addition.homomorphism &e &f &c &d) in |- *.

  lemma lower
    : ((&e * b + &a * f) * (&f * &d)%nat)%integer
      = (&e * b * (&f * &d)%nat + (&f * &f)%nat * (&a * d))%integer.
  {
    leibniz (Integer.multiplication.right.distributivity.over.addition
               (&f * &d)%nat
               (&e * b)%integer
               (&a * f)%integer) in |- *.
    leibniz <- (Integer.multiplication.positive.homomorphism &f &d),
            <- (Integer.multiplication.positive.homomorphism &f &f) in |- *.
    leibniz (Integer.multiplication.commutativity &a f) in |- *.
    leibniz (Integer.multiplication.interchange
               f &a f d) in |- *.
    quod idem est.
  }

  lemma upper
    : ((&e * d + &c * f) * (&f * &b)%nat)%integer
      = (&e * b * (&f * &d)%nat + (&f * &f)%nat * (&c * b))%integer.
  {
    leibniz (Integer.multiplication.right.distributivity.over.addition
               (&f * &b)%nat
               (&e * d)%integer
               (&c * f)%integer) in |- *.
    leibniz <- (Integer.multiplication.positive.homomorphism &f &b),
            <- (Integer.multiplication.positive.homomorphism &f &d),
            <- (Integer.multiplication.positive.homomorphism &f &f) in |- *.
    leibniz (Integer.multiplication.commutativity &c f) in |- *.
    leibniz (Integer.multiplication.interchange
               f &c f b) in |- *.
    leibniz (Integer.multiplication.commutativity f b)
      in |- *.
    leibniz (Integer.multiplication.interchange
               &e d b f) in |- *.
    leibniz (Integer.multiplication.commutativity d f)
      in |- *.
    quod idem est.
  }

  lemma cross
    : (((&e * b + &a * f) * (&f * &d)%nat)%integer
       < ((&e * d + &c * f) * (&f * &b)%nat)%integer)%integer.
  {
    let proof scaled := Integer.multiplication.left.order.strict.monotonicity
                          (&f * &f)%nat
                          (&a * d)%integer
                          (&c * b)%integer
                          &h.
    let proof shifted := Integer.addition.order.strict.monotonicity
                           (&e * b * (&f * &d)%nat)%integer
                           _ _ &scaled.
    leibniz <- &lower, <- &upper in &shifted.
    ipso &shifted.
  }

  modus aequans (make.order.strict.characterisation _ _ _ _), &cross |- facto.
  ipso facto.
Qed.

End strict. (* addition.order.strict *)

End order. (* addition.order *)

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
              (a * c)%integer (b * d)%nat e f) in |- *.
    leibniz (make.multiplication.homomorphism
              a b (c * e)%integer (d * f)%nat) in |- *.
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
    : make (Nat.One * numerator &x)%integer (denominator &x) = &x.
  {
    leibniz (Integer.multiplication.left.identity (numerator x)) in |- *.
    ipso (make.retraction x).
  }
  let proof facto
    : make (Nat.One * numerator &x)%integer
           (Nat.One * denominator &x)%nat
      = &x
    := facto.
  let proof facto
    : make (Nat.One * numerator &x)%integer
           (denominator One * denominator &x)%nat
      = &x
    := facto.
  ipso facto.
Qed.

(* multiplication.left.annihilation *)
Theorem annihilation : forall (x : Rational) . Zero * x = Zero.
Proof.
  intro x.
  simpl mul in |- *.
  lemma facto
    : make (Integer.Zero * numerator &x)%integer (denominator &x) = Zero.
  {
    leibniz (Integer.multiplication.left.annihilation (numerator x)) in |- *.
    ipso (make.annihilation (denominator x)).
  }
  let proof facto
    : make (Integer.Zero * numerator &x)%integer (Nat.One * denominator &x)%nat = Zero
    := facto.
  let proof facto
    : make (Integer.Zero * numerator &x)%integer
           (denominator Zero * denominator &x)%nat
      = Zero
    := facto.
  ipso facto.
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
              (c * f + e * d)%integer
              (d * f)%nat) in |- *.
    leibniz (make.multiplication.homomorphism a b c d) in |- *.
    leibniz (make.multiplication.homomorphism a b e f) in |- *.
    leibniz (make.addition.homomorphism
              (a * c)%integer (b * d)%nat
              (a * e)%integer (b * f)%nat) in |- *.

    let b' : Integer := b.
    let d' : Integer := d in *.
    let f' : Integer := f in *.

    lemma facto
      : make (&a * (&c * &f' + &e * &d'))%integer
             (&b * (&d * &f))%nat
        = make (&a * &c * (&b' * &f') + &a * &e * (&b' * &d'))%integer
               (&b * &d * (&b * &f))%nat.
    {
      lemma tops : (a * c * (b' * f') + a * e * (b' * d'))%integer
              = (b' * ((a) * (c * f' + e * d')))%integer.
      {
        leibniz (Integer.multiplication.left.distributivity.over.addition
                  a (c * f')%integer (e * d')%integer) in |- *.
        leibniz (Integer.multiplication.left.distributivity.over.addition
                  b'
                  (a * (c * f'))%integer
                  (a * (e * d'))%integer) in |- *.
        leibniz (Integer.multiplication.interchange a c b' f') in |- *.
        leibniz (Integer.multiplication.interchange a e b' d') in |- *.
        leibniz (Integer.multiplication.commutativity a b') in |- *.
        leibniz (Integer.multiplication.associativity
                  b' a (c * f')%integer) in |- *.
        leibniz (Integer.multiplication.associativity
                  b' a (e * d')%integer) in |- *.
        quod idem est.
      }

      lemma bots : (b * d * (b * f))%nat
              = ((b) * (b * (d * f)))%nat.
      {
        leibniz (Nat.multiplication.associativity b d (b * f)%nat) in |- *.
        leibniz (Nat.multiplication.commutativity d (b * f)%nat) in |- *.
        leibniz (Nat.multiplication.associativity b f d) in |- *.
        leibniz (Nat.multiplication.commutativity f d) in |- *.
        quod idem est.
      }

      leibniz tops in |- *.
      leibniz bots in |- *.
      symm in |- *.
      ipso (make.invariance
              ((a) * (c * f' + e * d'))%integer
              ((b) * (d * f))%nat
              (b)).
    }
    let proof facto
      : make (&a * (&c * &f' + &e * &d'))%integer
             (&b * (&d * &f))%nat
        = make (&a * &c * (&b' * &f') + &a * &e * (&b * &d)%nat)%integer
               (&b * &d * (&b * &f))%nat
      := facto.
    ipso facto.
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

Module order. (* multiplication.left.order *)

Module strict. (* multiplication.left.order.strict *)

(* multiplication.left.order.strict.monotonicity *)
Theorem monotonicity
  : forall (z : Rational) (x : Rational) (y : Rational) .
      Zero < z -> x < y -> z * x < z * y.
Proof.
  intros z x y positive h.
  match &z with | e f hz end.
  match &x with | a b hx end.
  match &y with | c d hy end.
  simpl ( _ < _ ), numerator, denominator in &positive, &h.
  simpl Zero in &positive.
  simpl in &positive.
  match &e with | k | | k end.
  - simpl in &positive.
    match &positive with | j e end.
    leibniz (Integer.addition.left.identity j) in &e.
    ex &e quodlibet.
  - simpl in &positive.
    ex (Integer.order.strict.irreflexivity Integer.Zero &positive) quodlibet.
  - let proof rz := make.retraction (Rational_introduction k &f &hz).
    let proof rx := make.retraction (Rational_introduction &a &b &hx).
    let proof ry := make.retraction (Rational_introduction &c &d &hy).
    simpl numerator, denominator in &rz, &rx, &ry.
    leibniz <- &rz, <- &rx, <- &ry in |- *.
    leibniz (make.multiplication.homomorphism k &f &a &b),
            (make.multiplication.homomorphism k &f &c &d) in |- *.

    lemma lower
      : (k * &a * (&f * &d)%nat)%integer
        = ((&k * &f)%nat * (&a * d))%integer.
    {
      leibniz <- (Integer.multiplication.positive.homomorphism &f &d),
              <- (Integer.multiplication.positive.homomorphism &k &f) in |- *.
      leibniz (Integer.multiplication.interchange
                 k &a f d) in |- *.
      quod idem est.
    }

    lemma upper
      : (k * &c * (&f * &b)%nat)%integer
        = ((&k * &f)%nat * (&c * b))%integer.
    {
      leibniz <- (Integer.multiplication.positive.homomorphism &f &b),
              <- (Integer.multiplication.positive.homomorphism &k &f) in |- *.
      leibniz (Integer.multiplication.interchange
                 k &c f b) in |- *.
      quod idem est.
    }

    lemma cross
      : ((k * &a * (&f * &d)%nat)%integer
         < (k * &c * (&f * &b)%nat)%integer)%integer.
    {
      let proof scaled := Integer.multiplication.left.order.strict.monotonicity
                            (&k * &f)%nat
                            (&a * d)%integer
                            (&c * b)%integer
                            &h.
      leibniz <- &lower, <- &upper in &scaled.
      ipso &scaled.
    }

    modus aequans (make.order.strict.characterisation _ _ _ _), &cross |- facto.
    ipso facto.
Qed.

End strict. (* multiplication.left.order.strict *)

End order. (* multiplication.left.order *)

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

  lemma unit : make Nat.One Nat.One = One.
  {
    let proof r := make.retraction One.
    let proof r : make Nat.One Nat.One = One := &r.
    ipso r.
  }

  let proof r := make.retraction x.
  simpl inverse in e.
  match (numerator x) with | p | | p end |- E.

  - let proof hy := Option.some.injectivity e.
    symm in r.
    leibniz r in |- *.
    symm in hy.
    leibniz hy in |- *.
    let d := denominator x in *.
    leibniz (make.multiplication.homomorphism (Integer.Negative p) (d) (Integer.Negative d) (p)) in |- *.
    lemma facto : make (&p * &d)%nat (&d * &p)%nat = One.
    {
      lemma cross : ((p * d)%nat * Nat.One)%integer
              = (Nat.One * (d * p)%nat)%integer.
      {
        lemma facto
          : ((&p * &d)%nat * Nat.One)%integer
            = (Nat.One * (&d * &p)%nat)%integer.
        {
          leibniz (Integer.multiplication.right.identity
                    (p * d)%nat) in |- *.
          leibniz (Integer.multiplication.left.identity
                    (d * p)%nat) in |- *.
          leibniz (Nat.multiplication.commutativity p d) in |- *.
          quod idem est.
        }
        let proof facto
          : ((&p * &d)%nat * Nat.One)%integer
            = (Nat.One * (&d * &p)%nat)%integer
          := facto.
        ipso facto.
      }

      let proof criterion := make.characterisation
                    (p * d)%nat
                    (d * p)%nat
                    Nat.One
                    (Nat.One).
      modus aequans criterion, cross |- joined.
      ipso (Identity.transitivity joined unit).
    }
    ipso facto.

  - ex e quodlibet.

  - let proof hy := Option.some.injectivity e.
    symm in r.
    leibniz r in |- *.
    symm in hy.
    leibniz hy in |- *.
    let d := denominator x in *.
    leibniz (make.multiplication.homomorphism
              p (d)
              d (p)) in |- *.
    lemma facto : make (&p * &d)%nat (&d * &p)%nat = One.
    {
      lemma cross : ((p * d)%nat * Nat.One)%integer
              = (Nat.One * (d * p)%nat)%integer.
      {
        lemma facto
          : ((&p * &d)%nat * Nat.One)%integer
            = (Nat.One * (&d * &p)%nat)%integer.
        {
          leibniz (Integer.multiplication.right.identity (p * d)%nat) in |- *.
          leibniz (Integer.multiplication.left.identity (d * p)%nat) in |- *.
          leibniz (Nat.multiplication.commutativity p d) in |- *.
          quod idem est.
        }
        let proof facto
          : ((&p * &d)%nat * Nat.One)%integer
            = (Nat.One * (&d * &p)%nat)%integer
          := facto.
        ipso facto.
      }

      let proof criterion := make.characterisation
                    (p * d)%nat
                    (d * p)%nat
                    Nat.One
                    (Nat.One).
      modus aequans criterion, cross |- joined.
      ipso (Identity.transitivity joined unit).
    }
    ipso facto.
Qed.

End inverse. (* inverse *)

Module order. (* order *)

Module strict. (* order.strict *)

(* order.strict.transitivity *)
Theorem transitivity
  : forall (x : Rational) (y : Rational) (z : Rational) .
      x < y -> y < z -> x < z.
Proof.
  intros x y z H1 H2.
  simpl ( _ < _ ) in H1, H2 |- *.

  let a := numerator   x in *.
  let b := denominator x in *.
  let c := numerator   y in *.
  let d := denominator y in *.
  let e := numerator   z in *.
  let f := denominator z in *.

  lemma bridge : (f * (c * b))%integer
          = (b * (c * f))%integer.
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    f c b).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity
               f c) in |- *.
    leibniz (Integer.multiplication.commutativity
               (c * f)%integer
               b) in |- *.
    quod idem est.
  }

  lemma leftward : (f * (a * d))%integer
          = (d * (a * f))%integer.
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    f a d).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity
              f
              (a)) in |- *.
    leibniz (Integer.multiplication.commutativity
              (a * f)%integer
              d) in |- *.
    quod idem est.
  }

  lemma rightward : (b * (e * d))%integer
          = (d * (e * b))%integer.
  {
    let proof h := Identity.symmetry
                  (Integer.multiplication.associativity
                    b
                    (e)
                    d).
    leibniz h in |- *.
    leibniz (Integer.multiplication.commutativity b e) in |- *.
    leibniz (Integer.multiplication.commutativity
               (e * b)%integer
               d) in |- *.
    quod idem est.
  }

  let proof S1 := Integer.multiplication.left.order.strict.monotonicity
                f (a * d)%integer
                  (c * b)%integer H1.
  let proof S2 := Integer.multiplication.left.order.strict.monotonicity
                b (c * f)%integer
                  (e * d)%integer H2.

  leibniz bridge    in S1.
  leibniz leftward  in S1.
  leibniz rightward in S2.

  let proof chain := Integer.order.strict.transitivity S1 S2.

  match (Comparable.order.strict.trichotomy
           (a * f)%integer
           (e * b)%integer)
        with | lt | rest end.

  - ipso lt.

  - match rest with | eq | gt end.

    + leibniz eq in chain.
      let proof ir := Integer.order.strict.irreflexivity
                    (d * (e * b))%integer.
      ex (ir chain) quodlibet.

    + let proof back := Integer.multiplication.left.order.strict.monotonicity
                    d (e * b)%integer
                      (a * f)%integer gt.
      let proof loop := Integer.order.strict.transitivity chain back.
      let proof ir := Integer.order.strict.irreflexivity
                    (d * (a * f))%integer.
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
              (numerator x * denominator y)%integer
              (numerator y * denominator x)%integer)
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
          (numerator x * denominator y)%integer
          (numerator y * denominator x)%integer).
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
    : (m * Nat.One)%integer = (n * Nat.One)%integer
    := &cross.
  leibniz (Integer.multiplication.right.identity m) in cross.
  leibniz (Integer.multiplication.right.identity n) in cross.
  ipso cross.
Qed.

(* embedding.addition *)
Theorem addition
  : forall (m : Integer) (n : Integer) .
      from_integer (m + n)%integer
    = (from_integer m) + (from_integer n).
Proof.
  intros m n.
  simpl from_integer in |- *.
  leibniz (make.addition.homomorphism m Nat.One n Nat.One) in |- *.
  lemma facto
    : make (&m + &n)%integer Nat.One
      = make (&m * Nat.One + &n * Nat.One)%integer
             (Nat.One * Nat.One)%nat.
  {
    leibniz (Integer.multiplication.right.identity m) in |- *.
    leibniz (Integer.multiplication.right.identity n) in |- *.
    lemma facto : make (&m + &n)%integer Nat.One = make (&m + &n)%integer Nat.One.
    {
      quod idem est.
    }
    ipso facto.
  }
  ipso facto.
Qed.

(* embedding.multiplication *)
Theorem multiplication
  : forall (m : Integer) (n : Integer) .
      from_integer (m * n)%integer
    = (from_integer m) * (from_integer n).
Proof.
  intros m n.
  simpl from_integer in |- *.
  leibniz (make.multiplication.homomorphism m Nat.One n Nat.One) in |- *.
  lemma facto : make (&m * &n)%integer Nat.One = make (&m * &n)%integer Nat.One.
  {
    quod idem est.
  }
  ipso facto.
Qed.

(* embedding.order *)
Theorem order
  : forall (m : Integer) (n : Integer) .
      (m < n)%integer
      <-> from_integer m < from_integer n.
Proof.
  intros m n.
  simpl from_integer in |- *.
  let proof c := make.order.strict.characterisation &m Nat.One &n Nat.One.
  leibniz (Integer.multiplication.right.identity &m),
          (Integer.multiplication.right.identity &n) in &c.
  ipso (Biconditional.symmetry &c).
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

(* An [Integer] stands wherever a [Rational] is expected, and through it a
 * [Nat] or a [NatWithZero]; the conversion is printed where it happened.
 *)
Coercion Rational.from_integer : Integer >-> Rational.
Add Printing Coercion Rational.from_integer.

Instance Rational_comparable
  : Comparable Rational.compare (<)%rational :=
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
