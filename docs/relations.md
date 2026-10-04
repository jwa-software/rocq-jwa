<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Relations

`jwa.Relation` holds the classes that name what a relation does, and the means to define a function by going down a relation:

| Class | Its law | Holds of |
|:---|:---|:---|
| `Reflexive R` | `R x x` | `=`, `<=` |
| `Symmetric R` | `R x y -> R y x` | `=` |
| `Transitive R` | `R x y -> R y z -> R x z` | `=`, `<`, `<=` |
| `Antisymmetric R` | `R x y -> R y x -> x = y` | `<=` |
| `Irreflexive R` | `~ R x x` | `<` |
| `Total R` | `R x y \/ R y x` | `<=` |
| `Trichotomous R` | `R x y \/ x = y \/ R y x` | `<` |
| `Equivalence R` | `Reflexive R`, `Symmetric R` and `Transitive R` together | `=`, `<->` |
| `WellFounded R` | every value is `Accessible` | `<` on `Nat0` |

- **A relation is a function into `Prop`.** `R : A -> A -> Prop` takes two values, and `R x y` is the proposition that they are related: `Nat0.LessThan 3 5`, written `(3 < 5)%n0`.
- **A class is about a relation, not about a type.** `<` and `<=` on `Nat0` are two relations, and the table gives them different rows.
- **A field is read behind the name of its class:** `Transitive.transitivity`, `Total.totality`.
- **The seven properties have no instance of their own.** Each is held by a larger class: `Equivalence` for `=` and `<->`, and the classes of [Order](order.md) for the `<` and `<=` of every type with a `Comparable` instance. A proof still asks for one property alone: `Transitive.transitivity` at `<` on `Nat0` is found through them.

`From jwa Require Import Relation.All` brings the classes. The examples on this page are in `Nat0`, under the key `%n0`.

---

## Reflexive

- **The problem.** A proof often needs a value related to itself: `5 <= 5`, `x = x`. Not every relation gives that: `5 < 5` does not hold.
- **The class.** `Reflexive R` has one field, `Reflexive.reflexivity`: `R x x`.
- **Instances.** `Equivalence` holds it for `=` and `<->`, and the order of a `Comparable` type for `<=`.
- **In a proof.** `Reflexive.reflexivity n` proves `n <= n`, and `n = n`.
- **What it does not say.** Anything of two different values.

---

## Symmetric

- **The problem.** An equation is used in either direction: `a = b` gives `b = a`. A relation with a direction does not allow it: `3 <= 5` holds, and `5 <= 3` does not.
- **The class.** `Symmetric R` has one field, `Symmetric.symmetry`: `R x y -> R y x`.
- **Instances.** `Equivalence` holds it for `=` and `<->`.
- **In a proof.** `Symmetric.symmetry m n e` turns `e : m = n` into a proof of `n = m`.
- **What it does not say.** That a value is related to itself.

---

## Transitive

- **The problem.** Facts are chained: from `3 < 5` and `5 < 9` follows `3 < 9`, with no second look at `5`. Not every relation chains: `4` is one more than `3`, `5` is one more than `4`, and `5` is not one more than `3`.
- **The class.** `Transitive R` has one field, `Transitive.transitivity`: `R x y -> R y z -> R x z`.
- **Instances.** `Equivalence` holds it for `=` and `<->`, and the orders of a `Comparable` type for `<` and `<=`.
- **In a proof.** `Transitive.transitivity l m n` takes a proof of `l < m` and one of `m < n`, and proves `l < n`.
- **What it does not say.** That the chain can be read backward; that is `Symmetric`.

---

## Antisymmetric

- **The problem.** Two numbers are shown equal by two bounds: from `x <= y` and `y <= x` follows `x = y`. Not every relation allows it: `13` and `23` end in the same digit, each way round, and are two numbers.
- **The class.** `Antisymmetric R` has one field, `Antisymmetric.antisymmetry`: `R x y -> R y x -> x = y`.
- **Instances.** The order of a `Comparable` type holds it for `<=`.
- **In a proof.** `Antisymmetric.antisymmetry m n` takes a proof of `m <= n` and one of `n <= m`, and proves `m = n`.
- **What it does not say.** That two values are related at all; that is `Total`.

---

## Irreflexive

- **The problem.** Under a strict order nothing is below itself: `5 < 5` never holds. A proof that reaches `x < x` has reached a contradiction, and needs the law that says so.
- **The class.** `Irreflexive R` has one field, `Irreflexive.irreflexivity`: `~ R x x`.
- **Instances.** The strict order of a `Comparable` type holds it for `<`.
- **In a proof.** With `h : n < n` in the context, `ex (Irreflexive.irreflexivity n h) quodlibet` closes any goal.
- **What it does not say.** A relation that is not reflexive is not thereby irreflexive. `m + n = 4` relates `2` to itself and does not relate `1` to itself, so it is neither.

---

## Total

- **The problem.** A proof splits in two cases on how two numbers compare: `x <= y`, or `y <= x`. The split is complete only when one of the two always holds. For "divides" it does not: `2` does not divide `3`, and `3` does not divide `2`.
- **The class.** `Total R` has one field, `Total.totality`: `R x y \/ R y x`.
- **Instances.** The order of a `Comparable` type holds it for `<=`.
- **In a proof.** `match (Total.totality m n) with | h | h end` gives the two cases, each with its `h`.
- **What it does not say.** Which of the two holds. The field is a proposition and decides nothing; `Nat0.compare` is the function that computes the answer. Both sides hold when `x` is `y`.

---

## Trichotomous

- **The problem.** Under a strict order two numbers compare in one of three ways: `x < y`, `x = y`, or `y < x`. A proof by cases needs the three to cover every pair.
- **The class.** `Trichotomous R` has one field, `Trichotomous.trichotomy`: `R x y \/ x = y \/ R y x`.
- **Instances.** The strict order of a `Comparable` type holds it for `<`.
- **In a proof.** `match (Trichotomous.trichotomy m n) with | below | rest end` gives the first case and the two others together, and a second `match` on `rest` separates them.
- **What it does not say.** That only one of the three holds. For a strict order that follows from `Irreflexive` and `Transitive`, not from this class.

---

## Equivalence

- **The problem.** Some relations behave as `=` does without being it: `P <-> Q` says two propositions hold together. A proof uses such a relation in either direction and chains it, so it needs the three laws at once.
- **The class.** `Equivalence R` holds `Reflexive R`, `Symmetric R` and `Transitive R`, and adds no law.
- **Instances.** `Identity_equivalence` for `=` at every type, and `Biconditional_equivalence` for `<->`.
- **In a proof.** `Reflexive.reflexivity`, `Symmetric.symmetry` and `Transitive.transitivity` are each found from the one instance.
- **What it does not say.** That a value may stand for an equivalent one inside a term. `leibniz` rewrites with `=` alone.

---

## WellFounded

- **The problem.** Rocq accepts a recursive function only when each call goes to a part of its argument. Euclid's algorithm goes from `(a, b)` to `(b, a %. b)`: the remainder is smaller than `b`, and is no part of it. "Smaller" has to be a reason to stop, and it is one exactly when no descent goes on for ever. From any `Nat0`, every descent `... < 2 < 5 < 9` ends at `0` or before; on `Integer`, `... < -3 < -2 < -1` never ends.
- **The class.** `WellFounded R` has one field, `WellFounded.accessibility`: every `x` is `Accessible R x`. Here `R y x` reads "`y` is below `x`", and `x` is accessible when every `y` below it is, which a value with nothing below it is for free.
- **Instances.** `Nat_less_than_well_founded`, `Nat0_less_than_well_founded`, `BinBase_less_than_well_founded` and `BinWithZero_less_than_well_founded` for `<`. `Integer_magnitude_well_founded` and `Bin_magnitude_well_founded` for the order of magnitudes, `Induced (<)%n0 Integer.abs`, under which `2` is below `-3` since `2 < 3`.
- **In a definition.** `WellFounded.recursion step x` builds a function from one step. The step, of type `Descent.Step R P`, answers at `x` from the answers below `x`: `forall x . (forall y . R y x -> P y) -> P x`. `Nat0.gcd a b` is `WellFounded.recursion Nat0.euclid.step (a, b)`: the step answers `a` where `b` is `0`, and asks at `(b, a %. b)` otherwise.
- **In a proof.** `WellFounded.recursion.unfolding` turns a recursion into one step and the recursion below it, for a step that is `Descent.Extensional`: one that gives the same answer whenever the answers below are the same. `Nat0.gcd.recurrence`, `gcd a (+ q) = gcd (+ q) (a %. q)`, is that law at `Nat0.euclid.step`.
- **A relation is carried along a function.** `Induced R f` puts `y` below `x` when `f y` is below `f x` under `R`, and `WellFounded.induced` makes it well founded when `R` is. That is how the pairs of Euclid's algorithm descend, by their second component (`Nat0.euclid.well_founded`), and how `Integer` descends by magnitude.
- **What it does not say.** That the function computes. `Nat0.gcd 12 18` is `6`, and no reduction shows it: the recursion runs on the proof of accessibility, which is opaque. The value is reached through the laws, `Nat0.gcd.recurrence` three times and then `Nat0.gcd.zero`.

---

## Using a property in a proof

At a concrete relation, the instance is found from the goal. A law stated over the classes is proved once and holds of every relation that has them:

```
From jwa Require Import Relation.All.
From jwa Require Import Data.All.

Definition chain
  : forall (l : Nat0) (m : Nat0) (n : Nat0) . (l < m -> m < n -> l < n)%n0
  := fun (l : Nat0) (m : Nat0) (n : Nat0) . Transitive.transitivity l m n.

Theorem meeting
  : forall {A : Type} {R : A -> A -> Prop} {S : Symmetric R} {T : Transitive R}
      (x : A) (y : A) (z : A) .
      R x z -> R y z -> R x y.
Proof.
  intros A R S T x y z h1 h2.
  ipso (Transitive.transitivity &x &z &y &h1 (Symmetric.symmetry &y &z &h2)).
Qed.

Definition meeting_of_propositions
  : forall (P : Prop) (Q : Prop) (C : Prop) . (P <-> C) -> (Q <-> C) -> (P <-> Q)
  := fun (P : Prop) (Q : Prop) (C : Prop) . meeting P Q C.
```

`meeting` names no relation: two values related to a third are related to each other, under any relation that is symmetric and transitive. `meeting_of_propositions` is that proof at `<->`, both properties found through `Biconditional_equivalence`.
