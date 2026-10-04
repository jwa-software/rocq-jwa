<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Algebra

`jwa.Algebra` holds nine classes. Each one names the laws an operation obeys, so that a proof asks for a law by one name whatever the type:

| Class | Holds | Adds the law |
|:---|:---|:---|
| `Semigroup op` | -- | `associativity` |
| `Monoid op e` | `Semigroup op` | `identity` |
| `Group op e inv` | `Monoid op e` | `inverse` |
| `Commutative op` | -- | `commutativity` |
| `AbelianMonoid op e` | `Monoid op e` and `Commutative op` | -- |
| `AbelianGroup op e inv` | `Group op e inv` and `Commutative op` | -- |
| `Cancellative op` | -- | `cancellation` |
| `Semiring add zero mul one` | `AbelianMonoid add zero` and `Monoid mul one` | `distributivity`, `annihilation` |
| `Ring add zero negate mul one` | `AbelianGroup add zero negate` and `Monoid mul one` | `distributivity` |

- **A class is about an operation, not about a type.** `Monoid Nat0.add Nat0.Zero` and `Monoid Nat0.mul Nat.One` are two instances on the one type `Nat0`.
- **A class is a proposition, and its fields are its laws.** A field is read behind the name of its class: `Monoid.identity`, `Group.inverse`.
- **A class gives the laws of the classes it holds.** With a `Group` in hand, `Monoid.identity` and `Semigroup.associativity` are found without being asked for.

`From jwa Require Import Algebra.All` brings the nine classes. An instance comes with the file of its type, `Nat0_add_monoid` with `Nat0`. The examples on this page are written under the key of their number type, `%n0` for `Nat0` and `%z` for `Integer`.

---

## Semigroup

- **The problem.** A sum of three numbers needs no parentheses: `(2 + 3) + 4` and `2 + (3 + 4)` are both `9`. A proof that regroups a sum, a product or a concatenation needs that fact, under one name for every operation.
- **The class.** `Semigroup op` has one field, `Semigroup.associativity`: `op (op x y) z = op x (op y z)`.
- **Instances.** `Nat_add_semigroup` for `+` on `Nat`, and `Nat0_min_semigroup` for `Nat0.min`. Every monoid below is a semigroup as well.
- **In a proof.** `Semigroup.associativity x y z` is that equation for the operation of the goal.
- **What it does not say.** That some value changes nothing. `Nat` starts at `1`, so no `Nat` added to `5` gives `5`; and a value that `Nat0.min` leaves every number unchanged with would have to be at least every number. These two operations are semigroups and not monoids.

---

## Monoid

- **The problem.** An operation over a whole list needs an answer for the empty list: the sum of no numbers is `0`, the product of none is `1`, the join of no strings is `""`. Each of these values changes nothing where it is used: `0 + 5` and `5 + 0` are both `5`.
- **The class.** `Monoid op e` holds `Semigroup op` and adds `Monoid.identity`: `op e x = x /\ op x e = x`, both sides in one field.
- **Instances.** One type has several. `Nat0_add_monoid` is `+` with `0`, `Nat0_mul_monoid` is `*` with `1`, and `Nat0_max_monoid` is `Nat0.max` with `0`. `Bool_and_monoid` is `Bool.and` with `true`, and `Bool_or_monoid` is `Bool.or` with `false`. `List_concat_monoid` is `++` with `[]`, and `AsciiStr_concat_monoid` and `Utf8Str_concat_monoid` are `++` with `""`.
- **In a proof.** `Monoid.identity x` gives the two equations as a conjunction.
- **What it does not say.** That the operands change places: `("ab" ++ "c")%a` is `"abc"` and `("c" ++ "ab")%a` is `"cab"`. Nor that an operation can be undone: no `Nat0` added to `3` gives `0`.

---

## Group

- **The problem.** To solve `x + 3 = 5`, take `3` away on both sides. That needs a value that undoes `3`: `(- 3) + 3` is `0`. `Nat0` has no such value, and `Integer` has one for every number.
- **The class.** `Group op e inv` holds `Monoid op e` and adds `Group.inverse`: `op (inv x) x = e /\ op x (inv x) = e`.
- **Instances.** `Integer_add_group` and `Rational_add_group`, with `negate`. `UInt8_add_group` and the other fixed-width integers, whose sum wraps: `UInt8.negate 1` is `255`. `Bool_xor_group`, where each value undoes itself: `Bool.xor true true` is `false`.
- **In a proof.** `Group.inverse x` gives the two equations as a conjunction.
- **What it does not say.** That the operands change places; that is `AbelianGroup`. Nor anything of a second operation: `*` on `Integer` is a monoid, `Integer_mul_monoid`, and no group, since no `Integer` multiplied by `2` gives `1`.

---

## Commutative

- **The problem.** `2 + 3` and `3 + 2` are both `5`: the operands change places. Not every operation allows it: `Integer.sub 5 3` is `2`, and `Integer.sub 3 5` is `-2`.
- **The class.** `Commutative op` has one field, `Commutative.commutativity`: `op x y = op y x`.
- **Instances.** `+` and `*` of the number types and of the fixed-width integers, as `Nat0_add_commutative` and `Nat0_mul_commutative`; `min` and `max`, as `Nat0_min_commutative`; and the `and`, `or` and `xor` of `Bool`, `Bit` and `Byte`, as `Bool_and_commutative`.
- **In a proof.** `Commutative.commutativity x y` is that equation for the operation of the goal.
- **What it does not say.** Anything else. It holds no other class, so it gives neither associativity nor an identity.

---

## AbelianMonoid and AbelianGroup

- **The problem.** To reorder a sum of several numbers, a proof regroups and swaps, so it needs associativity and commutativity together. "Abelian" is the name for a monoid or a group whose operands change places.
- **The class.** `AbelianMonoid op e` holds `Monoid op e` and `Commutative op`, and `AbelianGroup op e inv` holds `Group op e inv` and `Commutative op`. Neither adds a law.
- **Instances.** `Nat0_add_abelian_monoid`, and `Integer_add_abelian_group` and `Rational_add_abelian_group`. Each fixed-width integer has an abelian group for its `+`.
- **In a proof.** The fields of the classes held are found from the one instance: `Monoid.identity`, `Commutative.commutativity`, and `Group.inverse` for a group.
- **What it does not say.** An `AbelianGroup` instance gives no `AbelianMonoid` instance. The two classes stand side by side, and each gives `Monoid` and `Commutative` directly.

---

## Cancellative

- **The problem.** From `3 + y = 3 + z`, a proof concludes `y = z`. That step is not free: `0 * 1` and `0 * 2` are both `0`, and `1` is not `2`.
- **The class.** `Cancellative op` has one field, `Cancellative.cancellation`: `(op x y = op x z -> y = z) /\ (op x y = op z y -> x = z)`, an operand cancelled on the left and on the right.
- **Instances.** `Nat0_add_cancellative` and `Integer_add_cancellative` for `+`. `Nat_add_cancellative` and `Nat_mul_cancellative`: `*` cancels on `Nat`, which has no `0`, and has no instance on `Nat0`.
- **In a proof.** `Cancellative.cancellation x y z` gives the two implications as a conjunction.
- **What it does not say.** That a value undoes another: `+` on `Nat0` cancels with no negative numbers. A `Group` instance gives no `Cancellative` instance either; the fixed-width integers have none.

---

## Semiring

- **The problem.** Arithmetic has two operations that work together: `2 * (3 + 4)` and `2 * 3 + 2 * 4` are both `14`, and `0 * 5` is `0`. Neither fact is about `+` alone or about `*` alone.
- **The class.** `Semiring add zero mul one` holds `AbelianMonoid add zero` and `Monoid mul one`. It adds `Semiring.distributivity`, `mul x (add y z) = add (mul x y) (mul x z) /\ mul (add y z) x = add (mul y x) (mul z x)`, and `Semiring.annihilation`, `mul zero x = zero /\ mul x zero = zero`.
- **Instances.** `Nat0_semiring` and `BinWithZero_semiring`, the two number types that start at `0`.
- **In a proof.** `Semiring.distributivity x y z` and `Semiring.annihilation x`. `Monoid.identity` serves both operations: the goal decides whether it is `0 + n = n` or `1 * n = n`.
- **What it does not say.** That a sum can be undone; that is `Ring`. Nor that the factors change places: `Nat0_mul_commutative` is an instance of its own.

---

## Ring

- **The problem.** With negative numbers, every sum can be undone, and the two operations still work together: `Integer` adds, negates and multiplies.
- **The class.** `Ring add zero negate mul one` holds `AbelianGroup add zero negate` and `Monoid mul one`, and adds `Ring.distributivity`, the same two equations as `Semiring.distributivity`.
- **Instances.** `Integer_ring`, `Rational_ring` and `Bin_ring`. `UInt8_ring` and the other fixed-width integers, whose arithmetic wraps: `(200 + 100)%uint8` is `44`. `Bool_ring`, `Bit_ring` and `Byte_ring`, with `xor` as the sum and `and` as the product.
- **In a proof.** `Ring.distributivity x y z`, and the fields of the classes held: `Group.inverse`, `Commutative.commutativity` for the sum, `Monoid.identity` for both operations.
- **What it does not say.** That a product can be undone: no `Integer` is half of `1`. That the factors change places. And a `Ring` instance gives no `Semiring` instance: `Ring` has no `annihilation` field.

---

## Using a class in a proof

At a concrete operation, the instance is found from the goal. A law stated over a class is proved once and holds at every instance:

```
From jwa Require Import Algebra.All.
From jwa Require Import Data.All.

Definition zero_changes_nothing
  : forall (n : Nat0) . (0 + n = n /\ n + 0 = n)%n0
  := fun (n : Nat0) . Monoid.identity n.

Theorem neutrality
  : forall {A : Type} {op : A -> A -> A} {e : A} {M : Monoid op e} (x : A) .
      op e (op x e) = x.
Proof.
  intros A op e M x.
  match (Monoid.identity &x) with | left right end.
  leibniz &right in |- *.
  ipso &left.
Qed.

Definition neutrality_of_addition
  : forall (n : Nat0) . (0 + (n + 0) = n)%n0
  := fun (n : Nat0) . neutrality n.

Definition neutrality_of_strings
  : forall (s : AsciiStr) . ("" ++ (s ++ ""))%a = s
  := fun (s : AsciiStr) . neutrality s.
```

`neutrality` names no type. `neutrality_of_addition` and `neutrality_of_strings` are that one proof at `Nat0_add_monoid` and at `AsciiStr_concat_monoid`, each instance found from the operation in the statement.
