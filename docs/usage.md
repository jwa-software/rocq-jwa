<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Usage

## 1. Install

The package is not in the default opam repository. Pin it into your switch from GitHub:

```
opam pin add rocq-jwa git+https://github.com/jwa-software/rocq-jwa.git
```

## 2. Declare the dependency

In a dune project whose `dune-project` declares `(using rocq 0.11)`, list `Ltac2` and the layers your theory uses, and build it with `-noinit`, as the library itself is built:

```
(rocq.theory
 (name my_theory)
 (theories
  Ltac2
  jwa
  jwa.Dialect
  jwa.Core
  jwa.Tactics
  jwa.Algebra
  jwa.Relation
  jwa.Data
  jwa.Programming)
 (flags :standard -noinit))
```

## 3. Import and prove

A file of that theory imports the layers it needs. This one proves the commutativity of `Nat0` addition from the library's own law, and checks that `UInt8` addition wraps:

```
From jwa Require Import Data.All.

Theorem commutation
  : forall (m : Nat0) (n : Nat0) . (m + n = n + m)%n0.
Proof.
  intros m n.
  ipso (Nat0.addition.commutativity &m &n).
Qed.

Theorem wrapping
  : (200 + 100 = 44)%uint8.
Proof.
  ipso (Identity.reflexivity _).
Qed.
```

**Keep `-noinit`.** Without it, Rocq's prelude is loaded beside the library, the two declare overlapping notations, and Rocq warns wherever the library is imported (`Hiding binding of key list to list_scope`).
