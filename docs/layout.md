<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Layout

The library lives under `theories/`, **one directory per layer**. Each layer:

- is one dune theory under the logical root `jwa`: `theories/Data/` is `jwa.Data`;
- has an umbrella module `All` that re-exports the whole layer;
- lists `Ltac2` among its dependencies.

---

## The layers

| Layer | Purpose | Depends on |
|:---|:---|:---|
| `jwa.Dialect` | The tactic language: Ltac2 with Rocq's tactic syntax hidden, and the tactics that name no definition of the library | -- |
| `jwa.Core` | Base definitions, notations, the connectives and equality, the instance hint database and the minimal lemmas everything else shares | Dialect |
| `jwa.Tactics` | Tactics that apply the laws of Core: the rules of inference by name, symmetry and transitivity, witnesses | Dialect, Core |
| `jwa.Algebra` | Algebraic structures, from semigroups to rings, and their theory | Dialect, Core |
| `jwa.Relation` | Orders, well-founded and equivalence relations | Dialect, Core, Tactics |
| `jwa.Data` | Concrete data types: the base types, the machine units, products, coproducts, options, the numbers, lists, and the functor class they instantiate | Dialect, Core, Tactics, Algebra, Relation |
| `jwa.Assumption` | Axioms: classical principles, extensionality, decidability; the layer holds only its umbrella | Dialect, Core |
| `jwa.Programming` | Monad instances, effects, extraction-oriented code; the layer holds only its umbrella | Dialect, Core, Tactics, Algebra, Relation, Data |
| `jwa.All` | `From jwa Require Import All` brings in every layer except Assumption | every layer but Assumption |

**`Assumption` is the only layer that may introduce axioms**, and no other layer depends on it, so everything else stays axiom-free under `Print Assumptions`, the command its name is taken from. Import it explicitly, with `From jwa Require Import Assumption.All`, when a development needs it.

---

## Groups inside a layer

In `Core`, `Relation` and `Data`, whose `dune` files carry `(include_subdirs qualified)`, a subdirectory groups related modules and **becomes a segment of the module path**: `theories/Core/Logic/Conjunction.v` is `jwa.Core.Logic.Conjunction`. Each group has its own umbrella, such as `From jwa Require Import Core.Logic.All`.

| Group | Holds |
|:---|:---|
| `Core/Logic/` | The connectives, `Verum`, `Falsum`, `forsome` and the syllogisms |
| `Relation/Order/` | The order classes |
| `Data/Base/` | The types built from no other type: `Empty`, `Unit`, `Bool`, `Comparison` |
| `Data/Collection/` | `List` and `NonEmptyList` |
| `Data/Machine/` | The fixed-width units a machine stores: `Bit`, `Byte`, `UInt8`, `Int8` |
| `Data/Number/` | `Nat`, `Nat0`, `Integer`, `Rational`, and `Numeral`, the digit types a literal is read into |
| `Data/Number/Binary/` | `BinBase`, `BinWithZero`, `Bin`, also forwarded by `Data.Number.All` |
