# rocq-jwa
Library for Rocq

A general-purpose Rocq library organised in layers. Each layer is its own dune theory under the logical root `jwa`, so a client imports one layer with `From jwa Require Import Data.All`, or everything at once with `From jwa Require Import All`.

## Requirements

An opam switch with `dune >= 3.21` and `rocq-core >= 9.2`. Every command below runs inside that switch through `opam exec`.

## No prelude

The root `dune` builds every theory with `-noinit`, so `Corelib.Init.Prelude` is not loaded anywhere in this tree. A file has nothing in scope that it did not require by name.

That is wider than the datatypes. There is no tactic language -- `exact` is a syntax error, not an unknown tactic. There are no notations, including `->`, which is spelled `forall _ : A, B`. There is no numeral parsing, so `0` does not elaborate even once `Corelib.Init.Datatypes` is required.

Nothing in this tree requires anything from `Corelib`. The notations, the connectives, equality and the data types are all defined here. The one piece not rebuilt is the tactic language itself, which is a compiled plugin rather than a theory: `theories/Core/Ltac.v` declares it and sets the proof mode.

## Building

| Command | What it does | When to use it |
|:---|:---|:---|
| `opam exec -- dune build` | Compiles every layer to `.vo` under `_build/default/theories/`. Silent on success. | After any change to a `.v` or `dune` file. |
| `opam exec -- dune build theories/Data` | Compiles one layer and the layers it depends on. | Iterating on a single layer. |
| `opam exec -- dune build opam/rocq-jwa.opam` | Regenerates `opam/rocq-jwa.opam` from `dune-project`, rewriting it in place. | After changing a field of `dune-project` that ends up in the opam file: version, depends, synopsis, description, authors, maintainers, license, source, tags. |
| `opam exec -- dune build @fmt` | Prints the formatting diff of the `dune` files without touching them. | Before committing, to see what `dune fmt` would change. |
| `opam exec -- dune fmt` | Reformats the `dune` files in place. `.v` files are never touched. | When `@fmt` reports a diff you agree with. |
| `opam exec -- dune build @install` | Builds exactly what an opam installation of the package would build. | Before a release, as a self-check. |
| `opam exec -- dune clean` | Deletes `_build/`. | When a build result looks stale or inconsistent. |

The opam file is generated: after regenerating it, commit the rewritten file like any other change. CI fails when it is out of date.

## Layout

Layers live under `theories/`, one directory and one `dune` stanza per layer. Each layer has an umbrella module `All` that re-exports the whole layer.

A layer may group related modules in a subdirectory. `theories/Core/dune` carries `(include_subdirs qualified)`, which makes a subdirectory a segment of the module path, so `theories/Core/Logic/Conjunction.v` is the module `jwa.Core.Logic.Conjunction`. Such a group carries its own umbrella, imported as `From jwa Require Import Core.Logic.All`.

| Layer | Purpose | Depends on |
|:---|:---|:---|
| `jwa.Core` | Base definitions, notations and the minimal lemmas everything else shares | -- |
| `jwa.Tactics` | Ltac and Ltac2 tactics | Core |
| `jwa.Structures` | Type classes and interfaces: equality, orders, monoids, functors, monads, decidability | Core |
| `jwa.Relations` | Orders, well-founded and equivalence relations | Core, Structures |
| `jwa.Data` | Concrete data structures: booleans, naturals, options, lists, vectors, maps | Core, Tactics, Structures, Relations |
| `jwa.Assumption` | Axioms: classical principles, extensionality, decidability | Core |
| `jwa.Algebra` | Algebraic structures and their theory | Core, Tactics, Structures, Relations, Data |
| `jwa.Programming` | Monad instances, effects, extraction-oriented code | Core, Tactics, Structures, Relations, Data |
| `jwa.All` | `From jwa Require Import All` brings in every layer except Assumption | every layer but Assumption |

`Assumption` is the only layer that may introduce axioms, and no other layer depends on it; its name is the one `Print Assumptions` uses for them. Import it explicitly with `From jwa Require Import Assumption.All` when a development needs them; everything else stays axiom-free under `Print Assumptions`.

## Tests

`test/` is a theory of its own, `jwa_test`, and is not part of the library: its `dune` declares no package, so `dune build` compiles it while `dune build @install` leaves it out.

It holds one file per umbrella, each importing that umbrella and nothing else. An umbrella defines nothing, so it cannot fail to compile on its own -- it either forwards what its modules hold or silently does not, and importing one in isolation is what makes the difference visible. A file importing two would receive from one whatever the other fails to forward.
