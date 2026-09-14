# rocq-jwa
Library for Rocq

A general-purpose Rocq library organised in layers. Each layer is its own dune theory under the logical root `jwa`, so a client imports one layer with `From jwa Require Import Data.All`, or everything at once with `From jwa Require Import All`.

## Requirements

An opam switch with `dune >= 3.21` and `rocq-core >= 9.2`. Every command below runs inside that switch through `opam exec`.

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

| Layer | Purpose | Depends on |
|:---|:---|:---|
| `jwa.Core` | Base definitions, notations and the minimal lemmas everything else shares | -- |
| `jwa.Tactics` | Ltac and Ltac2 tactics | Core |
| `jwa.Structures` | Type classes and interfaces: equality, orders, monoids, functors, monads, decidability | Core |
| `jwa.Relations` | Orders, well-founded and equivalence relations | Core, Structures |
| `jwa.Data` | Concrete data structures: maps, vectors, naturals, lists, options | Core, Tactics, Structures, Relations |
| `jwa.Logic` | Classical axioms, extensionality, decidability principles | Core |
| `jwa.Algebra` | Algebraic structures and their theory | Core, Tactics, Structures, Relations, Data |
| `jwa.Programming` | Monad instances, effects, extraction-oriented code | Core, Tactics, Structures, Relations, Data |
| `jwa.All` | `From jwa Require Import All` brings in every layer except Logic | every layer but Logic |

`Logic` is the only layer that may introduce axioms, and no other layer depends on it. Import it explicitly with `From jwa Require Import Logic.All` when a development needs them; everything else stays axiom-free under `Print Assumptions`.
