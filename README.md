<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# rocq-jwa
Library for Rocq

A general-purpose Rocq library in layers, under the logical root `jwa`. Import a layer with `From jwa Require Import <Layer>.All`, or everything with `From jwa Require Import All`.

---

## Requirements

An opam switch holding these packages, all from the default opam repository:

| Package | Version | What it provides |
|:---|:---|:---|
| `rocq-core` | 9.2 or later | The prover, and Ltac2, the language the tactics are written in |
| `dune` | 3.21 or later | The build |
| `ocaml` | whatever `rocq-core` asks for | The compiler both are built with |

The versions tested are `rocq-core` 9.2.0, `dune` 3.23.1 and `ocaml` 5.4.1. From a fresh opam installation:

```
opam switch create rocq-jwa ocaml-base-compiler.5.4.1
eval $(opam env --switch=rocq-jwa)
make deps
make
```

`make deps` installs what `opam/rocq-jwa.opam` declares into the active switch. Every other `make` target runs its command inside the switch through `opam exec`, so the shell need not have run `opam env` for those.

---

## Building

| Command | What it does | When to use it |
|:---|:---|:---|
| `make` | Compiles every layer to `.vo` under `_build/default/theories/`, and the test suite. Silent on success. | After any change to a `.v` or `dune` file. |
| `opam exec -- dune build theories/Data` | Compiles one layer and the layers it depends on. | Iterating on a single layer. |
| `make opam` | Regenerates `opam/rocq-jwa.opam` from `dune-project`, rewriting it in place. | After changing a field of `dune-project` that ends up in the opam file: version, depends, synopsis, description, authors, maintainers, license, source, tags. |
| `make fmt-check` | Prints the formatting diff of the `dune` files without touching them; CI runs it. | Before committing, to see what `make fmt` would change. |
| `make fmt` | Reformats the `dune` files in place. `.v` files are never touched. | When `make fmt-check` reports a diff you agree with. |
| `opam exec -- dune build @install` | Builds exactly what an opam installation of the package would build. | Before a release, as a self-check. |
| `make clean` | Deletes `_build/`. | When a build result looks stale or inconsistent. |
| `make deps` | Installs the dependencies declared in `opam/rocq-jwa.opam` into the active switch. | Once, on a new switch. |

---

## No prelude

Every theory is built with `-noinit`, so **Rocq's prelude is never loaded**: a file sees only what it requires by name. The library defines its own notations, connectives, equality and data types, and requires nothing from `Corelib`. Two compiled plugins are used as they are:

- **Ltac2**, the tactic engine, loaded by `theories/Dialect/Ltac.v`;
- **the numeral reader** behind `Number Notation`, loaded by `theories/Data/Number/Numeral.v`.

---

## Documentation

- [Usage](docs/usage.md): installing the library and using it in a project of your own.
- [The tactic language](docs/tactic.md): Ltac2 with Rocq's own tactics hidden, and the tactics that take their place.
- [Numbers](docs/numbers.md): the number types, their conversions, arithmetic and literals.
- [Machine units](docs/machine.md): `Bit`, `Byte`, `UInt8` and `Int8`.
- [Layout](docs/layout.md): the layers, their directories and what each depends on.

---

## Tests

`test/` is the theory `jwa_test`, **not part of the library**: `make` builds it, an opam installation leaves it out.

- **One file per umbrella** (`DataAll.v`, `DataMachineAll.v`, ...), each importing that umbrella alone. An umbrella defines nothing, so only an import in isolation shows whether it forwards everything it should.
- **`TacticsAll.v`** checks every form of every tactic, and every refusal with `Fail`.
