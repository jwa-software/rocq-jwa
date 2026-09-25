# rocq-jwa
Library for Rocq

A general-purpose Rocq library organised in layers. Each layer is its own dune theory under the logical root `jwa`, so a client imports one layer with `From jwa Require Import Data.All`, or everything at once with `From jwa Require Import All`.

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

## No prelude

The root `dune` builds every theory with `-noinit`, so `Corelib.Init.Prelude` is not loaded anywhere in this tree. A file has nothing in scope that it did not require by name.

That is wider than the datatypes. There are no notations, including `->`, which is spelled `forall _ : A, B`. There is no numeral parsing, so `0` does not elaborate even once `Corelib.Init.Datatypes` is required. And there are none of Rocq's tactics: see the next section.

Nothing in this tree requires anything from `Corelib`. The notations, the connectives, equality and the data types are all defined here. The one piece not rebuilt is the tactic engine itself, which is a compiled plugin rather than a theory: `theories/Dialect/Ltac.v` loads the core of Ltac2, `Ltac2.Init`, and makes Ltac2 the proof mode.

## The tactic language

Proofs are written in Ltac2 with Rocq's own tactic syntax hidden. `theories/Dialect/Ltac.v` exports `Ltac2.Init` and never `Ltac2.Notations`, so `exact` is `Unbound value exact`: a tactic exists only once this library declares it. Two layers declare them. `jwa.Dialect` holds the tactics that name no definition of the library; `jwa.Tactics` holds those that apply laws of `jwa.Core`. Every file with a proof imports the language, through `Core.All` or `Dialect.All`; a file that does not falls back to Rocq's default proof mode, where every built-in tactic is open again.

```
Theorem commutativity
  : forall {A : Prop} {B : Prop} . A \/ B -> B \/ A.
Proof.
  intros A B h.
  match &h with | a | b end.
  - ipso (disjoin _, &a).
  - ipso (disjoin &b, _).
Qed.
```

Each tactic file opens with its grammar in a comment. In outline, against the Rocq tactic each one takes the place of:

| Rocq | Here | Declared in |
|:---|:---|:---|
| `intro`, `intros` | the same, borrowed from `Ltac2.Notations` | `Dialect/Loanword.v` |
| `exact h` | `ipso &h` | `Dialect/Ipso.v` |
| `reflexivity` | `quod idem est` | `Dialect/Idem.v` |
| `split` | `divide et impera` | `Dialect/DivideEtImpera.v` |
| `contradiction h`, `discriminate h` | `ex &h quodlibet` | `Dialect/ExFalso.v` |
| `destruct h as [a \| b] eqn:e` | `match &h with \| a \| b end \|- e` | `Dialect/Match.v` |
| `induction n as [\| n' IH] using Nat.induction` | `match &n with \| One \| Successor (n' by IH) end per Nat.induction` | `Dialect/Match.v` |
| `rewrite e in h \|- *` | `leibniz &e in &h \|- *` | `Dialect/Leibniz.v` |
| `unfold d in h`, `simpl in h` | `simpl d in &h`, `simpl in &h` | `Dialect/Simpl.v` |
| `pose (x := t)`, `set (x := t) in h` | `let x := t`, `let x := t in &h` | `Dialect/Let.v` |
| `pose proof t as p` | `let proof p := t` | `Dialect/Let.v` |
| `assert (h : T)` | `lemma h : T.` | `Dialect/Lemma.v` |
| `rename h into g`, `clear h` | `mv &h g`, `rm &h` (also `rm -f`, `rm -r`) | `Dialect/Context.v` |
| `revert h`, `generalize dependent h` | `extro &h`, `extros &h1 &h2` | `Dialect/Context.v` |
| `symmetry in h`, `symmetry` | `symm in &h`, `symm in \|- *` | `Tactics/Equation.v` |
| `exists w` | `exists &w` | `Tactics/Witness.v` |
| `left`, `right` | the terms `disjoin a, _` and `disjoin _, b` | `Core/Logic/Disjunction.v` |

`jwa.Tactics` also names the rules of inference: `modus ponens`, `modus tollens`, `modus tollendo ponens`, `modus ponendo tollens`, `modus aequans`, `hs` (hypothetical syllogism), `barbara`, `dni` and `dne` (double negation), `de morgan`, `trans` and `congru` (the transitivity and the congruence of `=`), and the introductions `conjoin`, `sejoin` and `abjoin`. Bare, each is a term, `ipso (modus ponens &hab, &a)`; followed by `as <p>` or `|- <p>` it is a tactic that adds the conclusion as `<p>`.

**Nothing is reduced on the user's behalf.** `quod idem est` closes `a = b` only when the two sides are the same term as written; `ex &h quodlibet` needs the empty type or the clash of constructors as written; `leibniz` takes an equation given whole, never a law left to be instantiated. A step that computes is written out before, with `simpl`, or on the proof itself as the term `simpl &h`, which is `&h` with its type reduced: `leibniz (simpl &e) in |- *`. **Every refusal says what and where**, in the tactic's own words: `simpl: negate does not occur in h`, `rm: the goal depends on n, so it cannot be cleared`.

**A name of the context is written `&h`**: a hypothesis, a local definition and a type introduced by `intros` alike. A global name is written bare, and a name being introduced takes no `&` (`intro a`, `let proof x`, the names of a `match` branch). By default a bare name of the context is accepted too; `Ltac2 Set Local.checking := Strict` makes every tactic refuse it with `<tactic>: h is in the context; write &h`.

**`let` and `match` take over Ltac2's own `let ... in` and `match ... with ... end`.** In a proof, and in any file that imports `Dialect.All` or `Core.All`, those two Ltac2 constructs no longer parse. Ltac2 code is therefore written only in files that import `Dialect.Ltac` alone, as the files of `jwa.Dialect` and `jwa.Tactics` do, with each helper declared before any notation of the same file that shadows what it uses.

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

The opam file is generated: after regenerating it, commit the rewritten file like any other change. CI fails when it is out of date.

## Layout

Layers live under `theories/`, one directory and one `dune` stanza per layer. Each layer has an umbrella module `All` that re-exports the whole layer, and every stanza lists `Ltac2` among its dependencies.

A layer may group related modules in a subdirectory. `theories/Core/dune` carries `(include_subdirs qualified)`, which makes a subdirectory a segment of the module path, so `theories/Core/Logic/Conjunction.v` is the module `jwa.Core.Logic.Conjunction`. Such a group carries its own umbrella, imported as `From jwa Require Import Core.Logic.All`. `theories/Relation/Order/` groups the order classes the same way, under `From jwa Require Import Relation.Order.All`, and `theories/Data/` has three such groups: `Base/` for the types built from no other type (`Empty`, `Unit`, `Bool`, `Comparison`), `Collection/` for `List` and `NonEmptyList`, and `Number/` for `Nat`, `NatWithZero`, `Integer` and `Rational`.

| Layer | Purpose | Depends on |
|:---|:---|:---|
| `jwa.Dialect` | The tactic language: Ltac2 with Rocq's tactic syntax hidden, and the tactics that name no definition of the library | -- |
| `jwa.Core` | Base definitions, notations, the connectives and equality, the instance hint database and the minimal lemmas everything else shares | Dialect |
| `jwa.Tactics` | Tactics that apply the laws of Core: the rules of inference by name, symmetry and transitivity, witnesses | Dialect, Core |
| `jwa.Algebra` | Algebraic structures, from semigroups to rings, and their theory | Dialect, Core |
| `jwa.Relation` | Orders, well-founded and equivalence relations | Dialect, Core, Tactics |
| `jwa.Data` | Concrete data types: the base types, products, coproducts, options, the numbers, lists, and the functor class they instantiate | Dialect, Core, Tactics, Algebra, Relation |
| `jwa.Assumption` | Axioms: classical principles, extensionality, decidability; the layer holds only its umbrella | Dialect, Core |
| `jwa.Programming` | Monad instances, effects, extraction-oriented code; the layer holds only its umbrella | Dialect, Core, Tactics, Algebra, Relation, Data |
| `jwa.All` | `From jwa Require Import All` brings in every layer except Assumption | every layer but Assumption |

`Assumption` is the only layer that may introduce axioms, and no other layer depends on it; its name is the one `Print Assumptions` uses for them. Import it explicitly with `From jwa Require Import Assumption.All` when a development needs them; everything else stays axiom-free under `Print Assumptions`.

## Tests

`test/` is a theory of its own, `jwa_test`, and is not part of the library: its `dune` declares no package, so `dune build` compiles it while `dune build @install` leaves it out.

It holds one file per umbrella that re-exports anything, each importing that umbrella and nothing else. An umbrella defines nothing, so it cannot fail to compile on its own -- it either forwards what its modules hold or silently does not, and importing one in isolation is what makes the difference visible. A file importing two would receive from one whatever the other fails to forward.

`TacticsAll.v` goes further, and imports `Data.All` beside `Tactics.All` to have something to prove. It holds a guard for every form of every tactic of the language, and one for each refusal, written with `Fail`. A guard that checks the shape a tactic leaves behind uses `lazy_match!`, which that file declares for itself.
