<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# The tactic language

Proofs are written in **Ltac2, with Rocq's own tactic syntax hidden**. `theories/Dialect/Ltac.v` exports `Ltac2.Init` but never `Ltac2.Notations`, so `exact` is an `Unbound value`: a tactic exists only once this library declares it.

- **`jwa.Dialect`** declares the tactics that name no definition of the library.
- **`jwa.Tactics`** declares those that apply laws of `jwa.Core`.

**Every file with a proof imports the language**, through `Core.All` or `Dialect.All`. A file that does not falls back to Rocq's default proof mode, where every built-in tactic is open again.

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

---

## Rocq's tactics and their replacements

Each tactic file opens with its grammar in a comment. In outline:

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

---

## Rules of inference

`jwa.Tactics` also names the rules of inference:

- `modus ponens`, `modus tollens`, `modus tollendo ponens`, `modus ponendo tollens` and `modus aequans`;
- `hs` (hypothetical syllogism) and `barbara`;
- `dni` and `dne` (double negation) and `de morgan`;
- `trans` and `congru`, the transitivity and the congruence of `=`;
- the introductions `conjoin`, `sejoin` and `abjoin`.

Bare, each is a term: `ipso (modus ponens &hab, &a)`. Followed by `as <p>` or `|- <p>`, it is a tactic that adds the conclusion as `<p>`.

---

## Principles

1. **Nothing is reduced on your behalf.**
   - `quod idem est` closes `a = b` only when both sides are the same term as written.
   - `ex &h quodlibet` needs the empty type, or a clash of constructors, as written.
   - `leibniz` takes an equation given whole, never a law left to be instantiated.

   A step that computes is written out first, with `simpl`, or as the term `simpl &h`, which is `&h` with its type reduced: `leibniz (simpl &e) in |- *`.
2. **Every refusal says what and where**, in the tactic's own words: `simpl: negate does not occur in h`, `rm: the goal depends on n, so it cannot be cleared`.
3. **A name of the context is written `&h`**: a hypothesis, a local definition or a type introduced by `intros`. A global name is written bare, and a name being introduced takes no `&` (`intro a`, `let proof x`, the names of a `match` branch). A bare name of the context is accepted by default; `Ltac2 Set Local.checking := Strict` makes every tactic refuse it with `<tactic>: h is in the context; write &h`.

---

## Writing Ltac2 code

**`let` and `match` take over Ltac2's own `let ... in` and `match ... with ... end`.** In a proof, and in any file that imports `Dialect.All` or `Core.All`, those two Ltac2 constructs no longer parse. Ltac2 code is therefore written only in files that import `Dialect.Ltac` alone, as the files of `jwa.Dialect` and `jwa.Tactics` do, each helper declared before any notation of the same file that shadows what it uses.
