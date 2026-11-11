# lean-assay

Check whether your Lean theorems pin down your implementation, by running broken implementations
against them.

A proof that goes through says nothing about the implementation if a broken implementation
satisfies the same theorems. `#assay f` breaks `f` in many small ways, runs every theorem about
`f` against each broken version, and reports the broken versions that satisfy every theorem but
change what `f` returns on an input that satisfies a theorem's hypotheses. It does not need the proofs: it decides the statements on concrete
inputs, so it also works on theorems that are still `sorry`.

```lean
import Assay
import MyProject.Progress

#assay proved.step
```

```
theorems, run on the original functions:
  T1 ended_accepts_nothing: 3/3 all inputs satisfy the hypotheses
  T2 only_begin_leaves_created.1: 1/9 all inputs satisfy the hypotheses
  …

mutant                                                        T1  T2  T3  T4  T5  T6  T7   verdict
step := fun _ _ => none                                       ·   ?   ?   ·   ·   ?   ✗    killed
step: 19:3: add | .begun, .begin => some .begun               ·   ·   ·   ·   ·   ·   ·    HOLE
…

19 mutants: 17 killed, 2 holes, 0 untested, 0 equivalent, 0 timed out, 0 stillborn
warning: hole: `step: 19:3: add | .begun, .begin => some .begun` satisfies every theorem but changes the output on an input that satisfies the hypotheses of begun_never_returns_to_created: k := proved.ProgressKind.begin
```

The full outputs for three files of [lsp-touchstone](https://github.com/conao3/rust-lsp-touchstone)
are the tests in [`AssayTest/`](AssayTest).

## Install

Lean 4.35.0. Add the package to `lakefile.toml`:

```toml
[[require]]
name = "assay"
git = "https://github.com/conao3/lean-assay"
rev = "master"
```

Run `#assay` in a file of its own: it derives the instances it needs (`Repr`, `DecidableEq`,
plausible's `Arbitrary` and `Shrinkable`) for the types of the audited package where a deriving
handler applies, and those instances stay in that file.

## What it checks

For `#assay f g …`:

1. It collects the theorems in the modules of `f`, `g`, … whose statements mention them or a
   definition that calls them. `#assay f g … using t₁ t₂ …` takes the theorems `t₁`, `t₂`, …
   instead, from any module. A proposition defined in the modules of the functions and the theorems
   that a conclusion is gets unfolded, so `theorem p_proven : P` with `def P : Prop := ∀ x, …` is
   read as `∀ x, …`; the propositions inside the conclusion stay folded.
   Each conjunct of a conclusion is a column of the table, also after unfolding `let` and `have`
   and under binders and hypotheses (`H → A ∧ B` gives `H → A` and `H → B`).
   - A hypothesis may be passed to the functions as a precondition (`f xs h` with
     `h : f_precond xs`). A column computes its conclusion only on inputs that satisfy the
     hypotheses, with the proofs replaced by the axiom `Assay.assumed`, which the compiler erases.
2. It runs every column on the original functions. A column that fails on the original is
   reported and left out of the rest. A column whose hypotheses no input satisfies is reported as
   possibly vacuous.
3. It breaks each function:
   - whole replacements: `default`, each constructor of the result type (and `some c` for each
     constructor `c` without fields), an argument returned unchanged, `xs.take 1` and `xs.reverse`
     of a list argument;
   - edits of the body: swapping a comparison, arithmetic or boolean operator, moving a numeric
     literal by one, swapping `take`/`drop`, `min`/`max` and similar pairs, swapping the operands
     of `++`, `-`, `/`, `<`, giving a match arm the result of another arm, adding an arm before the
     catch-all arm for a combination of constructors that has none, and swapping the branches of
     an `if`.
4. Each broken version is elaborated next to the original under a new name, together with the
   definitions between it and the theorems: those the statements reach that call it, directly or
   through each other, in any module of the same package. Versions that do not typecheck, or that
   raise an error when they are run, are counted as stillborn.
5. Every column is run on the broken version. A cell is `✗` when an input satisfies the hypotheses
   but not the conclusion, `·` when enough inputs satisfied the hypotheses and the conclusion held,
   `?` when too few inputs satisfied the hypotheses, and `-` when the column does not depend on the
   function.

A broken version is a `HOLE` when every column that depends on it held and, on an input that
satisfies the hypotheses of some column, a function it changes returns a different value from the
original. The warning names that theorem and input. A version whose output equals the original on
every value of its arguments (when they are few enough to try them all), or on every input tried
that satisfies the hypotheses of the columns, is counted as equivalent and not shown.

Each broken version has `assay.timeout` milliseconds to run the columns. A version that is not
killed before then is reported as `timeout`.

Inputs are random, from a fixed seed, so a run always gives the same table. When every binder has
a type whose constructors have no fields, and the product of their sizes is at most
`assay.enumLimit`, every input is tried instead. A column whose hypotheses few random inputs satisfy
gets more inputs, up to `assay.maxSamples`. The `Char` generator mixes ASCII with characters of
every UTF-8 and UTF-16 width and the code points at the boundaries between widths.

## Options

| Option | Default | Meaning |
|---|---|---|
| `assay.samples` | 1000 | random inputs per column |
| `assay.maxSamples` | 30000 | most random inputs for a column with rarely satisfied hypotheses |
| `assay.minSatisfied` | 20 | inputs that must satisfy the hypotheses before a cell counts as `·` |
| `assay.enumLimit` | 4096 | largest number of inputs tried exhaustively |
| `assay.maxSize` | 30 | largest size passed to the generators |
| `assay.seed` | 0 | seed of the random inputs |
| `assay.timeout` | 30000 | milliseconds a broken version may spend running the columns |
| `assay.failOnHole` | false | report holes as errors, so that `lake build` fails |

## Limits

- Only executable statements. A hypothesis or conclusion runs when it has a `Decidable` instance,
  or when it is built from such parts with `∧`, `∨`, `¬`, `→`, `↔`, `∃ xs, e = c … xs ∧ …` for a
  constructor `c` (`∃ t, f x = .ok t`), `∃ x, x ∈ l ∧ …` and `∀ x, x ∈ l → …` over a list, a
  `match` on a value of a non-recursive type, and non-recursive definitions. The data binders need
  plausible's `SampleableExt`. Theorems about real numbers or other noncomputable definitions are
  reported as not executable.
- A statement over a type runs over `Int`: its binders of type `Type` are set to `Int`, its
  universes to 0, and its instance binders to the instances of `Int`.
- Random inputs only show that no counterexample was found among the inputs tried. "Equivalent"
  means the same output on every input tried.
- The broken versions are elaborated from the source text, with the `open` commands of the file
  and the `variable` commands before the declaration.

## Development

```sh
nix develop -c make check            # format check, build, tests
nix develop -c scripts/update-expected.sh  # rewrite the expected output of AssayTest/
nix build                             # build and test inside the Nix sandbox
```

`Examples/LspTouchstone/` holds the Lean files of lsp-touchstone at commit
[`3c19dae`](https://github.com/conao3/rust-lsp-touchstone/tree/3c19daee54f248abfad0f7540e3b65f11602375d/lean/LeanRustGen/Embed/lsp_touchstone),
and `Examples/LspTouchstoneFixed/` the progress and position files at commit
[`f77cc2b`](https://github.com/conao3/rust-lsp-touchstone/tree/f77cc2b/lean/LeanRustGen/Embed/lsp_touchstone),
which adds the theorems that kill the holes `#assay` found in the earlier files.
`Examples/Forms/` holds small files in the shapes of other corpora: functions that take a
precondition proof, a property stated as `def P : Prop`, and a theorem in another module than the
function, about a function that calls it (`Split/`), and the shapes of statements that run without a
`Decidable` instance, over a type variable (`Shapes.lean`). `Examples/Verina/A35.lean` is the
task `verina_advanced_35` of [VERINA](https://github.com/sunblaze-ucb/verina) at commit `66b3ce5`,
without its benchmark markers.

## License

Apache-2.0
