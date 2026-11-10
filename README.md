# lean-assay

Check whether your Lean theorems pin down your implementation, by running broken implementations
against them.

A proof that goes through says nothing about the implementation if a broken implementation
satisfies the same theorems. `#assay f` breaks `f` in many small ways, runs every theorem about
`f` against each broken version, and reports the broken versions that change what `f` returns but
still satisfy every theorem. It does not need the proofs: it decides the statements on concrete
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

19 mutants: 17 killed, 2 holes, 0 untested, 0 equivalent, 0 stillborn
warning: hole: `step: 19:3: add | .begun, .begin => some .begun` satisfies every theorem; it differs from the original on #1 := proved.TokenState.begun, #2 := proved.ProgressKind.begin
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
plausible's `Arbitrary` and `Shrinkable`) for the types of the audited module, and those instances
stay in that file.

## What it checks

For `#assay f g …`:

1. It collects the theorems in the modules of `f`, `g`, … whose statements mention them or a
   definition that calls them. Each conjunct of a conclusion is a column of the table.
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
   definitions that call it. Versions that do not typecheck are counted as stillborn. A version
   whose output equals the original on every input tried is counted as equivalent and not shown.
5. Every column is run on the broken version. A cell is `✗` when an input satisfies the hypotheses
   but not the conclusion, `·` when enough inputs satisfied the hypotheses and the conclusion held,
   `?` when too few inputs satisfied the hypotheses, and `-` when the column does not depend on the
   function.

A broken version is a `HOLE` when it changes the output and every column that depends on it held.
The warning names an input on which it differs from the original.

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
| `assay.failOnHole` | false | report holes as errors, so that `lake build` fails |

## Limits

- Only executable statements: the hypotheses and conclusions must be decidable, and the data
  binders need plausible's `SampleableExt`. Theorems about real numbers or other noncomputable
  definitions are reported as not executable.
- Random inputs only show that no counterexample was found among the inputs tried. "Equivalent"
  means the same output on every input tried.
- Hypotheses that use the proof of an earlier hypothesis are not supported.
- The broken versions are elaborated from the source text, with `open` commands of the file. Section
  `variable`s are not carried over.

## Development

```sh
nix develop -c make check            # format check, build, tests
nix develop -c scripts/update-expected.sh  # rewrite the expected output of AssayTest/
nix build                             # build and test inside the Nix sandbox
```

`Examples/LspTouchstone/` holds the Lean files of lsp-touchstone at commit
[`3c19dae`](https://github.com/conao3/rust-lsp-touchstone/tree/3c19daee54f248abfad0f7540e3b65f11602375d/lean/LeanRustGen/Embed/lsp_touchstone).

## License

Apache-2.0
