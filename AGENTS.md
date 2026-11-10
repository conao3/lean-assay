# AGENTS.md

lean-assay: the `#assay` command, which runs broken versions of Lean functions against the
theorems about them.

## Layout

- `Assay/Runtime.lean`: the values a check returns and the loops that run it (random or exhaustive).
- `Assay/Sample.lean`: generators that replace plausible's defaults (`Char`).
- `Assay/Check.lean`: a theorem as clauses, and a clause as a generated, evaluated check.
- `Assay/Collect.lean`: the theorems about the audited functions, and the instances their types need.
- `Assay/Source.lean`: the source of a declaration, and elaborating an edited copy under a new name.
- `Assay/Mutant.lean`: the ways a function is broken.
- `Assay/Command.lean`: `#assay` and its report.
- `Examples/`: audited code. `AssayTest/`: `#guard_msgs` over the full report of each example.

## Conventions

- Lean 4.35.0 (`lean-toolchain`), plausible `v4.35.0`.
- A run must be reproducible: the seed is fixed and the report does not depend on timing.
- When the report changes on purpose, rewrite the expected outputs with
  `nix develop -c scripts/update-expected.sh` and read the diff.

## Verification

- `nix develop -c make check`: treefmt check, `lake build Assay Examples`, `lake test`.
- `nix build`: the same build and tests inside the Nix sandbox.
