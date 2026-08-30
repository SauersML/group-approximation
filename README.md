# Not Every Group Is MF

This repository formalizes an explicit countable group that is sofic but not
MF in the sequential operator-norm sense. The main result is
`ExplicitNonMF.explicit_sofic_not_MF`:

```lean
theorem explicit_sofic_not_MF :
    IsSoficGroup E ∧ ¬ IsSequentialOperatorMFGroup E
```

The formalization uses Lean 4 and Mathlib. Its axiom closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

`lake build` checks the complete proof library, the Mathlib-only Palomar
challenge, and the corresponding solution.

## Repository layout

| Path | Purpose |
| --- | --- |
| `GroupApproximation/` | Definitions, structural lemmas, finite certificates, and the proof |
| `GroupApproximation.lean` | Root module for the complete proof dependency graph |
| `Palomar/Challenge.lean` | Small Mathlib-only statement of record, with one deliberate `sorry` |
| `Palomar/Solution.lean` | The identical statement, proved from the library |
| `certificates/p13/` | Pinned inputs and generators for the exact P13 certificate |
| `scripts/` | Source, linter, axiom, signature, and Palomar verification gates |
| `metadata/` | Generated statement and audit snapshots |
| `comparator.json` | Palomar Comparator configuration |
| `formalization.yaml` | Structured provenance metadata |

## Verification

The local verification suite is:

```sh
uv sync --locked
uv run python scripts/check.py --self-test
uv run python scripts/check.py
uv run python scripts/check_palomar_submission.py --self-test
uv run python scripts/check_palomar_submission.py
uv run python scripts/check_p13_generated.py --temporary-root /tmp
lake env lean scripts/Calibrate.lean
lake env lean scripts/Audit.lean
lake env lean scripts/Lint.lean
bash scripts/check_palomar_statement_match.sh
```

The source scan permits only the deliberate hole in
`Palomar/Challenge.lean` and the planted defect used to calibrate the axiom
audit. The manual Comparator workflow performs the registry-level comparison
and independent kernel replay.

## Citation and license

Citation metadata is in `CITATION.cff`. The project is licensed under the
Apache License 2.0.
