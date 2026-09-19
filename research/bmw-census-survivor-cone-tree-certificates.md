---
rg: 2
id: bmw-census-survivor-cone-tree-certificates
kind: claim
title: Solver-free cone-propagation certificates that the parity kernel is not left-orderable, for 485 of the 994 BMW census classes that have neither an irreducibility nor a Klein certificate
distinct_from:
  bmw-degree-44-53-parity-kernels-not-left-orderable: that proves the census theorem with SAT solvers (CaDiCaL and Glucose agreeing); this replaces the solver by an explicit finite certificate for each listed class, checked by a short independent script
  bmw-census-klein-power-chain-certificates: that certifies classes by Klein-power cycles; the classes here have no such certificate
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that is the SAT-based statement for degrees (3,3), (4,3) and torsion-free (4,4)
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/README.md
  - experiments/bmw-cone-trees-2026-09-18/remaining.py
  - experiments/bmw-cone-trees-2026-09-18/remaining.json
  - experiments/bmw-cone-trees-2026-09-18/dtree2.py
  - experiments/bmw-cone-trees-2026-09-18/runall.py
  - experiments/bmw-cone-trees-2026-09-18/run_R4.jsonl
  - experiments/bmw-cone-trees-2026-09-18/run_R4b.jsonl
  - experiments/bmw-cone-trees-2026-09-18/run_R6.jsonl
  - experiments/bmw-cone-trees-2026-09-18/run_R6b.jsonl
  - experiments/bmw-cone-trees-2026-09-18/pack_trees.py
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
  - experiments/bmw-cone-trees-2026-09-18/mutate_test.py
  - experiments/bmw-cone-trees-2026-09-18/mutate_test.log
  - research/bmw-census-survivor-cone-tree-certificates-proof.md
---

**ESTABLISHED.** The proof is in `bmw-census-survivor-cone-tree-certificates-proof`. It is a soundness
argument plus an exact finite check (`verify_trees.log`: `summary: 485 certificates OK, 0 failed`).
No SAT solver is involved.

## Statement

Let `Γ` be the BMW group of a class of `experiments/bmw-census-left-orders-2026-09-17/census_<pattern>.json`
and `Γ^+` its parity kernel. For each of the 485 classes `(pattern, class)` recorded in
`experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz`, `Γ^+` is not left-orderable.

The record is a cone-propagation tree on the radius-`R` ball (`R = 4` or `6`), with at most 448
leaves (median 10). It refutes every positive cone on `Γ^+`, and `verify_cone.py` checks it
from the census squares alone.

The classes are among the 994 *remaining* census classes of `remaining.json`. A class is remaining
when its irreducibility is not certified in the census and it has no Klein-power or Klein-frame
certificate.

| degree | patterns | remaining | first UNSAT at `R = 4` | with a certificate here |
|---|---|---|---|---|
| `(3,3)` | `30_30` (`31_30`, `31_31` have none remaining) | 2 | 1 | 2 |
| `(4,3)` | `40_30`, `41_30`, `41_31`, `42_30`, `42_31` | 41 | 19 | 33 |
| `(4,4)` | `40_40`, `41_40`, `41_41`, `42_40`, `42_41`, `42_42` | 577 | 257 | 257 |
| `(5,3)` | `50_30`, `50_31`, `51_30`, `51_31`, `52_30`, `52_31` | 374 | 193 | 193 |
| total | | 994 | 470 | 485 |

- **Radius 4.** Every remaining class whose positive-cone instance is already UNSAT at radius 4 has a
  certificate: 470 of 470.
- **Radius 6.** Of the 524 classes first UNSAT at radius 6 (short 4), 15 have a radius-6 certificate
  so far. The search `dtree2.py` exhausted its budget on the others (`run_R6.jsonl`, `run_R6b.jsonl`), or did not reach them. For the `(4,4)`
  patterns the radius-6 ball did not fit the budget at all.

## Relation to the census theorem

For the listed classes, this upgrades non-left-orderability of `Γ^+` from "two SAT solvers agree" to
an explicit certificate. Its check (`verify_cone.py`, about 60 lines) needs only:
- the rewriting normal form;
- Newman's critical pairs;
- one pass through the product steps.

The quaternionic nodes `bmw-quaternionic-type-53-parity-kernels` and
`bmw-quaternionic-char3-type-44-parity-kernels` use sixteen of these certificates.
