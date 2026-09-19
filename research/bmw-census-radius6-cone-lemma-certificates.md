---
rg: 2
id: bmw-census-radius6-cone-lemma-certificates
kind: claim
title: Solver-free cone-lemma certificates that the parity kernel is not left-orderable for the 509 remaining BMW census classes without a cone tree, completing solver-free certificates for all 994
distinct_from:
  bmw-census-survivor-cone-tree-certificates: that gives tree-like cone refutations for 485 of the 994 remaining classes (all first UNSAT at radius 4, and 15 at radius 6); this gives DAG-shaped cone-lemma refutations for the other 509, all first UNSAT at radius 6 with short 4, where trees did not fit the budget
  bmw-degree-44-53-parity-kernels-not-left-orderable: that proves the census theorem with SAT solvers agreeing; this replaces the solver, for these classes, by an explicit certificate checked by an independent script
artifacts:
  - experiments/bmw-short4-cone-trees-2026-09-18/README.md
  - experiments/bmw-short4-cone-trees-2026-09-18/ctree.cpp
  - experiments/bmw-short4-cone-trees-2026-09-18/ctree.py
  - experiments/bmw-short4-cone-trees-2026-09-18/gsolve.py
  - experiments/bmw-short4-cone-trees-2026-09-18/lrat2cone.py
  - experiments/bmw-short4-cone-trees-2026-09-18/runlem.py
  - experiments/bmw-short4-cone-trees-2026-09-18/run_lem.jsonl
  - experiments/bmw-short4-cone-trees-2026-09-18/run_lemB.jsonl
  - experiments/bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz
  - experiments/bmw-short4-cone-trees-2026-09-18/verify_lemmas.py
  - experiments/bmw-short4-cone-trees-2026-09-18/verify_certs.log
  - experiments/bmw-short4-cone-trees-2026-09-18/mutate_lemmas.py
  - experiments/bmw-short4-cone-trees-2026-09-18/mutate_lemmas.log
  - experiments/bmw-short4-cone-trees-2026-09-18/coverage.py
  - experiments/bmw-short4-cone-trees-2026-09-18/coverage.log
  - research/bmw-census-radius6-cone-lemma-certificates-proof.md
---

**ESTABLISHED.** The proof is in `bmw-census-radius6-cone-lemma-certificates-proof`. It is a soundness
argument plus an exact finite check (`verify_certs.log`: `summary: 509 certificates OK, 0 failed`).
No SAT solver is part of the proof; one was used only to find the certificates.

## Statement

Let `Γ` be the BMW group of a class of `experiments/bmw-census-left-orders-2026-09-17/census_<pattern>.json`
and `Γ^+` its parity kernel. For each of the 509 classes `(pattern, class)` recorded in
`experiments/bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz`, `Γ^+` is not left-orderable.

These are exactly the classes of `experiments/bmw-cone-trees-2026-09-18/remaining.json` without a
cone tree in `bmw-census-survivor-cone-tree-certificates` (`coverage.log`). Together with that node,
**every one of the 994 remaining census classes has a solver-free certificate** that its parity
kernel is not left-orderable.

| degree | patterns | remaining | cone trees (w10) | cone-lemma certificates (here) |
|---|---|---|---|---|
| `(3,3)` | `30_30`, `31_30`, `31_31` | 2 | 2 | 0 |
| `(4,3)` | `40_30`, `41_30`, `41_31`, `42_30`, `42_31` | 41 | 33 | 8 |
| `(4,4)` | `40_40`, `41_40`, `41_41`, `42_40`, `42_41`, `42_42` | 577 | 257 | 320 |
| `(5,3)` | `50_30`, `50_31`, `51_30`, `51_31`, `52_30`, `52_31` | 374 | 193 | 181 |
| total | | 994 | 485 | 509 |

Each record is a list of *cone lemmas* `S_i ⊄ P`, where `S_i` is a finite set of nontrivial elements
of `Γ^+` and `P` is any positive cone of a left order on `Γ^+`. Each lemma is proved by a short
derivation from earlier lemmas and products, and the last lemma has `S = ∅`.
- **Words.** All words lie in the radius-6 ball.
- **Size.** Each certificate has 4 to 71 lemmas (median 13) and 23 to 1148 steps (median 188). The
  file `certs.jsonl.gz` is 0.5 MB.

## Relation to the census theorem and to the survivor node

For these classes, this upgrades non-left-orderability of `Γ^+` from "two SAT solvers agree" to an
explicit certificate. Its check (`verify_lemmas.py`, about 60 lines) uses only the rewriting normal
form, Newman's critical pairs and one pass through the lemmas.

The three survivors of `bmw-44-sat-survivor-parity-kernels-not-left-orderable` are not among the
994. That node is resolved separately.

The quaternionic searches of w10-107 (in characteristics 2 and 3, and for `(5,3)`) are not needed for
these classes: each of them now has a direct certificate.
