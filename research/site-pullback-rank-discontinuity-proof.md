---
rg: 2
id: site-pullback-rank-discontinuity-proof
kind: route
title: Columns of an algebra-preserving invertible matrix are disjoint idempotent vectors; the all-ones perturbation makes every pairwise product nonzero
target: site-pullbacks-are-discontinuous-in-the-rank-metric
requires: []
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

## Why sufficient

Artifact Section 3, Proposition 3.1.
- **Formula.** `E(a)(e_i ⊗ e_j) = delta_ij a e_i - (a e_i) * (a e_j)`, so `rk E(a)` is the dimension of the span of
  these vectors.
- **Vanishing.** Idempotent entries and disjoint supports, together with invertibility, force a permutation matrix.
- **Jump.** For `a = I + J` the columns are `e_i + 1`. The pairwise products are `e_i + e_j + 1` and the diagonal
  defects are `2 e_i`. In odd characteristic or characteristic zero they span `F^n`. In characteristic two, with
  `n` even and `n >= 4`, they span the sum-zero hyperplane.
