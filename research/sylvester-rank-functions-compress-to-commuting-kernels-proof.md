---
rg: 2
id: sylvester-rank-functions-compress-to-commuting-kernels-proof
kind: route
title: Check the axioms on stacks under P, getting the left-factor bound from submodularity, and shear a diagonal for the count
target: sylvester-rank-functions-compress-to-commuting-kernels
requires:
  - sylvester-rank-functions-are-submodular-on-stacked-rows
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

## Why sufficient

* **Part 1 (artifact Lemma 3.1).**
  - `rho([P; 1]) = 1` gives `sigma(1) = 1`.
  - Direct sums and triangular blocks under `P_n` are row permutations of direct sums and triangular blocks of
    stacks. This gives (S3) and (S4).
  - Right factor: `[P_p; A B] = diag(I_p, A) [P_p; B]`.
  - Left factor: submodularity for `A' = [A, 0]`, `B' = [P_n, 0]`, `C' = [[I_n, -B], [0, P_p]]`.
    - Since `P_n B = B P_p`, row operations delete `B'` against `C'`.
    - So `rho([B'; C']) = n + p rho(P)` and `rho([A'; B'; C']) = n + rho([P_p; A B])`.
    - Also `rho([A'; B']) = rho([P_n; A])` and `rho(B') = n rho(P)`.
* **Part 2 (artifact Lemma 3.2).** `diag(P, T) [[1, 0], [1, 1]]` has the rows `[P, 0]` and `[T, T]`. Adding
  `T·(row 1) - P·(row 2)` to a zero row gives `[0, -PT]`, and (S4) on `[[ [P; T], [0; T] ], [0, -PT]]` gives the
  count.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 39.3 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. The row operation that deletes `B'` uses only `P_n B = B P_p`, both ranks in the left-factor step check, and the count is one (S4) step after `T·(row 1) - P·(row 2)`.*
