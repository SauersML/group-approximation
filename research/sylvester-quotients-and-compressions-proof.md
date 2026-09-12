---
rg: 2
id: sylvester-quotients-and-compressions-proof
kind: route
title: Transport the Sylvester axioms through a two-sided ideal column or a commuting element
target: sylvester-rank-functions-descend-to-quotients-and-compressions
requires: []
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

## Why sufficient

* **Ideal quotients (artifact Lemma 1.1).** Two-sidedness of `J` gives, for every matrix `A`, a matrix `Y_A` with
  `X A = Y_A X`. So `rho(X AB) = rho(Y_A X B) <= rho(X B)`, while `rho(X AB) <= rho(X A)` is (S2). Block sums and
  upper triangular blocks pass through `X (x) I` by row permutations. Two generating columns dominate each other.
  `J = J^2` gives `X = Y (X X)`, hence `rho(X Z) = rho(X X Z)`.
* **Commuting compressions (artifact Lemma 1.2).** `A^k d_n = d_m A^k`, so `rho(A^k B^k d_p) = rho(A^k d_n B^k)`
  is bounded by `rho(A^k d_n)`; the other axioms are block computations.
* **Inequalities (artifact Section 1, Consequences).** Sylvester: `[[A, 0], [I, B]]` is equivalent to
  `[[0, -AB], [I, 0]]` and permutes to the upper triangular `[[B, I], [0, A]]`. Frobenius: `[[B, BC], [AB, 0]]` is
  equivalent to `[[B, 0], [0, -ABC]]` and permutes to `[[BC, B], [0, AB]]`. Stacking:
  `[A; B] = (A (+) B)[I; I]`.

Direct proof from the Sylvester axioms; no other node is used.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 26.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
