---
rg: 2
id: ring-rank-approximability-from-leavitt-el3-triviality
kind: route
title: Trivial EL_3 rank models make both sides of the ring-approximability equivalence false, so it holds
target: leavitt-unit-linear-soficity-is-ring-rank-approximability
requires:
  - leavitt-el3-rank-models-over-finite-fields-are-trivial
  - toeplitz-isometry-defects-have-total-rank-at-least-one
artifacts:
  - research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md
---

Let `K` be a finite field of characteristic `p` and `R = L_K(1,2)`.

- **The group side is false.**
  - By `leavitt-el3-rank-models-over-finite-fields-are-trivial` with `n = 2`, every homomorphism
    `EL_3(R) -> M^x` into a characteristic-`p` rank ultraproduct is trivial.
  - `R ~= M_3(R)` gives `EL_3(R) <= GL_3(R) ~= R^x`, and `EL_3(R)` is infinite.
  - An `F_p`-linear sofic approximation of `R^x` would restrict to `EL_3(R)` and give a nontrivial
    homomorphism of that kind. So `R^x` is not `F_p`-linear sofic.
- **The ring side is false.** This is `toeplitz-isometry-defects-have-total-rank-at-least-one` (artifact
  Corollary 4).
- **Conclusion.** Both sides of `leavitt-unit-linear-soficity-is-ring-rank-approximability` are false,
  so the equivalence holds.

This route is the partner of `ring-rank-approximability-forces-non-linear-soficity`. Together they show
the Plan 2 claim is exactly as hard as the payoff and adds no intermediate step.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 4.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
