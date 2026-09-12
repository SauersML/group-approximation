---
rg: 2
id: ternary-root-element-torus-normal-form-proof
kind: route
title: Keep only the weight components the torus allows, then compare conjugation by a reflection with inversion
target: ternary-rank-model-root-element-torus-normal-form
requires: [leavitt-gl-equals-el-and-perfect-unit-group, anti-central-rank-models-see-haar-measure-on-signed-diagonal]
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

## Why sufficient

- **Allowed components.** `τ_11` and `τ_0 τ_10` commute with `x_12(1)`, so `N` has only weight-preserving
  components `D` and components `A` flipping the first two signs.
- **The reflection.** `τ_0` conjugates `x_12(1)` to `x_12(−1)`. In characteristic three `N^3 = 0` and
  `(1 + N)^−1 − 1 = −N + N^2`, while conjugation by `σ(τ_0)` fixes `D` and negates `A`. So `D = −N^2`.
- **Squares.** `N^2` preserves weights, so `N^2 = D^2 + A^2 = A^2` (using `D^2 = N^4 = 0`), and the flipping
  part `DA + AD = −2A^3` vanishes, giving `A^3 = 0`.
- **Weights.** In the anti-central case the Haar law at the three-leaf code puts rank `1/4` on each odd sign
  pattern and nothing on even ones.

Details: artifact Section 5.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 54 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. The assigned verifier remains `w3-vf-linear`.*

*Verification by `w3-vf-linear` (2026-09-12), Section 15.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: the allowed components from τ_11 and τ_0τ_10, D = −N² by τ_0-conjugation with N³ = 0, and then N = A − A², A³ = 0.*
