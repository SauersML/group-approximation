---
rg: 2
id: matrix-unit-rank-models-extract-ring-rank-models-proof
kind: route
title: Propagate block support to every root, read off the corner ring homomorphism, and lift the corner idempotent
target: matrix-unit-rank-models-extract-ring-rank-models
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-two-root-identities-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

Complete proof: artifact Section 2.

- **Characteristic two.** [RR] Proposition 6 gives `n_ij(a) = C(a) E_ij` with `C` a unital ring
  homomorphism into `p_1 M p_1`.
- **Odd characteristic.** [RR] Proposition 8 gives block support. Then additivity,
  `[1+X, 1+Y] = 1 + XY` and `C(a) = psi_12(a) u_21` give the ring homomorphism, as computed in
  [RR] Corollary 9 before its simplicity step.
- **The corner is a rank ultraproduct.** Represent `p_1` by near-idempotent matrices, replace
  them by idempotents within rank `2 rk(A^2 - A)` (Fitting decomposition), and identify the
  corners with `M_(r_i)(k)`.
- **The trivial case.** If `p_1 = 0`, every `u_ij` vanishes. The normal closure of `x_kj(1)`
  contains `[x_ik(a), x_kj(1)] = x_ij(a)` for every `a`, so `sigma` is trivial.

[RR] = `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 35 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
