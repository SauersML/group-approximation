---
rg: 2
id: fpbs-spectral-dt-certificate-bounds-connectivity-operator-proof
kind: route
title: Iterate the finite-volume DT exploration inequality as a positive-kernel Neumann series and use upper semicontinuity of the spectral radius
target: fpbs-spectral-dt-certificate-bounds-connectivity-operator
requires: []
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

The complete proof is in the artifact. The main theorems use no import.

1. **Lemma 2.1: finite-volume exploration.** Explore the cluster of `x`
   inside `xS ∩ Lambda`, and take the last exit edge of an open path. The
   independence of `{C = A}`, the exit edge, and the connection off `A` gives
   `tau^Lambda <= A_S + R tau^Lambda` entrywise, with
   `R = rho_Gamma(nu_{S,p})`.
2. **Theorem A.**
   * Iterate: `T^Lambda <= sum_{k<m} R^k A_S + R^m T^Lambda`.
   * The remainder is at most `|Lambda| ||R^m||`, which tends to 0.
   * Let `Lambda` increase to `Gamma`. Entrywise domination of nonnegative
     kernels dominates norms, and `||A_S|| <= |S|`.
3. **Corollary 3.1.** Coefficients are polynomials in `p` on a fixed finite
   support. `sp = inf_k ||a^k||^(1/k)` is upper semicontinuous, and it is
   monotone in `p` by entrywise monotonicity.
4. **Section 3.3.** `p_sDT <= p_{2->2}` is Theorem A. The lower bound
   `p_c <= p_sDT` uses `sp <= phi_p(S)` and the DT theorem. That theorem is
   already imported verbatim in
   `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md` Section 1, via
   `fpbs-l2-gap-class-closed-under-local-limits-proof`.
5. **Section 6.** Explicit spherical-function computations.
