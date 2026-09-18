---
rg: 2
id: fpbs-spectral-dt-threshold-equals-l2-threshold-proof
kind: route
title: Dominate the ball boundary measure by the critical sphere operator and make it small with the trivial-kernel tail bootstrap
target: fpbs-spectral-dt-threshold-equals-l2-threshold
requires:
  - fpbs-spectral-dt-certificate-bounds-connectivity-operator
  - fpbs-sphere-fibre-operator-iff-critical-fibre-l2
artifacts:
  - research/artifacts/fpbs-spectral-dt-threshold-equals-p22-2026-09-17.md
---

The complete proof is in the artifact.

1. **Sphere support.** An edge leaving `B_R` starts on `S_R`, and
   `P_p(o <->_{B_R} u) <= tau_p(o,u)`. So
   `nu_{B_R,p} <= p (sigma_p 1_{S_R}) * a_D` entrywise, where `a_D` is the
   generator counting measure.
2. **Positive kernels.** Norms of nonnegative convolution kernels are monotone
   and submultiplicative, and `||a_D|| <= |D|`.
3. **Tail bootstrap.** Theorem A, "(b) implies (c)", of
   `research/artifacts/fpbs/docs/sphere-fibre-operator-is-critical-l2.md`, with
   `H = {1}`, is stated to work at every `p` with `N_p < infinity`. It gives
   `N(sigma_p 1_{|.| >= R}) <= e N_p exp(-R/(e N_p))`, and `N(sigma_p) = ||T_p||`
   by left invariance.
4. **Thresholds.** For `p < p_{2->2}`, a large ball certifies, so
   `p_sDT >= p_{2->2}`. The reverse inequality is Section 3.3 of the certificate
   artifact.
5. **Corollaries.**
   * `sp <= norm` and Corollary 3.3 of the certificate artifact.
   * `||T_{p_{2->2}}|| = infinity` (Hutchcroft arXiv:1804.10191, imported as (F5)
     in the sphere-fibre artifact).
   * The mass remark uses the DT theorem, imported verbatim in
     `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`.
