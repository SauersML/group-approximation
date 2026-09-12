---
rg: 2
id: toeplitz-pair-weyl-generation-proof
kind: route
title: Close the coefficient set of the generated root groups under permutation conjugation, sums and commutators
target: toeplitz-pair-and-weyl-elements-generate-jacobson-el3
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/fock-toeplitz-input-and-sofic-independence-2026-09-12.md
---

Artifact Section 3, Theorem 3.1.

1. **One coefficient set.** For the generated group `G'`, put `C_ij = {r : x_ij(r) in G'}`.
   * Each `C_ij` is additive, since `x_ij(a) x_ij(b) = x_ij(a+b)`.
   * Signed permutation matrices of the prime field lie in the generating set's `EL_3`, and conjugation by them permutes
     root groups: `pi x_ij(r) pi^(-1) = x_(pi(i) pi(j))(± r)`.
   * So all `C_ij` equal one set `C`.
2. **Products.** `[x_ij(a), x_jk(b)] = x_ik(ab)` for distinct `i, j, k`, so `C` is closed under products.
3. **Jacobson case.** `C` contains `1, s0, t0`, so `C ⊇ J`, and `G' = EL_3(J)`.
4. **Leavitt case.** With the constant root groups, `C ⊇ R_0 ∋ p = s0 t1 + s1 t0`.
   * `p s0 = s1` and `t0 p = t1`, so `C` contains `s0, s1, t0, t1` and hence all of `R`.
   * So `G' = EL_3(R) = R^x`, by `leavitt-gl-equals-el-and-perfect-unit-group`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 28.3 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
