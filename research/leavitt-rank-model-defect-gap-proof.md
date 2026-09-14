---
rg: 2
id: leavitt-rank-model-defect-gap-proof
kind: route
title: Pass to the fixed-point-free quotient, bound its displacement by four-generation, and bound the defect by compactness and corner locality
target: leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
requires:
  - two-root-identity-is-corner-local-for-leavitt-rank-models
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-four-generated
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

Artifact Section 2.

1. **Quotient (Lemma 2.1).**
   * `(1-f)sigma(g)f = 0`, so `sigma_W = (1-f) sigma (1-f)` is a homomorphism.
   * A vector `x` in `(1-f)M` fixed by `sigma_W` gives an additive cocycle `c(g) = f sigma(g) x`
     into the pointwise-fixed ideal `fM`. That is a homomorphism into an abelian group, so it
     vanishes by perfection, and `x = 0`.
   * `sigma_W` is trivial only if `sigma` lands in the abelian group `1 + fM(1-f)`, hence only if
     `sigma` is trivial.
   * Its cylinder defects are `(1-f) D_A`.
2. **Displacement (Lemma 2.2).** A fixed-point-free model fixes nothing. `Fix_r` is the intersection
   of the right annihilators of `sigma(g_i) - 1` over four generators, so
   `sum_i rk(sigma(g_i) - 1) >= 1`.
3. **Compactness (Lemma 2.3).** Suppose models with displacement at least `eta` had defects
   tending to `0`.
   * Finite-stage approximations over one field `Omega` give a limit homomorphism into a single rank
     ultraproduct.
   * Its `[1000]` corner product vanishes, so corner locality makes it trivial.
   * But its displacement is still at least `eta`, a contradiction.
4. **Gap (Theorem 2.4).**
   * Set `c_0 = c(1/4)`; by `V`-conjugacy it serves for every proper cylinder.
   * Upper bounds: `(1-f)N^A_12` is square-zero in the corner, and `D_A = D_A(1-f)`.
