---
rg: 2
id: c-linear-sofic-group-carries-nontrivial-rigid-defect
kind: claim
title: Some complex-linear sofic group contains an infranormal Kazhdan pair with nontrivial rigid compression defect
distinct_from:
  c-linear-sofic-groups-kill-rigid-compression-defects: that is the criterion; this is its negation, carried separately because both directions have live consequences.
  linear-sofic-nonsofic-group: that asks for any complex-linear sofic nonsofic group; this asks for one of a specific kind, which is automatically nonsofic by the Hamming defect criterion.
  kun-thom-wreath-linear-sofic: that asks for rank models of one specific wreath, which would witness this; this asks for any complex-linear sofic group with a nontrivial rigid defect.
  hyperlinear-group-carries-nontrivial-rigid-defect: that is the same negation in the Hilbert--Schmidt row; this is the rank row over C.
refuted_by:
  - c-linear-sofic-groups-kill-rigid-compression-defects
artifacts:
  - research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md
---

**OPEN.** There are a countable group `H`, linear sofic over `C`, and
`Gamma <= G <= H`, with:

- `Gamma` and `G` Kazhdan, and `Gamma` infranormal in `G`;
- `g in G`, `z in C_H(Gamma)` and `gamma in Gamma` with `[g z g^-1, gamma] != 1`.

By [[rigid-compression-defect-normalization-dichotomy]] it suffices to find an infranormal
Kazhdan pair `Gamma <= G` and a homomorphism
`sigma : G -> U = prod_omega GL_n(C) / d_rank`, not necessarily injective, such that
`sigma(G)` does not normalize `C_U(sigma(Gamma))`. Then `<sigma(G), z>` is a witness.

## Attempts

- **Algebraic models of localization pairs normalize.**
  - Let `A_+ <= A` be commutative rings with `A = A_+[s_1^-1, ..., s_k^-1]`, `r >= 2`, and
    `Gamma = EL_r(A_+) <= G = EL_r(A) x| Lambda`, where `Lambda` normalizes `EL_r(A)`.
  - Suppose `sigma(x_ij(a)) = 1 + E_ij (x) phi(a)` on `EL_r(A)`, for a unital ring
    homomorphism `phi` into a rank ultraproduct.
  - An element commuting with `sigma(Gamma)` commutes with `E_ij (x) phi(a)` for
    `a in A_+`, hence with the diagonal units `1 (x) phi(s_l)`, and hence with their
    inverses. So it commutes with `sigma(EL_r(A))`.
  - Then `C_U(sigma(Gamma)) = C_U(sigma(EL_r(A)))`, which `sigma(G)` normalizes because
    `EL_r(A)` is normal in `G`.
  - For integral Laurent pairs `EL_r(Z[x^±]) x| SL_d(Z)` this covers ultraproducts of
    the representations on `C[(Z/n)^d]^r`, with `SL_d(Z)` permuting monomials. For the
    Kun--Thom Theorem E pair over `F_q` there are no algebraic models over `C` at all,
    because a ring of characteristic `p` has no unital ring map into a nonzero `C`-algebra.
    So a witness needs non-algebraic models.
- **Room for a witness.** Over every field, images of Kazhdan groups in rank
  ultraproducts can have diffuse relative commutants
  ([[kazhdan-rank-rounding-fails-over-every-field]]). A witness needs such a commutant
  that a compressor strictly compresses by conjugation. No example is known.
- **The wreath.** [[kun-thom-wreath-linear-sofic]] would give a witness directly.
  Glebsky's permanence theorem has no known rank-metric analogue.
