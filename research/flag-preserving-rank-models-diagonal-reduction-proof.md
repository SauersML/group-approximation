---
rg: 2
id: flag-preserving-rank-models-diagonal-reduction-proof
kind: route
title: Diagonal compression is multiplicative and rank-contracting on block triangular matrices, and the remainder is unipotent
target: flag-preserving-rank-models-of-el3-reduce-to-their-diagonal
requires:
  - unipotent-valued-rank-models-of-el3-are-trivial
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Artifact Section 4.2.

1. **Lemma 6.** For block upper triangular matrices, `D(xy) = D(x) D(y)` at any number of blocks.
   `rk(D(x)) <= rk(x)`: invertible maximal submatrices of the diagonal blocks assemble into a
   block triangular invertible submatrix of `x`.
2. **Proposition 7.** Rank contraction makes `sigma_D` independent of the triangular
   representative, and multiplicativity makes it a homomorphism. `D_i(g_i)^(-1) g_i` is block
   unitriangular, hence unipotent, and it is within `rk(D_i(g_i) - 1)` of `g_i`.
3. **Reduction.** If `sigma_D` is trivial, `sigma` is unipotent-valued, so it is trivial by
   `unipotent-valued-rank-models-of-el3-are-trivial`. Conversely rank contraction gives
   `rk(sigma_D(g) - 1) <= rk(sigma(g) - 1)`.
4. **Special cases.**
   * Unitriangular representatives are unipotent.
   * One-dimensional blocks make `sigma_D` commutative, and `EL_3(R)` is perfect.
   * Bounded blocks: failing blocks carry dimension `o(n_i)`, while blocks nontrivial at a fixed
     `g_0` carry dimension at least `c n_i`. Choose exact blocks on growing finite sets and take
     an algebraic ultraproduct of `GL_(d')`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 38 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`. The implicit step that triangular representatives can be taken invertible (perturb singular diagonal blocks by their nullity, total rank `o(n_i)`) is supplied there.*
