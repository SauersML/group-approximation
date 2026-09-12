---
rg: 2
id: flag-preserving-rank-models-of-el3-reduce-to-their-diagonal
kind: claim
title: A rank model of EL_3 preserving flags of any length is trivial exactly when its block-diagonal model is
distinct_from:
  filtered-matrix-unit-rank-models-of-simple-el3-are-trivial: that needs a finite flag in M whose graded pieces are matrix-unit, transposed or trivial, and a simple non-directly-finite R; this allows flags of unbounded length at finite stages, any ring of characteristic p and any field, and reduces triviality to the block-diagonal model.
  el3-rank-models-factor-through-ring-rank-models: that asserts every rank model is trivial; this shows only that the triangular part of a flag-preserving model carries nothing, kills unitriangular, triangularizable and bounded-block models, and leaves diffuse block-diagonal models to the general claim.
  unipotent-valued-rank-models-of-el3-are-trivial: that is the unipotent case alone; this builds the diagonal model of any flag-preserving model, for any group, and reduces to that case.
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Let `M = prod_omega M_(n_i)(k) / d_omega` over any field `k`, `Gamma` a group and
`sigma : Gamma -> M^x` a homomorphism. Suppose that for ω-almost every `i` there is a
decomposition `k^(n_i) = W_(i,1) (+) ... (+) W_(i,m_i)`, with `m_i` arbitrary, such that every
`sigma(g)` has a block upper triangular representative `g_i`. Put
`D_i(x) = sum_t pi_(i,t) x pi_(i,t)`.

1. **Diagonal model (any group).** `sigma_D(g) = [D_i(g_i)]` is a well-defined homomorphism
   `Gamma -> M^x`, with `rk(sigma_D(g) - 1) <= rk(sigma(g) - 1)`, and `sigma_D(g)^(-1) sigma(g)`
   is unipotent. The key inequality is `rk(D(x)) <= rk(x)` for block triangular `x`.
2. **Reduction.** If `Gamma = EL_3(R)` with `R` unital and `p 1 = 0`, then `sigma` is trivial
   exactly when `sigma_D` is trivial.
3. **Unitriangular models.** If every `sigma(g)` is within rank-null error of a unitriangular
   matrix, `sigma` is trivial. The flag length at finite stages may be unbounded, with pieces of
   normalized rank tending to 0.
4. **Triangularizable models.** If every `W_(i,t)` has dimension 1, `sigma` is trivial.
5. **Bounded blocks.** If every `W_(i,t)` has dimension at most `d` and `sigma` is nontrivial,
   then `EL_3(R)` has a nontrivial homomorphism into `GL_(d')(K)` for some `d' <= d` and some
   ultrapower `K` of `k`.

What survives: diagonal models with blocks of unbounded dimension and normalized rank tending to
0. These are general rank models on smaller blocks, so the diffuse-flag case reduces to the
general claim and is not an independent obstacle (artifact Section 4.3).

**ESTABLISHED** by `flag-preserving-rank-models-diagonal-reduction-proof` (artifact Section 4.2,
Lemma 6, Proposition 7 and Theorem 8).
