---
rg: 2
id: rank-modelled-simple-rings-give-linear-sofic-projective-el-proof
kind: route
title: Amplify the ring model to matrices, then pass through the adjoint and bound commutants
target: rank-modelled-simple-rings-give-linear-sofic-projective-el
requires: []
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

This is Proposition 3 of the artifact.

1. **G.** `Psi` is injective (simple `R`, unital map). It induces an injective homomorphism
   `GL_m(R) -> M_m(M)^x`. Here `M_m(M)` is again a rank ultraproduct, and its unit group is the rank
   ultraproduct of the `GL_(m N_i)(k)`.
2. **The adjoint.** `Ad(A) = A ⊗ (A^(-1))^T` is multiplicative and trivial on scalars. Since
   `rk(A^(-1) - B^(-1)) = rk(A - B)`,
   `rk(Ad A - Ad B) <= N rk(A - B) + N rk(A^(-1) - B^(-1)) = 2N rk(A - B)`.
   So it induces a homomorphism of rank ultraproducts that kills `k^x`, and `Ad o Psi` factors
   through `S`.
3. **Commutants.** `rk(Ad A - 1) = N^2 - dim C(A)`. Over the algebraic closure,
   `dim C(A) = sum_λ sum_(i,j) min(p_i^λ, p_j^λ)`, where `(p_i^λ)` is the Jordan partition at `λ`.
   This is at most `sum_λ d_λ k_λ`, with `d_λ` the generalized multiplicity and
   `k_λ = dim ker(A - λ)`, hence at most `N max_λ k_λ`. So
   `rk(Ad A - 1)/N^2 >= min_λ rk(A - λ)/N`.
4. **Separation.** Let `g ∈ G \ Z` and let `A_i` represent `Psi(g)`.
   - For each of the finitely many `λ ∈ k`, `g - λ 1_m != 0` in `M_m(R)`, so
     `lim_omega rk(A_i - λ)/(m N_i) > 0`.
   - For `λ ∉ k`, `A_i` has entries in `k`, so Galois-conjugate eigenvalues have kernels of equal
     dimension. That dimension is at most `m N_i / 2`.

   So `Ad(A_i)` stays a positive normalized rank from `1`, and `S` embeds.
