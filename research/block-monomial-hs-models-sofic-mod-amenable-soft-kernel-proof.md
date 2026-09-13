---
rg: 2
id: block-monomial-hs-models-sofic-mod-amenable-soft-kernel-proof
kind: route
title: Compare HS with Hamming on block-monomials, then read the soft kernel inside a PI tracial ultraproduct
target: block-monomial-hs-models-sofic-mod-amenable-soft-kernel
requires: []
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

Complete proof in the artifact, sections 2 to 4.  In outline:

*Hamming comparison.*  For `M = (u; sigma)` and `M' = (u'; sigma')`, the
columns `i` with `sigma(i) != sigma'(i)` send each `e_i ⊗ v` to orthogonal
unit vectors.  So `||M - M'||_2^2 >= 2 d_H(sigma, sigma')`, and
`||M - (u; id)||_2^2 = 2 d_H(sigma, id)` exactly.  Hence `pi : (u; sigma) |-> sigma`
induces a homomorphism of metric ultraproducts, and `psi = pi_omega ∘ rho` is
a homomorphism.  `G/A ≅ psi(G)` is a countable subgroup of a metric
ultraproduct of symmetric groups with Hamming distance, which is the
definition of soficity (Pestov, arXiv:0804.3968, Definition 3.1).

*Soft kernel.*  For `a in A` the block-diagonal part `(u_m(a); id)`
represents `rho(a)`, by the exact identity above.  So `rho|_A` lands in the
unitary group of the tracial ultraproduct
`𝔄 = prod_omega (ℓ^∞_(n_m) ⊗ M_k)`, a finite von Neumann algebra satisfying
the Amitsur--Levitzki identity `S_(2k)` coordinatewise, hence in the limit.
Regularity pulls the trace back to the regular trace, so the generated von
Neumann algebra is `L(A)`, and `L(A)` satisfies `S_(2k)`.  A `II_1` summand
would contain unital `M_m` for every `m`, on which `S_(2k)` does not vanish once
`m > k`.  So `L(A)` is type I, hence injective, so `A` is amenable.  For `k = 1`,
`𝔄` is commutative and injectivity of `rho` gives `A` abelian.

*Corollary.*  The soft kernel is an amenable (resp. abelian) normal subgroup.
If the amenable radical is trivial then `A = 1`, and `G = G/A` is sofic.
Conversely, sofic approximations are permutation matrices with `k = 1`.
