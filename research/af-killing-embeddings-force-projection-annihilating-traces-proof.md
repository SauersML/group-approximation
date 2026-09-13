---
rg: 2
id: af-killing-embeddings-force-projection-annihilating-traces-proof
kind: route
title: Pull back a corner trace from the AF target, extended by infinity, and use injectivity of K_0 of AF ideals
target: af-killing-embeddings-force-projection-annihilating-traces
requires: []
artifacts:
  - research/artifacts/bk-af-killing-projection-traces-2026-09-13.md
---

Theorem A in §1 of the artifact.

0. Replace `B` by a separable AF subalgebra containing `φ(A)` and the partial
   isometries witnessing `φ_*(G) = 0`.  `G` is countable because `A` is
   separable.
1. `Q = φ_n(P) ≠ 0`, and `J_Q` is the ideal it generates.  The unital AF corner
   `Q M_n(B) Q` has a tracial state `t`.
2. Extend `t` to a densely finite trace `ρ` on `M_n(J_Q)` (Brown's stable
   isomorphism), and put `σ_n = ρ^∞ ∘ φ_n = Tr ⊗ σ`.  Then `σ(P) = 1`.
3. `φ(I_σ) ⊆ J_Q` and `σ^ = ρ^ ∘ (φ|)_*`.
4. For `x ∈ ι_σ^{-1}(G)`, the image `(φ|)_* x` maps to `φ_*(ι_σ x) = 0` in
   `K_0(B)`, and `K_0(J_Q) -> K_0(B)` is injective because `K_1(B/J_Q) = 0`.
   So `σ^(x) = 0`.
