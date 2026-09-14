---
rg: 2
id: shift-unit-of-subshift-crossed-product-is-not-elementary-proof
kind: route
title: The half-line compression index is a homomorphism on GL_n that kills elementary matrices and gives the shift index -1
target: shift-unit-of-subshift-crossed-product-is-not-elementary
requires: []
artifacts:
  - research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md
---

Artifact §1, Proposition 1. Direct proof.

1. **Representation.** Fix `x ∈ X`. `R` acts on `V = ⊕_(t∈Z) k δ_t` by `uδ_t = δ_(t+1)` and `fδ_t = f(T^t x)δ_t`.
   This respects `ufu^(-1) = f∘T^(-1)`. `M_n(R)` acts on `V^n` with bounded propagation. Let `P` project onto the span
   of the `δ_t`, `t ≥ 0`, in each coordinate. Then `Pa(1−P)` and `(1−P)aP` have finite rank for `a ∈ M_n(R)`.
2. **Index.**
   - For `a ∈ GL_n(R)`, `(Pa^(-1)P)(PaP) = P − Pa^(-1)(1−P)aP` and symmetrically. So `PaP` is invertible modulo
     finite rank on `PV^n`, with finite-dimensional kernel and cokernel.
   - Put `ind(a) = dim ker PaP − dim coker PaP`.
   - `PabP = PaP·PbP + Pa(1−P)bP`. Over a field the index is additive for composition and unchanged by finite-rank
     perturbations, so `ind : GL_n(R) -> Z` is a homomorphism.
3. **Elementary matrices.** For `i ≠ j`, `P e_ij(r) P = P + N` with `N = P rE_ij P` and
   `N^2 = P rE_ij P rE_ij P = 0`, because `E_ij E_ij = 0`. So `P e_ij(r) P` is invertible with inverse `P − N`, and
   `ind(e_ij(r)) = 0`. Hence `ind` vanishes on `E_n(R)`.
4. **The shift.** `P diag(u,1,…,1) P` is the unilateral shift in the first coordinate and the identity elsewhere.
   It is injective, with cokernel `kδ_0`, so `ind = −1 ≠ 0`. ∎
