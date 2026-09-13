---
rg: 2
id: o2-multiplier-extension-k1-injective-iff-unitization-proof
kind: route
title: Proof of the O_2-multiplier extension criterion via the unitary fibration over O_2
target: o2-multiplier-extension-k1-injective-iff-unitization
requires: []
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
---

Full derivation in artifact section 3.

1. `A = I + C*(S_1,S_2)`, and `A/I` is a nonzero quotient of the simple algebra `O_2`, so `A/I ≅ O_2`.
   `A` is properly infinite because it contains `S_1, S_2`.
2. (Fibration) Choose a Bartle--Graves continuous right inverse `σ` of `A_sa → (A/I)_sa`, normalized
   by `σ(0)=0`. Then `w ↦ exp(iσ(-i Log w))` is a local section of `U_0(A) → U_0(O_2)` near 1. So this
   map is a principal bundle with fibre `G = U_0(A) ∩ π^{-1}(1)`, and by Hurewicz it is a Serre
   fibration. Exactness gives `π_1(U(O_2)) → π_0(G) → *`.
3. `π_1(U(O_2)) = K_0(O_2) = 0`. This is Jiang, arXiv:math/9707228, abstract "π_i(U(A)) = K_{i-1}(A)"
   for unital Z-stable A. `O_2` is Z-stable, as a strongly self-absorbing algebra (Toms--Winter; Winter).
   So `G` is path-connected, and `U(Ĩ) ∩ U_0(A) ⊆ U_0(Ĩ)` after normalizing the scalar part.
4. If `A` is K1-injective and `u ∈ U(Ĩ)` has `[u] = 0` in `K_1(I)`, then `[u] = 0` in `K_1(A)`. So
   `u ∈ U_0(A)`, and `u ∈ U_0(Ĩ)` by step 3.
5. If `Ĩ` is K1-injective and `u ∈ U(A)` has `[u] = 0`, then `π(u) ∈ U(O_2) = U_0(O_2)` (Cuntz), so it
   lifts to some `w ∈ U_0(A)`. The unitary `y = uw^*` lies in `1+I`, and `[y] = 0` in `K_1(A)`. Since
   `K_0(O_2) = 0`, `K_1(I) → K_1(A)` is injective, so `[y] = 0` in `K_1(I)`. Hence
   `y ∈ U_0(Ĩ) ⊆ U_0(A)` and `u ∈ U_0(A)`.
