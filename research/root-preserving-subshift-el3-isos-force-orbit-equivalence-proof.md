---
rg: 2
id: root-preserving-subshift-el3-isos-force-orbit-equivalence-proof
kind: route
title: Coordinatize with the elementary relations, then apply the ring-to-dynamics theorem
target: root-preserving-subshift-el3-isos-force-orbit-equivalence
requires:
  - root-preserving-el3-isomorphisms-give-ring-isomorphisms
  - minimal-subshift-algebra-is-simple-lef-ring
  - cantor-crossed-product-matrix-ring-iso-forces-soe
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
---

**`R_Y` is directly finite.** By `minimal-subshift-algebra-is-simple-lef-ring`, `R_Y` is a LEF ring, so it embeds
unitally in an ultraproduct `∏_ω M_{N_ℓ}(F_2)` of finite matrix rings. Each `M_N(F_2)` is directly finite, and
`∀x∀y(xy = 1 → yx = 1)` is a first-order sentence, so it holds in the ultraproduct and passes to unital subrings.
This is exactly the finite-model theorem of the manuscript, used as a ring statement.

**`R_Y` has an anti-automorphism.** `τ(Σ_j f_j u^j) = Σ_j u^{-j} f_j` is additive and bijective, and
`τ(fu^i · gu^j) = τ(f (g∘T^{-i}) u^{i+j}) = u^{-i-j} f (g∘T^{-i}) = (u^{-j}g)(u^{-i}f) = τ(gu^j)τ(fu^i)`. So the
graph automorphism `g ↦ (τ(g)^t)^{-1}` of `EL_3(R_Y)` exists, and by the hexagon paragraph of
`root-preserving-el3-isomorphisms-give-ring-isomorphisms-proof` the labels of the six root subgroups can be matched
after composing `α` with it and with conjugation by a permutation matrix.

**Coordinatization.** `root-preserving-el3-isomorphisms-give-ring-isomorphisms` now applies with `R = R_X`,
`S = R_Y`, and gives a ring isomorphism `ψ: R_X → R_Y`.

**Dynamics.** `cantor-crossed-product-matrix-ring-iso-forces-soe` with `m = 1` turns a ring isomorphism
`LC(X,F_2) ⋊ Z ≅ LC(Y,F_2) ⋊ Z` into strong orbit equivalence of `(X,T)` and `(Y,S)`. ∎
