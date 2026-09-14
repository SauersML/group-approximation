---
rg: 2
id: orbit-bijective-cocycle-gives-z-action-groupoid-proof
kind: route
title: Proof - the level set c = 1 is a full bisection generating the groupoid
target: orbit-bijective-cocycle-gives-z-action-groupoid
requires: []
artifacts: [research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md]
---
Direct proof, with details in the artifact §3.

- **B_n = c^{-1}(n) is clopen.** c is continuous and Z is discrete.
- **B_n → G^(0) is a homeomorphism.** s|_{B_n} is a bijection onto G^(0) by the fibre hypothesis, and it is continuous
  and open because G is étale. So B_n is compact.
- **r|_{B_1} is injective.** If γ, γ′ ∈ B_1 have r(γ) = r(γ′), then δ = γ^{-1}γ′ ∈ s^{-1}(s(γ′)) has c(δ) = 0. By the fibre
  hypothesis δ is a unit, so γ = γ′.
- **r|_{B_1} is onto.** For a unit y, the unique η ∈ s^{-1}(y) with c(η) = −1 has η^{-1} ∈ B_1 with range y.
- **T is a homeomorphism.** B_1 is a full compact open bisection, so T = r∘(s|_{B_1})^{-1} is one.
- **Ranges.** By induction on |n|, the unique arrow of s^{-1}(x) with c = n is a product of arrows of B_1^{±1}, and
  its range is T^n x.
- **The isomorphism.** Φ(γ) = (c(γ), s(γ)) is a groupoid homomorphism to Z ⋉_T G^(0), bijective by the fibre hypothesis,
  and continuous. Its inverse (n,x) ↦ (s|_{B_n})^{-1}(x) is continuous.
- **Isotropy.** If γ ∈ G_x^x then T^{c(γ)} x = x, and c is injective on the isotropy group. So the isotropy is a subgroup
  of Z. ∎
