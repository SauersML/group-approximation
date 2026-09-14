---
rg: 2
id: kazhdan-marked-limits-eventually-uniform-expanders-proof
kind: route
title: Openness of (T) makes large approximants quotients of one Kazhdan group, and the Kazhdan constant bounds the gap
target: kazhdan-marked-limits-eventually-uniform-expanders
requires: [fpbs-shalom-property-t-is-open]
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
---

Full proof in the artifact §1.
- **Openness.** Openness of (T) gives a finite `R_0 ⊆ ker(F(T) → G)` with `Γ_0 = F(T)/⟨⟨R_0⟩⟩` Kazhdan, with Kazhdan constant `κ` for `T`.
- **Quotients.** Marked convergence makes every `ρ ∈ R_0` trivial in `Q_k` for large `k`, so `Γ_0 → Q_k` is onto.
- **Gap.** `ℓ^2_0(Q_k)` has no `Γ_0`-invariant vectors, so `max_t ‖λ(t)ξ − ξ‖ ≥ κ` for unit `ξ`. Then
  `⟨(I − M)ξ, ξ⟩ = (2|T^±|)^(-1) Σ_t ‖λ(t)ξ − ξ‖^2 ≥ κ^2/(2|T^±|)`.
- **Size.** Balls of the infinite group `G` inject into `Q_k`, so `|Q_k| → ∞`. The discrete Cheeger inequality gives uniform expansion.
