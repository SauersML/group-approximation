---
rg: 2
id: lamplighter-host-elementary-groups-are-character-rigid
kind: claim
title: For every infinite group Δ, every character of EL_n over the lamplighter crossed product LC(F_2^Δ,F_2) ⋊ (F_2 ≀ Δ) is c·1 + (1−c)δ_e
distinct_from:
  subshift-elementary-groups-are-character-rigid: that is the Z-subshift case, proved with Kakutani–Rokhlin tower unit groups of a free minimal Z-action; this is the non-free lamplighter action of any infinite Δ, where towers are replaced by the UHF subalgebra LC(Ω,F_2) ⋊ ⊕_Δ F_2 and the tower algebras are conjugated into it through the Λ-invariant Bernoulli measure.
artifacts:
  - research/artifacts/sk-lamplighter-characters-plan-2026-09-14.md
  - research/artifacts/sk-lamplighter-characters-2026-09-14-part1.md
  - research/artifacts/sk-lamplighter-characters-2026-09-14-part2.md
---

**ESTABLISHED (unreviewed, lane sk-lamplighter-characters, 2026-09-14)** by route `lamplighter-host-elementary-groups-character-rigid-proof`.

Let `Δ` be an infinite countable group, `Ω = F_2^Δ`, and `Λ = F_2 ≀ Δ` acting by `x ↦ δx + f`. Let `R_Δ = LC(Ω,F_2) ⋊ Λ` and `n ≥ 3`. Then every character (normalized positive definite class function) of `G_Δ = EL_n(R_Δ)` equals `c·1 + (1−c)δ_e` for some `c ∈ [0,1]`.

The proof uses neither amenability nor LEF nor finite generation of `Δ`, nor property (T). The only import is Larsen–Tiep Theorem A (arXiv:2403.09046v1), used as in the Z-case.

Consequences, for the paper's hosts (Corollaries 3–4):
- `L(G_Δ)` is the only II_1 factor representation with finite trace. `C*(G_Δ)` has exactly two extreme traces.
- `IRS(G_Δ)` is trivial, since `G_Δ` is infinite and simple.
- By `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, `G_Δ` is sofic iff it has one almost action with fixed-point proportion bounded away from 1. This is T3 of the sofic-host question `sofic-groups-embed-in-simple-kazhdan-sofic-groups`.

Firewalls: finite `Δ`; `F_q` with `q > 2`; topological full groups (Dudko–Medynets characters). See artifact part 2 §6.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part9.md`):** re-derived L1 (UHF matrix units from u_κ e_{[w]} = e_{[w+κ]}u_κ, support growth under x ↦ x⊗I); L2 (Larsen–Tiep decay, α_h = 1/N_m); L3 (d_δ normalizes G, all six root positions of u_δ^{±1}, subring argument); L4 (p_L = p_{A′} = p_{dLd⁻¹} by faithful trace, central); L5 (nontriviality inherited by clopen subsets; the conjugating unit w with ww̄ = 1 from aV_k ⊆ U; the commuting-tower Bessel step); §4 c_M = c via A‴ ⊆ L ∩ M. Wording note W1: L5 is applied to the unit built from g.
