---
rg: 2
id: sofic-lamplighter-bernoulli-crossed-products-have-rank-models
kind: claim
title: For every finitely generated infinite sofic group Δ, the crossed product of the lamplighter action of Z/2 ≀ Δ on 2^Δ embeds unitally in a rank ultraproduct over any field
distinct_from:
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that gives exact partial models, hence LEF, for LEF acting groups; this gives rank-metric models for sofic acting groups, where exact models need not exist.
  amenable-minimal-crossed-products-have-faithful-rank-models: that truncates orbits to Følner sets and needs amenability; this counts over sofic approximations using the Bernoulli measure, with no amenability.
artifacts:
  - research/artifacts/sk-measured-subshift-lamplighter-rank-envelopes-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be a finitely generated infinite sofic group.
- `Δ` acts on `Z = 2^Δ` by `(δx)(h) = x(δ^(-1)h)`, and `a` flips the coordinate at `e`, so `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ`.
- `k` is any field, and `R = LC(Z,k) ⋊ L`.

Then there are unital linear maps `Φ_k : R → M_(N_k)(k)` with `N_k → ∞` such that:
1. `rank(Φ_k(rs) − Φ_k(r)Φ_k(s)) = o(N_k)` for all `r, s ∈ R`;
2. for every `r ≠ 0` there is a nonempty clopen `U ⊆ Z` with `rank Φ_k(r) ≥ ν(U)N_k − o(N_k)`, where `ν` is the
   uniform Bernoulli measure.

So `R` embeds unitally and injectively in `∏_ω M_(N_k)(k)` modulo rank-null sequences.

**Mechanism.**
- The models live on `k[2^(V_k) × V_k]` for a sofic approximation `σ_k : Δ → Sym(V_k)`.
- Generators of `Δ` move the base point, `a` flips the colour at the base point, and a locally constant function reads
  the colouring around the base point.
- Multiplicativity fails only over bad base points.
- Faithfulness comes from exact counting over all colourings, together with a clopen set `U` separated from its
  translates, which exists because the action is topologically free.

Route: `sofic-lamplighter-bernoulli-rank-models-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS; every step re-derived (see the artifact).
