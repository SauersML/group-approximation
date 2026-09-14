---
rg: 2
id: lef-groups-embed-via-two-generator-lef-envelope
kind: route
title: A finitely generated LEF group in the commutator subgroup of a 2-generator LEF group, then the lamplighter host
target: lef-groups-embed-in-simple-kazhdan-lef-groups
requires: [countable-lef-groups-embed-in-two-generator-lef-groups, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-universal-lef-host-a-2026-09-13.md
---

This is an alternative to the route through `rf-groups-lie-in-derived-subgroups-of-rf-groups` (quotient doubling plus Ore).

1. **Envelope.** `countable-lef-groups-embed-in-two-generator-lef-groups` gives an infinite 2-generator LEF group `Δ = ⟨a,b⟩` and `ι: Γ ↪ Δ` with `ι(γ_j) = w_j(a,b) = [b^(−2^(2j−1)) a b^(2^(2j−1)), b^(−4^j) a b^(4^j)]`.
   - Each `ι(γ_j)` is a commutator, so `ι(Γ) ≤ [Δ,Δ]`.
   - The same conclusion holds for the independent presentation in artifact §1 (`Sym(m)≀Z/2^(2n+3)`, positions `2^j`).
2. **Host.** `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` makes `U = EL_3(LC(2^Δ,F_2) ⋊ L)`, with `L = Z/2 ≀ Δ`, infinite, f.g., simple, Kazhdan and LEF. `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L]` in `U`, because
   `diag(x,x^(−1),1) diag(y,y^(−1),1) diag((yx)^(−1),yx,1) = diag(xyx^(−1)y^(−1),1,1)`
   and `diag(z,z^(−1),1) ∈ E_3` by Whitehead's lemma.
3. **Conclusion.** `ι(Γ) ≤ [Δ,Δ] ≤ [L,L] ↪ U`, so `Γ` is a subgroup of `U`. The converse holds because subgroups of LEF groups are LEF. □
