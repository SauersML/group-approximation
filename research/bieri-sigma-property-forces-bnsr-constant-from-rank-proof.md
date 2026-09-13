---
rg: 2
id: bieri-sigma-property-forces-bnsr-constant-from-rank-proof
kind: route
title: "Conic Caratheodory bounds the Bieri Sigma-property chain by the rank"
target: bieri-sigma-property-forces-bnsr-constant-from-rank
requires: []
---

Write `A = Σ^1(G)^c ⊆ S(G) = (Hom(G,R) \ {0})/R_{>0}` and `V = Hom(G,R) ≅ R^r`.

**Step 1 (conic Carathéodory).** Let `x ∈ V \ {0}` be a nonnegative combination
`x = Σ_{t∈T} λ_t a_t` of representatives `a_t` of a finite set `T ⊆ A`, with all
`λ_t > 0`. Then `x` is a nonnegative combination of a linearly independent
subfamily `{a_t : t ∈ T'}`, `T' ⊆ T`, so `|T'| ≤ r`. Standard proof: if the `a_t`
are dependent, choose `μ ≠ 0` with `Σ μ_t a_t = 0` and some `μ_t > 0`. Replace
`λ` by `λ − εμ`, where `ε = min{λ_t/μ_t : μ_t > 0}`. This keeps every coefficient
nonnegative, kills at least one, and leaves the sum unchanged. Iterate.

**Step 2.** A subset of a non-antipodal set is non-antipodal. So Step 1 shows
`conv(T) ⊆ ∪_{T' ⊆ T, |T'| ≤ min(r,|T|)} conv(T')` for every non-antipodal
`T ⊆ A`. Hence `conv_{≤m} A = conv_{≤min(r,s)} A` whenever
`m ≥ min(r, s)`, with `s = |A|` (or `s = ∞`).

**Step 3.** By the Bieri Σ-property, `Σ^m(G)^c = conv_{≤m} A`. So for
`m ≥ min(r,s)`, `Σ^m(G)^c = conv_{≤min(r,s)} A = Σ^{min(r,s)}(G)^c`. ∎

**Other convention.** If the convex hull of `T` is instead taken only for `T` in
an open hemisphere, as the spherical geodesic hull, Step 2 still applies. A
subset of a set in an open hemisphere lies in that hemisphere, and the
spherical hull is the image of the cone.
