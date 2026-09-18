---
rg: 2
id: limit-set-escaping-forces-infinitely-many-double-cosets
kind: claim
title: If some loxodromic element of G has both fixed points outside the limit set of H in a hyperbolic G-space, then H has infinitely many double cosets in G
requires:
  - escaping-invariant-sets-force-infinitely-many-double-cosets
distinct_from:
  escaping-invariant-sets-force-infinitely-many-double-cosets: that needs a coarsely invariant set whose translates escape; this produces the escaping translates from a boundary condition alone, for arbitrary subgroups, with no quasiconvexity or finite generation.
  bounded-orbit-subgroups-have-infinitely-many-double-cosets: that is the case of empty limit set.
---

**ESTABLISHED** (lane proof; elementary Gromov-hyperbolic estimates, inline; not
reviewed; no priority claimed).

**Setting.**
- **The space.** `X` is a δ-hyperbolic geodesic space. It need not be proper.
- **The action.** `G` acts by isometries, and `H ≤ G` is any subgroup.
- **The orbit.** Fix `v ∈ X` and put `A = H·v`.
- **The limit set.** `Λ_H ⊆ ∂X` is the set of limits of sequences in `A`,
  where a sequence `x_i` converges to `ξ` if `(x_i·ξ)_v → ∞`.

**Statement.** If a loxodromic `χ ∈ G` has fixed points `χ^+, χ^− ∉ Λ_H`, then
`d(A, χ^kA) → ∞` as `k → ∞`. So `H\G/H` is infinite.

**Proof.**
- **Notation.** Constants `c` depend only on `δ`, `χ` and `v`. `τ > 0` is the
  stable translation length of `χ`, so `d(v, χ^{±k}v) ≥ kτ`. The orbit
  `j ↦ χ^jv` is a quasi-geodesic. By the Morse lemma, which needs no
  properness, `(χ^{±k}v · χ^±)_v ≥ d(v, χ^{±k}v) − c`.
- **Step 1.** `M_± := sup_{a∈A}(a·χ^±)_v < ∞`. Otherwise some `a_i ∈ A` has
  `(a_i·χ^+)_v → ∞`, so `a_i → χ^+` and `χ^+ ∈ Λ_H`.
- **Step 2.** Let `a ∈ A` and put `w = χ^{−k}v`.
  - Since `(a·χ^−)_v ≥ min{(a·w)_v, (w·χ^−)_v} − δ` and
    `(w·χ^−)_v ≥ kτ − c`, for large `k` we get `(a·w)_v ≤ M_− + δ`.
  - Since `(a·v)_w + (a·w)_v = d(v,w)`, we get `(a·v)_w ≥ kτ − c − M_− − δ`.
  - Also `(v·χ^+)_w = (χ^kv·χ^+)_v ≥ kτ − c`.
  - So `(a·χ^+)_w ≥ kτ − C`, where `C` depends on `M_−`, `δ`, `χ` and `v`.
    Applying `χ^k`, `(b·χ^+)_v ≥ kτ − C` for every `b ∈ χ^kA`.
- **Step 3.** If `a' ∈ A` and `b ∈ χ^kA` have `d(a',b) ≤ D`, then
  `(a'·χ^+)_v ≥ (b·χ^+)_v − D − 2δ ≥ kτ − C − D − 2δ`. This is at most `M_+`,
  so `k ≤ (M_+ + C + D + 2δ)/τ`. Hence `d(A, χ^kA) → ∞`.
- **Conclusion.** `A` is `H`-invariant. Apply
  `escaping-invariant-sets-force-infinitely-many-double-cosets` with `R = 0`.

**Contrapositive.** If `H\G/H` is finite, then `Λ_H` meets the fixed pair of
every loxodromic element of `G`, in every hyperbolic `G`-space.
