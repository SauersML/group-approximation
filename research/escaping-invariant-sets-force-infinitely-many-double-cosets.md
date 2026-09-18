---
rg: 2
id: escaping-invariant-sets-force-infinitely-many-double-cosets
kind: claim
title: If a subgroup coarsely preserves a subset of an isometric G-space whose G-translates move arbitrarily far from it, the subgroup has infinitely many double cosets
distinct_from:
  bounded-orbit-subgroups-have-infinitely-many-double-cosets: that is the special case of a bounded invariant set; this allows unbounded coarsely invariant sets such as the axis of a loxodromic element, which is what virtually cyclic subgroups need.
---

**ESTABLISHED** (lane proof, elementary, inline; not reviewed; no priority
claimed, the argument is folklore-level).

**Statement.** Let `G` act by isometries on a metric space `X`, and let `H ≤ G`.
Suppose some nonempty `A ⊆ X` and `R ≥ 0` satisfy `d_Haus(hA, A) ≤ R` for every
`h ∈ H`. Write `δ(g) = inf{d(a, b) : a ∈ A, b ∈ gA}`. If `δ` is unbounded on
`G`, then `H\G/H` is infinite.

**Proof.** Let `g' = hgh'` with `h, h' ∈ H`.
- `δ(g') = inf d(h⁻¹A, gh'A)`, by applying the isometry `h⁻¹`.
- `d_Haus(h⁻¹A, A) ≤ R`, and `d_Haus(gh'A, gA) = d_Haus(h'A, A) ≤ R`.
- So `|δ(g') − δ(g)| ≤ 2R`, and `δ` varies by at most `4R` on each double coset.
- Finitely many double cosets would make `δ` bounded.

**Special cases.**
- **Bounded orbits.** `A = H·x` bounded gives the bounded-orbit lemma. There
  `δ(g) ≥ d(x, gx) − 2 diam A`.
- **Axes.** For `H` virtually `⟨φ⟩` with `φ` loxodromic on a hyperbolic `X`,
  take `A = H·x`, which is a quasi-line. Then `δ(χ^k) → ∞` for any loxodromic
  `χ` whose fixed points avoid those of `φ`. This is used in
  `virtually-cyclic-out-free-subgroups-have-infinite-double-cosets`.
