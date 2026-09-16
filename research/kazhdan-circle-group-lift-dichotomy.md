---
rg: 2
id: kazhdan-circle-group-lift-dichotomy
kind: claim
title: A Kazhdan circle group virtually lifts to the line or has a Kazhdan central lift
artifacts:
  - research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md
---

**Setup.**

- Let `T(x) = x + 1`, and let `Homeo_Z(R)` be the group of homeomorphisms of `R` that
  commute with `T`. Every element of it is increasing.
- Reduction mod `Z` gives a surjective homomorphism `p : Homeo_Z(R) → Homeo_+(S^1)`
  with kernel `⟨T⟩ ≅ Z`, which is central.
- For `G ⊂ Homeo_+(S^1)` put `Ĝ := p^{-1}(G)`. It is a central extension
  `1 → ⟨T⟩ → Ĝ → G → 1`.

**Statement.** Let `G ⊂ Homeo_+(S^1)` have property (T). Then exactly one of the
following holds.

- **(A)** Some subgroup `K̂ ⊂ Ĝ` is mapped injectively by `p` onto a normal subgroup of
  finite index in `G`.
- **(B)** `Ĝ` has property (T).

In case (A), a finite-index subgroup of `G` is isomorphic to the group `K̂` of
homeomorphisms of the line. In case (B), `Ĝ ⊂ Homeo_+(R)` is an infinite Kazhdan group
whose centre contains the translation `T`.

**How to read it.** Case (A) is exactly the vanishing of the real Euler class
`e_R(G) ∈ H^2(G; R)` of the action. The proof does not use this. Either way, a Kazhdan
group of circle homeomorphisms produces a Kazhdan group of line homeomorphisms that is
infinite whenever `G` is. See `infinite-left-orderable-kazhdan-group-from-circle`.

The proof is `kazhdan-circle-group-lift-dichotomy-proof`. Full details of the covering
lemma are in the artifact (§0 and §2).
