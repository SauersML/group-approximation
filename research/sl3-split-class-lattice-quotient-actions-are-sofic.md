---
rg: 2
id: sl3-split-class-lattice-quotient-actions-are-sofic
kind: claim
title: If two lattices of SL3(R) are each commensurable with a conjugate of SL3(Z), either one acting on the quotient by the other is sofic
distinct_from:
  sl3z-lattice-space-action-is-sofic: that is the single pair SL3(Z), SL3(Z), handled by Hecke orbits; this spreads soficity to every pair in the split commensurability class using only duality, restriction and factors
  sl3z-on-cocompact-lattice-quotient-is-not-sofic: that is the open pair with a cocompact lattice, outside the class; this shows every pair inside the class is sofic, so that claim sits exactly in the complement
---

**ESTABLISHED (unreviewed).** Let `G = SL_3(R)`, and let `Γ_1, Γ_2 <= G` be lattices, each commensurable
with some conjugate of `SL_3(Z)`. Then the left action `Γ_1 ↷ G/Γ_2`, with the invariant probability
measure, is sofic (Păunescu Definition 1.4).

**Examples.** A congruence subgroup acting on the quotient by another congruence subgroup.
`SL_3(Z)` acting on `G/gSL_3(Z)g^(−1)` for any `g ∈ G`.

**Where the line falls.** Inside the commensurability class of the conjugates of `SL_3(Z)`, every
quotient action is sofic, with no new equidistribution input. A lattice outside the class gives actions
with no finite orbits. Any cocompact lattice is outside, because commensurable lattices are both uniform
or both not. That is `sl3z-on-cocompact-lattice-quotient-is-not-sofic`, which is therefore exactly the
complement of this claim for pairs involving `SL_3(Z)`.

Proof in `sl3-split-class-lattice-quotient-actions-are-sofic-proof`.
