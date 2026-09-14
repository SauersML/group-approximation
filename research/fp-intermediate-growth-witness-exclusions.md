---
rg: 2
id: fp-intermediate-growth-witness-exclusions
kind: claim
title: A finitely presented group of intermediate growth maps onto no cover of the Grigorchuk or Basilica groups, and is H semidirect Z whenever it is indicable
distinct_from:
  fp-group-of-intermediate-growth-exists: that is the open existence question; this lists established constraints on any witness
  fp-intermediate-growth-iff-subexponential-truncation: that is the truncation equivalence; this collects structural exclusions from imported cover, automorphism and gap theorems
---

**Statement.** Let `G` be a finitely presented group of intermediate growth, if one exists.
1. No quotient of `G` is a finitely generated cover of the first Grigorchuk group `𝔊`, of the
   Basilica group `𝔅`, or of any `G_ω` with `ω ∈ Ω₊`.
2. `G` has no normal subgroup isomorphic to `𝔊` (this holds for every finitely presented group).
3. If `G` is residually nilpotent (for example residually finite-`p`), then `γ_G(n) ≺ e^{√n}`
   fails.
4. If `G` maps onto `ℤ` with kernel `H`, then `H` is finitely generated of intermediate growth,
   `G ≅ H ⋊ ℤ`, and `H` has a finite ascending endomorphic presentation whose endomorphisms induce
   automorphisms of `H`.

Proof: `fp-intermediate-growth-witness-exclusions-proof`. No novelty claimed.
