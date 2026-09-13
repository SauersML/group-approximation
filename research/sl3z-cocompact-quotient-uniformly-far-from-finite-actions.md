---
rg: 2
id: sl3z-cocompact-quotient-uniformly-far-from-finite-actions
kind: claim
title: SL3(Z) on SL3(R)/Λ, for Λ from a cubic division algebra, is uniformly far from every finite action
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-part2-2026-09-13.md
distinct_from:
  sl3-prime-coset-action-exact-atlas-firewall: that excludes exact finite atlases for a discrete building-vertex coset action in Hamming density; this excludes finite actions carrying metrically almost-equivariant marks in a compact homogeneous space, by holonomy superrigidity and norm drift
  codense-kazhdan-coset-action-forces-permutation-outliers: that is the abstract Kazhdan co-density gap for coset actions; this uses no property (T), only discreteness, rational rigidity of representations and non-amenable drift
---

**ESTABLISHED (unreviewed).** Let `Λ <= SL_3(R)` be a cocompact lattice admitting a faithful
homomorphism `ι : Λ → GL_m(Q)` whose image contains no nontrivial unipotent matrix. Examples: every
lattice contained in a conjugate of `SL_1(D)(Q)`, for `D` a central division algebra of degree `3` over
`Q` split over `R`, through the left regular representation on `D`. Then there is `ε_E > 0` such that
for every finite set `V` with an action of `SL_3(Z)` and every map `y : V → SL_3(R)/Λ`, some `v ∈ V` and
elementary matrix `s` satisfy `d̄(y(sv), s·y(v)) >= ε_E`.

**Contrast.**
* For an irrational rotation of the circle, the analogous distance to finite actions is `0`.
* For `SL_3(Z)` on `SL_3(R)/SL_3(Z)`, the Hecke orbits give exactly equivariant finite marks.

So this is a Diophantine rigidity of the higher-rank action. In any finite model at scale below `ε_E`,
either the model is not an honest action or some vertex is misplaced.

**What it does not say.** Microstates allow a proportion `ε` of bad vertices, and this theorem allows
none. Nonsoficity would need the same conclusion with a vanishing fraction of defects, on almost-actions.

Proof in `sl3z-cocompact-quotient-uniformly-far-from-finite-actions-proof`.
