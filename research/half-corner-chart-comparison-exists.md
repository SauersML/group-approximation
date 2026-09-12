---
rg: 2
id: half-corner-chart-comparison-exists
kind: claim
title: The rank-40 half-corner projective f_+ S splits off P S through a group-ring comparison
distinct_from:
  leavitt-corner-one-sided-lift-exists: that asks for a one-sided inverse inside the order-three corner eSe of the evaluation lift; this asks for a split embedding between two explicit rank-40 projectives of the finite chart GL_2(F_4), which the half-corner shear construction converts into such a pair.
  chart-comparison-must-fuse-torus-classes: that is an established necessary condition on any solution's actor group; this is the existence question itself.
artifacts:
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
  - research/artifacts/kaplansky-single-macro-prefix-transporter-obstruction-2026-09-08.md
---

Let `Q = L_(F_2)(1,2)^x`, `S = F_2[Q]`, and let `K = <g, u g u^-1> ~= GL_2(F_4)` be the
chart of the half-corner artifact on the leaves `(000,001,010,011)`. Let `f_+, P`
be its explicit idempotents in `F_2[K]`, with supports 30 and 70, regular rank 40
and lifted 2-adic trace `2/9`.

**Claim.** There are `Z in P S f_+` and `L in f_+ S P` with `L Z = f_+`.

After conjugating the source by `U = [u]`, this is exactly the comparison of
Section 5 of the half-corner artifact. There the explicit upper shear installs
`a_M f = Z` and the lower shear `K = c f L` finishes the construction, producing
a literal strict one-sided inverse pair in `S`. A solution is automatically
strict: `ev(f) = 0` while `ev(P) = p_01 != 0`, so `Z L = P` is impossible, and
`P + Z L` is a nonzero idempotent of lifted trace zero.

A sufficient reduced target is the rank-32 comparison `L_0 Z_0 = f_0` between
`f_0 = f_+(1+E)` and `P_0 = P(1+E)`, followed by adding the finite-block
isomorphism `f_+ E ~= P E` (half-corner Section 7).

## Attempts

* **Finite coordinate interpretations (dead).** Actor groups with a finite image
  injective on `K` in which `K` acts through natural blocks cannot work, at any
  coefficient choice or support. These are Jacobson one-pair specializations,
  packed Cuntz actors, literal two-pair formulas and creation-only
  specializations. By `chart-comparison-must-fuse-torus-classes`, such an image
  would have to fuse the torus classes `T0, T1, T2`, and fixed-space dimensions
  forbid it. Recorded as the invalidated route
  `half-corner-comparison-via-finite-actor-images`.
* **Normalizer actors (dead).** Half-corner Section 8: modulo the chart radical,
  source and target types are disjoint under all normalizer automorphisms.
* **Single macro-prefix transporters and one double coset (dead).** The focused
  transporter note gives exterior-power rank certificates on an actual finite
  orbit module.
* **Closed Cuntz channels without finite images (partly dead).** Sections 13 and
  15 give explicit determinant-line and degree-three kernels on the infinite
  boundary module for the displayed architectures. Sums over several double
  cosets passing the mod-three orbit test, general linear Leavitt units, and
  bit-level prefix permutations mixing the binary coordinates remain open.
* **Additive invariants never obstruct.** `Q` fuses `T0 ~ T1 ~ T2`, so all lifted
  Hattori--Stallings ranks of `f_+` and `P` agree. A live design must route the
  surplus fixed mass of `T0` to `T1` and `T2` through relations with no faithful
  finite shadow on the chart, such as depth-changing prefix permutations.
