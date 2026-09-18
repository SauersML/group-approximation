---
rg: 2
id: titz-witzel-nowhere-domestic-via-open-dense-opposite-geometry
kind: route
title: Nontrivial elements of the Titz Mite–Witzel kernels are type-preserving hyperbolic isometries of a thick C̃₂ building, so their domestic sets are nowhere dense
target: titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity
requires:
  - exotic-rank-two-building-lattices-are-mif
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Let `g ∈ Γ̌ ∖ {1}`.
- **`g` is hyperbolic.** `Γ̌` acts freely on `X`, so `g` has no fixed point, and every isometry
  of an affine building is semisimple (Parreau 2000, as cited by the source).
- **`g` is type-preserving,** by step 2 of `titz-witzel-kernels-mif-via-exotic-building-lattice-mif`.
- **`X` is thick and locally finite, of type `C̃₂`.**

So item 3 of `exotic-rank-two-building-lattices-are-mif` (Le Bars–Leibtag–Vigdorovich,
`thm:gq-open-dense-opposite-geometry`) applies. The opposite geometry `𝒪_𝓕(g)` is open and
dense, so `N(g) = 𝓕 ∖ 𝒪_𝓕(g)` is closed with empty interior. ∎

This was the premise the graph called "the crux" of `titz-witzel-kernel-mif-via-opposition-ping-pong`.
It is proved by Le Bars–Leibtag–Vigdorovich, and the credit is theirs.
