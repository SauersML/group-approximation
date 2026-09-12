---
rg: 2
id: global-v4-cross-gram-curvature-proof
kind: route
title: Insert the five-fourths source trace into the Gram branching inequality
target: global-v4-exit-capacity-is-cross-gram-curvature
requires:
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
  - gram-branching-capacity-with-overlap
  - partial-isometry-gram-is-range-overlap
---

The three source projections over context `c` have total trace
`5tau(P_c)/4`.  Summing over contexts gives `s=5q/4`.  Apply `(GBC2)` to the
family of exit partial isometries and the block parent `P`: since
`tau(P)=q`, rearrangement gives `2l+o>=q/4`.  The cross-Gram/range-overlap
identity turns `o` into the sum of the off-diagonal context-exit overlaps,
proving `(VGC3)--(VGC4)`.

