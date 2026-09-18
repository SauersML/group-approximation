---
rg: 2
id: fpbs-retained-boundary-rounding-isoperimetric-floor-proof
kind: route
title: Count tree edges and half crossing edges per block, then bound each component boundary by degree and Cheeger constant
target: fpbs-retained-boundary-rounding-isoperimetric-floor
requires:
  - fpbs-relative-cycle-block-rounding-bound
artifacts:
  - research/artifacts/fpbs/docs/retained-boundary-isoperimetric-floor-2026-09-17.md
---

Sections 2--7. Mass transport over finite blocks turns the cost of H'
into the block average of sum_C (|C| - 1 + |boundary C|/2), since the
crossing edges at a block are the disjoint union of its component
boundaries. Each component boundary contains its S_0-Cayley boundary.
That boundary is at least d_0, by the atom proof of Mader's theorem
included in the artifact, and at least h|C|. So
|boundary C|/2 - 1 >= (1/2 - 1/d_0) h |C|.

The premise corollary combines this with inequality (10) of the
established rounding bound. The M-free corollary compares the forest
edge count of the source restricted to each block with that of H.
Calibration: the tree inequality in each Z-layer gives h >= 2 for
F_2 x Z with {a,b,t}.
