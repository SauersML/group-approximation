---
rg: 2
id: ugc-from-smooth-design-rich-2to1
kind: route
title: Feed smooth-design rich 2-to-1 hardness to the weakened-richness BKM reduction
target: unique-games-conjecture
requires: [smooth-design-rich-2to1-hardness, noise-test-sound-on-smooth-design-rich-inputs]
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

Given `epsilon`, BKM's Section 5 fixes `m`, `delta`, `zeta` and `K`. Put
`C_0 = C(K,m)` from the hypothesis. Then choose `gamma` for `C_0`, `d` so that
the noise `(1-epsilon)^(2d)` brings the high-degree mass below `gamma`, then
`t = 8d+1`, `tau`, and the source soundness `eta`.

The hypothesis at `(eta, t, m, K)` supplies NP-hard 2-to-1 instances at all large
alphabet sizes, with admissible pairing families. The transfer claim makes
Section 5.2's soundness argument valid on them, and completeness is unchanged.

This route is the weakened-richness analogue of
`ugc-from-rich-2to1-via-bkm-equivalence`. It is not a second copy: its
hypothesis only asks for a smooth low-degree design, which may be exponentially
smaller than the family of all pairings.
