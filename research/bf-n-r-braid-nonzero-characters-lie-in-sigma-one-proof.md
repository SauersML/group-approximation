---
rg: 2
id: bf-n-r-braid-nonzero-characters-lie-in-sigma-one-proof
kind: route
title: "Meinert's criterion with m = 1 on the Stein-space band, Sigma^1 of pure braid groups at the vertices"
target: bf-n-r-braid-nonzero-characters-lie-in-sigma-one
requires:
  - pure-braided-bht-braid-characters-dimension-n-n-minus-1
  - bf-n-r-twist-detected-characters-lie-in-sigma-infinity
artifacts:
  - research/artifacts/zp-pure-braided-bht-roots-and-sigma1-2026-09-13.md
---

Artifact part 3, Theorem 7. There are two cases.

- The braid part is supported on the first–last pair only. Then its full-twist
  value is constant and nonzero, and
  `bf-n-r-twist-detected-characters-lie-in-sigma-infinity` gives `Sigma^infinity`.
- Otherwise it is nonzero on an interior, first-leaf or last-leaf family.
  Such a type recurs at many index pairs, so the restriction `Phi_k` to the
  vertex stabilizer `PB_k` spans at least 5 strands for large `k`. By
  Koban–McCammond–Meier Theorem A (arXiv:1306.4046) it lies in `Sigma^1(PB_k)`.
  Meinert's criterion (Meier–Meinert–VanWyk Theorem 2.4) with `m = 1`, on the
  connected cocompact band of the Skipper–Wu Stein space, gives `[chi]` in
  `Sigma^1`.
