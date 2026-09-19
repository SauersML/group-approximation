---
rg: 2
id: atlas-q14-growing-width-rank-one-bridge-proof
kind: route
title: Sandwich one outer product by a square-root matrix phase inside the q14 centralizer
target: atlas-q14-growing-width-rank-one-bridge-is-sharp
requires:
  - atlas-fixed-width-phases-resist-low-rank-bridging
---

Use the pairwise-zero q14-centralizing chart positions `E13,E14,E24`.
Put shift and wrap generators of `M_s(F2)` in the first two positions and a
rank-one operator `u phi` in the third.  If the `s` multiplicity components
of `u` span `F2^k` and those of `phi` span its dual, sandwiching by `M_s`
produces every tensor matrix unit.  This is possible exactly when `k<=s`,
and gives the square-root-width construction.
