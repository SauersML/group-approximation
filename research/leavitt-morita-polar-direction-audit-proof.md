---
rg: 2
id: leavitt-morita-polar-direction-audit-proof
kind: route
title: Gauge the binary Morita coefficient chart and compute its Hilbert Gram
target: leavitt-forward-morita-polar-misses-reynolds-return
requires:
  - mixed-steinberg-loops-admit-morita-rectangular-model
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
---

Conjugating the target object by `G` gives `(MCP1)--(MCP2)`, so every typed
coefficient product is unchanged.  Expanding the sum gives the similarity
formula `(MCP3)`, and coefficient cancellation gives `(MCP4)`.

The standard identity `(L_aR_b)^*=L_(a^*)R_(b^*)` gives `(MCP5)`.  Arbitrary
condition number of `G` proves the lack of an HS polar estimate from typed
multiplication.  For unitary `G`, direct normalized-trace calculation gives
`(MCP6)`.  Its range is the diagonal amplified source label algebra inside
the doubled target, while the desired Reynolds contraction runs between the
commutants in reverse.  This proves the claim.
