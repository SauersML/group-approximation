---
rg: 2
id: atlas-six-relator-relative-pieces-proof
kind: route
title: Enumerate every symmetrized free-product piece in the six frozen Atlas relators
target: atlas-six-relator-relative-small-cancellation-audit
requires: []
artifacts:
  - experiments/atlas_six_relator_relative_pieces.py
  - experiments/atlas-six-relator-relative-pieces.json
---

The exact script reconstructs the six words over the two `GL4(2)` factors,
cyclically reduces them, closes under inversion and cyclic rotation, and
compares every pair of distinct symmetrized words.  Its pinned output has 92
words, eight maximum witnesses, and maximum piece ratio exactly `5/8`.
Exact period and dynamic-programming checks prove the remaining proper-power
and nonmetric-piece assertions.  These finite computations give
`(RSC1)--(RSC4)`; the cited small-cancellation hypotheses then yield the
stated theorem boundary.

