---
rg: 2
id: lin-explicit-dilation-intertwiner-proof
kind: route
title: Read the state-local intertwining identities coordinatewise from Lin's dilation
target: lin-state-local-gh-is-an-intertwining-exactifier
requires:
  - lin-state-dependent-gh-preserves-the-commutant
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
---

The coordinate indexed by `k` of `Phi(a)Vxi` is
`phi(k^(-1)a)xi/sqrt(|K|)`, while that of `Vphi(a)xi` is
`phi(k^(-1))phi(a)xi/sqrt(|K|)`. Squaring, summing, and reindexing proves
`(SLI1)`. The `k`-coordinate of `((U tensor I)V-VU)xi` is the corresponding
commutator divided by `sqrt(|K|)`, proving `(SLI2)`. Since every `phi(k)`
commutes with `A'`, `(SLI3)` is exact.
