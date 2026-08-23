---
rg: 2
id: low-rank-reflection-surgery-word-proof
kind: route
title: Telescope every fixed Iwahori word across the finite-rank reflection change
target: low-rank-reflection-surgery-preserves-the-exact-bs-core
requires:
  - two-exit-gram-swap-builds-low-rank-involution-surgery
---

The Gram-swap theorem gives `rank(X_1-X_0)<=ell<=8r`.  A word with `q`
occurrences of `X` changes by a sum of `q` terms, each a unitary translate
of `X_1-X_0`.  This proves both estimates in `(LRS2)`.  The core generators
are never changed, so their covariance row remains exact.
