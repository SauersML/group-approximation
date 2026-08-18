---
rg: 2
id: index-density-is-amplification-stable-proof
kind: route
title: Both numerator and denominator scale by k
target: index-density-is-amplification-stable
requires: []
---

Direct proof: additivity of the index under direct sums gives
`index(phi ⊗ I_k) = k · index(phi)`, and `dim(phi ⊗ I_k) = k · dim(phi)`, so
the ratio is unchanged.  The invariance of normalized-HS defects, traces and
scalar word values under `phi |-> phi ⊗ I_k` is the computation already
recorded in `additive-index-instability`.  No external input.
