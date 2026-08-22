---
rg: 2
id: sublinear-bandwidth-rank-amplification-proof
kind: route
title: Repeat every rank microstate in contiguous diagonal blocks
target: sublinear-bandwidth-is-vacuous-under-rank-amplification
requires: []
---

For a matrix `A`, the direct sum `A^(direct_sum r)` in contiguous blocks has
bandwidth at most the block size, and its inverse is
`(A^-1)^(direct_sum r)`.  Every Laurent word respects direct sums.  Therefore
each residual is the direct sum of `r` copies of the old residual, so both
its rank and the ambient dimension are multiplied by `r`.  All normalized
rank defects and separations are unchanged, while relative bandwidth is at
most `1/r`.  Taking `r` to infinity proves both implications in `(SBV1)`--
`(SBV2)`.
