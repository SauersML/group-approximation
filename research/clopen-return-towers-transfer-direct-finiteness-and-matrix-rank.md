---
rg: 2
id: clopen-return-towers-transfer-direct-finiteness-and-matrix-rank
kind: claim
title: A short-period-free subshift has a return corner supplying matrix levels and preserving failure of direct finiteness
distinct_from:
  binary-letter-repetition-realizes-matrix-amplification: that changes the subshift to obtain a full matrix ring; this keeps the original ring and uses a variable-height return section to obtain a matrix corner.
artifacts:
  - research/artifacts/pestov91-return-towers-lower-mf-rank-2026-09-13.md
---

If `T^j` has no fixed point for `1<=j<k`, a finite clopen construction
gives a return section `C` with return times in `[k,2k-1]`. Its corner
`P=1_C R_X 1_C` is another finite-alphabet subshift ring. The full
tower decomposition identifies `R_X` with a corner of `M_(2k-1)(P)`,
while the first `k` levels embed `M_k(P)` as a corner subring of `R_X`.

If `R_X` is not directly finite, neither is `P`: otherwise the subshift
ring theorem makes `P` stably finite, forcing its matrix corner `R_X`
to be directly finite.
