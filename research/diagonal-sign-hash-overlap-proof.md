---
rg: 2
id: diagonal-sign-hash-overlap-proof
kind: route
title: Cancel the block-off-diagonal boundary inside the trace
target: diagonal-sign-margin-controls-hash-overlap
requires: []
---

For each sampled coordinate, the wrong-sign spectral projection of `T_s`
relative to `H_s` has trace `(DSM3)`.  Insert `X_s` between `H_s` and `Q_s`.
The `H_s(Q_s-X_s)` term has trace zero by block orthogonality, while
Cauchy--Schwarz bounds the two remaining trace errors by `a_s` and `b_s`.
Finally every pair of unequal joint hash labels disagrees in some
coordinate, so summing the coordinate wrong-sign events dominates the total
off-label overlap.
