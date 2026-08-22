---
rg: 2
id: direct-sum-weil-compression-proof
kind: route
title: Add rank-one Frobenius errors and restore one fixed line per block
target: direct-sum-weil-compressions-have-quadratic-padding
requires:
  - even-weil-fixed-line-compression
---

Each compressed block has fixed-word error supported through one deleted
line, hence bounded unnormalized Frobenius square.  Orthogonal sums add those
squares, giving `O(K/D)` normalized squared defect.  Restoring the `K`
deleted lines produces the exact sum of full Weil constituents; the
zero-padded generalized-distance numerator is again `O(K)` and its
normalization is `D+K`.

Both estimates are upper bounds in terms of `K/D`.  No lower bound for the
maximum of the two cubic residuals is proved here, so the route does not
identify `K/D` with the squared observed presentation defect.
