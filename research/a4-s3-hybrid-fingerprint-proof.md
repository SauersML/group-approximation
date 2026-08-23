---
rg: 2
id: a4-s3-hybrid-fingerprint-proof
kind: route
title: Restrict the three S4 characters to A4 and a point-stabilizer S3
target: a4-s3-hybrid-fingerprint-diagonalizes-s4-extension-triple
requires: []
---

The two-dimensional `S4` representation factors through
`S4/V4 ~= S3`.  Its restriction to `A4/V4 ~= C3` is therefore
`omega direct_sum omega^2`.  The standard three-dimensional representation
restricts irreducibly to `A4`; twisting by the sign character does not change
that restriction because sign is trivial on `A4`.  This proves `(HFP1)`.

For the point stabilizer `S3`, restrict the four-point permutation
representation and remove its global invariant line.  The result is
`1 direct_sum sigma`; twisting by sign gives `epsilon direct_sum sigma`.
The two-dimensional representation restricts to `sigma`.  This proves
`(HFP2)`.  Reading the multiplicities of `omega`, `1`, and `epsilon` gives
the three rows of `(HFP4)`.

