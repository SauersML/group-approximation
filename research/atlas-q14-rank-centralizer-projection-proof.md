---
rg: 2
id: atlas-q14-rank-centralizer-projection-proof
kind: route
title: Project four offending transvection blocks onto the square-zero centralizer
target: atlas-q14-rank-centralizer-projection
requires: []
---

Multiply the q14 residual `(xy)^2-1` on the right by the invertible matrix
`yx` to identify its rank with `rank(NM-MN)`.  Split the first transvection
into image, source, and stationary blocks as in `(QRP5)`.  Direct block
multiplication gives the four centralizer equations `(QRP6)`.  Each offending
block is a compression of the commutator, so changing those four blocks costs
at most four times its rank.  The square defect of the corrected block matrix
is a two-term telescoping difference and costs at most twice the correction
rank.  These are `(QRP3)--(QRP4)`.
