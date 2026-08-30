---
rg: 2
id: hopf-power-weighted-hall-proof
kind: route
title: Expand the Euler polynomial and apply Hall to repeated demand copies
target: hopf-power-blocks-obey-weighted-hall-euler-criterion
requires: []
artifacts:
  - research/artifacts/stw99-lxvi-weighted-hall-rank-amplification-no-go-2026-08-30.md
---

Write `x_i=c_1(H_i)`.  In the torsion-free ring

`Z[x_i : i in union_j S_j]/(x_i^2)`,

the top Chern class is

`e(Xi)=product_j (sum_(i in S_j)x_i)^(r_j)`.

Every coefficient in this expansion is nonnegative.  A nonzero monomial
is obtained exactly by choosing, for each `j`, `r_j` distinct coordinates
from `S_j`, with no coordinate used for two different blocks.  Hence
`e(Xi)!=0` exactly when such disjoint demand sets `R_j` exist.

Replace block `j` by `r_j` labelled copies of the set `S_j`.  Ordinary
Hall says that these copies have a system of distinct representatives iff
every sublist has union at least its length.  For a fixed collection `F`
of underlying blocks, the strongest sublist using precisely those
supports takes all `r_j` copies and has length `sum_(j in F)r_j`.
Therefore ordinary Hall for the repeated list is equivalent to `(WH)`.
This proves the criterion.
