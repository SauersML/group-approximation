---
rg: 2
id: expander-flow-root-loss-proof
kind: route
title: Sum the divergence equations and test the isolated root coordinate
target: bounded-expander-flows-cannot-root-the-normalized-amitsur-sum
requires:
  - uniform-linear-pcpp-tensorizes-to-amitsur-hs
---

For `(BEF3)`, evaluate the linear tester on the coordinate vector supported
only at the distinguished root.  This reads off exactly the probability-
weighted squared norm of the root column of the check matrix.  Uniform
weights, bounded coefficients and bounded column occurrence give `(BEF4)`.

For the flow formulation, the incidence matrix kills the all-ones row
vector.  Summing the vertex equations therefore yields

```text
sum_i r_i=-alpha_N sum_i v_i+N beta_N t.
```

Vanishing on the normalized-sum graph forces `(BEF7)`.  The root-only
assignment proves `(BEF8)`.  If `beta_N` is bounded below instead, the reverse
triangle inequality gives `(BEF9)`, and the bounded vertex degree gives
`(BEF10)` by the triangle inequality.
