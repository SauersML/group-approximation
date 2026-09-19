---
rg: 2
id: one-phase-atomwise-leakage-proof
kind: route
title: Expand the section map in source and target phase blocks
target: one-phase-chart-tag-pays-atomwise-leakage
requires: []
---

For each source atom `E_i`, orthogonally split the range of `TE_i` into the
target atoms and the carrier exit:

```text
TE_i=(1-S)TE_i+sum_j F_jTE_i.                          (OPP1)
```

Because `AE_i=zeta^iE_i` and `BF_j=zeta^jF_j`,

```text
(BTR-TA)E_i
 =-zeta^i(1-S)TE_i
   +sum_j(zeta^j-zeta^i)F_jTE_i.                       (OPP2)
```

All displayed row blocks are orthogonal, and the source blocks indexed by
`i` are orthogonal as well. Pythagoras therefore gives the first identity
in `(OPT4)`. Applying `(OPP1)` to `(1-F_i)TE_i` gives the second.

For `i!=j`, the separation of distinct `q`-th roots satisfies

```text
|zeta^j-zeta^i|^2>=4 sin^2(pi/q)=gamma_q.              (OPP3)
```

The diagonal blocks have weight zero. Comparing the two sums in `(OPT4)`
proves `(OPT5)`.
