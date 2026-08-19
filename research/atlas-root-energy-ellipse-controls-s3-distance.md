---
rg: 2
id: atlas-root-energy-ellipse-controls-s3-distance
kind: claim
title: The four-cycle root-energy ellipse dominates three quarters of squared S3 commutant distance
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that is the open upper bound needed from the A4/collision compiler; this is the matching established lower geometry for an arbitrary relative chart unitary.
---

For any relative regular-A8 chart unitary `U`, put

```text
x_ij=sqrt(1-Re tau(V(tij))),
S=2x_01+2x_23+4x_30,
F=S^2+S x_12+x_12^2.
```

Let `C_K` be the unitary commutant of the raw
`S3=<t21,t12>` slice.  Then

```text
F >= (3/4) dist_2(U,C_K)^2.                            (ROOT-S3-DUAL)
```

Consequently, for a canonical atlas model with packet defect `delta`,
`atlas-19243-centrality-forces-s3-distance` implies

```text
F >= (3/4) max(0,(sqrt(2)-L_19243 delta)/16)^2.        (ROOT-19243-WALL)
```

In particular every packet-microstate sequence with `delta_n->0` satisfies

```text
liminf F_n >= 3/512.
```

Thus the `3/512` in the root-energy ellipse target is not a bookkeeping
constant.  It is the exact scalar dual of the established collision-19243 S3
distance wall after optimizing both detector weights and the positive t21 word
triangle bound.