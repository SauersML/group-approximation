---
rg: 2
id: atlas-root-energy-ellipse-controls-s3-distance
kind: claim
title: The four-cycle root-energy ellipse dominates three quarters of squared S3 commutant distance
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that is the open upper bound needed from the A4/collision compiler; this is the matching established lower geometry for an arbitrary relative chart unitary.
  atlas-19243-relation-forces-s3-distance: that is the sharper geometric input available when the collision word itself tends to one; this claim converts either S3-distance estimate into the scalar root-energy wall.
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

There is a sharper wall in a quotient-necessity sequence.  If the collision
relation itself has defect

```text
epsilon_q=||q_19243(U)-1||_2,
```

then `atlas-19243-relation-forces-s3-distance` gives

```text
F >= (3/4) max(0,(sqrt(2)-epsilon_q)/8)^2.             (ROOT-19243-REL-WALL)
```

Consequently `epsilon_q(n)->0` implies

```text
liminf F_n >= 3/128.
```

Thus `3/512` is the exact dual of the centrality-only wall, while `3/128` is
the stronger exact dual available in the actual Leavitt quotient necessity
sequence, where collision `19243` is a kernel relation.
