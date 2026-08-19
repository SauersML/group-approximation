---
rg: 2
id: nonhyperlinear-from-joint-weighted-a4-ceiling
kind: route
title: A jointly weighted four-cycle certificate contradicts the 19243 S3 distance wall
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-context-exact-regular-normalization
  - atlas-19243-centrality-forces-s3-distance
  - s3-weighted-two-generator-covariance-controls-commutant-distance
  - atlas-a8-t21-diagonal-energy-envelope
  - atlas-a4-joint-weighted-cycle-ceiling
---

Suppose the binary Leavitt unit group were hyperlinear.  Use the necessity
sequence from `leavitt-regular-atlas-hyperlinearity-criterion` and normalize the
thirty A4 context network exactly as in the established A4 holonomy route.  Its
canonical packet defect tends to zero, so
`atlas-19243-centrality-forces-s3-distance` gives

```text
liminf_n dist_2(U_n,C_K)^2 >= 1/128,                  (1)
```

where `C_K` is the commutant of the fixed raw `S3=<t21,t12>` slice.

Take the weights `p,q,c_01,c_23,c_30` supplied by
`atlas-a4-joint-weighted-cycle-ceiling` and put

```text
lambda=p+q-sqrt(p^2-pq+q^2).
```

The weighted S3 theorem and `(1)` imply

```text
liminf_n (p a_n^2+q b_n^2) >= lambda/128.             (2)
```

On the other hand the sharp diagonal `t21` envelope gives

```text
p a_n^2+q b_n^2
 <=2[
   p(c_01D_01+c_23D_23+c_30D_30)+qD_12
 ].                                                     (3)
```

The joint ceiling makes the limsup of `(3)` strictly smaller than
`2 lambda/256=lambda/128`, contradicting `(2)`.  Thus the hypothetical
hyperlinear necessity sequence cannot exist, and the binary Leavitt unit group
is not hyperlinear.

All prerequisites other than the joint scalar ceiling are finite or already
established in the atlas chain.  This route therefore makes
`atlas-a4-joint-weighted-cycle-ceiling` a single new optimization gate to the
primary goal.