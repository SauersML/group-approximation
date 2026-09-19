---
rg: 2
id: nonhyperlinear-from-a4-root-energy-ellipse
kind: route
title: The optimized root-energy ellipse contradicts the 19243 S3 distance wall
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-context-exact-regular-normalization
  - atlas-19243-centrality-forces-s3-distance
  - s3-weighted-two-generator-covariance-controls-commutant-distance
  - s3-weighted-budget-optimization
  - atlas-a4-root-energy-ellipse-ceiling
---

Suppose the binary Leavitt unit group were hyperlinear and take the normalized
exact-regular A4 necessity sequence from the established atlas compiler.  Put

```text
x_ij=sqrt(1-Re tau_n(V_n(tij))),
S_n=2x_01+2x_23+4x_30,
A_n=S_n^2,
B_n=x_12^2.
```

The exact positive `t21` word gives, before any Cauchy relaxation,

```text
a_n <= sqrt(2) S_n,
```

while the direct raw involution `t12` gives

```text
b_n^2=2B_n.
```

Hence for all `p,q>0`,

```text
p a_n^2+q b_n^2 <=2(pA_n+qB_n).                       (1)
```

The collision-distance theorem gives

```text
liminf_n dist_2(U_n,C_K)^2 >=1/128.                   (2)
```

The ellipse ceiling makes the bounded sequence `(A_n,B_n)` stay, eventually,
strictly inside

```text
A+B+sqrt(AB)<3/512.                                    (3)
```

Choose a convergent subsequence `(A_n,B_n)->(A,B)`.  By `(3)` and
`s3-weighted-budget-optimization`, there are fixed `p,q>0` such that

```text
pA+qB < lambda(p,q)/256.
```

The same strict inequality holds eventually on the chosen subsequence.  Thus
`(1)` gives

```text
limsup (p a_n^2+q b_n^2) < lambda(p,q)/128.            (4)
```

But the weighted S3 covariance theorem combined with `(2)` gives the opposite
bound

```text
liminf (p a_n^2+q b_n^2) >= lambda(p,q)/128,           (5)
```

a contradiction.  Therefore the hyperlinear necessity sequence cannot exist.

All remaining structure has disappeared from the endpoint: proving the one
root-energy ellipse ceiling is enough to establish the primary non-hyperlinear
group goal.