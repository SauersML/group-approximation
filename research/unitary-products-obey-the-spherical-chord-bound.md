---
rg: 2
id: unitary-products-obey-the-spherical-chord-bound
kind: claim
title: Products of unitaries obey the spherical chord bound in tracial L2
distinct_from:
  atlas-t30-is-one-parabolic-c3-bridge: that records a particular six-letter cocycle factorization and bounds its endpoint by the Euclidean polygonal length; this gives the strictly sharper spherical bound for every unitary product.
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let
`A_1,...,A_r` be unitaries.  With the normalized tracial `2`-norm, put

```text
d_i=||A_i-1||_2,
D=||A_1...A_r-1||_2.
```

Then

```text
asin(D/2)
 <= min(pi/2, sum_(i=1)^r asin(d_i/2)).                (SPH-CHORD)
```

Equivalently, whenever the sum on the right is at most `pi/2`,

```text
D <= 2 sin(sum_i asin(d_i/2)).                         (SPH-CHORD-2)
```

The same conclusion holds in every matrix algebra with normalized
Hilbert--Schmidt norm, uniformly in the dimension.

This is stronger than repeated use of `D<=sum_i d_i`: the partial products
are not arbitrary points of the ambient Hilbert space, but unit vectors on
its sphere.  A nondegenerate polygonal path through unitary points therefore
cannot saturate the ambient linear triangle inequality.

