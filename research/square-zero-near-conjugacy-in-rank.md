---
rg: 2
id: square-zero-near-conjugacy-in-rank
kind: claim
title: Close square-zero maps of the same rank are conjugate by a rank-small basis change
distinct_from:
  atlas-q14-rank-centralizer-projection: that projects one map linearly into a centralizer but can lose square-zero type; this starts with two exact square-zero maps of the same type and controls the conjugating basis change.
---

ESTABLISHED.  Let `A,B in M_n(k)` satisfy

```text
A^2=B^2=0,       rank A=rank B,
e=rank(A-B).                                           (SZC1)
```

Then there is `S in GL_n(k)` such that

```text
S A S^(-1)=B,       rank(S-1)<=8e.                    (SZC2)
```

Only the existence of a universal constant is used downstream.

### Proof

Put

```text
K=ker(A-B) intersect A^(-1)(ker(A-B)).                 (SZC3)
```

Then `codim K<=2e`.  On `K`, the two maps agree.  Moreover `K` is invariant
under both: if `v in K`, then `Av=Bv` lies in `ker(A-B)`, and its image under
either square-zero map is zero.

Write `c=codim K<=2e` and `r=rank A=rank B`.  Since the two maps agree on
`K`, put

```text
L=A(K)=B(K).
```

The loss of image rank through a codimension-`c` subspace is at most `c`, so
`dim L>=r-c`.  Choose common length-two chains in `K` whose terminal vectors
form a basis of `L`.

The rank bound also gives

```text
dim(im A+im B)<=r+e.                                  (SZC4)
```

Indeed, modulo `im A`, every vector `Bv` is represented by `(B-A)v`.
Meanwhile

```text
dim(K intersect ker A)>=n-r-c;
```

on `K`, the kernels of `A` and `B` coincide.  Therefore this common kernel
contains a subspace `T` disjoint from `im A+im B` of dimension at least

```text
(n-r-c)-(r+e)=n-2r-c-e.
```

Use `T` as common length-one chains.  The common module `H` formed by these
length-two and length-one chains is a direct summand for both maps: extend
the chosen basis of `L` inside each image, then extend `T` inside each kernel
modulo that image.  Its codimension satisfies

```text
codim H
 <= n-[2(r-c)+(n-2r-c-e)]
 =3c+e <=4c<=8e.                                     (SZC5)
```

The complements have the same numbers of length-two and length-one Jordan
blocks: the full modules have the same dimension and rank, and the common
summand has one fixed block type.  Choose a module isomorphism between the
two complements and take it to be the identity on `H`.  The resulting `S`
intertwines `A` and `B`, while `S-1` vanishes on `H`; `(SZC2)` follows.
