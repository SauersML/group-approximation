---
rg: 2
id: localized-rank-imbalance-intersection-proof
kind: route
title: Intersect the larger sign space with the smaller sign complement
target: localized-involution-rank-imbalance-forces-britton-carrier
requires: []
---

Work inside `E C^d`.  Since `E` reduces `C` and `B`, the operators `P,R`
in `(LRI1)` are orthogonal projections on this space.  For any two subspaces
`U,V` of a finite-dimensional space `H`,

```text
dim(U intersection V)>=dim(U)+dim(V)-dim(H).            (LRI8)
```

If `rank(P)>=rank(R)`, apply `(LRI8)` to

```text
U=Ran(P),                 V=Ker(R) inside Ran(E).
```

The resulting intersection has dimension at least

```text
rank(P)+(rank(E)-rank(R))-rank(E)
 =rank(P)-rank(R).                                      (LRI9)
```

Let `Q` be its orthogonal projection.  On `Ran(Q)`, `C=+I` and `B=-I`.
Because these operators are self-adjoint, a subspace on which either acts
scalarly is reducing, so `Q` commutes with both.  Hence `CBCB=I` on `Q`.
The case `rank(R)>=rank(P)` is identical with `Ker(P) intersection Ran(R)`.
Divide `(LRI9)` by `d` to obtain `(LRI2)`.

For the central-carrier calculation, expand in the canonical group trace:

```text
tau((1-J)(1+a)/4)
 =(tau(1)+tau(a)-tau(J)-tau(Ja))/4=1/4,                (LRI10)
```

under the stated nonidentity assumptions.  Canonical microstate convergence
gives the same balance asymptotically after fixed-word exactification.  This
proves both the positive intersection lemma and the balanced-half boundary.

