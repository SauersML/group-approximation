---
rg: 2
id: rational-balanced-hyperoctahedral-atlas-proof
kind: route
title: Rationalize the context marginals and match their sign fibers
target: tracial-bcs-has-rational-balanced-hyperoctahedral-atlas
requires: []
---

For a tracial state `tau`, let `p_(c,a)` be the joint context atom and put
`mu_(c,a)=tau(p_(c,a))`.  These numbers give a point of the polytope

```text
mu_(c,a)>=0,
sum_a mu_(c,a)=1,
sum_a a_x mu_(c,a)=sum_b b_x mu_(d,b)                    (RBH4)
```

for every overlap `(c,d,x)`.  The polytope is cut out by rational linear
equalities and inequalities and is nonempty, so it contains a rational point.
For completeness, take a nonempty face of minimum dimension containing a
feasible point in its relative interior; Gaussian elimination over `Q` gives
a rational point in its rational affine hull, and a sufficiently close
rational point stays inside all strict inequalities of that face.

Clear a common denominator to obtain `(RBH1)`.  Equality of the signed
marginals and equality of total mass imply

```text
sum_(a:a_x=+1)n_(c,a)=sum_(b:b_x=+1)n_(d,b),
sum_(a:a_x=-1)n_(c,a)=sum_(b:b_x=-1)n_(d,b).             (RBH5)
```

Choose arbitrary bijections between the two plus fibers and between the two
minus fibers.  Their union is `pi_(c,d,x)` and proves `(RBH3)`.  The common
hyperoctahedral realization and its signed corner are supplied by the same
irreducibility and coordinate-idempotent calculation as in
`all-bcs-contexts-share-one-hyperoctahedral-signed-type`.
