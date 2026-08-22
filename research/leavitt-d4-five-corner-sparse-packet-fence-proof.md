---
rg: 2
id: leavitt-d4-five-corner-sparse-packet-fence-proof
kind: route
title: Rerun the five-corner screen with algebraic inverse pairs and adaptive marks
target: leavitt-d4-five-corner-sparse-packet-fence
requires:
  - leavitt-bergman-adjoint-is-not-unit-inverse
---

The corrected artifact
`research/artifacts/search-degree4-five-corner-omega.py` carries each chart
unit together with its algebraic group inverse.  It tests both dihedral sign
classes, both choices of unary pivot, repeated coefficients, and every
support of exact size one through four from

```text
{h,u,v,v^-1,a,b,c,d,r,p,e}.
```

It first enforces the other unary relation and then accepts any nonidentity
one-copy cyclic reduction of the quotient of the two five-corner residuals.
MSI jobs `16672155` and `16672331`, together with the direct size-one/two
runs, exhausted

```text
15,096,466 sparse layouts,
55,420 ordered candidates surviving the unary filter,
0 adaptive one-copy hits.
```

This replaces the earlier invalid transpose-inverse run.  It is a bounded
support/library fence, not a universal fence on the `(1,1,5,5)` topology.

