---
rg: 2
id: shared-overlap-controls-packet-multiplicity-vector
kind: claim
title: Polar-aligned overlap controls the full weighted multiplicity-vector discrepancy
distinct_from:
  finite-group-shared-overlap-polar-alignment: that produces one large exact common submodule; this converts its discarded dimension into simultaneous bounds for every irreducible multiplicity.
  scaled-kazhdan-transport: that compares commutants under a Kazhdan action; this is a finite semisimple bookkeeping consequence of a supplied intertwining submodule.
---

In the setting of `finite-group-shared-overlap-polar-alignment`, suppose also
that

```text
m_i <= (1+zeta)d.
```

Write the exact `A`-multiplicity vectors of `rho_i` as
`mu_i in N^(Irr(A))`. Then

```text
sum_(sigma in Irr(A)) dim(sigma) |mu_1(sigma)-mu_2(sigma)|
  <= 2(zeta+4 eta^2)d.                                          (OMV1)
```

In particular each fixed packet-type discrepancy, divided by ambient
dimension, is `O_A(zeta+eta^2)`. One pairwise polar alignment therefore
controls the entire selector-sector multiplicity vector, not merely its total
dimension.
