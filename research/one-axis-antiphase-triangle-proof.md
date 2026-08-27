---
rg: 2
id: one-axis-antiphase-triangle-proof
kind: route
title: Absorb the source scalar into the local axis and multiply signs around a three-cycle
target: one-axis-pairwise-antiphase-routing-fails-on-triangles
requires: []
---

From `(OAR1)` one has

```text
A_j=sigma_(i,ij)sigma_(j,ij)A_i.
```

From `(OAR2)`, since every sign is its own inverse,

```text
sigma_(i,ij)sigma_(j,ij)=-eta_i eta_j.
```

Multiplying the first equality by `eta_j` gives `B_j=-B_i`.  Alternating a
nonzero operator on the three edges of an odd cycle is impossible, proving
the claim.
