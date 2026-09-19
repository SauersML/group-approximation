---
rg: 2
id: three-line-spectator-escape-proof
kind: route
title: Put equal nonzero charge on the swapped source and destination lines
target: three-line-first-hit-has-invariant-spectator-escape
requires: []
---

Equation `(TSE1)` obeys

```text
chi(u,z,v)=psi(z+v)=psi(v+z)=chi(u,v,z),
```

so the assignment `(u,v,z) mapsto chi(u,v,z)`, `w mapsto 1` respects the
semidirect-product relation.  It is therefore an exact one-dimensional
representation.

Its restriction to `F_p^3` has a single Fourier type, represented in dual
coordinates by `(0,1,1)`.  This type is nontrivial on each of the last two
coordinate lines, but it belongs to neither set requiring the other line to
be trivial.  Hence the full source-root support is one while both oriented
subset projections vanish, proving the claim.

