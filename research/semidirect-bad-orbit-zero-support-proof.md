---
rg: 2
id: semidirect-bad-orbit-zero-support-proof
kind: route
title: Use tracial conjugation invariance on the normal abelian subgroup
target: semidirect-bad-orbit-needs-zero-trace-support
requires: []
---

For `l in L`, conjugation sends the minimal idempotent `e_chi` of `C[H]` to
`e_(l chi)`. Traciality gives

```text
mu(l chi)=tau(e_(l chi))=tau(l e_chi l^(-1))=tau(e_chi)=mu(chi).
```

Thus `mu` is constant on `L`-orbits, proving the zero-support assertion.
Orthogonality of distinct character idempotents proves the packing statement.
