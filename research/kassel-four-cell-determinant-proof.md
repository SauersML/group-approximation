---
rg: 2
id: kassel-four-cell-determinant-proof
kind: route
title: Abelianize four Chevalley relators and telescope their integer phases
target: kassel-four-cell-is-minimal-determinant-holonomy
requires: []
artifacts:
  - research/artifacts/kassel-four-cell-determinant-holonomy-2026-08-21.md
---

With additive root phases `a,b,c,d,A,B,C,D`, the four determinant relators
are

```text
r4=c+d,  r5=2d,  r6=-2B,  r12=-c-b,
```

while `w_beta^4` has phase `m=8b-4B`.  Substitution gives
`m=-8r4+4r5+2r6-8r12`.  The four explicit assignments in the artifact show
that deleting any one row leaves an exact `omega`-sector scalar model, so
the support is minimal.

