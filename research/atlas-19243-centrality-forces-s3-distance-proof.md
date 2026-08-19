---
rg: 2
id: atlas-19243-centrality-forces-s3-distance-proof
kind: route
title: Equivariance plus word Lipschitzness gives the 19243 S3-distance wall
target: atlas-19243-centrality-forces-s3-distance
requires:
  - atlas-19243-s3-relative-normal-form
  - atlas-19243-centrality-is-bar-s-consequence
artifacts:
  - experiments/atlas_19243_s3_gap.py
---

`atlas-19243-s3-relative-normal-form` supplies the reduced polynomial

```text
F(c)=r c s c r^-1 c (s r)c.
```

The replay verifies `F(b)=b` and `[p1_12,b]!=1` in the finite `A_8` chart.
If `V` commutes with `r,s`, then `F(V^*bV)=V^*F(b)V`, hence the original
collision evaluates to the fixed first-chart element `b`.  Its named
centrality commutator is therefore a nonidentity regular-`A_8` element and has
normalized-HS distance `sqrt(2)` from the identity.

The collision contains four occurrences of a conjugated second-chart
syllable.  Bi-invariance and telescoping give the constants `8` for the
collision and `16` for its commutator with a fixed unitary.  Reverse triangle
and infimum over the `S_3` commutant give the displayed distance inequality.
The packet form is the fixed finite normal-closure estimate already proved in
`atlas-19243-centrality-is-bar-s-consequence`.
