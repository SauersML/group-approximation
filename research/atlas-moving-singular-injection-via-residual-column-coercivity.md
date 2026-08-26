---
rg: 2
id: atlas-moving-singular-injection-via-residual-column-coercivity
kind: route
title: Inject the moving source projection using tracially functorial residual-column coercivity
target: atlas-six-row-singular-counting-dominates-nontrivial-s3
requires:
  - atlas-pointwise-column-coercivity-misses-moving-injection
---

**INVALIDATED IN ITS FIXED-TRACIAL FORM.**  The proposed proof was to derive
`(PCC2)` from fixed C-star/Gram positivity, take the high-singular domain
projections `P_t,Q_(r,t)`, and use `(PCC5)` to show

```text
Ran(P_t) intersect intersection_r Ker(Q_(r,t))={0}.
```

The elementary codimension bound

```text
dim P_t <= sum_r codim Ker(Q_(r,t))=sum_r dim Q_(r,t)
```

would then prove `(SCI3)` with `C_rank=1`.

`atlas-pointwise-column-coercivity-misses-moving-injection`
shows that the required pointwise estimate is the fixed operator inequality
`A^*A<=L^2 sum_r R_r^*R_r`, contradicted in the exact Leavitt factor whenever
its derivation is tracially functorial.  Hence moving the spectral projections
does not rescue this fixed-positivity route.  A matrix-only proof of the same
pointwise inequality, or transversality proved directly after thresholding,
remains live.


