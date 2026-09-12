---
rg: 2
id: stw81-ctdim-type-i-composition-proof
kind: route
title: Compare continuous-trace subquotients with a type-I composition series
target: stw81-ctdim-equals-type-i-topological-dimension
requires:
  - stw81-continuous-trace-shadow-invariant
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

If `D=J/I` is a continuous-trace subquotient of `A`, then `Prim(D)` is a
locally closed Hausdorff subspace of `Prim(A)`.  Brown--Pedersen topological
dimension is the supremum of the covering dimensions of such subspaces, so

```text
ctdim(A) <= topdim(A).                                (1)
```

Conversely, choose a type-I composition series for `A` whose nonzero
successive factors `D_alpha` have continuous trace.  The composition-series
formula for Brown--Pedersen dimension gives

```text
topdim(A) = sup_alpha dim(Prim(D_alpha)).              (2)
```

Every `D_alpha` is a continuous-trace subquotient of `A`, so the right side
of (2) is at most `ctdim(A)`.  Combining with (1) proves equality.

**Trust boundary.**  The route uses the standard continuous-trace
composition series of a separable type-I algebra and the Brown--Pedersen--
Thiel composition-series formula for topological dimension.
