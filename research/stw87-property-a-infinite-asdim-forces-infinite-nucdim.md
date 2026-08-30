---
rg: 2
id: stw87-property-a-infinite-asdim-forces-infinite-nucdim
kind: claim
title: Property A and infinite asymptotic dimension force infinite uniform Roe nuclear dimension
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

For every countable discrete bounded-geometry metric space `X` with property A
and `asdim(X)=∞`, prove

```text
dim_nuc(C*_u(X))=∞.
```

## Attempts

Sako's theorem only shows that `C*_u(X)` is nuclear, so the nonnuclearity
obstruction used for spaces without property A is unavailable.  The
Winter--Zacharias estimate is one-sided and becomes vacuous at infinity.
Transfinite nuclear-dimension bounds likewise do not give an ordinary nuclear
lower bound.  The coarse-embedding corner reduction would suffice if `X`
coarsely contained spaces with unbounded uniform Roe nuclear dimension, but
no such finite-dimensional seeds beyond value one are known here.
