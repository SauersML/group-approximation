---
rg: 2
id: sv26-global-glimm-gives-two-color-splitting
kind: claim
title: Under m-comparison and bounded divisibility the Global Glimm Property gives a two-piece splitting (Seth--Vilalta)
distinct_from:
  sv26-bounded-divisibility-dimension-reduction: that goes from the two-piece splitting to purity and from purity to the Global Glimm Property; this is the remaining implication from the Global Glimm Property to the splitting.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `D` be a C*-algebra and `m, M in N`.  Assume that `Cu(D)` has
`m`-comparison and that for every `N >= 1` and every `x' << x` in `Cu(D)` there
is `y` with `x' << N y << M x`.  Put `M_1 = 2M^3` and `L = 2(m+1)(M_1+2)`.  If
`D` has the Global Glimm Property, then every `x' << x` in `Cu(D)` admits
`y_0, y_1 in Cu(D)` with

```text
y_0 + y_1 <= x          and          x' << L y_0 ,   x' << L y_1 .
```
