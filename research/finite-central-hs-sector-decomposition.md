---
rg: 2
id: finite-central-hs-sector-decomposition
kind: claim
title: Almost representations of a finite central extension decompose into weighted projective HS sectors
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  thom-central-corner-criterion: Thom decomposes the exact group von Neumann algebra into twisted central-character corners and characterizes Connes embeddability; this is the finite-matrix normalized-HS analogue for an almost representation before taking an ultraproduct.
  central-extension-twisted-sector-criterion: that criterion is formulated in the norm-matrix-corona/MF setting; this lemma is a normalized-HS spectral cutting statement with dimension-weighted error control.
---

Let

```text
1 -> C_m=<z> -> E -> Q -> 1                              (FCS1)
```

be a finitely presented central extension, and fix a finite presentation and a
section of `Q`, with multiplier `alpha:Q x Q -> C_m`.  Any sequence of
finite-dimensional normalized-HS almost representations of `E` whose
presentation defects tend to zero can, after `o(1)` normalized-HS change, be
written as an orthogonal sum of blocks indexed by `chi in hat(C_m)` such that
on the `chi` block:

1. `z` acts exactly by the scalar `chi(z)`;
2. the quotient generators form a `chi o alpha`-projective almost
   representation of `Q`;
3. the dimension-weighted sum of the projective relator defects tends to zero.

In particular, a fixed positive fraction of matrix dimension on which a
nontrivial central character survives produces a projective almost
representation of the corresponding twisted sector with vanishing defect.
