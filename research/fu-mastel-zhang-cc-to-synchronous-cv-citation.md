---
rg: 2
id: fu-mastel-zhang-cc-to-synchronous-cv-citation
kind: route
title: Import Fu--Mastel--Zhang's symmetrized constraint-variable theorem
target: fu-mastel-zhang-cc-to-synchronous-cv
requires: []
---

**Established by citation.**  Honghao Fu, Kieran Mastel, and Xingjian Zhang,
*Succinct Perfect Zero-knowledge for MIP\**, arXiv:2503.04517v2 (2025),
Theorem 3.1.

The construction samples an incident constraint--variable pair and then asks
one of `(i,i),(j,j),(i,j),(j,i)`.  The theorem gives perfect
finite-dimensional PCC completeness and quantitative finite-dimensional
soundness

```text
value(G^cv)>=1-epsilon  =>  value(G)>=1-poly(C,epsilon).
```

The v2 official arXiv HTML was checked directly on 2026-08-20.  The citation
does not claim commuting-operator completeness; that extension is an internal
tracial argument in `tracial-bcs-incidence-oracularization-proof`.
