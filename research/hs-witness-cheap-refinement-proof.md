---
rg: 2
id: hs-witness-cheap-refinement-proof
kind: route
title: Combine weighted median coarea with exact refinement accounting
target: hs-witness-cheap-refinement
requires:
  - weighted-median-coarea-relative-cut
  - block-refinement-boundary-increment
---

Apply `weighted-median-coarea-relative-cut` to the contractions
`a_s=pU_sp` in the normalized corner.  It gives a nonzero `q<=p` with
`tau_p(q)<=1/2` and

```text
sum_s ||[a_s,q]||_(2,p)^2 <= 2 sqrt(2mE) tau_p(q).
```

Multiplying squared corner norms and corner traces by `tau(p)` gives

```text
sum_s ||[pU_sp,q]||_2^2 <= 2 sqrt(2mE) tau(q).
```

By `block-refinement-boundary-increment`, the total boundary increase from
splitting `p` into `q` and `p-q` is exactly twice the left side.  This is
`(WCR)`.
