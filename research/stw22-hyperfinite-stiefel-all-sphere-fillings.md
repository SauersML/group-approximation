---
rg: 2
id: stw22-hyperfinite-stiefel-all-sphere-fillings
kind: claim
title: Hyperfinite strong Stiefel spaces have uniform sphere fillings in every finite degree
distinct_from:
  stw22-strong-stiefel-spaces-have-uniform-loop-fillings: that proves only the degree-one loop modulus; the present theorem proves every finite sphere degree with a modulus uniform over all corners.
  stw22-low-spectrum-weighted-boundary-filling: that transfers fixed positive weights through a moving target projection; the present theorem is unweighted and fixed-target.
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor.  For every integer `k>=0` and
`epsilon>0` there is `rho_k(epsilon)>0` such that the following holds
simultaneously for every nonzero projection `e in R`, every projection `p`
with `tau(p)<=tau(e)`, and every `v_0 in V(p,e)`.

Every continuous map

```text
v:S^k->V(p,e),       V(p,e)={v in eR:v^*v=p},
```

whose image lies in the `rho_k(epsilon)`-ball about `v_0` extends to
`B^(k+1)` inside the `epsilon`-ball about `v_0`.  Moreover every individual
`V(p,e)` is `k`-connected for every finite `k`.

Thus the family of all hyperfinite strong Stiefel spaces, viewed in the
common Hilbert space `L^2(R)`, is uniformly equi-`LC^k` for every finite
`k`.  The moduli do not depend on either corner trace.
