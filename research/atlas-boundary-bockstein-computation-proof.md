---
rg: 2
id: atlas-boundary-bockstein-computation-proof
kind: route
title: Close mod-four lifts and compute the first Bockstein in the mod-two cokernel
target: atlas-boundary-derivative-two-primary-torsion
requires: []
artifacts:
  - experiments/atlas_boundary_integral_bockstein.py
  - experiments/atlas-boundary-integral-bockstein.json
---

For an integer presentation matrix in Smith form, a diagonal entry `d`
contributes a mod-two kernel vector exactly when `d` is even.  The first
Bockstein sends that vector to `d/2` modulo two.  It is nonzero exactly when
`v_2(d)=1`; it is zero when `4|d`.  Hence

```text
rank(beta) = number of Smith factors with v_2(d)=1.              (B1)
```

The replay represents a vector modulo four by two bitsets `lo+2 hi`.  During
the exact mod-two left-ideal closure it retains a mod-four lift of every new
echelon row.  Whenever a translated row is dependent modulo two, applying
the same integral reductions leaves `(0,hi)`, i.e. the even vector `2 hi`;
`hi` is precisely its Bockstein value.  These values are closed under the
six generators of `G`, after first taking their canonical normal forms in
the mod-two cokernel.  This gives rank `35`.

The rational and mod-two ranks show independently that there are exactly 35
even nonzero Smith factors.  Equation `(B1)` therefore leaves zero factors
with valuation at least two and proves `(Z/2)^35` as the two-primary torsion.
The same quotient-normal-form closure applied to the four `1+h_i` classes
has rank `35`, identifying this torsion with the covariance-bridge module.
