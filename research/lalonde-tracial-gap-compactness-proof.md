---
rg: 2
id: lalonde-tracial-gap-compactness-proof
kind: route
title: Compactness upgrades Lalonde's empty tracial face to a uniform HS gap
target: lalonde-certificate-gives-dimension-free-tracial-gap
requires:
  - lalonde-perfect-fd-strategy-has-no-tracial-game-state
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

## Direct compactness proof

Fix strictly positive rational weights on the finitely many losing events
and let `Loss` be their weighted sum.  Each summand
`tr(E_a^x F_b^y)` is nonnegative for commuting positive effects.

Suppose there were no dimension-free positive lower bound for exact
finite-matrix tracial tuples.  Choose tuples in dimensions `d_n` with all
POVM and cross-commutation relations exact and `Loss -> 0`.  Their images
in a tracial matrix ultraproduct define positive effects satisfying the
same relations exactly.  Because the sum has finitely many nonnegative
terms and every weight is strictly positive, `Loss=0` in the ultralimit
forces

```text
tau(E_a^x F_b^y)=0
```

for every losing event.  This is precisely the perfect tracial face ruled
out by `lalonde-perfect-fd-strategy-has-no-tracial-game-state`, a
contradiction.  Therefore the infimum of `Loss` over exact finite-matrix
tracial tuples is some `eta_L>0`, independent of dimension.

For the robust statement, if no positive gap survived sufficiently small
normalized-HS relation defect, choose a sequence whose relation defects
and losses both tend to zero.  Passing to the same tracial ultraproduct
turns all approximate polynomial relations into exact ones, while the
loss again vanishes.  This gives the same forbidden tracial state.  Hence
there exist `delta_0>0` and `eta'_L>0` such that relation defect below
`delta_0` forces `Loss >= eta'_L`, uniformly in matrix dimension.
