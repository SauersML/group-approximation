---
rg: 2
id: operator-norm-rank-monodromy-zero-proof
kind: route
title: Convert subunit projection error to rank equality and cancel the nonzero carrier
target: operator-norm-rank-monodromy-zero
requires: []
artifacts:
  - GroupApproximation/Sofic/InvolutionRankMass.lean
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
---

`InvolutionRankMass.rank_eq_of_projections_close` proves that two orthogonal
projection matrices at operator distance below one have equal rank.  Apply it
edge by edge to obtain the cyclic integer ledger.  If the initial rank `r`
were nonzero, cancellation in

```text
a^k r=b^k r
```

would give `a^k=b^k`; positivity of `k` then gives `a=b`, contrary to the
selector mismatch. Therefore `r=0`.
