---
rg: 2
id: four-child-three-context-exits-preserve-carrier-proof
kind: route
title: Subtract three copies from a four-copy recurrence and telescope
target: four-child-three-context-exits-preserve-carrier
requires:
  - branching-plus-first-hit-exits-forces-hs-floor
  - robust-rank-one-endpoint-marginal-floor
---

Subtract `(FCE2)` from `(FCE1)` to obtain

```text
q_(n+1)>=4q_n-(3q_n+zeta_n)-delta_n,
```

which is `(FCE5)`.  Iteration gives

```text
q_n>=q_0-sum_(j<n)(delta_j+zeta_j).
```

Insert this lower bound into `(FCE3)`, sum over `n<N`, and use `(FCE4)`.
Reversing the finite double sum gives `(FCE6)`.  The energy-floor conclusion
is the same fixed-`N` argument as `(BFE8)`.

For the contextual specialization, each failure measure is a submeasure of a
law of mass `s_n`, hence the three masses sum to at most `3s_n<=3q_n`.
Equation `(RRF3)` supplies their lower sum.  No integrality, common classical
map, or choice of the largest failure context is used.
