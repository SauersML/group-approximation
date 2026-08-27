---
rg: 2
id: atlas-mixed-minor-nuisance-quotient-proof
kind: route
title: Project away nuisance columns and amplify the fixed scalar singular-value bound
target: atlas-mixed-minor-needs-nuisance-quotient-rank
requires: []
---

Let `P_D` be orthogonal projection onto `ker(D^*)`.  The rank identity

```text
rank[C D]=rank(D)+p
```

is equivalent to injectivity of `P_D C`.  If its least singular value is
`gamma>0`, then for every Hilbert space `K` and every equation
`E=CX+DY`,

```text
(P_D tensor I_K)E=(P_D C tensor I_K)X,
gamma ||X||<=||(P_D tensor I_K)E||<=||E||.
```

Tensoring with `I_K` does not change the nonzero singular values, proving the
dimension-free estimate.  Conversely, failure of the rank identity gives
`0!=x` and `y` with `Cx+Dy=0`; tensoring this scalar kernel vector with any
nonzero operator in `K` gives an exact amplified counterexample.  This proves
both directions and the sharp nuisance-cancellation no-go.
