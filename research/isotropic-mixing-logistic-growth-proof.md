---
rg: 2
id: isotropic-mixing-logistic-growth-proof
kind: route
title: Subtract overlap from the ambient hole and normalize the recurrence
target: isotropic-mixing-has-only-logistic-carrier-growth
requires: []
---

Since `D<=H` and `tr(D)=tr(A)=a`,

```text
tr(QD)=a-tr((H-Q)D)>=a-tr(H-Q),
```

which rearranges to `(IMG1)`. For an exact depolarizing average,

```text
E_u[uAu^*]=(a/tr(H))H,
```

so the expected overlap with `Q` is `(tr(Q)/tr(H))a`. Choosing the best
actuator yields no fixed improvement beyond the complementary hole fraction.
Substituting `a>=gamma tr(Q)` and normalizing by `tr(H)` gives the displayed
logistic recurrence. Its right side maps `[0,1]` into `[0,1]` when
`0<gamma<=1`, so this scalar mechanism cannot certify an overshoot.
