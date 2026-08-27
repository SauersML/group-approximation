---
rg: 2
id: binary-cut-projection-recurrence-gives-bfe1-proof
kind: route
title: Use Pythagoras for the sign cut and trace the recurrence residual
target: binary-cut-projection-recurrence-gives-bfe1
requires:
  - branching-plus-first-hit-exits-forces-hs-floor
  - product-clock-synchronizes-fanizza-and-e5
---

The projections `R_+,R_-` are orthogonal and sum to the identity.  Hence

```text
q'+r
 = tau(CR_+C)+tau(CR_-C)
 = tau(C(R_++R_-)C)
 = tau(C),                                             (1)
```

using `C^2=C` and traciality.  Unitary conjugacy gives `tau(B)=tau(A)=q`.
Therefore

```text
2q-(q'+r)=tau(A+B-C).                                  (2)
```

Normalized trace Cauchy--Schwarz gives

```text
|tau(A+B-C)| <= ||A+B-C||_2 ||I||_2
              = ||A+B-C||_2.                          (3)
```

Equations `(1)--(3)` prove `(BCR2)--(BCR3)`.  Notice that the proof uses block
masses, not intersections of commuting projections, so the sign cut creates
no additional commutator term.
