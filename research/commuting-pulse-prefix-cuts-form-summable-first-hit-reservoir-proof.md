---
rg: 2
id: commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir-proof
kind: route
title: Telescope the positive pulse prefix and compress the hard-sign estimate
target: commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir
requires:
  - hard-sign-transport-captures-exit-mass
  - free-root-sign-atoms-transport-with-linear-hs-loss
---

The commuting projections `(I+B_n)/2` give

```text
C_n=C_n(I+B_n)/2+C_n(I-B_n)/2=C_(n+1)+X_n.
```

Their two terms are orthogonal.  Iteration proves `(PCF2)`.

Apply `(HST1)` to `A_n,B_n,V_n,P_n`.  It bounds the mass of `V_nP_n`
outside `R_n^-`.  Inside `R_n^-`, the mass outside `C_n` is

```text
||(I-C_n)R_n^-V_nP_n||_2^2
 <=||(I-C_n)V_nP_n||_2^2,
```

because `C_n` and `R_n^-` commute.  Subtracting these two losses from
`tau(P_n)` gives `(PCF3)`.  The finite-depth approximate statement is the
telescoping product estimate `(SAT2)`.
