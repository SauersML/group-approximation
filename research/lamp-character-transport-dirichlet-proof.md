---
rg: 2
id: lamp-character-transport-dirichlet-proof
kind: route
title: Expand the covariance defect and apply Cauchy--Schwarz to the overlaps
target: lamp-character-transport-bounds-schreier-dirichlet
requires: []
---

**Complete direct proof.**

`Q_chi = U_s P_chi U_s^*` is a projection with `tau(Q_chi) = q_chi` by
traciality, so summing `(CTL1)` over the resolution of the identity gives

```text
L_s = sum over chi of (q_chi - a_s(chi)).
```

For the dictionary `(CTL3)`, expand each term with `P^* P = P`:

```text
|| Q_chi - P_(s chi) ||_2^2 = q_chi + q_(s chi) - 2 a_s(chi),
```

and sum over `chi`.  The dual action permutes the characters, so
`sum_chi q_(s chi) = sum_chi q_chi` and the right side is
`2 sum_chi (q_chi - a_s(chi)) = 2 L_s`.

For `(CTL2)`, the trace inner product `<x,y> = tau(y^* x)` gives
`tau(PQ) <= ||P||_2 ||Q||_2 = sqrt(tau(P) tau(Q))` for projections, so
`a_s(chi) <= sqrt(q_chi q_(s chi))` and

```text
sum_chi (sqrt(q_chi) - sqrt(q_(s chi)))^2
  = sum_chi q_chi + sum_chi q_(s chi) - 2 sum_chi sqrt(q_chi q_(s chi))
  <= 2 sum_chi (q_chi - a_s(chi))
  = 2 L_s,
```

which is `(CTL2)` after reindexing the left side as `|| h - s.h ||_2^2`.
