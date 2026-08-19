---
rg: 2
id: fixed-atlas-transport-cost-cannot-separate
kind: claim
title: No fixed positive-dual Fourier transport cost can vanish by universal atlas relations
---

Fix the minimal Wedderburn projections of the two labelled regular-`A_8` chart
algebras from `leavitt-regular-atlas-hyperlinearity-criterion`.  Let
`c_(u,v)>=0` be any **fixed** cost matrix, independent of the finite external
multiplicity and of the relative chart unitary.  Suppose there are dual
potentials `x_v,y_u` with

```text
x_v+y_u <= c_(u,v)
```

and strictly positive value

```text
gamma = sum_v alpha_v x_v + sum_u beta_u y_u > 0.    (FTC1)
```

Then no universal atlas estimate valid in arbitrary finite tracial von Neumann
algebras can force

```text
sum_(u,v) c_(u,v) ||q_u U p_v||_2^2
 <= F(delta)                                             (FTC2)
```

for every relative chart unitary `U`, where `delta` is the canonical packet
defect and `F(0)=0`.

In particular, replacing the hard Hall graph by one fixed soft cost matrix does
**not** evade `universal-atlas-ideal-cannot-force-hall-deficit`.  Any successful
soft-transport obstruction must select its cost/projections from genuinely
finite-multiplicity data in a way that has no fixed extension to the exact
Leavitt factor model.
