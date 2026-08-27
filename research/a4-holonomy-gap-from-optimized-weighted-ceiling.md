---
rg: 2
id: a4-holonomy-gap-from-optimized-weighted-ceiling
kind: route
title: Any sharp reciprocal weight certificate spends exactly the raw-S3 budget
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-optimized-weighted-four-cycle-ceiling
  - atlas-a8-t21-diagonal-energy-envelope
---

Let `c_01,c_23,c_30` be the weights supplied by the prerequisite and write

```text
x_ij=||[U_n,lambda_(k_n)(tij)]||_2,
D_ij=x_ij^2/2.
```

The exact `t21` word and `atlas-a8-t21-diagonal-energy-envelope` give

```text
a_n^2
 <= c_01 x_01^2+c_23 x_23^2+c_30 x_30^2
 = 2(c_01D_01+c_23D_23+c_30D_30).
```

The other raw involution is `t12`, so

```text
b_n^2=x_12^2=2D_12.
```

Consequently

```text
a_n^2+b_n^2
 <=2(c_01D_01+D_12+c_23D_23+c_30D_30).
```

The strict `1/256` weighted ceiling therefore implies

```text
limsup_n(a_n^2+b_n^2)<1/128,
```

which is exactly `atlas-a4-holonomy-coherence-gap`.

This turns the direct nonhyperlinear lane into a one-hole optimization target:
find any point on the reciprocal weight surface for which the fixed A4/collision
network has enough scalar trace slack.