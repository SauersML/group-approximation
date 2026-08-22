---
rg: 2
id: commuting-neighborhood-pruning-proof
kind: route
title: Partition the joint PVM atoms by one bad coordinate
target: commuting-neighborhood-pruning-pays-atom-mass
requires: []
---

The commuting neighbor PVMs have joint atoms

```text
E_boldb=product_i Q_(i,b_i),       sum_boldb E_boldb=1.
```

Choose one bad coordinate from each joint tuple.  For every projection `E`,
`tau(PE)=||PE||_2^2>=0`.  The joint atoms assigned to a fixed bad pair
`(i,b)` sum to a projection dominated by `Q_(i,b)`.  Therefore

```text
tau(P)=sum_boldb tau(P E_boldb)
 <=sum_(i,b bad)tau(P Q_(i,b))
 =sum_(i,b bad)||P Q_(i,b)||_2^2,
```

which is `(CNP1)`.
