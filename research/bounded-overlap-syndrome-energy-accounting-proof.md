---
rg: 2
id: bounded-overlap-syndrome-energy-accounting-proof
kind: route
title: Double-count the syndrome-relator incidence graph
target: bounded-overlap-syndrome-energy-accounting
requires: []
---

Sum the local charge inequalities and reverse the order of summation:

```text
sum_j q_j
 <= L sum_j sum_(r in N(j)) e_r
 =  L sum_(r in R) e_r * #{j : r in N(j)}
 <= L D sum_(r in R) e_r.
```

This is `(BOE)`.  If `sum_j q_j>=beta`, division by `LD` gives the stated
global energy floor.
