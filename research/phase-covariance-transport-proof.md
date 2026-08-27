---
rg: 2
id: phase-covariance-transport-proof
kind: route
title: Expand in the two type PVMs and apply Hilbert--Schmidt Pythagoras
target: phase-covariance-words-exactly-measure-type-transport-leakage
requires: []
---

Insert both partitions of unity to obtain

```text
D_lU-UC_l
 =sum_(alpha,beta)
   (lambda_(l,alpha)-mu_(l,beta))E_alpha U F_beta.     (PCT5)
```

The blocks in `(PCT5)` are pairwise orthogonal in `L^2(M,tau)`.  Different
source indices are killed by `E_alpha E_(alpha')=0`; for equal source index
and different target indices, traciality moves the final target projection
next to the first and uses `F_beta F_(beta')=0`.  Pythagoras gives `(PCT2)`.

For root-of-unity codes, every differing coordinate contributes at least
`4 sin^2(pi/m)`, proving `(PCT3)`.  Finally, right multiplication by the
unitary `C_l U^(-1)` identifies
`||D_lU-UC_l||_2` with the ordinary word defect in `(PCT4)`.

