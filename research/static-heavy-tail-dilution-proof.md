---
rg: 2
id: static-heavy-tail-dilution-proof
kind: route
title: Use the diameter of the unitary group and sum the carrier traces
target: bounded-hs-loss-kills-static-heavy-tail-library
requires: []
---

From `(BHL2)` and the operator-norm bound
`||U_(n,j)-V_(n,j)||<=2`,

```text
||U_(n,j)-V_(n,j)||_2^2
 =||(U_(n,j)-V_(n,j))P_n||_2^2
 <=4 tau(P_n).                                        (BHLP1)
```

Sum over the finite local test menu to get `(BHL3)`.  Taking normalized
trace in `(BHL1)` and then monotone limits gives `(BHL4)`.  Formula `(BHL5)`
is summable and satisfies

```text
b_n mu_n<=2^(-n),                                     (BHLP2)
```

so even a depth-dependent finite menu is diluted.  Approximate a finite
prefix of these weights by integer block ratios and put the remaining mass
in an easy bulk block.  Natural evaluation of group words preserves the
block sum, so the same estimates hold in matrix models.

