---
rg: 2
id: independent-chart-eda-leakage-proof
kind: route
title: Compute the loss after refining one conductor edge by independent labels
target: independent-chart-refinement-forces-eda-leakage
requires: []
---

By `(ICR2)` and orthogonality of the two row projections `S` and `1-S`,

```text
||SVR||_2^2=||VR||_2^2-L=mu-L.                         (ICP1)
```

For each `i`, `TE_i=VR tensor P_i`, so

```text
||TE_i||_2^2=mu/q.                                     (ICP2)
```

Moreover

```text
F_iTE_i=SVR tensor Q_iP_i.                             (ICP3)
```

The two coordinate projections commute and their intersection has trace
`1/q^2`. Hence

```text
||F_iTE_i||_2^2=(mu-L)/q^2.                            (ICP4)
```

The `F_i` and `1-F_i` row pieces are orthogonal. Subtracting `(ICP4)` from
`(ICP2)` and summing over `q` labels gives

```text
sum_i||(1-F_i)TE_i||_2^2
 =q(mu/q-(mu-L)/q^2)
 =mu(1-1/q)+L/q,                                       (ICP5)
```

which is `(ICR5)`. Tensoring any pre-existing defect operator by an identity
preserves its normalized `L_2` norm, proving the ledger statement.
