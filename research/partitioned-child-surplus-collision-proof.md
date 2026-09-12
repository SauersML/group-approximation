---
rg: 2
id: partitioned-child-surplus-collision-proof
kind: route
title: Sum source-to-partition support leakages and apply the contraction ladder
target: partitioned-child-surplus-collision-supplies-contraction
requires:
  - unitary-offdiagonal-block-gram-is-support-leakage
  - contractive-computation-ladder
---

For one piece, cyclicity of the trace gives

```text
||(1-D_i)U_iC_i||_2^2
 =tr(C_iU_i^*(1-D_i)U_iC_i)
 =tr(C_i)-tr(D_iU_iC_iU_i^*)
 >=tr(C_i)-tr(D_i).
```

Summing and using `sum_i tr(D_i)<=tr(Q_(n+1))` yields

```text
sum_i ell_i>=sum_i tr(C_i)-a_(n+1).
```

Now `(PCS3)` and `(PCS4)` give `(PCS5)`, and division by `1+beta`
gives `(PCS6)`.  Fixedly many word or finite-chart leakage estimates give
`(PCS8)`.  The conclusion is then exactly
`contractive-computation-ladder`.

