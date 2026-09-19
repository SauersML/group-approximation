---
rg: 2
id: six-exit-moving-cut-telescope-proof
kind: route
title: Compare the exact and compressed moving products one transition at a time
target: six-exit-moving-cut-seventh-power-telescope
requires:
  - order-seven-anchor-stops-at-whitehead-compression-leakage
---

Define the exact prefix `B_k=T^kE_0` and the moving compressed prefix
`C_k=E_kTE_(k-1)...TE_0`.  The recursion

```text
B_(k+1)-C_(k+1)
 =T(B_k-C_k)+(1-E_(k+1))TC_k
```

charges the `k`th error to the corresponding transition exit because
`C_k=E_kC_k` and `||C_k||<=1`.  Sum for the six intermediate projections,
left-compress the result by `E_0T`, add the `T^7` relator defect, and apply
Cauchy--Schwarz for the squared-energy form.
