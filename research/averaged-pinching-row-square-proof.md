---
rg: 2
id: averaged-pinching-row-square-proof
kind: route
title: Telescope averaged conjugations and apply weighted operator Jensen
target: averaged-pinching-channels-are-row-square-lipschitz
requires: []
---

The exact difference is

```text
 (A_Q-A_S)(T)=1/2 sum_r w_r(D_rTQ_r+S_rTD_r).           (APLIP5)
```

Weighted Jensen, contractivity, and traciality give

```text
 ||sum_r w_rD_rTQ_r||_2^2<=tau(T^*HT)<=||H||op||T||_2^2,
 ||sum_r w_rS_rTD_r||_2^2<=tau(T^*TH)<=||H||op||T||_2^2.
```

The triangle inequality and the factor `1/2` prove `(APLIP2)`.  Tensoring
all coefficients by an identity proves complete amplification.  Finally
telescope

```text
 A_Q^K-A_S^K=sum_(t=0)^(K-1)A_Q^t(A_Q-A_S)A_S^(K-1-t)
```

to obtain `(APLIP3)--(APLIP4)`.

