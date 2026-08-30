---
rg: 2
id: stw84-locally-finite-times-abelian-proof
kind: route
title: Combine locally finite factor invariance with Pontryagin dimension
target: stw84-locally-finite-times-abelian-computation
requires:
  - stw84-locally-finite-direct-factor-invariance
---

By `stw84-locally-finite-direct-factor-invariance`,

```text
dim_nuc(C*(L times A))=dim_nuc(C*(A)).
```

Fourier transform gives `C*(A)=C(A_hat)`.  Nuclear dimension agrees with
covering dimension for commutative C*-algebras, and the Pontryagin dimension
formula gives

```text
dim(A_hat)=dim_Q(Q tensor_Z A).
```

Combining these equalities proves the claim, including infinite rational
rank.
